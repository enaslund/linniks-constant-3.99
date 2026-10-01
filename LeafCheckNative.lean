module

public import LeafCheckCore
public import Lean.Data.Json

/-!
# Running the certificate checker and the numeric checker natively

`lake build leafcheck` (binary `.lake/build/bin/leafcheck`; no Mathlib is compiled). It reads JSON
lines from standard input, one leaf per line (written by
`computations/graded/graded_lean_export.py --full` in the research repository):

`{"name": .., "leaf": <as for certrun>, "tree": <as for certrun>, "meta": <the leaf's metadata>}`

where `meta` is the object written by `graded_lean_export.py --numerics` for the leaf (its fields
`L`, `far_profile`, `columns`, `far`, `first`; `research/notes/leaf-data-semantics-2026-09-29.md` in the research repository
§5). For each line it prints

`name value boxes num`

where `value` is `CertCore.checkLeaf` on the leaf and tree (`none` if it rejects) and `boxes` the
number of tree nodes, as `certrun` prints them, and `num` is `ok` if
`LeafCheckCore.checkNum meta leaf = true` and `fail:<reason>` otherwise (the reason, from
`LeafCheckCore.diagnose` or the metadata parser, is informational). With `--timing` two more
fields follow: the milliseconds spent in `checkLeaf` and in `checkNum`.

With `--num-only` the certificate check is skipped (for leaves whose certificates are checked by
another run, e.g. `certrun`): the line needs no `"tree"`, and `leafcheck` prints
`name skipped skipped num` (with `--timing`, `0` for the certificate check).

Soundness: `GradedNear.Cert.checkLeaf_ofCore` and `checkLeaf_sound` for `value`;
`GradedNear.Cert.checkNum_sound` (`checkNum m L = true → MetaValid m (Leaf.ofCore L)`) for `ok`.

The JSON parsing is unverified glue. It translates the metadata into `LeafMetaCore.LeafMeta`:
* each column's span (`bin lo hi`, or `tail lo` with `hi = "infinity"`) and objective
  (`{"G": φ}` or `{"hidden": {"phi", "p"}}`); every column's far profile must be the leaf's;
* the profile `(c₁, c₂, θ, α)`, whose `ε` must be `10⁻⁷` (the `ε` of `LeafNumCore` and of
  `GradedNear.Kernel.FarProfile`);
* `η`, the inside first family of the far budget (`far.inside`), its charge (`first.inside`);
  the two must describe the same family (equal `n` and `b`, both present or both absent). The
  checker itself requires, where the charge uses `J_new`, that this `b` is at most `p`
  (`LeafCheckCore.jnewOk`, `GradedNear.Cert.checkNum_jnew`);
* a reserved family charged without columns: `far.reserved` with `added_back = false`, with `φ₂`
  and `lo₂` from `first.J2` (which must then have `removed_for_columns = false`); a reserved
  family with second-family columns is not subtracted from the far budget nor charged in `first`.

It also compares the metadata's stored integers (every column's `G` and `W`, and `F`, `first`)
with the leaf's, and fails on a difference.
-/

@[expose] public section

open Lean CertCore LeafMetaCore

/-! ## The leaf and the tree (as in `CertRunNative.lean`) -/

def getInt (j : Json) : Except String Int := j.getInt?

def getNat (j : Json) : Except String Nat := j.getNat?

def intList (j : Json) : Except String (List Int) := do
  (← j.getArr?).toList.mapM getInt

def natList (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM getNat

def parseCol (j : Json) : Except String Col := do
  let a ← j.getArr?
  unless a.size = 7 do throw "column: expected 7 fields"
  return ⟨← getInt a[0]!, ← getInt a[1]!, ← getInt a[2]!, ← getInt a[3]!, ← getInt a[4]!,
    ← intList a[5]!, ← intList a[6]!⟩

def parseFam (j : Json) : Except String (Int × Int × Int) := do
  let a ← j.getArr?
  unless a.size = 3 do throw "family term: expected 3 fields"
  return (← getInt a[0]!, ← getInt a[1]!, ← getInt a[2]!)

def parseRow (j : Json) : Except String RowHead := do
  let a ← j.getArr?
  unless a.size = 2 do throw "row: expected 2 fields"
  return ⟨← getInt a[0]!, ← (← a[1]!.getArr?).toList.mapM parseFam⟩

def parseLeaf (j : Json) : Except String Leaf := do
  let cols ← (← (← j.getObjVal? "cols").getArr?).toList.mapM parseCol
  let rows ← (← (← j.getObjVal? "rows").getArr?).toList.mapM parseRow
  return ⟨cols, rows, ← getInt (← j.getObjVal? "F"), ← getInt (← j.getObjVal? "ng"),
    ← getInt (← j.getObjVal? "n2"), ← getInt (← j.getObjVal? "first"),
    ← getInt (← j.getObjVal? "final")⟩

def optNat (j : Json) (k : String) : Except String Nat :=
  match j.getObjVal? k with
  | .ok v => getNat v
  | .error _ => pure 0

def parseCase (j : Json) : Except String CaseCert := do
  if j == Json.str "excluded" then return .excluded
  return .duals ⟨← getNat (← j.getObjVal? "Y"), ← optNat j "V", ← optNat j "U", ← optNat j "P",
    ← optNat j "M", ← natList (← j.getObjVal? "Z")⟩

partial def parseTree (j : Json) : Except String Tree := do
  match j.getObjVal? "split" with
  | .ok k =>
    let ch ← (← j.getObjVal? "children").getArr?
    unless ch.size = 2 do throw "split: expected 2 children"
    return .split (← getNat k) (← getInt (← j.getObjVal? "mid")) (← parseTree ch[0]!)
      (← parseTree ch[1]!)
  | .error _ =>
    return .node (← natList (← j.getObjVal? "orders"))
      (← (← (← j.getObjVal? "cases").getArr?).toList.mapM parseCase)

def treeBoxes : Tree → Nat
  | .split _ _ l r => treeBoxes l + treeBoxes r
  | .node _ _ => 1

/-! ## The metadata -/

/-- An exact rational written as `"n"` or `"n/d"` (Python's `str(Fraction(x))`). -/
def parseRat (j : Json) : Except String Rat := do
  let s ← j.getStr?
  match s.splitOn "/" with
  | [a] =>
    match a.toInt? with
    | some n => pure (n : Rat)
    | none => throw s!"rational: {s}"
  | [a, b] =>
    match a.toInt?, b.toNat? with
    | some n, some d => if d = 0 then throw s!"rational: {s}" else pure ((n : Rat) / (d : Rat))
    | _, _ => throw s!"rational: {s}"
  | _ => throw s!"rational: {s}"

/-- A field that may be `null`. -/
def optField (j : Json) (k : String) : Except String (Option Json) := do
  match ← j.getObjVal? k with
  | .null => pure none
  | v => pure (some v)

/-- One column's metadata, its far profile's name and its stored `G` and `W`. -/
def parseColMeta (j : Json) : Except String (ColMeta × String × Int × Int) := do
  let kind ← (← j.getObjVal? "kind").getStr?
  let lo ← parseRat (← j.getObjVal? "lo")
  let span ← match kind with
    | "bin" => pure (Span.bin lo (← parseRat (← j.getObjVal? "hi")))
    | "tail" => do
      unless (← (← j.getObjVal? "hi").getStr?) == "infinity" do throw "tail: hi is not infinity"
      pure (Span.tail lo)
    | _ => throw s!"column kind {kind}"
  let o ← j.getObjVal? "obj"
  let obj ← match o.getObjVal? "G" with
    | .ok φ => pure (Obj.G (← parseRat φ))
    | .error _ => do
      let h ← o.getObjVal? "hidden"
      pure (Obj.hidden (← parseRat (← h.getObjVal? "phi")) (← parseRat (← h.getObjVal? "p")))
  return (⟨span, obj⟩, ← (← j.getObjVal? "w").getStr?, ← getInt (← j.getObjVal? "G"),
    ← getInt (← j.getObjVal? "W"))

/-- The metadata of a leaf (the object of `graded_lean_export.py --numerics`), checked for
consistency with the leaf's stored integers. -/
def parseMeta (j : Json) (L : Leaf) : Except String LeafMeta := do
  let lexp ← parseRat (← j.getObjVal? "L")
  -- the far profile
  let fp ← j.getObjVal? "far_profile"
  let pname ← (← fp.getObjVal? "profile").getStr?
  unless (← parseRat (← fp.getObjVal? "eps")) == LeafNumCore.epsQ do throw "profile:eps"
  let prof : Profile := ⟨← parseRat (← fp.getObjVal? "c1"), ← parseRat (← fp.getObjVal? "c2"),
    ← parseRat (← fp.getObjVal? "theta"),
    ← (← (← fp.getObjVal? "alpha").getArr?).toList.mapM parseRat⟩
  -- the columns
  let cs ← (← (← j.getObjVal? "columns").getArr?).toList.mapM parseColMeta
  unless cs.length = L.cols.length do throw "meta:columns:length"
  for (c, col, i) in cs.zip (L.cols.zip (List.range cs.length)) do
    unless c.2.1 == pname do throw s!"meta:column:{i}:profile"
    unless c.2.2.1 == col.G ∧ c.2.2.2 == col.W do throw s!"meta:column:{i}:stored"
  -- the far budget
  let far ← j.getObjVal? "far"
  unless (← (← far.getObjVal? "V").getStr?) == pname do throw "meta:far:profile"
  unless (← getInt (← far.getObjVal? "F")) == L.F do throw "meta:far:stored"
  let eta ← parseRat (← far.getObjVal? "eta")
  let farInside ← match ← optField far "inside" with
    | some v => pure (some (← getNat (← v.getObjVal? "n"), ← parseRat (← v.getObjVal? "b")))
    | none => pure none
  -- the first-family charge
  let first ← j.getObjVal? "first"
  unless (← getInt (← first.getObjVal? "first")) == L.first do throw "meta:first:stored"
  let firstInside ← match ← optField first "inside" with
    | some f => pure (some ⟨← getNat (← f.getObjVal? "n"), ← getNat (← f.getObjVal? "alpha"),
        ← parseRat (← f.getObjVal? "phi_t"), ← parseRat (← f.getObjVal? "a"),
        ← parseRat (← f.getObjVal? "p"), ← (← f.getObjVal? "J_new").getBool?⟩)
    | none => pure none
  -- the charged family is the far budget's inside family (same `n` and `b`)
  match ← optField first "inside", farInside with
  | some f, some (n, b) =>
    unless (← getNat (← f.getObjVal? "n")) == n ∧ (← parseRat (← f.getObjVal? "b")) == b do
      throw "meta:first:family"
  | none, none => pure ()
  | _, _ => throw "meta:first:family"
  -- a reserved family charged without columns
  let reserved ← match ← optField far "reserved", ← optField first "J2" with
    | none, none => pure none
    | some r, some j2 => do
      let n₂ ← getNat (← r.getObjVal? "n2")
      let back ← (← r.getObjVal? "added_back").getBool?
      unless (← getNat (← j2.getObjVal? "n2")) == n₂ do throw "meta:reserved:n2"
      unless (← (← j2.getObjVal? "removed_for_columns").getBool?) == back do
        throw "meta:reserved:columns"
      if back then pure none
      else pure (some ⟨n₂, ← parseRat (← j2.getObjVal? "phi2"), ← parseRat (← j2.getObjVal? "lo2"),
        ← parseRat (← r.getObjVal? "hi2")⟩)
    | _, _ => throw "meta:reserved:J2"
  return ⟨lexp, eta, prof, cs.map (·.1), farInside, firstInside, reserved⟩

/-! ## The loop -/

def noSpaces (s : String) : String := s.map fun c => if c = ' ' then '_' else c

def msSince (t : Nat) : IO String := do
  let t' ← IO.monoNanosNow
  return toString ((t' - t) / 1000000)

/-- `(value, boxes)` of the certificate check, or `(skipped, skipped)` without a tree
(`--num-only`). -/
def certFields (L : Leaf) : Option Tree → String × String
  | some T => ((match checkLeaf L T with
      | some v => toString v
      | none => "none"), toString (treeBoxes T))
  | none => ("skipped", "skipped")

partial def loop (timing numOnly : Bool) (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) :
    IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let parsed : Except String (String × Leaf × Option Tree × Json) := do
    let j ← Json.parse line
    let T ← if numOnly then pure none else some <$> parseTree (← j.getObjVal? "tree")
    return (← (← j.getObjVal? "name").getStr?, ← parseLeaf (← j.getObjVal? "leaf"), T,
      ← j.getObjVal? "meta")
  match parsed with
  | .error e => stdout.putStrLn s!"ERROR {e}"
  | .ok (name, L, T, mj) =>
    let t0 ← IO.monoNanosNow
    let (v, boxes) ← pure (certFields L T)
    let tc ← msSince t0
    let t1 ← IO.monoNanosNow
    let num ← pure (match parseMeta mj L with
      | .error e => s!"fail:{noSpaces e}"
      | .ok m =>
        if LeafCheckCore.checkNum m L then "ok"
        else s!"fail:{noSpaces ((LeafCheckCore.diagnose m L).getD "unknown")}")
    let tn ← msSince t1
    let extra := if timing then s!" {tc} {tn}" else ""
    stdout.putStrLn s!"{name} {v} {boxes} {num}{extra}"
  stdout.flush
  loop timing numOnly stdin stdout

def main (args : List String) : IO Unit := do
  loop (args.contains "--timing") (args.contains "--num-only") (← IO.getStdin) (← IO.getStdout)
