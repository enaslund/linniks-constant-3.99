module

public import RowCheckCore
public import Lean.Data.Json

/-!
# Running the near-row checker natively

`lake build rowcheck` (binary `.lake/build/bin/rowcheck`; no Mathlib is compiled). It reads JSON
lines from standard input, one leaf per line (written by
`computations/graded/graded_lean_export.py --rows` in the research repository):

`{"name": .., "leaf": <as for certrun>, "rows": [null | <row metadata>, ...]}`

with one entry per near row of the leaf: `null` for the inherited two-test row, otherwise
`{"p": {"gamma", "g1", "t0", "s", "s1", "h": [..]}, "xs": [..], "ds": [..],
  "cols": [null | [hi, anc, del, delHi, xi, di, dj], ..], "fam": [null | [.., spec?], ..]}`
(rationals as `"n"` or `"n/d"`), where a family term's optional eighth field names its second kept
zero (`parseSpec`). For each line it prints

`name ok rows checked items ms special` or `name fail:<reason>`

where `ok` means `RowCheckCore.checkRows leaf rows = true`, `rows` is the number of near rows,
`checked` the number with metadata, `items` the number of checked entries, `ms` the time, and
`special` the number of checked entries that keep a second zero (`Spec.two`, `Spec.cz`).
Soundness: `GradedNear.Row.checkRows_sound`. The JSON parsing and the failure diagnosis are
unverified glue.
-/

@[expose] public section

open Lean CertCore RowCheckCore IntervalCore

def getInt (j : Json) : Except String Int := j.getInt?

def getNat (j : Json) : Except String Nat := j.getNat?

def intList (j : Json) : Except String (List Int) := do
  (← j.getArr?).toList.mapM getInt

def parseCol (j : Json) : Except String Col := do
  let a ← j.getArr?
  unless a.size = 7 do throw "column: expected 7 fields"
  return ⟨← getInt a[0]!, ← getInt a[1]!, ← getInt a[2]!, ← getInt a[3]!, ← getInt a[4]!,
    ← intList a[5]!, ← intList a[6]!⟩

def parseFam (j : Json) : Except String (Int × Int × Int) := do
  let a ← j.getArr?
  unless a.size = 3 do throw "family term: expected 3 fields"
  return (← getInt a[0]!, ← getInt a[1]!, ← getInt a[2]!)

def parseRowHead (j : Json) : Except String RowHead := do
  let a ← j.getArr?
  unless a.size = 2 do throw "row: expected 2 fields"
  return ⟨← getInt a[0]!, ← (← a[1]!.getArr?).toList.mapM parseFam⟩

def parseLeaf (j : Json) : Except String Leaf := do
  let cols ← (← (← j.getObjVal? "cols").getArr?).toList.mapM parseCol
  let rows ← (← (← j.getObjVal? "rows").getArr?).toList.mapM parseRowHead
  return ⟨cols, rows, ← getInt (← j.getObjVal? "F"), ← getInt (← j.getObjVal? "ng"),
    ← getInt (← j.getObjVal? "n2"), ← getInt (← j.getObjVal? "first"),
    ← getInt (← j.getObjVal? "final")⟩

/-- An exact rational written as `"n"` or `"n/d"`. -/
def parseRat (j : Json) : Except String Rat := do
  let s ← j.getStr?
  match s.splitOn "/" with
  | [n] => match n.toInt? with
    | some n => return (n : Rat)
    | none => throw s!"bad rational {s}"
  | [n, d] => match n.toInt?, d.toNat? with
    | some n, some d => if d = 0 then throw s!"bad rational {s}" else return mkRat n d
    | _, _ => throw s!"bad rational {s}"
  | _ => throw s!"bad rational {s}"

def ratList (j : Json) : Except String (List Rat) := do
  (← j.getArr?).toList.mapM parseRat

/-- An entry's second kept zero: absent or `null` (`one`), `{"two": [xa, xb, ylo, yhi | null, ytop,
n]}` or `{"cz": [d, [y₀, y₁, ..]]}`. -/
def parseSpec (j : Json) : Except String Spec := do
  if j.isNull then return .one
  match j.getObjVal? "two" with
  | .ok t =>
    let a ← t.getArr?
    unless a.size = 6 do throw "two: expected 6 fields"
    let yhi ← if a[3]!.isNull then pure none else some <$> parseRat a[3]!
    return .two (← parseRat a[0]!) (← parseRat a[1]!) (← parseRat a[2]!) yhi
      (← parseRat a[4]!) (← getNat a[5]!)
  | .error _ =>
    let a ← (← j.getObjVal? "cz").getArr?
    unless a.size = 2 do throw "cz: expected 2 fields"
    return .cz (← parseRat a[0]!) (← ratList a[1]!)

def parseEnt (j : Json) : Except String (Option Ent) := do
  if j.isNull then return none
  let a ← j.getArr?
  unless a.size = 7 || a.size = 8 do throw "entry: expected 7 or 8 fields"
  let sp ← if a.size = 8 then parseSpec a[7]! else pure .one
  return some ⟨← parseRat a[0]!, ← parseRat a[1]!, ← parseRat a[2]!, ← parseRat a[3]!,
    ← getNat a[4]!, ← getNat a[5]!, ← getNat a[6]!, sp⟩

def parseRowMeta (j : Json) : Except String (Option RowMeta) := do
  if j.isNull then return none
  let pj ← j.getObjVal? "p"
  let g (k : String) : Except String Rat := do parseRat (← pj.getObjVal? k)
  let p : RowP := ⟨← g "gamma", ← g "g1", ← g "t0", ← g "s", ← g "s1",
    ← ratList (← pj.getObjVal? "h")⟩
  return some ⟨p, ← ratList (← j.getObjVal? "xs"), ← ratList (← j.getObjVal? "ds"),
    ← (← (← j.getObjVal? "cols").getArr?).toList.mapM parseEnt,
    ← (← (← j.getObjVal? "fam").getArr?).toList.mapM parseEnt⟩

/-! ## Diagnosis of a failure (informational) -/

def ratStr (q : Rat) : String := s!"{q.num}/{q.den}"

def diagnoseRow (L : Leaf) (k : Nat) (rm : RowMeta) : String := Id.run do
  let row := L.rows.getD k ⟨1, []⟩
  if rm.cols.length != L.cols.length then return s!"row {k}: {rm.cols.length} column semantics for {L.cols.length} columns"
  if rm.fam.length != row.fam.length then return s!"row {k}: {rm.fam.length} family semantics for {row.fam.length} terms"
  if !(row.fam.all fun t => decide (0 < t.2.2)) then return s!"row {k}: a family diagonal is not positive"
  match rowItems L k rm with
  | none => return s!"row {k}: a column with a positive feature has no semantics"
  | some items =>
    let p := rm.p
    if !p.good then return s!"row {k}: parameters not good"
    if !decide (0 < (row.d : Rat) / ((RowCheckCore.S : Rat) * (1 + eta)) - eta) then return s!"row {k}: radius"
    match ibUpper p with
    | none => return s!"row {k}: a cell bound of ω is not positive"
    | some IL =>
      match items.mapM (fun it => specVals p it.e.sp) with
      | none => return s!"row {k}: the values of a special entry could not be computed"
      | some vals =>
      let cs := ckFx p (defaultPrec + 16)
      let FT := rm.xs.map fun x => fI (2 * p.γ) x
      let DT := rm.ds.map fun δ => dI p cs δ
      let vs := items.zip vals
      let Du := duOf row.d DT vs
      for x in vs do
        let it := x.1
        if !itemPre p rm.xs rm.ds FT DT x then
          let e := it.e
          let Dj := (DT.getD e.dj default).lo
          let F := (FT.getD e.xi default).lo
          return s!"row {k}: entry hi={ratStr e.hi} anc={ratStr e.anc} del={ratStr e.del} delHi={ratStr e.delHi} v={it.v} D={it.D}: pre-check (D(delHi).lo-1/6={ratStr (Dj - 1/6)}, F.lo+add-1/6={ratStr (F + x.2.1 - 1/6)}, add={ratStr x.2.1}, exc={ratStr x.2.2})"
        if !itemFeat IL Du FT x then
          return s!"row {k}: entry hi={ratStr it.e.hi} anc={ratStr it.e.anc} v={it.v}: feature (add={ratStr x.2.1}, exc={ratStr x.2.2})"
      return s!"row {k}: unknown"

def diagnose (L : Leaf) (rms : List (Option RowMeta)) : String := Id.run do
  if rms.length != L.rows.length then return s!"{rms.length} row metadata for {L.rows.length} rows"
  for k in List.range rms.length do
    match rms.getD k none with
    | none => pure ()
    | some rm => if !checkRow L k rm then return diagnoseRow L k rm
  return "unknown"

def processLine (line : String) : IO Unit := do
  let j ← IO.ofExcept (Json.parse line)
  let name ← IO.ofExcept (j.getObjValAs? String "name")
  match (do
      let L ← parseLeaf (← j.getObjVal? "leaf")
      let rms ← (← (← j.getObjVal? "rows").getArr?).toList.mapM parseRowMeta
      return (L, rms)) with
  | .error e => IO.println s!"{name} fail:parse:{e}"
  | .ok (L, rms) =>
    let t0 ← IO.monoMsNow
    let ok := checkRows L rms
    let t1 ← IO.monoMsNow
    if ok then
      let checked := rms.filter Option.isSome
      let items := (List.range rms.length).foldl (fun acc k => match rms.getD k none with
        | none => acc
        | some rm => acc + ((rowItems L k rm).map List.length).getD 0) 0
      let isOne (it : Item) : Bool := match it.e.sp with
        | .one => true
        | _ => false
      let special := (List.range rms.length).foldl (fun acc k => match rms.getD k none with
        | none => acc
        | some rm => acc + (((rowItems L k rm).map fun its =>
            (its.filter fun it => !isOne it).length).getD 0)) 0
      IO.println s!"{name} ok {rms.length} {checked.length} {items} {t1 - t0} {special}"
    else
      IO.println s!"{name} fail:{diagnose L rms}"
  (← IO.getStdout).flush

def main : IO Unit := do
  let stdin ← IO.getStdin
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := line.trimAscii.toString
    unless line.isEmpty do processLine line
