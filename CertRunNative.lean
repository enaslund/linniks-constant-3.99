module

public import CertCore
public import Lean.Data.Json

/-!
# Running the checker natively on exported leaves

The compiled counterpart of `scripts/CertRun.lean` (`lake build certrun`, binary
`.lake/build/bin/certrun`), with the same protocol. It reads JSON lines from standard input, one
leaf per line (written by `computations/graded/graded_lean_export.py --jsonl` in the research repository):

`{"name": .., "leaf": {"cols": [[G, W, C, NH, E, [v..], [D..]], ..], "rows": [[d, [[n, v, D], ..]], ..],
  "F": .., "ng": .., "n2": .., "first": .., "final": ..}, "tree": <stored certificate tree>}`

and prints, for each, `name value boxes` where `value` is `CertCore.checkLeaf` evaluated on the
parsed leaf and tree (`none` if it rejects), and `boxes` the number of terminal boxes (the tree's
leaves).

`CertCore` depends on Lean core only, so this program compiles without Mathlib.
`GradedNear.Cert.checkLeaf_ofCore` (`GradedNear/Cert/FastEq.lean`) proves that
`CertCore.checkLeaf L T` is `GradedNear.Cert.checkLeaf` (whose soundness is
`GradedNear.Cert.checkLeaf_sound`) on the leaf and tree converted field by field. The JSON parsing
below is unverified glue, and the exporter compares its results with `graded_cert`'s values.
-/

@[expose] public section

open Lean CertCore

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

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let out : Except String String := do
    let j ← Json.parse line
    let name ← (← j.getObjVal? "name").getStr?
    let L ← parseLeaf (← j.getObjVal? "leaf")
    let T ← parseTree (← j.getObjVal? "tree")
    let v := match checkLeaf L T with
      | some v => toString v
      | none => "none"
    return s!"{name} {v} {treeBoxes T}"
  match out with
  | .ok s => stdout.putStrLn s
  | .error e => stdout.putStrLn s!"ERROR {e}"
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
