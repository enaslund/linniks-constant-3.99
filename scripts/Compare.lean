module

public import Lean

/-!
# A local stand-in for Palomar's comparator

Run from the project root with `lake env lean --run scripts/Compare.lean`. It follows the
algorithm of Lean FRO's `comparator` (`Comparator/Compare.lean`, `Comparator/Axioms.lean`), on
the elaborated environments instead of `lean4export` exports:
* each theorem of `comparator.json` is a theorem in both modules, with the same name, universe
  parameters and statement;
* every constant reachable from those statements (through types, values, constructors and
  recursor rules) other than the theorems themselves has an identical `ConstantInfo` in both
  environments (expressions are compared up to alpha-equivalence);
* the constants reachable from the Solution's theorems use no axiom outside `permitted_axioms`.

The kernel replay is `lake env leanchecker` in `scripts/verify.sh`. The real comparator was also
run locally (see `README.md`).
-/

@[expose] public section

open Lean

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

/-- As `Comparator.runForUsedConsts`. -/
def usedConsts (info : ConstantInfo) : Array Name := Id.run do
  let mut out := info.type.getUsedConstants.push info.name
  if let some val := info.value? (allowOpaque := true) then
    out := out ++ val.getUsedConstants
  match info with
  | .inductInfo i => out := out ++ i.ctors.toArray ++ i.all.toArray
  | .ctorInfo i => out := out.push i.induct
  | .recInfo i =>
    for r in i.rules do
      out := (out.push r.ctor) ++ r.rhs.getUsedConstants
  | _ => pure ()
  return out

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let cfg ← IO.ofExcept (Json.parse (← IO.FS.readFile "comparator.json"))
  let names := (← IO.ofExcept (cfg.getObjValAs? (Array String) "theorem_names")).map String.toName
  let permitted := (← IO.ofExcept (cfg.getObjValAs? (Array String) "permitted_axioms")).map
    String.toName
  let envC ← importModules #[{ module := `Challenge }] {}
  let envS ← importModules #[{ module := `Solution }] {}
  let mut problems : Array String := #[]
  -- the statements
  let mut work : Array Name := #[]
  for n in names do
    match envC.find? n, envS.find? n with
    | some (.thmInfo c), some (.thmInfo s) =>
      if c.toConstantVal != s.toConstantVal then
        problems := problems.push s!"statement differs: {n}"
      work := work ++ c.type.getUsedConstants
    | _, _ => problems := problems.push s!"not a theorem in both modules: {n}"
  -- every constant reachable from the statements
  let mut checked : NameSet := {}
  let mut count := 0
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if checked.contains n then continue
    checked := checked.insert n
    match envC.find? n, envS.find? n with
    | none, _ => problems := problems.push s!"not found in Challenge: {n}"
    | _, none => problems := problems.push s!"not found in Solution: {n}"
    | some c, some s =>
      count := count + 1
      if names.contains n then
        work := work ++ s.type.getUsedConstants
      else
        if c != s then problems := problems.push s!"constant differs: {n}"
        work := work ++ (usedConsts s).filter (!checked.contains ·)
  -- axioms of the Solution's theorems
  let mut axWork : Array Name := names
  let mut axSeen : NameSet := {}
  let mut axioms : NameSet := {}
  while !axWork.isEmpty do
    let n := axWork.back!
    axWork := axWork.pop
    if axSeen.contains n then continue
    axSeen := axSeen.insert n
    match envS.find? n with
    | none => problems := problems.push s!"not found in Solution: {n}"
    | some info =>
      if info matches .axiomInfo _ then
        axioms := axioms.insert n
        unless permitted.contains n do problems := problems.push s!"illegal axiom: {n}"
      axWork := axWork ++ (usedConsts info).filter (!axSeen.contains ·)
  for p in problems do IO.println p
  IO.println s!"{names.size} theorems, {count} reachable constants compared, axioms used: \
    {axioms.toList}, {problems.size} problems"
  return if problems.isEmpty then 0 else 1
