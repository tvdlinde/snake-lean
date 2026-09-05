/-
Dump the dependency table of every declaration of this development, for `genblueprint.py`.

Run from the repository root:

    lake env lean blueprint/deps.lean > blueprint/deps.tsv

Each line is `name <TAB> constants of the statement <TAB> constants of the proof`, both
restricted to declarations of this development and space-separated.  The split is what
leanblueprint wants: a declaration's type is its statement, so the constants of the type
are its statement dependencies (`\uses` in the statement, feeding `can_state`), and the
constants of the value that are not already in the type are what the proof needed
(`\uses` in the proof, feeding `can_prove`).

Membership is by *defining module*, not by namespace: the abelian-category modules of
Section 8 declare into `CategoryTheory` and `ObjectProperty`, and a namespace filter
misses all of them.

This is the dependency structure of the *Lean* proof, which is not always the paper's.
Where the two differ the graph shows the Lean route.
-/
import SnakeLean
open Lean

run_cmd do
  let env ← Elab.Command.liftCoreM getEnv
  let ours (n : Name) : Bool :=
    match env.getModuleFor? n with
    | some m => (`SnakeLean).isPrefixOf m
    | none   => false
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal || !ours n then continue
    let keep (s : NameSet) : List Name := s.toList.filter fun m => !m.isInternal && ours m
    let tdeps := keep ci.type.getUsedConstantsAsSet
    let tset : NameSet := tdeps.foldl (·.insert ·) {}
    let vdeps := match ci.value? with
      | some v => (keep v.getUsedConstantsAsSet).filter fun m => !tset.contains m
      | none   => []
    let fmt (l : List Name) : String := String.intercalate " " (l.map toString)
    out := out.push s!"{n}\t{fmt tdeps}\t{fmt vdeps}"
  IO.println (String.intercalate "\n" out.toList)
