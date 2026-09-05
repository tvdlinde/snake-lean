/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.LatticeNSD
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.DeriveFintype

/-!
# The pentagon: `Sup` is neither 2-di-exact nor (DPN)

The last clauses of Proposition 8.36 `P:SupModular` and Proposition 8.38 `P:SupNotDPN`, and the
five-element witness of Remark 9.5 `Rem NSD Strict`. The 2-category `Sup` of all complete
lattices (`SupAll`) is homologically self-dual, and its normal 2-monomorphisms and normal
2-epimorphisms compose (`SnakeLean.LatticeNSD.isHSD_sup`, `normalEpiCompSup`,
`normalMonoCompSup`); this module adds what those leave out, that it satisfies neither condition
(DI2) nor condition (DPN). Both negations come down to one lattice, by the two biconditionals of
Proposition 9.29 `P:SupClass`: `Sup_C` is 2-di-exact exactly when every member of `C` is modular
(`twoDiExact_iff_forall_isModularLattice`) and satisfies (DPN) exactly when every member is
transposition-symmetric (`dpn_iff_forall_transpositionSymmetric`). The pentagon `N₅` is neither.

`Pentagon` is `N₅ = {⊥, x, z, y, ⊤}` with `⊥ < x < z < ⊤` and `y` incomparable to `x` and `z`,
as in the paper's proof of `P:SupNotDPN`; Mathlib has no such lattice, so it is built here, its
order a Boolean table and every axiom discharged by `decide`. The two facts that matter are
decided the same way: the transposition of `y` and `z` is invertible (`transposes_y_z`, both
intervals being two-element chains) while the transposition of `z` and `y` is not
(`not_transposes_z_y`, a three-element chain onto a two-element one). Read through
`isNormal_segIncl_comp_upProj_iff`, these say that the antinormal 1-cell `c_{z,y} : ↓z ⟶ ↑y` of
`Sup` is not normal while its dinversion `c_{y,z}` is (`not_isNormal_pentagon`,
`isNormal_pentagon_dinversion`) — exactly the paper's witness pair `(↓z → N₅, q_y)` — and hence
that `Sup` is not (DPN) (`not_dpn_supAll`); the first alone says that `Sup` has a non-normal
antinormal 1-cell (`exists_isAntinormal_not_isNormal`), so it is not 2-di-exact
(`not_twoDiExact_supAll`).

## Main results

* `Pentagon` — `N₅` as a complete lattice.
* `Pentagon.transposes_y_z`, `Pentagon.not_transposes_z_y` — the two transpositions; hence
  `Pentagon.not_transpositionSymmetric` and `Pentagon.not_isModularLattice`.
* `not_twoDiExact_supAll`, `exists_isAntinormal_not_isNormal` — `Sup` is not 2-di-exact, the
  last clause of `P:SupModular`.
* `not_dpn_supAll`, with `not_isNormal_pentagon` and `isNormal_pentagon_dinversion` — `Sup` is
  not (DPN), the last clause of `P:SupNotDPN`, at the paper's witness pair.

## Not formalised

Nothing of the module's own content. With `SnakeLean.LatticeNSD.isHSD_sup`, `Sup` is the
five-element separation of homological self-duality from (DPN) that `Rem NSD Strict` promises;
that `AbCat` separates them too (Section 9.21 `SS:NSDAbCat`) is a statement about Serre
quotients and is not formalised, see `SnakeLean.AbCatModel`.
-/

universe u

namespace SnakeLean

open CategoryTheory Bicategory

/-- **The pentagon `N₅`**: `⊥ < x < z < ⊤`, and `y` comparable only to `⊥` and `⊤`, so that
`x ⊔ y = z ⊔ y = ⊤` and `x ⊓ y = z ⊓ y = ⊥`. The names are those of the paper's proof of
Proposition 8.38 `P:SupNotDPN`. -/
inductive Pentagon : Type u
  | bot
  | x
  | z
  | y
  | top
  deriving DecidableEq, Fintype

namespace Pentagon

/-- The order, as a Boolean table. -/
def le : Pentagon → Pentagon → Bool
  | bot, _ => true
  | _, top => true
  | x, x => true
  | x, z => true
  | z, z => true
  | y, y => true
  | _, _ => false

instance instLE : LE Pentagon.{u} := ⟨fun a b => le a b = true⟩

instance : DecidableLE Pentagon.{u} := fun a b => inferInstanceAs (Decidable (le a b = true))

instance : PartialOrder Pentagon.{u} where
  toLE := instLE
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

/-- The join, as a table. -/
def sup : Pentagon → Pentagon → Pentagon
  | bot, a => a
  | a, bot => a
  | top, _ => top
  | _, top => top
  | x, x => x
  | x, z => z
  | z, x => z
  | z, z => z
  | y, y => y
  | _, _ => top

/-- The meet, as a table. -/
def inf : Pentagon → Pentagon → Pentagon
  | top, a => a
  | a, top => a
  | bot, _ => bot
  | _, bot => bot
  | x, x => x
  | x, z => x
  | z, x => x
  | z, z => z
  | y, y => y
  | _, _ => bot

instance : Lattice Pentagon.{u} where
  sup := sup
  inf := inf
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : BoundedOrder Pentagon.{u} where
  bot := bot
  top := top
  bot_le := by decide
  le_top := by decide

/-- A finite bounded lattice is complete. -/
noncomputable instance : CompleteLattice Pentagon.{u} := Fintype.toCompleteLattice Pentagon.{u}

/-- **The transposition of `y` and `z` is invertible**: it runs from `[y ⊓ z, y] = {⊥, y}` to
`[z, y ⊔ z] = {z, ⊤}`, two-element chain onto two-element chain. -/
theorem transposes_y_z : Transposes y.{u} z := by
  unfold Transposes
  decide

/-- **The transposition of `z` and `y` is not invertible**: it runs from `[z ⊓ y, z] = {⊥, x, z}`
to `[y, z ⊔ y] = {y, ⊤}`, and sends both `x` and `z` to `⊤`. -/
theorem not_transposes_z_y : ¬ Transposes z.{u} y := by
  unfold Transposes
  decide

/-- The pentagon is not transposition-symmetric: `y` and `z` transpose, `z` and `y` do not. -/
theorem not_transpositionSymmetric : ¬ TranspositionSymmetric Pentagon.{u} :=
  fun h => not_transposes_z_y (h y z transposes_y_z)

/-- The pentagon is not modular, by Dedekind's transposition principle
(`isModularLattice_iff_forall_transposes`). -/
theorem not_isModularLattice : ¬ IsModularLattice Pentagon.{u} :=
  fun h => not_transposes_z_y (isModularLattice_iff_forall_transposes.1 h z y)

end Pentagon

/-! ## The pentagon as an object of `Sup` -/

/-- The pentagon, as an object of the 2-category `Sup` of all complete lattices. -/
noncomputable abbrev pentagonSup : SupAll.{u} :=
  { carrier := Pentagon.{u}, mem := trivial }

/-- **`Sup` is not 2-di-exact**, the last clause of Proposition 8.36 `P:SupModular`: condition
(DI2) would make every object modular (`isModularLattice_of_twoDiExact`), and the pentagon is
not. -/
theorem not_twoDiExact_supAll : ¬ TwoDiExact (zeroSup allClass.{u}) := fun h =>
  Pentagon.not_isModularLattice (twoDiExact_iff_forall_isModularLattice.1 h pentagonSup)

/-- **`Sup` does not satisfy (DPN)**, the last clause of Proposition 8.38 `P:SupNotDPN`: condition
(DPN) would make every object transposition-symmetric (`transpositionSymmetric_of_dpn`), and
the pentagon is not. -/
theorem not_dpn_supAll : ¬ DPN (zeroSup allClass.{u}) := fun h =>
  Pentagon.not_transpositionSymmetric (dpn_iff_forall_transpositionSymmetric.1 h pentagonSup)

/-- **The paper's witness, first half**: the antinormal 1-cell `c_{z,y} : ↓z ⟶ ↑y` of the
pentagon — the composite of the antinormal pair `(↓z → N₅, q_y)` — is not normal, since `z` and
`y` do not transpose. -/
theorem not_isNormal_pentagon :
    ¬ IsNormal (zeroSup allClass.{u})
      (segIncl (L := pentagonSup) Pentagon.z ≫ upProj Pentagon.y) := fun h =>
  Pentagon.not_transposes_z_y (isNormal_segIncl_comp_upProj_iff.1 h)

/-- **The paper's witness, second half**: the dinversion of that pair, which is
`(2-ker(q_y), 2-coker(↓z → N₅)) = (↓y → N₅, q_z)` by `isTwoKernel_upProj_segIncl` and
`isTwoCokernel_segIncl_upProj`, has composite `c_{y,z} : ↓y ⟶ ↑z`, and that one is normal,
since `y` and `z` transpose. So the biconditional of condition (DPN) fails at this pair. -/
theorem isNormal_pentagon_dinversion :
    IsNormal (zeroSup allClass.{u})
      (segIncl (L := pentagonSup) Pentagon.y ≫ upProj Pentagon.z) :=
  isNormal_segIncl_comp_upProj_iff.2 Pentagon.transposes_y_z

/-- **`Sup` has an antinormal 1-cell that is not normal** — the form in which the proof of
Proposition 8.36 `P:SupModular` states the failure of condition (DI2). -/
theorem exists_isAntinormal_not_isNormal :
    ∃ (L M : SupAll.{u}) (f : L ⟶ M),
      IsAntinormal (zeroSup allClass.{u}) f ∧ ¬ IsNormal (zeroSup allClass.{u}) f :=
  ⟨_, _, segIncl (L := pentagonSup) Pentagon.z ≫ upProj Pentagon.y,
    isAntinormal_comp ⟨_, _, isTwoKernel_upProj_segIncl (L := pentagonSup) Pentagon.z⟩
      ⟨_, _, isTwoCokernel_segIncl_upProj (L := pentagonSup) Pentagon.y⟩,
    not_isNormal_pentagon⟩

end SnakeLean
