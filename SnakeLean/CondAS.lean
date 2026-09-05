/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Noetherian
import SnakeLean.SerreJoin

/-!
# Condition (AS), and when the saturation of a Serre class is again a Serre class

This module, like `SnakeLean.SerreJoin`, is about abelian categories rather than about the
2-categorical development: it is Section 8.18 `SS:ModelAS` of the paper, where the saturated
abelian categories of Section 8.14 `SS:ModelSAT` are produced.

By Proposition 8.11 `P:DIabcat`, condition (DI2) for a 2-category of abelian categories asks
that the `S`-saturation of a Serre class `K` be a Serre class — that the category be *saturated*,
Definition 8.15 `D:SAT`. That fails in general — Proposition 8.12 `P:AbCatFails`. Condition
**(AS)**, Definition 8.20 `D:AS`, is what separates the categories in which it holds:

> for every Serre class `T` and every object `X`, if every nonzero subobject of `X` has a nonzero
> subobject in `T`, then `X` lies in `T`.

For finitely generated modules over a commutative noetherian ring, and for coherent sheaves on a
noetherian scheme, (AS) is the classical statement that the support of an object is the
specialisation-closure of its associated points. In the language of Kanda's atom spectrum
[R. Kanda, *Classifying Serre subcategories via atom spectrum*, Adv. Math. **231** (2012),
1572-1588] it says that `ASupp M` is determined by `AAss M`: Serre classes correspond to the open
subclasses of `ASpec` (Kanda, Theorem 4.3), an atom lies in the open subclass of `T` exactly when
one of its monoform representatives has a nonzero subobject in `T`, and every nonzero subobject of
a noetherian object has a monoform subobject (Kanda, Theorem 2.9). Remark 8.22 `R:Atoms` is that
dictionary, with the two traps it walks into; the formulation above mentions no atoms, and is what
the proofs below consume.

## Main results

* `CondAS` — condition (AS), Definition 8.20 `D:AS`.
* `exists_nonzeroSub_of_serreJoin` — a nonzero object of the join of `K` and `S` has a nonzero
  subobject lying in `K` or in `S`. The paper reads this off the first nonzero step of a finite
  filtration with subquotients in `K` or `S`; here the Serre class that does the work is
  `SQEssential`, and its closure under extensions is the one real diagram chase in this file.
* `exists_maximalSerreSub` — a noetherian object has a maximal subobject lying in `S`.
* `exists_epi_torsionFree` — hence an epimorphism onto an object with no nonzero subobject in `S`,
  whose kernel lies in `S`: the paper's `M ↠ N = M/M₁`.
* `isSerreClass_serreSaturation_of_condAS` — **Proposition 8.21 `P:ASimplies`**: a noetherian
  abelian category satisfying (AS) is saturated, for every pair `K`, `S` at once.
* `prop_of_condAS_of_forall_mono` — the shape (AS) takes in Remark 8.28 `Rem WhereNot`: an object
  each of whose nonzero subobjects receives a mono from a fixed `Y` lies in every Serre class
  containing `Y`.

## Elsewhere, and not formalised

That the finitely generated modules over a commutative noetherian ring satisfy (AS), Proposition
8.24 `P:ModAS`, is `SnakeLean.CondASModule`. Not formalised: the classification of Serre classes
by atom spectra (Remark 8.22, which the paper uses nowhere either); that `Coh X` satisfies (AS),
Lemma 8.25 `L:OneAss` and Proposition 8.26 `P:CohAS`; and the counterexample of Proposition 8.12
itself, which lives in a Serre quotient category and so is out of reach until Mathlib knows that
Serre quotients are abelian.
-/

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

section Subquotient

/-- `Z` is a **subquotient** of `X`: a quotient object of a subobject of `X`. -/
def IsSubquotient (Z X : C) : Prop :=
  ∃ (Y : C) (i : Y ⟶ X) (p : Y ⟶ Z), Mono i ∧ Epi p

omit [Abelian C] in
lemma IsSubquotient.refl (X : C) : IsSubquotient X X :=
  ⟨X, 𝟙 X, 𝟙 X, inferInstance, inferInstance⟩

omit [Abelian C] in
lemma IsSubquotient.of_mono {Z X : C} (i : Z ⟶ X) (hi : Mono i) : IsSubquotient Z X :=
  ⟨Z, i, 𝟙 Z, hi, inferInstance⟩

omit [Abelian C] in
lemma IsSubquotient.of_epi {Z X : C} (p : X ⟶ Z) (hp : Epi p) : IsSubquotient Z X :=
  ⟨X, 𝟙 X, p, inferInstance, hp⟩

/-- **A subobject of a quotient is a quotient of a subobject.** The pullback does it: it is mono
over the source because `i` is, and epi onto `Z` because `p` is and the category is abelian. -/
lemma exists_mono_epi_of_epi_mono {A B Z : C} (p : A ⟶ B) (i : Z ⟶ B) [Epi p] [Mono i] :
    ∃ (W : C) (j : W ⟶ A) (q : W ⟶ Z), Mono j ∧ Epi q :=
  ⟨pullback p i, pullback.fst p i, pullback.snd p i, inferInstance, inferInstance⟩

lemma IsSubquotient.trans {Z Y X : C} (h₁ : IsSubquotient Z Y) (h₂ : IsSubquotient Y X) :
    IsSubquotient Z X := by
  obtain ⟨Y', i₁, p₁, hi₁, hp₁⟩ := h₁
  obtain ⟨X', i₂, p₂, hi₂, hp₂⟩ := h₂
  haveI := hi₁; haveI := hp₁; haveI := hi₂; haveI := hp₂
  obtain ⟨W, j, q, hj, hq⟩ := exists_mono_epi_of_epi_mono p₂ i₁
  haveI := hj; haveI := hq
  exact ⟨W, j ≫ i₂, q ≫ p₁, inferInstance, inferInstance⟩

end Subquotient

namespace ObjectProperty

section Essential

variable (P : ObjectProperty C)

/-- Some nonzero subobject of `X` lies in `P`. -/
def HasNonzeroSub (X : C) : Prop :=
  ∃ (Y : C) (i : Y ⟶ X), Mono i ∧ ¬ IsZero Y ∧ P Y

/-- Every nonzero subobject of `X` has a nonzero subobject in `P`; that is, `P` meets every
nonzero subobject of `X`. -/
def SubEssential (X : C) : Prop :=
  ∀ ⦃Y : C⦄ (i : Y ⟶ X), Mono i → ¬ IsZero Y → P.HasNonzeroSub Y

/-- Every nonzero *subquotient* of `X` has a nonzero subobject in `P`. Unlike `SubEssential` this
is a Serre class, which is the only reason it is here. -/
def SQEssential : ObjectProperty C :=
  fun X => ∀ ⦃Z : C⦄, IsSubquotient Z X → ¬ IsZero Z → P.HasNonzeroSub Z

omit [Abelian C] in
lemma subEssential_of_sqEssential {X : C} (h : P.SQEssential X) : P.SubEssential X :=
  fun _ i hi => h (IsSubquotient.of_mono i hi)

omit [Abelian C] in
/-- The converse half of condition (AS), which holds always: a Serre class meets every nonzero
subobject of each of its own objects. So (AS) makes `SubEssential T` and `T` the same property,
and is in particular not vacuous. -/
lemma subEssential_of_prop [P.IsClosedUnderSubobjects] {X : C} (hX : P X) : P.SubEssential X :=
  fun _ i _ hi0 => ⟨_, 𝟙 _, inferInstance, hi0, P.prop_of_mono i hX⟩

instance : (P.SQEssential).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, by
    rintro Z ⟨Y, i, p, hi, hp⟩ hZ
    haveI := hi; haveI := hp
    exact (hZ (IsZero.of_epi p (IsZero.of_mono i (isZero_zero C)))).elim⟩

instance : (P.SQEssential).IsClosedUnderSubobjects where
  prop_of_mono := by
    intro X Y f hf hY
    haveI := hf
    exact fun Z hZ hZ0 => hY (hZ.trans (IsSubquotient.of_mono f hf)) hZ0

instance : (P.SQEssential).IsClosedUnderQuotients where
  prop_of_epi := by
    intro X Y f hf hX
    haveI := hf
    exact fun Z hZ hZ0 => hX (hZ.trans (IsSubquotient.of_epi f hf)) hZ0

/-- **`SQEssential P` is closed under extensions**, and this is the only diagram chase here.
A nonzero subquotient `Z` of the middle term is cut by the subobject: writing `Y ↣ X₂ ↠ Z` for
the subquotient and `k` for the kernel of `Y ⟶ X₃`, either `k ≫ e` is nonzero, and its image is a
nonzero subquotient of `X₁` inside `Z`, or it vanishes, and then `Z` is a quotient of the coimage
of `Y ⟶ X₃`, hence a subquotient of `X₃`. -/
instance : (P.SQEssential).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    rintro Z ⟨Y, y, e, hy, he⟩ hZ0
    haveI := hy; haveI := he; haveI := hT.mono_f; haveI := hT.epi_g
    by_cases hke : kernel.ι (y ≫ T.g) ≫ e = 0
    · refine h₃ ⟨Abelian.coimage (y ≫ T.g), Abelian.factorThruCoimage (y ≫ T.g),
        cokernel.desc _ e hke, inferInstance, ?_⟩ hZ0
      exact epi_of_epi_fac (cokernel.π_desc (kernel.ι (y ≫ T.g)) e hke)
    · have hlift : (kernel.ι (y ≫ T.g) ≫ y) ≫ T.g = 0 := by
        rw [Category.assoc]; exact kernel.condition (y ≫ T.g)
      have hmf : hT.exact.lift _ hlift ≫ T.f = kernel.ι (y ≫ T.g) ≫ y :=
        hT.exact.lift_f _ hlift
      haveI : Mono (hT.exact.lift _ hlift) := by
        have h : Mono (hT.exact.lift _ hlift ≫ T.f) := by rw [hmf]; infer_instance
        exact mono_of_mono _ T.f
      have hW : ¬ IsZero (Abelian.image (kernel.ι (y ≫ T.g) ≫ e)) := by
        intro h
        refine hke ?_
        rw [← Abelian.image.fac (kernel.ι (y ≫ T.g) ≫ e),
          h.eq_zero_of_src (Abelian.image.ι _), comp_zero]
      obtain ⟨V, v, hv, hv0, hvP⟩ :=
        h₁ ⟨kernel (y ≫ T.g), hT.exact.lift _ hlift,
          Abelian.factorThruImage (kernel.ι (y ≫ T.g) ≫ e), inferInstance, inferInstance⟩ hW
      haveI := hv
      exact ⟨V, v ≫ Abelian.image.ι _, inferInstance, hv0, hvP⟩

instance : (P.SQEssential).IsSerreClass where

omit [Abelian C] in
/-- A class closed under subobjects and quotients is `SQEssential` for any class containing it. -/
lemma le_sqEssential {Q : ObjectProperty C} [Q.IsClosedUnderSubobjects]
    [Q.IsClosedUnderQuotients] (h : Q ≤ P) : Q ≤ P.SQEssential := by
  rintro X hX Z ⟨Y, i, p, hi, hp⟩ hZ0
  haveI := hi; haveI := hp
  exact ⟨Z, 𝟙 Z, inferInstance, hZ0, h _ (Q.prop_of_epi p (Q.prop_of_mono i hX))⟩

end Essential

section Join

variable (K S : ObjectProperty C) [K.IsSerreClass] [S.IsSerreClass]

/-- **A nonzero object of the join has a nonzero subobject in `K` or in `S`.**

The join is the smallest Serre class containing both, so it suffices to exhibit a Serre class
with that property, and `SQEssential` of the union is one: the subquotients are what make it
closed under quotients as well as subobjects. -/
theorem exists_nonzeroSub_of_serreJoin {X : C} (hX : K.serreJoin S X) (hX0 : ¬ IsZero X) :
    ∃ (Y : C) (i : Y ⟶ X), Mono i ∧ ¬ IsZero Y ∧ (K Y ∨ S Y) := by
  let P : ObjectProperty C := fun Y => K Y ∨ S Y
  have h := K.serreJoin_le S (R := P.SQEssential) inferInstance
    (le_sqEssential P (fun _ h => Or.inl h)) (le_sqEssential P (fun _ h => Or.inr h)) X hX
  exact h (IsSubquotient.refl X) hX0

end Join

section Torsion

variable (S : ObjectProperty C) [S.IsSerreClass]

/-- **A noetherian object has a maximal subobject lying in `S`.** Maximality is all that is
needed below; that the maximal one is the largest, which would need the sum of two subobjects in
`S` to lie in `S`, is not used. -/
lemma exists_maximalSerreSub (M : C) [IsNoetherianObject M] :
    ∃ (A : C) (a : A ⟶ M), Mono a ∧ S A ∧
      ∀ ⦃B : C⦄ (b : B ⟶ M), Mono b → S B → (∃ u : A ⟶ B, u ≫ b = a) → ∃ v : B ⟶ A, v ≫ a = b := by
  have hne : {A : Subobject M | S (A : C)}.Nonempty :=
    ⟨⊥, S.prop_of_iso (Subobject.botCoeIsoZero (B := M)).symm S.prop_zero⟩
  obtain ⟨A, hA, hmax⟩ :=
    (IsWellFounded.wf (r := ((· > ·) : Subobject M → Subobject M → Prop))).has_min _ hne
  refine ⟨(A : C), A.arrow, inferInstance, hA, ?_⟩
  rintro B b hb hB ⟨u, hu⟩
  haveI := hb
  have hAB : A ≤ Subobject.mk b := Subobject.le_mk_of_comm u hu
  have hBA : Subobject.mk b ≤ A := by
    have := eq_of_le_of_not_lt hAB (hmax (Subobject.mk b)
      (S.prop_of_iso (Subobject.underlyingIso b).symm hB))
    exact this.ge
  refine ⟨(Subobject.underlyingIso b).inv ≫ Subobject.ofLE _ _ hBA, ?_⟩
  rw [Category.assoc, Subobject.ofLE_arrow, Subobject.underlyingIso_arrow]

/-- **The `S`-torsion presentation.** Every noetherian object admits an epimorphism whose kernel
lies in `S` and whose target has no nonzero subobject in `S`.

The target is the cokernel of a maximal subobject in `S`: a nonzero subobject of it in `S` pulls
back to a strictly larger subobject of `M` in `S`, because `S` is closed under extensions and
`isoModSerre` is stable under base change. -/
theorem exists_epi_torsionFree (M : C) [IsNoetherianObject M] :
    ∃ (N : C) (π : M ⟶ N), Epi π ∧ S (kernel π) ∧
      ∀ ⦃Z : C⦄ (z : Z ⟶ N), Mono z → S Z → IsZero Z := by
  obtain ⟨A, a, ha, hA, hmax⟩ := exists_maximalSerreSub S M
  haveI := ha
  refine ⟨cokernel a, cokernel.π a, inferInstance, ?_, ?_⟩
  · exact S.prop_of_iso (asIso (Abelian.factorThruImage a)) hA
  · intro Z z hz hZ
    haveI := hz
    have hπ : S.isoModSerre (cokernel.π a) :=
      S.isoModSerre_of_epi _ (S.prop_of_iso (asIso (Abelian.factorThruImage a)) hA)
    have hsnd : S.isoModSerre (pullback.snd (cokernel.π a) z) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hπ
    have hpb : S (pullback (cokernel.π a) z) := (S.prop_iff_of_isoModSerre hsnd).2 hZ
    obtain ⟨v, hv⟩ := hmax (pullback.fst (cokernel.π a) z) inferInstance hpb
      ⟨pullback.lift a 0 (by simp), by simp⟩
    have hz0 : z = 0 := by
      refine zero_of_epi_comp (pullback.snd (cokernel.π a) z) ?_
      rw [← pullback.condition, ← hv, Category.assoc, cokernel.condition, comp_zero]
    exact IsZero.of_mono_eq_zero z hz0

end Torsion

section CondAS

variable (C) in
/-- **Condition (AS), Definition 8.20 `D:AS`.** Every Serre class that meets every nonzero
subobject of `X` contains `X`.

Over a commutative noetherian ring this is the statement that a module whose associated primes
all lie in a specialisation-closed set is supported there, and it is what fails in the
counterexample of Proposition 8.12 `P:AbCatFails` (Remark 8.28 `Rem WhereNot`). -/
def CondAS : Prop :=
  ∀ (T : ObjectProperty C), T.IsSerreClass → ∀ ⦃X : C⦄, T.SubEssential X → T X

variable (S K : ObjectProperty C) [S.IsSerreClass] [K.IsSerreClass]

/-- **Proposition 8.21 `P:ASimplies`.** A noetherian abelian category satisfying (AS) is
saturated: the `S`-saturation of `K` is a Serre class, for every pair of Serre classes `K` and
`S`.

The proof is the paper's. The presentation demanded by Proposition 8.19
(`isSerreClass_serreSaturation_of_twoStep`) is the quotient by a maximal subobject lying in `S`
(`exists_epi_torsionFree`): its target has no nonzero subobject in `S`, so by
`exists_nonzeroSub_of_serreJoin` every nonzero subobject of it has a nonzero subobject in `K`,
and (AS) puts it in `K`. -/
theorem isSerreClass_serreSaturation_of_condAS [∀ X : C, IsNoetherianObject X]
    (hAS : CondAS C) : (serreSaturation S K).IsSerreClass := by
  refine isSerreClass_serreSaturation_of_twoStep S K (fun c hc => Or.inl ?_)
  obtain ⟨N, π, hπ, hker, htf⟩ := exists_epi_torsionFree S c
  haveI := hπ
  refine ⟨N, π, hπ, ?_, hker⟩
  refine hAS K inferInstance (fun W w hw hw0 => ?_)
  haveI := hw
  have hWjoin : K.serreJoin S W :=
    (K.serreJoin S).prop_of_mono w ((K.serreJoin S).prop_of_epi π hc)
  obtain ⟨V, v, hv, hv0, hV⟩ := exists_nonzeroSub_of_serreJoin K S hWjoin hw0
  haveI := hv
  refine ⟨V, v, hv, hv0, hV.resolve_right (fun hVS => hv0 ?_)⟩
  exact htf (v ≫ w) inferInstance hVS

variable {S K}

/-- **The shape (AS) takes in Remark 8.28 `Rem WhereNot`.** If every nonzero subobject of `X`
receives a monomorphism from a fixed nonzero `Y`, then `X` lies in every Serre class containing
`Y`.

In the counterexample of Proposition 8.12 `P:AbCatFails`, `Y` is the simple socle of a uniserial
object `X` of length three whose other composition factor is a different simple, and the Serre
class is the one generated by `Y`; so (AS) fails there, and fails for the same reason the
counterexample works. -/
theorem prop_of_condAS_of_forall_mono (hAS : CondAS C) (T : ObjectProperty C) [T.IsSerreClass]
    {Y X : C} (hY : T Y) (hY0 : ¬ IsZero Y)
    (h : ∀ ⦃W : C⦄ (w : W ⟶ X), Mono w → ¬ IsZero W → ∃ y : Y ⟶ W, Mono y) : T X :=
  hAS T inferInstance (fun W w hw hw0 => by
    obtain ⟨y, hy⟩ := h w hw hw0
    exact ⟨Y, y, hy, hY0, hY⟩)

end CondAS

end ObjectProperty

end CategoryTheory
