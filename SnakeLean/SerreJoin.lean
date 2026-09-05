/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Meets and joins of Serre classes

This module is about abelian categories, not about the 2-categorical development. It supports
Section 8, and in particular Proposition 8.11 `P:DIabcat` and Proposition 8.12 `P:AbCatFails`,
which together settle whether the 2-category `AbCat` of abelian categories, exact functors and
natural transformations is 2-di-exact. It is not.

Mathlib has `ObjectProperty.IsSerreClass`, but records no closure of Serre classes under the
lattice operations. Both are needed to state where (DI2) bites in `AbCat`.

## Main results

* `IsSerreClass.inf`, `isSerreClass_iInf` — Serre classes are closed under meets.
* `serreJoin` — the smallest Serre class containing two given ones.
* `serreSaturation` — the `S`-saturation of `K`, Definition 8.8 `D:Saturation`; with
  `serreSaturation_le` and `isSerreClass_serreSaturation_iff`, the clauses of Proposition 8.9
  `P:Saturation` that Proposition 8.11 `P:DIabcat` consumes (its closure under subobjects and
  under quotients is not formalised).
* `isSerreClass_serreSaturation_of_twoStep` — Proposition 8.19 `P:TwoStep`.
* `isSerreClass_inverseImage` — a Serre class pulls back along an exact functor.
-/

universe v v' u u'

namespace CategoryTheory

open Limits ZeroObject

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]

section Meet

variable (P Q : ObjectProperty C) [P.IsSerreClass] [Q.IsSerreClass]

instance : (P ⊓ Q).IsClosedUnderSubobjects where
  prop_of_mono := by
    intro X Y f hf hY
    haveI := hf
    exact ⟨P.prop_of_mono f hY.1, Q.prop_of_mono f hY.2⟩

instance : (P ⊓ Q).IsClosedUnderQuotients where
  prop_of_epi := by
    intro X Y f hf hX
    haveI := hf
    exact ⟨P.prop_of_epi f hX.1, Q.prop_of_epi f hX.2⟩

instance : (P ⊓ Q).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ :=
    ⟨P.prop_X₂_of_shortExact hS h₁.1 h₃.1, Q.prop_X₂_of_shortExact hS h₁.2 h₃.2⟩

instance : (P ⊓ Q).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, P.prop_zero, Q.prop_zero⟩

/-- **The meet of two Serre classes is a Serre class.** Mathlib has `IsSerreClass` but no
closure of it under the lattice operations. This is what makes `K ⊓ S` available, and with it
the Serre quotient `K / (K ⊓ S)` that the factorisation of `K ↪ X ↠ X/S` needs. -/
instance : (P ⊓ Q).IsSerreClass where

end Meet

section Join

variable (P Q : ObjectProperty C)

/-- The **join** of two object properties: the smallest Serre class containing both, defined
directly by its universal property rather than as a lattice-theoretic infimum. -/
def serreJoin : ObjectProperty C :=
  fun X => ∀ (R : ObjectProperty C), R.IsSerreClass → P ≤ R → Q ≤ R → R X

lemma serreJoin_iff (X : C) :
    P.serreJoin Q X ↔
      ∀ (R : ObjectProperty C), R.IsSerreClass → P ≤ R → Q ≤ R → R X := Iff.rfl

lemma le_serreJoin_left : P ≤ P.serreJoin Q := fun _ hX _ _ hP _ => hP _ hX

lemma le_serreJoin_right : Q ≤ P.serreJoin Q := fun _ hX _ _ _ hQ => hQ _ hX

/-- The join is least among the Serre classes containing both. -/
lemma serreJoin_le {R : ObjectProperty C} (hR : R.IsSerreClass) (hP : P ≤ R) (hQ : Q ≤ R) :
    P.serreJoin Q ≤ R := fun _ hX => hX R hR hP hQ

instance : (P.serreJoin Q).IsClosedUnderSubobjects where
  prop_of_mono := by
    intro X Y f hf hY R hR hP hQ
    haveI := hf
    haveI := hR
    exact R.prop_of_mono f (hY R hR hP hQ)

instance : (P.serreJoin Q).IsClosedUnderQuotients where
  prop_of_epi := by
    intro X Y f hf hX R hR hP hQ
    haveI := hf
    haveI := hR
    exact R.prop_of_epi f (hX R hR hP hQ)

instance : (P.serreJoin Q).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := fun R hR hP hQ => by
    haveI := hR; exact R.prop_X₂_of_shortExact hS (h₁ R hR hP hQ) (h₃ R hR hP hQ)

instance : (P.serreJoin Q).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, fun R hR _ _ => by haveI := hR; exact R.prop_zero⟩

/-- **The join of two Serre classes is a Serre class.** -/
instance : (P.serreJoin Q).IsSerreClass where

end Join


section Transfer

variable (R : ObjectProperty C) [R.IsSerreClass]

/-- **Membership in a Serre class transfers along an isomorphism modulo that class.** If the
kernel and cokernel of `f : X ⟶ Y` both lie in `R`, then `X` lies in `R` exactly when `Y` does.

The proof needs no image factorisation: `R.isoModSerre` is multiplicative, and composing `f`
with a zero morphism on either side turns the statement into `isoModSerre_zero_iff`. -/
lemma prop_iff_of_isoModSerre {X Y : C} {f : X ⟶ Y} (hf : R.isoModSerre f) : R X ↔ R Y := by
  constructor
  · intro hX
    have h₀ : R.isoModSerre (0 : (0 : C) ⟶ X) := (R.isoModSerre_zero_iff _ _).2 ⟨R.prop_zero, hX⟩
    have := R.isoModSerre.comp_mem _ _ h₀ hf
    rw [show (0 : (0 : C) ⟶ X) ≫ f = 0 by simp, R.isoModSerre_zero_iff] at this
    exact this.2
  · intro hY
    have h₀ : R.isoModSerre (0 : Y ⟶ (0 : C)) := (R.isoModSerre_zero_iff _ _).2 ⟨hY, R.prop_zero⟩
    have := R.isoModSerre.comp_mem _ _ hf h₀
    rw [show f ≫ (0 : Y ⟶ (0 : C)) = 0 by simp, R.isoModSerre_zero_iff] at this
    exact this.1

lemma isoModSerre_mono {P : ObjectProperty C} [P.IsSerreClass] (h : P ≤ R) {X Y : C}
    {f : X ⟶ Y} (hf : P.isoModSerre f) : R.isoModSerre f :=
  ⟨h _ hf.1, h _ hf.2⟩

end Transfer

section Saturation

variable (S K : ObjectProperty C) [S.IsSerreClass] [K.IsSerreClass]

/-- The **`S`-saturation of `K`**, Definition 8.8 `D:Saturation` in its second form: the
objects joined to an object of `K` by a span of morphisms that are isomorphisms modulo `S`.

Under the correspondence with the Serre quotient, `serreSaturation S K` is the preimage of the
essential image of `K` in `C / S`; an object satisfies it exactly when it becomes isomorphic in
`C / S` to an object of `K`. Equivalently it is the class of objects carrying a three-step
filtration with successive subquotients in `S`, `K` and `S`. -/
def serreSaturation : ObjectProperty C :=
  fun X => ∃ (A D : C) (f : D ⟶ A) (g : D ⟶ X), K A ∧ S.isoModSerre f ∧ S.isoModSerre g

omit [K.IsSerreClass] in
lemma le_serreSaturation : K ≤ serreSaturation S K :=
  fun _ hX => ⟨_, _, 𝟙 _, 𝟙 _, hX, S.isoModSerre_of_isIso _, S.isoModSerre_of_isIso _⟩

lemma serre_le_serreSaturation : S ≤ serreSaturation S K :=
  fun _ hX => ⟨0, 0, 𝟙 0, 0, K.prop_zero, S.isoModSerre_of_isIso _,
    (S.isoModSerre_zero_iff _ _).2 ⟨S.prop_zero, hX⟩⟩

omit [K.IsSerreClass] in
/-- **The saturation is contained in every Serre class containing `K` and `S`** — the clause
of Proposition 8.9 `P:Saturation` that the reduction needs. This is the whole of the chase, and
`prop_iff_of_isoModSerre` does it twice. `K` need not be a Serre class for this: the linter
reports the hypothesis as unused, and it is. -/
lemma serreSaturation_le {R : ObjectProperty C} [R.IsSerreClass] (hK : K ≤ R) (hS : S ≤ R) :
    serreSaturation S K ≤ R := by
  rintro X ⟨A, D, f, g, hA, hf, hg⟩
  have hD : R D := (R.prop_iff_of_isoModSerre (R.isoModSerre_mono hS hf)).2 (hK _ hA)
  exact (R.prop_iff_of_isoModSerre (R.isoModSerre_mono hS hg)).1 hD

omit [K.IsSerreClass] in
omit [K.IsSerreClass] in
lemma serreSaturation_of_iso {X Y : C} (e : X ≅ Y) (hX : serreSaturation S K X) :
    serreSaturation S K Y := by
  obtain ⟨A, D, f, g, hA, hf, hg⟩ := hX
  exact ⟨A, D, f, g ≫ e.hom, hA, hf,
    S.isoModSerre.comp_mem _ _ hg (S.isoModSerre_of_isIso _)⟩

instance : (serreSaturation S K).IsClosedUnderIsomorphisms where
  of_iso e hX := serreSaturation_of_iso S K e hX

omit [K.IsSerreClass] in
lemma serreSaturation_le_serreJoin : serreSaturation S K ≤ K.serreJoin S :=
  serreSaturation_le S K (K.le_serreJoin_left S) (K.le_serreJoin_right S)

/-- **The reduction**, the last clause of Proposition 8.9 `P:Saturation`: the `S`-saturation of
`K` is a Serre class exactly when it is the join of `K` and `S`.

This is where condition (DI2) bites in `AbCat`, by Proposition 8.11 `P:DIabcat`. A normal
2-monomorphism followed by a normal 2-epimorphism is `K ↪ C ↠ C/S` for Serre classes `K` and
`S`; it factors as the Serre quotient `K ↠ K/(K ⊓ S)` followed by a fully faithful exact functor
into `C/S` (Lemma 8.10 `L:FullyFaithful`) whose essential image is `serreSaturation S K`. That
second factor is a normal 2-monomorphism precisely when its essential image is a Serre
subcategory of `C/S`, which is the left-hand side below. The reduction itself, through Serre
quotients and Gabriel's correspondence, is not formalised; this theorem is the abelian-category
statement it lands on. -/
theorem isSerreClass_serreSaturation_iff :
    (serreSaturation S K).IsSerreClass ↔ serreSaturation S K = K.serreJoin S := by
  constructor
  · intro h
    exact le_antisymm (serreSaturation_le_serreJoin S K)
      (K.serreJoin_le S h (le_serreSaturation S K) (serre_le_serreSaturation S K))
  · intro h
    rw [h]
    infer_instance

end Saturation


section TwoStep

variable (S K : ObjectProperty C) [S.IsSerreClass] [K.IsSerreClass]

/-- `c` admits an **`S`-then-`K` presentation**: an epimorphism onto an object of `K` whose
kernel lies in `S`, that is, a two-step filtration with steps in `S` and `K`. -/
def TwoStepSK : ObjectProperty C :=
  fun c => ∃ (a : C) (p : c ⟶ a), Epi p ∧ K a ∧ S (kernel p)

/-- `c` admits a **`K`-then-`S` presentation**: a subobject in `K` with quotient in `S`. -/
def TwoStepKS : ObjectProperty C :=
  fun c => ∃ (b : C) (i : b ⟶ c), Mono i ∧ K b ∧ S (cokernel i)

omit [K.IsSerreClass] in
/-- A two-step filtration is a three-step filtration with an empty last step. -/
lemma serreSaturation_of_twoStepSK {c : C} (h : TwoStepSK S K c) : serreSaturation S K c := by
  obtain ⟨a, p, hp, hK, hS⟩ := h
  haveI := hp
  exact ⟨a, c, p, 𝟙 c, hK, S.isoModSerre_of_epi p hS, S.isoModSerre_of_isIso _⟩

omit [K.IsSerreClass] in
/-- Dually, with an empty first step. -/
lemma serreSaturation_of_twoStepKS {c : C} (h : TwoStepKS S K c) : serreSaturation S K c := by
  obtain ⟨b, i, hi, hK, hS⟩ := h
  haveI := hi
  exact ⟨b, b, 𝟙 b, i, hK, S.isoModSerre_of_isIso _, S.isoModSerre_of_mono i hS⟩

/-- **Proposition 8.19 `P:TwoStep`.** If every object of the join admits a two-step filtration,
in either order, then the saturation is a Serre class.

The proof is the paper's: a two-step filtration is a three-step one with an empty step, so the
join is contained in the saturation, and the reverse containment is `serreSaturation_le`. This
is the form in which the condition is verifiable, and the paper applies it once, in Proposition
8.21 `P:ASimplies` (`isSerreClass_serreSaturation_of_condAS`), with the `S`-then-`K`
presentation whose subobject is a maximal subobject lying in `S`. -/
theorem isSerreClass_serreSaturation_of_twoStep
    (h : ∀ c : C, K.serreJoin S c → TwoStepSK S K c ∨ TwoStepKS S K c) :
    (serreSaturation S K).IsSerreClass := by
  rw [isSerreClass_serreSaturation_iff]
  refine le_antisymm (serreSaturation_le_serreJoin S K) (fun c hc => ?_)
  rcases h c hc with h' | h'
  · exact serreSaturation_of_twoStepSK S K h'
  · exact serreSaturation_of_twoStepKS S K h'

end TwoStep


section ExactFunctor

variable {D : Type u'} [Category.{v'} D] [Abelian D]
  (P : ObjectProperty D) [P.IsSerreClass] (F : C ⥤ D) [F.PreservesZeroMorphisms]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]

instance : (P.inverseImage F).ContainsZero where
  exists_zero :=
    ⟨0, isZero_zero _, P.prop_of_isZero (F.mapZeroObject.isZero_iff.2 (isZero_zero _))⟩

instance : (P.inverseImage F).IsClosedUnderSubobjects where
  prop_of_mono := by
    intro X Y f hf hY
    haveI := hf
    exact P.prop_of_mono (F.map f) hY

instance : (P.inverseImage F).IsClosedUnderQuotients where
  prop_of_epi := by
    intro X Y f hf hX
    haveI := hf
    exact P.prop_of_epi (F.map f) hX

instance : (P.inverseImage F).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := P.prop_X₂_of_shortExact (hS.map_of_exact F) h₁ h₃

/-- **A Serre class pulls back along an exact functor.** Nothing but exactness is used, so this
covers both the inclusion of a Serre subcategory and the projection onto a Serre quotient. -/
instance isSerreClass_inverseImage : (P.inverseImage F).IsSerreClass where

end ExactFunctor

end ObjectProperty

end CategoryTheory
