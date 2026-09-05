/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.DiExact
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# A 2-di-exact 2-category

Every result of Sections 2 to 6 is stated over a strong bizero object satisfying (DI1) and
(DI2). `AbCat`, the 2-category of abelian categories and exact functors, is not one —
Proposition 8.12 `P:AbCatFails`.

This module is Example 6.5 `Ex DiExact`, a model at the cost of being one-dimensional. Every
abelian category, viewed as a locally discrete 2-category, has a strong bizero object and
satisfies (DI2). The
verification is short because in a locally discrete 2-category the only 2-cells are identities,
so "essentially null" collapses to "zero", "2-monomorphism" to "monomorphism", and the whole of
(DI2) to the epi-mono factorisation of an abelian category.

## Main results

* `isEssNull_locallyDiscrete_iff` — a 1-cell is essentially null exactly when it is a zero morphism.
* `isNormalMono_of_mono`, `isNormalEpi_of_epi` — every monomorphism is a normal
  2-monomorphism, and dually.
* `isNormal_locallyDiscrete` — **every** 1-cell is normal, which is the epi-mono factorisation.
* `twoZExact_locallyDiscrete`, `twoDiExact_locallyDiscrete` — conditions (DI1) and (DI2) hold,
  so the standing hypotheses of Section 6 are consistent.
* `isHSD_locallyDiscrete`, `isPureSnake_locallyDiscrete` — hence homological self-duality and
  the Pure Snake Lemma are not vacuous.

## The classical Snake Lemma

That the Snake Lemma of `exists_snakeGeneral`, read in this model, is the classical Snake Lemma
is `exists_snakeClassical`, in `SnakeLean.Classical`. Its typeclass hypotheses are all discharged
here; what that module adds is the translation in both directions — a commutative ladder of an
abelian category into a `MorphismSES`, and `IsExactAt` back into `ShortComplex.Exact`.
-/

universe v u

namespace SnakeLean

open CategoryTheory Bicategory Limits ZeroObject

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The zero object of `C`, viewed as an object of the locally discrete 2-category on `C`. -/
noncomputable abbrev zeroLD : LocallyDiscrete C := LocallyDiscrete.mk (0 : C)

noncomputable instance hasBizeroLD : HasBizero (zeroLD C) where
  toZero _ := ⟨0⟩
  fromZero _ := ⟨0⟩

instance isStrongLD : IsStrong (zeroLD C) := isStrong_locallyDiscrete (isZero_zero C)

variable {C}

/-- **Nullity is vanishing.** In a locally discrete 2-category the only invertible 2-cells are
identities, so a 1-cell is essentially null exactly when the morphism it names is zero. -/
theorem isEssNull_locallyDiscrete_iff {a b : LocallyDiscrete C} (f : a ⟶ b) :
    IsEssNull (zeroLD C) f ↔ f.as = 0 := by
  constructor
  · rintro ⟨n, ⟨t, i, rfl⟩, ⟨e⟩⟩
    have : f = t ≫ i := LocallyDiscrete.eq_of_hom e.hom
    subst this
    have ht : t.as = 0 := (isZero_zero C).eq_zero_of_tgt t.as
    change t.as ≫ i.as = 0
    rw [ht, zero_comp]
  · intro hf
    exact ⟨f, ⟨⟨0⟩, ⟨0⟩, Discrete.ext (by simpa using hf)⟩, ⟨Iso.refl f⟩⟩

/-- **2-kernels are kernels.** A 1-cell of the locally discrete 2-category is a 2-kernel of `f`
as soon as the morphism it names is a kernel of the morphism `f` names. -/
theorem isTwoKernel_of_lift {a b K : LocallyDiscrete C} {f : a ⟶ b} {k : K ⟶ a} [Mono k.as]
    (w : k.as ≫ f.as = 0)
    (hl : ∀ {Z : C} (z : Z ⟶ a.as), z ≫ f.as = 0 → ∃ u : Z ⟶ K.as, u ≫ k.as = z) :
    IsTwoKernel (zeroLD C) f k where
  isEssNull_comp := (isEssNull_locallyDiscrete_iff _).2 w
  fac z hz := by
    obtain ⟨u, hu⟩ := hl z.as ((isEssNull_locallyDiscrete_iff _).1 hz)
    exact ⟨⟨u⟩, ⟨eqToIso (Discrete.ext hu)⟩⟩
  isTwoMono := (isTwoMono_locallyDiscrete_iff _).2 inferInstance

/-- **2-cokernels are cokernels**, dually. -/
theorem isTwoCokernel_of_desc {a b Q : LocallyDiscrete C} {f : a ⟶ b} {q : b ⟶ Q} [Epi q.as]
    (w : f.as ≫ q.as = 0)
    (hc : ∀ {Z : C} (z : b.as ⟶ Z), f.as ≫ z = 0 → ∃ u : Q.as ⟶ Z, q.as ≫ u = z) :
    IsTwoCokernel (zeroLD C) f q where
  isEssNull_comp := (isEssNull_locallyDiscrete_iff _).2 w
  fac z hz := by
    obtain ⟨u, hu⟩ := hc z.as ((isEssNull_locallyDiscrete_iff _).1 hz)
    exact ⟨⟨u⟩, ⟨eqToIso (Discrete.ext hu)⟩⟩
  isTwoEpi := (isTwoEpi_locallyDiscrete_iff _).2 inferInstance

/-- **Condition (DI1).** Every 1-cell has a 2-kernel and a 2-cokernel, because every morphism of
an abelian category has a kernel and a cokernel. -/
instance twoZExact_locallyDiscrete : TwoZExact (zeroLD C) where
  hasTwoKernel f := ⟨_, (⟨kernel.ι f.as⟩ : LocallyDiscrete.mk (kernel f.as) ⟶ _),
    isTwoKernel_of_lift (kernel.condition f.as)
      (fun z hz => ⟨kernel.lift _ z hz, kernel.lift_ι _ _ _⟩)⟩
  hasTwoCokernel f := ⟨_, (⟨cokernel.π f.as⟩ : _ ⟶ LocallyDiscrete.mk (cokernel f.as)),
    isTwoCokernel_of_desc (cokernel.condition f.as)
      (fun z hz => ⟨cokernel.desc _ z hz, cokernel.π_desc _ _ _⟩)⟩

/-- **Every monomorphism is a normal 2-monomorphism**, being the 2-kernel of its cokernel. -/
theorem isNormalMono_of_mono {K A : LocallyDiscrete C} (k : K ⟶ A) [Mono k.as] :
    IsNormalMono (zeroLD C) k :=
  ⟨LocallyDiscrete.mk (cokernel k.as), ⟨cokernel.π k.as⟩,
    isTwoKernel_of_lift (cokernel.condition k.as)
      (fun z hz => ⟨Abelian.monoLift k.as z hz, Abelian.monoLift_comp k.as z hz⟩)⟩

/-- **Every epimorphism is a normal 2-epimorphism**, being the 2-cokernel of its kernel. -/
theorem isNormalEpi_of_epi {A Q : LocallyDiscrete C} (q : A ⟶ Q) [Epi q.as] :
    IsNormalEpi (zeroLD C) q :=
  ⟨LocallyDiscrete.mk (kernel q.as), ⟨kernel.ι q.as⟩,
    isTwoCokernel_of_desc (kernel.condition q.as)
      (fun z hz => ⟨Abelian.epiDesc q.as z hz, Abelian.comp_epiDesc q.as z hz⟩)⟩

/-- **Every 1-cell is normal.** This is exactly the epi-mono factorisation of an abelian
category: the first factor is an epimorphism and the second a monomorphism, and in an abelian
category every epimorphism and every monomorphism is normal. -/
theorem isNormal_locallyDiscrete {a b : LocallyDiscrete C} (f : a ⟶ b) :
    IsNormal (zeroLD C) f :=
  ⟨LocallyDiscrete.mk (image f.as),
    (⟨factorThruImage f.as⟩ : a ⟶ LocallyDiscrete.mk (image f.as)), ⟨image.ι f.as⟩,
    isNormalEpi_of_epi _, isNormalMono_of_mono _,
    ⟨eqToIso (Discrete.ext (image.fac f.as).symm)⟩⟩

/-- **Condition (DI2).** Every antinormal 1-cell is normal, because every 1-cell is. -/
instance twoDiExact_locallyDiscrete : TwoDiExact (zeroLD C) where
  isNormal_of_isAntinormal _ := isNormal_locallyDiscrete _

/-- **The standing hypotheses of Section 6 are consistent.** All four of `HasBizero`,
`IsStrong`, `TwoZExact` and `TwoDiExact` hold of `zeroLD C`, so every result of Sections 2 to 6
applies to it, `exists_snakeGeneral` included. -/
theorem isHSD_locallyDiscrete : IsHSD (zeroLD C) := isHSD_of_twoDiExact

/-- Homological self-duality being available, so is the Pure Snake Lemma. -/
theorem isPureSnake_locallyDiscrete : IsPureSnake (zeroLD C) := isPureSnake_of_twoDiExact

end SnakeLean
