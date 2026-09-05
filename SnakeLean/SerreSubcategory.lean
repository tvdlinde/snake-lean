/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import SnakeLean.SerreJoin

/-!
# A Serre subcategory is an abelian category, and (SAT) descends to it

This module is about abelian categories, not about the 2-categorical development. It supplies
the first half of Proposition 8.16 `P:SATclosed`: condition (SAT) --- that every `S`-saturation
of a Serre class is a Serre class --- is inherited by Serre subcategories.

Mathlib does not record that the full subcategory on a Serre class is abelian, so that comes
first. The inclusion then preserves finite limits and colimits, which is what makes the
dictionary between the Serre classes of the subcategory and those of the ambient category
contained in it work.

## Main results

* `ObjectProperty.abelianFullSubcategory` --- the full subcategory on a Serre class is abelian.
* `ObjectProperty.isSerreClass_map_ι` --- with `isSerreClass_inverseImage` of `SerreJoin.lean`,
  the dictionary: image and preimage along the inclusion carry Serre classes to Serre classes.
* `condSAT_fullSubcategory` --- (SAT) is inherited by Serre subcategories.
-/

universe v v' u u'

namespace CategoryTheory

open Limits ZeroObject

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] (B : ObjectProperty C) [B.IsSerreClass]

section AbelianStructure

/-- A Serre class is closed under binary products: a binary product is a biproduct, and a
biproduct is an extension. -/
instance isClosedUnderBinaryProducts_of_isSerreClass : B.IsClosedUnderBinaryProducts := by
  refine IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  refine B.prop_of_iso (HasLimit.isoOfNatIso (diagramIsoPair F)).symm ?_
  refine B.prop_of_iso (biprod.isoProd _ _) ?_
  exact B.prop_X₂_of_shortExact (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact
    (hF _) (hF _)

instance isClosedUnderFiniteProducts_of_isSerreClass : B.IsClosedUnderFiniteProducts :=
  IsClosedUnderFiniteProducts.mk'

/-- A Serre class is closed under equalisers, an equaliser being a subobject of the source. -/
instance isClosedUnderEqualizers_of_isSerreClass :
    B.IsClosedUnderLimitsOfShape WalkingParallelPair := by
  refine IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  refine B.prop_of_iso (HasLimit.isoOfNatIso (diagramIsoParallelPair F)).symm ?_
  exact B.prop_of_mono (equalizer.ι _ _) (hF WalkingParallelPair.zero)

/-- A Serre class is closed under coequalisers, a coequaliser being a quotient of the target. -/
instance isClosedUnderCoequalizers_of_isSerreClass :
    B.IsClosedUnderColimitsOfShape WalkingParallelPair := by
  refine IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  refine B.prop_of_iso (HasColimit.isoOfNatIso (diagramIsoParallelPair F)).symm ?_
  exact B.prop_of_epi (coequalizer.π _ _) (hF WalkingParallelPair.one)

instance : HasFiniteProducts B.FullSubcategory := ⟨fun _ => inferInstance⟩

instance : HasEqualizers B.FullSubcategory := inferInstance

instance : HasCoequalizers B.FullSubcategory := inferInstance

instance : HasKernels B.FullSubcategory := ⟨inferInstance⟩

instance : HasCokernels B.FullSubcategory := ⟨inferInstance⟩

instance : PreservesFiniteProducts B.ι := ⟨fun _ => inferInstance⟩

instance : PreservesLimitsOfShape WalkingParallelPair B.ι := inferInstance

instance : PreservesColimitsOfShape WalkingParallelPair B.ι := inferInstance

instance : HasFiniteLimits B.FullSubcategory :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

instance preservesFiniteLimits_ι : PreservesFiniteLimits B.ι :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _

instance : HasFiniteBiproducts B.FullSubcategory := HasFiniteBiproducts.of_hasFiniteProducts

instance : HasFiniteColimits B.FullSubcategory :=
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

instance preservesFiniteColimits_ι : PreservesFiniteColimits B.ι :=
  preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts _

instance {X Y : B.FullSubcategory} (f : X ⟶ Y) : IsIso (Abelian.coimageImageComparison f) :=
  have := IsIso.of_isIso_fac_right
    (Abelian.PreservesCoimage.hom_coimageImageComparison B.ι f).symm
  Functor.FullyFaithful.isIso_of_isIso_map B.fullyFaithfulι _

/-- **The full subcategory on a Serre class is abelian.** Mathlib has `IsSerreClass` but does
not record this, which is what the statement "(SAT) is inherited by Serre subcategories" needs
in order to be expressible at all. -/
noncomputable instance abelianFullSubcategory : Abelian B.FullSubcategory :=
  Abelian.ofCoimageImageComparisonIsIso

variable {A : Type u'} [Category.{v'} A] (F : A ⥤ C) (hF : ∀ X, B (F.obj X))

/-- An exact functor landing in a Serre subcategory is exact as a functor into it. The inclusion
reflects finite limits and colimits, being fully faithful and exact. -/
instance preservesFiniteLimits_lift [PreservesFiniteLimits F] :
    PreservesFiniteLimits (B.lift F hF) :=
  have : PreservesFiniteLimits (B.lift F hF ⋙ B.ι) := inferInstanceAs (PreservesFiniteLimits F)
  preservesFiniteLimits_of_reflects_of_preserves _ B.ι

instance preservesFiniteColimits_lift [PreservesFiniteColimits F] :
    PreservesFiniteColimits (B.lift F hF) :=
  have : PreservesFiniteColimits (B.lift F hF ⋙ B.ι) := inferInstanceAs (PreservesFiniteColimits F)
  preservesFiniteColimits_of_reflects_of_preserves _ B.ι

instance additive_lift [Preadditive A] [F.Additive] : (B.lift F hF).Additive where
  map_add := by
    intro X Y f g
    apply B.ι.map_injective
    rw [Functor.map_add]

end AbelianStructure


section Dictionary

omit [B.IsSerreClass] in
/-- The inclusion is conservative on zero objects: it neither creates nor destroys them. -/
lemma isZero_ι_obj_iff (X : B.FullSubcategory) : IsZero (B.ι.obj X) ↔ IsZero X := by
  simp only [IsZero.iff_id_eq_zero]
  constructor
  · intro h
    apply B.ι.map_injective
    rw [B.ι.map_id, B.ι.map_zero]
    exact h
  · intro h
    rw [← B.ι.map_id, h, B.ι.map_zero]

section Image

variable (Q : ObjectProperty B.FullSubcategory)

/-- Membership in the essential image of a class of objects of the subcategory, read off in the
ambient category. -/
lemma prop_map_ι_iff [Q.IsClosedUnderIsomorphisms] (X : C) :
    Q.map B.ι X ↔ ∃ (h : B X), Q ⟨X, h⟩ := by
  constructor
  · rintro ⟨Y, hY, ⟨e⟩⟩
    have hX : B X := B.prop_of_iso e Y.property
    exact ⟨hX, Q.prop_of_iso (B.isoMk (X := Y) (Y := ⟨X, hX⟩) e) hY⟩
  · rintro ⟨h, hQ⟩
    exact ⟨⟨X, h⟩, hQ, ⟨Iso.refl _⟩⟩

lemma prop_map_ι_ι_obj_iff [Q.IsClosedUnderIsomorphisms] (X : B.FullSubcategory) :
    Q.map B.ι (B.ι.obj X) ↔ Q X :=
  (prop_map_ι_iff B Q _).trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨X.property, h⟩⟩

/-- The image of `Q` along the inclusion of the full subcategory on `B` lies below `B`. -/
lemma map_ι_le : Q.map B.ι ≤ B := by
  rintro X ⟨Y, _, ⟨e⟩⟩
  exact B.prop_of_iso e Y.property

variable [Q.IsSerreClass]

instance : (Q.map B.ι).ContainsZero where
  exists_zero := ⟨0, isZero_zero C, (prop_map_ι_iff B Q _).2
    ⟨B.prop_zero, Q.prop_of_isZero ((isZero_ι_obj_iff B (X := ⟨0, B.prop_zero⟩)).1
      (isZero_zero C))⟩⟩

instance : (Q.map B.ι).IsClosedUnderSubobjects where
  prop_of_mono := by
    intro X Y f hf hY
    haveI := hf
    obtain ⟨hYB, hYQ⟩ := (prop_map_ι_iff B Q Y).1 hY
    have hXB : B X := B.prop_of_mono f hYB
    refine (prop_map_ι_iff B Q X).2 ⟨hXB, ?_⟩
    have h₂ : Mono (B.ι.map (B.homMk (X := ⟨X, hXB⟩) (Y := ⟨Y, hYB⟩) f)) := hf
    have := B.ι.mono_of_mono_map h₂
    exact Q.prop_of_mono (B.homMk (X := ⟨X, hXB⟩) (Y := ⟨Y, hYB⟩) f) hYQ

instance : (Q.map B.ι).IsClosedUnderQuotients where
  prop_of_epi := by
    intro X Y f hf hX
    haveI := hf
    obtain ⟨hXB, hXQ⟩ := (prop_map_ι_iff B Q X).1 hX
    have hYB : B Y := B.prop_of_epi f hXB
    refine (prop_map_ι_iff B Q Y).2 ⟨hYB, ?_⟩
    have h₂ : Epi (B.ι.map (B.homMk (X := ⟨X, hXB⟩) (Y := ⟨Y, hYB⟩) f)) := hf
    have := B.ι.epi_of_epi_map h₂
    exact Q.prop_of_epi (B.homMk (X := ⟨X, hXB⟩) (Y := ⟨Y, hYB⟩) f) hXQ

instance : (Q.map B.ι).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    obtain ⟨h₁B, h₁Q⟩ := (prop_map_ι_iff B Q _).1 h₁
    obtain ⟨h₃B, h₃Q⟩ := (prop_map_ι_iff B Q _).1 h₃
    have h₂B : B S.X₂ := B.prop_X₂_of_shortExact hS h₁B h₃B
    refine (prop_map_ι_iff B Q _).2 ⟨h₂B, ?_⟩
    let S' : ShortComplex B.FullSubcategory :=
      ShortComplex.mk (B.homMk (X := ⟨S.X₁, h₁B⟩) (Y := ⟨S.X₂, h₂B⟩) S.f)
        (B.homMk (X := ⟨S.X₂, h₂B⟩) (Y := ⟨S.X₃, h₃B⟩) S.g)
        (by
          apply B.ι.map_injective
          simp only [Functor.map_comp, Functor.map_zero]
          exact S.zero)
    have hmap : S'.map B.ι = S := rfl
    have hSE : S'.ShortExact := by
      have hm : Mono (B.ι.map S'.f) := hS.mono_f
      have he : Epi (B.ι.map S'.g) := hS.epi_g
      haveI := B.ι.mono_of_mono_map hm
      haveI := B.ι.epi_of_epi_map he
      exact { exact := (S'.exact_map_iff_of_faithful B.ι).1 (by rw [hmap]; exact hS.exact) }
    exact Q.prop_X₂_of_shortExact hSE h₁Q h₃Q

/-- **The essential image of a Serre class of a Serre subcategory is a Serre class.** With
`isSerreClass_inverseImage` this is the correspondence the paper's proof appeals to: the
Serre subcategories of `B` are exactly the Serre subcategories of `C` contained in `B`. -/
instance isSerreClass_map_ι : (Q.map B.ι).IsSerreClass where

end Image

end Dictionary

section SAT

variable (C) in
/-- **Condition (SAT).** For all Serre classes `K` and `S`, the `S`-saturation of `K` is again a
Serre class.

By `isSerreClass_serreSaturation_iff` this says that the saturation coincides with the join, and
it is exactly what condition (DI2) asks of the 2-category of abelian categories: see
Definition 8.15 `D:SAT`. -/
def CondSAT : Prop :=
  ∀ (S K : ObjectProperty C) [S.IsSerreClass] [K.IsSerreClass],
    (serreSaturation S K).IsSerreClass

variable (Q : ObjectProperty B.FullSubcategory) [Q.IsSerreClass]

/-- Being an isomorphism modulo a Serre class of the subcategory is detected in the ambient
category, the inclusion preserving kernels and cokernels. -/
lemma isoModSerre_of_map_ι {X Y : B.FullSubcategory} {f : X ⟶ Y}
    (hf : (Q.map B.ι).isoModSerre (B.ι.map f)) : Q.isoModSerre f := by
  constructor
  · change Q (kernel f)
    rw [← prop_map_ι_ι_obj_iff B Q]
    exact (Q.map B.ι).prop_of_iso (PreservesKernel.iso B.ι f).symm hf.1
  · change Q (cokernel f)
    rw [← prop_map_ι_ι_obj_iff B Q]
    exact (Q.map B.ι).prop_of_iso (PreservesCokernel.iso B.ι f).symm hf.2

/-- **(SAT) is inherited by Serre subcategories.** This is the first half of Proposition 8.16
`P:SATclosed`, and it needs no theory of Serre quotients: the saturation is defined by a span,
and both the span and the two Serre classes transport along the inclusion.

The shape is the paper's. Push `K'` and `S'` forward to Serre classes `K` and `S` of the
ambient category; the `S`-saturation of `K` is a Serre class by hypothesis, so its preimage is
one too, and it contains `K'` and `S'`, hence their join. It remains to see that an object of
the subcategory lying in that preimage lies in the saturation computed inside the subcategory ---
the paper's "the `S`-saturation of `K` computed in `B` is the intersection with `B` of the one
computed in `A`". The paper gets it from Lemma 8.10 `L:FullyFaithful`, the induced `B/S → A/S`
being fully faithful and so reflecting isomorphisms; here, with no Serre quotient in hand, it is
read off the span directly: its apex already lies in `B`, being joined to an object of `B` by a
morphism whose kernel and cokernel lie in `S ⊆ B`. -/
theorem condSAT_fullSubcategory (h : CondSAT C) : CondSAT B.FullSubcategory := by
  intro S' K' _ _
  refine (isSerreClass_serreSaturation_iff S' K').2
    (le_antisymm (serreSaturation_le_serreJoin S' K') ?_)
  haveI := h (S'.map B.ι) (K'.map B.ι)
  refine le_trans (K'.serreJoin_le S'
    (isSerreClass_inverseImage (serreSaturation (S'.map B.ι) (K'.map B.ι)) B.ι) ?_ ?_) ?_
  · exact fun X' hX' => le_serreSaturation _ _ _ (K'.prop_map_obj B.ι hX')
  · exact fun X' hX' => serre_le_serreSaturation _ _ _ (S'.prop_map_obj B.ι hX')
  rintro X' ⟨A, D, f, g, hA, hf, hg⟩
  obtain ⟨hAB, hAK⟩ := (prop_map_ι_iff B K' A).1 hA
  have hDB : B D :=
    (B.prop_iff_of_isoModSerre (isoModSerre_mono B (map_ι_le B S') hg)).2 X'.property
  let A'' : B.FullSubcategory := ⟨A, hAB⟩
  let D'' : B.FullSubcategory := ⟨D, hDB⟩
  refine ⟨A'', D'', B.homMk (X := D'') (Y := A'') f, B.homMk (X := D'') (Y := X') g, hAK, ?_, ?_⟩
  · exact isoModSerre_of_map_ι B S' (f := B.homMk (X := D'') (Y := A'') f) hf
  · exact isoModSerre_of_map_ι B S' (f := B.homMk (X := D'') (Y := X') g) hg

end SAT

end ObjectProperty

end CategoryTheory
