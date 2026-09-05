/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Abelian.Exact
import SnakeLean.LocallyDiscreteModel
import SnakeLean.SnakeGeneral

/-!
# The classical Snake Lemma

Corollary 6.24 `Snake General` recovers the Snake Lemma of homological algebra from the
2-categorical one, by reading an abelian category as a locally discrete 2-category. This module
carries out that instantiation over the model of `SnakeLean.LocallyDiscreteModel`.

The work is a translation in both directions. Going in, a commutative ladder with exact rows has
to become a `MorphismSES`, and the kernels and cokernels of an abelian category have to become
2-kernels and 2-cokernels; `SnakeLean.LocallyDiscreteModel` supplies the second half of that.
Coming out, `IsExactAt` has to become `ShortComplex.Exact`, which is
`isExactAt_locallyDiscrete_iff`: in a locally discrete 2-category `IsExactAt f g` says that `f`
factors as an epimorphism followed by a kernel of `g`, and that is exactly Mathlib's
`exact_iff_epi_kernel_lift`.

Nothing here is proved twice: the mathematics is `exists_snakeGeneral`, and the classical
statement is obtained from it rather than alongside it. Mathlib has its own Snake Lemma in
`Mathlib.Algebra.Homology.ShortComplex.SnakeLemma`; it is not used, and the point of this module
is precisely that it need not be.

## Main results

* `isExactAt_locallyDiscrete_iff` — exactness in the locally discrete 2-category is exactness of
  the corresponding short complex, in both directions.
* `exists_snakeClassical` — Corollary 6.24 `Snake General`, the Snake Lemma of homological
  algebra, deduced from `exists_snakeGeneral`.

## Not formalised

The last clause of Corollary 6.24 — that `ā` is a kernel of `b̄` when `a` is a kernel of `b`, and
dually. It is Proposition 6.17 `P:KerBarA`, machine-checked as `snake_isTwoKernel_barA`, and
carrying it across costs another translation of the same kind as the four here rather than any
further mathematics.
-/

universe v u

namespace SnakeLean

open CategoryTheory Bicategory Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ## Normality, monomorphisms and epimorphisms -/

/-- **Normal 2-epimorphisms are epimorphisms**, and conversely by `isNormalEpi_of_epi`. -/
theorem isNormalEpi_locallyDiscrete_iff {a b : LocallyDiscrete C} (q : a ⟶ b) :
    IsNormalEpi (zeroLD C) q ↔ Epi q.as := by
  refine ⟨fun h => ?_, fun _ => isNormalEpi_of_epi q⟩
  haveI := h.isTwoEpi
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b
  exact (isTwoEpi_locallyDiscrete_iff q).1 inferInstance

/-- **Normal 2-monomorphisms are monomorphisms**, and conversely by `isNormalMono_of_mono`. -/
theorem isNormalMono_locallyDiscrete_iff {a b : LocallyDiscrete C} (k : a ⟶ b) :
    IsNormalMono (zeroLD C) k ↔ Mono k.as := by
  refine ⟨fun h => ?_, fun _ => isNormalMono_of_mono k⟩
  haveI := h.isTwoMono
  obtain ⟨x⟩ := a; obtain ⟨y⟩ := b
  exact (isTwoMono_locallyDiscrete_iff k).1 inferInstance

/-! ## 2-kernels are kernels -/

/-- The factorisation property of a 2-kernel, read in the underlying category. -/
theorem IsTwoKernel.facLD {K a b : LocallyDiscrete C} {g : a ⟶ b} {m : K ⟶ a}
    (h : IsTwoKernel (zeroLD C) g m) {Z : C} (z : Z ⟶ a.as) (hz : z ≫ g.as = 0) :
    ∃ u : Z ⟶ K.as, u ≫ m.as = z := by
  obtain ⟨u, ⟨e⟩⟩ :=
    h.fac (⟨z⟩ : LocallyDiscrete.mk Z ⟶ a) ((isEssNull_locallyDiscrete_iff _).2 hz)
  exact ⟨u.as, congrArg Discrete.as (LocallyDiscrete.eq_of_hom e.hom)⟩

/-- A 2-kernel of the locally discrete 2-category is a monomorphism. -/
theorem IsTwoKernel.mono_asLD {K a b : LocallyDiscrete C} {g : a ⟶ b} {m : K ⟶ a}
    (h : IsTwoKernel (zeroLD C) g m) : Mono m.as := by
  haveI := h.isTwoMono
  obtain ⟨x⟩ := K; obtain ⟨y⟩ := a
  exact (isTwoMono_locallyDiscrete_iff m).1 inferInstance

/-- **A 2-kernel is a kernel.** -/
noncomputable def IsTwoKernel.isLimitLD {K a b : LocallyDiscrete C} {g : a ⟶ b} {m : K ⟶ a}
    (h : IsTwoKernel (zeroLD C) g m) :
    IsLimit (KernelFork.ofι m.as ((isEssNull_locallyDiscrete_iff _).1 h.isEssNull_comp)) :=
  haveI := h.mono_asLD
  KernelFork.IsLimit.ofι _ _ (fun z hz => (h.facLD z hz).choose)
    (fun z hz => (h.facLD z hz).choose_spec)
    (fun z hz _t ht => (cancel_mono m.as).1 (ht.trans (h.facLD z hz).choose_spec.symm))

/-! ## Exactness is exactness -/

/-- A pair of composable morphisms of an abelian category is **exact** when the composite
vanishes and the resulting short complex is exact. Mathlib's `ShortComplex.Exact` carries the
vanishing as data; here it is part of the claim, which is how the paper states it. -/
def ExactPair {X Y Z : C} (u : X ⟶ Y) (v : Y ⟶ Z) : Prop :=
  ∃ w : u ≫ v = 0, (ShortComplex.mk u v w).Exact

/-- **Exactness in the locally discrete 2-category is exactness.** `IsExactAt f g` says that `f`
factors as a normal 2-epimorphism followed by a 2-kernel of `g`; read in an abelian category that
is an epimorphism followed by a kernel of `g`, which is Mathlib's `exact_iff_epi_kernel_lift`. -/
theorem isExactAt_locallyDiscrete_iff {a b c : LocallyDiscrete C} (f : a ⟶ b) (g : b ⟶ c) :
    IsExactAt (zeroLD C) f g ↔ ExactPair f.as g.as := by
  constructor
  · rintro ⟨I, e, m, he, ⟨θ⟩, hm⟩
    haveI : Epi e.as := (isNormalEpi_locallyDiscrete_iff e).1 he
    have hfem : f.as = e.as ≫ m.as := congrArg Discrete.as (LocallyDiscrete.eq_of_hom θ.hom)
    have hmg : m.as ≫ g.as = 0 := (isEssNull_locallyDiscrete_iff _).1 hm.isEssNull_comp
    have w : f.as ≫ g.as = 0 := by rw [hfem, Category.assoc, hmg, comp_zero]
    refine ⟨w, ?_⟩
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    set φ := IsLimit.conePointUniqueUpToIso hm.isLimitLD (kernelIsKernel g.as) with hφ
    have hφι : φ.hom ≫ kernel.ι g.as = m.as := by
      simpa [hφ] using IsLimit.conePointUniqueUpToIso_hom_comp hm.isLimitLD (kernelIsKernel g.as)
        WalkingParallelPair.zero
    have : kernel.lift g.as f.as w = e.as ≫ φ.hom := by
      refine (cancel_mono (kernel.ι g.as)).1 ?_
      rw [kernel.lift_ι, Category.assoc, hφι, hfem]
    rw [this]
    exact epi_comp _ _
  · rintro ⟨w, hex⟩
    haveI : Epi (kernel.lift g.as f.as w) :=
      (ShortComplex.exact_iff_epi_kernel_lift (ShortComplex.mk f.as g.as w)).1 hex
    refine ⟨LocallyDiscrete.mk (kernel g.as), ⟨kernel.lift g.as f.as w⟩, ⟨kernel.ι g.as⟩,
      isNormalEpi_of_epi _, ⟨eqToIso (Discrete.ext (kernel.lift_ι g.as f.as w).symm)⟩, ?_⟩
    exact isTwoKernel_of_lift (kernel.condition g.as)
      (fun z hz => ⟨kernel.lift _ z hz, kernel.lift_ι _ _ _⟩)

/-! ## The classical Snake Lemma -/

/-- **Corollary 6.24 `Snake General`, the Snake Lemma of homological algebra.**

A commutative ladder in an abelian category, with exact rows, `b` an epimorphism and `c` a
monomorphism, admits a connecting morphism `δ : Ker h ⟶ Cok f` making the six-term sequence

`Ker f → Ker g → Ker h → Cok f → Cok g → Cok h`

exact at its four interior objects. This is `exists_snakeGeneral` read in `LocallyDiscrete C`;
no part of the argument is repeated here. The verticals need no hypothesis: in an abelian
category every morphism is normal, which is `isNormal_locallyDiscrete`. -/
theorem exists_snakeClassical {A M Cc X Y Z : C}
    {a : A ⟶ M} {b : M ⟶ Cc} {c : X ⟶ Y} {d : Y ⟶ Z}
    {f : A ⟶ X} {g : M ⟶ Y} {h : Cc ⟶ Z}
    (sqL : a ≫ g = f ≫ c) (sqR : b ≫ h = g ≫ d) [Epi b] [Mono c]
    (hT : ExactPair a b) (hB : ExactPair c d) :
    ∃ δ : kernel h ⟶ cokernel f,
      ExactPair (kernel.map f g a c sqL.symm) (kernel.map g h b d sqR.symm) ∧
      ExactPair (kernel.map g h b d sqR.symm) δ ∧
      ExactPair δ (cokernel.map f g a c sqL.symm) ∧
      ExactPair (cokernel.map f g a c sqL.symm) (cokernel.map g h b d sqR.symm) := by
  -- the ladder, with every 1-cell named in the locally discrete 2-category
  let a' : LocallyDiscrete.mk A ⟶ LocallyDiscrete.mk M := ⟨a⟩
  let b' : LocallyDiscrete.mk M ⟶ LocallyDiscrete.mk Cc := ⟨b⟩
  let c' : LocallyDiscrete.mk X ⟶ LocallyDiscrete.mk Y := ⟨c⟩
  let d' : LocallyDiscrete.mk Y ⟶ LocallyDiscrete.mk Z := ⟨d⟩
  let S : MorphismSES a' b' c' d' :=
    { f := (⟨f⟩ : LocallyDiscrete.mk A ⟶ LocallyDiscrete.mk X)
      g := (⟨g⟩ : LocallyDiscrete.mk M ⟶ LocallyDiscrete.mk Y)
      h := (⟨h⟩ : LocallyDiscrete.mk Cc ⟶ LocallyDiscrete.mk Z)
      φK := eqToIso (Discrete.ext sqL)
      φQ := eqToIso (Discrete.ext sqR) }
  -- the top row, straight from the bridge
  obtain ⟨I, ea, ma, hea, ⟨θa⟩, hma⟩ := (isExactAt_locallyDiscrete_iff a' b').2 hT
  -- the bottom row, in the coimage form the theorem consumes
  obtain ⟨wcd, hcd⟩ := hB
  haveI : Mono (cokernel.desc c d wcd) :=
    (ShortComplex.exact_iff_mono_cokernel_desc (ShortComplex.mk c d wcd)).1 hcd
  have hed : IsTwoCokernel (zeroLD C) c'
      (⟨cokernel.π c⟩ : LocallyDiscrete.mk Y ⟶ LocallyDiscrete.mk (cokernel c)) :=
    isTwoCokernel_of_desc (cokernel.condition c)
      (fun z hz => ⟨cokernel.desc _ z hz, cokernel.π_desc _ _ _⟩)
  have θd : d' ≅ (⟨cokernel.π c⟩ : LocallyDiscrete.mk Y ⟶ LocallyDiscrete.mk (cokernel c)) ≫
      (⟨cokernel.desc c d wcd⟩ : _ ⟶ LocallyDiscrete.mk Z) :=
    eqToIso (Discrete.ext (cokernel.π_desc c d wcd).symm)
  -- kernels and cokernels of the verticals
  have mk_ker : ∀ {P Q : C} (u : P ⟶ Q),
      IsTwoKernel (zeroLD C) (⟨u⟩ : LocallyDiscrete.mk P ⟶ LocallyDiscrete.mk Q)
        (⟨kernel.ι u⟩ : LocallyDiscrete.mk (kernel u) ⟶ _) := fun u =>
    isTwoKernel_of_lift (kernel.condition u) (fun z hz => ⟨kernel.lift _ z hz, kernel.lift_ι _ _ _⟩)
  have mk_cok : ∀ {P Q : C} (u : P ⟶ Q),
      IsTwoCokernel (zeroLD C) (⟨u⟩ : LocallyDiscrete.mk P ⟶ LocallyDiscrete.mk Q)
        (⟨cokernel.π u⟩ : _ ⟶ LocallyDiscrete.mk (cokernel u)) := fun u =>
    isTwoCokernel_of_desc (cokernel.condition u)
      (fun z hz => ⟨cokernel.desc _ z hz, cokernel.π_desc _ _ _⟩)
  obtain ⟨δ, e₁, e₂, e₃, e₄, -⟩ :=
    exists_snakeGeneral (O := zeroLD C) S (isNormalEpi_of_epi _) (isNormalMono_of_mono _)
      θa hea hma θd hed (isNormalMono_of_mono _)
      (isNormal_locallyDiscrete _) (isNormal_locallyDiscrete _) (isNormal_locallyDiscrete _)
      (mk_ker f) (mk_ker g) (mk_ker h) (mk_cok f) (mk_cok g) (mk_cok h)
      (aBar := ⟨kernel.map f g a c sqL.symm⟩) (eqToIso (Discrete.ext (by simp [a'])))
      (bBar := ⟨kernel.map g h b d sqR.symm⟩) (eqToIso (Discrete.ext (by simp [b'])))
      (cBar := ⟨cokernel.map f g a c sqL.symm⟩) (eqToIso (Discrete.ext (by simp [c'])))
      (dBar := ⟨cokernel.map g h b d sqR.symm⟩) (eqToIso (Discrete.ext (by simp [d'])))
  exact ⟨δ.as, (isExactAt_locallyDiscrete_iff _ _).1 e₁, (isExactAt_locallyDiscrete_iff _ _).1 e₂,
    (isExactAt_locallyDiscrete_iff _ _).1 e₃, (isExactAt_locallyDiscrete_iff _ _).1 e₄⟩

end SnakeLean
