/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.ZExact

/-!
# The canonical comparison, and self-duality of exactness

This module formalises the opening of Section 4 of *A two-categorical Snake Lemma*: the
comparison 1-cell `j_f : 2-Coim(f) → 2-Img(f)` of Lemma 4.2 `Normal Iff Comparison Iso`,
the characterisation of normal 1-cells by it, and Proposition 4.4 `Exactness Self-Dual`
with the definition of exactness that follows from it.

## Hypothesis form before choice form

Every statement is proved first in a form that names its 2-kernels and 2-cokernels explicitly,
and only then specialised to the chosen ones of `SnakeLean.ZExact`. This is not only the house
discipline. Proposition 4.18 `Criteria HSD` and Proposition 4.22 `Third Iso` both identify the
2-kernel of a dinversion with a 1-cell that is *not* the chosen one — the paper writes
`2-Ker(w) ≃ f` — so the results have to be available at an arbitrary 2-kernel or they cannot be
applied at all. The choice forms below carry a prime.

## The converse half of Lemma 4.2

The paper's proof that a normal 1-cell `f ≅ m ∘ e` has an equivalence for comparison goes
through Proposition 3.9 `CoKernel of Composite`, `2-Ker(f) ≃ 2-Ker(e)`, hence `2-Coim(f) ≃ e`,
and dually `2-Img(f) ≃ m`, and then reads the defining relation of the comparison under these
equivalences. The proof here is the same, with `isTwoKernel_comp_isTwoMono_iff` for the
proposition.

## Exactness dualises, and what that costs

`IsExactAt f g` renders Definition 4.5 `Def:ExactSequence` as "`f` factors as a normal
2-epimorphism followed by a 2-kernel of `g`". That is condition (i) of Proposition
4.4 `Exactness Self-Dual` read as a property of the *pair*, and it is asymmetric in a way the
paper's definition is not: the paper quantifies over pairs of composable **normal** 1-cells, whereas
`IsExactAt f g` implies `IsNormal O f` and says nothing about `g`. Adding back the normality of
`g` restores the symmetry exactly — `isExactAt_and_isNormal_op_iff` — and no homological
self-duality is needed for it: Proposition 4.4 `Exactness Self-Dual` comes before Definition 4.17
`Def:HSD` and does not depend on it. What homological self-duality buys instead is recorded in
`SnakeLean.Dinversion`.

This matters in Section 6: 2-exactness of the snake sequence at `2-Cok(g)` is the dual of
2-exactness at `2-Ker(g)`, and `isExactAt_op_iff` is what makes "dually" literal there.

## Main results

* `exists_comparison` and `comparison_unique` — the comparison exists and is unique up to an
  invertible 2-cell, the first half of Lemma 4.2 `Normal Iff Comparison Iso`.
* `isNormal_iff_isEquiv1_comparison` — its second half: `f` is normal exactly when the comparison
  is an equivalence.
* `exactness_tfae` — Proposition 4.4 `Exactness Self-Dual`.
* `IsExactAt` — Definition 4.5 `Def:ExactSequence`.
* `isExactAt_iff_of_isNormal` — exactness at any normal image factorisation, with no 2-kernel of
  `f` required once `g` is normal.
* `isExactAt_op_iff`, `isExactAt_and_isNormal_op_iff` — exactness of a pair of normal 1-cells is
  self-dual.

## Elsewhere

Homological self-duality and the Pure Snake Lemma are in `SnakeLean.Dinversion`; normal chain
complexes and the homology criterion in `SnakeLean.Homology`.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

section Transport

open Opposite Bicategory.Opposite

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {K K' A A' Q Q' : B}

/-- An equivalence cancels off the front of a 2-kernel. This is the converse of
`IsTwoKernel.isEquiv1_comp`, and is what lets a result proved at one 2-kernel be transported to
any other. -/
theorem IsTwoKernel.of_isEquiv1_comp {f : A ⟶ A'} {t : K' ⟶ K} {k : K ⟶ A} (ht : IsEquiv1 t)
    (h : IsTwoKernel O f (t ≫ k)) : IsTwoKernel O f k := by
  obtain ⟨t', ⟨η⟩, ⟨ε⟩⟩ := ht
  refine (h.isEquiv1_comp (isEquiv1_of_inv η ε)).of_iso_right ?_
  exact (eqToIso (Category.assoc t' t k)).symm ≪≫ Bicategory.whiskerRightIso ε k ≪≫
    eqToIso (Category.id_comp k)

/-- The dual: an equivalence cancels off the back of a 2-cokernel. -/
theorem IsTwoCokernel.of_comp_isEquiv1 {f : A ⟶ A'} {q : A' ⟶ Q} {t : Q ⟶ Q'} (ht : IsEquiv1 t)
    (h : IsTwoCokernel O f (q ≫ t)) : IsTwoCokernel O f q :=
  isTwoCokernel_of_op ((isTwoKernel_op h).of_isEquiv1_comp (isEquiv1_op ht))

end Transport

section Comparison

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {I J K A A' Q : B}

/-- **Lemma 4.2 `Normal Iff Comparison Iso`, existence.** If `k` is a 2-kernel of `f`, `e` a
2-cokernel of `k`, `q` a 2-cokernel of `f` and `m` a 2-kernel of `q`, then `f` factors through
the coimage and the image. -/
theorem exists_comparison {f : A ⟶ A'} {k : K ⟶ A} (hk : IsTwoKernel O f k) {e : A ⟶ I}
    (he : IsTwoCokernel O k e) {q : A' ⟶ Q} (hq : IsTwoCokernel O f q) {m : J ⟶ A'}
    (hm : IsTwoKernel O q m) : ∃ j : I ⟶ J, Nonempty (e ≫ j ≫ m ≅ f) := by
  haveI := he.isTwoEpi
  obtain ⟨v, ⟨θ⟩⟩ := he.fac f hk.isEssNull_comp
  have hv : IsEssNull O (v ≫ q) := by
    refine IsEssNull.of_comp_isTwoEpi e (hq.isEssNull_comp.of_iso ?_)
    exact (Bicategory.whiskerRightIso θ q).symm ≪≫ eqToIso (Category.assoc e v q)
  obtain ⟨j, ⟨γ⟩⟩ := hm.fac v hv
  exact ⟨j, ⟨Bicategory.whiskerLeftIso e γ ≪≫ θ⟩⟩

omit [Strict B] in
/-- **Lemma 4.2 `Normal Iff Comparison Iso`, uniqueness.** Any two comparisons are related by an
invertible 2-cell, and by exactly one compatible with the two factorisations, since `m` is
faithful. -/
theorem comparison_unique {f : A ⟶ A'} {e : A ⟶ I} [IsTwoEpi e] {m : J ⟶ A'} [IsTwoMono m]
    {j j' : I ⟶ J} (θ : e ≫ j ≫ m ≅ f) (θ' : e ≫ j' ≫ m ≅ f) : Nonempty (j ≅ j') :=
  ⟨IsTwoMono.preimageIso m (IsTwoEpi.preimageIso e (θ ≪≫ θ'.symm))⟩

/-- **Lemma 4.2 `Normal Iff Comparison Iso`.** A 1-cell is normal exactly when its comparison is an
equivalence. -/
theorem isNormal_iff_isEquiv1_comparison {f : A ⟶ A'} {k : K ⟶ A} (hk : IsTwoKernel O f k)
    {e : A ⟶ I} (he : IsTwoCokernel O k e) {q : A' ⟶ Q} (hq : IsTwoCokernel O f q) {m : J ⟶ A'}
    (hm : IsTwoKernel O q m) {j : I ⟶ J} (θ : e ≫ j ≫ m ≅ f) : IsNormal O f ↔ IsEquiv1 j := by
  haveI := he.isTwoEpi
  haveI := hm.isTwoMono
  constructor
  · rintro ⟨I₀, e₀, m₀, ⟨W, g₀, hg₀⟩, ⟨Z, ℓ₀, hℓ₀⟩, ⟨θ₀⟩⟩
    haveI := hg₀.isTwoEpi
    haveI := hℓ₀.isTwoMono
    -- `k` is a 2-kernel of `e₀`, and `e₀` is the 2-cokernel of its 2-kernel, so `e ≃ e₀`.
    have hke₀ : IsTwoKernel O e₀ k := (isTwoKernel_comp_isTwoMono_iff m₀).mp (hk.of_iso θ₀)
    obtain ⟨u, hu, ⟨γ⟩⟩ := he.exists_isEquiv1 (hg₀.of_isTwoKernel hke₀)
    -- dually `m ≃ m₀`.
    have hqm₀ : IsTwoCokernel O m₀ q := (isTwoCokernel_isTwoEpi_comp_iff e₀).mp (hq.of_iso θ₀)
    obtain ⟨v, hv, ⟨δ⟩⟩ := hm.exists_isEquiv1 (hℓ₀.of_isTwoCokernel hqm₀)
    -- so `u ≫ v` is a comparison, and every comparison is isomorphic to it.
    have huv : e ≫ (u ≫ v) ≫ m ≅ f :=
      calc e ≫ (u ≫ v) ≫ m ≅ (e ≫ u) ≫ v ≫ m := eqToIso (by simp)
        _ ≅ e₀ ≫ v ≫ m := Bicategory.whiskerRightIso γ (v ≫ m)
        _ ≅ e₀ ≫ m₀ := Bicategory.whiskerLeftIso e₀ δ
        _ ≅ f := θ₀.symm
    obtain ⟨σ⟩ := comparison_unique huv θ
    exact IsEquiv1.of_iso σ (hu.comp hv)
  · intro hj
    exact ⟨I, e, j ≫ m, ⟨K, k, he⟩, ⟨Q, q, hm.isEquiv1_comp hj⟩, ⟨θ.symm⟩⟩

end Comparison

section Chosen

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] [TwoZExact O] {A A' : B}

/-- The **comparison** `j_f : 2-Coim(f) → 2-Img(f)` of Lemma 4.2 `Normal Iff Comparison Iso`. -/
noncomputable def comparison (O : B) [HasBizero O] [IsStrong O] [TwoZExact O] {A A' : B}
    (f : A ⟶ A') : twoCoimObj O f ⟶ twoImgObj O f :=
  (exists_comparison (isTwoKernel_twoKernel O f) (isTwoCokernel_twoCoim f)
    (isTwoCokernel_twoCokernel O f) (isTwoKernel_twoImg f)).choose

theorem nonempty_comparison_iso (f : A ⟶ A') :
    Nonempty (twoCoim O f ≫ comparison O f ≫ twoImg O f ≅ f) :=
  (exists_comparison (isTwoKernel_twoKernel O f) (isTwoCokernel_twoCoim f)
    (isTwoCokernel_twoCokernel O f) (isTwoKernel_twoImg f)).choose_spec

/-- **Lemma 4.2 `Normal Iff Comparison Iso`**, in the paper's notation. -/
theorem isNormal_iff_isEquiv1_comparison' (f : A ⟶ A') :
    IsNormal O f ↔ IsEquiv1 (comparison O f) := by
  obtain ⟨θ⟩ := nonempty_comparison_iso (O := O) f
  exact isNormal_iff_isEquiv1_comparison (isTwoKernel_twoKernel O f) (isTwoCokernel_twoCoim f)
    (isTwoCokernel_twoCokernel O f) (isTwoKernel_twoImg f) θ

end Chosen

section Exactness

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {I J K A A' A'' : B}

/-- **Proposition 4.4 `Exactness Self-Dual`.** For a composable pair of normal 1-cells with normal
image factorisations `f ≅ ef ≫ mf` and `g ≅ eg ≫ mg`, the 2-image of `f` is a 2-kernel of `g`
exactly when the 2-coimage of `g` is a 2-cokernel of `f`, and exactly when the two form a short
2-exact sequence. -/
theorem exactness_tfae {f : A ⟶ A'} {g : A' ⟶ A''} {ef : A ⟶ I} {mf : I ⟶ A'}
    (θf : f ≅ ef ≫ mf) (hef : IsNormalEpi O ef) (hmf : IsNormalMono O mf) {eg : A' ⟶ J}
    {mg : J ⟶ A''} (θg : g ≅ eg ≫ mg) (heg : IsNormalEpi O eg) (hmg : IsNormalMono O mg) :
    List.TFAE [IsTwoKernel O g mf, IsTwoCokernel O f eg, IsSES O mf eg] := by
  obtain ⟨W, gf, hgf⟩ := hef
  obtain ⟨Z, ℓf, hℓf⟩ := hmf
  obtain ⟨W', gg, hgg⟩ := heg
  obtain ⟨Z', ℓg, hℓg⟩ := hmg
  haveI := hgf.isTwoEpi
  haveI := hℓg.isTwoMono
  have key1 : IsTwoKernel O g mf ↔ IsTwoKernel O eg mf :=
    ⟨fun h => (isTwoKernel_comp_isTwoMono_iff mg).mp (h.of_iso θg),
      fun h => ((isTwoKernel_comp_isTwoMono_iff mg).mpr h).of_iso θg.symm⟩
  have key2 : IsTwoCokernel O f eg ↔ IsTwoCokernel O mf eg :=
    ⟨fun h => (isTwoCokernel_isTwoEpi_comp_iff ef).mp (h.of_iso θf),
      fun h => ((isTwoCokernel_isTwoEpi_comp_iff ef).mpr h).of_iso θf.symm⟩
  tfae_have 1 → 3 := fun h => ⟨key1.mp h, hgg.of_isTwoKernel (key1.mp h)⟩
  tfae_have 3 → 1 := fun h => key1.mpr h.isTwoKernel
  tfae_have 2 → 3 := fun h => ⟨hℓf.of_isTwoCokernel (key2.mp h), key2.mp h⟩
  tfae_have 3 → 2 := fun h => key2.mpr h.isTwoCokernel
  tfae_finish

/-- **The remark after Proposition 4.4 `Exactness Self-Dual`**: the equivalent conditions imply that
the composite is null. -/
theorem isEssNull_comp_of_isSES {f : A ⟶ A'} {g : A' ⟶ A''} {ef : A ⟶ I} {mf : I ⟶ A'}
    (θf : f ≅ ef ≫ mf) {eg : A' ⟶ J} {mg : J ⟶ A''} (θg : g ≅ eg ≫ mg) (hs : IsSES O mf eg) :
    IsEssNull O (f ≫ g) := by
  refine ((hs.isTwoKernel.isEssNull_comp.comp mg).comp_left ef).of_iso ?_
  calc ef ≫ (mf ≫ eg) ≫ mg ≅ (ef ≫ mf) ≫ eg ≫ mg := eqToIso (by simp)
    _ ≅ f ≫ eg ≫ mg := (Bicategory.whiskerRightIso θf (eg ≫ mg)).symm
    _ ≅ f ≫ g := (Bicategory.whiskerLeftIso f θg).symm

/-- **Definition 4.5 `Def:ExactSequence`.** A composable pair is **exact** at the middle object when
`f` factors as a normal 2-epimorphism followed by a 2-kernel of `g`; by
`exactness_tfae` this is condition (i) of Proposition 4.4 `Exactness Self-Dual`. -/
def IsExactAt (O : B) [HasBizero O] {A A' A'' : B} (f : A ⟶ A') (g : A' ⟶ A'') : Prop :=
  ∃ (I : B) (e : A ⟶ I) (m : I ⟶ A'), IsNormalEpi O e ∧ Nonempty (f ≅ e ≫ m) ∧
    IsTwoKernel O g m

omit [Strict B] [IsStrong O] in
/-- An exact pair has a normal first component. -/
theorem IsExactAt.isNormal {f : A ⟶ A'} {g : A' ⟶ A''} (h : IsExactAt O f g) : IsNormal O f := by
  obtain ⟨I₀, e₀, m₀, he₀, ⟨θ₀⟩, hm₀⟩ := h
  exact ⟨I₀, e₀, m₀, he₀, ⟨A'', g, hm₀⟩, ⟨θ₀⟩⟩

/-- Exactness read off a chosen normal image factorisation. -/
theorem isExactAt_iff {f : A ⟶ A'} {g : A' ⟶ A''} {ef : A ⟶ I} {mf : I ⟶ A'} (θf : f ≅ ef ≫ mf)
    (hef : IsNormalEpi O ef) (hmf : IsNormalMono O mf) {k : K ⟶ A} (hk : IsTwoKernel O f k) :
    IsExactAt O f g ↔ IsTwoKernel O g mf := by
  obtain ⟨W, gf, hgf⟩ := hef
  obtain ⟨Z, ℓf, hℓf⟩ := hmf
  haveI := hgf.isTwoEpi
  haveI := hℓf.isTwoMono
  refine ⟨fun h => ?_, fun h => ⟨I, ef, mf, ⟨W, gf, hgf⟩, ⟨θf⟩, h⟩⟩
  obtain ⟨I₀, e₀, m₀, he₀, ⟨θ₀⟩, hm₀⟩ := h
  obtain ⟨t, ht, -, ⟨σ⟩⟩ := imageFactorisation_unique θ₀ θf he₀ ⟨A'', g, hm₀⟩ hk
  exact IsTwoKernel.of_isEquiv1_comp ht (hm₀.of_iso_right σ.symm)

end Exactness

section SelfDuality

open Opposite Bicategory.Opposite

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {A A' A'' I J : B}
  {f : A ⟶ A'} {g : A' ⟶ A''} {ef : A ⟶ I} {mf : I ⟶ A'} {eg : A' ⟶ J} {mg : J ⟶ A''}

/-- **Exactness read off any normal image factorisation of `f`, when `g` is normal too.**

Unlike `isExactAt_iff` this needs no 2-kernel of `f`. That hypothesis is there only to compare
two normal image factorisations of `f` through `imageFactorisation_unique`; if `g` is normal the
comparison can be routed through the 2-cokernel of `f` instead, which is condition (ii) of
Proposition 4.4 `Exactness Self-Dual`. -/
theorem isExactAt_iff_of_isNormal (θf : f ≅ ef ≫ mf) (hef : IsNormalEpi O ef)
    (hmf : IsNormalMono O mf) (θg : g ≅ eg ≫ mg) (heg : IsNormalEpi O eg)
    (hmg : IsNormalMono O mg) : IsExactAt O f g ↔ IsTwoKernel O g mf := by
  refine ⟨fun h => ?_, fun h => ⟨I, ef, mf, hef, ⟨θf⟩, h⟩⟩
  obtain ⟨I₀, e₀, m₀, he₀, ⟨θ₀⟩, hm₀⟩ := h
  have hcok : IsTwoCokernel O f eg :=
    ((exactness_tfae θ₀ he₀ ⟨A'', g, hm₀⟩ θg heg hmg).out 0 1).mp hm₀
  exact ((exactness_tfae θf hef hmf θg heg hmg).out 1 0).mp hcok

/-- **Exactness dualises**, provided the second 1-cell is normal.

Definition 4.5 `Def:ExactSequence` asks a pair `(f, g)` of composable **normal** 1-cells to satisfy
the equivalent conditions of Proposition 4.4 `Exactness Self-Dual`, and those conditions are visibly
symmetric in `f` and `g`. `IsExactAt` drops the normality of `g` — it asks only that `f` factor as
a normal 2-epimorphism followed by a 2-kernel of `g` — and *that* condition is not symmetric: it
implies `IsNormal O f` and says nothing about `g`. Restoring the missing hypothesis restores the
symmetry, and no homological self-duality is needed for it. -/
theorem IsExactAt.op (h : IsExactAt O f g) (hg : IsNormal O g) :
    IsExactAt (op O) g.op f.op := by
  obtain ⟨I₀, e₀, m₀, he₀, ⟨θ₀⟩, hm₀⟩ := h
  obtain ⟨J₀, eg₀, mg₀, heg₀, hmg₀, ⟨θg₀⟩⟩ := hg
  exact ⟨Opposite.op J₀, mg₀.op, eg₀.op, isNormalEpi_op hmg₀, ⟨θg₀.op2⟩,
    isTwoKernel_op (((exactness_tfae θ₀ he₀ ⟨A'', g, hm₀⟩ θg₀ heg₀ hmg₀).out 0 1).mp hm₀)⟩

/-- The converse of `IsExactAt.op`. -/
theorem isExactAt_of_op (h : IsExactAt (op O) g.op f.op) (hf : IsNormal O f) :
    IsExactAt O f g := by
  obtain ⟨J₀, e₀, m₀, he₀, ⟨θ₀⟩, hm₀⟩ := h
  obtain ⟨I₀, ef₀, mf₀, hef₀, hmf₀, ⟨θf₀⟩⟩ := hf
  have hq : IsTwoCokernel O f m₀.unop := isTwoCokernel_of_op (by simpa using hm₀)
  have hn : IsNormalMono O e₀.unop := isNormalMono_of_op (by simpa using he₀)
  exact ⟨I₀, ef₀, mf₀, hef₀, ⟨θf₀⟩,
    ((exactness_tfae θf₀ hef₀ hmf₀ θ₀.unop2 ⟨A, f, hq⟩ hn).out 1 0).mp hq⟩

/-- **Exactness of a pair of normal 1-cells is self-dual**, which is what Definition 4.5
`Def:ExactSequence` intends and what makes "dually" literal in Section 6. -/
theorem isExactAt_op_iff (hf : IsNormal O f) (hg : IsNormal O g) :
    IsExactAt (op O) g.op f.op ↔ IsExactAt O f g :=
  ⟨fun h => isExactAt_of_op h hf, fun h => h.op hg⟩

/-- The same without any hypothesis: the exact amount by which `IsExactAt` fails to be self-dual
is the normality of its second argument, which the paper's definition builds in. -/
theorem isExactAt_and_isNormal_op_iff :
    IsExactAt (op O) g.op f.op ∧ IsNormal O f ↔ IsExactAt O f g ∧ IsNormal O g :=
  ⟨fun h => ⟨isExactAt_of_op h.1 h.2, isNormal_of_op h.1.isNormal⟩,
    fun h => ⟨h.1.op h.2, h.1.isNormal⟩⟩

end SelfDuality

end SnakeLean
