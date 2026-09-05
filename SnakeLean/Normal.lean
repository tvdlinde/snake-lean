/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.Exact
import Mathlib.Tactic.TFAE

/-!
# Normal 1-cells and the normal image factorisation

This module completes Section 3 of *A two-categorical Snake Lemma* up to the doorstep of the
Normal Short Five Lemma: normal 1-cells, the second half of Proposition
3.6 `Composites of Normal Monos`, the characterisation of equivalences in Corollary
3.18 `Equivalence Is Mono Plus Normal Epi`, Proposition
3.22 `Image Factorisation of Normal Map is Unique`, and Corollary 3.8 `C:NormalTransport`.

## Normal 1-cells

A 1-cell is **normal** when it factors as a normal 2-epimorphism followed by a normal
2-monomorphism, and **antinormal** when it factors the other way round. An earlier draft defined
this by an equality `f = m ∘ e`, with a marginal note observing that it should ask instead for an
invertible 2-cell, and that every proof using normal 1-cells would have to be rechecked at that
weaker hypothesis. `IsNormal` is defined here with the invertible 2-cell from the start, so the
recheck is what this module carries out. Nothing breaks, and Definition 3.4 `Def Normal` now
reads that way.

## No 2-z-exactness

The paper states these results in a 2-z-exact 2-category, where all 2-kernels and 2-cokernels
exist. Nothing here needs that: each result needs at most the one 2-kernel or 2-cokernel named
in its own statement, which is therefore taken as an explicit hypothesis. Two results need none
at all — see `isEquiv1_of_isNormalEpi` and `isEquiv1_of_isNormalMono` in `SnakeLean.Exact`,
whose 2-kernel and 2-cokernel hypotheses the formalisation removed.

## Main results

* `IsNormalMono.of_comp` — Proposition 3.6 `Composites of Normal Monos`(ii), with its dual
  `IsNormalEpi.of_comp`.
* `IsEquiv1.isNormalMono` and `IsEquiv1.isNormalEpi` — the implication `(i) ⟹ (ii)` of Corollary
  3.18 `Equivalence Is Mono Plus Normal Epi`, whose four conditions are then assembled in
  `isEquiv1_tfae`.
* `isNormalMono_iff` and `isNormalEpi_iff` — Corollary 3.19 `Normal Mono Criterion`.
* `imageFactorisation_unique` and `isNormal_of_factorisation` — Proposition
  3.22 `Image Factorisation of Normal Map is Unique`.
* `isEquiv1_iff_isTrivial` — Proposition 3.20 `Normal Equivalence Trivial`.
* `IsNormalMono.comp_isEquiv1`, `IsNormalEpi.isEquiv1_comp` and the two halves already available
  from `SnakeLean.Exact` — Corollary 3.8 `C:NormalTransport`, assembled into `IsNormal.transport`,
  `IsAntinormal.transport` and the two `iff` forms.

## Remarks

Proposition 3.6 `Composites of Normal Monos`(i) asks only faithfulness of the middle 1-cell, and
`SnakeLean.Mono` states it that way. Part (ii) admits no such weakening, as Remark 3.7
`Rem Faithful Enough` says: its proof lifts an invertible 2-cell `g ∘ f ∘ s ≅ g ∘ r` along `g`,
which is exactly fullness. The hypothesis `[IsTwoMono g]` of `IsNormalMono.of_comp` is therefore
genuinely needed.

Corollary 3.8 `C:NormalTransport` was written for this development. It is what licenses the
reduction of condition (DI2) in the 2-category of abelian categories to the single composite of a
2-kernel with a 2-cokernel, in Section 8, and it does not follow from Proposition 3.6
`Composites of Normal Monos`(ii), which runs in the opposite direction. The two halves proved
here, `IsNormalMono.comp_isEquiv1` and its dual, need only a bizero object: the linter reports
`[IsStrong O]` unused in both, and both carry an `omit`. The other two halves inherit
`[IsStrong O]` through `IsTwoKernel.isEquiv1_comp`, which does use it, by way of
`IsEssNull.comp_left`. That is why `IsNormal.transport` carries an `omit` and
`IsAntinormal.transport` does not: the two call different halves. The asymmetry is an artefact of
the auxiliary lemmas, not a difference between the two statements.

`isEquiv1_iff_isTrivial` is proved as in the paper: the forward direction is Lemma 2.24
`2-Mono Trivial Kernel`, since an equivalence is both a 2-monomorphism and a 2-epimorphism, and
the converse makes `e` and `m` separately equivalences by Corollary 3.16
`Trivial Kernel Normal Mono`.

## Not formalised

Nothing of Section 3 that belongs here; morphisms of short 2-exact sequences and the Normal
Short Five Lemma are in `SnakeLean.FiveLemma`, and the bipullback results of Section 5 in
`SnakeLean.Bipullback` and `SnakeLean.Squares`.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.Strict B]

/-- A 1-cell is **normal** when it factors, up to an invertible 2-cell, as a normal
2-epimorphism followed by a normal 2-monomorphism. -/
def IsNormal (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A') : Prop :=
  ∃ (I : B) (e : A ⟶ I) (m : I ⟶ A'), IsNormalEpi O e ∧ IsNormalMono O m ∧ Nonempty (f ≅ e ≫ m)

/-- A 1-cell is **antinormal** when it factors, up to an invertible 2-cell, as a normal
2-monomorphism followed by a normal 2-epimorphism. -/
def IsAntinormal (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A') : Prop :=
  ∃ (I : B) (m : A ⟶ I) (e : I ⟶ A'), IsNormalMono O m ∧ IsNormalEpi O e ∧ Nonempty (f ≅ m ≫ e)

section OppositeNormal

open Opposite Bicategory.Opposite

variable {O : B} [HasBizero O] {A A' : B}

omit [Strict B]

/-- Being normal is self-dual: a normal 2-epimorphism followed by a normal 2-monomorphism
dualises to a normal 2-epimorphism followed by a normal 2-monomorphism. -/
theorem isNormal_op {f : A ⟶ A'} (h : IsNormal O f) : IsNormal (op O) f.op := by
  obtain ⟨I, e, m, he, hm, ⟨θ⟩⟩ := h
  exact ⟨op I, m.op, e.op, isNormalEpi_op hm, isNormalMono_op he, ⟨θ.op2⟩⟩

theorem isNormal_of_op {f : A ⟶ A'} (h : IsNormal (op O) f.op) : IsNormal O f := by
  obtain ⟨I, e, m, he, hm, ⟨θ⟩⟩ := h
  exact ⟨I.unop, m.unop, e.unop, isNormalEpi_of_op (by simpa using hm),
    isNormalMono_of_op (by simpa using he), ⟨θ.unop2⟩⟩

theorem isNormal_op_iff {f : A ⟶ A'} : IsNormal (op O) f.op ↔ IsNormal O f :=
  ⟨isNormal_of_op, isNormal_op⟩

/-- Being antinormal is self-dual. -/
theorem isAntinormal_op {f : A ⟶ A'} (h : IsAntinormal O f) : IsAntinormal (op O) f.op := by
  obtain ⟨I, m, e, hm, he, ⟨θ⟩⟩ := h
  exact ⟨op I, e.op, m.op, isNormalMono_op he, isNormalEpi_op hm, ⟨θ.op2⟩⟩

theorem isAntinormal_of_op {f : A ⟶ A'} (h : IsAntinormal (op O) f.op) : IsAntinormal O f := by
  obtain ⟨I, m, e, hm, he, ⟨θ⟩⟩ := h
  exact ⟨I.unop, e.unop, m.unop, isNormalMono_of_op (by simpa using he),
    isNormalEpi_of_op (by simpa using hm), ⟨θ.unop2⟩⟩

theorem isAntinormal_op_iff {f : A ⟶ A'} : IsAntinormal (op O) f.op ↔ IsAntinormal O f :=
  ⟨isAntinormal_of_op, isAntinormal_op⟩

end OppositeNormal

section Composites

open Opposite Bicategory.Opposite

-- Neither half of `Composites of Normal Monos`(ii) inspects a hom-category of the bizero
-- object, so `[IsStrong O]` is absent from this section: a bizero object suffices.
variable {O : B} [HasBizero O] {x y z : B}

/-- **Proposition 3.6 `Composites of Normal Monos`(ii).** If `k ≅ f ≫ g` with `g` a 2-monomorphism
and `k` a normal 2-monomorphism, then `f` is a normal 2-monomorphism: if `k` is a 2-kernel of
`ℓ`, then `f` is a 2-kernel of `g ≫ ℓ`.

Unlike part (i), this genuinely needs `g` to be full and not merely faithful: fullness is what
lifts the factorisation of `z ≫ g` through `k` back to a factorisation of `z` through `f`. -/
theorem IsNormalMono.of_comp {f : x ⟶ y} {g : y ⟶ z} {k : x ⟶ z} (θ : k ≅ f ≫ g) [IsTwoMono g]
    (hk : IsNormalMono O k) : IsNormalMono O f := by
  obtain ⟨D, ℓ, hℓ⟩ := hk
  haveI := hℓ.isTwoMono
  refine ⟨D, g ≫ ℓ, ?_, fun t ht => ?_, isTwoMono_of_comp θ⟩
  · exact hℓ.isEssNull_comp.of_iso
      (Bicategory.whiskerRightIso θ ℓ ≪≫ eqToIso (Category.assoc f g ℓ))
  · obtain ⟨u, ⟨γ⟩⟩ := hℓ.fac (t ≫ g) (ht.of_iso (eqToIso (Category.assoc t g ℓ)).symm)
    exact ⟨u, ⟨IsTwoMono.preimageIso g (eqToIso (Category.assoc u f g) ≪≫
      Bicategory.whiskerLeftIso u θ.symm ≪≫ γ)⟩⟩

/-- The dual of `IsNormalMono.of_comp`: if `k ≅ f ≫ g` with `f` a 2-epimorphism and `k` a normal
2-epimorphism, then `g` is a normal 2-epimorphism. -/
theorem IsNormalEpi.of_comp {f : x ⟶ y} {g : y ⟶ z} {k : x ⟶ z} (θ : k ≅ f ≫ g) [IsTwoEpi f]
    (hk : IsNormalEpi O k) : IsNormalEpi O g :=
  haveI := isTwoMono_op f
  isNormalEpi_of_op (IsNormalMono.of_comp (g := f.op) θ.op2 (isNormalMono_op hk))

end Composites

section Equivalences

variable {O : B} [HasBizero O] [IsStrong O] {x y : B}

/-- An equivalence is a normal 2-monomorphism: it is a 2-kernel of a null 1-cell. This is the
implication `(i) ⟹ (ii)` of Corollary 3.18 `Equivalence Is Mono Plus Normal Epi`. -/
theorem IsEquiv1.isNormalMono {f : x ⟶ y} (h : IsEquiv1 f) : IsNormalMono O f :=
  ⟨O, zero1 O y O, ((isTwoKernel_id (O := O) y O).isEquiv1_comp h).of_iso_right
    (eqToIso (Category.comp_id f))⟩

/-- Dually, an equivalence is a normal 2-epimorphism. -/
theorem IsEquiv1.isNormalEpi {f : x ⟶ y} (h : IsEquiv1 f) : IsNormalEpi O f :=
  ⟨O, zero1 O O x, ((isTwoCokernel_id (O := O) O x).comp_isEquiv1 h).of_iso_right
    (eqToIso (Category.id_comp f))⟩

/-- **Corollary 3.18 `Equivalence Is Mono Plus Normal Epi`.** The paper states this in a 2-z-exact
2-category; no such hypothesis is needed. -/
theorem isEquiv1_tfae {f : x ⟶ y} :
    List.TFAE [IsEquiv1 f, IsNormalMono O f ∧ IsNormalEpi O f, IsNormalMono O f ∧ IsTwoEpi f,
      IsTwoMono f ∧ IsNormalEpi O f] := by
  tfae_have 1 → 2 := fun h => ⟨h.isNormalMono, h.isNormalEpi⟩
  tfae_have 2 → 3 := fun h => ⟨h.1, by obtain ⟨X, g, hg⟩ := h.2; exact hg.isTwoEpi⟩
  tfae_have 2 → 4 := fun h => ⟨by obtain ⟨Y, g, hg⟩ := h.1; exact hg.isTwoMono, h.2⟩
  tfae_have 3 → 1 := fun h => by haveI := h.2; exact isEquiv1_of_isNormalMono h.1
  tfae_have 4 → 1 := fun h => by haveI := h.1; exact isEquiv1_of_isNormalEpi h.2
  tfae_finish

end Equivalences

section Transport

/-!
### Transport along equivalences

Corollary 3.8 `C:NormalTransport` of the paper. Normal 2-monomorphisms and normal 2-epimorphisms are
stable under composition with an equivalence on either side, so that normality and antinormality
are invariant under replacing a 1-cell by `u ≫ w ≫ v` with `u` and `v` equivalences. Two of the
four halves come from `IsTwoKernel.isEquiv1_comp` and `IsTwoCokernel.comp_isEquiv1`; the other
two are the work here.

The paper needs this to reduce condition (DI2) in the 2-category of abelian categories to a
statement about the single composite of a 2-kernel with a 2-cokernel, and it does **not** follow
from Proposition 3.6 `Composites of Normal Monos`(ii), which runs in the opposite direction: that
proposition concludes normality of a factor from normality of the composite, whereas what is
wanted here is normality of the composite from normality of a factor.
-/

variable {O : B} [HasBizero O] [IsStrong O] {W X K K' A A' Q Q' : B}

/-- Precomposing a normal 2-monomorphism with an equivalence gives a normal 2-monomorphism. -/
theorem IsNormalMono.isEquiv1_comp {k : K ⟶ A} (hk : IsNormalMono O k) {u : K' ⟶ K}
    (hu : IsEquiv1 u) : IsNormalMono O (u ≫ k) :=
  ⟨hk.choose, hk.choose_spec.choose, hk.choose_spec.choose_spec.isEquiv1_comp hu⟩

/-- Postcomposing a normal 2-epimorphism with an equivalence gives a normal 2-epimorphism. -/
theorem IsNormalEpi.comp_isEquiv1 {q : A ⟶ Q} (hq : IsNormalEpi O q) {v : Q ⟶ Q'}
    (hv : IsEquiv1 v) : IsNormalEpi O (q ≫ v) :=
  ⟨hq.choose, hq.choose_spec.choose, hq.choose_spec.choose_spec.comp_isEquiv1 hv⟩

omit [IsStrong O] in
/-- **Postcomposing a normal 2-monomorphism with an equivalence gives a normal
2-monomorphism.** If `k` is a 2-kernel of `f` and `v` is an equivalence with quasi-inverse `v'`,
then `k ≫ v` is a 2-kernel of `v' ≫ f`. Strongness of the bizero object is not used. -/
theorem IsNormalMono.comp_isEquiv1 {k : K ⟶ A} (hk : IsNormalMono O k) {v : A ⟶ A'}
    (hv : IsEquiv1 v) : IsNormalMono O (k ≫ v) := by
  haveI : IsTwoMono v := hv.isTwoMono
  obtain ⟨Y, f, h⟩ := hk
  obtain ⟨v', ⟨η⟩, ⟨ε⟩⟩ := hv
  haveI := h.isTwoMono
  refine ⟨Y, v' ≫ f, h.isEssNull_comp.of_iso ?_, fun z hz => ?_, inferInstance⟩
  · calc k ≫ f ≅ k ≫ 𝟙 A ≫ f := eqToIso (by simp)
      _ ≅ k ≫ (v ≫ v') ≫ f := Bicategory.whiskerLeftIso k (Bicategory.whiskerRightIso η.symm f)
      _ ≅ (k ≫ v) ≫ v' ≫ f := eqToIso (by simp)
  · obtain ⟨u, ⟨γ⟩⟩ := h.fac (z ≫ v') (hz.of_iso (eqToIso (by simp)))
    refine ⟨u, ⟨?_⟩⟩
    calc u ≫ k ≫ v ≅ (u ≫ k) ≫ v := eqToIso (by simp)
      _ ≅ (z ≫ v') ≫ v := Bicategory.whiskerRightIso γ v
      _ ≅ z ≫ v' ≫ v := eqToIso (by simp)
      _ ≅ z ≫ 𝟙 A' := Bicategory.whiskerLeftIso z ε
      _ ≅ z := eqToIso (by simp)

omit [IsStrong O] in
/-- The dual: precomposing a normal 2-epimorphism with an equivalence gives a normal
2-epimorphism. Strongness of the bizero object is not used here either. -/
theorem IsNormalEpi.isEquiv1_comp {q : A ⟶ Q} (hq : IsNormalEpi O q) {u : A' ⟶ A}
    (hu : IsEquiv1 u) : IsNormalEpi O (u ≫ q) :=
  isNormalEpi_of_op ((isNormalMono_op hq).comp_isEquiv1 (isEquiv1_op hu))

omit [Strict B] [IsStrong O] in
/-- Normality only depends on a 1-cell up to an invertible 2-cell. -/
theorem IsNormal.of_iso {f g : A ⟶ A'} (θ : f ≅ g) (h : IsNormal O f) : IsNormal O g :=
  let ⟨I, e, m, he, hm, ⟨σ⟩⟩ := h
  ⟨I, e, m, he, hm, ⟨θ.symm ≪≫ σ⟩⟩

omit [Strict B] [IsStrong O] in
/-- Antinormality only depends on a 1-cell up to an invertible 2-cell. -/
theorem IsAntinormal.of_iso {f g : A ⟶ A'} (θ : f ≅ g) (h : IsAntinormal O f) :
    IsAntinormal O g :=
  let ⟨I, m, e, hm, he, ⟨σ⟩⟩ := h
  ⟨I, m, e, hm, he, ⟨θ.symm ≪≫ σ⟩⟩

omit [IsStrong O] in
/-- **Normality is invariant under composing with equivalences on either side.** -/
theorem IsNormal.transport {w : A ⟶ A'} (hw : IsNormal O w) {u : W ⟶ A} (hu : IsEquiv1 u)
    {v : A' ⟶ X} (hv : IsEquiv1 v) : IsNormal O (u ≫ w ≫ v) := by
  obtain ⟨I, e, m, he, hm, ⟨θ⟩⟩ := hw
  refine ⟨I, u ≫ e, m ≫ v, he.isEquiv1_comp hu, hm.comp_isEquiv1 hv, ⟨?_⟩⟩
  calc u ≫ w ≫ v ≅ u ≫ (e ≫ m) ≫ v :=
        Bicategory.whiskerLeftIso u (Bicategory.whiskerRightIso θ v)
    _ ≅ (u ≫ e) ≫ m ≫ v := eqToIso (by simp)

/-- **Antinormality is invariant under composing with equivalences on either side.** -/
theorem IsAntinormal.transport {w : A ⟶ A'} (hw : IsAntinormal O w) {u : W ⟶ A}
    (hu : IsEquiv1 u) {v : A' ⟶ X} (hv : IsEquiv1 v) : IsAntinormal O (u ≫ w ≫ v) := by
  obtain ⟨I, m, e, hm, he, ⟨θ⟩⟩ := hw
  refine ⟨I, u ≫ m, e ≫ v, hm.isEquiv1_comp hu, he.comp_isEquiv1 hv, ⟨?_⟩⟩
  calc u ≫ w ≫ v ≅ u ≫ (m ≫ e) ≫ v :=
        Bicategory.whiskerLeftIso u (Bicategory.whiskerRightIso θ v)
    _ ≅ (u ≫ m) ≫ e ≫ v := eqToIso (by simp)

/-- The invertible 2-cell that cancels a pair of equivalences off a 1-cell. -/
private noncomputable def cancelEquivIso {w : A ⟶ A'} {u : W ⟶ A} (hu : IsEquiv1 u) {v : A' ⟶ X}
    (hv : IsEquiv1 v) : hu.inv ≫ (u ≫ w ≫ v) ≫ hv.inv ≅ w :=
  calc hu.inv ≫ (u ≫ w ≫ v) ≫ hv.inv
      ≅ (hu.inv ≫ u) ≫ w ≫ v ≫ hv.inv := eqToIso (by simp)
    _ ≅ 𝟙 A ≫ w ≫ v ≫ hv.inv :=
        Bicategory.whiskerRightIso hu.nonempty_inv_comp.some _
    _ ≅ w ≫ v ≫ hv.inv := eqToIso (by simp)
    _ ≅ w ≫ 𝟙 A' := Bicategory.whiskerLeftIso w hv.nonempty_comp_inv.some
    _ ≅ w := eqToIso (by simp)

omit [IsStrong O] in
/-- **Corollary 3.8 `C:NormalTransport`.** A 1-cell of the form `u ≫ w ≫ v`, with `u` and `v`
equivalences, is normal exactly when `w` is. -/
theorem isNormal_transport_iff {w : A ⟶ A'} {u : W ⟶ A} (hu : IsEquiv1 u) {v : A' ⟶ X}
    (hv : IsEquiv1 v) : IsNormal O (u ≫ w ≫ v) ↔ IsNormal O w :=
  ⟨fun h => IsNormal.of_iso (cancelEquivIso hu hv)
      (h.transport hu.isEquiv1_inv hv.isEquiv1_inv),
    fun h => h.transport hu hv⟩

/-- The antinormal counterpart of `isNormal_transport_iff`. -/
theorem isAntinormal_transport_iff {w : A ⟶ A'} {u : W ⟶ A} (hu : IsEquiv1 u) {v : A' ⟶ X}
    (hv : IsEquiv1 v) : IsAntinormal O (u ≫ w ≫ v) ↔ IsAntinormal O w :=
  ⟨fun h => IsAntinormal.of_iso (cancelEquivIso hu hv)
      (h.transport hu.isEquiv1_inv hv.isEquiv1_inv),
    fun h => h.transport hu hv⟩

end Transport

section Image

open Opposite Bicategory.Opposite

variable {O : B} [HasBizero O] [IsStrong O] {X Y K I I' A A' Q : B}

/-- **Corollary 3.19 `Normal Mono Criterion`.** A 1-cell is a normal 2-monomorphism exactly when
it is a 2-monomorphism that is normal. -/
theorem isNormalMono_iff {f : A ⟶ Y} {k : K ⟶ A} (hk : IsTwoKernel O f k) :
    IsNormalMono O f ↔ IsTwoMono f ∧ IsNormal O f := by
  constructor
  · rintro ⟨Z, ℓ, hℓ⟩
    exact ⟨hℓ.isTwoMono, A, 𝟙 A, f, (isEquiv1_id A).isNormalEpi, ⟨Z, ℓ, hℓ⟩,
      ⟨(eqToIso (Category.id_comp f)).symm⟩⟩
  · rintro ⟨hf, I, e, m, he, hm, ⟨θ⟩⟩
    haveI := hf
    exact (isNormalMono_of_isTrivial θ he hm hk hk.isTrivial_of_isTwoMono).2

/-- Dually, a 1-cell is a normal 2-epimorphism exactly when it is a 2-epimorphism that is
normal. -/
theorem isNormalEpi_iff {f : X ⟶ A} {q : A ⟶ Q} (hq : IsTwoCokernel O f q) :
    IsNormalEpi O f ↔ IsTwoEpi f ∧ IsNormal O f := by
  rw [← isNormalMono_op_iff (q := f), ← isTwoMono_op_iff f, ← isNormal_op_iff (f := f)]
  exact isNormalMono_iff (isTwoKernel_op hq)

/-- **Proposition 3.22 `Image Factorisation of Normal Map is Unique`.** A factorisation of `f` as a
normal 2-epimorphism followed by a normal 2-monomorphism is unique up to equivalence, and any
factorisation as a 2-epimorphism followed by a 2-monomorphism is comparable to it. -/
theorem imageFactorisation_unique {f : A ⟶ A'} {e : A ⟶ I} {m : I ⟶ A'} {e' : A ⟶ I'}
    {m' : I' ⟶ A'} (θ : f ≅ e ≫ m) (θ' : f ≅ e' ≫ m') (he : IsNormalEpi O e)
    (hm : IsNormalMono O m) [IsTwoEpi e'] [IsTwoMono m'] {k : K ⟶ A} (hk : IsTwoKernel O f k) :
    ∃ t : I ⟶ I', IsEquiv1 t ∧ Nonempty (e ≫ t ≅ e') ∧ Nonempty (t ≫ m' ≅ m) := by
  obtain ⟨W, g, hg⟩ := he
  obtain ⟨Z, ℓ, hℓ⟩ := hm
  haveI := hg.isTwoEpi
  haveI := hℓ.isTwoMono
  have hke : IsTwoKernel O e k := (isTwoKernel_comp_isTwoMono_iff m).mp (hk.of_iso θ)
  have hek : IsTwoCokernel O k e := hg.of_isTwoKernel hke
  have hke' : IsEssNull O (k ≫ e') :=
    IsEssNull.of_comp_isTwoMono m' (hk.isEssNull_comp.of_iso
      (Bicategory.whiskerLeftIso k θ' ≪≫ (eqToIso (Category.assoc k e' m')).symm))
  obtain ⟨t, ⟨γ⟩⟩ := hek.fac e' hke'
  have σ : t ≫ m' ≅ m := IsTwoEpi.preimageIso e
    ((eqToIso (Category.assoc e t m')).symm ≪≫ Bicategory.whiskerRightIso γ m' ≪≫ θ'.symm ≪≫ θ)
  have htm : IsNormalMono O t := IsNormalMono.of_comp σ.symm ⟨Z, ℓ, hℓ⟩
  haveI : IsTwoEpi t := isTwoEpi_of_comp γ.symm
  exact ⟨t, isEquiv1_of_isNormalMono htm, ⟨γ⟩, ⟨σ⟩⟩

/-- The second assertion of Proposition 3.22 `Image Factorisation of Normal Map is Unique`: a
factorisation of a normal 1-cell as a 2-epimorphism followed by a 2-monomorphism is automatically
a factorisation as a normal 2-epimorphism followed by a normal 2-monomorphism. -/
theorem isNormal_of_factorisation {f : A ⟶ A'} {e : A ⟶ I} {m : I ⟶ A'} {e' : A ⟶ I'}
    {m' : I' ⟶ A'} (θ : f ≅ e ≫ m) (θ' : f ≅ e' ≫ m') (he : IsNormalEpi O e)
    (hm : IsNormalMono O m) [IsTwoEpi e'] [IsTwoMono m'] {k : K ⟶ A} (hk : IsTwoKernel O f k) :
    IsNormalEpi O e' ∧ IsNormalMono O m' := by
  obtain ⟨t, ht, ⟨γ⟩, ⟨σ⟩⟩ := imageFactorisation_unique θ θ' he hm hk
  obtain ⟨W, g, hg⟩ := he
  obtain ⟨Z, ℓ, hℓ⟩ := hm
  obtain ⟨t', ⟨η⟩, ⟨ε⟩⟩ := ht
  refine ⟨⟨W, g, (hg.comp_isEquiv1 ⟨t', ⟨η⟩, ⟨ε⟩⟩).of_iso_right γ⟩, Z, ℓ, ?_⟩
  refine ((hℓ.of_iso_right σ.symm).isEquiv1_comp (isEquiv1_of_inv η ε)).of_iso_right ?_
  exact (eqToIso (Category.assoc t' t m')).symm ≪≫ Bicategory.whiskerRightIso ε m' ≪≫
    eqToIso (Category.id_comp m')

/-- **Proposition 3.20 `Normal Equivalence Trivial`.** A normal 1-cell is an equivalence exactly
when its 2-kernel and its 2-cokernel are trivial. -/
theorem isEquiv1_iff_isTrivial {f : A ⟶ A'} {e : A ⟶ I} {m : I ⟶ A'} (θ : f ≅ e ≫ m)
    (he : IsNormalEpi O e) (hm : IsNormalMono O m) {k : K ⟶ A} (hk : IsTwoKernel O f k)
    {q : A' ⟶ Q} (hq : IsTwoCokernel O f q) : IsEquiv1 f ↔ IsTrivial O K ∧ IsTrivial O Q := by
  constructor
  · intro hf
    haveI := hf.isTwoMono
    haveI := hf.isTwoEpi
    exact ⟨hk.isTrivial_of_isTwoMono, hq.isTrivial_of_isTwoEpi⟩
  · rintro ⟨hK, hQ⟩
    exact IsEquiv1.of_iso θ.symm
      (((isNormalMono_of_isTrivial θ he hm hk hK).1).comp
        ((isNormalEpi_of_isTrivial θ he hm hq hQ).1))

end Image

end SnakeLean
