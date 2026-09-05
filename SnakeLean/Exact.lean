/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.Kernel

/-!
# Trivial objects, short 2-exact sequences, and normal 1-cells

This module formalises the spine of Section 3 of *A two-categorical Snake Lemma*: trivial
objects, short 2-exact sequences, the fact that a normal 2-epimorphism is a 2-cokernel of its
2-kernel, and the characterisation of the sequences whose kernel part is trivial.

## Trivial objects

Definition 2.9 `Def Trivial` calls an object trivial when its identity is isomorphic to a null
1-cell, and `IsTrivial O X` is exactly that, `IsEssNull O (𝟙 X)`. Remark 2.10 `Rem Trivial`
derives that a trivial object is equivalent to a bizero object — `IsTrivial.isEquiv1_toZero` —
and explains why the identity condition is the definition: it is what makes the arguments short,
a single reflection step by a 2-monomorphism turning "the 1-cell is null" into "its domain is
trivial".

## The definition of a short 2-exact sequence

`IsSES O k q` asks that `k` be a 2-kernel of `q` and that `q` be a 2-cokernel of `k`, which is
Definition 3.12 `Def:SES`. The definition writes a single invertible 2-cell `κ : q ∘ k ≅ 0` for
both universal properties, and is entitled to: there is only one, as explained in
`SnakeLean.Kernel`.

## Two reflections

`IsTwoKernel.isTrivial_of_isTwoMono` — Lemma 2.24 `2-Mono Trivial Kernel`, that a 2-monomorphism
has trivial 2-kernel — is proved as in the paper, by reflecting nullity twice: `k ≫ m` is null,
so `k` is null since `m` reflects nullity, so `𝟙 K ≫ k` is null, so `𝟙 K` is null since `k`
reflects nullity. As the paper notes after the proof, no hom-category is inspected and the
bizero condition is never used, only strongness.

## Main results

* `IsTwoCokernel.of_isTwoKernel` and `IsTwoKernel.of_isTwoCokernel` — Proposition 3.11
  `kernel is kernel of its cokernel`.
* `IsSES.isTrivial_iff_isEquiv1` — Proposition 3.15 `Prop Equivalence CoKernel`.
* `isNormalMono_of_isTrivial` and `isNormalEpi_of_isTrivial` — Corollary 3.16
  `Trivial Kernel Normal Mono`.
* `isEquiv1_of_isNormalEpi` and `isEquiv1_of_isNormalMono` — Proposition 3.17
  `Normal Epi Mono Equivalence`: a normal 2-epimorphism that is a 2-monomorphism is an
  equivalence, and dually.

## The direct route to Proposition 3.17

An earlier draft folded `Normal Epi Mono Equivalence` into `Trivial Kernel Normal Mono` and
derived it from `Prop Equivalence CoKernel`, which needs a short 2-exact sequence and hence the
2-kernel of the 1-cell in question. That detour is avoidable, and the paper now states the result
separately with the direct proof. A normal 2-epimorphism `q` is the 2-cokernel of some `g`; if `q`
is also a 2-monomorphism it reflects `g ≫ q ≅ 0` to `g ≅ 0`, so the identity of the codomain of
`g` factors through `q`, and one preimage of an invertible 2-cell along `q` completes the
quasi-inverse. `isEquiv1_of_isNormalEpi` and `isEquiv1_of_isNormalMono` are stated accordingly,
with no 2-kernel or 2-cokernel hypothesis at all.

## Not formalised

Normal 1-cells, Corollary 3.18 `Equivalence Is Mono Plus Normal Epi` and the normal image
factorisation are in `SnakeLean.Normal`; the Normal Short Five Lemma is in
`SnakeLean.FiveLemma`. The class asserting that all 2-kernels and 2-cokernels exist — the
paper's 2-z-exactness, `TwoZExact` — is in `SnakeLean.ZExact`; the results here take the
2-kernel or 2-cokernel they need as an explicit hypothesis instead, which is all they consume.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.Strict B]

/-- An object is **trivial** when its identity 1-cell is essentially null.

This is Definition 2.9 `Def Trivial`. No bizero object is required: as Remark 2.10 `Rem Trivial`
observes, taking the condition on `𝟙 X` as the definition turns every question of triviality
into a question about a single 1-cell being null. -/
def IsTrivial (O : B) (X : B) : Prop :=
  IsEssNull O (𝟙 X)

section OppositeTrivial

open Opposite Bicategory.Opposite

omit [Strict B]

/-- Being trivial is self-dual. -/
theorem isTrivial_op {O X : B} (h : IsTrivial O X) : IsTrivial (op O) (op X) :=
  isEssNull_op h

/-- Triviality transports back along the 1-cell dual. -/
theorem isTrivial_of_op {O X : B} (h : IsTrivial (op O) (op X)) : IsTrivial O X :=
  isEssNull_of_op h

/-- Triviality in `Bᵒᵖ` and in `B` agree. -/
theorem isTrivial_op_iff {O X : B} : IsTrivial (op O) (op X) ↔ IsTrivial O X :=
  ⟨isTrivial_of_op, isTrivial_op⟩

end OppositeTrivial

section Trivial

variable {O : B} [HasBizero O] [IsStrong O] {X Y K A A' Q : B}

/-- Every 1-cell out of a trivial object is essentially null. -/
theorem IsTrivial.isEssNull_out (h : IsTrivial O X) (f : X ⟶ Y) : IsEssNull O f :=
  IsEssNull.of_iso (eqToIso (Category.id_comp f)) (h.comp f)

/-- Every 1-cell into a trivial object is essentially null. -/
theorem IsTrivial.isEssNull_in (h : IsTrivial O X) (f : Y ⟶ X) : IsEssNull O f :=
  IsEssNull.of_iso (eqToIso (Category.comp_id f)) (h.comp_left f)

/-- A trivial object is equivalent to the bizero object: the forward half of Remark 2.10
`Rem Trivial`. -/
theorem IsTrivial.isEquiv1_toZero (h : IsTrivial O X) :
    IsEquiv1 (HasBizero.toZero (O := O) X) := by
  rw [IsTrivial, isEssNull_iff] at h
  obtain ⟨θ⟩ := h
  refine ⟨HasBizero.fromZero (O := O) X, ⟨θ.symm⟩, ?_⟩
  exact (isNull_to (HasBizero.fromZero (O := O) X ≫ HasBizero.toZero (O := O) X)).nonempty_iso
    (isNull_to (𝟙 O))

/-- **Lemma 2.24 `2-Mono Trivial Kernel`.** A 2-monomorphism has trivial 2-kernel. -/
theorem IsTwoKernel.isTrivial_of_isTwoMono {m : A ⟶ A'} [IsTwoMono m] {k : K ⟶ A}
    (h : IsTwoKernel O m k) : IsTrivial O K := by
  haveI := h.isTwoMono
  have hk : IsEssNull O k := IsEssNull.of_comp_isTwoMono m h.isEssNull_comp
  exact IsEssNull.of_comp_isTwoMono k
    (IsEssNull.of_iso (eqToIso (Category.id_comp k)).symm hk)

/-- Dually, a 2-epimorphism has trivial 2-cokernel. -/
theorem IsTwoCokernel.isTrivial_of_isTwoEpi {e : A ⟶ A'} [IsTwoEpi e] {q : A' ⟶ Q}
    (h : IsTwoCokernel O e q) : IsTrivial O Q :=
  haveI := isTwoMono_op e
  isTrivial_of_op (isTwoKernel_op h).isTrivial_of_isTwoMono

end Trivial

/-- A **short 2-exact sequence**: `k` is a 2-kernel of `q` and `q` is a 2-cokernel of `k`. -/
structure IsSES (O : B) [HasBizero O] {K A Q : B} (k : K ⟶ A) (q : A ⟶ Q) : Prop where
  /-- `k` is a 2-kernel of `q`. -/
  isTwoKernel : IsTwoKernel O q k
  /-- `q` is a 2-cokernel of `k`. -/
  isTwoCokernel : IsTwoCokernel O k q

/-- A 1-cell is a **normal 2-monomorphism** when it occurs as a 2-kernel. -/
def IsNormalMono (O : B) [HasBizero O] {K A : B} (k : K ⟶ A) : Prop :=
  ∃ (Y : B) (f : A ⟶ Y), IsTwoKernel O f k

/-- A 1-cell is a **normal 2-epimorphism** when it occurs as a 2-cokernel. -/
def IsNormalEpi (O : B) [HasBizero O] {A Q : B} (q : A ⟶ Q) : Prop :=
  ∃ (X : B) (f : X ⟶ A), IsTwoCokernel O f q

omit [Strict B] in
theorem IsNormalMono.isTwoMono {O : B} [HasBizero O] {K A : B} {k : K ⟶ A}
    (h : IsNormalMono O k) : IsTwoMono k :=
  h.choose_spec.choose_spec.isTwoMono

omit [Strict B] in
theorem IsNormalEpi.isTwoEpi {O : B} [HasBizero O] {A Q : B} {q : A ⟶ Q}
    (h : IsNormalEpi O q) : IsTwoEpi q :=
  h.choose_spec.choose_spec.isTwoEpi

section OppositeNormal

open Opposite Bicategory.Opposite

variable {O : B} [HasBizero O] {K A Q : B}

omit [Strict B]

/-- Normal 2-monomorphisms dualise to normal 2-epimorphisms. -/
theorem isNormalEpi_op {k : K ⟶ A} (h : IsNormalMono O k) : IsNormalEpi (op O) k.op := by
  obtain ⟨Y, f, hf⟩ := h
  exact ⟨op Y, f.op, isTwoCokernel_op hf⟩

/-- Normal 2-epimorphisms dualise to normal 2-monomorphisms. -/
theorem isNormalMono_op {q : A ⟶ Q} (h : IsNormalEpi O q) : IsNormalMono (op O) q.op := by
  obtain ⟨X, f, hf⟩ := h
  exact ⟨op X, f.op, isTwoKernel_op hf⟩

theorem isNormalMono_of_op {k : K ⟶ A} (h : IsNormalEpi (op O) k.op) : IsNormalMono O k := by
  obtain ⟨X, f, hf⟩ := h
  exact ⟨X.unop, f.unop, isTwoKernel_of_op (by simpa using hf)⟩

theorem isNormalEpi_of_op {q : A ⟶ Q} (h : IsNormalMono (op O) q.op) : IsNormalEpi O q := by
  obtain ⟨Y, f, hf⟩ := h
  exact ⟨Y.unop, f.unop, isTwoCokernel_of_op (by simpa using hf)⟩

theorem isNormalEpi_op_iff {k : K ⟶ A} : IsNormalEpi (op O) k.op ↔ IsNormalMono O k :=
  ⟨isNormalMono_of_op, isNormalEpi_op⟩

theorem isNormalMono_op_iff {q : A ⟶ Q} : IsNormalMono (op O) q.op ↔ IsNormalEpi O q :=
  ⟨isNormalEpi_of_op, isNormalMono_op⟩

/-- A short 2-exact sequence dualises to one with its two halves exchanged. -/
theorem isSES_op {k : K ⟶ A} {q : A ⟶ Q} (h : IsSES O k q) : IsSES (op O) q.op k.op where
  isTwoKernel := isTwoKernel_op h.isTwoCokernel
  isTwoCokernel := isTwoCokernel_op h.isTwoKernel

theorem isSES_of_op {k : K ⟶ A} {q : A ⟶ Q} (h : IsSES (op O) q.op k.op) : IsSES O k q where
  isTwoKernel := isTwoKernel_of_op (by simpa using h.isTwoCokernel)
  isTwoCokernel := isTwoCokernel_of_op (by simpa using h.isTwoKernel)

theorem isSES_op_iff {k : K ⟶ A} {q : A ⟶ Q} : IsSES (op O) q.op k.op ↔ IsSES O k q :=
  ⟨isSES_of_op, isSES_op⟩

end OppositeNormal

section SES

open Opposite Bicategory.Opposite

variable {O : B} [HasBizero O] [IsStrong O] {X Y K K' A A' I Q Q' : B}

omit [Strict B] [IsStrong O] in
/-- A 1-cell isomorphic to a 2-kernel is a 2-kernel of the same 1-cell. -/
theorem IsTwoKernel.of_iso_right {f : A ⟶ Y} {k k' : K ⟶ A} (θ : k ≅ k')
    (h : IsTwoKernel O f k) : IsTwoKernel O f k' where
  isEssNull_comp := h.isEssNull_comp.of_iso (Bicategory.whiskerRightIso θ f)
  fac z hz :=
    let ⟨u, ⟨γ⟩⟩ := h.fac z hz
    ⟨u, ⟨Bicategory.whiskerLeftIso u θ.symm ≪≫ γ⟩⟩
  isTwoMono := haveI := h.isTwoMono; IsTwoMono.of_iso θ

omit [Strict B] [IsStrong O] in
/-- A 1-cell isomorphic to a 2-cokernel is a 2-cokernel of the same 1-cell. -/
theorem IsTwoCokernel.of_iso_right {f : X ⟶ A} {q q' : A ⟶ Q} (θ : q ≅ q')
    (h : IsTwoCokernel O f q) : IsTwoCokernel O f q' :=
  isTwoCokernel_of_op ((isTwoKernel_op h).of_iso_right θ.op2)

/-- Precomposing a 2-kernel with an equivalence gives a 2-kernel of the same 1-cell. -/
theorem IsTwoKernel.isEquiv1_comp {f : A ⟶ Y} {k : K ⟶ A} (h : IsTwoKernel O f k)
    {e : K' ⟶ K} (he : IsEquiv1 e) : IsTwoKernel O f (e ≫ k) := by
  obtain ⟨e', ⟨η⟩, ⟨ε⟩⟩ := he
  haveI := h.isTwoMono
  haveI := (IsEquiv1.isTwoMono ⟨e', ⟨η⟩, ⟨ε⟩⟩ : IsTwoMono e)
  refine ⟨h.isEssNull_comp.comp_left e |>.of_iso (eqToIso (Category.assoc e k f)).symm,
    fun z hz => ?_, inferInstance⟩
  obtain ⟨u, ⟨γ⟩⟩ := h.fac z hz
  refine ⟨u ≫ e', ⟨?_⟩⟩
  calc (u ≫ e') ≫ e ≫ k ≅ u ≫ (e' ≫ e) ≫ k := eqToIso (by simp)
    _ ≅ u ≫ 𝟙 K ≫ k := Bicategory.whiskerLeftIso u (Bicategory.whiskerRightIso ε k)
    _ ≅ u ≫ k := eqToIso (by simp)
    _ ≅ z := γ

/-- Postcomposing a 2-cokernel with an equivalence gives a 2-cokernel of the same 1-cell. -/
theorem IsTwoCokernel.comp_isEquiv1 {f : X ⟶ A} {q : A ⟶ Q} (h : IsTwoCokernel O f q)
    {e : Q ⟶ Q'} (he : IsEquiv1 e) : IsTwoCokernel O f (q ≫ e) :=
  isTwoCokernel_of_op ((isTwoKernel_op h).isEquiv1_comp (isEquiv1_op he))

/-- **Proposition 3.11 `kernel is kernel of its cokernel`.** A 2-cokernel is a 2-cokernel of its
own 2-kernel. -/
theorem IsTwoCokernel.of_isTwoKernel {f : X ⟶ A} {q : A ⟶ Q} {k : K ⟶ A}
    (hq : IsTwoCokernel O f q) (hk : IsTwoKernel O q k) : IsTwoCokernel O k q where
  isEssNull_comp := hk.isEssNull_comp
  fac z hz := by
    obtain ⟨w, ⟨θ⟩⟩ := hk.fac f hq.isEssNull_comp
    exact hq.fac z (IsEssNull.of_iso
      ((eqToIso (Category.assoc w k z)).symm ≪≫ Bicategory.whiskerRightIso θ z) (hz.comp_left w))
  isTwoEpi := hq.isTwoEpi

/-- Dually, a 2-kernel is a 2-kernel of its own 2-cokernel. -/
theorem IsTwoKernel.of_isTwoCokernel {f : A ⟶ Y} {k : K ⟶ A} {q : A ⟶ Q}
    (hk : IsTwoKernel O f k) (hq : IsTwoCokernel O k q) : IsTwoKernel O q k :=
  isTwoKernel_of_op ((isTwoCokernel_op hk).of_isTwoKernel (isTwoKernel_op hq))

/-- A normal 2-monomorphism, together with its 2-cokernel, forms a short 2-exact sequence. -/
theorem isSES_of_isTwoKernel {f : A ⟶ Y} {k : K ⟶ A} {q : A ⟶ Q} (hk : IsTwoKernel O f k)
    (hq : IsTwoCokernel O k q) : IsSES O k q :=
  ⟨hk.of_isTwoCokernel hq, hq⟩

/-- A normal 2-epimorphism, together with its 2-kernel, forms a short 2-exact sequence. -/
theorem isSES_of_isTwoCokernel {f : X ⟶ A} {q : A ⟶ Q} {k : K ⟶ A} (hq : IsTwoCokernel O f q)
    (hk : IsTwoKernel O q k) : IsSES O k q :=
  ⟨hk, hq.of_isTwoKernel hk⟩

/-- **Proposition 3.15 `Prop Equivalence CoKernel`.** In a short 2-exact sequence the kernel
object is trivial exactly when the 2-cokernel is an equivalence. -/
theorem IsSES.isTrivial_iff_isEquiv1 {k : K ⟶ A} {q : A ⟶ Q} (h : IsSES O k q) :
    IsTrivial O K ↔ IsEquiv1 q := by
  haveI := h.isTwoKernel.isTwoMono
  haveI := h.isTwoCokernel.isTwoEpi
  constructor
  · intro hK
    obtain ⟨u, ⟨θ⟩⟩ := h.isTwoCokernel.fac (𝟙 A)
      (IsEssNull.of_iso (eqToIso (Category.comp_id k)).symm (hK.isEssNull_out k))
    refine ⟨u, ⟨θ⟩, ⟨IsTwoEpi.preimageIso q ?_⟩⟩
    exact (eqToIso (Category.assoc q u q)).symm ≪≫ Bicategory.whiskerRightIso θ q ≪≫
      eqToIso (by simp)
  · rintro ⟨g, ⟨η⟩, -⟩
    have h2 : IsEssNull O k := IsEssNull.of_iso
      (eqToIso (Category.assoc k q g) ≪≫ Bicategory.whiskerLeftIso k η ≪≫ eqToIso (by simp))
      (h.isTwoKernel.isEssNull_comp.comp g)
    exact IsEssNull.of_comp_isTwoMono k (IsEssNull.of_iso (eqToIso (Category.id_comp k)).symm h2)

/-- The dual of `IsSES.isTrivial_iff_isEquiv1`: the cokernel object is trivial exactly when the
2-kernel is an equivalence. -/
theorem IsSES.isTrivial_iff_isEquiv1' {k : K ⟶ A} {q : A ⟶ Q} (h : IsSES O k q) :
    IsTrivial O Q ↔ IsEquiv1 k := by
  rw [← isTrivial_op_iff (O := O) (X := Q), ← isEquiv1_op_iff k]
  exact (isSES_op h).isTrivial_iff_isEquiv1

/-- **Proposition 3.17 `Normal Epi Mono Equivalence`.** A normal 2-epimorphism that is a
2-monomorphism is an equivalence.

The 2-kernel of `q` is not needed, and the paper's proof is this one: a normal 2-epimorphism `q`
is the 2-cokernel of some `g`, and `q` being a 2-monomorphism reflects `g ≫ q ≅ 0` to `g ≅ 0`,
after which the identity of `A` factors
through `q`. -/
theorem isEquiv1_of_isNormalEpi {q : A ⟶ Q} [IsTwoMono q] (hq : IsNormalEpi O q) : IsEquiv1 q := by
  obtain ⟨X, g, hg⟩ := hq
  haveI := hg.isTwoEpi
  have hgnull : IsEssNull O g := IsEssNull.of_comp_isTwoMono q hg.isEssNull_comp
  obtain ⟨u, ⟨γ⟩⟩ := hg.fac (𝟙 A) (hgnull.of_iso (eqToIso (Category.comp_id g)).symm)
  refine ⟨u, ⟨γ⟩, ⟨IsTwoEpi.preimageIso q ?_⟩⟩
  exact (eqToIso (Category.assoc q u q)).symm ≪≫ Bicategory.whiskerRightIso γ q ≪≫
    eqToIso (by simp)

/-- The dual: a normal 2-monomorphism that is a 2-epimorphism is an equivalence, again with no
2-cokernel hypothesis. -/
theorem isEquiv1_of_isNormalMono {k : K ⟶ A} [IsTwoEpi k] (hk : IsNormalMono O k) :
    IsEquiv1 k :=
  haveI := isTwoMono_op k
  isEquiv1_of_op (isEquiv1_of_isNormalEpi (isNormalEpi_op hk))

/-- **Corollary 3.16 `Trivial Kernel Normal Mono`.** If a 1-cell factors, up to an invertible
2-cell,
as a normal 2-epimorphism followed by a normal 2-monomorphism, and its 2-kernel is trivial, then
the 2-epimorphism is an equivalence and the 1-cell is a normal 2-monomorphism. -/
theorem isNormalMono_of_isTrivial {f : A ⟶ Y} {e : A ⟶ I} {m : I ⟶ Y} (θ : f ≅ e ≫ m)
    (he : IsNormalEpi O e) (hm : IsNormalMono O m) {k : K ⟶ A} (hk : IsTwoKernel O f k)
    (hK : IsTrivial O K) : IsEquiv1 e ∧ IsNormalMono O f := by
  obtain ⟨X, g, hg⟩ := he
  obtain ⟨Z, ℓ, hℓ⟩ := hm
  haveI := hℓ.isTwoMono
  have hke : IsTwoKernel O e k :=
    (isTwoKernel_comp_isTwoMono_iff m).mp (hk.of_iso θ)
  have hse : IsSES O k e := isSES_of_isTwoCokernel hg hke
  have hee : IsEquiv1 e := hse.isTrivial_iff_isEquiv1.mp hK
  exact ⟨hee, Z, ℓ, (hℓ.isEquiv1_comp hee).of_iso_right θ.symm⟩

/-- The dual of `isNormalMono_of_isTrivial`: if a 1-cell factors, up to an invertible 2-cell, as a
normal 2-epimorphism followed by a normal 2-monomorphism, and its 2-cokernel is trivial, then the
2-monomorphism is an equivalence and the 1-cell is a normal 2-epimorphism. -/
theorem isNormalEpi_of_isTrivial {f : X ⟶ A} {e : X ⟶ I} {m : I ⟶ A} (θ : f ≅ e ≫ m)
    (he : IsNormalEpi O e) (hm : IsNormalMono O m) {q : A ⟶ Q} (hq : IsTwoCokernel O f q)
    (hQ : IsTrivial O Q) : IsEquiv1 m ∧ IsNormalEpi O f := by
  obtain ⟨h1, h2⟩ := isNormalMono_of_isTrivial (O := op O) θ.op2 (isNormalEpi_op hm)
    (isNormalMono_op he) (isTwoKernel_op hq) (isTrivial_op hQ)
  exact ⟨isEquiv1_of_op h1, isNormalEpi_of_op h2⟩

end SES

end SnakeLean
