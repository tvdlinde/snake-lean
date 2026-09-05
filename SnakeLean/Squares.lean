/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.Bipullback
import SnakeLean.FiveLemma

/-!
# The squares of a morphism of short 2-exact sequences

This module formalises Propositions 5.7 `Mono Implies Left Pullback` and 5.9
`Right Square Pullback`.

## No bipullback but the one asserted

The paper's proof of `Mono Implies Left Pullback` verifies the universal property of the
left-hand square directly, and Remark 5.8 `Rem Left Pullback Cost` records that it forms no
bipullback other than the one it asserts. The proof here is the same. Given a square over the
cospan, its `A'`-component `b` satisfies `b ∘ q' ∘ h ≅ 0`, so `b ∘ q' ≅ 0` because `h` reflects
null morphisms, so `b` factors through the 2-kernel `k'`; the second factorisation 2-cell and the
pasting condition are then forced, because `k` is a 2-monomorphism. That is
`isBipullback_of_isTwoMono`.

Stated at the strength the argument consumes, as in Remark 5.8, the proposition needs neither
row to be a short 2-exact sequence: `q` may be an arbitrary 1-cell with `k` a 2-kernel of it, and
`q'` need not be a 2-cokernel. This is the same shape as Remark 3.29 `Rem NSFL Hypotheses` for
the Normal Short Five Lemma in `SnakeLean.FiveLemma`.

## Main results

* `isBipullback_left_of_isTwoMono` — Proposition 5.7 `Mono Implies Left Pullback`.
* `isEquiv1_of_isBipullback_right` — Proposition 5.9 `Right Square Pullback`.
* `isEquiv1_of_isBipushout_left` — Proposition 5.10 `Left Square Pushout`.

## The compatibility in `Right Square Pullback`

The proof of `Right Square Pullback` has to make two comparison 2-cells compatible before the
uniqueness half of the bipullback property can be applied. The compatibility asked for is an
equation between invertible 2-cells whose common codomain is essentially null, and any two such
agree: Lemma 2.6 `L:UniqueNull`, here `isEssNull_hom_ext`. The paper's proof appeals to that
lemma at this point, and notes after it that this is where a coherence condition on morphisms of
short 2-exact sequences would have been used, had Definition 3.25 imposed one; Proposition 3.26
`P:CoherenceFree` shows it is no condition at all.

## Not formalised

Nothing from this part of the paper. `Left Square Pushout` is obtained in the paper by passing to
the opposite 2-category, and everywhere else in this development that is what happens too (see
`SnakeLean.Op`). Bipullbacks are the one deliberate exception: the fields of `IsBipullback` are
equations between 2-cells rather than propositions, so transporting the structure would cost more
than the second proof. The dual of `Right Square Pullback` is therefore written out, on top of an
`IsBipushout` structure mirroring `IsBipullback`.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.Strict B]

section Squares

variable {O : B} [HasBizero O] [IsStrong O] {K' A' Q' K A Q : B} {k' : K' ⟶ A'} {q' : A' ⟶ Q'}
  {k : K ⟶ A} {q : A ⟶ Q}

/-- **Proposition 5.7 `Mono Implies Left Pullback`.** If the right-hand vertical of a morphism of
short 2-exact sequences is a 2-monomorphism, the left-hand square is a bipullback. -/
theorem isBipullback_left_of_isTwoMono (S : MorphismSES k' q' k q) (hk' : IsTwoKernel O q' k')
    (hk : IsTwoKernel O q k) (hh : IsTwoMono S.h) : IsBipullback S.f k' k S.g S.φK := by
  haveI := hk.isTwoMono
  haveI := hk'.isTwoMono
  haveI := hh
  refine isBipullback_of_isTwoMono S.φK ?_
  intro Z a b ψ
  have h₁ : IsEssNull O (b ≫ q') := by
    refine IsEssNull.of_comp_isTwoMono S.h ((hk.isEssNull_comp.comp_left a).of_iso ?_)
    calc a ≫ k ≫ q ≅ (a ≫ k) ≫ q := (eqToIso (Category.assoc a k q)).symm
      _ ≅ (b ≫ S.g) ≫ q := Bicategory.whiskerRightIso ψ.symm q
      _ ≅ b ≫ S.g ≫ q := eqToIso (Category.assoc b S.g q)
      _ ≅ b ≫ q' ≫ S.h := Bicategory.whiskerLeftIso b S.φQ.symm
      _ ≅ (b ≫ q') ≫ S.h := (eqToIso (Category.assoc b q' S.h)).symm
  obtain ⟨u, ⟨γ₂⟩⟩ := hk'.fac b h₁
  exact ⟨u, ⟨γ₂⟩⟩

omit [Strict B] [HasBizero O] in
/-- A 2-cell into an essentially null codomain is pinned down by any invertible one: if
`α : x ⟶ n` is invertible and `n` is essentially null, then every `β : x ⟶ n` equals `α`.
Only `α` need be invertible; this is `L:UniqueNull` in the form the squares use it. -/
theorem isEssNull_hom_ext {a b : B} {x n : a ⟶ b} (hn : IsEssNull O n) (α β : x ⟶ n) [IsIso α] :
    α = β := by
  obtain ⟨m, hm, ⟨θ⟩⟩ := hn
  have h : β ≫ θ.hom = α ≫ θ.hom := hm.eq_of_isIso (α ≫ θ.hom) (β ≫ θ.hom)
  exact ((Iso.cancel_iso_hom_right β α θ).mp h).symm

/-- **Proposition 5.9 `Right Square Pullback`.** If the right-hand square of a morphism of short
2-exact sequences is a bipullback, the left-hand vertical is an equivalence.

The structure 2-cell of the 2-kernel `k` gives a square over the cospan, hence a 1-cell
`s : K ⟶ A'` with `s ≫ g ≅ k` and `s ≫ q' ≅ 0`; the latter factors `s` through `k'` as `t`, and
`t` is a quasi-inverse of `f`. The two comparison 2-cells are made compatible by Lemma 2.6
`L:UniqueNull`, as in the paper: the compatibility is an equation between invertible 2-cells
whose common codomain is essentially null, and any two such agree. -/
theorem isEquiv1_of_isBipullback_right (S : MorphismSES k' q' k q) (hk' : IsTwoKernel O q' k')
    (hk : IsTwoKernel O q k) (hbp : IsBipullback S.g q' q S.h S.φQ) : IsEquiv1 S.f := by
  haveI := hk.isTwoMono
  haveI := hk'.isTwoMono
  have hnull : IsNull O (zero1 O K Q' ≫ S.h) :=
    ⟨HasBizero.toZero K, HasBizero.fromZero Q' ≫ S.h, by simp [zero1]⟩
  obtain ⟨n, hn, ⟨ζ⟩⟩ := hk.isEssNull_comp
  obtain ⟨ψ⟩ := hnull.nonempty_iso hn
  obtain ⟨s, γ₁, γ₂, -⟩ := hbp.fac k (zero1 O K Q') (ψ ≪≫ ζ.symm)
  obtain ⟨t, ⟨σ⟩⟩ := hk'.fac s ((isEssNull_zero1 (O := O) K Q').of_iso γ₂.symm)
  -- `t ≫ f ≅ 1`, by cancelling the 2-monomorphism `k`.
  have e₁ : t ≫ S.f ≅ 𝟙 K := IsTwoMono.preimageIso k
    (calc (t ≫ S.f) ≫ k ≅ t ≫ S.f ≫ k := eqToIso (Category.assoc t S.f k)
      _ ≅ t ≫ k' ≫ S.g := Bicategory.whiskerLeftIso t S.φK.symm
      _ ≅ (t ≫ k') ≫ S.g := (eqToIso (Category.assoc t k' S.g)).symm
      _ ≅ s ≫ S.g := Bicategory.whiskerRightIso σ S.g
      _ ≅ k := γ₁
      _ ≅ 𝟙 K ≫ k := (eqToIso (Category.id_comp k)).symm)
  -- `f ≫ s ≅ k'`, by the 2-dimensional universal property of the bipullback.
  have α : (S.f ≫ s) ≫ S.g ≅ k' ≫ S.g :=
    eqToIso (Category.assoc S.f s S.g) ≪≫ Bicategory.whiskerLeftIso S.f γ₁ ≪≫ S.φK.symm
  have hβ₁ : IsEssNull O ((S.f ≫ s) ≫ q') :=
    ((((isEssNull_zero1 (O := O) K Q').of_iso γ₂.symm).comp_left S.f).of_iso
      (eqToIso (Category.assoc S.f s q')).symm)
  obtain ⟨θ₁⟩ := (isEssNull_iff _).mp hβ₁
  obtain ⟨θ₂⟩ := (isEssNull_iff _).mp hk'.isEssNull_comp
  have β : (S.f ≫ s) ≫ q' ≅ k' ≫ q' := θ₁ ≪≫ θ₂.symm
  have htarget : IsEssNull O ((k' ≫ S.g) ≫ q) :=
    (hk.isEssNull_comp.comp_left S.f).of_iso
      ((eqToIso (Category.assoc S.f k q)).symm ≪≫ Bicategory.whiskerRightIso S.φK.symm q)
  obtain ⟨hfs⟩ := hbp.nonempty_ext_iso α β (by
    simpa using isEssNull_hom_ext htarget
      ((Bicategory.whiskerRightIso β S.h ≪≫ squareIso S.φQ k').hom)
      ((squareIso S.φQ (S.f ≫ s) ≪≫ Bicategory.whiskerRightIso α q).hom))
  have e₂ : S.f ≫ t ≅ 𝟙 K' := IsTwoMono.preimageIso k'
    (calc (S.f ≫ t) ≫ k' ≅ S.f ≫ t ≫ k' := eqToIso (Category.assoc S.f t k')
      _ ≅ S.f ≫ s := Bicategory.whiskerLeftIso S.f σ
      _ ≅ k' := hfs
      _ ≅ 𝟙 K' ≫ k' := (eqToIso (Category.id_comp k')).symm)
  exact ⟨t, ⟨e₂⟩, ⟨e₁⟩⟩

/-- **Proposition 5.10 `Left Square Pushout`.** If the left-hand square of a morphism of short
2-exact sequences is a bipushout, the right-hand vertical is an equivalence.

The paper obtains this by passing to the opposite 2-category. Duality is not yet available here,
so the argument dual to `isEquiv1_of_isBipullback_right` is written out. -/
theorem isEquiv1_of_isBipushout_left (S : MorphismSES k' q' k q) (hq' : IsTwoCokernel O k' q')
    (hq : IsTwoCokernel O k q) (hbp : IsBipushout k S.g S.f k' S.φK) : IsEquiv1 S.h := by
  haveI := hq.isTwoEpi
  haveI := hq'.isTwoEpi
  have hnull : IsNull O (S.f ≫ zero1 O K Q') :=
    ⟨S.f ≫ HasBizero.toZero K, HasBizero.fromZero Q', by simp [zero1]⟩
  obtain ⟨n, hn, ⟨ζ⟩⟩ := hq'.isEssNull_comp
  obtain ⟨ψ⟩ := hn.nonempty_iso hnull
  obtain ⟨s, γ₁, γ₂, -⟩ := hbp.fac (zero1 O K Q') q' (ζ ≪≫ ψ)
  obtain ⟨t, ⟨σ⟩⟩ := hq.fac s ((isEssNull_zero1 (O := O) K Q').of_iso γ₁.symm)
  have e₁ : S.h ≫ t ≅ 𝟙 Q' := IsTwoEpi.preimageIso q'
    (calc q' ≫ S.h ≫ t ≅ (q' ≫ S.h) ≫ t := (eqToIso (Category.assoc q' S.h t)).symm
      _ ≅ (S.g ≫ q) ≫ t := Bicategory.whiskerRightIso S.φQ t
      _ ≅ S.g ≫ q ≫ t := eqToIso (Category.assoc S.g q t)
      _ ≅ S.g ≫ s := Bicategory.whiskerLeftIso S.g σ
      _ ≅ q' := γ₂
      _ ≅ q' ≫ 𝟙 Q' := (eqToIso (Category.comp_id q')).symm)
  have hα₁ : IsEssNull O (k ≫ s ≫ S.h) :=
    ((((isEssNull_zero1 (O := O) K Q').of_iso γ₁.symm).comp S.h).of_iso
      (eqToIso (Category.assoc k s S.h)))
  obtain ⟨θ₁⟩ := (isEssNull_iff _).mp hα₁
  obtain ⟨θ₂⟩ := (isEssNull_iff _).mp hq.isEssNull_comp
  have α : k ≫ s ≫ S.h ≅ k ≫ q := θ₁ ≪≫ θ₂.symm
  have β : S.g ≫ s ≫ S.h ≅ S.g ≫ q :=
    (eqToIso (Category.assoc S.g s S.h)).symm ≪≫ Bicategory.whiskerRightIso γ₂ S.h ≪≫ S.φQ
  have htarget : IsEssNull O (S.f ≫ k ≫ q) := hq.isEssNull_comp.comp_left S.f
  obtain ⟨hsh⟩ := hbp.nonempty_ext_iso α β (by
    simpa using isEssNull_hom_ext htarget
      ((Bicategory.whiskerLeftIso k' β ≪≫ cosquareIso S.φK q).hom)
      ((cosquareIso S.φK (s ≫ S.h) ≪≫ Bicategory.whiskerLeftIso S.f α).hom))
  have e₂ : t ≫ S.h ≅ 𝟙 Q := IsTwoEpi.preimageIso q
    (calc q ≫ t ≫ S.h ≅ (q ≫ t) ≫ S.h := (eqToIso (Category.assoc q t S.h)).symm
      _ ≅ s ≫ S.h := Bicategory.whiskerRightIso σ S.h
      _ ≅ q := hsh
      _ ≅ q ≫ 𝟙 Q := (eqToIso (Category.comp_id q)).symm)
  exact ⟨t, ⟨e₁⟩, ⟨e₂⟩⟩

end Squares

end SnakeLean
