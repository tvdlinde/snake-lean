/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.Normal

/-!
# Morphisms of short 2-exact sequences and the Normal Short Five Lemma

This module closes Section 3 of *A two-categorical Snake Lemma* with Theorem 3.28 `NSFL`.

## No bipullbacks

The paper's proof of Theorem 3.28 `NSFL` is a nullity chase, and Remark 3.29
`Rem NSFL Hypotheses` records that no bilimit is involved anywhere; Section 5, where bipullbacks
enter, is not imported here. `isTrivial_of_isTwoMono_ladder` is that chase — nullity reflected
five times along the ladder:

`n ≫ g ≅ 0`, so `n ≫ q' ≫ h ≅ 0` through `φQ`, so `n ≫ q' ≅ 0` as `h` reflects nullity, so `n`
factors as `m ≫ k'` through the 2-kernel `k'`; then `(m ≫ f) ≫ k ≅ n ≫ g ≅ 0` through `φK`, so
`m ≫ f ≅ 0` as `k` reflects nullity, so `m ≅ 0` as `f` does, so `n ≅ m ≫ k' ≅ 0`, so `𝟙 N ≅ 0`
as `n` reflects nullity.

Statement (2) is the mirror image, and is deduced by duality through `SnakeLean.Op`, as the
paper's "mirror halves" suggests.

## Hypotheses the chase does not use

Stated at the strength the proof actually consumes — which is Remark 3.29 `Rem NSFL Hypotheses`
— part (1) needs neither row to be a short 2-exact sequence. It needs `k'` to be a 2-kernel of
`q'`, and `k`, `f`, `h` to be 2-monomorphisms — nothing about `q` beyond its being a 1-cell, and
nothing about `q'` being a 2-cokernel. Part (2) needs the mirror halves: `q` a 2-cokernel of `k`,
and `q'`, `f`, `h` 2-epimorphisms. Nor is 2-z-exactness used anywhere: the 2-kernel or 2-cokernel
of `g` is an explicit hypothesis.

## The coherence condition

`MorphismSES` carries the two invertible square-fillers and no coherence condition, as
Definition 3.25 `Def:morphism of SES` does. `MorphismSES.coherence` is Proposition 3.26
`P:CoherenceFree`, that the condition one might expect holds regardless, for the reason recorded
in `SnakeLean.Null`: both sides are invertible 2-cells out of `k' ≫ g ≫ q` into a null 1-cell,
and there is at most one such.

## Main results

* `MorphismSES.coherence` — Proposition 3.26 `P:CoherenceFree`.
* `isTrivial_of_isTwoMono_ladder` and `isTrivial_of_isTwoEpi_ladder` — the chases.
* `nsfl_isNormalMono`, `nsfl_isNormalEpi`, `nsfl_isEquiv1` — Theorem 3.28 `NSFL`, parts (1), (2),
  (3).

## Not formalised

2-cells between morphisms of short 2-exact sequences, which nothing here consumes. The
bipullback results of Section 5 — Propositions 5.3 `Kernel vs pullback`, 5.7
`Mono Implies Left Pullback`, 5.9 `Right Square Pullback` and 5.10 `Left Square Pushout` — live
in `SnakeLean.Bipullback` and `SnakeLean.Squares`, which no module of Sections 2 to 4 imports. In
the paper, `Mono Implies Left Pullback` is cited exactly once, in the proof of Proposition 9.11
`P:NSDKappa`.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.Strict B]

/-- A **morphism of short 2-exact sequences**: a ladder between two composable pairs, with both
squares filled by invertible 2-cells.

Definition 3.25 `Def:morphism of SES` imposes no coherence condition on the two 2-cells, and
Proposition 3.26 `P:CoherenceFree` — `MorphismSES.coherence` — is why none is needed. -/
structure MorphismSES {K' A' Q' K A Q : B} (k' : K' ⟶ A') (q' : A' ⟶ Q') (k : K ⟶ A)
    (q : A ⟶ Q) where
  /-- The 1-cell between the kernel objects. -/
  f : K' ⟶ K
  /-- The 1-cell between the middle objects. -/
  g : A' ⟶ A
  /-- The 1-cell between the cokernel objects. -/
  h : Q' ⟶ Q
  /-- The invertible 2-cell filling the left-hand square. -/
  φK : k' ≫ g ≅ f ≫ k
  /-- The invertible 2-cell filling the right-hand square. -/
  φQ : q' ≫ h ≅ g ≫ q

section OppositeLadder

open Opposite Bicategory.Opposite

variable {K' A' Q' K A Q : B} {k' : K' ⟶ A'} {q' : A' ⟶ Q'} {k : K ⟶ A} {q : A ⟶ Q}

omit [Strict B]

/-- **The dual ladder.** Read in `Bᵒᵖ` a morphism of short 2-exact sequences becomes one again,
with the two rows exchanged, the verticals reversed and the two filling 2-cells transposed. Every
dual statement about ladders in this development is the primal one applied to this. -/
def MorphismSES.op (S : MorphismSES k' q' k q) : MorphismSES q.op k.op q'.op k'.op where
  f := S.h.op
  g := S.g.op
  h := S.f.op
  φK := S.φQ.op2.symm
  φQ := S.φK.op2.symm

end OppositeLadder

section Ladder

open Opposite Bicategory.Opposite

variable {O : B} [HasBizero O] [IsStrong O] {K' A' Q' K A Q N P : B}
  {k' : K' ⟶ A'} {q' : A' ⟶ Q'} {k : K ⟶ A} {q : A ⟶ Q}

omit [Strict B] in
/-- **Proposition 3.26 `P:CoherenceFree`: the coherence condition is automatic.** One might expect
Definition 3.25 `Def:morphism of SES` to require the two invertible 2-cells `q ∘ g ∘ k' ≅ 0` —
one built from `φK` and the structure 2-cell of the lower sequence, the other from `φQ` and the
structure 2-cell of the upper one — to coincide. They do regardless: both are invertible 2-cells
out of `k' ≫ g ≫ q` into a null 1-cell, and any two such agree. -/
theorem MorphismSES.coherence (S : MorphismSES k' q' k q)
    (α β : k' ≫ S.g ≫ q ≅ zero1 O K' Q) : α = β :=
  (isNull_zero1 O K' Q).iso_ext α β

/-- The kernel object of `g` is trivial, when `f` and `h` are 2-monomorphisms.

This is the substance of Theorem 3.28 `NSFL`(1). No bipullback is involved, and the hypotheses are
weaker than a morphism of short 2-exact sequences: `q` is an arbitrary 1-cell, `q'` need not be a
2-cokernel, and `k` need only be a 2-monomorphism rather than a 2-kernel. -/
theorem isTrivial_of_isTwoMono_ladder {f : K' ⟶ K} {g : A' ⟶ A} {h : Q' ⟶ Q}
    (φK : k' ≫ g ≅ f ≫ k) (φQ : q' ≫ h ≅ g ≫ q) (hk' : IsTwoKernel O q' k')
    [IsTwoMono k] [IsTwoMono f] [IsTwoMono h] {n : N ⟶ A'} (hn : IsTwoKernel O g n) :
    IsTrivial O N := by
  haveI := hn.isTwoMono
  -- `n ≫ q'` is null, since `h` reflects nullity.
  have h₁ : IsEssNull O (n ≫ q') := by
    refine IsEssNull.of_comp_isTwoMono h (hn.isEssNull_comp.comp q |>.of_iso ?_)
    exact eqToIso (Category.assoc n g q) ≪≫ Bicategory.whiskerLeftIso n φQ.symm ≪≫
      (eqToIso (Category.assoc n q' h)).symm
  -- so `n` factors through the 2-kernel `k'`.
  obtain ⟨m, ⟨γ⟩⟩ := hk'.fac n h₁
  -- `m` is null, since `k` and then `f` reflect nullity.
  have h₂ : IsEssNull O m :=
    IsEssNull.of_comp_isTwoMono f (IsEssNull.of_comp_isTwoMono k (hn.isEssNull_comp.of_iso
      (Bicategory.whiskerRightIso γ.symm g ≪≫ eqToIso (Category.assoc m k' g) ≪≫
        Bicategory.whiskerLeftIso m φK ≪≫ (eqToIso (Category.assoc m f k)).symm)))
  -- hence `n` is null, and `n` reflects nullity in turn.
  exact IsEssNull.of_comp_isTwoMono n (IsEssNull.of_iso (eqToIso (Category.id_comp n)).symm
    ((h₂.comp k').of_iso γ))

/-- The cokernel object of `g` is trivial, when `f` and `h` are 2-epimorphisms. This is the
substance of Theorem 3.28 `NSFL`(2), and uses the mirror halves of the two rows. -/
theorem isTrivial_of_isTwoEpi_ladder {f : K' ⟶ K} {g : A' ⟶ A} {h : Q' ⟶ Q}
    (φK : k' ≫ g ≅ f ≫ k) (φQ : q' ≫ h ≅ g ≫ q) (hq : IsTwoCokernel O k q)
    [IsTwoEpi q'] [IsTwoEpi f] [IsTwoEpi h] {p : A ⟶ P} (hp : IsTwoCokernel O g p) :
    IsTrivial O P :=
  haveI := isTwoMono_op q'
  haveI := isTwoMono_op f
  haveI := isTwoMono_op h
  isTrivial_of_op (isTrivial_of_isTwoMono_ladder (k := q'.op) (f := h.op) (h := f.op)
    φQ.op2.symm φK.op2.symm (isTwoKernel_op hq) (isTwoKernel_op hp))

end Ladder

section NSFL

open Opposite Bicategory.Opposite

variable {O : B} [HasBizero O] [IsStrong O] {K' A' Q' K A Q N P : B}
  {k' : K' ⟶ A'} {q' : A' ⟶ Q'} {k : K ⟶ A} {q : A ⟶ Q}

/-- **The Normal Short Five Lemma, part (1).** If `f` and `h` are 2-monomorphisms and `g` is
normal, then `g` is a normal 2-monomorphism. -/
theorem nsfl_isNormalMono (S : MorphismSES k' q' k q) (hk' : IsTwoKernel O q' k')
    (hk : IsTwoKernel O q k) (hf : IsTwoMono S.f) (hh : IsTwoMono S.h) (hg : IsNormal O S.g)
    {n : N ⟶ A'} (hn : IsTwoKernel O S.g n) : IsNormalMono O S.g := by
  haveI := hk.isTwoMono
  haveI := hf
  haveI := hh
  obtain ⟨I, e, m, he, hm, ⟨θ⟩⟩ := hg
  exact (isNormalMono_of_isTrivial θ he hm hn
    (isTrivial_of_isTwoMono_ladder S.φK S.φQ hk' hn)).2

/-- **The Normal Short Five Lemma, part (2).** If `f` and `h` are 2-epimorphisms and `g` is
normal, then `g` is a normal 2-epimorphism. -/
theorem nsfl_isNormalEpi (S : MorphismSES k' q' k q) (hq' : IsTwoCokernel O k' q')
    (hq : IsTwoCokernel O k q) (hf : IsTwoEpi S.f) (hh : IsTwoEpi S.h) (hg : IsNormal O S.g)
    {p : A ⟶ P} (hp : IsTwoCokernel O S.g p) : IsNormalEpi O S.g :=
  haveI := hf
  haveI := hh
  isNormalEpi_of_op (nsfl_isNormalMono S.op (isTwoKernel_op hq) (isTwoKernel_op hq')
    (isTwoMono_op S.h) (isTwoMono_op S.f) (isNormal_op hg) (isTwoKernel_op hp))

/-- **The Normal Short Five Lemma, part (3).** If `f` and `h` are equivalences and `g` is normal,
then `g` is an equivalence. -/
theorem nsfl_isEquiv1 (S : MorphismSES k' q' k q) (hk' : IsTwoKernel O q' k')
    (hk : IsTwoKernel O q k) (hq' : IsTwoCokernel O k' q') (hq : IsTwoCokernel O k q)
    (hf : IsEquiv1 S.f) (hh : IsEquiv1 S.h) (hg : IsNormal O S.g) {n : N ⟶ A'}
    (hn : IsTwoKernel O S.g n) {p : A ⟶ P} (hp : IsTwoCokernel O S.g p) : IsEquiv1 S.g := by
  have h₁ : IsNormalMono O S.g := nsfl_isNormalMono S hk' hk hf.isTwoMono hh.isTwoMono hg hn
  obtain ⟨W, g₀, hg₀⟩ := nsfl_isNormalEpi S hq' hq hf.isTwoEpi hh.isTwoEpi hg hp
  haveI := hg₀.isTwoEpi
  exact isEquiv1_of_isNormalMono h₁

end NSFL

end SnakeLean
