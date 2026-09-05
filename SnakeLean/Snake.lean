/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.PureSnake

/-!
# The induced maps on 2-kernels and 2-cokernels, and exactness at the ends

This module formalises Proposition 6.17 `P:KerBarA`, the second assertion of Theorem 6.9
`Snake General 2D`: if `a = 2-ker(b)` and `c` is a 2-monomorphism then `ā = 2-ker(b̄)`, and
dually. That is 2-exactness of the snake sequence at `2-Ker(g)` and at `2-Cok(g)` in the special
case.

## Hypothesis form, and what it buys

Everything is stated with the 2-kernels and the induced 1-cells given as hypotheses rather than
chosen. Two reasons. First, the same house rule as in `SnakeLean.Comparison`: the construction of
the connecting 1-cell identifies these 2-kernels with 1-cells that are not the chosen ones.
Second, and specific to this module, hypothesis form is what makes the transport of
`SnakeLean.Op` usable: the chosen 2-kernel of `f.op` in `Bᵒᵖ` is not the opposite of the chosen
2-cokernel of `f` in `B`, only equivalent to it, whereas a *given* one dualises on the nose.

**Every dual in this module is obtained by transport.** `exists_cokMap` and
`snake_isTwoCokernel_barD` are three-line applications of their primal forms in `Bᵒᵖ`, the latter
through `MorphismSES.op`.

## What the chase uses

The proof is the paper's. The verification of `ā = 2-ker(b̄)` is the step where the proof of
Proposition 6.17 remarks that "here the 2-dimensionality is essential": from `c ∘ f ∘ y ≅ 0` one
concludes `f ∘ y ≅ 0` because `c` is fully faithful and therefore *reflects* null 1-cells. That is
`IsEssNull.of_comp_isTwoMono`, and it is the only genuinely 2-categorical move in the argument.

The hypotheses are those of Remark 6.18 `Rem BarA Cost`: neither 2-di-exactness, nor 2-z-exactness,
nor the Pure Snake Lemma, nor the normality of `f`, `g` and `h`; of the lower row only that `c` is
a 2-monomorphism — `c` need not be a 2-kernel and `d` plays no part at all; and `a = 2-ker(b)`,
which is the special-case hypothesis. The statement below carries no `TwoZExact O` and no
`TwoDiExact O`.

Strongness of the bizero object *is* used, and at exactly the point the remark singles out: the
reflection step is `prop2monoreflectsnull`, which the paper states for a 2-category with a strong
bizero object.

## Main results

* `exists_kerMap`, `exists_cokMap` — the 1-cell induced on 2-kernels, respectively 2-cokernels, by
  a square commuting up to an invertible 2-cell.
* `snake_isTwoKernel_barA` — Proposition 6.17 `P:KerBarA`, `ā = 2-ker(b̄)`, hence 2-exactness
  at `2-Ker(g)`.
* `snake_isTwoCokernel_barD` — its dual, hence 2-exactness at `2-Cok(g)`.

## Elsewhere

The construction of the connecting 1-cell is `SnakeLean.SnakeConnecting` and
`SnakeLean.SnakeQuotient`, 2-exactness at `2-Ker(h)` and `2-Cok(f)` is `SnakeLean.SnakeDelta`,
and the general case is `SnakeLean.SnakeGeneral`.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory Opposite

variable {B : Type u} [Bicategory.{w, v} B]

section InducedMaps

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {K K' A A' Y Y' Q Q' : B}

/-- **The 1-cell induced on 2-kernels.** A square `p ≫ v ≅ u ≫ p'` carries the 2-kernel of `p`
to the 2-kernel of `p'`.

This is how `ā` and `b̄` arise: for `ā` take the left-hand square of the ladder, for `b̄` the
right-hand one. -/
theorem exists_kerMap {u : A ⟶ A'} {p : A ⟶ Y} {p' : A' ⟶ Y'} {v : Y ⟶ Y'}
    (φ : p ≫ v ≅ u ≫ p') {k : K ⟶ A} (hk : IsTwoKernel O p k) {k' : K' ⟶ A'}
    (hk' : IsTwoKernel O p' k') : ∃ ū : K ⟶ K', Nonempty (ū ≫ k' ≅ k ≫ u) := by
  refine hk'.fac (k ≫ u) ?_
  refine ((hk.isEssNull_comp.comp v).of_iso ?_)
  exact eqToIso (Category.assoc k p v) ≪≫ Bicategory.whiskerLeftIso k φ ≪≫
    (eqToIso (Category.assoc k u p')).symm

/-- **The 1-cell induced on 2-cokernels**, the dual of `exists_kerMap`. Obtained by transport
through `Bᵒᵖ` rather than by a second proof. -/
theorem exists_cokMap {p : A ⟶ Y} {p' : A' ⟶ Y'} {w : A ⟶ A'} {u : Y ⟶ Y'}
    (φ : p ≫ u ≅ w ≫ p') {q : Y ⟶ Q} (hq : IsTwoCokernel O p q) {q' : Y' ⟶ Q'}
    (hq' : IsTwoCokernel O p' q') : ∃ ū : Q ⟶ Q', Nonempty (q ≫ ū ≅ u ≫ q') := by
  obtain ⟨ū, ⟨θ⟩⟩ := exists_kerMap (O := op O) (u := u.op) (p := p'.op) (p' := p.op) (v := w.op)
    φ.op2.symm (isTwoKernel_op hq') (isTwoKernel_op hq)
  exact ⟨ū.unop, ⟨θ.unop2⟩⟩

end InducedMaps

section EndExactness

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {A M C X Y Z : B}
  {a : A ⟶ M} {b : M ⟶ C}
  {c : X ⟶ Y} {d : Y ⟶ Z}

/-- **Proposition 6.17 `P:KerBarA`.** If `a` is a 2-kernel of `b` and `c` is a 2-monomorphism,
then the induced `ā` is a 2-kernel of the induced `b̄`. This is 2-exactness of the snake sequence
at `2-Ker(g)`, the second assertion of Theorem 6.9 `Snake General 2D`.

The hypotheses are those of Remark 6.18 `Rem BarA Cost`: no 2-di-exactness, no Pure Snake Lemma,
and of the lower row only that `c` is a 2-monomorphism — it need not be a 2-kernel, and `d` plays
no part at all. -/
theorem snake_isTwoKernel_barA (S : MorphismSES a b c d) (hab : IsSES O a b) [IsTwoMono c]
    {KF KG KH : B} {kf : KF ⟶ A} {kg : KG ⟶ M} {kh : KH ⟶ C} (hkf : IsTwoKernel O S.f kf)
    (hkg : IsTwoKernel O S.g kg) (hkh : IsTwoKernel O S.h kh) {aBar : KF ⟶ KG} {bBar : KG ⟶ KH}
    (ψa : aBar ≫ kg ≅ kf ≫ a) (ψb : bBar ≫ kh ≅ kg ≫ b) : IsTwoKernel O bBar aBar := by
  haveI := hkf.isTwoMono
  haveI := hkg.isTwoMono
  haveI := hkh.isTwoMono
  haveI := hab.isTwoKernel.isTwoMono
  haveI : IsTwoMono (kf ≫ a) := IsTwoMono.comp kf a
  refine ⟨?_, ?_, isTwoMono_of_comp ψa.symm⟩
  · -- `ā ≫ b̄` is essentially null, because `2-ker(h)` reflects nullity and `a ≫ b ≅ 0`.
    refine IsEssNull.of_comp_isTwoMono kh
      (((hab.isTwoKernel.isEssNull_comp).comp_left kf).of_iso ?_)
    exact (eqToIso (Category.assoc kf a b)).symm ≪≫ Bicategory.whiskerRightIso ψa.symm b ≪≫
      eqToIso (Category.assoc aBar kg b) ≪≫ Bicategory.whiskerLeftIso aBar ψb.symm ≪≫
      (eqToIso (Category.assoc aBar bBar kh)).symm
  · -- The chase.
    intro T t ht
    -- Whiskering with `2-ker(h)` turns `b̄ ∘ t ≅ 0` into `b ∘ 2-ker(g) ∘ t ≅ 0`.
    have h1 : IsEssNull O ((t ≫ kg) ≫ b) := by
      refine ((ht.comp kh).of_iso ?_)
      exact eqToIso (Category.assoc t bBar kh) ≪≫ Bicategory.whiskerLeftIso t ψb ≪≫
        (eqToIso (Category.assoc t kg b)).symm
    -- `a = 2-ker(b)` produces `s : T ⟶ A`.
    obtain ⟨s, ⟨γ⟩⟩ := hab.isTwoKernel.fac (t ≫ kg) h1
    -- Here the 2-dimensionality is essential: `c` reflects the nullity of `f ∘ s`.
    have h2 : IsEssNull O (s ≫ S.f) := by
      refine IsEssNull.of_comp_isTwoMono c (((hkg.isEssNull_comp.comp_left t)).of_iso ?_)
      refine (eqToIso (Category.assoc t kg S.g)).symm ≪≫ ?_
      refine Bicategory.whiskerRightIso γ.symm S.g ≪≫ ?_
      exact eqToIso (Category.assoc s a S.g) ≪≫ Bicategory.whiskerLeftIso s S.φK ≪≫
        (eqToIso (Category.assoc s S.f c)).symm
    -- so `s` factors through `2-ker(f)`.
    obtain ⟨s', ⟨δ⟩⟩ := hkf.fac s h2
    refine ⟨s', ⟨IsTwoMono.preimageIso kg ?_⟩⟩
    exact eqToIso (Category.assoc s' aBar kg) ≪≫ Bicategory.whiskerLeftIso s' ψa ≪≫
      (eqToIso (Category.assoc s' kf a)).symm ≪≫ Bicategory.whiskerRightIso δ a ≪≫ γ

/-- **The dual half of Proposition 6.17 `P:KerBarA`**: if `d` is a 2-cokernel of `c` and `b` is
a 2-epimorphism, then `d̲` is a 2-cokernel of `c̲`, which is 2-exactness at `2-Cok(g)`. Obtained
by transport through `Bᵒᵖ`. -/
theorem snake_isTwoCokernel_barD (S : MorphismSES a b c d) (hcd : IsSES O c d) [IsTwoEpi b]
    {QF QG QH : B} {qf : X ⟶ QF} {qg : Y ⟶ QG} {qh : Z ⟶ QH} (hqf : IsTwoCokernel O S.f qf)
    (hqg : IsTwoCokernel O S.g qg) (hqh : IsTwoCokernel O S.h qh) {cBar : QF ⟶ QG}
    {dBar : QG ⟶ QH} (ψc : qf ≫ cBar ≅ c ≫ qg) (ψd : qg ≫ dBar ≅ d ≫ qh) :
    IsTwoCokernel O cBar dBar := by
  haveI : IsTwoMono b.op := isTwoMono_op b
  exact isTwoKernel_op_iff.mp (snake_isTwoKernel_barA S.op (isSES_op hcd) (isTwoKernel_op hqh)
    (isTwoKernel_op hqg) (isTwoKernel_op hqf) ψd.op2 ψc.op2)

end EndExactness

end SnakeLean
