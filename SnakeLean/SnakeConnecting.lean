/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.Snake

/-!
# The top half of the snake construction

This module formalises the first half of the proof of Theorem 6.9 `Snake General 2D`, Section
6.8 `SS:Construction`: the part of Figure 1 `Fig Constructing Snake` that produces the equivalence
`z₁ : 2-Cok(b̄) ≃ 2-Ker(t)`, which is the first of the three connecting equivalences whose
composite is the connecting 1-cell `∂`; and Lemma 6.10 `L:ImageOfBBar` on the way.

## The construction

Step by step, as the paper has it.

1. `b ∘ 2-ker(g)` is a normal 2-monomorphism followed by a normal 2-epimorphism, hence
   antinormal, hence *normal* by (DI2). Factor it as `r : 2-Ker(g) ↠ I` then `i : I ↣ C`.
2. `h ∘ i ≅ 0`, because `r` is a 2-epimorphism and `h ∘ b ∘ 2-ker(g) ≅ d ∘ g ∘ 2-ker(g) ≅ 0`.
3. So `i` corestricts to `ī : I ⟶ 2-Ker(h)`, a normal 2-monomorphism by
   `Composites of Normal Monos`(ii).
4. `r ≫ ī` satisfies the defining property of `b̄`, so it *is* a normal image factorisation of
   `b̄` — Lemma 6.10 `L:ImageOfBBar`.
5. Hence `2-Cok(b̄) ≃ 2-Cok(ī)`, by `CoKernel of Composite` — the lemma's last assertion.
6. `Q := 2-Cok(i)`, and `2-coim(h) ∘ i ≅ 0` induces `t : Q ⟶ 2-Coim(h)`.
7. The Pure Snake Lemma applied to the rows `I ↣ C ↠ Q` and `2-Ker(h) ↣ C ↠ 2-Coim(h)`, whose
   middle component is the identity of `C`, gives `2-Cok(ī) ≃ 2-Ker(t)`.

## Lemma 6.10 `L:ImageOfBBar`

The proof of step 4 is the paper's: `r ≫ ī` and `b̄` both become `2-ker(g) ≫ b` after composing
with the 2-monomorphism `2-ker(h)`, so they agree up to an invertible 2-cell — and a normal
2-epimorphism followed by a normal 2-monomorphism *is* a normal image factorisation, by
Proposition 3.22 `Image Factorisation of Normal Map is Unique`. It is one line, but step 5 stands
on it, and so does the second half of Proposition 6.14 `P:Shape`, which is where the paper says
the normality of `b̄` is consumed.

## Main definitions

* `SnakeTop` — the data of steps 1 to 3, packaged.
* `snakeTop` — its construction, which is where (DI2) is used.
* `SnakeTop.t` — the 1-cell `t : Q ⟶ 2-Coim(h)` of step 6.
* `SnakeTop.comparison` — the equivalence `2-Cok(ī) ≃ 2-Ker(t)` of step 7.

## Main results

* `SnakeTop.nonempty_iso_bBar` — step 4, that `b̄ ≅ r ≫ ī`.
* `SnakeTop.isNormal_bBar` — `b̄` is normal, with `r` its 2-coimage and `ī` its 2-image. With
  the previous item this is Lemma 6.10 `L:ImageOfBBar`.
* `SnakeTop.isTwoCokernel_bBar_iff` — step 5, the lemma's last assertion.
* `snakeBot` — the bottom half of the figure, as a one-line application of `snakeTop` in `Bᵒᵖ`.

## Elsewhere

The third application of the Pure Snake Lemma needs the routine verification of Section 6.11
`SS:Connecting`: that the 2-cokernel of the normal 2-monomorphism `2-Img(f) ↣ 2-Img(g)` is
`Q = C/I`. The paper is right to route the top row of that application through the 2-cokernel
rather than through the composite `2-Img(g) ↠ Q` — the latter would need normal 2-epimorphisms
to be closed under composition, which is *not* implied by 2-di-exactness and appears as a
separate hypothesis wherever the paper needs it, most visibly as Definition 9.4 `Def:NEC`, the
second standing hypothesis of the non-self-dual Snake Lemma. The verification is
`SnakeLean.SnakeQuotient`, and the connecting 1-cell is assembled from it in
`SnakeLean.SnakeDelta`.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory Opposite

variable {B : Type u} [Bicategory.{w, v} B]

section Top

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {KG M C KH : B}

/-- **The normal image factorisation of `b ∘ 2-ker(g)`, corestricted to `2-Ker(h)`.** This is the
top-left corner of Figure 1 `Fig Constructing Snake`: the object `I`, the normal 2-epimorphism `r`,
the normal 2-monomorphism `i`, and the corestriction `ī`. -/
structure SnakeTop (O : B) [HasBizero O] {KG M C KH : B} (kg : KG ⟶ M) (b : M ⟶ C)
    (kh : KH ⟶ C) where
  /-- The 2-image of `b ∘ 2-ker(g)`. -/
  I : B
  /-- The normal 2-epimorphism onto it. -/
  r : KG ⟶ I
  /-- The normal 2-monomorphism out of it. -/
  i : I ⟶ C
  /-- `r` is a normal 2-epimorphism. -/
  isNormalEpi_r : IsNormalEpi O r
  /-- `i` is a normal 2-monomorphism. -/
  isNormalMono_i : IsNormalMono O i
  /-- The factorisation 2-cell. -/
  θ : kg ≫ b ≅ r ≫ i
  /-- The corestriction of `i` to the 2-kernel of `h`. -/
  iBar : I ⟶ KH
  /-- The 2-cell exhibiting the corestriction. -/
  θi : iBar ≫ kh ≅ i

variable {kg : KG ⟶ M} {b : M ⟶ C} {kh : KH ⟶ C}

/-- **Steps 1 to 3.** In a 2-di-exact 2-category the top-left corner of the figure exists. This
is the only place in the whole snake construction where (DI2) is used for the top half. -/
noncomputable def snakeTop {Y Z : B} {g : M ⟶ Y} {d : Y ⟶ Z} {h : C ⟶ Z} [TwoDiExact O]
    (hkg : IsTwoKernel O g kg) (hb : IsNormalEpi O b) (hkh : IsTwoKernel O h kh)
    (φQ : b ≫ h ≅ g ≫ d) : SnakeTop O kg b kh :=
  let hn : IsNormal O (kg ≫ b) :=
    isNormal_of_normalMono_comp_normalEpi ⟨_, g, hkg⟩ hb
  let H := hn.choose_spec.choose_spec.choose_spec
  let r := hn.choose_spec.choose
  let i := hn.choose_spec.choose_spec.choose
  haveI : IsTwoEpi r := H.1.isTwoEpi
  haveI : IsTwoMono kh := hkh.isTwoMono
  let θ : kg ≫ b ≅ r ≫ i := H.2.2.some
  let hih : IsEssNull O (i ≫ h) := by
    refine IsEssNull.of_comp_isTwoEpi r (((hkg.isEssNull_comp.comp d)).of_iso ?_)
    exact eqToIso (Category.assoc kg g d) ≪≫ Bicategory.whiskerLeftIso kg φQ.symm ≪≫
      (eqToIso (Category.assoc kg b h)).symm ≪≫ Bicategory.whiskerRightIso θ h ≪≫
      eqToIso (Category.assoc r i h)
  { I := hn.choose
    r := r
    i := i
    isNormalEpi_r := H.1
    isNormalMono_i := H.2.1
    θ := θ
    iBar := (hkh.fac i hih).choose
    θi := (hkh.fac i hih).choose_spec.some }

variable [IsTwoMono kh]

omit [IsStrong O] in
/-- **Step 4, Lemma 6.10 `L:ImageOfBBar`.** `r ≫ ī` satisfies the defining property of `b̄`, so
the two agree up to an invertible 2-cell; the proof is the paper's, through the 2-monomorphism
`2-ker(h)`. -/
theorem SnakeTop.nonempty_iso_bBar (T : SnakeTop O kg b kh) {bBar : KG ⟶ KH}
    (ψb : bBar ≫ kh ≅ kg ≫ b) : Nonempty (bBar ≅ T.r ≫ T.iBar) := by
  refine ⟨IsTwoMono.preimageIso kh (ψb ≪≫ T.θ ≪≫ ?_)⟩
  exact (Bicategory.whiskerLeftIso T.r T.θi).symm ≪≫ (eqToIso (Category.assoc T.r T.iBar kh)).symm

omit [IsStrong O] in
/-- **Step 4, continued — Lemma 6.10 `L:ImageOfBBar`.** `b̄` is normal, with 2-coimage `r` and
2-image `ī`. -/
theorem SnakeTop.isNormal_bBar (T : SnakeTop O kg b kh) {bBar : KG ⟶ KH}
    (ψb : bBar ≫ kh ≅ kg ≫ b) : IsNormal O bBar :=
  ⟨T.I, T.r, T.iBar, T.isNormalEpi_r,
    IsNormalMono.of_comp (g := kh) T.θi.symm T.isNormalMono_i,
    T.nonempty_iso_bBar ψb⟩

/-- **Step 5, the last assertion of Lemma 6.10.** `2-Cok(b̄) = 2-Cok(ī)`, by
`CoKernel of Composite`: `b̄ ≅ r ≫ ī` with `r` a 2-epimorphism. -/
theorem SnakeTop.isTwoCokernel_bBar_iff (T : SnakeTop O kg b kh) {W : B} {bBar : KG ⟶ KH}
    (ψb : bBar ≫ kh ≅ kg ≫ b) (q : KH ⟶ W) :
    IsTwoCokernel O bBar q ↔ IsTwoCokernel O T.iBar q := by
  haveI : IsTwoEpi T.r := T.isNormalEpi_r.isTwoEpi
  have θ := (T.nonempty_iso_bBar ψb).some
  exact ⟨fun H => (isTwoCokernel_isTwoEpi_comp_iff T.r).mp (IsTwoCokernel.of_iso θ H),
    fun H => IsTwoCokernel.of_iso θ.symm ((isTwoCokernel_isTwoEpi_comp_iff T.r).mpr H)⟩

end Top

section Comparison

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] [TwoZExact O]
  {KG M C KH Z : B} {kg : KG ⟶ M} {b : M ⟶ C} {kh : KH ⟶ C} {h : C ⟶ Z} [IsTwoMono kh]

omit [IsTwoMono kh] in
/-- **Step 6.** Since `2-coker(2-ker(h)) ∘ i ≅ 0`, the quotient `Q = C/I` receives an induced
1-cell to `2-Coim(h)`. -/
theorem SnakeTop.exists_t (T : SnakeTop O kg b kh) :
    ∃ t : twoCokernelObj O T.i ⟶ twoCokernelObj O kh,
      Nonempty (twoCokernel O T.i ≫ t ≅ twoCokernel O kh) := by
  refine (isTwoCokernel_twoCokernel O T.i).fac (twoCokernel O kh) ?_
  refine (((isTwoCokernel_twoCokernel O kh).isEssNull_comp.comp_left T.iBar)).of_iso ?_
  exact (eqToIso (Category.assoc T.iBar kh (twoCokernel O kh))).symm ≪≫
    Bicategory.whiskerRightIso T.θi (twoCokernel O kh)

/-- The 1-cell `t : Q ⟶ 2-Coim(h)` of Figure 1 `Fig Constructing Snake`. -/
noncomputable def SnakeTop.t (T : SnakeTop O kg b kh) :
    twoCokernelObj O T.i ⟶ twoCokernelObj O kh :=
  T.exists_t.choose

omit [IsTwoMono kh] in
theorem SnakeTop.nonempty_comp_t (T : SnakeTop O kg b kh) :
    Nonempty (twoCokernel O T.i ≫ T.t ≅ twoCokernel O kh) :=
  T.exists_t.choose_spec

/-- **Step 7, the first application of the Pure Snake Lemma.** Its two rows are
`I ↣ C ↠ Q` and `2-Ker(h) ↣ C ↠ 2-Coim(h)`, sharing the middle object `C` with identity middle
component; its verticals are `ī` and `t`. The resulting comparison is an equivalence
`2-Cok(ī) ≃ 2-Ker(t)`.

Composed with `SnakeTop.isTwoCokernel_bBar_iff`, this is the paper's
`z₁ : 2-Cok(b̄) ≃ 2-Cok(ī) ≃ 2-Ker(t)`. -/
noncomputable def SnakeTop.comparison (T : SnakeTop O kg b kh) (hHSD : IsHSD O)
    (hkh : IsTwoKernel O h kh) :
    PureSnakeComparison O kh (twoCokernel O T.i) (twoCokernel O T.iBar) (twoKernel O T.t) :=
  pureSnakeComparison hHSD
    (isSES_twoCokernel T.isNormalMono_i.choose_spec.choose_spec)
    (isSES_twoCokernel hkh) T.θi.symm T.nonempty_comp_t.some
    (isTwoCokernel_twoCokernel O T.iBar) (isTwoKernel_twoKernel O T.t)

end Comparison

section Bottom

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] [TwoDiExact O]
  {A M C X Y Z : B} {a : A ⟶ M} {b : M ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}

/-- **The bottom half of Figure 1 `Fig Constructing Snake`.** The paper obtains it "by the mirror
construction in the lower half" of the figure. Here that is literal: it is `snakeTop` applied to
the ladder read in `Bᵒᵖ`, where the two rows exchange places and the verticals reverse.

Read back in `B`, it factors `c ≫ 2-coker(g) : X ⟶ 2-Cok(g)` as a normal 2-epimorphism followed
by a normal 2-monomorphism `u : J ↣ 2-Cok(g)`, and corestricts along `2-coker(f)`, giving the
bottom row `2-Cok(f) ↠ J ↣ 2-Cok(g)` of the figure and the map the paper calls `s`. -/
noncomputable def snakeBot (S : MorphismSES a b c d) {QG QF : B} {qg : Y ⟶ QG} {qf : X ⟶ QF}
    (hqg : IsTwoCokernel O S.g qg) (hc : IsNormalMono O c) (hqf : IsTwoCokernel O S.f qf) :
    SnakeTop (op O) qg.op c.op qf.op :=
  snakeTop (isTwoKernel_op hqg) (isNormalEpi_op hc) (isTwoKernel_op hqf) S.φK.op2.symm

end Bottom

end SnakeLean
