/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.SnakeQuotient

/-!
# The connecting 1-cell, and the Snake Lemma in the special case

This module completes the proof of Theorem 6.9 `Snake General 2D` in the special case
`a = 2-ker(b)`, `d = 2-cok(c)`: it assembles the connecting 1-cell `∂` of Section 6.11
`SS:Connecting` out of the three applications of the Pure Snake Lemma prepared in
`SnakeLean.SnakeConnecting` and `SnakeLean.SnakeQuotient`, and proves 2-exactness of the snake
sequence at all four inner positions, as Section 6.16 `SS:OuterExactness` does.

## The shape of `∂`, and what 2-exactness at the ends really costs

The paper sets
```
∂ = 2-ker(c̲) ∘ z ∘ 2-coker(b̄),   z = z₃ ∘ z₂⁻¹ ∘ z₁ : 2-Cok(b̄) ≃ 2-Ker(t) ≃ 2-Cok(s) ≃ 2-Ker(c̲)
```
and Proposition 6.14 `P:Shape` says what 2-exactness at the two ends costs:
`isExactAt_left_of_shape` and `isExactAt_right_of_shape` are its two halves, formal consequences
of the *shape* `∂ ≅ q ≫ z ≫ m` with `q` a 2-cokernel of `b̄`, `z` an equivalence and `m` a
2-kernel of `c̲`. Neither statement mentions the snake at all, and the proofs are the paper's.

They are not even symmetric in cost, which is the point the paragraph after the proposition
makes. 2-exactness at `2-Cok(f)` is a one-line term: `q ≫ z` is a 2-cokernel of `b̄` because a
2-cokernel followed by an equivalence is one, so `∂` already *is* a normal 2-epimorphism followed
by `2-ker(c̲)`. Nothing about `b̄` is used — not its normality, not even that `q` is its
2-cokernel rather than some other 1-cell's. 2-exactness at `2-Ker(h)` needs one thing more: that
`b̄` is normal, which is `SnakeTop.isNormal_bBar`, Lemma 6.10 `L:ImageOfBBar`, and this is where
the paper says that lemma is consumed.

## What the whole construction consumes

`exists_snakeConnecting` runs the figure in both directions and produces the shape. Its
hypotheses are the ladder, the two rows short 2-exact, normality of the three verticals, and
chosen 2-kernels and 2-cokernels. Three remarks.

* **The Pure Snake Lemma's hypothesis is free here.** Every application below is at
  `isHSD_of_twoDiExact`, so `IsHSD O` never appears as an assumption: it is implied by (DI2).
  The paper connects the two definitions in Proposition 6.3 `P:DiExactHSD`; see
  `SnakeLean.DiExact`.
* **(DI2) is used exactly twice**, once in each half of the figure, through `snakeTop`; and
  once more per half inside `SnakeQuotient.isNormalMono_imgMap`.
* **2-exactness at `2-Ker(g)` and `2-Cok(g)` uses neither (DI1) nor (DI2)** — the linter
  reports both instance arguments unused in `snake_isExactAt_twoKerG` and
  `snake_isExactAt_twoCokG`, and they are `omit`ted accordingly.

## A place where "dually" is not literal

`snake_isExactAt_twoCokG` is *not* the `Bᵒᵖ` reading of `snake_isExactAt_twoKerG`. `IsExactAt`
asks for a normal image factorisation of its **first** argument, so dualising exchanges the two
arguments as well; what `Bᵒᵖ` delivers at `2-Cok(g)` is that `d̲` is a 2-cokernel of `c̲`
followed by a 2-monomorphism, and converting that into `IsExactAt O c̲ d̲` goes through
Proposition 4.4 `Exactness Self-Dual` and needs `c̲` to be **normal**. The paper says, after the
statement of Theorem 6.9, that 2-exactness of the snake sequence asserts the normality of its six
1-cells and that for `b̄` and `c̲` this comes out of the construction; here `IsNormal O c̲` is
produced by the construction itself, as `SnakeTop.isNormal_bBar` read in `Bᵒᵖ` — the dual of
Lemma 6.10 `L:ImageOfBBar`, which is the point the paragraph closing Section 6.16 makes — and
`exists_snakeConnecting` returns it.

## Main results

* `isExactAt_left_of_shape`, `isExactAt_right_of_shape` — Proposition 6.14 `P:Shape`,
  2-exactness at `2-Ker(h)` and at `2-Cok(f)` from the shape of `∂` alone.
* `isTwoCokernel_coim`, `isTwoKernel_img` — the two halves of a normal image factorisation are
  the 2-cokernel of the 2-kernel and the 2-kernel of the 2-cokernel.
* `coim_square_of_img_square` and its dual — transposing a comparison square between two normal
  image factorisations from the 2-image side to the 2-coimage side.
* `SnakeHalf`, `snakeHalf` — half of Figure 1 `Fig Constructing Snake`, up to and including the
  first application of the Pure Snake Lemma. The other half is this one read in `Bᵒᵖ`.
* `exists_snakeConnecting` — the connecting 1-cell, in the shape the paper gives it.
* `exists_snakeConnecting_isExactAt` — 2-exactness at `2-Ker(h)` and at `2-Cok(f)`.
* `snake_isExactAt_twoKerG`, `snake_isExactAt_twoCokG` — 2-exactness at `2-Ker(g)` and at
  `2-Cok(g)` in the special case.
* `nonempty_iso_snakeComparison`, `nonempty_iso_connecting` — Remark 6.15
  `Rem Partial Choices`, that `∂` does not depend on which comparisons the three applications of
  the Pure Snake Lemma produce.

## Elsewhere

The general case is `SnakeLean.SnakeGeneral`. 2-naturality of `∂` is in `SnakeLean.Naturality`,
built on `nonempty_iso_snakeComparison` and on the notion of morphism of pure configurations
supplied there; what that module stops short of is assembling the three such morphisms out of a
single morphism of ladders.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory Opposite

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.Strict B]

section Shape

variable {O : B} [HasBizero O] [IsStrong O] {K KG KH CB KC QF QG : B}

/-- **Proposition 6.14 `P:Shape`, second half: 2-exactness of the snake sequence at
`2-Ker(h)`**, from the shape of `∂` and the normality of `b̄`. -/
theorem isExactAt_left_of_shape {bBar : KG ⟶ KH} (hbBar : IsNormal O bBar)
    {q : KH ⟶ CB} (hq : IsTwoCokernel O bBar q) {z : CB ⟶ KC} (hz : IsEquiv1 z)
    {m : KC ⟶ QF} [IsTwoMono m] {k : K ⟶ KG} (hk : IsTwoKernel O bBar k) :
    IsExactAt O bBar (q ≫ z ≫ m) := by
  obtain ⟨I, e, n, he, hn, ⟨θ⟩⟩ := hbBar
  haveI := he.isTwoEpi
  haveI := hz.isTwoMono
  haveI : IsTwoMono (z ≫ m) := IsTwoMono.comp z m
  obtain ⟨Z, ℓ, hℓ⟩ := hn
  have hqn : IsTwoCokernel O n q := (isTwoCokernel_isTwoEpi_comp_iff e).mp (hq.of_iso θ)
  refine (isExactAt_iff θ he ⟨Z, ℓ, hℓ⟩ hk).mpr ?_
  exact (isTwoKernel_comp_isTwoMono_iff (z ≫ m)).mpr (hℓ.of_isTwoCokernel hqn)

/-- **Proposition 6.14 `P:Shape`, first half: 2-exactness of the snake sequence at `2-Cok(f)`**,
from the shape of `∂` alone. -/
theorem isExactAt_right_of_shape {bBar : KG ⟶ KH} {q : KH ⟶ CB}
    (hq : IsTwoCokernel O bBar q) {z : CB ⟶ KC} (hz : IsEquiv1 z) {cBar : QF ⟶ QG}
    {m : KC ⟶ QF} (hm : IsTwoKernel O cBar m) : IsExactAt O (q ≫ z ≫ m) cBar :=
  ⟨KC, q ≫ z, m, ⟨KG, bBar, hq.comp_isEquiv1 hz⟩,
    ⟨eqToIso (Category.assoc q z m).symm⟩, hm⟩

end Shape

section Factorisation

variable {O : B} [HasBizero O] [IsStrong O] {K Q A A' I : B}

/-- The 2-coimage half of a normal image factorisation **is** the 2-cokernel of the 2-kernel. -/
theorem isTwoCokernel_coim {f : A ⟶ A'} {e : A ⟶ I} {m : I ⟶ A'} [IsTwoMono m] (θ : f ≅ e ≫ m)
    (he : IsNormalEpi O e) {k : K ⟶ A} (hk : IsTwoKernel O f k) : IsTwoCokernel O k e := by
  obtain ⟨W, p, hp⟩ := he
  exact hp.of_isTwoKernel ((isTwoKernel_comp_isTwoMono_iff m).mp (hk.of_iso θ))

/-- The 2-image half of a normal image factorisation **is** the 2-kernel of the 2-cokernel. -/
theorem isTwoKernel_img {f : A ⟶ A'} {e : A ⟶ I} {m : I ⟶ A'} [IsTwoEpi e] (θ : f ≅ e ≫ m)
    (hm : IsNormalMono O m) {q : A' ⟶ Q} (hq : IsTwoCokernel O f q) : IsTwoKernel O q m := by
  haveI : IsTwoMono e.op := isTwoMono_op e
  exact isTwoKernel_of_op (isTwoCokernel_coim (m := e.op) θ.op2 (isNormalEpi_op hm)
    (isTwoKernel_op hq))

end Factorisation

section Transpose

variable {A M X Y Z C IF IG IH : B}

/-- **Transposing a comparison square.** -/
noncomputable def coim_square_of_img_square {a : A ⟶ M} {f : A ⟶ X} {c : X ⟶ Y} {g : M ⟶ Y}
    {ef : A ⟶ IF} {mf : IF ⟶ X} {eg : M ⟶ IG} {mg : IG ⟶ Y} [IsTwoMono mg]
    (θf : f ≅ ef ≫ mf) (θg : g ≅ eg ≫ mg) (φ : a ≫ g ≅ f ≫ c) {j : IF ⟶ IG}
    (ψ : j ≫ mg ≅ mf ≫ c) : ef ≫ j ≅ a ≫ eg :=
  IsTwoMono.preimageIso mg <| calc
    (ef ≫ j) ≫ mg ≅ ef ≫ j ≫ mg := eqToIso (Category.assoc ef j mg)
    _ ≅ ef ≫ mf ≫ c := Bicategory.whiskerLeftIso ef ψ
    _ ≅ (ef ≫ mf) ≫ c := (eqToIso (Category.assoc ef mf c)).symm
    _ ≅ f ≫ c := Bicategory.whiskerRightIso θf.symm c
    _ ≅ a ≫ g := φ.symm
    _ ≅ a ≫ eg ≫ mg := Bicategory.whiskerLeftIso a θg
    _ ≅ (a ≫ eg) ≫ mg := (eqToIso (Category.assoc a eg mg)).symm

/-- The dual, read in `Bᵒᵖ`. -/
noncomputable def img_square_of_coim_square {b : M ⟶ C} {g : M ⟶ Y} {d : Y ⟶ Z} {h : C ⟶ Z}
    {eg : M ⟶ IG} {mg : IG ⟶ Y} {eh : C ⟶ IH} {mh : IH ⟶ Z} [IsTwoEpi eg]
    (θg : g ≅ eg ≫ mg) (θh : h ≅ eh ≫ mh) (φ : b ≫ h ≅ g ≫ d) {dBar : IG ⟶ IH}
    (ψ : eg ≫ dBar ≅ b ≫ eh) : dBar ≫ mh ≅ mg ≫ d := by
  haveI : IsTwoMono eg.op := isTwoMono_op eg
  exact (coim_square_of_img_square (ef := mh.op) (mg := eg.op) (j := dBar.op) θh.op2 θg.op2
    φ.symm.op2 ψ.op2).unop2

end Transpose

section Half

variable {O : B} [HasBizero O] [IsStrong O] {KG M C KH IG IH Y Z : B}
  {kg : KG ⟶ M} {b : M ⟶ C} {kh : KH ⟶ C} {eg : M ⟶ IG} {eh : C ⟶ IH} {bBar : KG ⟶ KH}

/-- **Step 6 at an arbitrary 2-cokernel.** -/
theorem SnakeTop.exists_t' (T : SnakeTop O kg b kh) {Q : B} {qi : C ⟶ Q}
    (hqi : IsTwoCokernel O T.i qi) (heh : IsTwoCokernel O kh eh) :
    ∃ t : Q ⟶ IH, Nonempty (qi ≫ t ≅ eh) := by
  refine hqi.fac eh ?_
  refine (heh.isEssNull_comp.comp_left T.iBar).of_iso ?_
  exact (eqToIso (Category.assoc T.iBar kh eh)).symm ≪≫ Bicategory.whiskerRightIso T.θi eh

/-- **Half of Figure 1 `Fig Constructing Snake`.** -/
structure SnakeHalf (O : B) [HasBizero O] {KG M C KH IG IH : B} (kg : KG ⟶ M) (b : M ⟶ C)
    (kh : KH ⟶ C) (eg : M ⟶ IG) (eh : C ⟶ IH) (bBar : KG ⟶ KH) where
  /-- The 2-image of `b ∘ 2-ker(g)`. -/
  I : B
  /-- The quotient `Q = C/I`. -/
  Q : B
  /-- The 2-cokernel object of `b̄`. -/
  CB : B
  /-- The 2-kernel object of `t`. -/
  KT : B
  /-- The normal 2-epimorphism onto the 2-image. -/
  r : KG ⟶ I
  /-- The normal 2-monomorphism out of it. -/
  i : I ⟶ C
  /-- Its corestriction along `2-ker(h)`, the 2-image of `b̄`. -/
  iBar : I ⟶ KH
  /-- `r` is a 2-epimorphism. -/
  isTwoEpi_r : IsTwoEpi r
  /-- The factorisation 2-cell. -/
  θ : kg ≫ b ≅ r ≫ i
  /-- The corestriction 2-cell. -/
  θi : iBar ≫ kh ≅ i
  /-- The 2-cokernel of `i`. -/
  qi : C ⟶ Q
  /-- and its universal property. -/
  hqi : IsTwoCokernel O i qi
  /-- The induced `t : Q ⟶ 2-Img(h)`. -/
  t : Q ⟶ IH
  /-- and its defining 2-cell. -/
  θt : qi ≫ t ≅ eh
  /-- A 2-cokernel of `b̄`. -/
  q : KH ⟶ CB
  /-- and its universal property. -/
  hq : IsTwoCokernel O bBar q
  /-- A 2-kernel of `t`. -/
  mt : KT ⟶ Q
  /-- and its universal property. -/
  hmt : IsTwoKernel O t mt
  /-- The first Pure Snake comparison. -/
  z : CB ⟶ KT
  /-- It is an equivalence. -/
  hz : IsEquiv1 z
  /-- Its characterising 2-cell. -/
  θz : q ≫ z ≫ mt ≅ kh ≫ qi
  /-- The comparison `2-Img(g) ↠ Q`. -/
  π : IG ⟶ Q
  /-- and its defining 2-cell. -/
  ψπ : eg ≫ π ≅ b ≫ qi
  /-- The comparison `2-Img(g) ↠ 2-Img(h)`. -/
  dBar : IG ⟶ IH
  /-- and its defining 2-cell. -/
  ψd : eg ≫ dBar ≅ b ≫ eh
  /-- `b̄` is normal, with 2-coimage `r` and 2-image `ī`. -/
  isNormal_bBar : IsNormal O bBar

/-- **The construction of half the figure**, up to and including the first application of the
Pure Snake Lemma. -/
noncomputable def snakeHalf [TwoDiExact O] [TwoZExact O] {g : M ⟶ Y} {d : Y ⟶ Z} {h : C ⟶ Z}
    (hkg : IsTwoKernel O g kg) (hb : IsNormalEpi O b)
    (hkh : IsTwoKernel O h kh) (φQ : b ≫ h ≅ g ≫ d) (heg : IsTwoCokernel O kg eg)
    (heh : IsTwoCokernel O kh eh) (ψb : bBar ≫ kh ≅ kg ≫ b) :
    SnakeHalf O kg b kh eg eh bBar :=
  haveI : IsTwoMono kh := hkh.isTwoMono
  let T := snakeTop hkg hb hkh φQ
  haveI : IsTwoEpi T.r := T.isNormalEpi_r.isTwoEpi
  let qi := twoCokernel O T.i
  have hqi : IsTwoCokernel O T.i qi := isTwoCokernel_twoCokernel O T.i
  let Ht := T.exists_t' hqi heh
  have hq : IsTwoCokernel O bBar (twoCokernel O T.iBar) :=
    (T.isTwoCokernel_bBar_iff ψb _).mpr (isTwoCokernel_twoCokernel O T.iBar)
  let P := pureSnakeComparison isHSD_of_twoDiExact
    (isSES_twoCokernel T.isNormalMono_i.choose_spec.choose_spec)
    (isSES_of_isTwoKernel hkh heh) T.θi.symm Ht.choose_spec.some
    (isTwoCokernel_twoCokernel O T.iBar) (isTwoKernel_twoKernel O Ht.choose)
  have hie : IsEssNull O (T.i ≫ eh) :=
    (heh.isEssNull_comp.comp_left T.iBar).of_iso
      ((eqToIso (Category.assoc T.iBar kh eh)).symm ≪≫ Bicategory.whiskerRightIso T.θi eh)
  let Hπ := heg.fac (b ≫ qi)
    ((hqi.isEssNull_comp.comp_left T.r).of_iso
      ((eqToIso (Category.assoc T.r T.i qi)).symm ≪≫
        (Bicategory.whiskerRightIso T.θ qi).symm ≪≫ eqToIso (Category.assoc kg b qi)))
  let Hd := heg.fac (b ≫ eh)
    ((hie.comp_left T.r).of_iso
      ((eqToIso (Category.assoc T.r T.i eh)).symm ≪≫
        (Bicategory.whiskerRightIso T.θ eh).symm ≪≫ eqToIso (Category.assoc kg b eh)))
  { I := T.I
    Q := twoCokernelObj O T.i
    CB := twoCokernelObj O T.iBar
    KT := twoKernelObj O Ht.choose
    r := T.r
    i := T.i
    iBar := T.iBar
    isTwoEpi_r := T.isNormalEpi_r.isTwoEpi
    θ := T.θ
    θi := T.θi
    qi := qi
    hqi := hqi
    t := Ht.choose
    θt := Ht.choose_spec.some
    q := twoCokernel O T.iBar
    hq := hq
    mt := twoKernel O Ht.choose
    hmt := isTwoKernel_twoKernel O Ht.choose
    z := P.j
    hz := P.isEquiv1
    θz := P.θ
    π := Hπ.choose
    ψπ := Hπ.choose_spec.some
    dBar := Hd.choose
    ψd := Hd.choose_spec.some
    isNormal_bBar := T.isNormal_bBar ψb }

end Half

section Assembly

variable {O : B} [HasBizero O] [IsStrong O] [TwoDiExact O] [TwoZExact O]
  {A M C X Y Z KG KH QF QG : B} {a : A ⟶ M} {b : M ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}

/-- **The connecting 1-cell, in the shape `(Def Partial)` gives it.** -/
theorem exists_snakeConnecting (S : MorphismSES a b c d)
    (hab : IsSES O a b) (hcd : IsSES O c d)
    (hf : IsNormal O S.f) (hg : IsNormal O S.g) (hh : IsNormal O S.h)
    {kg : KG ⟶ M} (hkg : IsTwoKernel O S.g kg) {kh : KH ⟶ C} (hkh : IsTwoKernel O S.h kh)
    {qf : X ⟶ QF} (hqf : IsTwoCokernel O S.f qf) {qg : Y ⟶ QG} (hqg : IsTwoCokernel O S.g qg)
    {bBar : KG ⟶ KH} (ψb : bBar ≫ kh ≅ kg ≫ b)
    {cBar : QF ⟶ QG} (ψc : qf ≫ cBar ≅ c ≫ qg) :
    ∃ (CB KC : B) (q : KH ⟶ CB) (z : CB ⟶ KC) (m : KC ⟶ QF),
      IsNormal O bBar ∧ IsNormal O cBar ∧ IsTwoCokernel O bBar q ∧ IsEquiv1 z ∧
        IsTwoKernel O cBar m := by
  obtain ⟨IF, ef, mf, hef, hmf, ⟨θf⟩⟩ := hf
  obtain ⟨IG, eg, mg, heg₀, hmg₀, ⟨θg⟩⟩ := hg
  obtain ⟨IH, eh, mh, heh₀, hmh₀, ⟨θh⟩⟩ := hh
  haveI := hef.isTwoEpi
  haveI := hmf.isTwoMono
  haveI := heg₀.isTwoEpi
  haveI := hmg₀.isTwoMono
  haveI := heh₀.isTwoEpi
  haveI := hmh₀.isTwoMono
  haveI : IsTwoMono c := hcd.isTwoKernel.isTwoMono
  haveI : IsTwoEpi b := hab.isTwoCokernel.isTwoEpi
  have heg : IsTwoCokernel O kg eg := isTwoCokernel_coim θg heg₀ hkg
  have hmg : IsTwoKernel O qg mg := isTwoKernel_img θg hmg₀ hqg
  have heh : IsTwoCokernel O kh eh := isTwoCokernel_coim θh heh₀ hkh
  have hmf' : IsTwoKernel O qf mf := isTwoKernel_img θf hmf hqf
  have hb : IsNormalEpi O b := ⟨A, a, hab.isTwoCokernel⟩
  have hc : IsNormalMono O c := ⟨Z, d, hcd.isTwoKernel⟩
  -- The two halves of Figure 1 `Fig Constructing Snake`, the second in `Bᵒᵖ`.
  have Th := snakeHalf hkg hb hkh S.φQ heg heh ψb
  have Bh := snakeHalf (O := op O) (isTwoKernel_op hqg) (isNormalEpi_op hc)
    (isTwoKernel_op hqf) S.φK.op2.symm (isTwoCokernel_op hmg) (isTwoCokernel_op hmf') ψc.op2
  haveI := Th.isTwoEpi_r
  haveI : IsTwoMono Bh.r.unop := isTwoMono_of_isTwoEpi_op Bh.isTwoEpi_r
  haveI : IsTwoEpi Th.dBar := isTwoEpi_of_comp Th.ψd.symm
  -- The comparison `j : 2-Img(f) ⟶ 2-Img(g)` and the two squares that determine it.
  have ψjImg : Bh.dBar.unop ≫ mg ≅ mf ≫ c := Bh.ψd.unop2
  haveI : IsTwoMono Bh.dBar.unop := isTwoMono_imgMap ψjImg
  have ψj : ef ≫ Bh.dBar.unop ≅ a ≫ eg :=
    coim_square_of_img_square θf θg S.φK ψjImg
  -- The top row of the third pure configuration.
  have htop : IsSES O Bh.dBar.unop Th.π :=
    isSES_imgRow hab Th.θ Th.hqi heg ψj Th.ψπ
  -- The bottom row, from `SnakeQuotient`.
  have ψdImg : Th.dBar ≫ mh ≅ mg ≫ d := img_square_of_coim_square θg θh S.φQ Th.ψd
  have hκ : IsTwoKernel O Bh.i.unop Bh.qi.unop := isTwoKernel_of_op Bh.hqi
  have hbot : IsSES O Bh.π.unop Th.dBar :=
    isSES_imgRowDual hcd Bh.θ.unop2 hκ hmg ψdImg Bh.ψπ.unop2
  -- The two verticals of the third configuration.
  have θsκ : Bh.t.unop ≫ Bh.qi.unop ≅ mf := Bh.θt.unop2
  have θs : Bh.dBar.unop ≅ Bh.t.unop ≫ Bh.π.unop := IsTwoMono.preimageIso mg <| calc
    Bh.dBar.unop ≫ mg ≅ mf ≫ c := ψjImg
    _ ≅ (Bh.t.unop ≫ Bh.qi.unop) ≫ c := Bicategory.whiskerRightIso θsκ.symm c
    _ ≅ Bh.t.unop ≫ Bh.qi.unop ≫ c := eqToIso (Category.assoc _ _ _)
    _ ≅ Bh.t.unop ≫ Bh.π.unop ≫ mg := Bicategory.whiskerLeftIso _ Bh.ψπ.unop2.symm
    _ ≅ (Bh.t.unop ≫ Bh.π.unop) ≫ mg := (eqToIso (Category.assoc _ _ _)).symm
  have θt3 : Th.π ≫ Th.t ≅ Th.dBar := IsTwoEpi.preimageIso eg <| calc
    eg ≫ Th.π ≫ Th.t ≅ (eg ≫ Th.π) ≫ Th.t := (eqToIso (Category.assoc _ _ _)).symm
    _ ≅ (b ≫ Th.qi) ≫ Th.t := Bicategory.whiskerRightIso Th.ψπ Th.t
    _ ≅ b ≫ Th.qi ≫ Th.t := eqToIso (Category.assoc _ _ _)
    _ ≅ b ≫ eh := Bicategory.whiskerLeftIso b Th.θt
    _ ≅ eg ≫ Th.dBar := Th.ψd.symm
  have hes : IsTwoCokernel O Bh.t.unop Bh.mt.unop := isTwoCokernel_of_op Bh.hmt
  -- The third application of the Pure Snake Lemma.
  have P := pureSnakeComparison isHSD_of_twoDiExact htop hbot θs θt3 hes Th.hmt
  refine ⟨Th.CB, Bh.CB.unop, Th.q, Th.z ≫ P.isEquiv1.inv ≫ Bh.z.unop, Bh.q.unop,
    Th.isNormal_bBar, isNormal_of_op Bh.isNormal_bBar, Th.hq,
    Th.hz.comp (P.isEquiv1.isEquiv1_inv.comp (isEquiv1_of_op Bh.hz)), isTwoKernel_of_op Bh.hq⟩

/-- **The Snake Lemma, special case: 2-exactness at `2-Ker(h)` and at `2-Cok(f)`.** -/
theorem exists_snakeConnecting_isExactAt (S : MorphismSES a b c d)
    (hab : IsSES O a b) (hcd : IsSES O c d)
    (hf : IsNormal O S.f) (hg : IsNormal O S.g) (hh : IsNormal O S.h)
    {kg : KG ⟶ M} (hkg : IsTwoKernel O S.g kg) {kh : KH ⟶ C} (hkh : IsTwoKernel O S.h kh)
    {qf : X ⟶ QF} (hqf : IsTwoCokernel O S.f qf) {qg : Y ⟶ QG} (hqg : IsTwoCokernel O S.g qg)
    {bBar : KG ⟶ KH} (ψb : bBar ≫ kh ≅ kg ≫ b)
    {cBar : QF ⟶ QG} (ψc : qf ≫ cBar ≅ c ≫ qg) :
    ∃ δ : KH ⟶ QF, IsExactAt O bBar δ ∧ IsExactAt O δ cBar := by
  obtain ⟨CB, KC, q, z, m, hn, -, hq, hz, hm⟩ :=
    exists_snakeConnecting S hab hcd hf hg hh hkg hkh hqf hqg ψb ψc
  haveI := hm.isTwoMono
  exact ⟨q ≫ z ≫ m, isExactAt_left_of_shape hn hq hz (isTwoKernel_twoKernel O bBar),
    isExactAt_right_of_shape hq hz hm⟩

omit [TwoDiExact O] [TwoZExact O] in
/-- **Special case, 2-exactness at `2-Ker(g)`.** When `a` is a 2-kernel of `b` the comparison
`ā` *is* the 2-kernel of `b̄`, so it is its own normal image factorisation. -/
theorem snake_isExactAt_twoKerG (S : MorphismSES a b c d) (hab : IsSES O a b) [IsTwoMono c]
    {KF : B} {kf : KF ⟶ A} {kg : KG ⟶ M} {kh : KH ⟶ C} (hkf : IsTwoKernel O S.f kf)
    (hkg : IsTwoKernel O S.g kg) (hkh : IsTwoKernel O S.h kh) {aBar : KF ⟶ KG}
    {bBar : KG ⟶ KH} (ψa : aBar ≫ kg ≅ kf ≫ a) (ψb : bBar ≫ kh ≅ kg ≫ b) :
    IsExactAt O aBar bBar :=
  ⟨KF, 𝟙 KF, aBar, (isEquiv1_id KF).isNormalEpi, ⟨eqToIso (Category.id_comp aBar).symm⟩,
    snake_isTwoKernel_barA S hab hkf hkg hkh ψa ψb⟩

omit [TwoDiExact O] [TwoZExact O] in
/-- **Special case, 2-exactness at `2-Cok(g)`.** Here the dual of `snake_isExactAt_twoKerG` is not
literally the statement wanted: `IsExactAt` asks for a factorisation of its *first* argument, so
the passage from `d̲ = 2-cok(c̲)` to `IsExactAt O c̲ d̲` goes through `isExactAt_of_op`, and needs
`c̲` to be normal — which `exists_snakeConnecting` supplies. -/
theorem snake_isExactAt_twoCokG (S : MorphismSES a b c d) (hcd : IsSES O c d) [IsTwoEpi b]
    {QH : B} {cBar : QF ⟶ QG} {dBar : QG ⟶ QH} (hcBar : IsNormal O cBar)
    {qf : X ⟶ QF} {qg : Y ⟶ QG} {qh : Z ⟶ QH} (hqf : IsTwoCokernel O S.f qf)
    (hqg : IsTwoCokernel O S.g qg) (hqh : IsTwoCokernel O S.h qh)
    (ψc : qf ≫ cBar ≅ c ≫ qg) (ψd : qg ≫ dBar ≅ d ≫ qh) : IsExactAt O cBar dBar := by
  have h := snake_isTwoCokernel_barD S hcd hqf hqg hqh ψc ψd
  exact isExactAt_of_op ⟨Opposite.op QH, 𝟙 _, dBar.op, (isEquiv1_id _).isNormalEpi,
    ⟨(eqToIso (Category.id_comp dBar.op)).symm⟩, isTwoKernel_op h⟩ hcBar

end Assembly

section Uniqueness

variable {O : B} [HasBizero O] {KH CB KT KS KC QF C₁ C₂ C₃ X₁ X₂ X₃ Y₁ Y₂ Y₃ : B}
  {c₁ : X₁ ⟶ Y₁} {b₁ : Y₁ ⟶ C₁} {e₁ : X₁ ⟶ CB} {m₁ : KT ⟶ C₁}
  {c₃ : X₃ ⟶ Y₃} {b₃ : Y₃ ⟶ C₃} {e₃ : X₃ ⟶ KS} {m₃ : KT ⟶ C₃}
  {c₂ : X₂ ⟶ Y₂} {b₂ : Y₂ ⟶ C₂} {e₂ : X₂ ⟶ KS} {m₂ : KC ⟶ C₂}

omit [Strict B]

/-- **Remark 6.15 `Rem Partial Choices`: the three comparisons determine the middle equivalence
of `∂` up to an invertible 2-cell.** -/
theorem nonempty_iso_snakeComparison [IsTwoEpi e₁] [IsTwoMono m₁] [IsTwoEpi e₃] [IsTwoMono m₃]
    [IsTwoEpi e₂] [IsTwoMono m₂] (P₁ P₁' : PureSnakeComparison O c₁ b₁ e₁ m₁)
    (P₃ P₃' : PureSnakeComparison O c₃ b₃ e₃ m₃) (P₂ P₂' : PureSnakeComparison O c₂ b₂ e₂ m₂) :
    Nonempty (P₁.j ≫ P₃.isEquiv1.inv ≫ P₂.j ≅ P₁'.j ≫ P₃'.isEquiv1.inv ≫ P₂'.j) := by
  obtain ⟨θ₁⟩ := P₁.nonempty_iso P₁'
  obtain ⟨θ₂⟩ := P₂.nonempty_iso P₂'
  obtain ⟨θ₃⟩ := P₃.isEquiv1.nonempty_iso_inv P₃'.isEquiv1 (P₃.nonempty_iso P₃').some
  exact ⟨Bicategory.whiskerRightIso θ₁ _ ≪≫ Bicategory.whiskerLeftIso P₁'.j
    (Bicategory.whiskerRightIso θ₃ P₂.j ≪≫ Bicategory.whiskerLeftIso P₃'.isEquiv1.inv θ₂)⟩

/-- **`∂` is essentially unique.** -/
theorem nonempty_iso_connecting {q : KH ⟶ CB} {z z' : CB ⟶ KC} {m : KC ⟶ QF} (θ : z ≅ z') :
    Nonempty (q ≫ z ≫ m ≅ q ≫ z' ≫ m) :=
  ⟨Bicategory.whiskerLeftIso q (Bicategory.whiskerRightIso θ m)⟩

end Uniqueness

end SnakeLean
