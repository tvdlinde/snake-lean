/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.SnakeDelta

/-!
# The Snake Lemma, general case

Theorem 6.9 `Snake General 2D` is stated for rows that are merely 2-exact, and is proved by
reducing the general case to the special one along Figure 2 `Fig Snake General`, in Section 6.19
`SS:GeneralCase`. This module is that reduction: Lemma 6.20 `L:Restriction`, Proposition 6.21
`P:KerComparison`, and the assembly the paragraph after the proposition describes.

## The reduction

Factor `a ≅ 2-coim(a) ≫ a'` and `d ≅ d' ≫ 2-img(d)`. 2-exactness of the rows makes `a'` a
2-kernel of `b` and `d'` a 2-cokernel of `c`, so the middle ladder
```
2-Coim(a) ↣ M ↠ C          X ↣ Y ↠ 2-Img(d)
```
satisfies the hypotheses of the special case. What has to be produced is the restriction
`f' : 2-Coim(a) ⟶ X` of `f`, the corestriction `h' : C ⟶ 2-Img(d)` of `h`, their normality, and
the two comparisons `ā'' : 2-Ker(f) ⟶ 2-Ker(f')` and `d̲'' : 2-Cok(h') ⟶ 2-Cok(h)`.

## Where the 2-dimensionality enters

`isEssNull_comp_left_of_square` is the only genuinely 2-categorical step, and it is used three
times, as Remark 6.22 `Rem General Cost` counts: a 1-cell killed by `a` is killed by `f`, because
`c` is a 2-monomorphism and therefore *reflects* null 1-cells. It produces `f'`, it produces the
comparison `2-Ker(2-coim(a)) ⟶ 2-Ker(f)`, and — dually — it produces `h'`.

## The two identifications, and the fourth Pure Snake

* **`2-Cok(f') ≃ 2-Cok(f)` and `2-Ker(h') ≃ 2-Ker(h)`.** The paper obtains both from Proposition
  3.9 `CoKernel of Composite` "in the form in which neither factor is required to be normal".
  That form is `isTwoCokernel_isTwoEpi_comp_iff`, stated for an arbitrary 2-epimorphism, and
  `isTwoKernel_comp_isTwoMono_iff`, for an arbitrary 2-monomorphism.
* **`ā''` is a normal 2-epimorphism.** Proposition 6.21 `P:KerComparison` proves it by a
  **fourth application of the Pure Snake Lemma**, to the two rows
  ```
  2-Ker(2-coim(a)) ↣ A ↠ 2-Coim(a)          2-Ker(f) ↣ A ↠ 2-Coim(f)
  ```
  through the shared middle object `A`, and `isNormalEpi_kerComparison` is that proof. Its
  comparison equivalence `2-Cok(v) ≃ 2-Ker(f')` is characterised by exactly the triangle that
  characterises `ā''`, so `ā''` is a 2-cokernel followed by an equivalence. As Remark 6.22 says,
  this needs no (DI2) beyond homological self-duality, no image identification, and no
  2-z-exactness — only a 2-cokernel of the comparison `v : 2-Ker(2-coim(a)) ⟶ 2-Ker(f)`.

## Main results

* `isEssNull_comp_left_of_square` — the reflection step.
* `exists_restriction` — Lemma 6.20 `L:Restriction`: `f` restricts along `2-coim(a)`, and the
  restriction is normal.
* `exists_kerRestriction` — the comparison on 2-kernels that the fourth pure configuration needs.
* `isNormalEpi_kerComparison` — Proposition 6.21 `P:KerComparison`: `ā''` is a normal
  2-epimorphism.
* `exists_snakeGeneral` — the Snake Lemma: a connecting 1-cell exists, the snake sequence is
  2-exact at `2-Ker(g)`, `2-Ker(h)`, `2-Cok(f)` and `2-Cok(g)`, and `d̲` is normal. The last
  conjunct is there because Definition 4.5 `Def:ExactSequence` requires every 1-cell of an exact
  sequence to be normal: `IsExactAt` supplies that for its *first* argument, so the four exactness
  statements cover `ā`, `b̄`, `∂` and `c̲`, and the sixth 1-cell has to be stated separately. It
  costs nothing — the reduction exhibits `d̲` as a 2-cokernel of `c̲` followed by a normal
  2-monomorphism — and it is what makes the dual half of Theorem 9.19 `T:SnakeNonSelfDual` a
  transport (`SnakeLean.NSDConnecting`).

## Elsewhere

The classical Snake Lemma, Corollary 6.24 `Snake General`, is deduced from `exists_snakeGeneral`
in `SnakeLean.Classical`. The Normal Short Five Lemma, which the theorem contains as the case in
which the outer 2-kernels and 2-cokernels are trivial, is proved directly in
`SnakeLean.FiveLemma`, at strictly weaker hypotheses — it needs neither 2-di-exactness nor
2-z-exactness — and is not re-derived from here.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory Opposite

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.Strict B]

section Reduction

variable {O : B} [HasBizero O] [IsStrong O] {A M X Y W KA KF CoimA IF : B}
  {a : A ⟶ M} {f : A ⟶ X} {c : X ⟶ Y} {g : M ⟶ Y} {ea : A ⟶ CoimA} {ma : CoimA ⟶ M}

/-- **The left-hand square reflects nullity.** A 1-cell killed by `a` is killed by `f`, because
`c` is a 2-monomorphism. This is the one step of the reduction where the 2-dimensionality is
essential, and it is used three times — the count of Remark 6.22 `Rem General Cost`. -/
theorem isEssNull_comp_left_of_square [IsTwoMono c] (φ : a ≫ g ≅ f ≫ c) {p : W ⟶ A}
    (hp : IsEssNull O (p ≫ a)) : IsEssNull O (p ≫ f) :=
  IsEssNull.of_comp_isTwoMono c ((hp.comp g).of_iso (eqToIso (Category.assoc p a g) ≪≫
    Bicategory.whiskerLeftIso p φ ≪≫ (eqToIso (Category.assoc p f c)).symm))

/-- **Lemma 6.20 `L:Restriction`.** `f` restricts along the 2-coimage of `a`, and the
restriction `w ≫ 2-img(f)` is normal — the paper's `f'`, with the paper's `w`. The proof is the
paper's: `w` is a normal 2-epimorphism because `w ∘ e` is one and `e` is a 2-epimorphism, the
dual of part (ii) of Proposition 3.6 `Composites of Normal Monos`. -/
theorem exists_restriction [IsTwoMono c] (φ : a ≫ g ≅ f ≫ c) (θa : a ≅ ea ≫ ma)
    (hea : IsNormalEpi O ea) {ef : A ⟶ IF} {mf : IF ⟶ X} [IsTwoMono mf] (θf : f ≅ ef ≫ mf)
    (hef : IsNormalEpi O ef) :
    ∃ w : CoimA ⟶ IF, Nonempty (ea ≫ w ≅ ef) ∧ IsNormalEpi O w := by
  obtain ⟨V, p, hp⟩ := hea
  haveI := hp.isTwoEpi
  have h1 : IsEssNull O (p ≫ a) := (hp.isEssNull_comp.comp ma).of_iso
    (eqToIso (Category.assoc p ea ma) ≪≫ Bicategory.whiskerLeftIso p θa.symm)
  have h3 : IsEssNull O (p ≫ ef) := IsEssNull.of_comp_isTwoMono mf
    ((isEssNull_comp_left_of_square φ h1).of_iso
      (Bicategory.whiskerLeftIso p θf ≪≫ (eqToIso (Category.assoc p ef mf)).symm))
  obtain ⟨w, ⟨θw⟩⟩ := hp.fac ef h3
  exact ⟨w, ⟨θw⟩, IsNormalEpi.of_comp θw.symm hef⟩

/-- The 2-kernel of `2-coim(a)` sits inside the 2-kernel of `f`. -/
theorem exists_kerRestriction [IsTwoMono c] (φ : a ≫ g ≅ f ≫ c) (θa : a ≅ ea ≫ ma)
    {ka : KA ⟶ A} (hka : IsTwoKernel O ea ka) {kf : KF ⟶ A} (hkf : IsTwoKernel O f kf) :
    ∃ v : KA ⟶ KF, Nonempty (v ≫ kf ≅ ka) :=
  hkf.fac ka (isEssNull_comp_left_of_square φ ((hka.isEssNull_comp.comp ma).of_iso
    (eqToIso (Category.assoc ka ea ma) ≪≫ Bicategory.whiskerLeftIso ka θa.symm)))

end Reduction

section Comparison

variable {O : B} [HasBizero O] [IsStrong O] {A X KA KF KF' E CoimA IF : B} {f : A ⟶ X}
  {ea : A ⟶ CoimA}

/-- **Proposition 6.21 `P:KerComparison`, a fourth application of the Pure Snake Lemma.** The
comparison `ā'' : 2-Ker(f) ⟶ 2-Ker(f')` induced by the 2-coimage of `a` is a normal
2-epimorphism. -/
theorem isNormalEpi_kerComparison (hHSD : IsHSD O)
    {ka : KA ⟶ A} (hka : IsTwoKernel O ea ka) (hea : IsNormalEpi O ea)
    {kf : KF ⟶ A} (hkf : IsTwoKernel O f kf) {ef : A ⟶ IF} (hef : IsTwoCokernel O kf ef)
    {v : KA ⟶ KF} (θv : v ≫ kf ≅ ka) {e : KF ⟶ E} (he : IsTwoCokernel O v e)
    {w : CoimA ⟶ IF} (θw : ea ≫ w ≅ ef) {kf' : KF' ⟶ CoimA} (hkf' : IsTwoKernel O w kf')
    {aBB : KF ⟶ KF'} (ψ : aBB ≫ kf' ≅ kf ≫ ea) : IsNormalEpi O aBB := by
  obtain ⟨V, p, hp⟩ := hea
  haveI := hkf'.isTwoMono
  have P := pureSnakeComparison hHSD (isSES_of_isTwoCokernel hp hka)
    (isSES_of_isTwoKernel hkf hef) θv.symm θw he hkf'
  refine ⟨KA, v, (he.comp_isEquiv1 P.isEquiv1).of_iso_right (IsTwoMono.preimageIso kf' ?_)⟩
  calc (e ≫ P.j) ≫ kf' ≅ e ≫ P.j ≫ kf' := eqToIso (Category.assoc _ _ _)
    _ ≅ kf ≫ ea := P.θ
    _ ≅ aBB ≫ kf' := ψ.symm

end Comparison

section General

/-- **The special case of the Snake Lemma, as a hypothesis.** The reduction of the general case
to the special one is independent of *why* the special case holds, so it is shared: 2-di-exactness
supplies this through `SnakeLean.SnakeDelta.exists_snakeConnecting`, and the non-self-dual
hypotheses of Section 9 supply it through `SnakeLean.NSDConnecting.exists_snakeConnectingNSD`. -/
def SnakeSpecial (O : B) [HasBizero O] : Prop :=
  ∀ {A M C X Y Z KG KH QF QG : B} {a : A ⟶ M} {b : M ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}
    (S : MorphismSES a b c d), IsSES O a b → IsSES O c d →
    IsNormal O S.f → IsNormal O S.g → IsNormal O S.h →
    ∀ {kg : KG ⟶ M} {kh : KH ⟶ C} {qf : X ⟶ QF} {qg : Y ⟶ QG},
      IsTwoKernel O S.g kg → IsTwoKernel O S.h kh → IsTwoCokernel O S.f qf →
      IsTwoCokernel O S.g qg → ∀ {bBar : KG ⟶ KH} {cBar : QF ⟶ QG},
      (bBar ≫ kh ≅ kg ≫ b) → (qf ≫ cBar ≅ c ≫ qg) →
      ∃ (CB KC : B) (qb : KH ⟶ CB) (z : CB ⟶ KC) (mc : KC ⟶ QF),
        IsNormal O bBar ∧ IsNormal O cBar ∧ IsTwoCokernel O bBar qb ∧ IsEquiv1 z ∧
          IsTwoKernel O cBar mc

variable {O : B} [HasBizero O] [IsStrong O] [TwoZExact O]
  {A M C X Y Z KF KG KH QF QG QH CoimA ImD : B}
  {a : A ⟶ M} {b : M ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}

/-- **The Snake Lemma, general case**, reduced to the special one. The conclusion asserts
2-exactness at the four inner positions and, separately, that `d̲` is normal, so that all six
1-cells of the snake sequence are normal as Definition 4.5 `Def:ExactSequence` requires. -/
theorem exists_snakeGeneral_of_special (hHSD : IsHSD O) (hspec : SnakeSpecial O)
    (S : MorphismSES a b c d)
    (hb : IsNormalEpi O b) (hc : IsNormalMono O c)
    {ea : A ⟶ CoimA} {ma : CoimA ⟶ M} (θa : a ≅ ea ≫ ma) (hea : IsNormalEpi O ea)
    (hma : IsTwoKernel O b ma)
    {ed : Y ⟶ ImD} {md : ImD ⟶ Z} (θd : d ≅ ed ≫ md) (hed : IsTwoCokernel O c ed)
    (hmd : IsNormalMono O md)
    (hf : IsNormal O S.f) (hg : IsNormal O S.g) (hh : IsNormal O S.h)
    {kf : KF ⟶ A} (hkf : IsTwoKernel O S.f kf) {kg : KG ⟶ M} (hkg : IsTwoKernel O S.g kg)
    {kh : KH ⟶ C} (hkh : IsTwoKernel O S.h kh)
    {qf : X ⟶ QF} (hqf : IsTwoCokernel O S.f qf) {qg : Y ⟶ QG} (hqg : IsTwoCokernel O S.g qg)
    {qh : Z ⟶ QH} (hqh : IsTwoCokernel O S.h qh)
    {aBar : KF ⟶ KG} (ψa : aBar ≫ kg ≅ kf ≫ a) {bBar : KG ⟶ KH} (ψb : bBar ≫ kh ≅ kg ≫ b)
    {cBar : QF ⟶ QG} (ψc : qf ≫ cBar ≅ c ≫ qg) {dBar : QG ⟶ QH} (ψd : qg ≫ dBar ≅ d ≫ qh) :
    ∃ δ : KH ⟶ QF, IsExactAt O aBar bBar ∧ IsExactAt O bBar δ ∧ IsExactAt O δ cBar ∧
      IsExactAt O cBar dBar ∧ IsNormal O dBar := by
  obtain ⟨IF, ef, mf, hef, hmf, ⟨θf⟩⟩ := hf
  obtain ⟨IH, eh, mh, heh, hmh, ⟨θh⟩⟩ := hh
  haveI := hef.isTwoEpi
  haveI := hmf.isTwoMono
  haveI := heh.isTwoEpi
  haveI := hmh.isTwoMono
  haveI := hea.isTwoEpi
  haveI := hmd.isTwoMono
  haveI := hb.isTwoEpi
  haveI := hc.isTwoMono
  haveI := hkg.isTwoMono
  haveI := hqg.isTwoEpi
  haveI : IsTwoMono b.op := isTwoMono_op b
  haveI : IsTwoMono eh.op := isTwoMono_op eh
  -- The restriction `f'` of `f` along `2-coim(a)`, and dually the corestriction `h'` of `h`.
  obtain ⟨wf, ⟨θwf⟩, hwf⟩ := exists_restriction S.φK θa hea θf hef
  obtain ⟨wh, ⟨θwh'⟩, hwh'⟩ := exists_restriction (O := op O) (a := d.op) (f := S.h.op)
    (g := S.g.op) (c := b.op) (ea := md.op) (ma := ed.op) (ef := mh.op) (mf := eh.op)
    S.φQ.symm.op2 θd.op2 (isNormalEpi_op hmd) θh.op2 (isNormalEpi_op hmh)
  have θwh : wh.unop ≫ md ≅ mh := θwh'.unop2
  have hwh : IsNormalMono O wh.unop := isNormalMono_of_op hwh'
  -- The two triangles of the reduction.
  have θf' : ea ≫ wf ≫ mf ≅ S.f := calc
    ea ≫ wf ≫ mf ≅ (ea ≫ wf) ≫ mf := (eqToIso (Category.assoc ea wf mf)).symm
    _ ≅ ef ≫ mf := Bicategory.whiskerRightIso θwf mf
    _ ≅ S.f := θf.symm
  have θh' : (eh ≫ wh.unop) ≫ md ≅ S.h := calc
    (eh ≫ wh.unop) ≫ md ≅ eh ≫ wh.unop ≫ md := eqToIso (Category.assoc eh wh.unop md)
    _ ≅ eh ≫ mh := Bicategory.whiskerLeftIso eh θwh
    _ ≅ S.h := θh.symm
  -- The two squares of the reduced ladder.
  have φK' : ma ≫ S.g ≅ (wf ≫ mf) ≫ c := IsTwoEpi.preimageIso ea <| calc
    ea ≫ ma ≫ S.g ≅ (ea ≫ ma) ≫ S.g := (eqToIso (Category.assoc ea ma S.g)).symm
    _ ≅ a ≫ S.g := Bicategory.whiskerRightIso θa.symm S.g
    _ ≅ S.f ≫ c := S.φK
    _ ≅ (ea ≫ wf ≫ mf) ≫ c := Bicategory.whiskerRightIso θf'.symm c
    _ ≅ ea ≫ (wf ≫ mf) ≫ c := eqToIso (Category.assoc ea (wf ≫ mf) c)
  have φQ' : b ≫ eh ≫ wh.unop ≅ S.g ≫ ed := IsTwoMono.preimageIso md <| calc
    (b ≫ eh ≫ wh.unop) ≫ md ≅ b ≫ (eh ≫ wh.unop) ≫ md :=
      eqToIso (Category.assoc b (eh ≫ wh.unop) md)
    _ ≅ b ≫ S.h := Bicategory.whiskerLeftIso b θh'
    _ ≅ S.g ≫ d := S.φQ
    _ ≅ S.g ≫ ed ≫ md := Bicategory.whiskerLeftIso S.g θd
    _ ≅ (S.g ≫ ed) ≫ md := (eqToIso (Category.assoc S.g ed md)).symm
  -- The two rows of the reduced ladder are short 2-exact.
  have hab' : IsSES O ma b := by
    obtain ⟨V, p, hp⟩ := hb
    exact isSES_of_isTwoKernel hma (hp.of_isTwoKernel hma)
  have hcd' : IsSES O c ed := by
    obtain ⟨V, ℓ, hℓ⟩ := hc
    exact isSES_of_isTwoCokernel hed (hℓ.of_isTwoCokernel hed)
  -- Transferring the 2-kernels and 2-cokernels.
  have hkwf : IsTwoKernel O (wf ≫ mf) (twoKernel O wf) :=
    (isTwoKernel_comp_isTwoMono_iff mf).mpr (isTwoKernel_twoKernel O wf)
  have hkh' : IsTwoKernel O (eh ≫ wh.unop) kh :=
    (isTwoKernel_comp_isTwoMono_iff md).mp (hkh.of_iso θh'.symm)
  have hqf' : IsTwoCokernel O (wf ≫ mf) qf :=
    (isTwoCokernel_isTwoEpi_comp_iff ea).mp (hqf.of_iso θf'.symm)
  have hqwh : IsTwoCokernel O (eh ≫ wh.unop) (twoCokernel O wh.unop) :=
    (isTwoCokernel_isTwoEpi_comp_iff eh).mpr (isTwoCokernel_twoCokernel O wh.unop)
  -- The comparison `ā''` and its normality.
  have hefk : IsTwoCokernel O kf ef := isTwoCokernel_coim θf hef hkf
  have hmhk : IsTwoKernel O qh mh := isTwoKernel_img θh hmh hqh
  obtain ⟨aBB, ⟨ψaBB⟩⟩ := (isTwoKernel_twoKernel O wf).fac (kf ≫ ea)
    (hefk.isEssNull_comp.of_iso ((Bicategory.whiskerLeftIso kf θwf).symm ≪≫
      (eqToIso (Category.assoc kf ea wf)).symm))
  have haBB : IsNormalEpi O aBB := by
    obtain ⟨v, ⟨θv⟩⟩ := exists_kerRestriction S.φK θa (isTwoKernel_twoKernel O ea) hkf
    exact isNormalEpi_kerComparison hHSD (isTwoKernel_twoKernel O ea) hea hkf
      hefk θv (isTwoCokernel_twoCokernel O v) θwf (isTwoKernel_twoKernel O wf) ψaBB
  -- The comparison `d̲''` and its normality, by duality.
  obtain ⟨dBB, ⟨ψdBB⟩⟩ := (isTwoCokernel_twoCokernel O wh.unop).fac (md ≫ qh)
    ((hmhk.isEssNull_comp.of_iso (Bicategory.whiskerRightIso θwh qh).symm).of_iso
      (eqToIso (Category.assoc wh.unop md qh)))
  have hdBB : IsNormalMono O dBB := by
    obtain ⟨v, ⟨θv⟩⟩ := exists_kerRestriction (O := op O) (a := d.op) (f := S.h.op)
      (g := S.g.op) (c := b.op) (ea := md.op) (ma := ed.op) S.φQ.symm.op2 θd.op2
      (isTwoKernel_op (isTwoCokernel_twoCokernel O md)) (isTwoKernel_op hqh)
    exact isNormalMono_of_op (isNormalEpi_kerComparison (O := op O) (ea := md.op)
      (w := wh) (aBB := dBB.op) (isHSD_op hHSD)
      (isTwoKernel_op (isTwoCokernel_twoCokernel O md)) (isNormalEpi_op hmd)
      (isTwoKernel_op hqh) (isTwoCokernel_op hmhk) θv
      (isTwoCokernel_op (isTwoKernel_twoKernel O v.unop)) θwh'
      (isTwoKernel_op (isTwoCokernel_twoCokernel O wh.unop)) ψdBB.op2)
  -- The comparisons of the reduced ladder.
  obtain ⟨aBar', ⟨ψa'⟩⟩ := exists_kerMap φK'.symm hkwf hkg
  obtain ⟨dBar', ⟨ψd'⟩⟩ := exists_cokMap φQ'.symm hqg hqwh
  have θaBar : aBar ≅ aBB ≫ aBar' := IsTwoMono.preimageIso kg <| calc
    aBar ≫ kg ≅ kf ≫ a := ψa
    _ ≅ kf ≫ ea ≫ ma := Bicategory.whiskerLeftIso kf θa
    _ ≅ (kf ≫ ea) ≫ ma := (eqToIso (Category.assoc kf ea ma)).symm
    _ ≅ (aBB ≫ twoKernel O wf) ≫ ma := Bicategory.whiskerRightIso ψaBB.symm ma
    _ ≅ aBB ≫ twoKernel O wf ≫ ma := eqToIso (Category.assoc aBB (twoKernel O wf) ma)
    _ ≅ aBB ≫ aBar' ≫ kg := Bicategory.whiskerLeftIso aBB ψa'.symm
    _ ≅ (aBB ≫ aBar') ≫ kg := (eqToIso (Category.assoc aBB aBar' kg)).symm
  have θdBar : dBar ≅ dBar' ≫ dBB := IsTwoEpi.preimageIso qg <| calc
    qg ≫ dBar ≅ d ≫ qh := ψd
    _ ≅ (ed ≫ md) ≫ qh := Bicategory.whiskerRightIso θd qh
    _ ≅ ed ≫ md ≫ qh := eqToIso (Category.assoc ed md qh)
    _ ≅ ed ≫ twoCokernel O wh.unop ≫ dBB := Bicategory.whiskerLeftIso ed ψdBB.symm
    _ ≅ (ed ≫ twoCokernel O wh.unop) ≫ dBB :=
      (eqToIso (Category.assoc ed (twoCokernel O wh.unop) dBB)).symm
    _ ≅ (qg ≫ dBar') ≫ dBB := Bicategory.whiskerRightIso ψd'.symm dBB
    _ ≅ qg ≫ dBar' ≫ dBB := eqToIso (Category.assoc qg dBar' dBB)
  -- The special case, applied to the reduced ladder.
  have hf' : IsNormal O (wf ≫ mf) := ⟨IF, wf, mf, hwf, hmf, ⟨Iso.refl _⟩⟩
  have hh' : IsNormal O (eh ≫ wh.unop) := ⟨IH, eh, wh.unop, heh, hwh, ⟨Iso.refl _⟩⟩
  obtain ⟨CB, KC, qb', z', mc', hbBar', hcBar, hqb', hz', hmc'⟩ := hspec
    (⟨wf ≫ mf, S.g, eh ≫ wh.unop, φK', φQ'⟩ : MorphismSES ma b c ed)
    hab' hcd' hf' hg hh' hkg hkh' hqf' hqg ψb ψc
  haveI := hmc'.isTwoMono
  have hδ1 : IsExactAt O bBar (qb' ≫ z' ≫ mc') :=
    isExactAt_left_of_shape hbBar' hqb' hz' (isTwoKernel_twoKernel O bBar)
  have hδ2 : IsExactAt O (qb' ≫ z' ≫ mc') cBar := isExactAt_right_of_shape hqb' hz' hmc'
  set δ := qb' ≫ z' ≫ mc' with hδdef
  -- `d̲'` is a 2-cokernel of `c̲`, so `d̲ ≅ d̲' ≫ d̲''` is a normal image factorisation of `d̲`.
  have hcok : IsTwoCokernel O cBar dBar' := snake_isTwoCokernel_barD
    (⟨wf ≫ mf, S.g, eh ≫ wh.unop, φK', φQ'⟩ : MorphismSES ma b c ed) hcd' hqf' hqg hqwh ψc ψd'
  refine ⟨δ, ⟨_, aBB, aBar', haBB, ⟨θaBar⟩, ?_⟩, hδ1, hδ2, ?_,
    ⟨_, dBar', dBB, ⟨QF, cBar, hcok⟩, hdBB, ⟨θdBar⟩⟩⟩
  · exact snake_isTwoKernel_barA (⟨wf ≫ mf, S.g, eh ≫ wh.unop, φK', φQ'⟩ : MorphismSES ma b c ed)
      hab' hkwf hkg hkh' ψa' ψb
  · obtain ⟨I, e, m, he, hm, ⟨θ⟩⟩ := hcBar
    exact ⟨I, e, m, he, ⟨θ⟩,
      ((exactness_tfae θ he hm θdBar ⟨QF, cBar, hcok⟩ hdBB).out 1 0).mp hcok⟩

/-- 2-di-exactness supplies the special case of Theorem 6.9 `Snake General 2D` — the construction
of Sections 6.8 `SS:Construction` to 6.16 `SS:OuterExactness`, in the shape
`exists_snakeGeneral_of_special` consumes. -/
theorem snakeSpecial_of_twoDiExact [TwoDiExact O] : SnakeSpecial O := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ S hab hcd hf hg hh _ _ _ _ hkg hkh hqf hqg _ _ ψb ψc
  exact exists_snakeConnecting S hab hcd hf hg hh hkg hkh hqf hqg ψb ψc

/-- **Theorem 6.9 `Snake General 2D`, the Snake Lemma** in a 2-di-exact 2-category. -/
theorem exists_snakeGeneral [TwoDiExact O] (S : MorphismSES a b c d)
    (hb : IsNormalEpi O b) (hc : IsNormalMono O c)
    {ea : A ⟶ CoimA} {ma : CoimA ⟶ M} (θa : a ≅ ea ≫ ma) (hea : IsNormalEpi O ea)
    (hma : IsTwoKernel O b ma)
    {ed : Y ⟶ ImD} {md : ImD ⟶ Z} (θd : d ≅ ed ≫ md) (hed : IsTwoCokernel O c ed)
    (hmd : IsNormalMono O md)
    (hf : IsNormal O S.f) (hg : IsNormal O S.g) (hh : IsNormal O S.h)
    {kf : KF ⟶ A} (hkf : IsTwoKernel O S.f kf) {kg : KG ⟶ M} (hkg : IsTwoKernel O S.g kg)
    {kh : KH ⟶ C} (hkh : IsTwoKernel O S.h kh)
    {qf : X ⟶ QF} (hqf : IsTwoCokernel O S.f qf) {qg : Y ⟶ QG} (hqg : IsTwoCokernel O S.g qg)
    {qh : Z ⟶ QH} (hqh : IsTwoCokernel O S.h qh)
    {aBar : KF ⟶ KG} (ψa : aBar ≫ kg ≅ kf ≫ a) {bBar : KG ⟶ KH} (ψb : bBar ≫ kh ≅ kg ≫ b)
    {cBar : QF ⟶ QG} (ψc : qf ≫ cBar ≅ c ≫ qg) {dBar : QG ⟶ QH} (ψd : qg ≫ dBar ≅ d ≫ qh) :
    ∃ δ : KH ⟶ QF, IsExactAt O aBar bBar ∧ IsExactAt O bBar δ ∧ IsExactAt O δ cBar ∧
      IsExactAt O cBar dBar ∧ IsNormal O dBar :=
  exists_snakeGeneral_of_special isHSD_of_twoDiExact snakeSpecial_of_twoDiExact S hb hc θa hea
    hma θd hed hmd hf hg hh hkf hkg hkh hqf hqg hqh ψa ψb ψc ψd

end General

end SnakeLean
