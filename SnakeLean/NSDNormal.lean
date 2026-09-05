/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.NonSelfDual

/-!
# The two normal morphisms of the non-self-dual Snake Lemma

Section 9.9 `SS:NSDNormal`. Under (DPN) and (NEC), the two normality statements
that Section 6 extracted from (DI2) at its two sites are recovered, at very different prices.

* `isNormal_cLower` is Proposition 9.12 `P:NSDcbar`: the pair `(c, 2-coker(g))` is antinormal
  and its dinversion *is* `2-img(h) ∘ t`, a normal 2-epimorphism followed by a normal
  2-monomorphism; (DPN) then
  makes `2-coker(g) ∘ c` normal, and `c̲` follows by cancelling the 2-epimorphism `2-coker(f)`.
* `isNormal_bBar_full` is Proposition 9.13 `P:NSDbbar`: the antinormal decomposition
  `2-Ker(g) ↣ 2-Ker(e) ↠ 2-Ker(h)` of `b̄` is assembled here from two applications of the Pure
  Snake Lemma, and its dinversion `A ↣ 2-Ker(e) ↠ 2-Ker(t)` is identified with `f` corestricted
  along `κ`, so that `SnakeLean.NonSelfDual.isNormal_bBar_of_isNormal_f` applies.

The 1-cells `α`, `m₁`, `e₁` and `ρ` that `isNormal_bBar_of_isNormal_f` takes as inputs are built
here: `α` and `m₁` by factoring `a` and `2-ker(g)` through `2-ker(e)`, and `e₁` and `ρ` as the
comparisons of the two pure configurations with middle object `M` that the paper describes.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.Strict B]

section CLower

variable {O : B} [HasBizero O] [IsStrong O] [DPN O] {X Y Z IG IH QG QF CX : B}
  {c : X ⟶ Y} {d : Y ⟶ Z} {qg : Y ⟶ QG} {mg : IG ⟶ Y} {mh : IH ⟶ Z} {t : IG ⟶ IH}

omit [Bicategory.Strict B] [IsStrong O] in
/-- **Proposition 9.12 `P:NSDcbar`, the composite.** The pair `(c, 2-coker(g))` is antinormal,
and its dinversion is `2-img(h) ∘ t`: a normal 2-epimorphism followed by a normal
2-monomorphism, hence normal. So (DPN) makes `2-coker(g) ∘ c` normal. This is the cheap half of
Remark 9.14 `Rem NSD Sites`. -/
theorem isNormal_c_comp_qg (hcd : IsSES O c d) (hqg : IsNormalEpi O qg)
    (hmg : IsTwoKernel O qg mg) (ht : IsNormalEpi O t) (hmh : IsNormalMono O mh)
    (θsq : t ≫ mh ≅ mg ≫ d) : IsNormal O (c ≫ qg) :=
  (DPN.isNormal_comp_iff ⟨_, d, hcd.isTwoKernel⟩ hqg hmg hcd.isTwoCokernel).mpr
    (IsNormal.of_iso θsq ⟨_, t, mh, ht, hmh, ⟨Iso.refl _⟩⟩)

omit [DPN O] in
/-- **A 1-cell whose composite with a 2-epimorphism on the left is normal is itself normal**, the
dual of `IsNormal.of_comp_isTwoMono`. -/
theorem IsNormal.of_isTwoEpi_comp {U V W QQ : B} {e : U ⟶ V} {u : V ⟶ W} [IsTwoEpi e]
    (h : IsNormal O (e ≫ u)) {q : W ⟶ QQ} (hq : IsTwoCokernel O (e ≫ u) q) : IsNormal O u := by
  haveI : IsTwoMono e.op := isTwoMono_op e
  exact isNormal_of_op
    (IsNormal.of_comp_isTwoMono (u := u.op) (m := e.op) (isNormal_op h) (isTwoKernel_op hq))

/-- **Proposition 9.12 `P:NSDcbar`.** The morphism `c̲` between the 2-cokernels is normal. -/
theorem isNormal_cLower (hcd : IsSES O c d) (hqg : IsNormalEpi O qg)
    (hmg : IsTwoKernel O qg mg) (ht : IsNormalEpi O t) (hmh : IsNormalMono O mh)
    (θsq : t ≫ mh ≅ mg ≫ d) {A : B} {f : A ⟶ X} {qf : X ⟶ QF} (hqf : IsTwoCokernel O f qf)
    {cLower : QF ⟶ QG} (ψc : qf ≫ cLower ≅ c ≫ qg) {QQ : B} {q : QG ⟶ QQ}
    (hq : IsTwoCokernel O (qf ≫ cLower) q) : IsNormal O cLower := by
  haveI : IsTwoEpi qf := hqf.isTwoEpi
  exact IsNormal.of_isTwoEpi_comp
    (IsNormal.of_iso ψc.symm (isNormal_c_comp_qg hcd hqg hmg ht hmh θsq)) hq

end CLower

section BBarAssembly

variable {O : B} [HasBizero O] [IsStrong O]
  {A M C KG KH KE KT CA CM IG IH : B}
  {a : A ⟶ M} {b : M ⟶ C} {kg : KG ⟶ M} {kh : KH ⟶ C} {eg : M ⟶ IG} {ch : C ⟶ IH}
  {t : IG ⟶ IH} {kt : KT ⟶ IG} {ke : KE ⟶ M}

/-- **Proposition 9.13 `P:NSDbbar`, first step.** Since `e ∘ a` is null, `a` factors through
`2-ker(e)`, by a normal 2-monomorphism. -/
theorem exists_alpha (hab : IsSES O a b) (hke : IsTwoKernel O (b ≫ ch) ke) :
    ∃ alpha : A ⟶ KE, IsNormalMono O alpha ∧ Nonempty (alpha ≫ ke ≅ a) := by
  have hnull : IsEssNull O (a ≫ b ≫ ch) :=
    (hab.isTwoCokernel.isEssNull_comp.comp ch).of_iso (eqToIso (by simp))
  obtain ⟨alpha, ⟨γ⟩⟩ := hke.fac a hnull
  haveI := hke.isTwoMono
  exact ⟨alpha, IsNormalMono.of_comp γ.symm ⟨_, b, hab.isTwoKernel⟩, ⟨γ⟩⟩

/-- **Proposition 9.13 `P:NSDbbar`, second step.** Since `e ∘ 2-ker(g)` is null, `2-ker(g)`
factors through `2-ker(e)`, by a normal 2-monomorphism. -/
theorem exists_mOne {Y Z : B} {g : M ⟶ Y} {d : Y ⟶ Z} {h : C ⟶ Z}
    (hkg : IsTwoKernel O g kg) (hkh : IsTwoKernel O h kh) (hch : IsTwoCokernel O kh ch)
    (φh : b ≫ h ≅ g ≫ d) (hke : IsTwoKernel O (b ≫ ch) ke) :
    ∃ m₁ : KG ⟶ KE, IsNormalMono O m₁ ∧ Nonempty (m₁ ≫ ke ≅ kg) := by
  obtain ⟨m₁, ⟨γ⟩⟩ := hke.fac kg (isEssNull_kg_comp hkg hkh hch φh)
  haveI := hke.isTwoMono
  exact ⟨m₁, IsNormalMono.of_comp γ.symm ⟨_, g, hkg⟩, ⟨γ⟩⟩

/-- **Proposition 9.13 `P:NSDbbar`, the first pure configuration.** The rows `A ↣ M ↠ C` and
`2-Ker(e) ↣ M ↠ 2-Img(h)` share the middle object `M`; their verticals are `α` and `2-coim(h)`,
and the comparison of the Pure Snake Lemma turns `2-coker(α)` into a normal 2-epimorphism
`e₁ : 2-Ker(e) ↠ 2-Ker(h)` with 2-kernel `α` — the paper's `Pure Snake Lemma` and
Proposition 3.9 `CoKernel of Composite` step. -/
theorem exists_eOne (hHSD : IsHSD O) (hab : IsSES O a b) (hkeE : IsSES O ke (b ≫ ch))
    (hkh : IsTwoKernel O ch kh) {alpha : A ⟶ KE} (hαn : IsNormalMono O alpha)
    (halpha : alpha ≫ ke ≅ a) {eA : KE ⟶ CA} (hcα : IsTwoCokernel O alpha eA) :
    ∃ e₁ : KE ⟶ KH, IsNormalEpi O e₁ ∧ IsTwoKernel O e₁ alpha ∧
      Nonempty (e₁ ≫ kh ≅ ke ≫ b) := by
  have P := pureSnakeComparison hHSD hab hkeE halpha.symm (Iso.refl (b ≫ ch)) hcα hkh
  have hcok : IsTwoCokernel O alpha (eA ≫ P.j) := hcα.comp_isEquiv1 P.isEquiv1
  refine ⟨eA ≫ P.j, ⟨_, alpha, hcok⟩,
    (hαn.choose_spec.choose_spec).of_isTwoCokernel hcok, ⟨?_⟩⟩
  calc (eA ≫ P.j) ≫ kh ≅ eA ≫ P.j ≫ kh := eqToIso (by simp)
    _ ≅ ke ≫ b := P.θ

/-- **Proposition 9.13 `P:NSDbbar`, the second pure configuration.** The rows
`2-Ker(g) ↣ M ↠ 2-Img(g)` and `2-Ker(e) ↣ M ↠ 2-Img(h)` share the middle object `M`; their
verticals are `m₁` and `t`, and the comparison turns `2-coker(m₁)` into `ρ : 2-Ker(e) ↠ 2-Ker(t)`.
-/
theorem exists_rho (hHSD : IsHSD O) (hkgeg : IsSES O kg eg) (hkeE : IsSES O ke (b ≫ ch))
    (hkt : IsTwoKernel O t kt) {m₁ : KG ⟶ KE} (hm₁ : m₁ ≫ ke ≅ kg)
    {eM : KE ⟶ CM} (hcm : IsTwoCokernel O m₁ eM) (θt : eg ≫ t ≅ b ≫ ch) :
    ∃ rho : KE ⟶ KT, IsTwoCokernel O m₁ rho ∧ Nonempty (rho ≫ kt ≅ ke ≫ eg) := by
  have P := pureSnakeComparison hHSD hkgeg hkeE hm₁.symm θt hcm hkt
  refine ⟨eM ≫ P.j, hcm.comp_isEquiv1 P.isEquiv1, ⟨?_⟩⟩
  calc (eM ≫ P.j) ≫ kt ≅ eM ≫ P.j ≫ kt := eqToIso (by simp)
    _ ≅ ke ≫ eg := P.θ

end BBarAssembly

section BBar

variable {O : B} [HasBizero O] [IsStrong O] [TwoZExact O] [DPN O]
  {A M C X Y Z KG KH KE KT KF IG IH : B}
  {a : A ⟶ M} {b : M ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}
  {kg : KG ⟶ M} {kh : KH ⟶ C} {eg : M ⟶ IG} {mg : IG ⟶ Y} {ch : C ⟶ IH} {mh : IH ⟶ Z}
  {t : IG ⟶ IH} {kt : KT ⟶ IG} {kappa : KT ⟶ X} {ke : KE ⟶ M} {kf : KF ⟶ A}
  {bBar : KG ⟶ KH}

/-- **Proposition 9.13 `P:NSDbbar`, with the data.** The antinormal decomposition
`2-Ker(g) ↣ 2-Ker(e) ↠ 2-Ker(h)` of `b̄` is assembled from the two pure configurations with
middle object `M`; its dinversion `A ↣ 2-Ker(e) ↠ 2-Ker(t)` composed with `κ` is the vertical
`f`, so that (DPN) transfers normality from `f` to `b̄`. The 1-cells are returned as well,
because the connecting 1-cell of Section 9.15 `SS:NSDConnecting` is built from the dinversion. -/
theorem exists_bBarData (S : MorphismSES a b c d) (hHSD : IsHSD O)
    (hab : IsSES O a b) (hkeE : IsSES O ke (b ≫ ch))
    (hkg : IsTwoKernel O S.g kg) (hkh : IsTwoKernel O S.h kh) (hch : IsTwoCokernel O kh ch)
    (hkt : IsTwoKernel O t kt) (heg : IsTwoCokernel O kg eg)
    (hf : IsNormal O S.f) (hkf : IsTwoKernel O S.f kf)
    (θg : eg ≫ mg ≅ S.g) (θh : ch ≫ mh ≅ S.h) (θt : eg ≫ t ≅ b ≫ ch)
    (θk : kt ≫ mg ≅ kappa ≫ c) (ψb : bBar ≫ kh ≅ kg ≫ b)
    [IsTwoMono kappa] [IsTwoMono c] [IsTwoMono mh] :
    ∃ (KE' : B) (alpha : A ⟶ KE') (m₁ : KG ⟶ KE') (e₁ : KE' ⟶ KH) (rho : KE' ⟶ KT),
      IsNormalMono O m₁ ∧ IsNormalEpi O e₁ ∧ IsTwoKernel O e₁ alpha ∧
        IsTwoCokernel O m₁ rho ∧ Nonempty (bBar ≅ m₁ ≫ e₁) ∧
        Nonempty ((alpha ≫ rho) ≫ kappa ≅ S.f) ∧ IsNormal O bBar := by
  haveI : IsTwoMono kh := hkh.isTwoMono
  have hkhch : IsTwoKernel O ch kh := (isTwoKernel_comp_isTwoMono_iff mh).mp (hkh.of_iso θh.symm)
  have hkgeg' : IsSES O kg eg := isSES_of_isTwoKernel hkg heg
  obtain ⟨alpha, hαn, ⟨halpha⟩⟩ := exists_alpha hab hkeE.isTwoKernel
  obtain ⟨m₁, hm₁n, ⟨hm₁⟩⟩ := exists_mOne hkg hkh hch S.φQ hkeE.isTwoKernel
  obtain ⟨e₁, he₁, hαker, ⟨θe₁⟩⟩ :=
    exists_eOne hHSD hab hkeE hkhch hαn halpha (isTwoCokernel_twoCokernel O alpha)
  obtain ⟨rho, hρ, ⟨θρ⟩⟩ :=
    exists_rho hHSD hkgeg' hkeE hkt hm₁ (isTwoCokernel_twoCokernel O m₁) θt
  have θb : bBar ≅ m₁ ≫ e₁ := by
    refine IsTwoMono.preimageIso kh ?_
    calc bBar ≫ kh ≅ kg ≫ b := ψb
      _ ≅ (m₁ ≫ ke) ≫ b := Bicategory.whiskerRightIso hm₁.symm b
      _ ≅ m₁ ≫ ke ≫ b := eqToIso (by simp)
      _ ≅ m₁ ≫ e₁ ≫ kh := Bicategory.whiskerLeftIso m₁ θe₁.symm
      _ ≅ (m₁ ≫ e₁) ≫ kh := eqToIso (by simp)
  have θfk : (alpha ≫ rho) ≫ kappa ≅ S.f := by
    refine IsTwoMono.preimageIso c ?_
    calc ((alpha ≫ rho) ≫ kappa) ≫ c ≅ (alpha ≫ rho) ≫ kappa ≫ c := eqToIso (by simp)
      _ ≅ (alpha ≫ rho) ≫ kt ≫ mg := Bicategory.whiskerLeftIso _ θk.symm
      _ ≅ alpha ≫ (rho ≫ kt) ≫ mg := eqToIso (by simp)
      _ ≅ alpha ≫ (ke ≫ eg) ≫ mg := Bicategory.whiskerLeftIso alpha
            (Bicategory.whiskerRightIso θρ mg)
      _ ≅ alpha ≫ ke ≫ eg ≫ mg := eqToIso (by simp)
      _ ≅ alpha ≫ ke ≫ S.g := Bicategory.whiskerLeftIso alpha
            (Bicategory.whiskerLeftIso ke θg)
      _ ≅ (alpha ≫ ke) ≫ S.g := eqToIso (by simp)
      _ ≅ a ≫ S.g := Bicategory.whiskerRightIso halpha S.g
      _ ≅ S.f ≫ c := S.φK
  exact ⟨KE, alpha, m₁, e₁, rho, hm₁n, he₁, hαker, hρ, ⟨θb⟩, ⟨θfk⟩,
    isNormal_bBar_of_isNormal_f hm₁n he₁ hαker hρ hf hkf θfk θb⟩

/-- **Proposition 9.13 `P:NSDbbar`.** The morphism `b̄` between the 2-kernels is normal. -/
theorem isNormal_bBar_full (S : MorphismSES a b c d) (hHSD : IsHSD O)
    (hab : IsSES O a b) (hkeE : IsSES O ke (b ≫ ch))
    (hkg : IsTwoKernel O S.g kg) (hkh : IsTwoKernel O S.h kh) (hch : IsTwoCokernel O kh ch)
    (hkt : IsTwoKernel O t kt) (heg : IsTwoCokernel O kg eg)
    (hf : IsNormal O S.f) (hkf : IsTwoKernel O S.f kf)
    (θg : eg ≫ mg ≅ S.g) (θh : ch ≫ mh ≅ S.h) (θt : eg ≫ t ≅ b ≫ ch)
    (θk : kt ≫ mg ≅ kappa ≫ c) (ψb : bBar ≫ kh ≅ kg ≫ b)
    [IsTwoMono kappa] [IsTwoMono c] [IsTwoMono mh] : IsNormal O bBar := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ :=
    exists_bBarData S hHSD hab hkeE hkg hkh hch hkt heg hf hkf θg θh θt θk ψb
  exact h

end BBar

end SnakeLean
