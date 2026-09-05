/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.NSDNormal

/-!
# The connecting 1-cell of the non-self-dual Snake Lemma

Section 9.15 `SS:NSDConnecting`. The construction differs from Section 6's: the connecting 1-cell
is built as `2-ker(c̲) ∘ z ∘ 2-coker(b̄)` from a pure configuration with middle object `X`, not
`C` (Proposition 9.16 `P:NSDLambda`), and the equivalence `z` is assembled from the four
identifications of Lemma 9.17 `L:NSDChain`.

Two of the four are equalities of objects rather than equivalences, because a 2-cokernel of
`λ ∘ 2-coim(f)` *is* a 2-cokernel of `λ` and a 2-kernel of `v ∘ μ` *is* a 2-kernel of `v`. The
remaining two are Lemma 4.10 `L:DinversionCoker` and the comparison of the Pure Snake Lemma. That
is why the blueprint marks Lemma 9.17 as partial: its four identifications are run inside
`exists_snakeConnectingNSD`, and only their composite is stated.

## Both halves of the theorem

`exists_snakeGeneralNSD` is Theorem 9.19 `T:SnakeNonSelfDual` under (DPN) and (NEC);
`exists_snakeGeneralNSD'` is its last sentence, with normal 2-monomorphisms closed under
composition instead. The second is a transport of the first through `Bᵒᵖ`, and the one thing the
transport needs that the first half's conclusion did not originally carry is the normality of
the last 1-cell of the snake sequence — which is why both theorems, like `exists_snakeGeneral`,
now assert `IsNormal O d̲` alongside the four 2-exactness statements.

## `L:DinversionCoker`

`exists_isEquiv1_cokernel_dinversion` is Lemma 4.10 `L:DinversionCoker`, added to Section 4 for this
purpose: an antinormal composite and its dinversion have the same 2-cokernel. The proof is the
paper's, and it is a pure universal-property argument: a 1-cell killing `e ∘ m` corresponds to a
1-cell killing the dinversion, in both directions, and the two correspondences undo each other
because `e` and `q` are 2-epimorphisms.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.Strict B]

section DinversionCokernel

variable {O : B} [HasBizero O] [IsStrong O] {K X R N Cc Q₁ Q₂ : B}
  {m : K ⟶ X} {e : X ⟶ R} {k : N ⟶ X} {q : X ⟶ Cc} {q₁ : R ⟶ Q₁} {q₂ : Cc ⟶ Q₂}

/-- **Lemma 4.10 `L:DinversionCoker`.** An antinormal composite and its dinversion have the same
2-cokernel. -/
theorem exists_isEquiv1_cokernel_dinversion (he : IsNormalEpi O e) (hk : IsTwoKernel O e k)
    (hq : IsTwoCokernel O m q) (hq₁ : IsTwoCokernel O (m ≫ e) q₁)
    (hq₂ : IsTwoCokernel O (k ≫ q) q₂) : ∃ x : Q₂ ⟶ Q₁, IsEquiv1 x := by
  obtain ⟨S, s, hs⟩ := he
  have hek : IsTwoCokernel O k e := (isSES_of_isTwoCokernel hs hk).isTwoCokernel
  haveI : IsTwoEpi e := hs.isTwoEpi
  haveI : IsTwoEpi q := hq.isTwoEpi
  haveI : IsTwoEpi q₁ := hq₁.isTwoEpi
  haveI : IsTwoEpi q₂ := hq₂.isTwoEpi
  -- A 1-cell killing `m ≫ e` induces one killing the dinversion.
  obtain ⟨q₁', ⟨γ₁⟩⟩ := hq.fac (e ≫ q₁)
    (hq₁.isEssNull_comp.of_iso (eqToIso (by simp)))
  have hnull₁ : IsEssNull O ((k ≫ q) ≫ q₁') :=
    ((hk.isEssNull_comp.comp q₁)).of_iso (by
      calc (k ≫ e) ≫ q₁ ≅ k ≫ e ≫ q₁ := eqToIso (by simp)
        _ ≅ k ≫ q ≫ q₁' := Bicategory.whiskerLeftIso k γ₁.symm
        _ ≅ (k ≫ q) ≫ q₁' := eqToIso (by simp))
  obtain ⟨x, ⟨γx⟩⟩ := hq₂.fac q₁' hnull₁
  -- And conversely.
  obtain ⟨q₂', ⟨γ₂⟩⟩ := hek.fac (q ≫ q₂)
    (hq₂.isEssNull_comp.of_iso (eqToIso (by simp)))
  have hnull₂ : IsEssNull O ((m ≫ e) ≫ q₂') :=
    ((hq.isEssNull_comp.comp q₂)).of_iso (by
      calc (m ≫ q) ≫ q₂ ≅ m ≫ q ≫ q₂ := eqToIso (by simp)
        _ ≅ m ≫ e ≫ q₂' := Bicategory.whiskerLeftIso m γ₂.symm
        _ ≅ (m ≫ e) ≫ q₂' := eqToIso (by simp))
  obtain ⟨y, ⟨γy⟩⟩ := hq₁.fac q₂' hnull₂
  -- The two are mutually inverse.
  have hx : q₂' ≫ x ≅ q₁ := by
    refine IsTwoEpi.preimageIso e ?_
    calc e ≫ q₂' ≫ x ≅ (e ≫ q₂') ≫ x := eqToIso (by simp)
      _ ≅ (q ≫ q₂) ≫ x := Bicategory.whiskerRightIso γ₂ x
      _ ≅ q ≫ q₂ ≫ x := eqToIso (by simp)
      _ ≅ q ≫ q₁' := Bicategory.whiskerLeftIso q γx
      _ ≅ e ≫ q₁ := γ₁
  have hy : q₁' ≫ y ≅ q₂ := by
    refine IsTwoEpi.preimageIso q ?_
    calc q ≫ q₁' ≫ y ≅ (q ≫ q₁') ≫ y := eqToIso (by simp)
      _ ≅ (e ≫ q₁) ≫ y := Bicategory.whiskerRightIso γ₁ y
      _ ≅ e ≫ q₁ ≫ y := eqToIso (by simp)
      _ ≅ e ≫ q₂' := Bicategory.whiskerLeftIso e γy
      _ ≅ q ≫ q₂ := γ₂
  refine ⟨x, y, ⟨?_⟩, ⟨?_⟩⟩
  · refine IsTwoEpi.preimageIso q₂ ?_
    calc q₂ ≫ x ≫ y ≅ (q₂ ≫ x) ≫ y := eqToIso (by simp)
      _ ≅ q₁' ≫ y := Bicategory.whiskerRightIso γx y
      _ ≅ q₂ := hy
      _ ≅ q₂ ≫ 𝟙 Q₂ := eqToIso (by simp)
  · refine IsTwoEpi.preimageIso q₁ ?_
    calc q₁ ≫ y ≫ x ≅ (q₁ ≫ y) ≫ x := eqToIso (by simp)
      _ ≅ q₂' ≫ x := Bicategory.whiskerRightIso γy x
      _ ≅ q₁ := hx
      _ ≅ q₁ ≫ 𝟙 Q₁ := eqToIso (by simp)

end DinversionCokernel

section ImageFactorisation

variable {O : B} [HasBizero O] [IsStrong O] {A A' KW QW : B} {w : A ⟶ A'} {kw : KW ⟶ A}
  {qw : A ⟶ QW}

/-- **The 2-epimorphism of a normal image factorisation may be taken to be the 2-cokernel of the
2-kernel**, which is how Proposition 9.12 `P:NSDcbar` names `μ`. This is the first step of the
proof of Proposition 3.22 `Image Factorisation of Normal Map is Unique`, isolated. -/
theorem exists_normalMono_of_isNormal (h : IsNormal O w) (hkw : IsTwoKernel O w kw)
    (hqw : IsTwoCokernel O kw qw) :
    ∃ mu : QW ⟶ A', IsNormalMono O mu ∧ Nonempty (qw ≫ mu ≅ w) := by
  obtain ⟨I, e, m, he, hm, ⟨θ⟩⟩ := h
  haveI : IsTwoEpi e := he.isTwoEpi
  haveI : IsTwoMono m := hm.isTwoMono
  haveI : IsTwoEpi qw := hqw.isTwoEpi
  have hke : IsTwoKernel O e kw := (isTwoKernel_comp_isTwoMono_iff m).mp (hkw.of_iso θ)
  obtain ⟨S, s, hs⟩ := he
  have hcok : IsTwoCokernel O kw e := (isSES_of_isTwoCokernel hs hke).isTwoCokernel
  obtain ⟨u, ⟨γ⟩⟩ := hqw.fac e hcok.isEssNull_comp
  obtain ⟨u', ⟨γ'⟩⟩ := hcok.fac qw hqw.isEssNull_comp
  have h₁ : u ≫ u' ≅ 𝟙 QW := by
    refine IsTwoEpi.preimageIso qw ?_
    calc qw ≫ u ≫ u' ≅ (qw ≫ u) ≫ u' := eqToIso (by simp)
      _ ≅ e ≫ u' := Bicategory.whiskerRightIso γ u'
      _ ≅ qw := γ'
      _ ≅ qw ≫ 𝟙 QW := eqToIso (by simp)
  have h₂ : u' ≫ u ≅ 𝟙 I := by
    refine IsTwoEpi.preimageIso e ?_
    calc e ≫ u' ≫ u ≅ (e ≫ u') ≫ u := eqToIso (by simp)
      _ ≅ qw ≫ u := Bicategory.whiskerRightIso γ' u
      _ ≅ e := γ
      _ ≅ e ≫ 𝟙 I := eqToIso (by simp)
  refine ⟨u ≫ m, IsNormalMono.isEquiv1_comp hm ⟨u', ⟨h₁⟩, ⟨h₂⟩⟩, ⟨?_⟩⟩
  calc qw ≫ u ≫ m ≅ (qw ≫ u) ≫ m := eqToIso (by simp)
    _ ≅ e ≫ m := Bicategory.whiskerRightIso γ m
    _ ≅ w := θ.symm

end ImageFactorisation

section Lambda

variable {O : B} [HasBizero O] [IsStrong O] {A X KF IF KE KT QF QK : B}
  {f : A ⟶ X} {kf : KF ⟶ A} {ecf : A ⟶ IF} {mf : IF ⟶ X} {qf : X ⟶ QF}
  {alpha : A ⟶ KE} {rho : KE ⟶ KT} {kappa : KT ⟶ X} {lambda : IF ⟶ KT}

/-- **Proposition 9.16 `P:NSDLambda`.** The dinversion `ρ ∘ α` kills `2-ker(f)`, because `κ`
reflects null morphisms and `κ ∘ ρ ∘ α ≅ f`; so it factors through `2-coim(f)` by a 1-cell `λ`
into `2-Ker(t)`, and `λ` is a normal 2-monomorphism because `κ ∘ λ ≅ 2-img(f)`. The proof is the
paper's. -/
theorem exists_lambda (hkf : IsTwoKernel O f kf) (hcf : IsTwoCokernel O kf ecf)
    (θf : ecf ≫ mf ≅ f) (hmf : IsNormalMono O mf) [IsTwoMono kappa]
    (θfk : (alpha ≫ rho) ≫ kappa ≅ f) :
    ∃ lambda : IF ⟶ KT, IsNormalMono O lambda ∧ Nonempty (ecf ≫ lambda ≅ alpha ≫ rho) ∧
      Nonempty (lambda ≫ kappa ≅ mf) := by
  haveI : IsTwoEpi ecf := hcf.isTwoEpi
  have hnull : IsEssNull O (kf ≫ alpha ≫ rho) := by
    refine IsEssNull.of_comp_isTwoMono kappa ?_
    refine (hkf.isEssNull_comp).of_iso ?_
    calc kf ≫ f ≅ kf ≫ (alpha ≫ rho) ≫ kappa := Bicategory.whiskerLeftIso kf θfk.symm
      _ ≅ (kf ≫ alpha ≫ rho) ≫ kappa := eqToIso (by simp)
  obtain ⟨lambda, ⟨γ⟩⟩ := hcf.fac (alpha ≫ rho) hnull
  have hlk : lambda ≫ kappa ≅ mf := by
    refine IsTwoEpi.preimageIso ecf ?_
    calc ecf ≫ lambda ≫ kappa ≅ (ecf ≫ lambda) ≫ kappa := eqToIso (by simp)
      _ ≅ (alpha ≫ rho) ≫ kappa := Bicategory.whiskerRightIso γ kappa
      _ ≅ f := θfk
      _ ≅ ecf ≫ mf := θf.symm
  exact ⟨lambda, IsNormalMono.of_comp hlk.symm hmf, ⟨γ⟩, ⟨hlk⟩⟩

/-- **The right-hand vertical of the pure configuration with middle object `X`**, the 1-cell `v`
of Proposition 9.16 `P:NSDLambda`. -/
theorem exists_v (hqf : IsTwoCokernel O mf qf) {qk : X ⟶ QK} (hqk : IsTwoCokernel O kappa qk)
    (hlk : lambda ≫ kappa ≅ mf) : ∃ v : QF ⟶ QK, Nonempty (qf ≫ v ≅ qk) := by
  refine hqf.fac qk ?_
  refine (hqk.isEssNull_comp.comp_left lambda).of_iso ?_
  calc lambda ≫ kappa ≫ qk ≅ (lambda ≫ kappa) ≫ qk := eqToIso (by simp)
    _ ≅ mf ≫ qk := Bicategory.whiskerRightIso hlk qk

end Lambda

section Assembly

variable {O : B} [HasBizero O] [IsStrong O] [TwoZExact O] [DPN O] [NormalEpiComp O]
  {A M C X Y Z KG KH QF QG : B} {a : A ⟶ M} {b : M ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}
  {kg : KG ⟶ M} {kh : KH ⟶ C} {qf : X ⟶ QF} {qg : Y ⟶ QG}
  {bBar : KG ⟶ KH} {cBar : QF ⟶ QG}

/-- **The connecting 1-cell, without self-duality.** Under (DPN) and (NEC) the shape the Snake
Lemma needs is available: `b̄` and `c̲` are normal, and `2-Cok(b̄)` is equivalent to `2-Ker(c̲)`.

The equivalence is assembled from four identifications, exactly as in Lemma 9.17 `L:NSDChain`.
Two of them are equalities of objects: a 2-cokernel of `λ ∘ 2-coim(f)` is a 2-cokernel of `λ`,
and a 2-kernel of `μ ∘ v` is a 2-kernel of `v`. The other two are Lemma 4.10 `L:DinversionCoker`,
applied to the antinormal pair `(m₁, e₁)` of Proposition 9.13 `P:NSDbbar`, and the comparison of
the Pure Snake Lemma for the pure configuration with middle object `X`.

The conclusion is in the shape `SnakeLean.SnakeDelta.exists_snakeConnecting` produces, so that
the 2-exactness statements of the Snake Lemma follow from `isExactAt_left_of_shape` and
`isExactAt_right_of_shape` exactly as in the 2-di-exact case. -/
theorem exists_snakeConnectingNSD (S : MorphismSES a b c d) (hab : IsSES O a b)
    (hcd : IsSES O c d) (hf : IsNormal O S.f) (hg : IsNormal O S.g) (hh : IsNormal O S.h)
    (hkg : IsTwoKernel O S.g kg) (hkh : IsTwoKernel O S.h kh)
    (hqf : IsTwoCokernel O S.f qf) (hqg : IsTwoCokernel O S.g qg)
    (ψb : bBar ≫ kh ≅ kg ≫ b) (ψc : qf ≫ cBar ≅ c ≫ qg) :
    ∃ (CB KC : B) (qb : KH ⟶ CB) (z : CB ⟶ KC) (mc : KC ⟶ QF),
      IsNormal O bBar ∧ IsNormal O cBar ∧ IsTwoCokernel O bBar qb ∧ IsEquiv1 z ∧
        IsTwoKernel O cBar mc := by
  have hHSD : IsHSD O := isHSD_of_dpn
  haveI : IsTwoMono c := hcd.isTwoKernel.isTwoMono
  haveI : IsTwoEpi b := hab.isTwoCokernel.isTwoEpi
  obtain ⟨IF, ecf, mf, hecf, hmf, ⟨θf⟩⟩ := id hf
  obtain ⟨IG, eg, mg, heg₀, hmg₀, ⟨θg⟩⟩ := hg
  obtain ⟨IH, ch, mh, hch₀, hmh, ⟨θh⟩⟩ := hh
  haveI : IsTwoEpi ecf := hecf.isTwoEpi
  haveI : IsTwoMono mf := hmf.isTwoMono
  haveI : IsTwoEpi eg := heg₀.isTwoEpi
  haveI : IsTwoMono mg := hmg₀.isTwoMono
  haveI : IsTwoEpi ch := hch₀.isTwoEpi
  haveI : IsTwoMono mh := hmh.isTwoMono
  haveI : IsTwoEpi qf := hqf.isTwoEpi
  have heg : IsTwoCokernel O kg eg := isTwoCokernel_coim θg heg₀ hkg
  have hch : IsTwoCokernel O kh ch := isTwoCokernel_coim θh hch₀ hkh
  have hkf : IsTwoKernel O S.f (twoKernel O S.f) := isTwoKernel_twoKernel O S.f
  have hcf : IsTwoCokernel O (twoKernel O S.f) ecf := isTwoCokernel_coim θf hecf hkf
  have hmgk : IsTwoKernel O qg mg := isTwoKernel_img θg hmg₀ hqg
  have hqfmf : IsTwoCokernel O mf qf := (isTwoCokernel_isTwoEpi_comp_iff ecf).mp
    (hqf.of_iso θf)
  -- The normal 2-epimorphism `e = b ≫ 2-coim(h)` and its 2-kernel.
  have hbch : IsNormalEpi O (b ≫ ch) := isNormalEpi_comp_coim hab hch
  obtain ⟨SS, ss, hss⟩ := hbch
  have hke : IsTwoKernel O (b ≫ ch) (twoKernel O (b ≫ ch)) := isTwoKernel_twoKernel O _
  have hkeE : IsSES O (twoKernel O (b ≫ ch)) (b ≫ ch) := isSES_of_isTwoCokernel hss hke
  -- The induced normal 2-epimorphism `t` and its 2-kernel.
  obtain ⟨t, ⟨θt⟩⟩ := heg.fac (b ≫ ch) (isEssNull_kg_comp hkg hkh hch S.φQ)
  have ht : IsNormalEpi O t := isNormalEpi_t hab hch heg θt
  have hkt : IsTwoKernel O t (twoKernel O t) := isTwoKernel_twoKernel O t
  have θsq : t ≫ mh ≅ mg ≫ d := (nonempty_square_t heg θg.symm θh.symm θt S.φQ).some
  -- The 1-cell `κ : 2-Ker(t) ↣ X`, a 2-kernel of `2-coker(g) ∘ c`.
  have hnullkt : IsEssNull O ((twoKernel O t ≫ mg) ≫ d) := by
    refine ((hkt.isEssNull_comp.comp mh)).of_iso ?_
    calc (twoKernel O t ≫ t) ≫ mh ≅ twoKernel O t ≫ t ≫ mh := eqToIso (by simp)
      _ ≅ twoKernel O t ≫ mg ≫ d := Bicategory.whiskerLeftIso _ θsq
      _ ≅ (twoKernel O t ≫ mg) ≫ d := eqToIso (by simp)
  obtain ⟨kappa, ⟨θk⟩⟩ := hcd.isTwoKernel.fac (twoKernel O t ≫ mg) hnullkt
  haveI : IsTwoMono kappa := isTwoMono_of_comp (k := twoKernel O t ≫ mg) θk.symm
  have hkappa : IsTwoKernel O (c ≫ qg) kappa := isTwoKernel_kappa hcd hkt hmgk θsq θk.symm
  -- `c̲` is normal, and `μ` names the 2-image of `2-coker(g) ∘ c`.
  have hcqg : IsNormal O (c ≫ qg) :=
    isNormal_c_comp_qg hcd ⟨_, S.g, hqg⟩ hmgk ht hmh θsq
  have hqk : IsTwoCokernel O kappa (twoCokernel O kappa) := isTwoCokernel_twoCokernel O kappa
  obtain ⟨mu, hmu, ⟨θmu⟩⟩ := exists_normalMono_of_isNormal hcqg hkappa hqk
  haveI : IsTwoMono mu := hmu.isTwoMono
  have hcBar : IsNormal O cBar :=
    isNormal_cLower hcd ⟨_, S.g, hqg⟩ hmgk ht hmh θsq hqf ψc
      (isTwoCokernel_twoCokernel O (qf ≫ cBar))
  -- The antinormal decomposition of `b̄`, and its dinversion.
  obtain ⟨KE, alpha, m₁, e₁, rho, hm₁n, he₁, hαker, hρ, ⟨θb⟩, ⟨θfk⟩, hbBar⟩ :=
    exists_bBarData S hHSD hab hkeE hkg hkh hch hkt heg hf hkf θg.symm θh.symm θt θk.symm ψb
  -- `λ`, the right-hand vertical `v`, and the pure configuration with middle object `X`.
  obtain ⟨lambda, hlam, ⟨θlam⟩, ⟨θlk⟩⟩ := exists_lambda hkf hcf θf.symm hmf θfk
  obtain ⟨v, ⟨θv⟩⟩ := exists_v hqfmf hqk θlk
  have hqL : IsTwoCokernel O lambda (twoCokernel O lambda) := isTwoCokernel_twoCokernel O lambda
  have hkv : IsTwoKernel O v (twoKernel O v) := isTwoKernel_twoKernel O v
  have P₂ := pureSnakeComparison hHSD (isSES_of_isTwoKernel hmf.choose_spec.choose_spec hqfmf)
    (isSES_of_isTwoKernel hkappa hqk) θlk.symm θv hqL hkv
  -- `L:DinversionCoker`, at the antinormal pair `(m₁, e₁)`.
  have hqb : IsTwoCokernel O bBar (twoCokernel O bBar) := isTwoCokernel_twoCokernel O bBar
  obtain ⟨x, hx⟩ := exists_isEquiv1_cokernel_dinversion he₁ hαker hρ (hqb.of_iso θb)
    (((isTwoCokernel_isTwoEpi_comp_iff ecf).mpr hqL).of_iso θlam)
  obtain ⟨x', ⟨ηx⟩, ⟨εx⟩⟩ := hx
  -- `2-Ker(v)` is a 2-kernel of `c̲`.
  have θcBar : v ≫ mu ≅ cBar := by
    refine IsTwoEpi.preimageIso qf ?_
    calc qf ≫ v ≫ mu ≅ (qf ≫ v) ≫ mu := eqToIso (by simp)
      _ ≅ twoCokernel O kappa ≫ mu := Bicategory.whiskerRightIso θv mu
      _ ≅ c ≫ qg := θmu
      _ ≅ qf ≫ cBar := ψc.symm
  refine ⟨_, _, twoCokernel O bBar, x' ≫ P₂.j, twoKernel O v, hbBar, hcBar, hqb,
    IsEquiv1.comp ⟨x, ⟨εx⟩, ⟨ηx⟩⟩ P₂.isEquiv1, ?_⟩
  exact ((isTwoKernel_comp_isTwoMono_iff mu).mpr hkv).of_iso θcBar

/-- The non-self-dual hypotheses supply the special case of the Snake Lemma: the first paragraph
of the proof of Theorem 9.19 `T:SnakeNonSelfDual`, in the shape `exists_snakeGeneral_of_special`
consumes. -/
theorem snakeSpecial_of_dpn : SnakeSpecial O := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ S hab hcd hf hg hh _ _ _ _ hkg hkh hqf hqg _ _ ψb ψc
  exact exists_snakeConnectingNSD S hab hcd hf hg hh hkg hkh hqf hqg ψb ψc

end Assembly

section General

variable {O : B} [HasBizero O] [IsStrong O] [TwoZExact O] [DPN O] [NormalEpiComp O]
  {A M C X Y Z KF KG KH QF QG QH CoimA ImD : B}
  {a : A ⟶ M} {b : M ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}

/-- **Theorem 9.19 `T:SnakeNonSelfDual`, the Snake Lemma without self-duality**: in a 2-z-exact
2-category with a strong bizero object satisfying (DPN) and (NEC), the conclusion of the Snake
Lemma holds.

Neither `TwoDiExact` nor `IsHSD` appears among the hypotheses: homological self-duality is
supplied by `isHSD_of_dpn`, and the reduction of the general case to the special one is the one
of Section 6.19 `SS:GeneralCase`, which `SnakeLean.SnakeGeneral` performs once as
`exists_snakeGeneral_of_special` — the paper's proof, whose second paragraph says the reduction
does not depend on why the special case holds. -/
theorem exists_snakeGeneralNSD (S : MorphismSES a b c d)
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
  exists_snakeGeneral_of_special isHSD_of_dpn snakeSpecial_of_dpn S hb hc θa hea hma θd hed hmd
    hf hg hh hkf hkg hkh hqf hqg hqh ψa ψb ψc ψd

end General

section GeneralDual

open Opposite Bicategory.Opposite

variable {O : B} [HasBizero O] [IsStrong O] [TwoZExact O] [DPN O] [NormalMonoComp O]
  {A M C X Y Z KF KG KH QF QG QH CoimA ImD : B}
  {a : A ⟶ M} {b : M ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}

/-- **The Snake Lemma without self-duality, dual form**: the last sentence of Theorem 9.19
`T:SnakeNonSelfDual`, with closure of normal 2-*mono*morphisms under composition in place of
(NEC). It is `exists_snakeGeneralNSD` read in `Bᵒᵖ`: the ladder turns upside down (`MorphismSES.op`
exchanges the rows and reverses the verticals), (DPN) and the closure hypothesis dualise (`dpnOp`,
`normalEpiCompOp`), and the conclusion is read back through `isExactAt_of_op`. That last step is
why the primal theorem asserts the normality of the *last* 1-cell of the snake sequence: the
transport of `IsExactAt` along `Bᵒᵖ` needs the normality of the 1-cell it is being transported
onto, and for `ā` nothing else in the dual conclusion supplies it. -/
theorem exists_snakeGeneralNSD' (S : MorphismSES a b c d)
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
  obtain ⟨δ', e₁, e₂, e₃, e₄, hn⟩ := exists_snakeGeneralNSD (O := op O) S.op
    (isNormalEpi_op hc) (isNormalMono_op hb)
    (ea := md.op) (ma := ed.op) θd.op2 (isNormalEpi_op hmd) (isTwoKernel_op hed)
    (ed := ma.op) (md := ea.op) θa.op2 (isTwoCokernel_op hma) (isNormalMono_op hea)
    (isNormal_op hh) (isNormal_op hg) (isNormal_op hf)
    (isTwoKernel_op hqh) (isTwoKernel_op hqg) (isTwoKernel_op hqf)
    (isTwoCokernel_op hkh) (isTwoCokernel_op hkg) (isTwoCokernel_op hkf)
    (aBar := dBar.op) ψd.op2 (bBar := cBar.op) ψc.op2 (cBar := bBar.op) ψb.op2
    (dBar := aBar.op) ψa.op2
  exact ⟨δ'.unop,
    isExactAt_of_op (f := aBar) (g := bBar) e₄ (isNormal_of_op hn),
    isExactAt_of_op (f := bBar) (g := δ'.unop) e₃ (isNormal_of_op e₄.isNormal),
    isExactAt_of_op (f := δ'.unop) (g := cBar) e₂ (isNormal_of_op e₃.isNormal),
    isExactAt_of_op (f := cBar) (g := dBar) e₁ (isNormal_of_op e₂.isNormal),
    isNormal_of_op e₁.isNormal⟩

end GeneralDual

end SnakeLean
