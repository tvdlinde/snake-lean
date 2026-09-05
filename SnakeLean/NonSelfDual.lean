/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.SnakeGeneral
import SnakeLean.Squares

/-!
# The non-self-dual hypotheses

This module formalises the opening of Section 9, which replaces the self-dual hypothesis of
2-di-exactness by two that are not self-dual:

* **(DPN)**, *dinversion preserves normality*: for every antinormal pair `(m, e)`, the composite
  `m ≫ e` is normal if and only if its dinversion `2-ker(e) ≫ 2-cok(m)` is;
* **closure of normal 2-epimorphisms under composition**.

## Why (DPN) alone cannot suffice

Section 9.7 `SS:NSDCircular`. The whole Snake Lemma consumes (DI2) at exactly two places:
`IsNormal O (2-ker(g) ≫ b)` in `SnakeLean.SnakeConnecting` (Lemma 6.10 `L:ImageOfBBar`) and
`IsNormal O (a ≫ 2-coim(g))` in `SnakeLean.SnakeQuotient` (Lemma 6.12 `L:ImgMapNormal`). Those
two 1-cells are each other's dinversions, since `2-ker(b) ≅ a` and `2-cok(2-ker(g)) ≅ 2-coim(g)`
for a short 2-exact top row. So (DPN) *relates* the two uses but proves neither: on its own it is
circular, and the second hypothesis is what breaks the circle. That equivalence is
`isNormal_kerComp_iff`, Proposition 9.8 `P:TwoSites`, and it needs neither strictness nor a
strong bizero object.

## What is proved here

* `dpn_of_twoDiExact`, `isHSD_of_dpn` — Proposition 9.3 `P:DPNPlace`: (DPN) sits between
  2-di-exactness and homological self-duality, so the Pure Snake Lemma and the criteria of
  Proposition 4.18 `Criteria HSD` are available under it. That both implications are strict is
  Remark 9.5 `Rem NSD Strict`, with witnesses in `SnakeLean.Pentagon` (the second) and behind
  the Serre-quotient bridge of `SnakeLean.AbCatModel` (the first).
* `dpnOp`, `normalEpiCompOp`, `normalMonoCompOp` — the hypotheses dualise, which is what makes
  the last assertion of Theorem 9.19 `T:SnakeNonSelfDual` a transport through `Bᵒᵖ`
  (`SnakeLean.NSDConnecting.exists_snakeGeneralNSD'`).
* `isNormalEpi_comp_coim`, `isEssNull_kg_comp`, `isNormalEpi_t`, `nonempty_square_t` —
  Lemma 9.10 `L:NSDEpi`: the composite `e = b ≫ 2-coim(h)` is a normal 2-epimorphism, the one
  point at which (NEC) is used, exactly as the paper says; it annihilates `2-ker(g)`; and the
  induced `t : 2-Img(g) ↠ 2-Img(h)` is a normal 2-epimorphism with its square over `d`.
* `isNormal_ke_comp_b` and `isNormal_ke_comp_coim` — the two consequences of homological
  self-duality that build the upper-left corner of the paper's diagram. Both are homological
  self-duality applied to a zero-antinormal pair with second component `e`: the pair `(a, e)`
  gives the row `A ↣ 2-Ker(e) ↠ 2-Ker(h)`, and the pair `(2-ker(g), e)` gives the row
  `2-Ker(g) ↣ 2-Ker(e) ↠ 2-Ker(t)`. Together they are the whole use the paper makes of the
  object `2-Ker(e)`; `SnakeLean.NSDNormal` turns them into the `α`, `m₁`, `e₁`, `ρ` of
  Proposition 9.13 `P:NSDbbar`.
* `isTwoKernel_kappa`, `isNormalMono_kappa` — Proposition 9.11 `P:NSDKappa`: `κ : 2-Ker(t) ↣ X`
  is a 2-kernel of `2-coker(g) ∘ c`. The morphism of short 2-exact sequences

      2-Ker(t) ↣ 2-Img(g) ↠ 2-Img(h)
         ↓κ         ↓          ↓
         X    ↣     Y     ↠    Z

  has `2-img(h)` as its right-hand vertical, a 2-monomorphism, so Proposition 5.7
  `Mono Implies Left Pullback` makes the left-hand square a bipullback; and normal
  2-monomorphisms are stable under bipullback, which is Proposition 5.4
  `P:NormalMonoBipullback` (`isTwoKernel_of_isBipullback_of_isTwoKernel`: the leg opposite a
  2-kernel of `w` in a bipullback is a 2-kernel of `f ≫ w`). This is the one use of a
  bipullback outside Section 5 (Remark 9.14 `Rem NSD Sites`).
* `IsNormal.of_comp_isTwoMono` — Proposition 3.23 `P:NormalCancel`: a 1-cell whose composite
  with a 2-monomorphism is normal is itself normal.
* `isNormal_bBar`, `isNormal_bBar_of_isNormal_f` — the key step of Proposition 9.13
  `P:NSDbbar`, given its data: `b̄` carries the antinormal decomposition
  `2-Ker(g) ↣ 2-Ker(e) ↠ 2-Ker(h)`, whose dinversion is `A ↣ 2-Ker(e) ↠ 2-Ker(t)`; that
  dinversion composed with `κ` is the vertical `f`, so `IsNormal.of_comp_isTwoMono` makes it
  normal as soon as `f` is, and (DPN) transfers normality back to `b̄`. The paper's proof, in
  these words: "now `f` is normal and `κ` is a 2-monomorphism, so `ρ ∘ α` is normal by
  Proposition 3.23; by (DPN), the composite `b̄ ≅ e₁ ∘ m₁` is normal."

## Where the theorem is, and why not here

Theorem 9.19 `T:SnakeNonSelfDual` is `exists_snakeGeneralNSD` in `SnakeLean.NSDConnecting`, in
both of its forms. The proof runs through the paper's own route — Section 9.9 `SS:NSDNormal`
in `SnakeLean.NSDNormal`, Section 9.15 `SS:NSDConnecting` in `SnakeLean.NSDConnecting`, where
the connecting 1-cell is `2-ker(c̲) ∘ 2-coker(b̄)` — and then through the reduction of the
general case to the special one, which `SnakeLean.SnakeGeneral.exists_snakeGeneral_of_special`
states with the special case as a hypothesis, because that reduction does not depend on why the
special case holds.

What this module records, in `isNormal_comp_of_isNormal_bBar`, is why the theorem could not be
had by exchanging a typeclass in `SnakeLean.SnakeGeneral`: Remark 9.20 `Rem NSD NotSwap`.
`SnakeLean.SnakeConnecting` consumes not `IsNormal O b̄` but `IsNormal O (2-ker(g) ≫ b)`, and it
uses the 2-image `i : I ⟶ C` of that composite as a *normal* 2-monomorphism, because the first
pure configuration of the Section 6 construction needs the short 2-exact sequence
`I ↣ C ↠ C/I`. Since `2-ker(g) ≫ b ≅ b̄ ≫ 2-ker(h)`, getting there from `b̄` composes two normal
2-monomorphisms — the hypothesis of the *dual* half of Theorem 9.19, not of the half assumed.
That is why Section 9 forms its pure configurations with middle objects `B` and `X` instead,
and why Proposition 9.11 has to be proved at all.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- **Condition (DPN)**, Definition 9.2 `Def:DPN`. For every antinormal pair
`(m, e)`, the antinormal composite `m ≫ e` is normal exactly when its dinversion is.

As with `IsHSD`, the 2-kernel and the 2-cokernel are universally quantified rather than chosen,
so that the condition needs no 2-z-exactness and applies at whichever 2-kernel is in hand. -/
class DPN (O : B) [HasBizero O] : Prop where
  /-- An antinormal composite is normal exactly when its dinversion is. -/
  isNormal_comp_iff {K X R N C : B} {m : K ⟶ X} {e : X ⟶ R} {k : N ⟶ X} {q : X ⟶ C} :
    IsNormalMono O m → IsNormalEpi O e → IsTwoKernel O e k → IsTwoCokernel O m q →
      (IsNormal O (m ≫ e) ↔ IsNormal O (k ≫ q))

/-- **Normal 2-epimorphisms are closed under composition.** The second hypothesis of Theorem 9.19
`T:SnakeNonSelfDual`. It is not automatic: the paper adds it separately, as Definition 9.4
`Def:NEC`. -/
class NormalEpiComp (O : B) [HasBizero O] : Prop where
  /-- A composite of normal 2-epimorphisms is a normal 2-epimorphism. -/
  isNormalEpi_comp {X Y Z : B} {e : X ⟶ Y} {e' : Y ⟶ Z} :
    IsNormalEpi O e → IsNormalEpi O e' → IsNormalEpi O (e ≫ e')

/-- **Normal 2-monomorphisms are closed under composition**, the hypothesis of the dual half of
Theorem 9.19 `T:SnakeNonSelfDual`, which `SnakeLean.NSDConnecting.exists_snakeGeneralNSD'` proves
by transport. It is also what the architecture of `SnakeLean.SnakeConnecting` would need to run the
Section 6 construction under the non-self-dual hypotheses; see the module docstring. -/
class NormalMonoComp (O : B) [HasBizero O] : Prop where
  /-- A composite of normal 2-monomorphisms is a normal 2-monomorphism. -/
  isNormalMono_comp {X Y Z : B} {m : X ⟶ Y} {m' : Y ⟶ Z} :
    IsNormalMono O m → IsNormalMono O m' → IsNormalMono O (m ≫ m')

section Basic

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O]

/-- **2-di-exactness implies (DPN)**, for the same one-line reason that it implies homological
self-duality: both `m ≫ e` and its dinversion are antinormal, so (DI2) makes both normal and the
biconditional is trivially true. -/
instance (priority := 100) dpn_of_twoDiExact [TwoDiExact O] : DPN O where
  isNormal_comp_iff hm he hk hq :=
    ⟨fun _ => isNormal_of_normalMono_comp_normalEpi ⟨_, _, hk⟩ ⟨_, _, hq⟩,
      fun _ => isNormal_of_normalMono_comp_normalEpi hm he⟩

/-- **(DPN) implies homological self-duality.** Taking the antinormal composite to be null makes
the left-hand side of the biconditional automatic, by `isNormal_of_isEssNull`. -/
theorem isHSD_of_dpn [TwoZExact O] [DPN O] : IsHSD O := by
  intro _ _ _ _ _ _ _ hme _ _ hk hq
  exact (DPN.isNormal_comp_iff hme.isNormalMono hme.isNormalEpi hk hq).mp
    (isNormal_of_isEssNull hme.isEssNull_comp)

end Basic

section Opposite

open Opposite Bicategory.Opposite

variable {O : B} [HasBizero O]

/-- **(DPN) is self-dual.** An antinormal pair `(m, e)` of `Bᵒᵖ` is the antinormal pair
`(e.unop, m.unop)` of `B` with its two members exchanged, and its dinversion is the dual of the
dinversion of that pair, read backwards; so the biconditional of `B` is the one of `Bᵒᵖ`. -/
instance dpnOp [DPN O] : DPN (op O) where
  isNormal_comp_iff {K X R N C m e k q} hm he hk hq := by
    have h := DPN.isNormal_comp_iff (O := O) (m := e.unop) (e := m.unop) (k := q.unop) (q := k.unop)
      (isNormalMono_of_op (by simpa using he)) (isNormalEpi_of_op (by simpa using hm))
      (isTwoKernel_of_op (by simpa using hq)) (isTwoCokernel_of_op (by simpa using hk))
    exact ⟨fun hme => isNormal_op (h.mp (isNormal_of_op (by simpa using hme))),
      fun hkq => isNormal_op (h.mpr (isNormal_of_op (by simpa using hkq)))⟩

/-- **The two closure hypotheses are each other's duals.** Normal 2-monomorphisms of `B` composing
is normal 2-epimorphisms of `Bᵒᵖ` composing, which is what lets the dual half of Theorem 9.19
`T:SnakeNonSelfDual` be a transport of the first half. -/
instance normalEpiCompOp [NormalMonoComp O] : NormalEpiComp (op O) where
  isNormalEpi_comp {X Y Z e e'} he he' :=
    isNormalEpi_op (NormalMonoComp.isNormalMono_comp (isNormalMono_of_op (by simpa using he'))
      (isNormalMono_of_op (by simpa using he)))

/-- The dual of `normalEpiCompOp`. -/
instance normalMonoCompOp [NormalEpiComp O] : NormalMonoComp (op O) where
  isNormalMono_comp {X Y Z m m'} hm hm' :=
    isNormalMono_op (NormalEpiComp.isNormalEpi_comp (isNormalEpi_of_op (by simpa using hm'))
      (isNormalEpi_of_op (by simpa using hm)))

end Opposite

section Reduction

variable {O : B} [HasBizero O] {A M C KG IG Y : B} {a : A ⟶ M} {b : M ⟶ C} {kg : KG ⟶ M}
  {eg : M ⟶ IG}

/-- **(DPN) makes the two uses of (DI2) equivalent, and that is all it does.**

The Snake Lemma consumes (DI2) at exactly two places: `IsNormal O (2-ker(g) ≫ b)` in
`SnakeLean.SnakeConnecting` and `IsNormal O (a ≫ 2-coim(g))` in `SnakeLean.SnakeQuotient`.
For a short 2-exact top row `(a, b)` these two 1-cells are each other's dinversions, so (DPN)
turns each into the other. It follows that (DPN) on its own cannot discharge either: the second
hypothesis of Theorem 9.19 `T:SnakeNonSelfDual` is what breaks the circle. -/
theorem isNormal_kerComp_iff [DPN O] (hab : IsSES O a b) {g : M ⟶ Y}
    (hkg : IsTwoKernel O g kg) (heg : IsTwoCokernel O kg eg) :
    IsNormal O (kg ≫ b) ↔ IsNormal O (a ≫ eg) :=
  DPN.isNormal_comp_iff ⟨_, g, hkg⟩ ⟨_, a, hab.isTwoCokernel⟩ hab.isTwoKernel heg

end Reduction

section Composite

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O]
  {A M C KG KH IG ICH Y Z KE : B} {a : A ⟶ M} {b : M ⟶ C} {g : M ⟶ Y} {h : C ⟶ Z} {d : Y ⟶ Z}
  {kg : KG ⟶ M} {kh : KH ⟶ C} {eg : M ⟶ IG} {ch : C ⟶ ICH} {ke : KE ⟶ M}

omit [Strict B] [IsStrong O] in
/-- **The composite normal 2-epimorphism `e = b ∘ 2-coim(h)`.** This is the one point of
Theorem 9.19 `T:SnakeNonSelfDual` at which closure of normal 2-epimorphisms under composition is
used. -/
theorem isNormalEpi_comp_coim [NormalEpiComp O] (hab : IsSES O a b)
    (hch : IsTwoCokernel O kh ch) : IsNormalEpi O (b ≫ ch) :=
  NormalEpiComp.isNormalEpi_comp ⟨_, a, hab.isTwoCokernel⟩ ⟨_, kh, hch⟩

/-- The composite `2-ker(g) ≫ b ≫ 2-coim(h)` is null: `2-ker(g) ≫ b` factors through
`2-ker(h)`, which `2-coim(h)` annihilates. -/
theorem isEssNull_kg_comp (hkg : IsTwoKernel O g kg) (hkh : IsTwoKernel O h kh)
    (hch : IsTwoCokernel O kh ch) (φh : b ≫ h ≅ g ≫ d) :
    IsEssNull O (kg ≫ b ≫ ch) := by
  have hnull : IsEssNull O ((kg ≫ b) ≫ h) := by
    refine ((hkg.isEssNull_comp.comp d)).of_iso ?_
    calc (kg ≫ g) ≫ d ≅ kg ≫ g ≫ d := eqToIso (by simp)
      _ ≅ kg ≫ b ≫ h := Bicategory.whiskerLeftIso kg φh.symm
      _ ≅ (kg ≫ b) ≫ h := eqToIso (by simp)
  obtain ⟨u, ⟨γ⟩⟩ := hkh.fac (kg ≫ b) hnull
  refine ((hch.isEssNull_comp.comp_left u)).of_iso ?_
  calc u ≫ kh ≫ ch ≅ (u ≫ kh) ≫ ch := eqToIso (by simp)
    _ ≅ (kg ≫ b) ≫ ch := Bicategory.whiskerRightIso γ ch
    _ ≅ kg ≫ b ≫ ch := eqToIso (by simp)

/-- **The first consequence of homological self-duality**: the dinversion of the zero-antinormal
pair `(a, e)` is `2-ker(e) ≫ b`, which is therefore normal. Its normal image factorisation is
the short 2-exact sequence `A ↣ 2-Ker(e) ↠ 2-Ker(h)` of Section 9. -/
theorem isNormal_ke_comp_b [TwoZExact O] [DPN O] [NormalEpiComp O] (hab : IsSES O a b)
    (hch : IsTwoCokernel O kh ch) (hke : IsTwoKernel O (b ≫ ch) ke) : IsNormal O (ke ≫ b) := by
  refine isHSD_of_dpn ⟨⟨_, b, hab.isTwoKernel⟩, isNormalEpi_comp_coim hab hch, ?_⟩ hke
    hab.isTwoCokernel
  refine ((hab.isTwoCokernel.isEssNull_comp.comp ch)).of_iso (eqToIso (by simp))

/-- **The second consequence of homological self-duality**: the dinversion of the zero-antinormal
pair `(2-ker(g), e)` is `2-ker(e) ≫ 2-coim(g)`, which is therefore normal. Its normal image
factorisation supplies the object `2-Ker(t)` of Section 9 and the short 2-exact
sequence `2-Ker(g) ↣ 2-Ker(e) ↠ 2-Ker(t)`. -/
theorem isNormal_ke_comp_coim [TwoZExact O] [DPN O] [NormalEpiComp O] (hab : IsSES O a b)
    (hkg : IsTwoKernel O g kg) (hkh : IsTwoKernel O h kh) (hch : IsTwoCokernel O kh ch)
    (heg : IsTwoCokernel O kg eg) (hke : IsTwoKernel O (b ≫ ch) ke) (φh : b ≫ h ≅ g ≫ d) :
    IsNormal O (ke ≫ eg) :=
  isHSD_of_dpn ⟨⟨_, g, hkg⟩, isNormalEpi_comp_coim hab hch,
    isEssNull_kg_comp hkg hkh hch φh⟩ hke heg

end Composite

section Stability

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O]
  {P A A' Cc W : B} {p₁ : P ⟶ A} {p₂ : P ⟶ A'} {fc : A ⟶ Cc} {gc : A' ⟶ Cc}

/-- **Normal 2-monomorphisms are stable under bipullback**, Proposition 5.4
`P:NormalMonoBipullback`, in the precise form the argument needs: if `gc` is a 2-kernel of `w`
and the square is a bipullback, then the opposite leg `p₁` is a 2-kernel of `fc ≫ w`.

The 2-monomorphism hypothesis on `p₁` is taken as given rather than derived: in the application
it is already known, since `p₁` composed with a 2-monomorphism is one. The lemma is general; it
lives here rather than in `SnakeLean.Bipullback` because this is its only consumer, so that the
modules of Sections 2 to 4 and 6 stay free of bipullbacks (Remark 9.14 `Rem NSD Sites`). -/
theorem isTwoKernel_of_isBipullback_of_isTwoKernel {φ : p₂ ≫ gc ≅ p₁ ≫ fc}
    (h : IsBipullback p₁ p₂ fc gc φ) {w : Cc ⟶ W} (hg : IsTwoKernel O w gc) [IsTwoMono p₁] :
    IsTwoKernel O (fc ≫ w) p₁ := by
  refine ⟨?_, fun z hz => ?_, inferInstance⟩
  · refine ((hg.isEssNull_comp.comp_left p₂)).of_iso ?_
    calc p₂ ≫ gc ≫ w ≅ (p₂ ≫ gc) ≫ w := eqToIso (by simp)
      _ ≅ (p₁ ≫ fc) ≫ w := Bicategory.whiskerRightIso φ w
      _ ≅ p₁ ≫ fc ≫ w := eqToIso (by simp)
  · obtain ⟨y, ⟨γ⟩⟩ := hg.fac (z ≫ fc) (hz.of_iso (eqToIso (by simp)))
    obtain ⟨u, γ₁, -, -⟩ := h.fac z y γ
    exact ⟨u, ⟨γ₁⟩⟩

/-- The same, stated for normality rather than for a named 2-kernel. -/
theorem isNormalMono_of_isBipullback {φ : p₂ ≫ gc ≅ p₁ ≫ fc}
    (h : IsBipullback p₁ p₂ fc gc φ) (hg : IsNormalMono O gc) [IsTwoMono p₁] :
    IsNormalMono O p₁ :=
  ⟨_, fc ≫ hg.choose_spec.choose,
    isTwoKernel_of_isBipullback_of_isTwoKernel h hg.choose_spec.choose_spec⟩

/-! ### The row `2-Ker(t) ↣ X`: Proposition 9.11 `P:NSDKappa` -/

section KerT


variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O]
  {A M C X Y Z KG KH IG ICH KT : B} {a : A ⟶ M} {b : M ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}
  {g : M ⟶ Y} {h : C ⟶ Z} {kg : KG ⟶ M} {kh : KH ⟶ C} {eg : M ⟶ IG} {ch : C ⟶ ICH}
  {mg : IG ⟶ Y} {mh : ICH ⟶ Z} {t : IG ⟶ ICH} {kt : KT ⟶ IG} {kappa : KT ⟶ X}

-- `[Strict B]` is genuinely needed throughout this section: it supplies the `Category B`
-- instance behind the associativity steps and the bipullback lemmas, and omitting it breaks the
-- build. The unused-section-variable linter reports it anyway, so it is silenced here.
set_option linter.unusedSectionVars false

omit [IsStrong O] in
/-- **The induced 1-cell `t : 2-Img(g) ↠ 2-Img(h)` is a normal 2-epimorphism**, Lemma 9.10
`L:NSDEpi`. The composite
`e = b ≫ 2-coim(h)` annihilates `2-ker(g)`, hence factors through `2-coim(g)`; the factor is a
normal 2-epimorphism because `e` is one and `2-coim(g)` is a 2-epimorphism. -/
@[nolint unusedArguments]
theorem isNormalEpi_t [NormalEpiComp O] (hab : IsSES O a b) (hch : IsTwoCokernel O kh ch)
    (heg : IsTwoCokernel O kg eg) (θt : eg ≫ t ≅ b ≫ ch) : IsNormalEpi O t :=
  haveI : IsTwoEpi eg := heg.isTwoEpi
  IsNormalEpi.of_comp θt.symm (isNormalEpi_comp_coim hab hch)

omit [IsStrong O] in
/-- **The square `2-img(h) ∘ t ≅ d ∘ 2-img(g)` of Lemma 9.10 `L:NSDEpi`** — the right-hand
square of the morphism of short 2-exact sequences with rows `2-Ker(t) ↣ 2-Img(g) ↠ 2-Img(h)` and
`X ↣ Y ↠ Z` that Proposition 9.11 `P:NSDKappa` rests on. -/
@[nolint unusedArguments]
theorem nonempty_square_t (heg : IsTwoCokernel O kg eg)
    (θg : eg ≫ mg ≅ g) (θh : ch ≫ mh ≅ h) (θt : eg ≫ t ≅ b ≫ ch) (φh : b ≫ h ≅ g ≫ d) :
    Nonempty (t ≫ mh ≅ mg ≫ d) := by
  haveI : IsTwoEpi eg := heg.isTwoEpi
  refine ⟨IsTwoEpi.preimageIso eg ?_⟩
  calc eg ≫ t ≫ mh ≅ (eg ≫ t) ≫ mh := eqToIso (by simp)
    _ ≅ (b ≫ ch) ≫ mh := Bicategory.whiskerRightIso θt mh
    _ ≅ b ≫ ch ≫ mh := eqToIso (by simp)
    _ ≅ b ≫ h := Bicategory.whiskerLeftIso b θh
    _ ≅ g ≫ d := φh
    _ ≅ (eg ≫ mg) ≫ d := Bicategory.whiskerRightIso θg.symm d
    _ ≅ eg ≫ mg ≫ d := eqToIso (by simp)

/-- **`κ : 2-Ker(t) ↣ X` is a 2-kernel of `2-coker(g) ∘ c`**, Proposition 9.11 `P:NSDKappa`, by
the paper's argument: Proposition 5.7 `Mono Implies Left Pullback` makes the left-hand square of
the morphism of short 2-exact sequences above a bipullback, because its right-hand vertical
`2-img(h)` is a 2-monomorphism, and the leg of a bipullback opposite a 2-kernel is a 2-kernel
(`isTwoKernel_of_isBipullback_of_isTwoKernel`, Proposition 5.4 `P:NormalMonoBipullback`). -/
@[nolint unusedArguments]
theorem isTwoKernel_kappa {QG : B} {qg : Y ⟶ QG} (hcd : IsSES O c d) (hkt : IsTwoKernel O t kt)
    (hmg : IsTwoKernel O qg mg) [IsTwoMono mh] (θsq : t ≫ mh ≅ mg ≫ d)
    (θk : kt ≫ mg ≅ kappa ≫ c) : IsTwoKernel O (c ≫ qg) kappa := by
  haveI : IsTwoMono kt := hkt.isTwoMono
  haveI : IsTwoMono mg := hmg.isTwoMono
  haveI : IsTwoMono c := hcd.isTwoKernel.isTwoMono
  haveI : IsTwoMono kappa := isTwoMono_of_comp (k := kt ≫ mg) θk
  exact isTwoKernel_of_isBipullback_of_isTwoKernel
    (isBipullback_left_of_isTwoMono ⟨kappa, mg, mh, θk, θsq⟩ hkt hcd.isTwoKernel inferInstance)
    hmg

/-- **`2-Ker(t) ↣ X` is a normal 2-monomorphism**, the last clause of Proposition 9.11
`P:NSDKappa`: it is a 2-kernel by `isTwoKernel_kappa`, of `2-coker(g) ∘ c` for whichever
2-cokernel of `2-ker(g)` the normal 2-monomorphism `2-img(g)` is a 2-kernel of. -/
@[nolint unusedArguments]
theorem isNormalMono_kappa (hcd : IsSES O c d) (hkt : IsTwoKernel O t kt)
    (hmg : IsNormalMono O mg) [IsTwoMono mh] (θsq : t ≫ mh ≅ mg ≫ d)
    (θk : kt ≫ mg ≅ kappa ≫ c) : IsNormalMono O kappa := by
  obtain ⟨_, _, hmg'⟩ := hmg
  exact ⟨_, _, isTwoKernel_kappa hcd hkt hmg' θsq θk⟩

end KerT

end Stability

section BBar

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {U V W KF : B}

/-- **Proposition 3.23 `P:NormalCancel`.** A 1-cell whose composite with a 2-monomorphism is
normal is itself normal: the normal image factorisation of `u ≫ m` has
`2-coim(u ≫ m) = 2-coim(u)`, and its 2-image factors through `m` by a normal 2-monomorphism.

This is the step by which Proposition 9.13 `P:NSDbbar` gets normality of the dinversion
`A ↣ 2-Ker(e) ↠ 2-Ker(t)` out of normality of the vertical `f`: that dinversion composed with
the 2-monomorphism `κ : 2-Ker(t) ↣ X` is `f`. -/
theorem IsNormal.of_comp_isTwoMono {u : U ⟶ V} {m : V ⟶ W} [IsTwoMono m]
    (h : IsNormal O (u ≫ m)) {kf : KF ⟶ U} (hkf : IsTwoKernel O (u ≫ m) kf) : IsNormal O u := by
  obtain ⟨I, ef, mf, hef, hmf, ⟨θ⟩⟩ := h
  haveI : IsTwoEpi ef := hef.isTwoEpi
  haveI : IsTwoMono mf := hmf.isTwoMono
  have hkef : IsTwoKernel O ef kf := (isTwoKernel_comp_isTwoMono_iff mf).mp (hkf.of_iso θ)
  obtain ⟨S, s, hs⟩ := hef
  have hcok : IsTwoCokernel O kf ef := (isSES_of_isTwoCokernel hs hkef).isTwoCokernel
  have hnull : IsEssNull O (kf ≫ u) :=
    IsEssNull.of_comp_isTwoMono m (hkf.isEssNull_comp.of_iso (eqToIso (by simp)))
  obtain ⟨μ, ⟨γ⟩⟩ := hcok.fac u hnull
  refine ⟨I, ef, μ, ⟨S, s, hs⟩, IsNormalMono.of_comp (g := m) ?_ hmf, ⟨γ.symm⟩⟩
  refine IsTwoEpi.preimageIso ef ?_
  calc ef ≫ mf ≅ u ≫ m := θ.symm
    _ ≅ (ef ≫ μ) ≫ m := Bicategory.whiskerRightIso γ.symm m
    _ ≅ ef ≫ μ ≫ m := eqToIso (by simp)

variable {A KG KE KH KT : B}

omit [Strict B] [IsStrong O] in
/-- **The key step of Proposition 9.13 `P:NSDbbar`.** The 1-cell `b̄` between the 2-kernels
admits the antinormal decomposition `2-Ker(g) ↣ 2-Ker(e) ↠ 2-Ker(h)` whose dinversion is
`A ↣ 2-Ker(e) ↠ 2-Ker(t)`; when that dinversion is normal, (DPN) makes `b̄` normal. -/
theorem isNormal_bBar [DPN O] {m₁ : KG ⟶ KE} {e₁ : KE ⟶ KH} {alpha : A ⟶ KE} {rho : KE ⟶ KT}
    {bBar : KG ⟶ KH} (hm₁ : IsNormalMono O m₁) (he₁ : IsNormalEpi O e₁)
    (hα : IsTwoKernel O e₁ alpha) (hρ : IsTwoCokernel O m₁ rho)
    (hdin : IsNormal O (alpha ≫ rho)) (θb : bBar ≅ m₁ ≫ e₁) : IsNormal O bBar :=
  IsNormal.of_iso θb.symm ((DPN.isNormal_comp_iff hm₁ he₁ hα hρ).mpr hdin)

/-- **`b̄` is normal, from normality of the vertical `f`** — the last paragraph of the proof of
Proposition 9.13 `P:NSDbbar`, given the data `α`, `m₁`, `e₁`, `ρ` that `SnakeLean.NSDNormal`
constructs: the dinversion is identified as `f` corestricted along the 2-monomorphism `κ`,
normal by `IsNormal.of_comp_isTwoMono`, and (DPN) concludes. -/
theorem isNormal_bBar_of_isNormal_f [DPN O] {X KF : B} {m₁ : KG ⟶ KE} {e₁ : KE ⟶ KH}
    {alpha : A ⟶ KE} {rho : KE ⟶ KT} {bBar : KG ⟶ KH} {kappa : KT ⟶ X} [IsTwoMono kappa]
    {f : A ⟶ X} {kf : KF ⟶ A} (hm₁ : IsNormalMono O m₁) (he₁ : IsNormalEpi O e₁)
    (hα : IsTwoKernel O e₁ alpha) (hρ : IsTwoCokernel O m₁ rho) (hf : IsNormal O f)
    (hkf : IsTwoKernel O f kf) (θf : (alpha ≫ rho) ≫ kappa ≅ f) (θb : bBar ≅ m₁ ≫ e₁) :
    IsNormal O bBar :=
  isNormal_bBar hm₁ he₁ hα hρ
    ((IsNormal.of_iso θf.symm hf).of_comp_isTwoMono (hkf.of_iso θf.symm)) θb

end BBar

section Obstruction

variable [Bicategory.Strict B] {O : B} [HasBizero O] {KG M C KH : B} {kg : KG ⟶ M} {b : M ⟶ C}
  {kh : KH ⟶ C} {bBar : KG ⟶ KH}

/-- **What the existing architecture needs on top of normality of `b̄`** — Remark 9.20
`Rem NSD NotSwap`.

`SnakeLean.SnakeConnecting` does not consume `IsNormal O bBar`; it consumes
`IsNormal O (2-ker(g) ≫ b)`, and it uses the resulting 2-image `i : I ⟶ C` as a *normal*
2-monomorphism, since the first pure configuration of the snake construction needs the short
2-exact sequence `I ↣ C ↠ C/I`. Passing from `b̄` to `2-ker(g) ≫ b ≅ b̄ ≫ 2-ker(h)` therefore
composes two normal 2-monomorphisms, and that is the hypothesis below.

This is the *dual* of the hypothesis Theorem 9.19 `T:SnakeNonSelfDual` assumes, which is why it
cannot be obtained from `SnakeLean.SnakeGeneral` by exchanging a typeclass: under closure of
normal 2-epimorphisms it needs the paper's own route, `SnakeLean.NSDConnecting`, in which the
connecting 1-cell is `2-ker(c̲) ∘ 2-coker(b̄)` and no pure configuration with middle object `C`
is ever formed. -/
theorem isNormal_comp_of_isNormal_bBar [NormalMonoComp O] (hbBar : IsNormal O bBar)
    (hkh : IsNormalMono O kh) (ψb : bBar ≫ kh ≅ kg ≫ b) : IsNormal O (kg ≫ b) := by
  obtain ⟨I, r, i, hr, hi, ⟨θ⟩⟩ := hbBar
  refine ⟨I, r, i ≫ kh, hr, NormalMonoComp.isNormalMono_comp hi hkh, ⟨?_⟩⟩
  calc kg ≫ b ≅ bBar ≫ kh := ψb.symm
    _ ≅ (r ≫ i) ≫ kh := Bicategory.whiskerRightIso θ kh
    _ ≅ r ≫ i ≫ kh := eqToIso (Category.assoc r i kh)

end Obstruction

end SnakeLean
