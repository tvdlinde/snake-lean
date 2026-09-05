/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.Comparison

/-!
# Dinversion, homological self-duality, and the Pure Snake Lemma

This module formalises Definitions 4.7 `Def:Dinversion` and 4.17 `Def:HSD`, the equivalence
(i) ⟺ (iii) of Proposition 4.18 `Criteria HSD`, and Lemma 4.27, the `Pure Snake Lemma`.

## Orientation

The paper writes the dinversion of an antinormal pair `(m, e)` as `w = 2-cok(m) ∘ 2-ker(e)`, in
applicative order. In the diagrammatic order Lean uses this is `2-ker(e) ≫ 2-cok(m)`, and for a
morphism of short 2-exact sequences with rows `A →a Y →b C` and `X →c Y →d Z` the dinversion of
`(a, d)` is `c ≫ b : X ⟶ C`, which is the paper's `b ∘ c`.

## The two halves of (i) ⟺ (iii)

The proof of Proposition 4.18 `Criteria HSD` derives (i) ⟺ (iii) from the identification
`2-Ker(w) ≃ f` and `2-Cok(w) ≃ h` and from its converse, that every antinormal decomposition of
the zero map arises from such a morphism. Both halves are carried out here as in the paper.
`isTwoKernel_dinversion_of_ladder` and `isTwoCokernel_dinversion_of_ladder` are the
identification; `isHSD_of_isPureSnake` is the converse construction, which takes the top row
`K →m X →2-cok(m) 2-Cok(m)`, the bottom row `2-Ker(e) →2-ker(e) X →e R` and the identity of
`X` in the middle.

The two directions are not equally cheap, which is Remark 4.19 `Rem HSD Cost`. **`(i) ⟹ (iii)`
needs no 2-z-exactness**: the comparison and the two 2-kernels it compares are part of the
statement of (iii). **`(iii) ⟹ (i)` does**, because the reconstructed morphism of short 2-exact
sequences has verticals `t` and `r` whose 2-cokernel and 2-kernel must exist before (iii) can be
applied to it. The paper states the whole proposition in a 2-z-exact 2-category, and the remark
records the asymmetry.

## Exactness is the degenerate case

Conditions (i) and (ii) of Proposition 4.4 `Exactness Self-Dual` are exchanged by duality, so
neither displays the symmetry of exactness; condition (iii) is symmetric only after one notices that
`IsSES` is. Proposition 4.8 `P:NullDinversion` is the condition that is fixed by duality on the
nose: `IsZeroAntinormal.isSES_iff_isEssNull_dinversion` says that an antinormal pair `(m, e)` is
short 2-exact exactly when its dinversion `2-ker(e) ≫ 2-cok(m)` is **null**. Both directions are
the same three-line chase read in the two possible orders, and neither uses homological
self-duality; Corollary 4.9 `Cor Exact Null Dinversion` is the same for a pair of normal 1-cells.

That places exactness inside Section 4, as the paragraph after Definition 4.17 `Def:HSD` says.
Homological self-duality asks the dinversion of every antinormal pair to be **normal**; exactness
at one spot asks its dinversion to be **null**; and a null 1-cell is normal (Proposition 4.13
`P:NullNormal`, `isNormal_of_isEssNull` in `SnakeLean.Homology`). So exactness is the degenerate
case of the condition, and homological self-duality is a genuine strengthening of it — not a
hypothesis the symmetry of exactness stands in need of.

## What the hypotheses are actually for

Remark 4.28 `Rem Pure Snake Cost` says, and the linter confirms, that four of the results below
never touch the strongness of the bizero object: the two identifications `2-Ker(w) ≃ f` and
`2-Cok(w) ≃ h`, and with them the assertions of the Pure Snake Lemma that `f` is a normal
2-monomorphism and `h` a normal 2-epimorphism. They are pure factorisation arguments through the
universal properties of the two rows. Homological self-duality enters the Pure Snake Lemma at
exactly one point, exactness at `C`, and 2-z-exactness at none.

## Main results

* `IsZeroAntinormal` — an antinormal decomposition of the zero map.
* `IsHSD` — Definition 4.17 `Def:HSD`, homological self-duality.
* `IsPureSnake` — condition (iii) of Proposition 4.18 `Criteria HSD`.
* `isPureSnake_of_isHSD` and `isHSD_of_isPureSnake` — their equivalence.
* `pureSnake_isNormalMono`, `pureSnake_isNormalEpi`, `pureSnake_isExactAt_left`,
  `pureSnake_isExactAt_right` — the Pure Snake Lemma.
* `IsZeroAntinormal.isSES_iff_isEssNull_dinversion` — Proposition 4.8 `P:NullDinversion`: an
  antinormal pair is short 2-exact exactly when its dinversion is null.
* `isExactAt_iff_isEssNull_dinversion` — Corollary 4.9 `Cor Exact Null Dinversion`, the
  manifestly self-dual fourth condition for Proposition 4.4 `Exactness Self-Dual`.

## Not formalised

Condition (ii) of Proposition 4.18 `Criteria HSD`, which needs normal chain complexes; it is in
`SnakeLean.Homology`. Exactness of the Pure Snake sequence at its two outer positions is not
stated separately: it says exactly that `f` is a 2-monomorphism and `h` a 2-epimorphism, which
`isTwoKernel_dinversion_of_ladder` and its dual already record.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- An **antinormal decomposition of the zero map**: a normal 2-monomorphism followed by a normal
2-epimorphism, with null composite. -/
structure IsZeroAntinormal (O : B) [HasBizero O] {K X R : B} (m : K ⟶ X) (e : X ⟶ R) : Prop where
  /-- The first component is a normal 2-monomorphism. -/
  isNormalMono : IsNormalMono O m
  /-- The second component is a normal 2-epimorphism. -/
  isNormalEpi : IsNormalEpi O e
  /-- The antinormal composite is null. -/
  isEssNull_comp : IsEssNull O (m ≫ e)

/-- **Definition 4.17 `Def:HSD`.** A 2-category is **homologically self-dual** when the dinversion
`2-ker(e) ≫ 2-cok(m)` of every antinormal decomposition `(m, e)` of the zero map is normal.

The 2-kernel and the 2-cokernel are universally quantified rather than chosen, so that the
condition can be stated without 2-z-exactness and applied at whichever 2-kernel is in hand. -/
def IsHSD (O : B) [HasBizero O] : Prop :=
  ∀ {K X R N C : B} {m : K ⟶ X} {e : X ⟶ R}, IsZeroAntinormal O m e →
    ∀ {k : N ⟶ X} {q : X ⟶ C}, IsTwoKernel O e k → IsTwoCokernel O m q → IsNormal O (k ≫ q)

/-- **Condition (iii) of Proposition 4.18 `Criteria HSD`.** In every morphism of short 2-exact
sequences with identity middle component, the comparison `2-Cok(f) → 2-Ker(h)` is an
equivalence. -/
def IsPureSnake (O : B) [HasBizero O] : Prop :=
  ∀ {A Y C X Z I J : B} {a : A ⟶ Y} {b : Y ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z} {f : A ⟶ X} {h : C ⟶ Z}
    {e : X ⟶ I} {m : J ⟶ C} {j : I ⟶ J}, IsSES O a b → IsSES O c d → Nonempty (a ≅ f ≫ c) →
    Nonempty (b ≫ h ≅ d) → IsTwoCokernel O f e → IsTwoKernel O h m →
    Nonempty (e ≫ j ≫ m ≅ c ≫ b) → IsEquiv1 j

section Involution

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {K N X R C : B}

/-- **Dinversion is involutive**, first half: the normal 2-monomorphism of an antinormal pair is
a 2-kernel of the 2-cokernel that the dinverse pair uses. -/
theorem IsZeroAntinormal.isTwoKernel_of_isTwoCokernel {m : K ⟶ X} {e : X ⟶ R}
    (hme : IsZeroAntinormal O m e) {q : X ⟶ C} (hq : IsTwoCokernel O m q) :
    IsTwoKernel O q m := by
  obtain ⟨Y, ℓ, hℓ⟩ := hme.isNormalMono
  exact hℓ.of_isTwoCokernel hq

/-- **Dinversion is involutive**, second half. -/
theorem IsZeroAntinormal.isTwoCokernel_of_isTwoKernel {m : K ⟶ X} {e : X ⟶ R}
    (hme : IsZeroAntinormal O m e) {k : N ⟶ X} (hk : IsTwoKernel O e k) :
    IsTwoCokernel O k e := by
  obtain ⟨W, g, hg⟩ := hme.isNormalEpi
  exact hg.of_isTwoKernel hk

end Involution

section Ladder

open Opposite Bicategory.Opposite

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {A C X Y Z I J : B}

omit [IsStrong O] in
/-- **The identification `2-Ker(w) ≃ f` in the proof of Proposition 4.18 `Criteria HSD`.** For a
morphism of short 2-exact sequences with identity middle component, the left-hand vertical is a
2-kernel of the dinversion `w = c ≫ b`.

Only the left-hand square is used, and of the two rows only that `a` is a 2-kernel of `b` and
that `c` is a 2-monomorphism. -/
theorem isTwoKernel_dinversion_of_ladder {a : A ⟶ Y} {b : Y ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}
    {f : A ⟶ X} (hab : IsSES O a b) (hcd : IsSES O c d) (θ : a ≅ f ≫ c) :
    IsTwoKernel O (c ≫ b) f := by
  haveI := hab.isTwoKernel.isTwoMono
  haveI := hcd.isTwoKernel.isTwoMono
  haveI : IsTwoMono f := isTwoMono_of_comp θ
  refine ⟨?_, ?_, inferInstance⟩
  · exact hab.isTwoKernel.isEssNull_comp.of_iso
      (Bicategory.whiskerRightIso θ b ≪≫ eqToIso (Category.assoc f c b))
  · intro T t ht
    obtain ⟨s, ⟨γ⟩⟩ := hab.isTwoKernel.fac (t ≫ c) (ht.of_iso (eqToIso (by simp)))
    exact ⟨s, ⟨IsTwoMono.preimageIso c (eqToIso (Category.assoc s f c) ≪≫
      Bicategory.whiskerLeftIso s θ.symm ≪≫ γ)⟩⟩

omit [IsStrong O] in
/-- **The dual identification `2-Cok(w) ≃ h`.** -/
theorem isTwoCokernel_dinversion_of_ladder {a : A ⟶ Y} {b : Y ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}
    {h : C ⟶ Z} (hab : IsSES O a b) (hcd : IsSES O c d) (θ : b ≫ h ≅ d) :
    IsTwoCokernel O (c ≫ b) h :=
  isTwoCokernel_of_op
    (isTwoKernel_dinversion_of_ladder (isSES_op hcd) (isSES_op hab) θ.op2.symm)

/-- The outer 1-cells of a morphism of short 2-exact sequences with identity middle component
form an antinormal decomposition of the zero map, whose dinversion is `c ≫ b`. -/
theorem isZeroAntinormal_of_ladder {a : A ⟶ Y} {b : Y ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z} {f : A ⟶ X}
    (hab : IsSES O a b) (hcd : IsSES O c d) (θ : a ≅ f ≫ c) : IsZeroAntinormal O a d where
  isNormalMono := ⟨C, b, hab.isTwoKernel⟩
  isNormalEpi := ⟨X, c, hcd.isTwoCokernel⟩
  isEssNull_comp :=
    (hcd.isTwoKernel.isEssNull_comp.comp_left f).of_iso
      ((eqToIso (Category.assoc f c d)).symm ≪≫ (Bicategory.whiskerRightIso θ d).symm)

/-- **Proposition 4.18 `Criteria HSD`, (i) ⟹ (iii)**, which is also a proof of the Pure Snake Lemma.
No 2-z-exactness is needed: the comparison and the two 2-kernels it compares are given. -/
theorem isPureSnake_of_isHSD (hHSD : IsHSD O) : IsPureSnake O := by
  intro A Y C X Z I J a b c d f h e m j hab hcd ⟨θf⟩ ⟨θh⟩ he hm ⟨θ⟩
  have hw : IsNormal O (c ≫ b) :=
    hHSD (isZeroAntinormal_of_ladder hab hcd θf) hcd.isTwoKernel hab.isTwoCokernel
  exact (isNormal_iff_isEquiv1_comparison (isTwoKernel_dinversion_of_ladder hab hcd θf) he
    (isTwoCokernel_dinversion_of_ladder hab hcd θh) hm θ).mp hw

/-- **Proposition 4.18 `Criteria HSD`, (iii) ⟹ (i).** Every antinormal decomposition of the zero map
arises from a morphism of short 2-exact sequences with identity middle component: take the top
row `K → X → 2-Cok(m)`, the bottom row `2-Ker(e) → X → R`, and the identity of `X` in the middle.

Unlike its converse this direction does need 2-z-exactness, to form the 2-cokernel of `t` and the
2-kernel of `r`. -/
theorem isHSD_of_isPureSnake [TwoZExact O] (H : IsPureSnake O) : IsHSD O := by
  intro K X R N C m e hme k q hk hq
  have hsm : IsSES O m q := ⟨hme.isTwoKernel_of_isTwoCokernel hq, hq⟩
  have hse : IsSES O k e := ⟨hk, hme.isTwoCokernel_of_isTwoKernel hk⟩
  obtain ⟨t, ⟨γ⟩⟩ := hk.fac m hme.isEssNull_comp
  obtain ⟨r, ⟨δ⟩⟩ := hq.fac e hme.isEssNull_comp
  obtain ⟨j, ⟨θ⟩⟩ := exists_comparison (isTwoKernel_dinversion_of_ladder hsm hse γ.symm)
    (isTwoCokernel_twoCokernel O t) (isTwoCokernel_dinversion_of_ladder hsm hse δ)
    (isTwoKernel_twoKernel O r)
  have hj : IsEquiv1 j :=
    H hsm hse ⟨γ.symm⟩ ⟨δ⟩ (isTwoCokernel_twoCokernel O t) (isTwoKernel_twoKernel O r) ⟨θ⟩
  exact (isNormal_iff_isEquiv1_comparison (isTwoKernel_dinversion_of_ladder hsm hse γ.symm)
    (isTwoCokernel_twoCokernel O t) (isTwoCokernel_dinversion_of_ladder hsm hse δ)
    (isTwoKernel_twoKernel O r) θ).mpr hj

end Ladder

section PureSnake

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {A C X Y Z : B}
  {a : A ⟶ Y} {b : Y ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z} {f : A ⟶ X} {h : C ⟶ Z}

omit [IsStrong O] in
/-- **The Pure Snake Lemma**: the left-hand vertical is a normal 2-monomorphism. This needs no
hypothesis on the 2-category. -/
theorem pureSnake_isNormalMono (hab : IsSES O a b) (hcd : IsSES O c d) (θf : a ≅ f ≫ c) :
    IsNormalMono O f :=
  ⟨C, c ≫ b, isTwoKernel_dinversion_of_ladder hab hcd θf⟩

omit [IsStrong O] in
/-- **The Pure Snake Lemma**: the right-hand vertical is a normal 2-epimorphism. -/
theorem pureSnake_isNormalEpi (hab : IsSES O a b) (hcd : IsSES O c d) (θh : b ≫ h ≅ d) :
    IsNormalEpi O h :=
  ⟨X, c ≫ b, isTwoCokernel_dinversion_of_ladder hab hcd θh⟩

/-- **The Pure Snake Lemma**: the induced sequence is exact at `X`. This too is unconditional,
since `f` is itself a 2-kernel of `c ≫ b`. -/
theorem pureSnake_isExactAt_left (hab : IsSES O a b) (hcd : IsSES O c d) (θf : a ≅ f ≫ c) :
    IsExactAt O f (c ≫ b) :=
  ⟨A, 𝟙 A, f, (isEquiv1_id A).isNormalEpi, ⟨(eqToIso (Category.id_comp f)).symm⟩,
    isTwoKernel_dinversion_of_ladder hab hcd θf⟩

/-- **The Pure Snake Lemma**: the induced sequence is exact at `C`. This is where homological
self-duality is used, and it is the only place. -/
theorem pureSnake_isExactAt_right (hHSD : IsHSD O) (hab : IsSES O a b) (hcd : IsSES O c d)
    (θf : a ≅ f ≫ c) (θh : b ≫ h ≅ d) : IsExactAt O (c ≫ b) h := by
  obtain ⟨I₀, e₀, m₀, he₀, hm₀, ⟨θ₀⟩⟩ :=
    hHSD (isZeroAntinormal_of_ladder hab hcd θf) hcd.isTwoKernel hab.isTwoCokernel
  obtain ⟨W, g₀, hg₀⟩ := he₀
  obtain ⟨Z₀, ℓ₀, hℓ₀⟩ := hm₀
  haveI := hg₀.isTwoEpi
  have hqm₀ : IsTwoCokernel O m₀ h := (isTwoCokernel_isTwoEpi_comp_iff e₀).mp
    ((isTwoCokernel_dinversion_of_ladder hab hcd θh).of_iso θ₀)
  exact ⟨I₀, e₀, m₀, ⟨W, g₀, hg₀⟩, ⟨θ₀⟩, hℓ₀.of_isTwoCokernel hqm₀⟩

end PureSnake

section OppositeHSD

open Opposite Bicategory.Opposite

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O]

omit [Strict B] [IsStrong O]

/-- An antinormal decomposition of the zero map dualises to one with its two halves
exchanged. -/
theorem isZeroAntinormal_op {K X R : B} {m : K ⟶ X} {e : X ⟶ R} (h : IsZeroAntinormal O m e) :
    IsZeroAntinormal (op O) e.op m.op where
  isNormalMono := isNormalMono_op h.isNormalEpi
  isNormalEpi := isNormalEpi_op h.isNormalMono
  isEssNull_comp := isEssNull_op h.isEssNull_comp

theorem isZeroAntinormal_of_op {K X R : B} {m : K ⟶ X} {e : X ⟶ R}
    (h : IsZeroAntinormal (op O) e.op m.op) : IsZeroAntinormal O m e where
  isNormalMono := isNormalMono_of_op (by simpa using h.isNormalEpi)
  isNormalEpi := isNormalEpi_of_op (by simpa using h.isNormalMono)
  isEssNull_comp := isEssNull_of_op (by simpa using h.isEssNull_comp)

/-- **Homological self-duality is self-dual.** The dinversion of the dual antinormal pair is the
dual of the dinversion, read backwards. -/
theorem isHSD_op (h : IsHSD O) : IsHSD (op O) := by
  intro K X R N C m e hme k q hk hq
  exact isNormal_op (h (isZeroAntinormal_of_op (by simpa using hme))
    (isTwoKernel_of_op (by simpa using hq)) (isTwoCokernel_of_op (by simpa using hk)))

theorem isHSD_of_op (h : IsHSD (op O)) : IsHSD O := by
  intro K X R N C m e hme k q hk hq
  exact isNormal_of_op (h (isZeroAntinormal_op hme) (isTwoKernel_op hq) (isTwoCokernel_op hk))

theorem isHSD_op_iff : IsHSD (op O) ↔ IsHSD O :=
  ⟨isHSD_of_op, isHSD_op⟩

end OppositeHSD

section SymmetricExactness

open Opposite Bicategory.Opposite

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {K N X R C A A' A'' I J : B}
  {m : K ⟶ X} {e : X ⟶ R} {k : N ⟶ X} {q : X ⟶ C}

/-- **An antinormal pair is short 2-exact exactly when its dinversion is null**, first half.

Both directions are the same three-line chase read in the two possible orders. If `m` is a
2-kernel of `e` then `k` factors through `m`, so `k ≫ q` is null because `m ≫ q` is; if `k ≫ q` is
null then every `t` killed by `e` factors through `k`, hence is killed by `q`, hence factors
through `m` — which is a 2-kernel of `q` because it is a normal 2-monomorphism. -/
theorem IsZeroAntinormal.isTwoKernel_iff_isEssNull_dinversion (hme : IsZeroAntinormal O m e)
    (hk : IsTwoKernel O e k) (hq : IsTwoCokernel O m q) :
    IsTwoKernel O e m ↔ IsEssNull O (k ≫ q) := by
  constructor
  · intro h
    obtain ⟨u, ⟨γ⟩⟩ := h.fac k hk.isEssNull_comp
    exact (hq.isEssNull_comp.comp_left u).of_iso
      ((eqToIso (Category.assoc u m q)).symm ≪≫ Bicategory.whiskerRightIso γ q)
  · intro h
    have hm : IsTwoKernel O q m := hme.isTwoKernel_of_isTwoCokernel hq
    refine ⟨hme.isEssNull_comp, fun t ht => ?_, hm.isTwoMono⟩
    obtain ⟨u, ⟨γ⟩⟩ := hk.fac t ht
    exact hm.fac t ((h.comp_left u).of_iso
      ((eqToIso (Category.assoc u k q)).symm ≪≫ Bicategory.whiskerRightIso γ q))

/-- The second half, obtained by transport: the dinversion of the dual antinormal pair is the
dual of the dinversion, so the criterion is literally self-dual. -/
theorem IsZeroAntinormal.isTwoCokernel_iff_isEssNull_dinversion (hme : IsZeroAntinormal O m e)
    (hk : IsTwoKernel O e k) (hq : IsTwoCokernel O m q) :
    IsTwoCokernel O m e ↔ IsEssNull O (k ≫ q) := by
  have H := (isZeroAntinormal_op hme).isTwoKernel_iff_isEssNull_dinversion
    (isTwoKernel_op hq) (isTwoCokernel_op hk)
  have hnull : IsEssNull (Opposite.op O) (q.op ≫ k.op) ↔ IsEssNull O (k ≫ q) :=
    isEssNull_op_iff (k ≫ q)
  exact isTwoKernel_op_iff.symm.trans (H.trans hnull)

/-- **An antinormal pair is short 2-exact exactly when its dinversion is null**, Proposition 4.8
`P:NullDinversion`. This is the one formulation of exactness that is visibly symmetric: the
dinversion `k ≫ q` is the 1-cell `2-Ker(e) → 2-Cok(m)` that homological self-duality is a statement
about, and dualising the configuration replaces it by its own opposite. -/
theorem IsZeroAntinormal.isSES_iff_isEssNull_dinversion (hme : IsZeroAntinormal O m e)
    (hk : IsTwoKernel O e k) (hq : IsTwoCokernel O m q) :
    IsSES O m e ↔ IsEssNull O (k ≫ q) :=
  ⟨fun h => (hme.isTwoKernel_iff_isEssNull_dinversion hk hq).mp h.isTwoKernel,
    fun h => ⟨(hme.isTwoKernel_iff_isEssNull_dinversion hk hq).mpr h,
      (hme.isTwoCokernel_iff_isEssNull_dinversion hk hq).mpr h⟩⟩

/-- **Corollary 4.9 `Cor Exact Null Dinversion`**, a fourth condition for Proposition 4.4
`Exactness Self-Dual`: a pair `(f, g)` of composable normal 1-cells with null composite is exact
exactly when the dinversion `2-ker(2-coim(g)) ≫ 2-cok(2-img(f)) : 2-Ker(g) ⟶ 2-Cok(f)` of its
antinormal pair `(2-img(f), 2-coim(g))` is null.

Conditions (i) and (ii) of the proposition are exchanged by duality; this one is fixed by it. It
also locates exactness inside Section 4: homological self-duality asks the dinversion of an
antinormal pair to be *normal*, exactness asks it to be *null*, and a null 1-cell is normal by
Proposition 4.13 `P:NullNormal`. So exactness at a spot is the degenerate case of the condition,
and homological self-duality is the genuine strengthening — not a hypothesis the symmetry
needs. -/
theorem isExactAt_iff_isEssNull_dinversion {f : A ⟶ A'} {g : A' ⟶ A''} {ef : A ⟶ I} {mf : I ⟶ A'}
    (θf : f ≅ ef ≫ mf) (hef : IsNormalEpi O ef) (hmf : IsNormalMono O mf) {eg : A' ⟶ J}
    {mg : J ⟶ A''} (θg : g ≅ eg ≫ mg) (heg : IsNormalEpi O eg) (hmg : IsNormalMono O mg)
    (hfg : IsEssNull O (f ≫ g)) {k' : N ⟶ A'} (hk : IsTwoKernel O eg k') {q' : A' ⟶ C}
    (hq : IsTwoCokernel O mf q') : IsExactAt O f g ↔ IsEssNull O (k' ≫ q') := by
  haveI := hef.isTwoEpi
  haveI := hmg.isTwoMono
  have hme : IsZeroAntinormal O mf eg :=
    ⟨hmf, heg, IsEssNull.of_comp_isTwoMono mg (IsEssNull.of_comp_isTwoEpi ef (hfg.of_iso
      (Bicategory.whiskerRightIso θf g ≪≫ Bicategory.whiskerLeftIso (ef ≫ mf) θg ≪≫
        eqToIso (by simp))))⟩
  have hses : IsTwoKernel O g mf ↔ IsSES O mf eg := (exactness_tfae θf hef hmf θg heg hmg).out 0 2
  rw [isExactAt_iff_of_isNormal θf hef hmf θg heg hmg, hses,
    hme.isSES_iff_isEssNull_dinversion hk hq]

end SymmetricExactness

end SnakeLean
