/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.Homology

/-!
# The Third Isomorphism Property

This module formalises Definition 4.21 `Def:TotallyNormal` and Proposition 4.22 `Third Iso`: for
a 2-z-exact 2-category, homological self-duality is equivalent to short 2-exactness of the
sequence comparing successive quotients of a tower of normal 2-monomorphisms, and dually to the
sequence comparing successive subobjects of a tower of normal 2-epimorphisms.

## The converse, (ii) ⟹ (i)

The paper's proof takes an antinormal decomposition `(m, e)` of the zero map, corestricts `m` to
`t : K → 2-Ker(e)`, which is a normal 2-monomorphism by Proposition 3.6 `Composites of Normal
Monos`(ii) — the 2-monomorphism `2-ker(e)` cancelling off the normal 2-monomorphism `m` — and
applies (ii) to the totally normal sequence `K → 2-Ker(e) → X`. That returns a short 2-exact
sequence whose 2-monomorphism part is `c'`, with `2-cok(t) ≫ c' ≅ w` by construction. A
2-cokernel followed by a 2-kernel *is* a normal image factorisation, so `w` is normal. The proof
here is that one; as the paper notes after it, nothing about `2-ker(w)` is ever needed.

## Hypotheses

(i) ⟹ (ii) and (i) ⟹ (iii) use no 2-z-exactness: the normal image factorisation that homological
self-duality provides already supplies the 2-kernel the conclusion needs. The two converses do
need it, to form one further 2-cokernel or 2-kernel — the same asymmetry as in
`SnakeLean.Dinversion` and `SnakeLean.Homology`.

## Main results

* `IsTotallyNormalMono`, `IsTotallyNormalEpi` — Definition 4.21 `Def:TotallyNormal`.
* `IsThirdIso`, `IsThirdIsoDual` — conditions (ii) and (iii).
* `isThirdIso_of_isHSD`, `isHSD_of_isThirdIso` and their duals — Proposition 4.22 `Third Iso`.

## Duality

Condition (iii) is condition (ii) read in `Bᵒᵖ`: `isThirdIsoDual_iff_isThirdIso_op` translates
one into the other, and both dual halves of Proposition 4.22 `Third Iso` are then one-line
consequences of their primal halves. This is where the transport of `SnakeLean.Op` pays best,
since the two directions of the paper's proof are the longest arguments in Section 4.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- **Definition 4.21 `Def:TotallyNormal`.** A sequence of 2-monomorphisms is **totally normal**
when both 1-cells and their composite are normal 2-monomorphisms. -/
structure IsTotallyNormalMono (O : B) [HasBizero O] {A X Y : B} (a : A ⟶ X) (c : X ⟶ Y)
    (b : A ⟶ Y) : Prop where
  /-- `b` is the composite. -/
  comp : Nonempty (b ≅ a ≫ c)
  /-- The first 1-cell is a normal 2-monomorphism. -/
  left : IsNormalMono O a
  /-- The second 1-cell is a normal 2-monomorphism. -/
  right : IsNormalMono O c
  /-- The composite is a normal 2-monomorphism. -/
  total : IsNormalMono O b

/-- The dual of `IsTotallyNormalMono`. -/
structure IsTotallyNormalEpi (O : B) [HasBizero O] {X Y Z : B} (p : X ⟶ Y) (q : Y ⟶ Z)
    (pq : X ⟶ Z) : Prop where
  /-- `pq` is the composite. -/
  comp : Nonempty (pq ≅ p ≫ q)
  /-- The first 1-cell is a normal 2-epimorphism. -/
  left : IsNormalEpi O p
  /-- The second 1-cell is a normal 2-epimorphism. -/
  right : IsNormalEpi O q
  /-- The composite is a normal 2-epimorphism. -/
  total : IsNormalEpi O pq

/-- **Condition (ii) of Proposition 4.22 `Third Iso`.** For every totally normal sequence of
2-monomorphisms `A → X → Y`, the induced sequence `2-Cok(a) → 2-Cok(c ∘ a) → 2-Cok(c)` is short
2-exact. -/
def IsThirdIso (O : B) [HasBizero O] : Prop :=
  ∀ {A X Y Qa Qb Qc : B} {a : A ⟶ X} {c : X ⟶ Y} {b : A ⟶ Y}, IsTotallyNormalMono O a c b →
    ∀ {qa : X ⟶ Qa} {qb : Y ⟶ Qb} {qc : Y ⟶ Qc}, IsTwoCokernel O a qa → IsTwoCokernel O b qb →
    IsTwoCokernel O c qc → ∀ {c' : Qa ⟶ Qb} {r : Qb ⟶ Qc}, Nonempty (qa ≫ c' ≅ c ≫ qb) →
    Nonempty (qb ≫ r ≅ qc) → IsSES O c' r

/-- **Condition (iii) of Proposition 4.22 `Third Iso`.** For every totally normal sequence of
2-epimorphisms `X → Y → Z`, the induced sequence `2-Ker(p) → 2-Ker(q ∘ p) → 2-Ker(q)` is short
2-exact. -/
def IsThirdIsoDual (O : B) [HasBizero O] : Prop :=
  ∀ {X Y Z Kp Kq Kpq : B} {p : X ⟶ Y} {q : Y ⟶ Z} {pq : X ⟶ Z}, IsTotallyNormalEpi O p q pq →
    ∀ {kp : Kp ⟶ X} {kq : Kq ⟶ Y} {kpq : Kpq ⟶ X}, IsTwoKernel O p kp → IsTwoKernel O q kq →
    IsTwoKernel O pq kpq → ∀ {i : Kp ⟶ Kpq} {p' : Kpq ⟶ Kq}, Nonempty (i ≫ kpq ≅ kp) →
    Nonempty (p' ≫ kq ≅ kpq ≫ p) → IsSES O i p'

section Mono

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O]

/-- **Proposition 4.22 `Third Iso`, (i) ⟹ (ii).** -/
theorem isThirdIso_of_isHSD (hHSD : IsHSD O) : IsThirdIso O := by
  intro A X Y Qa Qb Qc a c b htn qa qb qc hqa hqb hqc c' r ⟨θc⟩ ⟨θr⟩
  obtain ⟨θb⟩ := htn.comp
  obtain ⟨Wb, ℓb, hℓb⟩ := htn.total
  obtain ⟨Wc, ℓc, hℓc⟩ := htn.right
  have hsb : IsSES O b qb := isSES_of_isTwoKernel hℓb hqb
  have hsc : IsSES O c qc := isSES_of_isTwoKernel hℓc hqc
  have hwa : IsTwoKernel O (c ≫ qb) a := isTwoKernel_dinversion_of_ladder hsb hsc θb
  have hwr : IsTwoCokernel O (c ≫ qb) r := isTwoCokernel_dinversion_of_ladder hsb hsc θr
  obtain ⟨I₀, e₀, m₀, he₀, hm₀, ⟨θ₀⟩⟩ :=
    hHSD (isZeroAntinormal_of_ladder hsb hsc θb) hsc.isTwoKernel hsb.isTwoCokernel
  obtain ⟨W₁, g₁, hg₁⟩ := he₀
  obtain ⟨W₂, ℓ₂, hℓ₂⟩ := hm₀
  haveI := hg₁.isTwoEpi
  haveI := hℓ₂.isTwoMono
  haveI := hqa.isTwoEpi
  -- `2-coim(w)` and `2-cok(a)` are 2-cokernels of the same 1-cell, so they agree up to `u`.
  have hae₀ : IsTwoKernel O e₀ a := (isTwoKernel_comp_isTwoMono_iff m₀).mp (hwa.of_iso θ₀)
  obtain ⟨u, hu, ⟨δ⟩⟩ := hqa.exists_isEquiv1 (hg₁.of_isTwoKernel hae₀)
  -- `2-img(w)` is a 2-kernel of `r`.
  have hm₀r : IsTwoKernel O r m₀ :=
    hℓ₂.of_isTwoCokernel ((isTwoCokernel_isTwoEpi_comp_iff e₀).mp (hwr.of_iso θ₀))
  have hc' : c' ≅ u ≫ m₀ := IsTwoEpi.preimageIso qa
    (θc ≪≫ θ₀ ≪≫ (Bicategory.whiskerRightIso δ m₀).symm ≪≫ eqToIso (Category.assoc qa u m₀))
  have hkc' : IsTwoKernel O r c' := (hm₀r.isEquiv1_comp hu).of_iso_right hc'.symm
  exact ⟨hkc', hwr.of_isTwoKernel hkc'⟩

/-- **Proposition 4.22 `Third Iso`, (ii) ⟹ (i).** Every antinormal decomposition `(m, e)` of the
zero map arises from the totally normal sequence `K → 2-Ker(e) → X`. The corestriction `t` of `m` is
a normal 2-monomorphism by Proposition 3.6 `Composites of Normal Monos`(ii), and the sequence
returned by (ii) exhibits `w` as a 2-cokernel followed by a 2-kernel, as in the paper. -/
theorem isHSD_of_isThirdIso [TwoZExact O] (H : IsThirdIso O) : IsHSD O := by
  intro K X R N C m e hme k q hk hq
  haveI := hk.isTwoMono
  haveI := hq.isTwoEpi
  obtain ⟨t, ⟨γ⟩⟩ := hk.fac m hme.isEssNull_comp
  have hseq : IsTotallyNormalMono O t k m :=
    ⟨⟨γ.symm⟩, IsNormalMono.of_comp γ.symm hme.isNormalMono, ⟨R, e, hk⟩, hme.isNormalMono⟩
  have h₁ : IsEssNull O (t ≫ k ≫ q) := hq.isEssNull_comp.of_iso
    ((Bicategory.whiskerRightIso γ q).symm ≪≫ eqToIso (Category.assoc t k q))
  obtain ⟨c', ⟨θc⟩⟩ := (isTwoCokernel_twoCokernel O t).fac (k ≫ q) h₁
  have h₂ : IsEssNull O (m ≫ twoCokernel O k) :=
    ((isTwoCokernel_twoCokernel O k).isEssNull_comp.comp_left t).of_iso
      ((eqToIso (Category.assoc t k (twoCokernel O k))).symm ≪≫
        Bicategory.whiskerRightIso γ (twoCokernel O k))
  obtain ⟨r, ⟨θr⟩⟩ := hq.fac (twoCokernel O k) h₂
  have hses : IsSES O c' r :=
    H hseq (isTwoCokernel_twoCokernel O t) hq (isTwoCokernel_twoCokernel O k) ⟨θc⟩ ⟨θr⟩
  exact ⟨_, twoCokernel O t, c', isNormalEpi_twoCokernel O t, ⟨_, r, hses.isTwoKernel⟩,
    ⟨θc.symm⟩⟩

end Mono

section Epi

open Opposite Bicategory.Opposite

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O]

omit [Strict B] [IsStrong O] in
/-- **Condition (iii) is condition (ii) read in `Bᵒᵖ`.** A totally normal sequence of
2-epimorphisms dualises to a totally normal sequence of 2-monomorphisms with its two 1-cells
exchanged, and the induced sequence of 2-kernels to the induced sequence of 2-cokernels. -/
theorem isThirdIsoDual_of_isThirdIso_op (H : IsThirdIso (op O)) : IsThirdIsoDual O := by
  intro X Y Z Kp Kq Kpq p q pq htn kp kq kpq hkp hkq hkpq i p' ⟨θi⟩ ⟨θp⟩
  refine isSES_of_op (H (a := q.op) (c := p.op) (b := pq.op) ?_ (isTwoCokernel_op hkq)
    (isTwoCokernel_op hkpq) (isTwoCokernel_op hkp) ⟨θp.op2⟩ ⟨θi.op2⟩)
  exact { comp := ⟨htn.comp.some.op2⟩
          left := isNormalMono_op htn.right
          right := isNormalMono_op htn.left
          total := isNormalMono_op htn.total }

omit [Strict B] [IsStrong O] in
/-- The converse translation, which reads an arbitrary totally normal sequence of
2-monomorphisms of `Bᵒᵖ` back in `B`. -/
theorem isThirdIso_op_of_isThirdIsoDual (H : IsThirdIsoDual O) : IsThirdIso (op O) := by
  intro A X Y Qa Qb Qc a c b htn qa qb qc hqa hqb hqc c' r ⟨θc⟩ ⟨θr⟩
  refine isSES_op (H (p := c.unop) (q := a.unop) (pq := b.unop) ?_ (isTwoKernel_of_op hqc)
    (isTwoKernel_of_op hqa) (isTwoKernel_of_op hqb) ⟨θr.unop2⟩ ⟨θc.unop2⟩)
  exact { comp := ⟨htn.comp.some.unop2⟩
          left := isNormalEpi_of_op htn.right
          right := isNormalEpi_of_op htn.left
          total := isNormalEpi_of_op htn.total }

omit [Strict B] [IsStrong O] in
theorem isThirdIsoDual_iff_isThirdIso_op : IsThirdIsoDual O ↔ IsThirdIso (op O) :=
  ⟨isThirdIso_op_of_isThirdIsoDual, isThirdIsoDual_of_isThirdIso_op⟩

/-- **Proposition 4.22 `Third Iso`, (i) ⟹ (iii)**, as (i) ⟹ (ii) read in `Bᵒᵖ`. -/
theorem isThirdIsoDual_of_isHSD (hHSD : IsHSD O) : IsThirdIsoDual O :=
  isThirdIsoDual_of_isThirdIso_op (isThirdIso_of_isHSD (isHSD_op hHSD))

/-- **Proposition 4.22 `Third Iso`, (iii) ⟹ (i)**, as (ii) ⟹ (i) read in `Bᵒᵖ`. -/
theorem isHSD_of_isThirdIsoDual [TwoZExact O] (H : IsThirdIsoDual O) : IsHSD O :=
  isHSD_of_op (isHSD_of_isThirdIso (isThirdIso_op_of_isThirdIsoDual H))

end Epi

end SnakeLean
