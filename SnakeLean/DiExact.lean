/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.ThirdIso

/-!
# 2-di-exactness

This module formalises Definition 6.2 `Def:DiExact`, the standing hypothesis of Section 6, and
connects it to the hypothesis Section 6 actually uses.

## The bridge

Section 6 works in a 2-di-exact 2-category and invokes the Pure Snake Lemma five times. The Pure
Snake Lemma is stated for a *homologically self-dual* 2-category; the bridge between Definition
4.17 `Def:HSD` and Definition 6.2 `Def:DiExact` is Proposition 6.3 `P:DiExactHSD`, and
`isHSD_of_twoDiExact` is it.

The proof is the paper's, and not the one the shape of the definitions suggests. Specialising
(DI2) to a null composite would only give that a null 1-cell is normal, which is
`isNormal_of_isEssNull` and not homological self-duality. What works instead is that the
*dinversion* of an antinormal pair is itself an antinormal composite: `2-ker(e)` is a normal
2-monomorphism and `2-cok(m)` a normal 2-epimorphism, so (DI2) applies to `2-ker(e) ≫ 2-cok(m)`
directly.

**Nullity is never used.** The hypothesis `IsZeroAntinormal O m e` of `IsHSD` asks that `m ≫ e`
be null; the proof discards it, as Remark 6.4 `Rem Bridge Cost` says and the linter confirms. So
2-di-exactness gives the stronger statement that the dinversion of *every* antinormal pair is
normal, which is exactly condition (DPN), Definition 9.2 `Def:DPN`, the weaker replacement for
di-exactness that Section 9 runs on. `P:DiExactHSD` states the proposition in that stronger form,
and it is the first implication of Proposition 9.3 `P:DPNPlace`.

## Separated from 2-z-exactness

Definition 6.2 bundles (DI1) — all 2-kernels and all 2-cokernels — with (DI2). Here
(DI1) stays `TwoZExact` and only (DI2) is `TwoDiExact`, for the reason `IsStrong` is kept apart
from `HasBizero` throughout: the linter then reports which of the two each result consumes. As
Remark 6.4 says, `isHSD_of_twoDiExact` needs neither 2-z-exactness nor a *strong* bizero object.

## Non-vacuity

No model is exhibited here. The paper's 2-di-exact models are Example 6.5 `Ex DiExact`,
formalised in `SnakeLean.LocallyDiscreteModel`; Theorem 8.17 `T:SatModel`, whose 2-category is
built in `SnakeLean.AbCatModel` but whose (DI2) is behind the Serre-quotient bridge (see there);
and Theorem 8.37 `T:LatticeModel`, in `SnakeLean.LatticeModel`. Theorem 9.32 `T:HilbertModel` is
a model of Section 9's hypotheses and is *not* 2-di-exact. The 2-category of all abelian
categories and exact functors is not 2-di-exact either — Proposition 8.12 `P:AbCatFails`, whose
module-theoretic content is `SnakeLean.SerreJoin` — and the ingredient its 2-categorical reading
needs, that the Serre quotient of an abelian category is abelian, is listed as future work in
Mathlib (`Mathlib/CategoryTheory/Abelian/SerreClass/Basic.lean`, which has Serre classes and
`monoModSerre`/`epiModSerre`/`isoModSerre` but not the quotient).

## Main definitions

* `TwoDiExact` — condition (DI2), every antinormal 1-cell is normal.

## Main results

* `isAntinormal_comp` — a normal 2-monomorphism followed by a normal 2-epimorphism is antinormal.
* `isNormal_of_normalMono_comp_normalEpi` — the antinormal composite is normal, which is (DI2)
  in the form Section 6 uses it.
* `isHSD_of_twoDiExact` — 2-di-exactness implies homological self-duality.
* `isPureSnake_of_twoDiExact`, `isHomologySelfDual_of_twoDiExact`, `isThirdIso_of_twoDiExact`,
  `isThirdIsoDual_of_twoDiExact` — the four equivalents of `IsHSD`, now available under the
  standing hypothesis of Section 6.

## Not formalised

Condition (DI1), which is `TwoZExact` in `SnakeLean.ZExact`. Condition (DPN) itself is
`SnakeLean.NonSelfDual`, and the Snake Lemma it supports — Theorem 9.19 `T:SnakeNonSelfDual` — is
`SnakeLean.NSDConnecting`.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- **Condition (DI2) of Definition 6.2 `Def:DiExact`.** Every 1-cell that factors as a
normal 2-monomorphism followed by a normal 2-epimorphism also factors as a normal
2-epimorphism followed by a normal 2-monomorphism.

The paper phrases this as "every morphism that factorises, up to an invertible 2-cell, as a 2-kernel
followed by a 2-cokernel also factorises, up to an invertible 2-cell, as a 2-cokernel followed by a
2-kernel", which is `IsAntinormal O f → IsNormal O f`. Condition (DI1) is kept separate, as
`TwoZExact`. -/
class TwoDiExact (O : B) [HasBizero O] : Prop where
  /-- Every antinormal 1-cell is normal. -/
  isNormal_of_isAntinormal {A A' : B} {f : A ⟶ A'} : IsAntinormal O f → IsNormal O f

section Antinormal

variable {O : B} [HasBizero O] {K X R : B} {m : K ⟶ X} {e : X ⟶ R}

/-- A normal 2-monomorphism followed by a normal 2-epimorphism is an antinormal 1-cell. This is
the definition of an antinormal pair in `Def:Dinversion` read as a statement about the
composite. -/
theorem isAntinormal_comp (hm : IsNormalMono O m) (he : IsNormalEpi O e) :
    IsAntinormal O (m ≫ e) :=
  ⟨X, m, e, hm, he, ⟨Iso.refl _⟩⟩

/-- **(DI2) in the form Section 6 uses it**: the antinormal composite of a normal
2-monomorphism and a normal 2-epimorphism is a normal 1-cell, hence has a normal image
factorisation. -/
theorem isNormal_of_normalMono_comp_normalEpi [TwoDiExact O] (hm : IsNormalMono O m)
    (he : IsNormalEpi O e) : IsNormal O (m ≫ e) :=
  TwoDiExact.isNormal_of_isAntinormal (isAntinormal_comp hm he)

end Antinormal

section Bridge

variable {O : B} [HasBizero O]

/-- **2-di-exactness implies homological self-duality**, which is Proposition 6.3
`P:DiExactHSD`. Section 6 depends on it: its proofs invoke the Pure Snake Lemma, whose hypothesis
is Definition 4.17 `Def:HSD`.

The dinversion `k ≫ q` of an antinormal pair `(m, e)` is a 2-kernel followed by a 2-cokernel,
hence antinormal, hence normal by (DI2). The nullity of `m ≫ e` plays no part, so the same
argument gives the stronger conclusion that the dinversion of *every* antinormal pair is
normal. -/
theorem isHSD_of_twoDiExact [TwoDiExact O] : IsHSD O := by
  intro K X R N C m e _hme k q hk hq
  exact isNormal_of_normalMono_comp_normalEpi ⟨R, e, hk⟩ ⟨K, m, hq⟩

end Bridge

section Consequences

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] [TwoDiExact O]

/-- The Pure Snake Lemma is available in a 2-di-exact 2-category. -/
theorem isPureSnake_of_twoDiExact : IsPureSnake O :=
  isPureSnake_of_isHSD isHSD_of_twoDiExact

/-- Homology is self-dual in a 2-di-exact 2-category, by Proposition 4.18 `Criteria HSD`
(i) ⟹ (ii). -/
theorem isHomologySelfDual_of_twoDiExact : IsHomologySelfDual O :=
  isHomologySelfDual_of_isHSD isHSD_of_twoDiExact

/-- The Third Isomorphism Property holds in a 2-di-exact 2-category. -/
theorem isThirdIso_of_twoDiExact : IsThirdIso O :=
  isThirdIso_of_isHSD isHSD_of_twoDiExact

/-- The dual Third Isomorphism Property holds in a 2-di-exact 2-category. -/
theorem isThirdIsoDual_of_twoDiExact : IsThirdIsoDual O :=
  isThirdIsoDual_of_isHSD isHSD_of_twoDiExact

end Consequences

section Opposite

open Opposite Bicategory.Opposite

variable {O : B} [HasBizero O]

/-- 2-di-exactness is self-dual. -/
instance twoDiExactOp [TwoDiExact O] : TwoDiExact (op O) where
  isNormal_of_isAntinormal {A A' f} h :=
    isNormal_op (TwoDiExact.isNormal_of_isAntinormal (isAntinormal_of_op (by simpa using h)))

end Opposite

end SnakeLean
