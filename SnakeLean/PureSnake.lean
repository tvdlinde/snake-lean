/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.DiExact

/-!
# The Pure Snake Lemma with its comparison as data

Lemma 4.27, the `Pure Snake Lemma`, names its comparison: the 1-cell
`j : 2-Cok(f) → 2-Ker(h)` characterised by `2-ker(h) ∘ j ∘ 2-coker(f) ≅ b ∘ c` is an equivalence,
unique up to a unique invertible 2-cell with that property. `IsPureSnake` in
`SnakeLean.Dinversion` records the equivalence half — it takes a comparison `j` as an input and
concludes `IsEquiv1 j` — which is all Section 4 consumes.

Section 6 needs the rest. The connecting 1-cell of the Snake Lemma is *defined* as a composite of
three such comparisons, so they have to be nameable, and Section 7 proves them 2-natural, which is
not a statement one can make about an equivalence that has no name. This module is the
comparison as data, with the uniqueness clause.

## What the paper says

The Pure Snake Lemma's "in particular" clause reads: *the comparison
`j : 2-Cok(f) → 2-Ker(h)`, characterised by `2-coker(f) ≫ j ≫ 2-ker(h) ≅ c ∘ b`, is an
equivalence, and is unique up to a unique invertible 2-cell with that property.* The uniqueness
half is `PureSnakeComparison.nonempty_iso`, and it is what makes the naturality of Section 7
statable at all: a morphism of pure configurations sends one comparison to another comparison over
the transported data, so the two agree up to the unique 2-cell.

Nothing here is new mathematics — `exists_comparison` and `comparison_unique` already do the work
in `SnakeLean.Comparison`. What is new is that the two are packaged with `IsPureSnake` into a
single object that can be composed and compared.

## Orientation

The pure configuration is a morphism of short 2-exact sequences whose middle component is an
identity: two rows `A →a Y →b C` and `X →c Y →d Z` through the *same* object `Y`, with verticals
`f : A ⟶ X` and `h : C ⟶ Z`. Its dinversion is `c ≫ b : X ⟶ C`, which is the paper's `b ∘ c`, and
the content of the lemma is that this dinversion is normal with 2-coimage `e = 2-coker(f)` and
2-image `m = 2-ker(h)`.

## Main definitions

* `PureSnakeComparison` — the comparison 1-cell, its characterising 2-cell, and the proof that it
  is an equivalence.

## Main results

* `pureSnakeComparison` — the comparison exists, given homological self-duality.
* `PureSnakeComparison.nonempty_iso` — it is unique up to invertible 2-cell.
* `PureSnakeComparison.isNormal_dinversion` — the dinversion is normal, which is the Pure Snake
  Lemma's assertion of 2-exactness at the middle.
* `pureSnakeComparison'` — the same at the chosen 2-kernel and 2-cokernel.

## Not formalised

Nothing from this layer. Naturality of the comparison in a morphism of pure configurations is in
`SnakeLean.Naturality`, which formalises Definition 7.3 `Def:MorphismPure` and builds on
`PureSnakeComparison.nonempty_iso`.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- **The comparison of the Pure Snake Lemma, as data.** For a pure configuration with rows
`A →a Y →b C` and `X →c Y →d Z`, verticals `f` and `h`, a 2-cokernel `e` of `f` and a 2-kernel `m`
of `h`, this is the comparison `j : I ⟶ J` factoring the dinversion `c ≫ b`, together with the
factorisation 2-cell and the proof that `j` is an equivalence.

This is the `j` of Lemma 4.27, as a structure. -/
structure PureSnakeComparison (O : B) [HasBizero O] {C X Y I J : B} (c : X ⟶ Y) (b : Y ⟶ C)
    (e : X ⟶ I) (m : J ⟶ C) where
  /-- The comparison 1-cell. -/
  j : I ⟶ J
  /-- The 2-cell exhibiting `j` as the comparison: `e ≫ j ≫ m` is the dinversion. -/
  θ : e ≫ j ≫ m ≅ c ≫ b
  /-- The content of the Pure Snake Lemma: the comparison is an equivalence. -/
  isEquiv1 : IsEquiv1 j

section Construction

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {A C X Y Z I J : B}
  {a : A ⟶ Y} {b : Y ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z} {f : A ⟶ X} {h : C ⟶ Z} {e : X ⟶ I} {m : J ⟶ C}

/-- **The Pure Snake Lemma.** In a homologically self-dual 2-category, a pure configuration has a
comparison, and it is an equivalence.

This is `exists_comparison` for the existence and `isPureSnake_of_isHSD` for the equivalence,
packaged so that the resulting 1-cell can be composed. -/
noncomputable def pureSnakeComparison (hHSD : IsHSD O) (hab : IsSES O a b) (hcd : IsSES O c d)
    (θf : a ≅ f ≫ c) (θh : b ≫ h ≅ d) (he : IsTwoCokernel O f e) (hm : IsTwoKernel O h m) :
    PureSnakeComparison O c b e m :=
  let H := exists_comparison (isTwoKernel_dinversion_of_ladder hab hcd θf) he
    (isTwoCokernel_dinversion_of_ladder hab hcd θh) hm
  { j := H.choose
    θ := H.choose_spec.some
    isEquiv1 := isPureSnake_of_isHSD hHSD hab hcd ⟨θf⟩ ⟨θh⟩ he hm ⟨H.choose_spec.some⟩ }

/-- The comparison at the chosen 2-cokernel of `f` and the chosen 2-kernel of `h`. -/
noncomputable def pureSnakeComparison' (hHSD : IsHSD O) [HasTwoCokernel O f] [HasTwoKernel O h]
    (hab : IsSES O a b) (hcd : IsSES O c d) (θf : a ≅ f ≫ c) (θh : b ≫ h ≅ d) :
    PureSnakeComparison O c b (twoCokernel O f) (twoKernel O h) :=
  pureSnakeComparison hHSD hab hcd θf θh (isTwoCokernel_twoCokernel O f) (isTwoKernel_twoKernel O h)

end Construction

section Uniqueness

variable {O : B} [HasBizero O] {C X Y I J : B} {c : X ⟶ Y} {b : Y ⟶ C} {e : X ⟶ I} {m : J ⟶ C}

/-- **The comparison is unique up to an invertible 2-cell.** Any two 1-cells filling the same
triangle agree, because `e` is a 2-epimorphism and `m` a 2-monomorphism.

This is the uniqueness clause of Lemma 4.27, and the property Section 7 relies on when it calls
the connecting comparison "natural". -/
theorem PureSnakeComparison.nonempty_iso [IsTwoEpi e] [IsTwoMono m]
    (P P' : PureSnakeComparison O c b e m) : Nonempty (P.j ≅ P'.j) :=
  comparison_unique P.θ P'.θ

end Uniqueness

section Dinversion

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {K C Q X Y I J : B}
  {c : X ⟶ Y} {b : Y ⟶ C} {e : X ⟶ I} {m : J ⟶ C}

/-- **The dinversion is normal**, with 2-coimage `e` and 2-image `m`. This is the Pure Snake
Lemma's assertion of 2-exactness at the middle position of the induced sequence, in the form
`Exactness via Homology` uses it. -/
theorem PureSnakeComparison.isNormal_dinversion (P : PureSnakeComparison O c b e m) {k : K ⟶ X}
    (hk : IsTwoKernel O (c ≫ b) k) (he : IsTwoCokernel O k e) {q : C ⟶ Q}
    (hq : IsTwoCokernel O (c ≫ b) q) (hm : IsTwoKernel O q m) : IsNormal O (c ≫ b) :=
  (isNormal_iff_isEquiv1_comparison hk he hq hm P.θ).mpr P.isEquiv1

end Dinversion

end SnakeLean
