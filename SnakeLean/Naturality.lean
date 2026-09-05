/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.SnakeDelta

/-!
# 2-naturality of the Pure Snake comparison

This module formalises Section 7: a notion of morphism between pure configurations, Definition
7.3 `Def:MorphismPure`, and the proof that the comparison of the Pure Snake Lemma is 2-natural in
it. `SnakeLean.PureSnake` and `SnakeLean.SnakeDelta` both point here for it.

## The definition needs no extra data

A pure configuration is a morphism of short 2-exact sequences whose middle component is an
identity. A **morphism of pure configurations** is, correspondingly, a pair of morphisms of short
2-exact sequences — one between the two top rows, one between the two bottom rows — sharing their
middle component `πY`. That is all: `MorphismPure` carries five 1-cells and four invertible
2-cells, and no axiom.

In particular it imposes nothing on the verticals `f` and `h`. It does not have to:
`MorphismPure.exists_piF` produces the comparison `πf : f ≫ πX ≅ πA ≫ f'` by reflecting a pasted
2-cell along the 2-monomorphism `c'`, and `MorphismPure.exists_piH` produces `πh` by coreflecting
along the 2-epimorphism `b`. Both reflections are unique, so the two comparisons are determined by
the data already present.

## What the naturality proof uses

`natural_comparison` is `comparison_unique` in disguise. Both `πf ≫ j'` and `j ≫ πh` become the
1-cell `c ≫ b ≫ πC` after whiskering by the 2-epimorphism `e = 2-coker(f)` on the left and the
2-monomorphism `m' = 2-ker(h')` on the right, so the two agree, uniquely. Homological
self-duality enters only through the existence of `j` and `j'`; that they are equivalences plays
no part, and neither does the 2-di-exactness that the Snake Lemma needs to produce them.

## Naturality of the rest of the snake sequence

The four squares of Theorem 7.10 `T:NaturalSnake` that do not involve `∂` need none of this. They
are `nonempty_iso_kerMap_square` and its dual: a cube whose four side faces commute up to invertible
2-cells and whose bottom face is a square between 2-kernels has a commuting top face, because the
2-kernel it lands in is a 2-monomorphism. `nonempty_iso_connecting_square` then pastes the three
squares that make up `∂ = 2-ker(c̲) ∘ z ∘ 2-coker(b̄)` — with `nonempty_iso_inv_square` supplying
the middle one for the inverted comparison `z₂⁻¹`.

## Main definitions

* `MorphismPure` — Definition 7.3 `Def:MorphismPure`, a morphism of pure configurations.
* `MorphismPure.op` — its dual; the two rows are exchanged and the morphism reverses.

## Main results

* `MorphismPure.exists_piF`, `MorphismPure.exists_piH` — Lemma 7.4 `L:InducedVerticals`: the
  comparisons on the verticals are induced, not imposed.
* `MorphismPure.exists_cokMapF`, `MorphismPure.exists_kerMapH` — the 1-cells induced on
  `2-Cok(f)` and on `2-Ker(h)`.
* `naturalComparisonIso`, `natural_comparison` — Theorem 7.6 `T:NaturalComparison`: the Pure
  Snake comparison is 2-natural.
* `natural_comparison_whisker` — its compatibility clause: whiskered by `2-coker(f)` and
  `2-ker(h')`, the 2-cell is the composite of the two characterising pastings.
* `natural_comparison_unique` — and the 2-natural comparison is unique.
* `nonempty_iso_kerMap_square`, `nonempty_iso_cokMap_square` — the four squares of Theorem 7.10
  `T:NaturalSnake` that avoid `∂`.
* `exists_normalImageMap` — the comparison induced on normal images by a square, which is what a
  morphism of ladders supplies on the object `I` of the construction.
* `nonempty_iso_inv_square`, `nonempty_iso_connecting_square`,
  `nonempty_iso_snakeComparison_square`, `nonempty_iso_connecting_snake` — the pasting that turns
  naturality of the three Pure Snake comparisons into naturality of `∂`.

## Not formalised

The construction of the three morphisms of pure configurations out of a morphism of ladders,
which is the one paragraph of Theorem 7.10 `T:NaturalSnake` that the paper itself compresses into
"the other two configurations are handled in the same way". Everything the pasting needs of them
is isolated in `nonempty_iso_connecting_square`.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

section Definition

variable {A C X Y Z A' C' X' Y' Z' : B}

/-- A **morphism of pure configurations**: a pair of morphisms of short 2-exact sequences, one
between the two top rows and one between the two bottom rows, sharing their middle component.

There is no further data and no axiom. In particular nothing is imposed on the verticals `f` and
`h` of the two configurations: the comparisons `πf` and `πh` are induced, by
`MorphismPure.exists_piF` and `MorphismPure.exists_piH`. -/
structure MorphismPure (a : A ⟶ Y) (b : Y ⟶ C) (c : X ⟶ Y) (d : Y ⟶ Z)
    (a' : A' ⟶ Y') (b' : Y' ⟶ C') (c' : X' ⟶ Y') (d' : Y' ⟶ Z') where
  /-- The component on the source of the top row. -/
  πA : A ⟶ A'
  /-- The shared middle component. -/
  πY : Y ⟶ Y'
  /-- The component on the target of the top row. -/
  πC : C ⟶ C'
  /-- The component on the source of the bottom row. -/
  πX : X ⟶ X'
  /-- The component on the target of the bottom row. -/
  πZ : Z ⟶ Z'
  /-- The square over `a`. -/
  ψa : a ≫ πY ≅ πA ≫ a'
  /-- The square over `b`. -/
  ψb : b ≫ πC ≅ πY ≫ b'
  /-- The square over `c`. -/
  ψc : c ≫ πY ≅ πX ≫ c'
  /-- The square over `d`. -/
  ψd : d ≫ πZ ≅ πY ≫ d'

section Opposite

open Opposite Bicategory.Opposite

variable {a : A ⟶ Y} {b : Y ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}
  {a' : A' ⟶ Y'} {b' : Y' ⟶ C'} {c' : X' ⟶ Y'} {d' : Y' ⟶ Z'}

/-- **The dual morphism of pure configurations.** Read in `Bᵒᵖ` a pure configuration becomes one
again, with its two rows exchanged; and since 1-cells reverse, a morphism from `Π` to `Π'`
becomes a morphism from `Π'ᵒᵖ` to `Πᵒᵖ`. -/
def MorphismPure.op (S : MorphismPure a b c d a' b' c' d') :
    MorphismPure d'.op c'.op b'.op a'.op d.op c.op b.op a.op where
  πA := S.πZ.op
  πY := S.πY.op
  πC := S.πX.op
  πX := S.πC.op
  πZ := S.πA.op
  ψa := S.ψd.op2.symm
  ψb := S.ψc.op2.symm
  ψc := S.ψb.op2.symm
  ψd := S.ψa.op2.symm

end Opposite

end Definition

section InducedVerticals

variable [Bicategory.Strict B] {A C X Y Z A' C' X' Y' Z' : B}
  {a : A ⟶ Y} {b : Y ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}
  {a' : A' ⟶ Y'} {b' : Y' ⟶ C'} {c' : X' ⟶ Y'} {d' : Y' ⟶ Z'}

/-- **Lemma 7.4 `L:InducedVerticals`.** A morphism of pure configurations induces a comparison on
the
left-hand verticals. It is not part of the data: the pasting of `ψc`, `θf`, `ψa` and `θf'` is
reflected along the 2-monomorphism `c'`, uniquely. -/
theorem MorphismPure.exists_piF (S : MorphismPure a b c d a' b' c' d') {f : A ⟶ X} {f' : A' ⟶ X'}
    (θf : a ≅ f ≫ c) (θf' : a' ≅ f' ≫ c') [IsTwoMono c'] :
    Nonempty (f ≫ S.πX ≅ S.πA ≫ f') :=
  ⟨IsTwoMono.preimageIso c' <| calc
    (f ≫ S.πX) ≫ c' ≅ f ≫ S.πX ≫ c' := eqToIso (Category.assoc _ _ _)
    _ ≅ f ≫ c ≫ S.πY := Bicategory.whiskerLeftIso f S.ψc.symm
    _ ≅ (f ≫ c) ≫ S.πY := (eqToIso (Category.assoc _ _ _)).symm
    _ ≅ a ≫ S.πY := Bicategory.whiskerRightIso θf.symm S.πY
    _ ≅ S.πA ≫ a' := S.ψa
    _ ≅ S.πA ≫ f' ≫ c' := Bicategory.whiskerLeftIso S.πA θf'
    _ ≅ (S.πA ≫ f') ≫ c' := (eqToIso (Category.assoc _ _ _)).symm⟩

/-- **Lemma 7.4 `L:InducedVerticals`, the other half.** The comparison on the right-hand
verticals is
coreflected along the 2-epimorphism `b`. This is `MorphismPure.exists_piF` read in `Bᵒᵖ`. -/
theorem MorphismPure.exists_piH (S : MorphismPure a b c d a' b' c' d') {h : C ⟶ Z} {h' : C' ⟶ Z'}
    (θh : b ≫ h ≅ d) (θh' : b' ≫ h' ≅ d') [IsTwoEpi b] :
    Nonempty (h ≫ S.πZ ≅ S.πC ≫ h') := by
  open Opposite Bicategory.Opposite in
  haveI := isTwoMono_op b
  obtain ⟨θ⟩ := S.op.exists_piF (f := h'.op) (f' := h.op) θh'.op2.symm θh.op2.symm
  exact ⟨θ.unop2.symm⟩

end InducedVerticals

section InducedMaps

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O]
  {A C X Y Z A' C' X' Y' Z' I I' J J' : B}
  {a : A ⟶ Y} {b : Y ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}
  {a' : A' ⟶ Y'} {b' : Y' ⟶ C'} {c' : X' ⟶ Y'} {d' : Y' ⟶ Z'}

/-- **The 1-cell induced on `2-Cok(f)`.** -/
theorem MorphismPure.exists_cokMapF (S : MorphismPure a b c d a' b' c' d') {f : A ⟶ X}
    {f' : A' ⟶ X'} (θf : a ≅ f ≫ c) (θf' : a' ≅ f' ≫ c') [IsTwoMono c'] {e : X ⟶ I}
    (he : IsTwoCokernel O f e) {e' : X' ⟶ I'} (he' : IsTwoCokernel O f' e') :
    ∃ u : I ⟶ I', Nonempty (e ≫ u ≅ S.πX ≫ e') :=
  exists_cokMap (S.exists_piF θf θf').some he he'

/-- **The 1-cell induced on `2-Ker(h)`.** -/
theorem MorphismPure.exists_kerMapH (S : MorphismPure a b c d a' b' c' d') {h : C ⟶ Z}
    {h' : C' ⟶ Z'} (θh : b ≫ h ≅ d) (θh' : b' ≫ h' ≅ d') [IsTwoEpi b] {m : J ⟶ C}
    (hm : IsTwoKernel O h m) {m' : J' ⟶ C'} (hm' : IsTwoKernel O h' m') :
    ∃ w : J ⟶ J', Nonempty (w ≫ m' ≅ m ≫ S.πC) :=
  exists_kerMap (S.exists_piH θh θh').some hm hm'

end InducedMaps

section NaturalComparison

variable [Bicategory.Strict B] {O : B} [HasBizero O]
  {A C X Y Z A' C' X' Y' Z' I I' J J' : B}
  {a : A ⟶ Y} {b : Y ⟶ C} {c : X ⟶ Y} {d : Y ⟶ Z}
  {a' : A' ⟶ Y'} {b' : Y' ⟶ C'} {c' : X' ⟶ Y'} {d' : Y' ⟶ Z'}
  {e : X ⟶ I} {m : J ⟶ C} {e' : X' ⟶ I'} {m' : J' ⟶ C'}

/-- The first of the two characterising pastings of Theorem 7.6 `T:NaturalComparison`: `u ≫ j'`,
whiskered by `e` on the left and `m'` on the right, is the dinversion `c ≫ b` followed by `πC`. -/
def naturalComparisonPasting₁ (S : MorphismPure a b c d a' b' c' d')
    (P' : PureSnakeComparison O c' b' e' m') {u : I ⟶ I'} (hu : e ≫ u ≅ S.πX ≫ e') :
    e ≫ (u ≫ P'.j) ≫ m' ≅ c ≫ b ≫ S.πC :=
  calc e ≫ (u ≫ P'.j) ≫ m' ≅ (e ≫ u) ≫ P'.j ≫ m' := eqToIso (by simp)
    _ ≅ (S.πX ≫ e') ≫ P'.j ≫ m' := Bicategory.whiskerRightIso hu _
    _ ≅ S.πX ≫ e' ≫ P'.j ≫ m' := eqToIso (by simp)
    _ ≅ S.πX ≫ c' ≫ b' := Bicategory.whiskerLeftIso S.πX P'.θ
    _ ≅ (S.πX ≫ c') ≫ b' := eqToIso (by simp)
    _ ≅ (c ≫ S.πY) ≫ b' := Bicategory.whiskerRightIso S.ψc.symm b'
    _ ≅ c ≫ S.πY ≫ b' := eqToIso (by simp)
    _ ≅ c ≫ b ≫ S.πC := Bicategory.whiskerLeftIso c S.ψb.symm

/-- The second characterising pasting: `j ≫ w`, whiskered the same way, is the same 1-cell. -/
def naturalComparisonPasting₂ (S : MorphismPure a b c d a' b' c' d')
    (P : PureSnakeComparison O c b e m) {w : J ⟶ J'} (hw : w ≫ m' ≅ m ≫ S.πC) :
    e ≫ (P.j ≫ w) ≫ m' ≅ c ≫ b ≫ S.πC :=
  calc e ≫ (P.j ≫ w) ≫ m' ≅ e ≫ P.j ≫ w ≫ m' := eqToIso (by simp)
    _ ≅ e ≫ P.j ≫ m ≫ S.πC := Bicategory.whiskerLeftIso e (Bicategory.whiskerLeftIso P.j hw)
    _ ≅ (e ≫ P.j ≫ m) ≫ S.πC := eqToIso (by simp)
    _ ≅ (c ≫ b) ≫ S.πC := Bicategory.whiskerRightIso P.θ S.πC
    _ ≅ c ≫ b ≫ S.πC := eqToIso (by simp)

/-- **Theorem 7.6 `T:NaturalComparison`, the 2-cell.** Given a morphism of pure configurations and
the 1-cells `u` and `w` it induces on `2-Cok(f)` and `2-Ker(h)`, the invertible 2-cell
`u ≫ j' ≅ j ≫ w` obtained by reflecting the composite of the two characterising pastings along the
2-epimorphism `e` and the 2-monomorphism `m'`. -/
noncomputable def naturalComparisonIso (S : MorphismPure a b c d a' b' c' d')
    (P : PureSnakeComparison O c b e m) (P' : PureSnakeComparison O c' b' e' m')
    [IsTwoEpi e] [IsTwoMono m'] {u : I ⟶ I'} (hu : e ≫ u ≅ S.πX ≫ e') {w : J ⟶ J'}
    (hw : w ≫ m' ≅ m ≫ S.πC) : u ≫ P'.j ≅ P.j ≫ w :=
  IsTwoMono.preimageIso m' (IsTwoEpi.preimageIso e
    (naturalComparisonPasting₁ S P' hu ≪≫ (naturalComparisonPasting₂ S P hw).symm))

/-- **Theorem 7.6 `T:NaturalComparison`, the compatibility clause.** Whiskered by `e` on the left
and by `m'` on the right, the 2-cell of `naturalComparisonIso` is the first characterising pasting
followed by the inverse of the second: the two pastings displayed in the paper's proof compose to
the identity of `πC ∘ b ∘ c`. -/
theorem natural_comparison_whisker (S : MorphismPure a b c d a' b' c' d')
    (P : PureSnakeComparison O c b e m) (P' : PureSnakeComparison O c' b' e' m')
    [IsTwoEpi e] [IsTwoMono m'] {u : I ⟶ I'} (hu : e ≫ u ≅ S.πX ≫ e') {w : J ⟶ J'}
    (hw : w ≫ m' ≅ m ≫ S.πC) :
    e ◁ ((naturalComparisonIso S P P' hu hw).hom ▷ m') =
      (naturalComparisonPasting₁ S P' hu).hom ≫ (naturalComparisonPasting₂ S P hw).inv := by
  have h₁ : (naturalComparisonIso S P P' hu hw).hom ▷ m' =
      (IsTwoEpi.preimageIso e (naturalComparisonPasting₁ S P' hu ≪≫
        (naturalComparisonPasting₂ S P hw).symm)).hom := by
    unfold naturalComparisonIso IsTwoMono.preimageIso
    rw [Functor.preimageIso_hom]
    exact (Bicategory.postcomp I m').map_preimage _
  have h₂ : e ◁ (IsTwoEpi.preimageIso e (naturalComparisonPasting₁ S P' hu ≪≫
      (naturalComparisonPasting₂ S P hw).symm)).hom =
      (naturalComparisonPasting₁ S P' hu ≪≫ (naturalComparisonPasting₂ S P hw).symm).hom := by
    unfold IsTwoEpi.preimageIso
    rw [Functor.preimageIso_hom]
    exact (Bicategory.precomp C' e).map_preimage _
  rw [h₁, h₂]
  rfl

/-- **Theorem 7.6 `T:NaturalComparison`: the Pure Snake comparison is 2-natural.** Given a
morphism of pure configurations and the 1-cells `u` and `w` it induces on `2-Cok(f)` and
`2-Ker(h)`, the two composites `u ≫ j'` and `j ≫ w` agree up to an invertible 2-cell — the one of
`naturalComparisonIso`, whose compatibility with the characterising 2-cells is
`natural_comparison_whisker`.

Only the characterising 2-cells of the two comparisons are used; that they are equivalences plays
no part, so neither homological self-duality nor 2-di-exactness appears. -/
theorem natural_comparison (S : MorphismPure a b c d a' b' c' d')
    (P : PureSnakeComparison O c b e m) (P' : PureSnakeComparison O c' b' e' m')
    [IsTwoEpi e] [IsTwoMono m'] {u : I ⟶ I'} (hu : e ≫ u ≅ S.πX ≫ e') {w : J ⟶ J'}
    (hw : w ≫ m' ≅ m ≫ S.πC) : Nonempty (u ≫ P'.j ≅ P.j ≫ w) :=
  ⟨naturalComparisonIso S P P' hu hw⟩

omit [Strict B] in
/-- **The 2-natural comparison is unique.** Any two 2-cells that agree after whiskering by the
2-epimorphism `e` and the 2-monomorphism `m'` are equal, so `natural_comparison` produces the only
2-cell compatible with the two characterising triangles. -/
theorem natural_comparison_unique [IsTwoEpi e] [IsTwoMono m'] {j : I ⟶ J} {j' : I' ⟶ J'}
    {u : I ⟶ I'} {w : J ⟶ J'} (ν ν' : u ≫ j' ⟶ j ≫ w)
    (hν : e ◁ (ν ▷ m') = e ◁ (ν' ▷ m')) : ν = ν' :=
  (Bicategory.postcomp I m').map_injective ((Bicategory.precomp C' e).map_injective hν)

end NaturalComparison

section Squares

variable [Bicategory.Strict B]

/-- **Naturality of the 1-cell induced on 2-kernels.** Four of the five squares of Theorem 7.10
`T:NaturalSnake` are instances of this: given a cube whose bottom face is the square `ψa` between
two 2-kernels, whose top face is the primed square `ψa'`, and whose three remaining known faces
commute up to invertible 2-cells, the fourth face commutes too, because `kg'` is a
2-monomorphism.

Nothing about 2-kernels is used beyond that, so the statement is about an arbitrary
2-monomorphism. -/
theorem nonempty_iso_kerMap_square {A M KF KG A' M' KF' KG' : B} {a : A ⟶ M} {a' : A' ⟶ M'}
    {kf : KF ⟶ A} {kg : KG ⟶ M} {kf' : KF' ⟶ A'} {kg' : KG' ⟶ M'} [IsTwoMono kg']
    {aBar : KF ⟶ KG} {aBar' : KF' ⟶ KG'} {pA : A ⟶ A'} {pM : M ⟶ M'} {pKF : KF ⟶ KF'}
    {pKG : KG ⟶ KG'} (ψa : aBar ≫ kg ≅ kf ≫ a) (ψa' : aBar' ≫ kg' ≅ kf' ≫ a')
    (pa : a ≫ pM ≅ pA ≫ a') (pf : pKF ≫ kf' ≅ kf ≫ pA) (pg : pKG ≫ kg' ≅ kg ≫ pM) :
    Nonempty (aBar ≫ pKG ≅ pKF ≫ aBar') :=
  ⟨IsTwoMono.preimageIso kg' <| calc
    (aBar ≫ pKG) ≫ kg' ≅ aBar ≫ pKG ≫ kg' := eqToIso (by simp)
    _ ≅ aBar ≫ kg ≫ pM := Bicategory.whiskerLeftIso aBar pg
    _ ≅ (aBar ≫ kg) ≫ pM := eqToIso (by simp)
    _ ≅ (kf ≫ a) ≫ pM := Bicategory.whiskerRightIso ψa pM
    _ ≅ kf ≫ a ≫ pM := eqToIso (by simp)
    _ ≅ kf ≫ pA ≫ a' := Bicategory.whiskerLeftIso kf pa
    _ ≅ (kf ≫ pA) ≫ a' := eqToIso (by simp)
    _ ≅ (pKF ≫ kf') ≫ a' := Bicategory.whiskerRightIso pf.symm a'
    _ ≅ pKF ≫ kf' ≫ a' := eqToIso (by simp)
    _ ≅ pKF ≫ aBar' ≫ kg' := Bicategory.whiskerLeftIso pKF ψa'.symm
    _ ≅ (pKF ≫ aBar') ≫ kg' := eqToIso (by simp)⟩

open Opposite Bicategory.Opposite in
/-- **Naturality of the 1-cell induced on 2-cokernels**, the dual of `nonempty_iso_kerMap_square`.
Obtained by transport through `Bᵒᵖ`, where the morphism of ladders reverses, so the primed and
unprimed data change places. -/
theorem nonempty_iso_cokMap_square {X Y QF QG X' Y' QF' QG' : B} {c : X ⟶ Y} {c' : X' ⟶ Y'}
    {qf : X ⟶ QF} {qg : Y ⟶ QG} {qf' : X' ⟶ QF'} {qg' : Y' ⟶ QG'} [IsTwoEpi qf]
    {cBar : QF ⟶ QG} {cBar' : QF' ⟶ QG'} {pX : X ⟶ X'} {pY : Y ⟶ Y'} {pQF : QF ⟶ QF'}
    {pQG : QG ⟶ QG'} (ψc : qf ≫ cBar ≅ c ≫ qg) (ψc' : qf' ≫ cBar' ≅ c' ≫ qg')
    (pc : c ≫ pY ≅ pX ≫ c') (pqf : qf ≫ pQF ≅ pX ≫ qf') (pqg : qg ≫ pQG ≅ pY ≫ qg') :
    Nonempty (cBar ≫ pQG ≅ pQF ≫ cBar') :=
  haveI := isTwoMono_op qf
  ⟨(nonempty_iso_kerMap_square (kf := qg'.op) (kg := qf'.op) (kf' := qg.op) (kg' := qf.op)
    ψc'.op2 ψc.op2 pc.op2.symm pqg.op2 pqf.op2).some.unop2.symm⟩

/-- **Naturality of a chosen quasi-inverse.** If a square between two equivalences commutes up to
an invertible 2-cell, so does the square between their chosen quasi-inverses. This is what turns
naturality of the middle Pure Snake comparison into naturality of its inverse, which is how it
occurs in `∂`. -/
theorem nonempty_iso_inv_square {V W V' W' : B} {z : V ⟶ W} {z' : V' ⟶ W'} (hz : IsEquiv1 z)
    (hz' : IsEquiv1 z') {pV : V ⟶ V'} {pW : W ⟶ W'} (ν : z ≫ pW ≅ pV ≫ z') :
    Nonempty (hz.inv ≫ pV ≅ pW ≫ hz'.inv) :=
  ⟨calc hz.inv ≫ pV ≅ (hz.inv ≫ pV) ≫ 𝟙 V' := eqToIso (by simp)
    _ ≅ (hz.inv ≫ pV) ≫ z' ≫ hz'.inv :=
        Bicategory.whiskerLeftIso _ hz'.nonempty_comp_inv.some.symm
    _ ≅ hz.inv ≫ (pV ≫ z') ≫ hz'.inv := eqToIso (by simp)
    _ ≅ hz.inv ≫ (z ≫ pW) ≫ hz'.inv := Bicategory.whiskerLeftIso _
        (Bicategory.whiskerRightIso ν.symm hz'.inv)
    _ ≅ (hz.inv ≫ z) ≫ pW ≫ hz'.inv := eqToIso (by simp)
    _ ≅ 𝟙 W ≫ pW ≫ hz'.inv := Bicategory.whiskerRightIso hz.nonempty_inv_comp.some _
    _ ≅ pW ≫ hz'.inv := eqToIso (by simp)⟩

/-- **The pasting that makes `∂` 2-natural.** The connecting 1-cell has the shape
`∂ = 2-ker(c̲) ∘ z ∘ 2-coker(b̄)`, so once each of its three factors is 2-natural, so is `∂`. -/
theorem nonempty_iso_connecting_square {KH CB KC QF KH' CB' KC' QF' : B} {q : KH ⟶ CB}
    {z : CB ⟶ KC} {m : KC ⟶ QF} {q' : KH' ⟶ CB'} {z' : CB' ⟶ KC'} {m' : KC' ⟶ QF'}
    {pKH : KH ⟶ KH'} {pCB : CB ⟶ CB'} {pKC : KC ⟶ KC'} {pQF : QF ⟶ QF'}
    (νq : q ≫ pCB ≅ pKH ≫ q') (νz : z ≫ pKC ≅ pCB ≫ z') (νm : m ≫ pQF ≅ pKC ≫ m') :
    Nonempty ((q ≫ z ≫ m) ≫ pQF ≅ pKH ≫ q' ≫ z' ≫ m') :=
  ⟨calc (q ≫ z ≫ m) ≫ pQF ≅ q ≫ z ≫ m ≫ pQF := eqToIso (by simp)
    _ ≅ q ≫ z ≫ pKC ≫ m' := Bicategory.whiskerLeftIso q (Bicategory.whiskerLeftIso z νm)
    _ ≅ q ≫ (z ≫ pKC) ≫ m' := eqToIso (by simp)
    _ ≅ q ≫ (pCB ≫ z') ≫ m' := Bicategory.whiskerLeftIso q (Bicategory.whiskerRightIso νz m')
    _ ≅ (q ≫ pCB) ≫ z' ≫ m' := eqToIso (by simp)
    _ ≅ (pKH ≫ q') ≫ z' ≫ m' := Bicategory.whiskerRightIso νq _
    _ ≅ pKH ≫ q' ≫ z' ≫ m' := eqToIso (by simp)⟩

end Squares

section ImageMap

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {K A A' I I' Bo Bo' : B}

/-- **The 1-cell induced on normal images.** A square `u ≫ pB ≅ pA ≫ u'` between two 1-cells
equipped with normal image factorisations `u ≅ e ≫ m` and `u' ≅ e' ≫ m'` induces a comparison
`pI` on the images, filling both halves of the square.

This is what Theorem 7.10 `T:NaturalSnake` invokes as "the 1-cell `I → I'` obtained from the
uniqueness
of the normal image factorisation", and it is the only piece of the construction of a morphism of
pure configurations that is more than bookkeeping. The proof reflects nullity along `m'` to factor
`pA ≫ e'` through the 2-cokernel `e`, then recovers the second square by coreflecting along the
2-epimorphism `e`. -/
theorem exists_normalImageMap {u : A ⟶ Bo} {u' : A' ⟶ Bo'} {e : A ⟶ I} {m : I ⟶ Bo}
    {e' : A' ⟶ I'} {m' : I' ⟶ Bo'} [IsTwoMono m'] {k : K ⟶ A} (he : IsTwoCokernel O k e)
    (θ : u ≅ e ≫ m) (θ' : u' ≅ e' ≫ m') {pA : A ⟶ A'} {pB : Bo ⟶ Bo'}
    (φ : u ≫ pB ≅ pA ≫ u') :
    ∃ pI : I ⟶ I', Nonempty (e ≫ pI ≅ pA ≫ e') ∧ Nonempty (pI ≫ m' ≅ m ≫ pB) := by
  haveI := he.isTwoEpi
  have hnull : IsEssNull O (k ≫ pA ≫ e') := by
    refine IsEssNull.of_comp_isTwoMono m' (((he.isEssNull_comp.comp m).comp pB).of_iso ?_)
    calc ((k ≫ e) ≫ m) ≫ pB ≅ (k ≫ e ≫ m) ≫ pB := eqToIso (by simp)
      _ ≅ (k ≫ u) ≫ pB := Bicategory.whiskerRightIso (Bicategory.whiskerLeftIso k θ.symm) pB
      _ ≅ k ≫ u ≫ pB := eqToIso (by simp)
      _ ≅ k ≫ pA ≫ u' := Bicategory.whiskerLeftIso k φ
      _ ≅ k ≫ pA ≫ e' ≫ m' := Bicategory.whiskerLeftIso k (Bicategory.whiskerLeftIso pA θ')
      _ ≅ (k ≫ pA ≫ e') ≫ m' := eqToIso (by simp)
  obtain ⟨pI, ⟨γ⟩⟩ := he.fac (pA ≫ e') hnull
  refine ⟨pI, ⟨γ⟩, ⟨IsTwoEpi.preimageIso e <| calc
    e ≫ pI ≫ m' ≅ (e ≫ pI) ≫ m' := eqToIso (by simp)
    _ ≅ (pA ≫ e') ≫ m' := Bicategory.whiskerRightIso γ m'
    _ ≅ pA ≫ e' ≫ m' := eqToIso (by simp)
    _ ≅ pA ≫ u' := Bicategory.whiskerLeftIso pA θ'.symm
    _ ≅ u ≫ pB := φ.symm
    _ ≅ (e ≫ m) ≫ pB := Bicategory.whiskerRightIso θ pB
    _ ≅ e ≫ m ≫ pB := eqToIso (by simp)⟩⟩

end ImageMap

section Assembly

variable [Bicategory.Strict B] {CB KT KS KC CB' KT' KS' KC' QF QF' KH KH' : B}

/-- **The middle equivalence of `∂` is 2-natural.** The connecting 1-cell factors through
`z = z₁ ≫ z₂⁻¹ ≫ z₃` — the paper's `z₃ ∘ z₂⁻¹ ∘ z₁` of `(Def Partial)`, in diagrammatic order —
the composite of the three Pure Snake comparisons of the construction.
Given naturality of each of the three — which is `natural_comparison` applied to a morphism of the
corresponding pure configurations — `z` is 2-natural.

The two shared components are what makes the pasting close: the first and the middle
configurations induce the *same* 1-cell `w₁` on `2-Ker(t)`, and the middle and the last induce the
same `u₃` on `2-Cok(s)`. -/
theorem nonempty_iso_snakeComparison_square {z₁ : CB ⟶ KT} {z₂ : KS ⟶ KT} {z₃ : KS ⟶ KC}
    {z₁' : CB' ⟶ KT'} {z₂' : KS' ⟶ KT'} {z₃' : KS' ⟶ KC'} (hz₂ : IsEquiv1 z₂)
    (hz₂' : IsEquiv1 z₂') {u₁ : CB ⟶ CB'} {w₁ : KT ⟶ KT'} {u₃ : KS ⟶ KS'} {w₂ : KC ⟶ KC'}
    (ν₁ : u₁ ≫ z₁' ≅ z₁ ≫ w₁) (ν₂ : u₃ ≫ z₂' ≅ z₂ ≫ w₁) (ν₃ : u₃ ≫ z₃' ≅ z₃ ≫ w₂) :
    Nonempty ((z₁ ≫ hz₂.inv ≫ z₃) ≫ w₂ ≅ u₁ ≫ z₁' ≫ hz₂'.inv ≫ z₃') :=
  ⟨calc (z₁ ≫ hz₂.inv ≫ z₃) ≫ w₂ ≅ z₁ ≫ hz₂.inv ≫ z₃ ≫ w₂ := eqToIso (by simp)
    _ ≅ z₁ ≫ hz₂.inv ≫ u₃ ≫ z₃' :=
        Bicategory.whiskerLeftIso z₁ (Bicategory.whiskerLeftIso hz₂.inv ν₃.symm)
    _ ≅ z₁ ≫ (hz₂.inv ≫ u₃) ≫ z₃' := eqToIso (by simp)
    _ ≅ z₁ ≫ (w₁ ≫ hz₂'.inv) ≫ z₃' := Bicategory.whiskerLeftIso z₁
        (Bicategory.whiskerRightIso (nonempty_iso_inv_square hz₂ hz₂' ν₂.symm).some z₃')
    _ ≅ (z₁ ≫ w₁) ≫ hz₂'.inv ≫ z₃' := eqToIso (by simp)
    _ ≅ (u₁ ≫ z₁') ≫ hz₂'.inv ≫ z₃' := Bicategory.whiskerRightIso ν₁.symm _
    _ ≅ u₁ ≫ z₁' ≫ hz₂'.inv ≫ z₃' := eqToIso (by simp)⟩

/-- **2-naturality of the connecting 1-cell.** This is the square of Theorem 7.10
`T:NaturalSnake` that
involves `∂`, assembled from the three Pure Snake comparisons and the two 1-cells induced on
`2-Cok(b̄)` and `2-Ker(c̲)`.

What it does not do is *construct* the three morphisms of pure configurations out of a morphism of
ladders; that is the paragraph the paper compresses. Everything the pasting needs of them appears
here as the hypotheses `ν₁`, `ν₂`, `ν₃`. -/
theorem nonempty_iso_connecting_snake {q : KH ⟶ CB} {m : KC ⟶ QF} {q' : KH' ⟶ CB'}
    {m' : KC' ⟶ QF'} {z₁ : CB ⟶ KT} {z₂ : KS ⟶ KT} {z₃ : KS ⟶ KC} {z₁' : CB' ⟶ KT'}
    {z₂' : KS' ⟶ KT'} {z₃' : KS' ⟶ KC'} (hz₂ : IsEquiv1 z₂) (hz₂' : IsEquiv1 z₂')
    {pKH : KH ⟶ KH'} {u₁ : CB ⟶ CB'} {w₁ : KT ⟶ KT'} {u₃ : KS ⟶ KS'} {w₂ : KC ⟶ KC'}
    {pQF : QF ⟶ QF'} (νq : q ≫ u₁ ≅ pKH ≫ q') (ν₁ : u₁ ≫ z₁' ≅ z₁ ≫ w₁)
    (ν₂ : u₃ ≫ z₂' ≅ z₂ ≫ w₁) (ν₃ : u₃ ≫ z₃' ≅ z₃ ≫ w₂) (νm : m ≫ pQF ≅ w₂ ≫ m') :
    Nonempty ((q ≫ (z₁ ≫ hz₂.inv ≫ z₃) ≫ m) ≫ pQF ≅
      pKH ≫ q' ≫ (z₁' ≫ hz₂'.inv ≫ z₃') ≫ m') :=
  nonempty_iso_connecting_square νq
    (nonempty_iso_snakeComparison_square hz₂ hz₂' ν₁ ν₂ ν₃).some νm

end Assembly

end SnakeLean
