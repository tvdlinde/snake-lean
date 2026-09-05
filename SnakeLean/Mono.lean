/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.TFAE
import SnakeLean.Op

/-!
# 2-monomorphisms and 2-epimorphisms

This module formalises the part of Section 2 of *A two-categorical Snake Lemma* that introduces
2-monomorphisms and 2-epimorphisms, together with the cancellation property that the paper needs
in Proposition 3.6 `Composites of Normal Monos`.

Following the paper, a **2-monomorphism** is a representably fully faithful 1-cell: `f : x ⟶ y`
is one when the postcomposition functor `(w ⟶ x) ⥤ (w ⟶ y)` is fully faithful for every `w`.
A **2-epimorphism** is the dual, defined through precomposition. A **faithful 1-cell** is one for
which those postcomposition functors are merely faithful; the paper does not take it as its
notion of 2-monomorphism, but uses it where it is all a proof consumes, as in Proposition 3.6
`Composites of Normal Monos`(i) and Remark 3.7 `Rem Faithful Enough`.

Mathlib supplies the two functors as `Bicategory.postcomp` and `Bicategory.precomp`, along with
the natural isomorphisms relating them to composition, so the whole module is a translation into
Mathlib's `Full`/`Faithful` API.

## Main results

* `isEquiv1_tfae_representable` — Lemma 2.15 `L:RepEquiv`: a 1-cell is an equivalence exactly when
  precomposition with it is an equivalence of hom-categories, and exactly when postcomposition
  with it is. Neither strictness nor a bizero object is needed.

## Faithful is enough

Proposition 3.6 `Composites of Normal Monos`(i) reads: if `k ≅ f ≫ g` with `k` a 2-monomorphism
and `g` faithful, then `f` is a 2-monomorphism — faithfulness of `g`, not full faithfulness, as
Remark 3.7 `Rem Faithful Enough` points out. `isTwoMono_of_comp` is that statement, assuming
`IsFaithful₁ g`; `isTwoEpi_of_comp` is its dual, with `f` cofaithful.

## Non-vacuity, and the discretisation

`isTwoMono_locallyDiscrete_iff`: in a locally discrete 2-category, a 1-cell is a 2-monomorphism
exactly when it is a monomorphism of the underlying category. This is the paper's remark that
the discretisation of a 2-monomorphism is a monomorphism, and it makes every statement below
non-vacuous.

## Not formalised

Nothing that needs 2-kernels, which come later: that 2-kernels are 2-monomorphisms is in
`SnakeLean.Kernel`, and Proposition 3.6 `Composites of Normal Monos`(ii), which is about *normal*
2-monomorphisms, in `SnakeLean.Normal`.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- A **faithful 1-cell**: postcomposition with `f` is faithful on every hom-category. -/
class IsFaithful₁ {x y : B} (f : x ⟶ y) : Prop where
  /-- Postcomposition with `f` is faithful. -/
  faithful (w : B) : (Bicategory.postcomp w f).Faithful

/-- A **2-monomorphism**, that is, a representably fully faithful 1-cell: postcomposition with
`f` is fully faithful on every hom-category. -/
class IsTwoMono {x y : B} (f : x ⟶ y) : Prop where
  /-- Postcomposition with `f` is full. -/
  full (w : B) : (Bicategory.postcomp w f).Full
  /-- Postcomposition with `f` is faithful. -/
  faithful (w : B) : (Bicategory.postcomp w f).Faithful

/-- A **cofaithful 1-cell**: precomposition with `f` is faithful on every hom-category. -/
class IsCofaithful₁ {x y : B} (f : x ⟶ y) : Prop where
  /-- Precomposition with `f` is faithful. -/
  faithful (w : B) : (Bicategory.precomp w f).Faithful

/-- A **2-epimorphism**, that is, a representably cofully faithful 1-cell: precomposition with
`f` is fully faithful on every hom-category. -/
class IsTwoEpi {x y : B} (f : x ⟶ y) : Prop where
  /-- Precomposition with `f` is full. -/
  full (w : B) : (Bicategory.precomp w f).Full
  /-- Precomposition with `f` is faithful. -/
  faithful (w : B) : (Bicategory.precomp w f).Faithful

attribute [instance] IsFaithful₁.faithful IsTwoMono.full IsTwoMono.faithful
  IsCofaithful₁.faithful IsTwoEpi.full IsTwoEpi.faithful

instance (priority := 100) IsTwoMono.toIsFaithful₁ {x y : B} (f : x ⟶ y) [IsTwoMono f] :
    IsFaithful₁ f := ⟨fun w => IsTwoMono.faithful w⟩

instance (priority := 100) IsTwoEpi.toIsCofaithful₁ {x y : B} (f : x ⟶ y) [IsTwoEpi f] :
    IsCofaithful₁ f := ⟨fun w => IsTwoEpi.faithful w⟩

section Opposite

open Opposite Bicategory.Opposite

variable {x y : B}

/-- A 2-monomorphism dualises to a 2-epimorphism. -/
theorem isTwoEpi_op (f : x ⟶ y) [IsTwoMono f] : IsTwoEpi f.op where
  full w :=
    { map_surjective := by
        intro g g' η
        obtain ⟨ζ, hζ⟩ := (IsTwoMono.full (f := f) w.unop).map_surjective η.unop2
        exact ⟨op2 ζ, by simpa using congrArg op2 hζ⟩ }
  faithful w :=
    { map_injective := by
        intro g g' η η' hh
        have h1 := congrArg Hom2.unop2 hh
        simp only [Bicategory.precomp] at h1
        have h2 := (IsTwoMono.faithful (f := f) w.unop).map_injective h1
        simpa using congrArg op2 h2 }

/-- A 2-epimorphism dualises to a 2-monomorphism. -/
theorem isTwoMono_op (f : x ⟶ y) [IsTwoEpi f] : IsTwoMono f.op where
  full w :=
    { map_surjective := by
        intro g g' η
        obtain ⟨ζ, hζ⟩ := (IsTwoEpi.full (f := f) w.unop).map_surjective η.unop2
        exact ⟨op2 ζ, by simpa using congrArg op2 hζ⟩ }
  faithful w :=
    { map_injective := by
        intro g g' η η' hh
        have h1 := congrArg Hom2.unop2 hh
        simp only [Bicategory.postcomp] at h1
        have h2 := (IsTwoEpi.faithful (f := f) w.unop).map_injective h1
        simpa using congrArg op2 h2 }

/-- A 1-cell of `Bᵒᵖ` that is a 2-epimorphism comes from a 2-monomorphism. -/
theorem isTwoMono_of_isTwoEpi_op {f : x ⟶ y} (h : IsTwoEpi f.op) : IsTwoMono f where
  full w :=
    { map_surjective := by
        intro g g' η
        obtain ⟨ζ, hζ⟩ := (h.full (op w)).map_surjective (op2 η)
        exact ⟨ζ.unop2, by simpa using congrArg Hom2.unop2 hζ⟩ }
  faithful w :=
    { map_injective := by
        intro g g' η η' hh
        have h2 := (h.faithful (op w)).map_injective (congrArg op2 hh)
        simpa using congrArg Hom2.unop2 h2 }

/-- A 1-cell of `Bᵒᵖ` that is a 2-monomorphism comes from a 2-epimorphism. -/
theorem isTwoEpi_of_isTwoMono_op {f : x ⟶ y} (h : IsTwoMono f.op) : IsTwoEpi f where
  full w :=
    { map_surjective := by
        intro g g' η
        obtain ⟨ζ, hζ⟩ := (h.full (op w)).map_surjective (op2 η)
        exact ⟨ζ.unop2, by simpa using congrArg Hom2.unop2 hζ⟩ }
  faithful w :=
    { map_injective := by
        intro g g' η η' hh
        have h2 := (h.faithful (op w)).map_injective (congrArg op2 hh)
        simpa using congrArg Hom2.unop2 h2 }

theorem isTwoEpi_op_iff (f : x ⟶ y) : IsTwoEpi f.op ↔ IsTwoMono f :=
  ⟨isTwoMono_of_isTwoEpi_op, fun h => haveI := h; isTwoEpi_op f⟩

theorem isTwoMono_op_iff (f : x ⟶ y) : IsTwoMono f.op ↔ IsTwoEpi f :=
  ⟨isTwoEpi_of_isTwoMono_op, fun h => haveI := h; isTwoMono_op f⟩

end Opposite

section Iso

variable {x y z : B}

/-- Postcomposition turns composition of 1-cells into composition of functors. -/
def postcompCompIso (w : B) (f : x ⟶ y) (g : y ⟶ z) :
    Bicategory.postcomp w f ⋙ Bicategory.postcomp w g ≅ Bicategory.postcomp w (f ≫ g) :=
  Bicategory.associatorNatIsoLeft w f g

/-- Precomposition turns composition of 1-cells into composition of functors, contravariantly. -/
def precompCompIso (w : B) (f : x ⟶ y) (g : y ⟶ z) :
    Bicategory.precomp w (f ≫ g) ≅ Bicategory.precomp w g ⋙ Bicategory.precomp w f :=
  Bicategory.associatorNatIsoRight f g w

/-- An invertible 2-cell induces a natural isomorphism of postcomposition functors. -/
def postcompMapIso (w : B) {f f' : x ⟶ y} (θ : f ≅ f') :
    Bicategory.postcomp w f ≅ Bicategory.postcomp w f' :=
  (Bicategory.postcomposing w x y).mapIso θ

/-- An invertible 2-cell induces a natural isomorphism of precomposition functors. -/
def precompMapIso (w : B) {f f' : x ⟶ y} (θ : f ≅ f') :
    Bicategory.precomp w f ≅ Bicategory.precomp w f' :=
  (Bicategory.precomposing x y w).mapIso θ

/-- Postcomposition with an identity is the identity functor. -/
def postcompIdIso (w x : B) : Bicategory.postcomp w (𝟙 x) ≅ 𝟭 (w ⟶ x) :=
  Bicategory.rightUnitorNatIso w x

/-- Precomposition with an identity is the identity functor. -/
def precompIdIso (x w : B) : Bicategory.precomp w (𝟙 x) ≅ 𝟭 (x ⟶ w) :=
  Bicategory.leftUnitorNatIso x w

end Iso

section Basic

variable {x y z : B}

instance isTwoMono_id (x : B) : IsTwoMono (𝟙 x) where
  full w := Functor.Full.of_iso (postcompIdIso w x).symm
  faithful w := Functor.Faithful.of_iso (postcompIdIso w x).symm

instance isTwoEpi_id (x : B) : IsTwoEpi (𝟙 x) where
  full w := Functor.Full.of_iso (precompIdIso x w).symm
  faithful w := Functor.Faithful.of_iso (precompIdIso x w).symm

instance IsTwoMono.comp (f : x ⟶ y) (g : y ⟶ z) [IsTwoMono f] [IsTwoMono g] :
    IsTwoMono (f ≫ g) where
  full w := Functor.Full.of_iso (postcompCompIso w f g)
  faithful w := Functor.Faithful.of_iso (postcompCompIso w f g)

instance IsTwoEpi.comp (f : x ⟶ y) (g : y ⟶ z) [IsTwoEpi f] [IsTwoEpi g] : IsTwoEpi (f ≫ g) where
  full w := Functor.Full.of_iso (precompCompIso w f g).symm
  faithful w := Functor.Faithful.of_iso (precompCompIso w f g).symm

/-- Being a 2-monomorphism only depends on the 1-cell up to an invertible 2-cell. -/
theorem IsTwoMono.of_iso {f f' : x ⟶ y} (θ : f ≅ f') [IsTwoMono f] : IsTwoMono f' where
  full w := Functor.Full.of_iso (postcompMapIso w θ)
  faithful w := Functor.Faithful.of_iso (postcompMapIso w θ)

/-- Being a 2-epimorphism only depends on the 1-cell up to an invertible 2-cell. -/
theorem IsTwoEpi.of_iso {f f' : x ⟶ y} (θ : f ≅ f') [IsTwoEpi f] : IsTwoEpi f' where
  full w := Functor.Full.of_iso (precompMapIso w θ)
  faithful w := Functor.Faithful.of_iso (precompMapIso w θ)

end Basic

section Cancellation

variable {x y z : B}

/-- **Proposition 3.6 `Composites of Normal Monos`(i)**: if `k ≅ f ≫ g` with `k` a
2-monomorphism and `g` faithful, then `f` is a 2-monomorphism. -/
theorem isTwoMono_of_comp {f : x ⟶ y} {g : y ⟶ z} {k : x ⟶ z} (θ : k ≅ f ≫ g) [IsTwoMono k]
    [IsFaithful₁ g] : IsTwoMono f where
  full w := Functor.Full.of_comp_faithful_iso (postcompCompIso w f g ≪≫ (postcompMapIso w θ).symm)
  faithful w := Functor.Faithful.of_comp_iso (postcompCompIso w f g ≪≫ (postcompMapIso w θ).symm)

/-- The dual of `isTwoMono_of_comp`: if `k ≅ f ≫ g` with `k` a 2-epimorphism and `f` merely
cofaithful, then `g` is a 2-epimorphism. -/
theorem isTwoEpi_of_comp {f : x ⟶ y} {g : y ⟶ z} {k : x ⟶ z} (θ : k ≅ f ≫ g) [IsTwoEpi k]
    [IsCofaithful₁ f] : IsTwoEpi g where
  full w := Functor.Full.of_comp_faithful_iso
    ((precompCompIso w f g).symm ≪≫ (precompMapIso w θ).symm)
  faithful w := Functor.Faithful.of_comp_iso
    ((precompCompIso w f g).symm ≪≫ (precompMapIso w θ).symm)

/-- A 2-monomorphism lifts invertible 2-cells: this is Remark 2.14 `rem2monoismonouptoiso`, that
a 2-monomorphism is a monomorphism up to invertible 2-cells. -/
noncomputable def IsTwoMono.preimageIso (f : x ⟶ y) [IsTwoMono f] {w : B} {u v : w ⟶ x}
    (θ : u ≫ f ≅ v ≫ f) : u ≅ v :=
  (Bicategory.postcomp w f).preimageIso θ

/-- A 2-epimorphism lifts invertible 2-cells. -/
noncomputable def IsTwoEpi.preimageIso (f : x ⟶ y) [IsTwoEpi f] {w : B} {u v : y ⟶ w}
    (θ : f ≫ u ≅ f ≫ v) : u ≅ v :=
  (Bicategory.precomp w f).preimageIso θ

/-- A 1-cell is an **equivalence** when it admits a quasi-inverse. -/
def IsEquiv1 {x y : B} (f : x ⟶ y) : Prop :=
  ∃ g : y ⟶ x, Nonempty (f ≫ g ≅ 𝟙 x) ∧ Nonempty (g ≫ f ≅ 𝟙 y)

theorem isEquiv1_id (x : B) : IsEquiv1 (𝟙 x) :=
  ⟨𝟙 x, ⟨(ρ_ (𝟙 x))⟩, ⟨(ρ_ (𝟙 x))⟩⟩

/-- An equivalence is a 2-monomorphism. -/
theorem IsEquiv1.isTwoMono {f : x ⟶ y} (h : IsEquiv1 f) : IsTwoMono f := by
  obtain ⟨g, ⟨η⟩, ⟨ε⟩⟩ := h
  refine ⟨fun w => ?_, fun w => ?_⟩ <;>
    · have i₁ : Bicategory.postcomp w f ⋙ Bicategory.postcomp w g ≅ 𝟭 (w ⟶ x) :=
        postcompCompIso w f g ≪≫ postcompMapIso w η ≪≫ postcompIdIso w x
      have i₂ : Bicategory.postcomp w g ⋙ Bicategory.postcomp w f ≅ 𝟭 (w ⟶ y) :=
        postcompCompIso w g f ≪≫ postcompMapIso w ε ≪≫ postcompIdIso w y
      haveI : (Bicategory.postcomp w g).Faithful := Functor.Faithful.of_comp_iso i₂
      haveI : (Bicategory.postcomp w f).Faithful := Functor.Faithful.of_comp_iso i₁
      first
        | exact Functor.Full.of_comp_faithful_iso i₁
        | infer_instance

section Opposite

open Opposite Bicategory.Opposite

/-- Being an equivalence is self-dual. -/
theorem isEquiv1_op {f : x ⟶ y} (h : IsEquiv1 f) : IsEquiv1 f.op := by
  obtain ⟨g, ⟨η⟩, ⟨ε⟩⟩ := h
  exact ⟨g.op, ⟨ε.op2⟩, ⟨η.op2⟩⟩

theorem isEquiv1_of_op {f : x ⟶ y} (h : IsEquiv1 f.op) : IsEquiv1 f := by
  obtain ⟨g, ⟨η⟩, ⟨ε⟩⟩ := h
  exact ⟨g.unop, ⟨ε.unop2⟩, ⟨η.unop2⟩⟩

theorem isEquiv1_op_iff (f : x ⟶ y) : IsEquiv1 f.op ↔ IsEquiv1 f :=
  ⟨isEquiv1_of_op, isEquiv1_op⟩

end Opposite

/-- An equivalence is a 2-epimorphism. This is `IsEquiv1.isTwoMono` read in `Bᵒᵖ`. -/
theorem IsEquiv1.isTwoEpi {f : x ⟶ y} (h : IsEquiv1 f) : IsTwoEpi f :=
  isTwoEpi_of_isTwoMono_op (isEquiv1_op h).isTwoMono

/-- A quasi-inverse of an equivalence is itself an equivalence. -/
theorem isEquiv1_of_inv {f : x ⟶ y} {g : y ⟶ x} (η : f ≫ g ≅ 𝟙 x) (ε : g ≫ f ≅ 𝟙 y) :
    IsEquiv1 g :=
  ⟨f, ⟨ε⟩, ⟨η⟩⟩

/-- A chosen quasi-inverse of an equivalence. The connecting 1-cell of the Snake Lemma is a
composite in which two of the factors are inverses of comparison equivalences, so the inverse has
to be nameable and not merely existent. -/
noncomputable def IsEquiv1.inv {f : x ⟶ y} (h : IsEquiv1 f) : y ⟶ x := h.choose

theorem IsEquiv1.nonempty_comp_inv {f : x ⟶ y} (h : IsEquiv1 f) : Nonempty (f ≫ h.inv ≅ 𝟙 x) :=
  h.choose_spec.1

theorem IsEquiv1.nonempty_inv_comp {f : x ⟶ y} (h : IsEquiv1 f) : Nonempty (h.inv ≫ f ≅ 𝟙 y) :=
  h.choose_spec.2

theorem IsEquiv1.isEquiv1_inv {f : x ⟶ y} (h : IsEquiv1 f) : IsEquiv1 h.inv :=
  isEquiv1_of_inv h.nonempty_comp_inv.some h.nonempty_inv_comp.some

/-- **Isomorphic equivalences have isomorphic chosen quasi-inverses.** The connecting 1-cell of
the Snake Lemma inverts two of the three comparison equivalences, so its independence of the
choices made rests on this as much as on the uniqueness of the comparisons themselves. -/
theorem IsEquiv1.nonempty_iso_inv {f f' : x ⟶ y} (h : IsEquiv1 f) (h' : IsEquiv1 f')
    (θ : f ≅ f') : Nonempty (h.inv ≅ h'.inv) :=
  ⟨calc h.inv ≅ h.inv ≫ 𝟙 x := (ρ_ h.inv).symm
    _ ≅ h.inv ≫ f' ≫ h'.inv := Bicategory.whiskerLeftIso h.inv h'.nonempty_comp_inv.some.symm
    _ ≅ (h.inv ≫ f') ≫ h'.inv := (α_ h.inv f' h'.inv).symm
    _ ≅ (h.inv ≫ f) ≫ h'.inv := Bicategory.whiskerRightIso
        (Bicategory.whiskerLeftIso h.inv θ).symm h'.inv
    _ ≅ 𝟙 y ≫ h'.inv := Bicategory.whiskerRightIso h.nonempty_inv_comp.some h'.inv
    _ ≅ h'.inv := λ_ h'.inv⟩

/-- Being an equivalence is invariant under invertible 2-cells. -/
theorem IsEquiv1.of_iso {f f' : x ⟶ y} (θ : f ≅ f') (h : IsEquiv1 f) : IsEquiv1 f' := by
  obtain ⟨g, ⟨η⟩, ⟨ε⟩⟩ := h
  exact ⟨g, ⟨Bicategory.whiskerRightIso θ.symm g ≪≫ η⟩,
    ⟨Bicategory.whiskerLeftIso g θ.symm ≪≫ ε⟩⟩

end Cancellation

section Strict

variable [Bicategory.Strict B] {x y z : B}

/-- Equivalences are closed under composition. -/
theorem IsEquiv1.comp {f : x ⟶ y} {g : y ⟶ z} (hf : IsEquiv1 f) (hg : IsEquiv1 g) :
    IsEquiv1 (f ≫ g) := by
  obtain ⟨f', ⟨η⟩, ⟨ε⟩⟩ := hf
  obtain ⟨g', ⟨η'⟩, ⟨ε'⟩⟩ := hg
  refine ⟨g' ≫ f', ⟨?_⟩, ⟨?_⟩⟩
  · calc (f ≫ g) ≫ g' ≫ f' ≅ f ≫ (g ≫ g') ≫ f' := eqToIso (by simp)
      _ ≅ f ≫ 𝟙 y ≫ f' := Bicategory.whiskerLeftIso f (Bicategory.whiskerRightIso η' f')
      _ ≅ f ≫ f' := eqToIso (by simp)
      _ ≅ 𝟙 x := η
  · calc (g' ≫ f') ≫ f ≫ g ≅ g' ≫ (f' ≫ f) ≫ g := eqToIso (by simp)
      _ ≅ g' ≫ 𝟙 y ≫ g := Bicategory.whiskerLeftIso g' (Bicategory.whiskerRightIso ε g)
      _ ≅ g' ≫ g := eqToIso (by simp)
      _ ≅ 𝟙 z := ε'

end Strict

section LocallyDiscrete

variable {C : Type u} [Category.{v} C] {x y : C}

/-- **The discretisation.** In a locally discrete 2-category, a 1-cell is a 2-monomorphism
exactly when it is a monomorphism of the underlying category. -/
theorem isTwoMono_locallyDiscrete_iff (f : LocallyDiscrete.mk x ⟶ LocallyDiscrete.mk y) :
    IsTwoMono f ↔ Mono f.as := by
  constructor
  · intro _
    refine ⟨fun {c} u v huv => ?_⟩
    have h : (⟨u⟩ : LocallyDiscrete.mk c ⟶ LocallyDiscrete.mk x) ≫ f = (⟨v⟩ : _) ≫ f :=
      Discrete.ext huv
    obtain ⟨η, -⟩ :=
      Functor.Full.map_surjective (F := Bicategory.postcomp (LocallyDiscrete.mk c) f) (eqToHom h)
    exact congrArg Discrete.as (LocallyDiscrete.eq_of_hom η)
  · intro hf
    refine ⟨fun w => ⟨fun {u v} η => ?_⟩, fun w => ⟨fun _ => Subsingleton.elim _ _⟩⟩
    refine ⟨eqToHom (Discrete.ext (hf.right_cancellation u.as v.as ?_)), Subsingleton.elim _ _⟩
    exact congrArg Discrete.as (LocallyDiscrete.eq_of_hom η)

/-- **The discretisation, dually.** In a locally discrete 2-category, a 1-cell is a
2-epimorphism exactly when it is an epimorphism of the underlying category. -/
theorem isTwoEpi_locallyDiscrete_iff (f : LocallyDiscrete.mk x ⟶ LocallyDiscrete.mk y) :
    IsTwoEpi f ↔ Epi f.as := by
  constructor
  · intro _
    refine ⟨fun {c} u v huv => ?_⟩
    have h : f ≫ (⟨u⟩ : LocallyDiscrete.mk y ⟶ LocallyDiscrete.mk c) = f ≫ (⟨v⟩ : _) :=
      Discrete.ext huv
    obtain ⟨η, -⟩ :=
      Functor.Full.map_surjective (F := Bicategory.precomp (LocallyDiscrete.mk c) f) (eqToHom h)
    exact congrArg Discrete.as (LocallyDiscrete.eq_of_hom η)
  · intro hf
    refine ⟨fun w => ⟨fun {u v} η => ?_⟩, fun w => ⟨fun _ => Subsingleton.elim _ _⟩⟩
    refine ⟨eqToHom (Discrete.ext (hf.left_cancellation u.as v.as ?_)), Subsingleton.elim _ _⟩
    exact congrArg Discrete.as (LocallyDiscrete.eq_of_hom η)

end LocallyDiscrete

section Representable

variable {x y : B}

/-- **Lemma 2.15 `L:RepEquiv`.** A 1-cell is an equivalence exactly when precomposing with it is
an equivalence of hom-categories, and exactly when postcomposing with it is.

The forward implications are the paper's: whiskering with a quasi-inverse supplies one for each
functor, and here that is assembled from `precompCompIso`, `precompMapIso` and `precompIdIso`
without touching a naturality square. The converses take `Z` to be the domain, where essential
surjectivity applied to an identity produces the quasi-inverse, and then the codomain, where full
faithfulness lifts the resulting invertible 2-cell. -/
theorem isEquiv1_tfae_representable (q : x ⟶ y) :
    List.TFAE [IsEquiv1 q,
      ∀ Z : B, (Bicategory.precomp Z q).IsEquivalence,
      ∀ Z : B, (Bicategory.postcomp Z q).IsEquivalence] := by
  tfae_have 1 → 2 := by
    rintro ⟨p, ⟨hqp⟩, ⟨hpq⟩⟩ Z
    exact (CategoryTheory.Equivalence.mk (Bicategory.precomp Z q) (Bicategory.precomp Z p)
      ((precompIdIso y Z).symm ≪≫ (precompMapIso Z hpq).symm ≪≫ precompCompIso Z p q)
      ((precompCompIso Z q p).symm ≪≫ precompMapIso Z hqp ≪≫
        precompIdIso x Z)).isEquivalence_functor
  tfae_have 1 → 3 := by
    rintro ⟨p, ⟨hqp⟩, ⟨hpq⟩⟩ Z
    exact (CategoryTheory.Equivalence.mk (Bicategory.postcomp Z q) (Bicategory.postcomp Z p)
      ((postcompIdIso Z x).symm ≪≫ (postcompMapIso Z hqp).symm ≪≫
        (postcompCompIso Z q p).symm)
      (postcompCompIso Z p q ≪≫ postcompMapIso Z hpq ≪≫
        postcompIdIso Z y)).isEquivalence_functor
  tfae_have 2 → 1 := by
    intro h
    haveI := h x
    haveI := h y
    refine ⟨(Bicategory.precomp x q).objPreimage (𝟙 x),
      ⟨(Bicategory.precomp x q).objObjPreimageIso (𝟙 x)⟩, ⟨?_⟩⟩
    set p := (Bicategory.precomp x q).objPreimage (𝟙 x)
    have hqp : q ≫ p ≅ 𝟙 x := (Bicategory.precomp x q).objObjPreimageIso (𝟙 x)
    refine (Bicategory.precomp y q).preimageIso ?_
    change q ≫ p ≫ q ≅ q ≫ 𝟙 y
    exact (Bicategory.associator q p q).symm ≪≫ Bicategory.whiskerRightIso hqp q ≪≫
      Bicategory.leftUnitor q ≪≫ (Bicategory.rightUnitor q).symm
  tfae_have 3 → 1 := by
    intro h
    haveI := h x
    haveI := h y
    refine ⟨(Bicategory.postcomp y q).objPreimage (𝟙 y), ⟨?_⟩,
      ⟨(Bicategory.postcomp y q).objObjPreimageIso (𝟙 y)⟩⟩
    set p := (Bicategory.postcomp y q).objPreimage (𝟙 y)
    have hpq : p ≫ q ≅ 𝟙 y := (Bicategory.postcomp y q).objObjPreimageIso (𝟙 y)
    refine (Bicategory.postcomp x q).preimageIso ?_
    change (q ≫ p) ≫ q ≅ 𝟙 x ≫ q
    exact Bicategory.associator q p q ≪≫ Bicategory.whiskerLeftIso q hpq ≪≫
      Bicategory.rightUnitor q ≪≫ (Bicategory.leftUnitor q).symm
  tfae_finish

end Representable

end SnakeLean
