/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.Op
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Null 1-cells and strong bizero objects

This module formalises the part of Section 2 of *A two-categorical Snake Lemma* that concerns
null 1-cells, and proves Lemma 2.6 `L:UniqueNull`, the lemma behind every appeal in the paper to
a structure 2-cell being "the" one induced by a universal property.

The paper's `0` is a **bizero object**: an object `Z` such that every hom-category into it and
out of it is equivalent to the terminal category. It is **strong** when any two parallel 1-cells
that factor through `Z` admit exactly one 2-cell between them. A 1-cell is **null** when it
factors through `Z`.

## Main result

`IsNull.eq_of_isIso`: in a 2-category with a strong bizero object, a 1-cell admits **at most
one** 2-cell into a given null 1-cell, as soon as one such 2-cell is invertible. In particular a
2-cell into a null codomain is determined by any invertible one parallel to it.

This is Lemma 2.6 `L:UniqueNull`, which the paper calls the precise form of the slogan that a
strong bizero object guarantees that all 2-cells are null — its point being that `x` itself is
not asked to be null. Its most useful consequence is Proposition 3.26 `P:CoherenceFree`: the
coherence condition one might expect Definition 3.25 `Def:morphism of SES` to impose on a
morphism of short 2-exact sequences,
```
(κ ⋆ f) · (q ⋆ φ_K) = (h ⋆ κ') · (φ_Q⁻¹ ⋆ k'),
```
holds for every choice of the data: both of its sides are invertible 2-cells `q ∘ g ∘ k' ⟹ 0`
with the same domain and the same null codomain, so `IsNull.eq_of_isIso` identifies them. No
hypothesis beyond strongness of the bizero object is needed.

## Hypotheses

The lemma is stated at the paper's hypotheses and a little below them: it needs neither the
hom-categories of `Z` to be equivalent to the terminal category nor the 2-category to be strict,
only that 2-cells between parallel null 1-cells are unique.

## Non-vacuity

`isStrong_locallyDiscrete`: a zero object of an ordinary category is a strong bizero object of
the associated locally discrete 2-category. This is the paper's remark that in a 1-category
there is no difference between a bizero object and a strong bizero object.

## Not formalised

The bizero condition itself (that the hom-categories are equivalent to the terminal category)
is not defined here, because no result below consumes it; 2-kernels, 2-cokernels and short
2-exact sequences are left to later modules.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- A 1-cell is **null relative to `Z`** when it factors through `Z`. -/
def IsNull (Z : B) {a b : B} (f : a ⟶ b) : Prop :=
  ∃ (t : a ⟶ Z) (i : Z ⟶ b), f = t ≫ i

/-- `Z` is a **strong** bizero object when any two parallel 1-cells that factor through `Z`
admit exactly one 2-cell between them. -/
class IsStrong (Z : B) : Prop where
  /-- There is a 2-cell between any two parallel null 1-cells. -/
  nonempty_hom {a b : B} {m n : a ⟶ b} (hm : IsNull Z m) (hn : IsNull Z n) : Nonempty (m ⟶ n)
  /-- There is at most one 2-cell between any two parallel null 1-cells. -/
  subsingleton_hom {a b : B} {m n : a ⟶ b} (hm : IsNull Z m) (hn : IsNull Z n) :
    Subsingleton (m ⟶ n)

section Strong

variable {Z : B} [IsStrong Z] {a b : B}

/-- The only endo-2-cell of a null 1-cell is the identity. -/
theorem IsNull.eq_id {n : a ⟶ b} (hn : IsNull Z n) (γ : n ⟶ n) : γ = 𝟙 n :=
  (IsStrong.subsingleton_hom hn hn).elim γ (𝟙 n)

/-- **Key lemma.** A 1-cell admits at most one 2-cell into a null 1-cell, as soon as one such
2-cell is invertible. -/
theorem IsNull.eq_of_isIso {x n : a ⟶ b} (hn : IsNull Z n) (β : x ⟶ n) [IsIso β] (γ : x ⟶ n) :
    γ = β :=
  calc γ = 𝟙 x ≫ γ := (Category.id_comp γ).symm
    _ = (β ≫ inv β) ≫ γ := by rw [IsIso.hom_inv_id]
    _ = β ≫ inv β ≫ γ := Category.assoc _ _ _
    _ = β ≫ 𝟙 n := by rw [hn.eq_id (inv β ≫ γ)]
    _ = β := Category.comp_id β

/-- Once one 2-cell into a null 1-cell is invertible, there is only one 2-cell at all. -/
theorem IsNull.subsingleton_hom_of_isIso {x n : a ⟶ b} (hn : IsNull Z n) (β : x ⟶ n) [IsIso β] :
    Subsingleton (x ⟶ n) :=
  ⟨fun γ δ => (hn.eq_of_isIso β γ).trans (hn.eq_of_isIso β δ).symm⟩

/-- **The coherence condition is automatic.** A 2-cell into a null codomain equals any invertible
2-cell parallel to it; in particular any two such invertible 2-cells agree. -/
theorem IsNull.eq_of_isIso_of_isIso {x n : a ⟶ b} (hn : IsNull Z n) (α β : x ⟶ n) [IsIso α] :
    α = β :=
  (hn.eq_of_isIso α β).symm

/-- The invertible-2-cell form: a 1-cell carries at most one isomorphism to a null 1-cell. -/
theorem IsNull.iso_ext {x n : a ⟶ b} (hn : IsNull Z n) (α β : x ≅ n) : α = β :=
  Iso.ext (hn.eq_of_isIso α.hom β.hom).symm

/-- Every 2-cell between parallel null 1-cells is invertible. -/
theorem IsNull.isIso {m n : a ⟶ b} (hm : IsNull Z m) (hn : IsNull Z n) (η : m ⟶ n) : IsIso η := by
  obtain ⟨θ⟩ := IsStrong.nonempty_hom hn hm
  exact ⟨θ, hm.eq_id _, hn.eq_id _⟩

/-- Parallel null 1-cells are isomorphic, by a unique 2-cell. -/
theorem IsNull.nonempty_iso {m n : a ⟶ b} (hm : IsNull Z m) (hn : IsNull Z n) :
    Nonempty (m ≅ n) := by
  obtain ⟨η⟩ := IsStrong.nonempty_hom hm hn
  obtain ⟨θ⟩ := IsStrong.nonempty_hom hn hm
  exact ⟨η, θ, hm.eq_id _, hn.eq_id _⟩

end Strong

section Strict

variable [Bicategory.Strict B] {Z : B}

/-- Null 1-cells absorb composition on the left. -/
theorem IsNull.comp_left {a b c : B} (f : a ⟶ b) {n : b ⟶ c} (hn : IsNull Z n) :
    IsNull Z (f ≫ n) := by
  obtain ⟨t, i, rfl⟩ := hn
  exact ⟨f ≫ t, i, (Bicategory.Strict.assoc f t i).symm⟩

/-- Null 1-cells absorb composition on the right. -/
theorem IsNull.comp_right {a b c : B} {n : a ⟶ b} (hn : IsNull Z n) (f : b ⟶ c) :
    IsNull Z (n ≫ f) := by
  obtain ⟨t, i, rfl⟩ := hn
  exact ⟨t, i ≫ f, Bicategory.Strict.assoc t i f⟩

/-- Every 1-cell into `Z` is null. -/
theorem isNull_to {a : B} (t : a ⟶ Z) : IsNull Z t :=
  ⟨t, 𝟙 Z, (Bicategory.Strict.comp_id t).symm⟩

/-- Every 1-cell out of `Z` is null. -/
theorem isNull_from {b : B} (i : Z ⟶ b) : IsNull Z i :=
  ⟨𝟙 Z, i, (Bicategory.Strict.id_comp i).symm⟩

end Strict

section LocallyDiscrete

variable {C : Type u} [Category.{v} C] {Z : C}

/-- Parallel null 1-cells of a locally discrete 2-category over a category with a zero object
are equal. -/
theorem eq_of_isNull_locallyDiscrete (hZ : Limits.IsZero Z) {a b : LocallyDiscrete C}
    {m n : a ⟶ b} (hm : IsNull (LocallyDiscrete.mk Z) m) (hn : IsNull (LocallyDiscrete.mk Z) n) :
    m = n := by
  obtain ⟨t, i, rfl⟩ := hm
  obtain ⟨t', i', rfl⟩ := hn
  obtain rfl : t = t' := Discrete.ext (hZ.eq_of_tgt t.as t'.as)
  obtain rfl : i = i' := Discrete.ext (hZ.eq_of_src i.as i'.as)
  rfl

/-- **Non-vacuity.** A zero object of an ordinary category is a strong bizero object of the
associated locally discrete 2-category: in a 1-category there is no difference between a bizero
object and a strong bizero object. -/
theorem isStrong_locallyDiscrete (hZ : Limits.IsZero Z) : IsStrong (LocallyDiscrete.mk Z) where
  nonempty_hom hm hn := ⟨eqToHom (eq_of_isNull_locallyDiscrete hZ hm hn)⟩
  subsingleton_hom _ _ := inferInstance

end LocallyDiscrete

section Opposite

open Opposite Bicategory.Opposite

variable {Z : B} {a b : B}

/-- Being null is self-dual. Neither side mentions a `HasBizero` instance. -/
theorem isNull_op {f : a ⟶ b} (h : IsNull Z f) : IsNull (op Z) f.op := by
  obtain ⟨t, i, rfl⟩ := h
  exact ⟨i.op, t.op, rfl⟩

theorem isNull_of_op {f : a ⟶ b} (h : IsNull (op Z) f.op) : IsNull Z f := by
  obtain ⟨t, i, hf⟩ := h
  exact ⟨i.unop, t.unop, Quiver.Hom.op_inj hf⟩

theorem isNull_op_iff (f : a ⟶ b) : IsNull (op Z) f.op ↔ IsNull Z f :=
  ⟨isNull_of_op, isNull_op⟩

/-- A strong bizero object stays strong in the dual. -/
instance isStrongOp (Z : B) [IsStrong Z] : IsStrong (op Z) where
  nonempty_hom hm hn :=
    ⟨op2 (IsStrong.nonempty_hom (Z := Z) (isNull_of_op (by simpa using hm))
      (isNull_of_op (by simpa using hn))).some⟩
  subsingleton_hom hm hn :=
    ⟨fun η η' => by
      have := (IsStrong.subsingleton_hom (Z := Z) (isNull_of_op (by simpa using hm))
        (isNull_of_op (by simpa using hn))).allEq η.unop2 η'.unop2
      simpa using congrArg op2 this⟩

end Opposite

end SnakeLean
