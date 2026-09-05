/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Bicategory.Opposites
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# The 1-cell dual

Every result of the paper comes in a dual pair, and the paper discharges the second half by
saying "dually". This development makes that word literal: each notion is transported through
Mathlib's 1-cell dual
`Bᵒᵖ` in the module that defines it, and every dual statement is then obtained by applying the
primal one in `Bᵒᵖ`.

This module is the foundation of that arrangement. It contains the one thing Mathlib does not
supply and every other module needs.

## What Mathlib supplies, and what it does not

`Mathlib.CategoryTheory.Bicategory.Opposites` builds `Bᵒᵖ`: the objects of `B`, the 1-cells
reversed, and the 2-cells **not** reversed. It supplies the `Bicategory` instance, `op2`/`unop2`
on 2-cells and on isomorphisms, and the comparison lemmas for the unitors and the associator. It
does **not** supply `Bicategory.Strict Bᵒᵖ`, which every module here assumes; `strictOp` is that
instance. Its three interesting fields go through `op2_eqToIso`, which is the observation that
`op2` sends `eqToIso` to `eqToIso`.

## Which notions are self-dual and which swap

Under `ᵒᵖ`, 2-monomorphisms and 2-epimorphisms swap, as do 2-kernels and 2-cokernels, normal
2-monomorphisms and normal 2-epimorphisms, and the two halves of a short 2-exact sequence. Being
null, essentially null, trivial, an equivalence, normal, or antinormal is self-dual, as are
2-z-exactness, homological self-duality and 2-di-exactness. That last group is the useful one: a
theorem hypothesising `IsHSD O` can be applied in `Bᵒᵖ` without further ado.

## Orientation

Objects go `X ↦ op X` and 1-cells `f ↦ f.op`, so a 1-cell `f : A ⟶ A'` of `B` becomes
`f.op : op A' ⟶ op A`. Composites reverse: `(f ≫ g).op = g.op ≫ f.op`, definitionally. The
transports are therefore all of the form "`P O f` in `B` iff `Pᵒᵖ (op O) f.op` in `Bᵒᵖ`", with
both directions written out; the reverse direction is not obtained from the forward one by a
second dualisation, since `Bᵒᵖᵒᵖ` is only isomorphic to `B`, not equal to it.

## Where the transports live

| notion | module |
| --- | --- |
| 2-monomorphisms, 2-epimorphisms, equivalences | `SnakeLean.Mono` |
| null 1-cells, strong bizero objects | `SnakeLean.Null` |
| essentially null 1-cells, bizero objects, 2-kernels, 2-cokernels | `SnakeLean.Kernel` |
| trivial objects, normal 2-monos and 2-epis, short 2-exact sequences | `SnakeLean.Exact` |
| normal and antinormal 1-cells | `SnakeLean.Normal` |
| 2-z-exactness | `SnakeLean.ZExact` |
| homological self-duality | `SnakeLean.Dinversion` |
| 2-di-exactness | `SnakeLean.DiExact` |

## Main results

* `op2_eqToIso` — the 1-cell dual sends `eqToIso` to `eqToIso`.
* `strictOp` — the strictness instance Mathlib lacks.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory Opposite Bicategory.Opposite

variable {B : Type u} [Bicategory.{w, v} B]

/-- The 1-cell dual sends `eqToIso` to `eqToIso`. This is what makes the three isomorphism fields
of `Bicategory.Strict Bᵒᵖ` go through. -/
theorem op2_eqToIso {a b : B} {f g : a ⟶ b} (p : f = g) :
    (eqToIso p).op2 = eqToIso (congrArg Quiver.Hom.op p) := by
  cases p; rfl

/-- **The 1-cell dual of a strict bicategory is strict.** Mathlib builds `Bᵒᵖ` but not this
instance, and every module of this development assumes strictness. -/
instance strictOp [Bicategory.Strict B] : Bicategory.Strict Bᵒᵖ where
  id_comp f := by apply Quiver.Hom.unop_inj; simp
  comp_id f := by apply Quiver.Hom.unop_inj; simp
  assoc f g h := by apply Quiver.Hom.unop_inj; simp
  leftUnitor_eqToIso f := by
    rw [show f = f.unop.op from rfl, ← Bicategory.Opposite.op2_rightUnitor,
      Bicategory.Strict.rightUnitor_eqToIso, op2_eqToIso]
  rightUnitor_eqToIso f := by
    rw [show f = f.unop.op from rfl, ← Bicategory.Opposite.op2_leftUnitor,
      Bicategory.Strict.leftUnitor_eqToIso, op2_eqToIso]
  associator_eqToIso f g h := by
    rw [show f = f.unop.op from rfl, show g = g.unop.op from rfl, show h = h.unop.op from rfl]
    have key := Bicategory.Opposite.op2_associator h.unop g.unop f.unop
    rw [Bicategory.Strict.associator_eqToIso, op2_eqToIso] at key
    rw [← Iso.symm_symm_eq (α_ f.unop.op g.unop.op h.unop.op), ← key]
    rfl

end SnakeLean
