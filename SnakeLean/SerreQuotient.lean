/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.SerreSubcategory

/-!
# (SAT) descends to a Serre quotient

This module supplies the second half of Proposition 8.16 `P:SATclosed`: condition (SAT) is
inherited by Serre quotients.

Mathlib has the Serre quotient only as a localisation, and not the fact that it is abelian --- that
is listed as future work in `Mathlib/CategoryTheory/Abelian/SerreClass/Basic.lean`. So the quotient
enters here as a hypothesis, `IsSerreQuotient`, and the point of the module is how little of it the
conclusion consumes.

Of the three fields of `IsSerreQuotient`, two are bookkeeping: the projection is essentially
surjective and it annihilates `S`. The third, `isSerreClass_map`, is one half of Gabriel's
correspondence: a Serre class of `A` containing `S` pushes forward to a Serre class of `A / S`.
That is the one thing the paper's proof of `P:SATclosed` takes from Gabriel, and the proof below
is the paper's: pull the two Serre classes back to `A`, saturate there, push the answer forward
along the exact `q` --- a span witnessing membership upstairs becomes one downstairs, the kernels
and cokernels of the images being the images of the kernels and cokernels --- and compare with
the join through Proposition 8.9 `P:Saturation`.

## Main results

* `IsSerreQuotient` --- what a Serre quotient is asked to supply.
* `condSAT_of_isSerreQuotient` --- (SAT) is inherited by Serre quotients.
-/

universe v v' u u'

namespace CategoryTheory

open Limits ZeroObject ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- **What a Serre quotient supplies.** `q : A ⥤ D` is exact --- carried by the instance
arguments of the results below --- essentially surjective, annihilates `S`, and pushes Serre
classes containing `S` forward to Serre classes.

The last condition is one half of Gabriel's correspondence between the Serre subcategories of
`A / S` and the Serre subcategories of `A` containing `S`. Mathlib does not yet have the abelian
structure on `A / S`, so this cannot be proved here; it is stated as a hypothesis, and
`condSAT_of_isSerreQuotient` consumes nothing else. -/
structure IsSerreQuotient (S : ObjectProperty A) [S.IsSerreClass] (q : A ⥤ D) : Prop where
  /-- Every object of the quotient comes from an object upstairs. -/
  essSurj : q.EssSurj
  /-- The projection annihilates the Serre class it is taken modulo. -/
  isZero_map_of_prop : ∀ ⦃X : A⦄, S X → IsZero (q.obj X)
  /-- A Serre class containing `S` has a Serre class as its essential image. -/
  isSerreClass_map (R : ObjectProperty A) [R.IsSerreClass] (hR : S ≤ R) :
    (R.map q).IsSerreClass

variable {S : ObjectProperty A} [S.IsSerreClass] {q : A ⥤ D}
  [q.PreservesZeroMorphisms] [PreservesFiniteLimits q] [PreservesFiniteColimits q]

/-- **(SAT) is inherited by Serre quotients.** This is the second half of Proposition 8.16
`P:SATclosed`.

The argument is the one used for Serre subcategories, run through `q` instead of through the
inclusion. Pull `K'` and `T'` back to Serre classes `K` and `T` of `A`, both containing `S`; the
`T`-saturation of `K` is a Serre class by hypothesis, so its image under `q` is one too. That
image contains `K'` and `T'`, hence their join; and it is contained in the `T'`-saturation of
`K'`, since `q` carries the span witnessing membership upstairs to one witnessing it
downstairs. -/
theorem condSAT_of_isSerreQuotient (hq : IsSerreQuotient S q) (h : CondSAT A) : CondSAT D := by
  intro T' K' _ _
  haveI := hq.essSurj
  have hST : S ≤ T'.inverseImage q := fun _ hX => T'.prop_of_isZero (hq.isZero_map_of_prop hX)
  haveI := h (T'.inverseImage q) (K'.inverseImage q)
  haveI := hq.isSerreClass_map (serreSaturation (T'.inverseImage q) (K'.inverseImage q))
    (hST.trans (serre_le_serreSaturation _ _))
  refine (isSerreClass_serreSaturation_iff T' K').2
    (le_antisymm (serreSaturation_le_serreJoin T' K') ?_)
  refine le_trans (K'.serreJoin_le T'
    (R := (serreSaturation (T'.inverseImage q) (K'.inverseImage q)).map q) inferInstance
    (fun X' hX' => ?_) (fun X' hX' => ?_)) ?_
  · exact ⟨q.objPreimage X', le_serreSaturation _ _ _
      (K'.prop_of_iso (q.objObjPreimageIso X').symm hX'), ⟨q.objObjPreimageIso X'⟩⟩
  · exact ⟨q.objPreimage X', serre_le_serreSaturation _ _ _
      (T'.prop_of_iso (q.objObjPreimageIso X').symm hX'), ⟨q.objObjPreimageIso X'⟩⟩
  rintro X' ⟨M, ⟨A₀, D₀, f, g, hA₀, hf, hg⟩, ⟨e⟩⟩
  refine serreSaturation_of_iso T' K' e ⟨q.obj A₀, q.obj D₀, q.map f, q.map g, hA₀, ?_, ?_⟩
  · exact ⟨T'.prop_of_iso (PreservesKernel.iso q f) hf.1,
      T'.prop_of_iso (PreservesCokernel.iso q f) hf.2⟩
  · exact ⟨T'.prop_of_iso (PreservesKernel.iso q g) hg.1,
      T'.prop_of_iso (PreservesCokernel.iso q g) hg.2⟩

end CategoryTheory
