/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.DiExact
import SnakeLean.ModularPair
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.ModularLattice
import Mathlib.CategoryTheory.Category.Preorder

/-!
# The locally ordered model: classes of complete lattices

Section 8.30 `SS:ModelLattices` and Proposition 9.29 `P:SupClass`. Complete
lattices, join-preserving maps and instances of the pointwise order form a locally ordered
2-category, and the constructions of the paper stay inside any **class** of complete lattices
closed under down-segments, up-segments and order isomorphism, and containing a one-element
lattice: that is `LatticeClass`, and `SupOf C` is the resulting 2-category. Two members of the
family matter. Taking all complete lattices gives the paper's `Sup`; taking the modular ones
gives `ModSup`, which is 2-di-exact, and taking the lattices of closed subspaces of Hilbert
spaces would give `Suphil`.

The 2-kernel of `f : L ⟶ M` is the down-segment `↓(⋁{x | f x = ⊥})` (`isTwoKernel_segIncl`),
the 2-cokernel is `x ↦ x ⊔ f ⊤` onto the up-segment `↑(f ⊤)` (`isTwoCokernel_upProj`), and up
to isomorphism these are all the normal 2-monomorphisms and normal 2-epimorphisms
(`exists_isEquiv1_of_isTwoKernel`, `exists_isEquiv1_of_isTwoCokernel` — Corollary 8.34
`C:SupNormal`). An antinormal 1-cell is therefore, up to isomorphism, a map
`c_{a,b} : ↓a ⟶ ↑b`, `x ↦ x ⊔ b`, and **`c_{a,b}` is normal exactly when the transposition
`[a ⊓ b, a] → [b, a ⊔ b]` is invertible** (`isNormal_segIncl_comp_upProj_iff`), which is
Proposition 8.35 `P:SupAntinormal` in both directions. Condition (DI2) is therefore Dedekind's
transposition principle (Proposition 8.36 `P:SupModular`), and modularity of every member gives
it (`twoDiExact_of_forall_isModularLattice`; for the modular lattices, Theorem 8.37
`T:LatticeModel`). Condition (DPN) becomes transposition-symmetry, and that is
`SnakeLean.LatticeNSD`.

## Main results

* `LatticeClass`, `SupOf` — the class and its 2-category; `bicategorySup`, `strictSup`.
* `isStrongSup` — the one-element lattice is a strong bizero object (Proposition 8.32
  `P:SupBizero`).
* `twoZExactSup` — condition (DI1) (Proposition 8.33 `P:SupKernels`).
* `isNormal_segIncl_comp_upProj_iff` — Proposition 8.35 `P:SupAntinormal`, in both directions;
  with `isModularLattice_iff_forall_transposes` of `SnakeLean.ModularPair` it is
  Proposition 8.36 `P:SupModular`.
* `twoDiExact_of_forall_isModularLattice`, `twoDiExactModSup` — condition (DI2)
  (Theorem 8.37 `T:LatticeModel`); `isModularLattice_of_twoDiExact` and
  `twoDiExact_iff_forall_isModularLattice` — its converse, the (DI2) half of Proposition 9.29
  `P:SupClass`.
* `allClass`, `SupAll` — the class of all complete lattices, the paper's `Sup`.
* `isHSD_modSup`, `isPureSnake_modSup` — hence every result of Sections 2 to 6 applies to
  `ModSup`, `exists_snakeGeneral` included.

## Elsewhere, and not formalised

Both directions of both biconditionals of Proposition 9.29 `P:SupClass` are checked
(`twoDiExact_iff_forall_isModularLattice` here, `dpn_iff_forall_transpositionSymmetric` in
`SnakeLean.LatticeNSD`), as are the two negative clauses — that the class of *all* complete
lattices (`SupAll` below) is neither 2-di-exact (Proposition 8.36) nor (DPN) (Proposition 8.38
`P:SupNotDPN`) — in `SnakeLean.Pentagon`, where the pentagon is built as a complete lattice and
both facts are read off `isNormal_segIncl_comp_upProj_iff`. Not formalised: the element-level
reading of the Snake Lemma in `ModSup` that Remark 8.40 `Rem Lattice Snake` gives, which would be
the lattice analogue of `SnakeLean.Classical`; and Remark 8.43 `Rem Lattice Sharp`.
-/

universe u

namespace SnakeLean

open CategoryTheory Bicategory Set

/-! ## Up-segments as complete lattices

Mathlib provides `CompleteLattice (Set.Iic a)` and `IsModularLattice (Set.Iic a)`; for
`Set.Ici b` it provides the `Lattice`, `OrderBot` and `OrderTop` instances but not the
complete lattice structure, which we supply. Joins are computed in the ambient lattice, with
`b` joined in so that the empty join is the bottom element `b`. -/

section Ici

variable {α : Type u} [CompleteLattice α]

instance iciCompleteLattice (b : α) : CompleteLattice (Set.Ici b) where
  __ := (inferInstance : Lattice (Set.Ici b))
  __ := (inferInstance : OrderBot (Set.Ici b))
  __ := (inferInstance : OrderTop (Set.Ici b))
  sSup S := ⟨sSup ((↑) '' S) ⊔ b, le_sup_right⟩
  le_sSup S x hx :=
    show (x : α) ≤ sSup ((↑) '' S) ⊔ b from
      le_sup_of_le_left (le_sSup (mem_image_of_mem _ hx))
  sSup_le S x hx :=
    show sSup ((↑) '' S) ⊔ b ≤ (x : α) from
      sup_le (sSup_le (by rintro y ⟨z, hz, rfl⟩; exact hx z hz)) x.2
  sInf S := ⟨sInf ((↑) '' S) ⊔ b, le_sup_right⟩
  sInf_le S x hx :=
    show sInf ((↑) '' S) ⊔ b ≤ (x : α) from
      sup_le (sInf_le (mem_image_of_mem _ hx)) x.2
  le_sInf S x hx :=
    show (x : α) ≤ sInf ((↑) '' S) ⊔ b from
      le_sup_of_le_left (le_sInf (by rintro y ⟨z, hz, rfl⟩; exact hx z hz))

theorem Ici.coe_sSup' (b : α) (S : Set (Set.Ici b)) :
    ((sSup S : Set.Ici b) : α) = sSup ((↑) '' S) ⊔ b :=
  rfl

instance iciIsModularLattice (b : α) [IsModularLattice α] :
    IsModularLattice (Set.Ici b) := by
  refine ⟨fun {x} y {z} h => ?_⟩
  change (((x ⊔ y) ⊓ z : Set.Ici b) : α) ≤ ((x ⊔ y ⊓ z : Set.Ici b) : α)
  rw [Ici.coe_inf, Ici.coe_sup, Ici.coe_sup, Ici.coe_inf]
  exact IsModularLattice.sup_inf_le_assoc_of_le _ h

end Ici

/-! ## The 2-category -/

/-- **A class of complete lattices**, in the sense of Proposition 9.29 `P:SupClass`: a property
of complete
lattices closed under order isomorphism and under passing to the down-segments and up-segments
of its members, and containing a one-element lattice. Those are exactly the closure conditions
under which the constructions below stay inside the class. -/
structure LatticeClass : Type (u + 1) where
  /-- The class, as a property of complete lattices. -/
  Mem : (α : Type u) → [CompleteLattice α] → Prop
  /-- It contains the one-element lattice. -/
  mem_punit : Mem PUnit
  /-- It is closed under down-segments. -/
  mem_iic : ∀ {α : Type u} [CompleteLattice α], Mem α → ∀ a : α, Mem ↥(Set.Iic a)
  /-- It is closed under up-segments. -/
  mem_ici : ∀ {α : Type u} [CompleteLattice α], Mem α → ∀ b : α, Mem ↥(Set.Ici b)
  /-- It is closed under order isomorphism. -/
  mem_of_orderIso : ∀ {α β : Type u} [CompleteLattice α] [CompleteLattice β],
    (α ≃o β) → Mem α → Mem β

variable {C : LatticeClass.{u}}

/-- An object of the 2-category: a complete lattice belonging to the class. -/
structure SupOf (C : LatticeClass.{u}) : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  [completeLattice : CompleteLattice carrier]
  /-- The carrier belongs to the class. -/
  mem : C.Mem carrier

attribute [instance] SupOf.completeLattice

instance : CoeSort (SupOf C) (Type u) :=
  ⟨SupOf.carrier⟩

/-- Any two parallel 2-cells coincide: the hom-categories are posets. -/
private theorem twocell_ext {X : Type u} [Preorder X] {x y : X} (α β : x ⟶ y) : α = β := by
  obtain ⟨⟨_⟩⟩ := α; obtain ⟨⟨_⟩⟩ := β; rfl

instance categoryStructSup : CategoryStruct.{u} (SupOf C) where
  Hom L M := sSupHom L.carrier M.carrier
  id L := sSupHom.id L.carrier
  comp f g := sSupHom.comp g f

instance instFunLikeHom {L M : (SupOf C)} : FunLike (L ⟶ M) L.carrier M.carrier :=
  inferInstanceAs (FunLike (sSupHom L.carrier M.carrier) L.carrier M.carrier)

instance instSSupHomClassHom {L M : (SupOf C)} :
    sSupHomClass (L ⟶ M) L.carrier M.carrier :=
  inferInstanceAs (sSupHomClass (sSupHom L.carrier M.carrier) L.carrier M.carrier)

instance instPartialOrderHom {L M : (SupOf C)} : PartialOrder (L ⟶ M) :=
  inferInstanceAs (PartialOrder (sSupHom L.carrier M.carrier))

instance instBotHomClassHom {L M : (SupOf C)} : BotHomClass (L ⟶ M) L.carrier M.carrier :=
  inferInstanceAs (BotHomClass (sSupHom L.carrier M.carrier) L.carrier M.carrier)

/-- Interpret a join-preserving map as a 1-cell. -/
def mkHom {L M : (SupOf C)} (f : sSupHom L.carrier M.carrier) : L ⟶ M := f

/-- **The locally ordered 2-category `Sup_C`** of Section 8.30 `SS:ModelLattices` and
Proposition 9.29 `P:SupClass`: objects the complete lattices of the class, 1-cells the
join-preserving maps, 2-cells the instances of the pointwise order. For the modular lattices it
is the `Supmod` of Theorem 8.37 `T:LatticeModel` (`ModSup`); for all complete lattices the
paper's `Sup` (`SupAll`). -/
instance bicategorySup : Bicategory.{u, u} (SupOf C) where
  toCategoryStruct := categoryStructSup
  homCategory L M := Preorder.smallCategory _
  whiskerLeft f g h η := homOfLE fun x => leOfHom η (f x)
  whiskerRight η h := homOfLE fun x => OrderHomClass.mono h (leOfHom η x)
  associator f g h := Iso.refl _
  leftUnitor f := Iso.refl _
  rightUnitor f := Iso.refl _
  whiskerLeft_id := by intros; exact twocell_ext _ _
  whiskerLeft_comp := by intros; exact twocell_ext _ _
  id_whiskerLeft := by intros; exact twocell_ext _ _
  comp_whiskerLeft := by intros; exact twocell_ext _ _
  id_whiskerRight := by intros; exact twocell_ext _ _
  comp_whiskerRight := by intros; exact twocell_ext _ _
  whiskerRight_id := by intros; exact twocell_ext _ _
  whiskerRight_comp := by intros; exact twocell_ext _ _
  whisker_assoc := by intros; exact twocell_ext _ _
  whisker_exchange := by intros; exact twocell_ext _ _
  pentagon := by intros; exact twocell_ext _ _
  triangle := by intros; exact twocell_ext _ _

/-- Composition of join-preserving maps is strictly associative and unital. -/
instance strictSup : Bicategory.Strict (SupOf C) where
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  leftUnitor_eqToIso _ := Iso.ext (twocell_ext _ _)
  rightUnitor_eqToIso _ := Iso.ext (twocell_ext _ _)
  associator_eqToIso _ _ _ := Iso.ext (twocell_ext _ _)

@[simp]
theorem comp_apply' {L M N : (SupOf C)} (f : L ⟶ M) (g : M ⟶ N) (x : L) :
    (f ≫ g) x = g (f x) :=
  rfl

/-- In a locally ordered 2-category, isomorphic 1-cells are equal. -/
theorem eq_of_iso_hom {L M : (SupOf C)} {f g : L ⟶ M} (θ : f ≅ g) : f = g :=
  le_antisymm (leOfHom θ.hom) (leOfHom θ.inv)

/-- A pointwise inequality of 1-cells is a 2-cell. -/
def twoCellOfLe {L M : (SupOf C)} {f g : L ⟶ M} (h : ∀ x, f x ≤ g x) : f ⟶ g :=
  homOfLE h

/-- A 2-cell is a pointwise inequality. -/
theorem le_of_twoCell {L M : (SupOf C)} {f g : L ⟶ M} (η : f ⟶ g) (x : L.carrier) :
    f x ≤ g x :=
  leOfHom η x

/-! ## The strong bizero object -/

/-- The one-element lattice. -/
abbrev zeroSup (C : LatticeClass.{u}) : (SupOf C) :=
  { carrier := PUnit, mem := C.mem_punit }

instance hasBizeroSup : HasBizero (zeroSup C) where
  toZero L := mkHom
    { toFun := fun _ => ⊥
      map_sSup' := fun _ => Subsingleton.elim _ _ }
  fromZero M := mkHom
    { toFun := fun _ => ⊥
      map_sSup' := fun S =>
        (le_antisymm (sSup_le (by rintro y ⟨x, _, rfl⟩; exact le_rfl)) bot_le).symm }

/-- A null 1-cell is the constant map at `⊥`. -/
theorem apply_eq_bot_of_isNull {L M : (SupOf C)} {n : L ⟶ M}
    (h : IsNull (zeroSup C) n) (x : L) : n x = ⊥ := by
  obtain ⟨t, i, rfl⟩ := h
  change i (t x) = ⊥
  rw [Subsingleton.elim (t x) ⊥, map_bot]

/-- Conversely, the constant map at `⊥` is null. -/
theorem isNull_of_forall_eq_bot {L M : (SupOf C)} {n : L ⟶ M}
    (h : ∀ x, n x = ⊥) : IsNull (zeroSup C) n :=
  ⟨HasBizero.toZero L, HasBizero.fromZero M, DFunLike.ext _ _ fun x => h x⟩

/-- **Proposition 8.32 `P:SupBizero`.** The one-element lattice is a strong bizero object: between
two parallel null 1-cells there is exactly one 2-cell, because they are equal and the hom-categories
are posets. -/
instance isStrongSup : IsStrong (zeroSup C) where
  nonempty_hom hm hn :=
    ⟨twoCellOfLe fun x => le_of_eq (by
      rw [apply_eq_bot_of_isNull hm x, apply_eq_bot_of_isNull hn x])⟩
  subsingleton_hom _ _ := ⟨fun α β => twocell_ext α β⟩

/-- Essential nullity is pointwise vanishing: in a locally ordered 2-category a 1-cell
isomorphic to a null 1-cell is that null 1-cell. -/
theorem isEssNull_iff_forall {L M : (SupOf C)} {f : L ⟶ M} :
    IsEssNull (zeroSup C) f ↔ ∀ x, f x = ⊥ := by
  constructor
  · rintro ⟨n, hn, ⟨θ⟩⟩ x
    rw [eq_of_iso_hom θ]
    exact apply_eq_bot_of_isNull hn x
  · intro h
    exact ⟨f, isNull_of_forall_eq_bot h, ⟨Iso.refl f⟩⟩

/-! ## Segments and the (co)kernel constructions -/

section Segments

variable {L : (SupOf C)}

/-- The down-segment `↓a`, an object of `SupOf C` by the class's closure under down-segments:
Mathlib provides the complete lattice structure (and modularity, for `ModSup`). -/
abbrev seg (a : L) : (SupOf C) :=
  { carrier := ↥(Set.Iic a), mem := C.mem_iic L.mem a }

/-- The up-segment `↑b`, an object of `SupOf C` by the closure under up-segments, through the
instances above. -/
abbrev upSeg (b : L) : (SupOf C) :=
  { carrier := ↥(Set.Ici b), mem := C.mem_ici L.mem b }

/-- The inclusion of a down-segment, as a 1-cell. -/
def segIncl (a : L) : seg a ⟶ L := mkHom
  { toFun := (↑)
    map_sSup' := fun S => by rw [Iic.coe_sSup] }

/-- Corestriction to a down-segment. -/
def segRestrict {Z : (SupOf C)} (f : Z ⟶ L) {a : L} (h : ∀ x, f x ≤ a) : Z ⟶ seg a := mkHom
  { toFun := fun x => ⟨f x, h x⟩
    map_sSup' := fun S => Subtype.ext (by
      change f (sSup S) = ((sSup _ : Set.Iic a) : L.carrier)
      rw [Iic.coe_sSup, image_image]
      exact map_sSup f S) }

/-- The join-projection onto an up-segment, `x ↦ x ⊔ b`. -/
def upProj (b : L) : L ⟶ upSeg b := mkHom
  { toFun := fun x => ⟨x ⊔ b, le_sup_right⟩
    map_sSup' := fun S => by
      apply Subtype.ext
      change sSup S ⊔ b = ((sSup _ : Set.Ici b) : L.carrier)
      rw [Ici.coe_sSup', image_image]
      refine le_antisymm (sup_le (sSup_le fun x hx => ?_) le_sup_right)
        (sup_le (sSup_le ?_) le_sup_right)
      · exact le_sup_of_le_left (le_trans le_sup_left (le_sSup ⟨x, hx, rfl⟩))
      · rintro y ⟨x, hx, rfl⟩
        exact sup_le_sup_right (le_sSup hx) b }

/-- Restriction of a 1-cell that kills `b` along the join-projection. -/
def upRestrict {Z : (SupOf C)} (f : L ⟶ Z) {b : L} (h : f b = ⊥) : upSeg b ⟶ Z := mkHom
  { toFun := fun y => f y
    map_sSup' := fun S => by
      change f ((sSup S : Set.Ici b) : L.carrier) = _
      rw [Ici.coe_sSup', map_sup, map_sSup, h, sup_bot_eq, image_image] }

@[simp]
theorem segIncl_apply (a : L) (x : seg a) : segIncl a x = (x : L.carrier) := rfl

@[simp]
theorem upProj_apply (b : L) (x : L) : ((upProj b x : Set.Ici b) : L.carrier) = x ⊔ b := rfl

/-- The 2-monomorphisms among the segment inclusions: postcomposition reflects the pointwise
order because the subtype order is the restricted one. -/
theorem isTwoMono_segIncl (a : L) : IsTwoMono (segIncl a) where
  full _ :=
    ⟨fun {u v} θ =>
      ⟨twoCellOfLe fun x => by
        have h1 : ((u x : Set.Iic a) : L.carrier) ≤ ((v x : Set.Iic a) : L.carrier) :=
          le_of_twoCell θ x
        exact Subtype.coe_le_coe.mp h1, twocell_ext _ _⟩⟩
  faithful _ := ⟨fun _ => twocell_ext _ _⟩

/-- The join-projections are 2-epimorphisms: they are surjective. -/
theorem isTwoEpi_upProj (b : L) : IsTwoEpi (upProj b) where
  full _ :=
    ⟨fun {u v} θ =>
      ⟨twoCellOfLe fun y => by
        have hy : upProj b (y : L.carrier) = y := Subtype.ext (sup_eq_left.mpr y.2)
        have h1 : u (upProj b (y : L.carrier)) ≤ v (upProj b (y : L.carrier)) :=
          le_of_twoCell θ (y : L.carrier)
        rwa [hy] at h1, twocell_ext _ _⟩⟩
  faithful _ := ⟨fun _ => twocell_ext _ _⟩

/-- The top of the kernel: `⋁ {x | f x = ⊥}`. -/
def kerElt {M : (SupOf C)} (f : L ⟶ M) : L :=
  sSup {x | f x = ⊥}

theorem apply_kerElt {M : (SupOf C)} (f : L ⟶ M) : f (kerElt f) = ⊥ := by
  rw [kerElt, map_sSup]
  refine le_bot_iff.mp (sSup_le ?_)
  rintro y ⟨x, hx, rfl⟩
  exact le_of_eq hx

theorem apply_eq_bot_of_le_kerElt {M : (SupOf C)} (f : L ⟶ M) {x : L}
    (h : x ≤ kerElt f) : f x = ⊥ :=
  le_bot_iff.mp (le_of_le_of_eq (OrderHomClass.mono f h) (apply_kerElt f))

theorem le_kerElt {M : (SupOf C)} (f : L ⟶ M) {x : L} (h : f x = ⊥) : x ≤ kerElt f :=
  le_sSup h

/-- **Proposition 8.33 `P:SupKernels`, kernel half.** The inclusion of `↓(⋁{x | f x = ⊥})` is a
2-kernel of `f`. -/
theorem isTwoKernel_segIncl {M : (SupOf C)} (f : L ⟶ M) :
    IsTwoKernel (zeroSup C) f (segIncl (kerElt f)) where
  isEssNull_comp := isEssNull_iff_forall.mpr fun x => apply_eq_bot_of_le_kerElt f x.2
  fac z hz :=
    ⟨segRestrict z (fun w => le_kerElt f (isEssNull_iff_forall.mp hz w)),
      ⟨eqToIso (DFunLike.ext _ _ fun _ => rfl)⟩⟩
  isTwoMono := isTwoMono_segIncl _

/-- **Proposition 8.33 `P:SupKernels`, cokernel half.** The join-projection onto `↑(f ⊤)` is a
2-cokernel of `f`. -/
theorem isTwoCokernel_upProj {M : (SupOf C)} (f : L ⟶ M) :
    IsTwoCokernel (zeroSup C) f (upProj (f ⊤)) where
  isEssNull_comp := isEssNull_iff_forall.mpr fun x =>
    Subtype.ext (sup_eq_right.mpr (OrderHomClass.mono f le_top))
  fac z hz := by
    have hb : z (f ⊤) = ⊥ := isEssNull_iff_forall.mp hz ⊤
    refine ⟨upRestrict z hb, ⟨eqToIso (DFunLike.ext _ _ fun y => ?_)⟩⟩
    change z ((y : M.carrier) ⊔ f ⊤) = z y
    rw [map_sup, hb, sup_bot_eq]
  isTwoEpi := isTwoEpi_upProj _

/-- Every segment inclusion is a 2-kernel, namely of its own join-projection
(`C:SupNormal`). -/
theorem isTwoKernel_upProj_segIncl (s : L) :
    IsTwoKernel (zeroSup C) (upProj s) (segIncl s) where
  isEssNull_comp := isEssNull_iff_forall.mpr fun x => Subtype.ext (sup_eq_right.mpr x.2)
  fac z hz := by
    have h : ∀ w, z w ≤ s := fun w => by
      have := congrArg Subtype.val (isEssNull_iff_forall.mp hz w)
      rw [Ici.coe_bot] at this
      exact sup_eq_right.mp this
    exact ⟨segRestrict z h, ⟨eqToIso (DFunLike.ext _ _ fun _ => rfl)⟩⟩
  isTwoMono := isTwoMono_segIncl _

/-- Every join-projection is a 2-cokernel, namely of its own segment inclusion
(`C:SupNormal`). -/
theorem isTwoCokernel_segIncl_upProj (t : L) :
    IsTwoCokernel (zeroSup C) (segIncl t) (upProj t) where
  isEssNull_comp := isEssNull_iff_forall.mpr fun x => Subtype.ext (sup_eq_right.mpr x.2)
  fac z hz := by
    have hb : z t = ⊥ := isEssNull_iff_forall.mp hz ⟨t, le_refl t⟩
    refine ⟨upRestrict z hb, ⟨eqToIso (DFunLike.ext _ _ fun y => ?_)⟩⟩
    change z ((y : L.carrier) ⊔ t) = z y
    rw [map_sup, hb, sup_bot_eq]
  isTwoEpi := isTwoEpi_upProj _

end Segments

/-- **Condition (DI1)**: every 1-cell has a 2-kernel and a 2-cokernel (Proposition 8.33
`P:SupKernels`). -/
instance twoZExactSup : TwoZExact (zeroSup C) where
  hasTwoKernel f := ⟨_, _, isTwoKernel_segIncl f⟩
  hasTwoCokernel f := ⟨_, _, isTwoCokernel_upProj f⟩

/-! ## Classification of the normal 1-cells -/

section Classification

variable {W K L M R : (SupOf C)}

/-- In a locally ordered 2-category, 2-monomorphisms cancel on 1-cells: fullness of
postcomposition turns an equality of composites into 2-cells in both directions. -/
theorem cancel_isTwoMono {m : K ⟶ L} (hm : IsTwoMono m) {w₁ w₂ : W ⟶ K}
    (h : w₁ ≫ m = w₂ ≫ m) : w₁ = w₂ := by
  haveI := hm
  obtain ⟨μ, -⟩ := (Bicategory.postcomp W m).map_surjective (eqToHom h)
  obtain ⟨ν, -⟩ := (Bicategory.postcomp W m).map_surjective (eqToHom h.symm)
  exact le_antisymm (leOfHom μ) (leOfHom ν)

/-- Dually, 2-epimorphisms cancel on 1-cells. -/
theorem cancel_isTwoEpi {e : L ⟶ M} (he : IsTwoEpi e) {w₁ w₂ : M ⟶ W}
    (h : e ≫ w₁ = e ≫ w₂) : w₁ = w₂ := by
  haveI := he
  obtain ⟨μ, -⟩ := (Bicategory.precomp W e).map_surjective (eqToHom h)
  obtain ⟨ν, -⟩ := (Bicategory.precomp W e).map_surjective (eqToHom h.symm)
  exact le_antisymm (leOfHom μ) (leOfHom ν)

/-- **Corollary 8.34 `C:SupNormal`, kernel half.** Every 2-kernel is a segment inclusion
precomposed with an isomorphism: a normal 2-monomorphism of `SupOf C` is, up to isomorphism, the
inclusion of a down-segment. -/
theorem exists_isEquiv1_of_isTwoKernel {g : L ⟶ M} {m : K ⟶ L}
    (h : IsTwoKernel (zeroSup C) g m) :
    ∃ φ : K ⟶ seg (kerElt g), IsEquiv1 φ ∧ m = φ ≫ segIncl (kerElt g) := by
  have hle : ∀ x, m x ≤ kerElt g := fun x =>
    le_kerElt g (isEssNull_iff_forall.mp h.isEssNull_comp x)
  refine ⟨segRestrict m hle, ?_, DFunLike.ext _ _ fun x => rfl⟩
  obtain ⟨u, ⟨θ⟩⟩ := h.fac (segIncl (kerElt g))
    (isEssNull_iff_forall.mpr fun x => apply_eq_bot_of_le_kerElt g x.2)
  have hu : u ≫ m = segIncl (kerElt g) := eq_of_iso_hom θ
  have h₁ : segRestrict m hle ≫ u = 𝟙 K := by
    refine cancel_isTwoMono h.isTwoMono ?_
    change segRestrict m hle ≫ u ≫ m = 𝟙 K ≫ m
    rw [hu]
    exact DFunLike.ext _ _ fun x => rfl
  have h₂ : u ≫ segRestrict m hle = 𝟙 (seg (kerElt g)) := by
    refine cancel_isTwoMono (isTwoMono_segIncl (kerElt g)) ?_
    change u ≫ segRestrict m hle ≫ segIncl (kerElt g) = 𝟙 _ ≫ segIncl (kerElt g)
    have : segRestrict m hle ≫ segIncl (kerElt g) = m := DFunLike.ext _ _ fun x => rfl
    rw [this, hu]
    rfl
  exact ⟨u, ⟨eqToIso h₁⟩, ⟨eqToIso h₂⟩⟩

/-- **Corollary 8.34 `C:SupNormal`, cokernel half.** Every 2-cokernel is a join-projection
postcomposed with an isomorphism. -/
theorem exists_isEquiv1_of_isTwoCokernel {h : L ⟶ M} {e : M ⟶ R}
    (hc : IsTwoCokernel (zeroSup C) h e) :
    ∃ ψ : upSeg (h ⊤) ⟶ R, IsEquiv1 ψ ∧ e = upProj (h ⊤) ≫ ψ := by
  have hb : e (h ⊤) = ⊥ := isEssNull_iff_forall.mp hc.isEssNull_comp ⊤
  have hfac : upProj (h ⊤) ≫ upRestrict e hb = e := by
    refine DFunLike.ext _ _ fun x => ?_
    change e (x ⊔ h ⊤) = e x
    rw [map_sup, hb, sup_bot_eq]
  obtain ⟨u, ⟨θ⟩⟩ := hc.fac (upProj (h ⊤))
    (isEssNull_iff_forall.mpr fun x => Subtype.ext (sup_eq_right.mpr (OrderHomClass.mono h le_top)))
  have hu : e ≫ u = upProj (h ⊤) := eq_of_iso_hom θ
  have h₁ : upRestrict e hb ≫ u = 𝟙 (upSeg (h ⊤)) := by
    refine cancel_isTwoEpi (isTwoEpi_upProj (h ⊤)) ?_
    change upProj (h ⊤) ≫ upRestrict e hb ≫ u = upProj (h ⊤) ≫ 𝟙 _
    have : upProj (h ⊤) ≫ (upRestrict e hb ≫ u) = (upProj (h ⊤) ≫ upRestrict e hb) ≫ u := rfl
    rw [this, hfac, hu]
    rfl
  have h₂ : u ≫ upRestrict e hb = 𝟙 R := by
    refine cancel_isTwoEpi hc.isTwoEpi ?_
    change e ≫ u ≫ upRestrict e hb = e ≫ 𝟙 R
    have : e ≫ (u ≫ upRestrict e hb) = (e ≫ u) ≫ upRestrict e hb := rfl
    rw [this, hu, hfac]
    rfl
  exact ⟨upRestrict e hb, ⟨u, ⟨eqToIso h₁⟩, ⟨eqToIso h₂⟩⟩, hfac.symm⟩

end Classification

/-! ## Dedekind's transposition principle is condition (DI2) -/

section Transpose

variable {L : (SupOf C)} (a b : L)

/-- An order isomorphism of complete lattices, as a 1-cell. -/
def orderIsoHom {L M : (SupOf C)} (e : L.carrier ≃o M.carrier) : L ⟶ M := mkHom
  { toFun := e
    map_sSup' := fun S => map_sSup e S }

theorem isEquiv1_orderIsoHom {L M : (SupOf C)} (e : L.carrier ≃o M.carrier) :
    IsEquiv1 (orderIsoHom e) :=
  ⟨orderIsoHom e.symm,
    ⟨eqToIso (DFunLike.ext _ _ fun x => e.symm_apply_apply x)⟩,
    ⟨eqToIso (DFunLike.ext _ _ fun y => e.apply_symm_apply y)⟩⟩

variable {a b}

/-- **The transposition**, as an order isomorphism between the coimage and the image of
`c_{a,b}`, available exactly when `a` and `b` transpose. This is where modularity enters, and
the only place: for a modular lattice every pair transposes, by `transposes_of_isModularLattice`
— Dedekind's transposition principle, as in the proof of Proposition 8.36 `P:SupModular`. -/
def transposeIso (h : Transposes a b) :
    (upSeg (L := seg a) ⟨a ⊓ b, inf_le_left⟩).carrier ≃o
      (seg (L := upSeg b) ⟨a ⊔ b, le_sup_right⟩).carrier where
  toFun x :=
    ⟨⟨((x : Set.Iic a) : L.carrier) ⊔ b, le_sup_right⟩,
      sup_le_sup_right (x : Set.Iic a).2 b⟩
  invFun y :=
    ⟨⟨((y : Set.Ici b) : L.carrier) ⊓ a, inf_le_right⟩,
      le_inf (le_trans inf_le_right (y : Set.Ici b).2) inf_le_left⟩
  left_inv x := by
    apply Subtype.ext; apply Subtype.ext
    exact h.1 _ x.2 (x : Set.Iic a).2
  right_inv y := by
    apply Subtype.ext; apply Subtype.ext
    exact h.2 _ (y : Set.Ici b).2 y.2
  map_rel_iff' {x x'} := by
    constructor
    · intro hle
      have h1 : ((x : Set.Iic a) : L.carrier) ⊔ b ≤ ((x' : Set.Iic a) : L.carrier) ⊔ b := hle
      have e1 := h.1 ((x : Set.Iic a) : L.carrier) x.2 (x : Set.Iic a).2
      have e2 := h.1 ((x' : Set.Iic a) : L.carrier) x'.2 (x' : Set.Iic a).2
      have hxx : ((x : Set.Iic a) : L.carrier) ≤ ((x' : Set.Iic a) : L.carrier) := by
        rw [← e1, ← e2]
        exact inf_le_inf_right a h1
      exact hxx
    · intro hle
      exact sup_le_sup_right (show ((x : Set.Iic a) : L.carrier) ≤ _ from hle) b

/-- **Proposition 8.35 `P:SupAntinormal`, the 'if' half.** The antinormal composite
`c_{a,b} : ↓a ⟶ ↑b`, `x ↦ x ⊔ b`, is normal as soon as `a` and `b` transpose: it factors as the
join-projection onto `[a ⊓ b, a]` followed by the transposition and the inclusion of
`[b, a ⊔ b]`, as in the paper. -/
theorem isNormal_segIncl_comp_upProj (h : Transposes a b) :
    IsNormal (zeroSup C) (segIncl a ≫ upProj b) := by
  refine ⟨upSeg (L := seg a) ⟨a ⊓ b, inf_le_left⟩,
    upProj (L := seg a) ⟨a ⊓ b, inf_le_left⟩,
    orderIsoHom (transposeIso h) ≫ segIncl (L := upSeg b) ⟨a ⊔ b, le_sup_right⟩,
    ⟨_, _, isTwoCokernel_segIncl_upProj _⟩,
    IsNormalMono.isEquiv1_comp ⟨_, _, isTwoKernel_upProj_segIncl _⟩
      (isEquiv1_orderIsoHom (transposeIso h)),
    ⟨eqToIso (DFunLike.ext _ _ fun x => ?_)⟩⟩
  apply Subtype.ext
  change (x : L.carrier) ⊔ b = ((x ⊔ ⟨a ⊓ b, inf_le_left⟩ : Set.Iic a) : L.carrier) ⊔ b
  rw [Iic.coe_sup]
  change (x : L.carrier) ⊔ b = ((x : L.carrier) ⊔ (a ⊓ b)) ⊔ b
  rw [sup_assoc]
  congr 1
  exact (sup_eq_right.mpr (inf_le_right : a ⊓ b ≤ b)).symm

/-- In a locally ordered 2-category an equivalence is an order isomorphism; all we need is
that it is a bijection. -/
theorem bijective_of_isEquiv1 {L M : (SupOf C)} {f : L ⟶ M} (h : IsEquiv1 f) :
    Function.Bijective (f : L.carrier → M.carrier) := by
  obtain ⟨g, ⟨η⟩, ⟨ε⟩⟩ := h
  have hgf : Function.LeftInverse (g : M.carrier → L.carrier) f := fun x =>
    DFunLike.congr_fun (eq_of_iso_hom η) x
  have hfg : Function.LeftInverse (f : L.carrier → M.carrier) g := fun y =>
    DFunLike.congr_fun (eq_of_iso_hom ε) y
  exact ⟨hgf.injective, hfg.surjective⟩

/-- **The elementwise core of the 'only if' half of Proposition 8.35 `P:SupAntinormal`.** If
`c_{a,b}` factors as the
join-projection onto `[s, a]`, then a bijection, then the inclusion of `[b, t]`, then `a` and `b`
transpose: reading the factorisation off at the bottom of `↓a` gives `s = a ⊓ b`, reading off
which elements are hit gives `t = a ⊔ b`, and the bijection in the middle is therefore the
transposition. -/
theorem transposes_of_factorisation {I : (SupOf C)} (s : seg a) (t : upSeg b)
    {χ : upSeg s ⟶ I} {χ' : I ⟶ seg (L := upSeg b) t}
    (hχ : Function.Bijective (χ : (upSeg s).carrier → I.carrier))
    (hχ' : Function.Bijective (χ' : I.carrier → (seg (L := upSeg b) t).carrier))
    (hfac : ∀ x : seg a, ((x : L.carrier) ⊔ b : L.carrier)
      = (((χ' (χ (upProj s x)) : seg (L := upSeg b) t) : upSeg b) : L.carrier)) :
    Transposes a b := by
  obtain ⟨hχinj, hχsurj⟩ := hχ
  obtain ⟨hχ'inj, hχ'surj⟩ := hχ'
  have hsL : ((s : Set.Iic a) : L.carrier) ≤ a := s.2
  -- `s ≤ b`: the join-projection sends the bottom of `↓a` and `s` to the same place.
  have hsb : ((s : Set.Iic a) : L.carrier) ≤ b := by
    have h₁ := hfac ⟨⊥, bot_le⟩
    have h₂ := hfac ⟨((s : Set.Iic a) : L.carrier), hsL⟩
    have hup : upProj s (⟨⊥, bot_le⟩ : seg a)
        = upProj s (⟨((s : Set.Iic a) : L.carrier), hsL⟩ : seg a) := by
      apply Subtype.ext; apply Subtype.ext
      rw [upProj_apply, upProj_apply, Iic.coe_sup, Iic.coe_sup, bot_sup_eq, sup_idem]
    rw [hup] at h₁
    have hbs := h₂.trans h₁.symm
    rw [bot_sup_eq] at hbs
    exact sup_eq_right.1 hbs
  have hsab : ((s : Set.Iic a) : L.carrier) ≤ a ⊓ b := le_inf hsL hsb
  -- The elements of `↑b` of the form `x ⊔ b` are exactly those below `t`.
  have himage : ∀ z : L.carrier, b ≤ z →
      ((∃ x : L.carrier, x ≤ a ∧ x ⊔ b = z) ↔ z ≤ ((t : Set.Ici b) : L.carrier)) := by
    intro z hbz
    constructor
    · rintro ⟨x, hxa, rfl⟩
      rw [hfac ⟨x, hxa⟩]
      exact (χ' (χ (upProj s ⟨x, hxa⟩))).2
    · intro hzt
      obtain ⟨i, hi⟩ := hχ'surj (⟨⟨z, hbz⟩, hzt⟩ : seg (L := upSeg b) t)
      obtain ⟨w, hw⟩ := hχsurj i
      refine ⟨(((w : Set.Iic a) : L.carrier)), (w : Set.Iic a).2, ?_⟩
      have hwu : upProj s ⟨((w : Set.Iic a) : L.carrier), (w : Set.Iic a).2⟩ = w := by
        apply Subtype.ext
        exact sup_eq_left.2 w.2
      rw [hfac ⟨_, _⟩, hwu, hw, hi]
  -- Hence `t = a ⊔ b`.
  have ht : ((t : Set.Ici b) : L.carrier) = a ⊔ b := by
    refine le_antisymm ?_ ((himage (a ⊔ b) le_sup_right).1 ⟨a, le_rfl, rfl⟩)
    obtain ⟨x, hxa, hx⟩ := (himage ((t : Set.Ici b) : L.carrier) t.2).2 le_rfl
    rw [← hx]
    exact sup_le_sup_right hxa b
  -- The transposition is therefore a bijection.
  refine transposes_iff_bijective.2 ⟨?_, ?_⟩
  · intro x y hxy
    have h1 : ((x : L.carrier)) ⊔ b = ((y : L.carrier)) ⊔ b := congrArg Subtype.val hxy
    have e1 := hfac ⟨(x : L.carrier), x.2.2⟩
    have e2 := hfac ⟨(y : L.carrier), y.2.2⟩
    have heq : χ' (χ (upProj s ⟨(x : L.carrier), x.2.2⟩))
        = χ' (χ (upProj s ⟨(y : L.carrier), y.2.2⟩)) := by
      apply Subtype.ext; apply Subtype.ext
      rw [← e1, ← e2]
      exact h1
    have hup := hχinj (hχ'inj heq)
    have hxs : ((x : L.carrier)) ⊔ ((s : Set.Iic a) : L.carrier)
        = ((y : L.carrier)) ⊔ ((s : Set.Iic a) : L.carrier) :=
      congrArg Subtype.val (congrArg Subtype.val hup)
    rw [sup_eq_left.2 (hsab.trans x.2.1), sup_eq_left.2 (hsab.trans y.2.1)] at hxs
    exact Subtype.ext hxs
  · intro z
    obtain ⟨x, hxa, hx⟩ := (himage ((z : L.carrier)) z.2.1).2 (by rw [ht]; exact z.2.2)
    refine ⟨⟨x ⊔ (a ⊓ b), le_sup_right, sup_le hxa inf_le_left⟩, ?_⟩
    apply Subtype.ext
    rw [coe_transposeMap, sup_assoc, sup_eq_right.2 (inf_le_right : a ⊓ b ≤ b), hx]

/-- **Proposition 8.35 `P:SupAntinormal`, the 'only if' half.** If the antinormal composite
`c_{a,b}` is normal then `a` and `b` transpose: its normal image factorisation is a
join-projection followed by an equivalence followed by a segment inclusion (Corollary 8.34
`C:SupNormal`), and `transposes_of_factorisation` identifies the middle equivalence as the
transposition. The paper locates the join-projection through the 2-kernel of `c_{a,b}` and
Proposition 3.9 `CoKernel of Composite`; here it is read off at `⊥` instead. -/
theorem transposes_of_isNormal (h : IsNormal (zeroSup C) (segIncl a ≫ upProj b)) :
    Transposes a b := by
  obtain ⟨I, e, m, he, hm, ⟨θ⟩⟩ := h
  obtain ⟨X, g₁, hq⟩ := he
  obtain ⟨Y, g₂, hk⟩ := hm
  obtain ⟨ψ, hψ, rfl⟩ := exists_isEquiv1_of_isTwoCokernel hq
  obtain ⟨φ, hφ, rfl⟩ := exists_isEquiv1_of_isTwoKernel hk
  exact transposes_of_factorisation (g₁ ⊤) (kerElt g₂)
    (bijective_of_isEquiv1 hψ) (bijective_of_isEquiv1 hφ)
    (fun x => congrArg Subtype.val (DFunLike.congr_fun (eq_of_iso_hom θ) x))

/-- **Proposition 8.35 `P:SupAntinormal` in full**: the antinormal composite `c_{a,b}` is normal
exactly when `a` and `b` transpose. With `isModularLattice_iff_forall_transposes` this is
Proposition 8.36 `P:SupModular`, whose (ii) ⟹ (i) the paper proves through the pentagon and
`SnakeLean.ModularPair` through the units alone. -/
theorem isNormal_segIncl_comp_upProj_iff :
    IsNormal (zeroSup C) (segIncl a ≫ upProj b) ↔ Transposes a b :=
  ⟨transposes_of_isNormal, isNormal_segIncl_comp_upProj⟩

end Transpose

/-! ## The two conditions, on a class of lattices -/

section Conditions

/-- **Every antinormal 1-cell is a `c_{a,b}` up to equivalences** — the first clause of
Proposition 8.35 `P:SupAntinormal`. This is the classification of Corollary 8.34 `C:SupNormal`
read on a composite: a normal 2-monomorphism into `L` is a down-segment inclusion
and a normal 2-epimorphism out of `L` is a join-projection. -/
theorem exists_form_of_isAntinormal {A A' : (SupOf C)} {f : A ⟶ A'}
    (hf : IsAntinormal (zeroSup C) f) :
    ∃ (L : (SupOf C)) (a b : L) (u : A ⟶ seg a) (v : upSeg b ⟶ A'),
      IsEquiv1 u ∧ IsEquiv1 v ∧ f = u ≫ (segIncl a ≫ upProj b) ≫ v := by
  obtain ⟨I, m, e, hm, he, ⟨θ⟩⟩ := hf
  obtain ⟨Y, g, hk⟩ := hm
  obtain ⟨X, h, hq⟩ := he
  obtain ⟨φ, hφ, rfl⟩ := exists_isEquiv1_of_isTwoKernel hk
  obtain ⟨ψ, hψ, rfl⟩ := exists_isEquiv1_of_isTwoCokernel hq
  exact ⟨I, kerElt g, h ⊤, φ, ψ, hφ, hψ, eq_of_iso_hom θ⟩

/-- **Condition (DI2) on a class of lattices** (Proposition 9.29 `P:SupClass`, and Theorem 8.37
`T:LatticeModel` when the class is that of the modular lattices): if every member is modular
then every antinormal 1-cell is normal. -/
theorem twoDiExact_of_forall_isModularLattice
    (hmod : ∀ L : (SupOf C), IsModularLattice L.carrier) : TwoDiExact (zeroSup C) where
  isNormal_of_isAntinormal hf := by
    obtain ⟨L, a, b, u, v, hu, hv, rfl⟩ := exists_form_of_isAntinormal hf
    haveI := hmod L
    exact (isNormal_segIncl_comp_upProj (transposes_of_isModularLattice a b)).transport hu hv

/-- **Proposition 9.29 `P:SupClass`, the (DI2) half, converse direction.** If `Sup_C` satisfies
(DI2) then every member of the class is modular: for `a`, `b` in a member `L` the antinormal 1-cell
`c_{a,b} = segIncl a ≫ upProj b` is normal, so `a` and `b` transpose, and a lattice all of whose
pairs transpose is modular. -/
theorem isModularLattice_of_twoDiExact [TwoDiExact (zeroSup C)] (L : (SupOf C)) :
    IsModularLattice L.carrier :=
  isModularLattice_of_forall_transposes fun a b =>
    isNormal_segIncl_comp_upProj_iff.1 (TwoDiExact.isNormal_of_isAntinormal
      (isAntinormal_comp ⟨_, _, isTwoKernel_upProj_segIncl a⟩
        ⟨_, _, isTwoCokernel_segIncl_upProj b⟩))

/-- **Proposition 9.29 `P:SupClass`, the (DI2) half in full**: `Sup_C` satisfies condition (DI2)
exactly when every member of `C` is modular. -/
theorem twoDiExact_iff_forall_isModularLattice :
    TwoDiExact (zeroSup C) ↔ ∀ L : (SupOf C), IsModularLattice L.carrier :=
  ⟨fun _ => isModularLattice_of_twoDiExact, twoDiExact_of_forall_isModularLattice⟩

end Conditions

/-! ## All complete lattices -/

/-- The class of all complete lattices. -/
def allClass : LatticeClass.{u} where
  Mem := fun α [CompleteLattice α] => True
  mem_punit := trivial
  mem_iic := fun _ _ => trivial
  mem_ici := fun _ _ => trivial
  mem_of_orderIso := fun _ _ => trivial

/-- **The 2-category `Sup`** of Section 8.30 `SS:ModelLattices`: all complete lattices,
join-preserving maps and the pointwise order. It is 2-z-exact with a strong bizero object and
homologically self-dual (`SnakeLean.LatticeNSD.isHSD_sup`), its normal 2-monomorphisms and
normal 2-epimorphisms compose, and it is neither 2-di-exact (Proposition 8.36 `P:SupModular`)
nor (DPN) (Proposition 8.38 `P:SupNotDPN`): that is the pentagon, `SnakeLean.Pentagon`
(`not_twoDiExact_supAll`, `not_dpn_supAll`). -/
abbrev SupAll := SupOf allClass.{u}

/-! ## The modular lattices -/

/-- The class of complete modular lattices. -/
def modularClass : LatticeClass.{u} where
  Mem := fun α [CompleteLattice α] => IsModularLattice α
  mem_punit := inferInstance
  mem_iic := fun {_} _ h a => by haveI := h; infer_instance
  mem_ici := fun {_} _ h b => by haveI := h; infer_instance
  mem_of_orderIso := fun {_ _} _ _ e h => by
    haveI := h
    constructor
    intro x y z hxz
    rw [← e.symm.le_iff_le]
    simp only [map_inf, map_sup]
    exact sup_inf_le_assoc_of_le _ (e.symm.le_iff_le.2 hxz)

/-- **The 2-category `Supmod`** of Section 8.30 `SS:ModelLattices` and Theorem 8.37
`T:LatticeModel`: the complete modular lattices, join-preserving maps and the pointwise order. -/
abbrev ModSup := SupOf modularClass.{u}

instance (L : ModSup.{u}) : IsModularLattice L.carrier := L.mem

/-- **Theorem 8.37 `T:LatticeModel`.** Condition (DI2): every antinormal 1-cell of `ModSup` is
normal, by Dedekind's transposition principle. -/
instance twoDiExactModSup : TwoDiExact (zeroSup modularClass.{u}) :=
  twoDiExact_of_forall_isModularLattice fun L => L.mem

/-- **The standing hypotheses of Section 6 are consistent, two-dimensionally.** All four of
`HasBizero`, `IsStrong`, `TwoZExact` and `TwoDiExact` hold of `zeroSup modularClass`, so every
result of Sections 2 to 6 applies to `ModSup`, `exists_snakeGeneral` included: a Snake Lemma for
complete modular lattices, whose element-level reading is Remark 8.40 `Rem Lattice Snake`. -/
theorem isHSD_modSup : IsHSD (zeroSup modularClass.{u}) :=
  isHSD_of_twoDiExact

/-- Homological self-duality being available, so is the Pure Snake Lemma. -/
theorem isPureSnake_modSup : IsPureSnake (zeroSup modularClass.{u}) :=
  isPureSnake_of_twoDiExact

end SnakeLean
