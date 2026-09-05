/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.ModularLattice
import Mathlib.Order.LatticeIntervals
import Mathlib.Order.GaloisConnection.Basic

/-!
# Modular pairs and transpositions

This module is about lattices, not about the 2-categorical development. It supports
Proposition 8.36 `P:SupModular`, Proposition 9.29 `P:SupClass` and Lemma 9.30 `L:ModularPairs`,
which translate the hypotheses of the two Snake Lemmas into lattice theory: for the full
sub-2-category of the 2-category of complete lattices and join-preserving maps on a class of
lattices, condition (DI2) says that every member is modular, and condition (DPN) says that every
member is *transposition-symmetric* (Proposition 9.29); Lemma 9.30 reads the invertibility of one
transposition as a pair of modular-pair conditions.

Mathlib has `IsModularLattice` and the four semimodularity classes, but no notion of a **modular
pair**, which is what both conditions are really about. Everything here is new.

## The elementwise convention

The transposition of `a` and `b` is the map
`T(a, b) : [a ⊓ b, a] → [b, a ⊔ b]`, `x ↦ x ⊔ b`, with right adjoint `z ↦ z ⊓ a`. It is
invertible exactly when the unit and the counit of that adjunction are equalities, and
`Transposes` says just that, quantifying over elements of the ambient lattice constrained by
inequalities rather than over a bundled interval type. Two things become free that way:
`Transposes` computed inside an interval is `Transposes` computed in the ambient lattice
(`transposes_coe_Icc`), and passage to the order dual merely exchanges the unit with the counit
(`transposes_toDual`). The bundled form is available as `transposeOrderIso`, and
`transposes_iff_bijective` says the two agree.

## Main results

* `modularPair_iff`, `dualModularPair_iff` — the two conditions in interval form.
* `transposes_iff` — **Lemma 9.30 `L:ModularPairs`**: the transposition at `(a, b)` is invertible if
  and only if `(b, a)` is a modular pair and `(a, b)` a dual modular pair.
* `transposes_toDual`, `transpositionSymmetric_orderDual` — transposition-symmetry is
  self-dual, which is what lets the dual half of Proposition 9.34 `P:FiniteLength` be a
  transport rather than a second proof, in `SnakeLean.Semimodular`.
* `isModularLattice_iff_forall_transposes` — **Proposition 8.36 `P:SupModular` at lattice
  level**: a lattice is modular precisely when all of its transpositions are invertible. This is
  Dedekind's transposition principle, and in the paper it is condition (DI2).
* `transposes_iff_bijective`, `transposeOrderIso` — the bundled transposition.
-/

namespace SnakeLean

open Set OrderDual

variable {α : Type*}

section Defs

variable [Lattice α]

/-- **A modular pair**, in the sense of Maeda and Maeda: `(a, b)` is a modular pair when the
modular law holds for `a`, `b` and everything below `b`. -/
def ModularPair (a b : α) : Prop := ∀ c ≤ b, (c ⊔ a) ⊓ b = c ⊔ a ⊓ b

/-- **A dual modular pair**: the order dual of `ModularPair`. -/
def DualModularPair (a b : α) : Prop := ∀ c, b ≤ c → (c ⊓ a) ⊔ b = c ⊓ (a ⊔ b)

/-- **The transposition of `a` and `b` is invertible**: the unit and the counit of the adjunction
`(· ⊔ b) ⊣ (· ⊓ a)` between `[a ⊓ b, a]` and `[b, a ⊔ b]` are equalities. -/
def Transposes (a b : α) : Prop :=
  (∀ x, a ⊓ b ≤ x → x ≤ a → (x ⊔ b) ⊓ a = x) ∧ (∀ z, b ≤ z → z ≤ a ⊔ b → (z ⊓ a) ⊔ b = z)

/-- **A transposition-symmetric lattice**: whenever the transposition of `a` and `b` is
invertible, so is the transposition of `b` and `a`. This is condition (DPN),
read on a lattice. -/
def TranspositionSymmetric (α : Type*) [Lattice α] : Prop :=
  ∀ a b : α, Transposes a b → Transposes b a

end Defs

section Basic

variable [Lattice α] {a b : α}

/-- Being a dual modular pair is being a modular pair in the order dual. -/
theorem dualModularPair_iff_toDual :
    DualModularPair a b ↔ ModularPair (toDual a) (toDual b) :=
  Iff.rfl

/-- And conversely. -/
theorem modularPair_iff_toDual :
    ModularPair a b ↔ DualModularPair (toDual a) (toDual b) :=
  Iff.rfl

/-- A modular pair, in interval form: the quantifier may be restricted to `[a ⊓ b, b]`, where
the conclusion becomes the statement that the unit of the transposition of `b` and `a` is an
equality. -/
theorem modularPair_iff : ModularPair a b ↔ ∀ x, a ⊓ b ≤ x → x ≤ b → (x ⊔ a) ⊓ b = x := by
  constructor
  · intro h x hx hxb
    rw [h x hxb]
    exact sup_eq_left.2 hx
  · intro h c hc
    have := h (c ⊔ a ⊓ b) le_sup_right (sup_le hc inf_le_right)
    rwa [sup_assoc, sup_eq_right.2 (inf_le_left : a ⊓ b ≤ a)] at this

/-- A dual modular pair, in interval form. -/
theorem dualModularPair_iff : DualModularPair a b ↔ ∀ z, b ≤ z → z ≤ a ⊔ b → (z ⊓ a) ⊔ b = z := by
  constructor
  · intro h z hz hza
    rw [h z hz]
    exact inf_eq_left.2 hza
  · intro h c hc
    have := h (c ⊓ (a ⊔ b)) (le_inf hc le_sup_right) inf_le_right
    rwa [inf_assoc, inf_eq_right.2 (le_sup_left : a ≤ a ⊔ b)] at this

/-- **Lemma 9.30 `L:ModularPairs`.** The transposition of `a` and `b` is invertible if and only if
`(b, a)` is a modular pair and `(a, b)` is a dual modular pair: the unit is an equality exactly
in the first case, the counit exactly in the second. -/
theorem transposes_iff : Transposes a b ↔ ModularPair b a ∧ DualModularPair a b := by
  rw [modularPair_iff, dualModularPair_iff, inf_comm b a]
  exact Iff.rfl

/-- When `a ≤ b`, the transposition of `b` and `a` runs from `[a, b]` to `[a, b]` and is the
identity, so it is invertible. This is what makes every class of complete lattices homologically
self-dual (`SnakeLean.LatticeNSD.isHSD_sup`): the dinversion of an antinormal decomposition of the
zero map is a transposition of this kind. -/
theorem transposes_of_le (h : a ≤ b) : Transposes b a := by
  refine ⟨fun x hx hxb => ?_, fun z hz hzb => ?_⟩
  · have hax : a ≤ x := (inf_eq_right.2 h).symm.le.trans hx
    rw [sup_eq_left.2 hax, inf_eq_left.2 hxb]
  · have hzb' : z ≤ b := hzb.trans (sup_eq_left.2 h).le
    rw [inf_eq_left.2 hzb', sup_eq_left.2 hz]

end Basic

section Duality

variable [Lattice α]

/-- **Transposition-invertibility is self-dual**, with the roles of `a` and `b` exchanged: the unit
of one transposition is the counit of the other. In the words of the proof of Proposition 9.34
`P:FiniteLength`, the transposition of `Lᵒᵖ` at `(a, b)` is the right adjoint of the transposition
of `L` at `(b, a)`, and an adjoint is invertible precisely when its partner is. -/
theorem transposes_toDual (a b : α) :
    Transposes (toDual a) (toDual b) ↔ Transposes b a := by
  rw [transposes_iff, transposes_iff, ← dualModularPair_iff_toDual,
    ← modularPair_iff_toDual]
  exact and_comm

/-- **Transposition-symmetry is self-dual**, which is what lets the dual half of
Proposition 9.34 `P:FiniteLength` be a transport rather than a second proof
(`isLowerModularLattice_of_transpositionSymmetric`). -/
theorem transpositionSymmetric_orderDual :
    TranspositionSymmetric αᵒᵈ ↔ TranspositionSymmetric α := by
  constructor
  · intro h a b hab
    exact (transposes_toDual a b).1 (h (toDual b) (toDual a) ((transposes_toDual b a).2 hab))
  · intro h A B hAB
    exact (transposes_toDual (ofDual B) (ofDual A)).2
      (h _ _ ((transposes_toDual (ofDual A) (ofDual B)).1 hAB))

end Duality

section Modular

variable [Lattice α]

/-- In a modular lattice every pair is a modular pair. -/
theorem modularPair_of_isModularLattice [IsModularLattice α] (a b : α) : ModularPair a b :=
  fun _ hc => sup_inf_assoc_of_le _ hc

/-- In a modular lattice every pair is a dual modular pair. -/
theorem dualModularPair_of_isModularLattice [IsModularLattice α] (a b : α) :
    DualModularPair a b :=
  fun _ hc => inf_sup_assoc_of_le _ hc

/-- **Dedekind's transposition principle**: in a modular lattice every transposition is
invertible. -/
theorem transposes_of_isModularLattice [IsModularLattice α] (a b : α) : Transposes a b :=
  transposes_iff.2 ⟨modularPair_of_isModularLattice b a, dualModularPair_of_isModularLattice a b⟩

/-- The converse: a lattice all of whose transpositions are invertible is modular. Only the
units are used, so the hypothesis could be weakened to `∀ a b, ModularPair a b`. -/
theorem isModularLattice_of_forall_transposes (h : ∀ a b : α, Transposes a b) :
    IsModularLattice α where
  sup_inf_le_assoc_of_le := by
    intro x y z hxz
    have key := (h z y).1 (x ⊔ y ⊓ z) (by rw [inf_comm]; exact le_sup_right)
      (sup_le hxz inf_le_right)
    rw [sup_assoc, sup_eq_right.2 (inf_le_left : y ⊓ z ≤ y)] at key
    exact le_of_eq key

/-- **Proposition 8.36 `P:SupModular` at lattice level**: a lattice is modular precisely when all of
its transpositions are invertible. In the paper the right-hand side is condition (DI2). -/
theorem isModularLattice_iff_forall_transposes :
    IsModularLattice α ↔ ∀ a b : α, Transposes a b :=
  ⟨fun _ => transposes_of_isModularLattice, isModularLattice_of_forall_transposes⟩

/-- A modular lattice is transposition-symmetric, so (DI2) implies (DPN) on lattices. -/
theorem transpositionSymmetric_of_isModularLattice [IsModularLattice α] :
    TranspositionSymmetric α :=
  fun a b _ => transposes_of_isModularLattice b a

end Modular

section Interval

variable [Lattice α] {p q : α}

/-- **Transposition-invertibility is computed in the ambient lattice.** The elements the
definition quantifies over lie between `x ⊓ y` and `x ⊔ y` already, so an interval containing
`x` and `y` contains all of them. -/
theorem transposes_coe_Icc (x y : Icc p q) :
    Transposes x y ↔ Transposes (x : α) (y : α) := by
  have hp : p ≤ (x : α) ⊓ (y : α) := le_inf x.2.1 y.2.1
  have hq : (x : α) ⊔ (y : α) ≤ q := sup_le x.2.2 y.2.2
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun u hu hux => ?_, fun w hw hwq => ?_⟩
    · have hmem : u ∈ Icc p q := ⟨hp.trans hu, hux.trans x.2.2⟩
      have := h₁ ⟨u, hmem⟩ (by rw [Subtype.mk_le_mk, Icc.coe_inf]; exact hu) hux
      simpa [Icc.coe_inf, Icc.coe_sup] using congrArg Subtype.val this
    · have hmem : w ∈ Icc p q := ⟨y.2.1.trans hw, hwq.trans hq⟩
      have := h₂ ⟨w, hmem⟩ hw (by rw [Subtype.mk_le_mk, Icc.coe_sup]; exact hwq)
      simpa [Icc.coe_inf, Icc.coe_sup] using congrArg Subtype.val this
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun u hu hux => ?_, fun w hw hwq => ?_⟩
    · apply Subtype.ext
      rw [Icc.coe_inf, Icc.coe_sup]
      refine h₁ (u : α) ?_ hux
      have : ((x ⊓ y : Icc p q) : α) ≤ (u : α) := hu
      rwa [Icc.coe_inf] at this
    · apply Subtype.ext
      rw [Icc.coe_sup, Icc.coe_inf]
      refine h₂ (w : α) hw ?_
      have : (w : α) ≤ ((x ⊔ y : Icc p q) : α) := hwq
      rwa [Icc.coe_sup] at this

/-- Transposition-symmetry passes to intervals. -/
theorem transpositionSymmetric_Icc (h : TranspositionSymmetric α) (p q : α) :
    TranspositionSymmetric (Icc p q) :=
  fun x y hxy => (transposes_coe_Icc y x).2 (h x y ((transposes_coe_Icc x y).1 hxy))

end Interval

section Bundled

variable [Lattice α] (a b : α)

/-- The transposition `[a ⊓ b, a] → [b, a ⊔ b]`, `x ↦ x ⊔ b`. -/
def transposeMap (x : Icc (a ⊓ b) a) : Icc b (a ⊔ b) :=
  ⟨(x : α) ⊔ b, le_sup_right, sup_le_sup_right x.2.2 b⟩

/-- Its right adjoint `[b, a ⊔ b] → [a ⊓ b, a]`, `z ↦ z ⊓ a`. -/
def transposeInv (z : Icc b (a ⊔ b)) : Icc (a ⊓ b) a :=
  ⟨(z : α) ⊓ a, le_inf (inf_le_right.trans z.2.1) inf_le_left, inf_le_right⟩

@[simp] theorem coe_transposeMap (x : Icc (a ⊓ b) a) :
    (transposeMap a b x : α) = (x : α) ⊔ b := rfl

@[simp] theorem coe_transposeInv (z : Icc b (a ⊔ b)) :
    (transposeInv a b z : α) = (z : α) ⊓ a := rfl

/-- The transposition is left adjoint to `z ↦ z ⊓ a`. -/
theorem transpose_gc : GaloisConnection (transposeMap a b) (transposeInv a b) := by
  intro x z
  constructor
  · intro h
    have h' : (x : α) ⊔ b ≤ (z : α) := h
    exact le_inf (le_sup_left.trans h') x.2.2
  · intro h
    have h' : (x : α) ≤ (z : α) ⊓ a := h
    exact sup_le (h'.trans inf_le_left) z.2.1

variable {a b}

/-- The unit of the transposition is an equality, in bundled form. -/
theorem transposeInv_transposeMap (h : Transposes a b) (x : Icc (a ⊓ b) a) :
    transposeInv a b (transposeMap a b x) = x :=
  Subtype.ext (h.1 (x : α) x.2.1 x.2.2)

/-- The counit of the transposition is an equality, in bundled form. -/
theorem transposeMap_transposeInv (h : Transposes a b) (z : Icc b (a ⊔ b)) :
    transposeMap a b (transposeInv a b z) = z :=
  Subtype.ext (h.2 (z : α) z.2.1 z.2.2)

/-- **The elementwise and the bundled forms agree**: the transposition of `a` and `b` is
invertible in the sense of `Transposes` exactly when it is a bijection. -/
theorem transposes_iff_bijective : Transposes a b ↔ Function.Bijective (transposeMap a b) := by
  constructor
  · intro h
    have hl : Function.LeftInverse (transposeInv a b) (transposeMap a b) :=
      transposeInv_transposeMap h
    have hr : Function.RightInverse (transposeInv a b) (transposeMap a b) :=
      transposeMap_transposeInv h
    exact ⟨hl.injective, hr.surjective⟩
  · rintro ⟨hinj, hsurj⟩
    have hunit : ∀ x, transposeInv a b (transposeMap a b x) = x := fun x =>
      hinj ((transpose_gc a b).l_u_l_eq_l x)
    refine ⟨fun u hu hua => ?_, fun w hw hwa => ?_⟩
    · exact congrArg Subtype.val (hunit ⟨u, hu, hua⟩)
    · obtain ⟨x, hx⟩ := hsurj ⟨w, hw, hwa⟩
      have hux : (w : α) ⊓ a = (x : α) := by
        have hx' := hunit x
        rw [hx] at hx'
        exact congrArg Subtype.val hx'
      rw [hux]
      exact congrArg Subtype.val hx

/-- The transposition reflects the order as soon as it is invertible. -/
theorem transposeMap_le_transposeMap_iff (h : Transposes a b) {x y : Icc (a ⊓ b) a} :
    transposeMap a b x ≤ transposeMap a b y ↔ x ≤ y := by
  refine ⟨fun hxy => ?_, fun hxy => (transpose_gc a b).monotone_l hxy⟩
  have h2 := (transpose_gc a b).monotone_u hxy
  rwa [transposeInv_transposeMap h, transposeInv_transposeMap h] at h2

/-- **The transposition as an order isomorphism**, which is the form Proposition 8.35
`P:SupAntinormal` uses. -/
def transposeOrderIso (h : Transposes a b) : Icc (a ⊓ b) a ≃o Icc b (a ⊔ b) where
  toFun := transposeMap a b
  invFun := transposeInv a b
  left_inv := transposeInv_transposeMap h
  right_inv := transposeMap_transposeInv h
  map_rel_iff' := transposeMap_le_transposeMap_iff h

end Bundled

end SnakeLean
