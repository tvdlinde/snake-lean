/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.Semimodular
import Mathlib.Order.KrullDimension

/-!
# Birkhoff's theorem: semimodular in both directions implies modular

This module supplies the one ingredient of Proposition 9.34 `P:FiniteLength` that the
paper takes from the literature: a lattice of finite length which is semimodular and dually
semimodular is modular. It is Theorem 16 of Chapter II, §8 of Birkhoff's *Lattice Theory*
(3rd edition, 1967, p. 41), where it appears as the equivalence of the modular identity, both
semimodularities, and the Jordan–Dedekind chain condition together with `h[x] + h[y] =
h[x ⊔ y] + h[x ⊓ y]`. Mathlib has the semimodularity classes and the `Order.height` API but not
this theorem.

## The hypotheses

Birkhoff assumes finite length, meaning that the lengths of chains are bounded. What the proof
below consumes is weaker: the two chain conditions, and that each element has finite height.
The last is genuinely needed — it is what makes the final cancellation legitimate — but it is
required of the elements one at a time, not uniformly.

## The argument

`covBy_height_eq` is the Jordan–Dedekind content: along a covering the height goes up by exactly
one. Its proof needs only *dual* semimodularity, and no finiteness: for `y < b` either `y ≤ a`,
or `a ⊔ y = b` and then `a ⊓ y ⋖ y` by dual semimodularity, so that induction gives
`height y = height (a ⊓ y) + 1 ≤ height a`.

`sup_eq_or_covBy_sup` is the covering lemma: if `a ⋖ b` then `a ⊔ t` either equals `b ⊔ t` or is
covered by it. It turns the two semimodularities into the two halves of Birkhoff's identity,
`height_sup_add_height_inf_le` and `le_height_sup_add_height_inf`, by inductions that walk one
covering at a time. Modularity then follows from the pentagon: a lattice which is not modular
carries `x < z` with `x ⊓ y = z ⊓ y` and `x ⊔ y = z ⊔ y`, and the identity forces
`height x = height z`.
-/

namespace SnakeLean

open Order

variable {α : Type*} [Lattice α]

section Covering

/-- **The covering lemma.** In a semimodular lattice, joining with a fixed element sends a
covering either to an equality or to a covering. -/
theorem sup_eq_or_covBy_sup [IsUpperModularLattice α] {a b : α} (hab : a ⋖ b) (t : α) :
    a ⊔ t = b ⊔ t ∨ a ⊔ t ⋖ b ⊔ t := by
  rcases hab.eq_or_eq (le_inf le_sup_left hab.le) (inf_le_right : (a ⊔ t) ⊓ b ≤ b) with h | h
  · right
    have hcov : b ⊓ (a ⊔ t) ⋖ b := by rw [inf_comm, h]; exact hab
    have h2 := IsUpperModularLattice.covBy_sup_of_inf_covBy hcov
    have he : b ⊔ (a ⊔ t) = b ⊔ t := by rw [← sup_assoc, sup_eq_left.2 hab.le]
    rwa [he] at h2
  · left
    have hba : b ≤ a ⊔ t := by rw [← h]; exact inf_le_left
    exact le_antisymm (sup_le_sup_right hab.le t) (sup_le hba le_sup_right)

/-- **The dual covering lemma**, in a dually semimodular lattice. -/
theorem inf_eq_or_covBy_inf [IsLowerModularLattice α] {a b : α} (hab : a ⋖ b) (t : α) :
    a ⊓ t = b ⊓ t ∨ a ⊓ t ⋖ b ⊓ t := by
  rcases hab.eq_or_eq (le_sup_right : a ≤ b ⊓ t ⊔ a) (sup_le inf_le_left hab.le) with h | h
  · left
    have hba : b ⊓ t ≤ a := by rw [← h]; exact le_sup_left
    exact le_antisymm (inf_le_inf_right t hab.le) (le_inf hba inf_le_right)
  · right
    have hcov : a ⋖ a ⊔ b ⊓ t := by rw [sup_comm, h]; exact hab
    have h2 := IsLowerModularLattice.inf_covBy_of_covBy_sup hcov
    have he : a ⊓ (b ⊓ t) = a ⊓ t := by rw [← inf_assoc, inf_eq_left.2 hab.le]
    rwa [he] at h2

/-- **The Jordan–Dedekind chain condition, in the form the height function needs**: in a dually
semimodular lattice satisfying the descending chain condition, a covering raises the height by
exactly one. No finiteness is required. -/
theorem covBy_height_eq [IsLowerModularLattice α] [WellFoundedLT α] {a b : α} (hab : a ⋖ b) :
    height b = height a + 1 := by
  induction b using WellFoundedLT.induction generalizing a with
  | _ b IH =>
    rw [height_eq_iSup_lt_height b]
    apply le_antisymm
    · refine iSup₂_le fun y hyb => ?_
      have hle : height y ≤ height a := by
        rcases hab.eq_or_eq (le_sup_left : a ≤ a ⊔ y) (sup_le hab.le hyb.le) with h | h
        · exact height_mono (le_sup_right.trans h.le)
        · have hay : a ⊓ y ⋖ y := by
            refine IsLowerModularLattice.inf_covBy_of_covBy_sup ?_
            rw [h]; exact hab
          have hlt : a ⊓ y < a := by
            rcases lt_or_eq_of_le (inf_le_left : a ⊓ y ≤ a) with h' | h'
            · exact h'
            · exfalso
              have hay' : a ≤ y := by rw [← h']; exact inf_le_right
              rw [sup_eq_right.2 hay'] at h
              exact absurd h (ne_of_lt hyb)
          rw [IH y hyb hay]
          exact height_add_one_le hlt
      gcongr
    · exact le_iSup₂_of_le a hab.lt le_rfl

end Covering

section Identity

variable [IsUpperModularLattice α] [IsLowerModularLattice α] [WellFoundedLT α] [WellFoundedGT α]

/-- **Half of Birkhoff's identity**, from semimodularity: the height function is submodular. -/
theorem height_sup_add_height_inf_le (a c : α) :
    height (a ⊔ c) + height (a ⊓ c) ≤ height a + height c := by
  induction a using WellFoundedLT.induction with
  | _ a IH =>
    by_cases hac : a ≤ c
    · rw [sup_eq_right.2 hac, inf_eq_left.2 hac, add_comm]
    · have hlt : a ⊓ c < a := by
        refine lt_of_le_of_ne inf_le_left fun hEq => hac ?_
        rw [← hEq]; exact inf_le_right
      obtain ⟨a', hle', hmax⟩ := exists_maximal_ge_of_wellFoundedGT (· < a) (a ⊓ c) hlt
      have hlt' : a' < a := hmax.prop
      have hcov : a' ⋖ a := ⟨hlt', fun t ht hta => absurd (hmax.2 hta ht.le) ht.not_ge⟩
      have hinf' : a' ⊓ c = a ⊓ c :=
        le_antisymm (inf_le_inf_right c hlt'.le) (le_inf hle' inf_le_right)
      have hha : height a = height a' + 1 := covBy_height_eq hcov
      have hsup : height (a ⊔ c) ≤ height (a' ⊔ c) + 1 := by
        rcases sup_eq_or_covBy_sup hcov c with h | h
        · rw [h]; exact le_self_add
        · exact le_of_eq (covBy_height_eq h)
      have hIH := IH a' hlt'
      calc height (a ⊔ c) + height (a ⊓ c)
          ≤ (height (a' ⊔ c) + 1) + height (a ⊓ c) := by gcongr
        _ = (height (a' ⊔ c) + height (a' ⊓ c)) + 1 := by
              rw [← hinf']; exact add_right_comm _ 1 _
        _ ≤ (height a' + height c) + 1 := by gcongr
        _ = height a + height c := by rw [hha]; exact (add_right_comm _ 1 _).symm

omit [IsUpperModularLattice α] in
/-- **The other half**, from dual semimodularity: the height function is supermodular. Only
dual semimodularity is used, since `covBy_height_eq` needs no more than that either. -/
theorem le_height_sup_add_height_inf (a c : α) :
    height a + height c ≤ height (a ⊔ c) + height (a ⊓ c) := by
  induction a using WellFoundedGT.induction with
  | _ a IH =>
    by_cases hac : c ≤ a
    · rw [sup_eq_left.2 hac, inf_eq_right.2 hac, add_comm]
    · have hlt : a < a ⊔ c := by
        refine lt_of_le_of_ne le_sup_left fun hEq => hac ?_
        rw [hEq]; exact le_sup_right
      obtain ⟨b, hle', hmin⟩ := exists_minimal_le_of_wellFoundedLT (a < ·) (a ⊔ c) hlt
      have hlt' : a < b := hmin.prop
      have hcov : a ⋖ b := ⟨hlt', fun t ht htb => absurd (hmin.2 ht htb.le) htb.not_ge⟩
      have hsup' : b ⊔ c = a ⊔ c :=
        le_antisymm (sup_le hle' le_sup_right) (sup_le_sup_right hlt'.le c)
      have hhb : height b = height a + 1 := covBy_height_eq hcov
      have hinf : height (b ⊓ c) ≤ height (a ⊓ c) + 1 := by
        rcases inf_eq_or_covBy_inf hcov c with h | h
        · rw [← h]; exact le_self_add
        · exact le_of_eq (covBy_height_eq h)
      have hIH := IH b hlt'
      have key : (height a + height c) + 1 ≤ (height (a ⊔ c) + height (a ⊓ c)) + 1 := by
        calc (height a + height c) + 1 = height b + height c := by
              rw [hhb]; exact (add_right_comm _ 1 _).symm
          _ ≤ height (b ⊔ c) + height (b ⊓ c) := hIH
          _ ≤ height (a ⊔ c) + (height (a ⊓ c) + 1) := by rw [hsup']; gcongr
          _ = (height (a ⊔ c) + height (a ⊓ c)) + 1 := (add_assoc _ _ _).symm
      exact (WithTop.add_le_add_iff_right (by simp)).1 key

/-- **Birkhoff's identity**, Theorem II.16(iii). -/
theorem height_sup_add_height_inf (a c : α) :
    height (a ⊔ c) + height (a ⊓ c) = height a + height c :=
  le_antisymm (height_sup_add_height_inf_le a c) (le_height_sup_add_height_inf a c)

end Identity

section Modular

/-- A lattice with no pentagon is modular: the failure of the modular law at `x ≤ z` produces
two distinct elements with the same meet and join against `y`. -/
theorem isModularLattice_of_forall_pentagon
    (h : ∀ x z y : α, x < z → x ⊓ y = z ⊓ y → x ⊔ y = z ⊔ y → False) : IsModularLattice α where
  sup_inf_le_assoc_of_le := by
    intro x y z hxz
    by_contra hcon
    have hle : x ⊔ y ⊓ z ≤ (x ⊔ y) ⊓ z :=
      sup_le (le_inf le_sup_left hxz) (le_inf (inf_le_left.trans le_sup_right) inf_le_right)
    have hlt : x ⊔ y ⊓ z < (x ⊔ y) ⊓ z := lt_of_le_of_ne hle fun he => hcon (le_of_eq he.symm)
    refine h _ _ y hlt ?_ ?_
    · have h1 : (x ⊔ y ⊓ z) ⊓ y = y ⊓ z :=
        le_antisymm (le_trans (inf_le_inf_right y (sup_le hxz inf_le_right))
          (le_of_eq (inf_comm z y))) (le_inf le_sup_right inf_le_left)
      have h2 : ((x ⊔ y) ⊓ z) ⊓ y = y ⊓ z :=
        le_antisymm (le_trans (inf_le_inf_right y (inf_le_right : (x ⊔ y) ⊓ z ≤ z))
          (le_of_eq (inf_comm z y)))
          (le_inf (le_inf (inf_le_left.trans le_sup_right) inf_le_right) inf_le_left)
      rw [h1, h2]
    · have h1 : (x ⊔ y ⊓ z) ⊔ y = x ⊔ y := by
        rw [sup_assoc, sup_eq_right.2 (inf_le_left : y ⊓ z ≤ y)]
      have h2 : ((x ⊔ y) ⊓ z) ⊔ y = x ⊔ y :=
        le_antisymm (sup_le inf_le_left le_sup_right)
          (sup_le (le_sup_of_le_left (le_inf le_sup_left hxz)) le_sup_right)
      rw [h1, h2]

variable [IsUpperModularLattice α] [IsLowerModularLattice α] [WellFoundedLT α] [WellFoundedGT α]

/-- **Birkhoff's theorem**, *Lattice Theory* Chapter II, Theorem 16: a lattice which is
semimodular and dually semimodular, satisfies both chain conditions and has all heights finite
is modular. -/
theorem isModularLattice_of_isUpperModular_of_isLowerModular
    (hfin : ∀ a : α, height a ≠ ⊤) : IsModularLattice α := by
  refine isModularLattice_of_forall_pentagon fun x z y hxz hinf hsup => ?_
  have h1 := height_sup_add_height_inf x y
  have h2 := height_sup_add_height_inf z y
  rw [← hinf, ← hsup] at h2
  have h3 : height x + 1 ≤ height z := height_add_one_le hxz
  have h4 : height x + 1 + height y ≤ height z + height y := by gcongr
  rw [← h2, h1] at h4
  have hne : height x + height y ≠ ⊤ := fun hcon => by
    rcases WithTop.add_eq_top.1 hcon with hx | hy
    exacts [hfin x hx, hfin y hy]
  have h5 : (height x + height y) + 1 ≤ height x + height y := by
    calc (height x + height y) + 1 = height x + 1 + height y := (add_right_comm _ 1 _).symm
      _ ≤ height x + height y := h4
  exact absurd ((ENat.add_one_le_iff hne).1 h5) (lt_irrefl _)

omit [IsUpperModularLattice α] [IsLowerModularLattice α] in
/-- **Proposition 9.34 `P:FiniteLength`.** A transposition-symmetric lattice satisfying both chain
conditions, all of whose elements have finite height, is modular. Hence on such lattices
condition (DPN) and condition (DI2) agree. -/
theorem isModularLattice_of_transpositionSymmetric (hfin : ∀ a : α, height a ≠ ⊤)
    (h : TranspositionSymmetric α) : IsModularLattice α := by
  haveI := isUpperModularLattice_of_transpositionSymmetric h
  haveI := isLowerModularLattice_of_transpositionSymmetric h
  exact isModularLattice_of_isUpperModular_of_isLowerModular hfin

omit [IsUpperModularLattice α] [IsLowerModularLattice α] [WellFoundedLT α] [WellFoundedGT α] in
/-- Finite length in Birkhoff's sense — a bound on the lengths of chains — gives the finiteness
the two theorems above consume. -/
theorem height_ne_top_of_krullDim_lt_top (hdim : krullDim α < ⊤) (a : α) : height a ≠ ⊤ :=
  (WithBot.coe_lt_coe.mp (lt_of_le_of_lt (height_le_krullDim a) hdim)).ne

omit [IsUpperModularLattice α] [IsLowerModularLattice α] [WellFoundedLT α] [WellFoundedGT α] in
/-- **`P:FiniteLength` at exactly the paper's hypothesis.** A lattice of finite length which is
transposition-symmetric is modular. Finite length — `krullDim α < ⊤` — supplies both chain
conditions itself, through `FiniteDimensionalOrder`, so neither is assumed. -/
theorem isModularLattice_of_transpositionSymmetric_of_krullDim (hdim : krullDim α < ⊤)
    (h : TranspositionSymmetric α) : IsModularLattice α := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨fun {x} _ _ _ => (IsEmpty.false x).elim⟩
  · haveI : FiniteDimensionalOrder α :=
      Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.2
        ⟨Order.krullDim_ne_bot_iff.2 hα, hdim.ne⟩
    haveI : WellFoundedLT α :=
      ⟨SetRel.IsWellFounded.of_finiteDimensional {(a, b) : α × α | a < b}⟩
    haveI : WellFoundedGT α :=
      ⟨SetRel.IsWellFounded.inv_of_finiteDimensional {(a, b) : α × α | a < b}⟩
    exact isModularLattice_of_transpositionSymmetric (height_ne_top_of_krullDim_lt_top hdim) h

end Modular

end SnakeLean
