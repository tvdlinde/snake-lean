/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.ModularPair
import Mathlib.Order.Minimal
import Mathlib.Order.Cover

/-!
# Transposition-symmetry implies semimodularity

This module is the first half of Proposition 9.34 `P:FiniteLength`: a lattice of finite
length which is transposition-symmetric is modular. What is proved here is the step that is the
paper's own, that transposition-symmetry forces semimodularity; the classical theorem of Birkhoff
which converts semimodularity in both directions into modularity is `SnakeLean.Birkhoff`.

## The hypothesis

The paper says "of finite length". Only the **ascending** chain condition is used, and only to
ascend from a witness `w` to a maximal element below `a ⊔ b`, so the hypothesis here is
`WellFoundedGT`. The dual half needs the descending chain condition, and the two together are
weaker than finite length: they say every chain is finite, not that the lengths are bounded.
Birkhoff's theorem needs both.

## The argument

Let `a ⊓ b ⋖ a` and suppose `a ⊔ b` does not cover `b`, so that there is `w` with
`b < w < a ⊔ b`. Ascend from `w` to an element `B` maximal below `a ⊔ b`; then `B ⋖ a ⊔ b`, and
`B ⊓ a = a ⊓ b` because `B ⊓ a` lies between `a ⊓ b` and `a`, and taking the value `a` would put
`a ⊔ b` below `B`. The transposition at `(B, a)` runs from `[a ⊓ b, B]` to `[a, a ⊔ b]`, and its
unit fails at `b`, since `(b ⊔ a) ⊓ B = B ≠ b`. Transposition-symmetry therefore denies the
transposition at `(a, B)`. But that one runs from `[a ⊓ b, a]` to `[B, a ⊔ b]`, both two-element
chains by the two coverings, and it is an isomorphism — a contradiction.
-/

namespace SnakeLean

open OrderDual

variable {α : Type*} [Lattice α]

/-- **The first half of `P:FiniteLength`.** A transposition-symmetric lattice satisfying the
ascending chain condition is semimodular. -/
theorem isUpperModularLattice_of_transpositionSymmetric [WellFoundedGT α]
    (h : TranspositionSymmetric α) : IsUpperModularLattice α where
  covBy_sup_of_inf_covBy := by
    intro a b hcov
    have hba : b < a ⊔ b := by
      rcases lt_or_eq_of_le (le_sup_right : b ≤ a ⊔ b) with h' | h'
      · exact h'
      · exact absurd (inf_eq_left.2 (le_sup_left.trans h'.ge)) (ne_of_lt hcov.lt)
    refine ⟨hba, ?_⟩
    intro w hw hwab
    -- Ascend from `w` to an element `B` maximal below `a ⊔ b`.
    obtain ⟨B, hwB, hBmax⟩ := exists_maximal_ge_of_wellFoundedGT (· < a ⊔ b) w hwab
    have hBab : B < a ⊔ b := hBmax.prop
    have hbB : b < B := hw.trans_le hwB
    have hBcov : B ⋖ a ⊔ b := ⟨hBab, fun c hc hcab => absurd (hBmax.2 hcab hc.le) hc.not_ge⟩
    -- `B ⊓ a = a ⊓ b`: the value `a` would force `a ⊔ b ≤ B`.
    have hBa : B ⊓ a = a ⊓ b := by
      have h1 : a ⊓ b ≤ B ⊓ a := le_inf (inf_le_right.trans hbB.le) inf_le_left
      rcases hcov.eq_or_eq h1 inf_le_right with heq | heq
      · exact heq
      · exfalso
        have hat : a ≤ B := by rw [← heq]; exact inf_le_left
        exact absurd (sup_le hat hbB.le) hBab.not_ge
    have haB : a ⊓ B = a ⊓ b := by rw [inf_comm]; exact hBa
    have haBsup : a ⊔ B = a ⊔ b :=
      le_antisymm (sup_le le_sup_left hBab.le) (sup_le le_sup_left (hbB.le.trans le_sup_right))
    -- The transposition at `(B, a)` is not invertible: its unit fails at `b`.
    have hnot : ¬ Transposes B a := by
      intro hT
      have hb := hT.1 b (by rw [hBa]; exact inf_le_right) hbB.le
      rw [sup_comm b a, inf_eq_right.2 hBab.le] at hb
      exact absurd hb.symm (ne_of_lt hbB)
    -- But the transposition at `(a, B)` is: both intervals are two-element chains.
    refine hnot (h a B ⟨fun x hx hxa => ?_, fun z hz hza => ?_⟩)
    · rw [haB] at hx
      rcases hcov.eq_or_eq hx hxa with rfl | rfl
      · rw [sup_eq_right.2 (inf_le_right.trans hbB.le)]
        exact hBa
      · exact inf_eq_right.2 le_sup_left
    · rw [haBsup] at hza
      rcases hBcov.eq_or_eq hz hza with rfl | rfl
      · exact sup_eq_right.2 inf_le_left
      · rw [inf_eq_right.2 (le_sup_left : a ≤ a ⊔ b)]
        exact haBsup

/-- **The dual half**, by transport along the order dual rather than a second proof: a
transposition-symmetric lattice satisfying the descending chain condition is dually
semimodular. -/
theorem isLowerModularLattice_of_transpositionSymmetric [WellFoundedLT α]
    (h : TranspositionSymmetric α) : IsLowerModularLattice α where
  inf_covBy_of_covBy_sup := by
    intro a b hcov
    haveI : IsUpperModularLattice αᵒᵈ :=
      isUpperModularLattice_of_transpositionSymmetric (transpositionSymmetric_orderDual.2 h)
    have := IsUpperModularLattice.covBy_sup_of_inf_covBy
      (a := toDual a) (b := toDual b) hcov.toDual
    exact toDual_covBy_toDual_iff.1 this

end SnakeLean
