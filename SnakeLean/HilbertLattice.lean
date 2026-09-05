/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.ModularPair
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Hilbert lattices are transposition-symmetric

Proposition 9.31 `P:HilbertSymmetric`. In the lattice of closed subspaces of a Hilbert space the
transposition of `A` and `B` is invertible exactly when `A + B` and `Aᗮ + Bᗮ` are closed — a
criterion manifestly symmetric in `A` and `B`, so the lattice is transposition-symmetric and, by
`SnakeLean.LatticeNSD`, the corresponding 2-category satisfies condition (DPN). It is **not**
modular, so it is not 2-di-exact: this is the model of Theorem 9.32 `T:HilbertModel`. Only the
lattice-level statement is proved here — what is missing for 9.32 is at the end of this
docstring.

Mathlib supplies the lattice: `ClosedSubmodule 𝕜 E` is a complete lattice whose meet is the
intersection and whose join is the closure of the sum, with the orthogonal complement and both
De Morgan laws attached.

## Mackey's theorem

`dualModularPair_iff_isClosed_sup` is Theorem III-6 of Mackey's *On infinite-dimensional linear
spaces*: `(A, B)` is a dual modular pair if and only if `A + B` is closed. Both directions are
elementary, as they are in Mackey. The forward direction needs that a closed subspace plus a line
is closed, which is `isClosed_sup_span_singleton` below and is where the inner product is used:
the line may be taken orthogonal to the subspace, and then the sum is the kernel of a continuous
map. The `ᗮ`-flip `modularPair_iff_dualModularPair_orthogonal` is Theorem 5(i) of Schreiner,
as in the paper; Kato's duality, which the paper cites only to collapse the criterion to
closedness of `A + B` alone, is not needed and not formalised.

## Not formalised

The 2-category `Suphil` itself: the `LatticeClass` of Hilbert lattices needs `↓A ≅ L(A)` and
`↑B ≅ L(Bᗮ)`, which is plumbing through `ClosedSubmodule.comap` along the subtype, and with it
the (DPN) instance that `dpn_of_forall_transpositionSymmetric` would give. And the witness of
Theorem 9.32 that `L(H)` is not modular — the two closed subspaces of `ℓ²` whose sum is not
closed — so that the theorem's negative clause is not machine-checked either.
-/

namespace SnakeLean

open Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

section Elementary

variable {A Bb : ClosedSubmodule 𝕜 E}

/-- If the algebraic sum is closed, the join is the algebraic sum. -/
theorem toSubmodule_sup_of_isClosed
    (h : IsClosed ((A.toSubmodule ⊔ Bb.toSubmodule : Submodule 𝕜 E) : Set E)) :
    (A ⊔ Bb).toSubmodule = A.toSubmodule ⊔ Bb.toSubmodule := by
  rw [ClosedSubmodule.toSubmodule_sup, Submodule.closure_eq' h]

/-- **Mackey's Theorem III-6, the elementary half.** If `A + B` is closed then `(A, B)` is a dual
modular pair. -/
theorem dualModularPair_of_isClosed_sup
    (h : IsClosed ((A.toSubmodule ⊔ Bb.toSubmodule : Submodule 𝕜 E) : Set E)) :
    DualModularPair A Bb := by
  intro K hK
  refine le_antisymm (sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_left))
    (le_inf hK le_sup_right)) ?_
  intro x hx
  obtain ⟨hxK, hxAB⟩ := hx
  have hxsum : x ∈ A.toSubmodule ⊔ Bb.toSubmodule := by
    have hx' : x ∈ (A ⊔ Bb).toSubmodule := hxAB
    rwa [toSubmodule_sup_of_isClosed h] at hx'
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxsum
  have hzK : z ∈ K.toSubmodule := hK hz
  have hyK : y ∈ K.toSubmodule := by
    have hyz : y = (y + z) - z := (add_sub_cancel_right y z).symm
    rw [hyz]
    exact Submodule.sub_mem _ hxK hzK
  exact add_mem (SetLike.le_def.mp le_sup_left (show y ∈ K ⊓ A from ⟨hyK, hy⟩))
    (SetLike.le_def.mp le_sup_right hz)

end Elementary

section Orthogonal

variable [CompleteSpace E] {A Bb : ClosedSubmodule 𝕜 E}

/-- **The `ᗮ`-flip**, Theorem 5(i) of Schreiner: a modular pair is a dual modular pair of the
orthogonal complements. The orthogonal complement is an order-reversing involution exchanging
meets with joins, so this is the self-duality of the lattice made explicit. -/
theorem modularPair_iff_dualModularPair_orthogonal :
    ModularPair A Bb ↔ DualModularPair Aᗮ Bbᗮ := by
  constructor
  · intro h C hC
    have hCB : Cᗮ ≤ Bb := by
      have := ClosedSubmodule.orthogonal_le hC
      rwa [ClosedSubmodule.orthogonal_orthogonal_eq] at this
    have hh := congrArg (fun S : ClosedSubmodule 𝕜 E => Sᗮ) (h Cᗮ hCB)
    simp only [← ClosedSubmodule.inf_orthogonal, ← ClosedSubmodule.sup_orthogonal,
      ClosedSubmodule.orthogonal_orthogonal_eq] at hh
    exact hh
  · intro h c hc
    have hC : Bbᗮ ≤ cᗮ := ClosedSubmodule.orthogonal_le hc
    have hh := congrArg (fun S : ClosedSubmodule 𝕜 E => Sᗮ) (h cᗮ hC)
    simp only [← ClosedSubmodule.inf_orthogonal, ← ClosedSubmodule.sup_orthogonal,
      ClosedSubmodule.orthogonal_orthogonal_eq] at hh
    exact hh

end Orthogonal

section ClosedSum

variable [CompleteSpace E]

/-- **A closed subspace plus a line is closed.** Mathlib has that a finite-dimensional subspace
is closed, but not that a sum with one is; in a Hilbert space the line may be taken orthogonal
to the subspace, and then the sum is the kernel of a continuous map. This is what makes the
converse half of Mackey's theorem work — his `K = M + x` — and what the counterexample of
Theorem 9.32 `T:HilbertModel` would need in order to know the elements of `Z = B ∨ ⟨v⟩`. -/
theorem isClosed_sup_span_singleton (B : ClosedSubmodule 𝕜 E) (x : E) :
    IsClosed ((B.toSubmodule ⊔ 𝕜 ∙ x : Submodule 𝕜 E) : Set E) := by
  have hqperp : x - B.toSubmodule.starProjection x ∈ B.toSubmoduleᗮ :=
    Submodule.sub_starProjection_mem_orthogonal x
  have hPmem : B.toSubmodule.starProjection x ∈ B.toSubmodule :=
    Submodule.starProjection_apply_mem _ x
  -- Replace `x` by its component orthogonal to `B`.
  have hsum : (B.toSubmodule ⊔ 𝕜 ∙ x : Submodule 𝕜 E)
      = B.toSubmodule ⊔ 𝕜 ∙ (x - B.toSubmodule.starProjection x) := by
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
    · rw [Submodule.span_singleton_le_iff_mem]
      have hx : B.toSubmodule.starProjection x + (x - B.toSubmodule.starProjection x)
          ∈ (B.toSubmodule ⊔ 𝕜 ∙ (x - B.toSubmodule.starProjection x) : Submodule 𝕜 E) :=
        Submodule.add_mem _ (Submodule.mem_sup_left hPmem)
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      simpa using hx
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
        (Submodule.mem_sup_left hPmem)
  rw [hsum]
  -- The orthogonal sum is the kernel of `1 - P - Q`.
  have hker : (B.toSubmodule ⊔ 𝕜 ∙ (x - B.toSubmodule.starProjection x) : Submodule 𝕜 E)
      = LinearMap.ker ((ContinuousLinearMap.id 𝕜 E - B.toSubmodule.starProjection
          - (𝕜 ∙ (x - B.toSubmodule.starProjection x)).starProjection : E →L[𝕜] E)
        : E →ₗ[𝕜] E) := by
    refine le_antisymm (sup_le (fun y hy => ?_) (fun y hy => ?_)) (fun y hy => ?_)
    · have hPy : B.toSubmodule.starProjection y = y := Submodule.starProjection_eq_self_iff.mpr hy
      have hQy : (𝕜 ∙ (x - B.toSubmodule.starProjection x)).starProjection y = 0 := by
        refine (Submodule.starProjection_apply_eq_zero_iff _).mpr ?_
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
        exact inner_eq_zero_symm.mp (hqperp y hy)
      simp [LinearMap.mem_ker, hPy, hQy]
    · have hPy : B.toSubmodule.starProjection y = 0 := by
        refine (Submodule.starProjection_apply_eq_zero_iff _).mpr ?_
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
        exact Submodule.smul_mem _ c hqperp
      have hQy : (𝕜 ∙ (x - B.toSubmodule.starProjection x)).starProjection y = y :=
        Submodule.starProjection_eq_self_iff.mpr hy
      simp [LinearMap.mem_ker, hPy, hQy]
    · simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.id_apply] at hy
      have hyeq : y = B.toSubmodule.starProjection y
          + (𝕜 ∙ (x - B.toSubmodule.starProjection x)).starProjection y := by
        refine sub_eq_zero.mp ?_
        rw [← sub_sub]
        exact hy
      rw [hyeq]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.starProjection_apply_mem _ y))
        (Submodule.mem_sup_right (Submodule.starProjection_apply_mem _ y))
  rw [hker]
  exact ContinuousLinearMap.isClosed_ker _

end ClosedSum

section Mackey

variable [CompleteSpace E] {A Bb : ClosedSubmodule 𝕜 E}

/-- **Mackey's Theorem III-6.** `(A, B)` is a dual modular pair if and only if `A + B` is closed.
The converse half is Mackey's own argument: if `A + B` is not closed, pick `x` in the closure but
not in the sum and test the dual modular law at `K = B + ⟨x⟩`, which is closed by
`isClosed_sup_span_singleton`; then `K ⊓ A ≤ B`, because a nonzero multiple of `x` in `K ⊓ A`
would put `x` into `A + B`. -/
theorem dualModularPair_iff_isClosed_sup :
    DualModularPair A Bb ↔
      IsClosed ((A.toSubmodule ⊔ Bb.toSubmodule : Submodule 𝕜 E) : Set E) := by
  refine ⟨fun h => ?_, dualModularPair_of_isClosed_sup⟩
  by_contra hnc
  obtain ⟨x, hxc, hxn⟩ := Set.not_subset.mp
    (fun hsub => hnc (closure_subset_iff_isClosed.mp hsub))
  -- `x` lies in the join but not in the algebraic sum.
  have hxAB : x ∈ (A ⊔ Bb : ClosedSubmodule 𝕜 E) := hxc
  -- `K = B + ⟨x⟩` is closed, contains `B`, and sits inside the join.
  let K : ClosedSubmodule 𝕜 E := ⟨Bb.toSubmodule ⊔ 𝕜 ∙ x, isClosed_sup_span_singleton Bb x⟩
  have hBK : Bb ≤ K := fun y hy => Submodule.mem_sup_left hy
  have hKAB : K ≤ A ⊔ Bb := by
    intro y hy
    obtain ⟨u, hu, z, hz, rfl⟩ :=
      Submodule.mem_sup.mp (show y ∈ Bb.toSubmodule ⊔ 𝕜 ∙ x from hy)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact add_mem (SetLike.le_def.mp le_sup_right hu) (smul_mem _ c hxAB)
  -- `K ⊓ A ≤ B`, since a nonzero multiple of `x` there would put `x` into `A + B`.
  have hKA : K ⊓ A ≤ Bb := by
    intro y hy
    obtain ⟨hyK, hyA⟩ := hy
    obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.mp hyK
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rcases eq_or_ne c 0 with rfl | hc
    · simpa using hu
    · exfalso
      refine hxn ?_
      have hxeq : x = c⁻¹ • ((u + c • x) - u) := by
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hxeq]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
      · exact Submodule.mem_sup_left hyA
      · exact Submodule.mem_sup_right hu
  -- The dual modular law at `K` then says `B = K`, which `x` contradicts.
  have hcon := h K hBK
  rw [sup_eq_right.mpr hKA, inf_eq_left.mpr hKAB] at hcon
  refine hxn (Submodule.mem_sup_right ?_)
  have hxK : x ∈ K :=
    show x ∈ Bb.toSubmodule ⊔ 𝕜 ∙ x from
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  rw [← hcon] at hxK
  exact hxK

/-- **Proposition 9.31 `P:HilbertSymmetric`.** The transposition of `A` and `B` in the lattice of
closed subspaces of a Hilbert space is invertible exactly when `A + B` and `Aᗮ + Bᗮ` are both
closed. The unit half is Mackey's theorem and the counit half is Mackey's theorem after the
`ᗮ`-flip. -/
theorem transposes_iff_isClosed :
    Transposes A Bb ↔
      IsClosed ((A.toSubmodule ⊔ Bb.toSubmodule : Submodule 𝕜 E) : Set E) ∧
        IsClosed (((Aᗮ : ClosedSubmodule 𝕜 E).toSubmodule
          ⊔ (Bbᗮ : ClosedSubmodule 𝕜 E).toSubmodule : Submodule 𝕜 E) : Set E) := by
  rw [transposes_iff, modularPair_iff_dualModularPair_orthogonal,
    dualModularPair_iff_isClosed_sup, dualModularPair_iff_isClosed_sup, and_comm,
    sup_comm (Bbᗮ : ClosedSubmodule 𝕜 E).toSubmodule]

/-- **The lattice of closed subspaces of a Hilbert space is transposition-symmetric**, because
the criterion of `transposes_iff_isClosed` is symmetric in `A` and `B`. With
`SnakeLean.LatticeNSD.dpn_of_forall_transpositionSymmetric` this is condition (DPN) for the
2-category of Hilbert lattices, once that 2-category is built: the model of Theorem 9.32
`T:HilbertModel`, and the last clause of Proposition 9.31. -/
theorem transpositionSymmetric_closedSubmodule :
    TranspositionSymmetric (ClosedSubmodule 𝕜 E) := by
  intro A Bb h
  rw [transposes_iff_isClosed] at h ⊢
  exact ⟨by rw [sup_comm]; exact h.1, by rw [sup_comm]; exact h.2⟩

end Mackey

end SnakeLean
