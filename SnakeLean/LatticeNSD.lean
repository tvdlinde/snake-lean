/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.LatticeModel
import SnakeLean.NonSelfDual

/-!
# The non-self-dual hypotheses on a class of lattices

Proposition 9.29 `P:SupClass`: for a class of complete lattices closed under segments, condition
(DI2) says that every member is modular (`twoDiExact_of_forall_isModularLattice`) and condition
(DPN) says that every member is **transposition-symmetric**. This module proves the second half in
both directions (`dpn_of_forall_transpositionSymmetric`, `transpositionSymmetric_of_dpn`), which is
what Section 9.28 `SS:NSDHilbert` needs: the Hilbert lattices are transposition-symmetric
(`SnakeLean.HilbertLattice`) and not modular, so they satisfy the hypotheses of Theorem 9.19
`T:SnakeNonSelfDual` without being 2-di-exact (Theorem 9.32 `T:HilbertModel`). It also proves
that every such class is homologically self-dual (`isHSD_sup`) and that its normal
2-monomorphisms and normal 2-epimorphisms compose (`normalMonoCompSup`, `normalEpiCompSup` —
the closure properties Proposition 9.29 transfers from Corollary 8.34 `C:SupNormal`), which with
the class of all complete lattices (`SupAll`) is all of Proposition 8.38 `P:SupNotDPN` but its
last clause; that clause, the failure of (DPN) at the pentagon, is `not_dpn_supAll` in
`SnakeLean.Pentagon`.

The reduction is Proposition 8.35 `P:SupAntinormal` in the sharp form
`isNormal_segIncl_comp_upProj_iff`: an
antinormal pair of `Sup_C` is, up to equivalences, a segment inclusion followed by a
join-projection, its composite is `c_{a,b}` and its dinversion is `c_{b,a}`, and `c_{a,b}` is
normal exactly when `a` and `b` transpose.
-/

universe u

namespace SnakeLean

open CategoryTheory Bicategory Set

variable {C : LatticeClass.{u}}

/-- Postcomposing with an equivalence does not change the top of the 2-kernel. -/
theorem kerElt_comp_isEquiv1 {L M N : (SupOf C)} (f : L ⟶ M) {ψ : M ⟶ N} (hψ : IsEquiv1 ψ) :
    kerElt (f ≫ ψ) = kerElt f := by
  have hinj := (bijective_of_isEquiv1 hψ).1
  refine congrArg sSup (Set.ext fun x => ?_)
  simp only [Set.mem_setOf_eq, comp_apply']
  exact ⟨fun h => hinj (by rw [h, map_bot]), fun h => by rw [h, map_bot]⟩

/-- The 2-kernel of a join-projection is the segment it projects away. -/
theorem kerElt_upProj {L : (SupOf C)} (b : L.carrier) : kerElt (upProj b) = b := by
  have hset : {x : L.carrier | upProj b x = ⊥} = Set.Iic b := by
    ext x
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      rw [upProj_apply, Ici.coe_bot] at h'
      exact sup_eq_right.1 h'
    · intro h
      apply Subtype.ext
      rw [upProj_apply, Ici.coe_bot]
      exact sup_eq_right.2 h
  rw [kerElt, hset]
  exact le_antisymm (sSup_le fun _ hx => hx) (le_sSup le_rfl)

/-- An equivalence preserves the top element. -/
theorem apply_top_of_isEquiv1 {L M : (SupOf C)} {φ : L ⟶ M} (hφ : IsEquiv1 φ) :
    φ ⊤ = ⊤ := by
  obtain ⟨x, hx⟩ := (bijective_of_isEquiv1 hφ).2 ⊤
  exact le_antisymm le_top (hx ▸ OrderHomClass.mono φ le_top)

/-- **Proposition 9.29 `P:SupClass`, the (DPN) half.** A class of complete lattices satisfies
condition (DPN) as soon as each of its members is transposition-symmetric: an antinormal pair is a
segment inclusion followed by a join-projection up to equivalences, its composite is `c_{a,b}` and
its dinversion is `c_{b,a}`, and `isNormal_segIncl_comp_upProj_iff` turns normality of the two into
`Transposes a b` and `Transposes b a`. -/
theorem dpn_of_forall_transpositionSymmetric
    (hsym : ∀ L : (SupOf C), TranspositionSymmetric L.carrier) : DPN (zeroSup C) where
  isNormal_comp_iff := by
    intro K X R N Q m e k q hm he hk hq
    obtain ⟨Y, g₁, hkm⟩ := hm
    obtain ⟨Z, g₂, hqe⟩ := he
    obtain ⟨φ, hφ, rfl⟩ := exists_isEquiv1_of_isTwoKernel hkm
    obtain ⟨ψ, hψ, rfl⟩ := exists_isEquiv1_of_isTwoCokernel hqe
    obtain ⟨φ', hφ', hk'⟩ := exists_isEquiv1_of_isTwoKernel hk
    obtain ⟨ψ', hψ', hq'⟩ := exists_isEquiv1_of_isTwoCokernel hq
    have hA : ((φ ≫ segIncl (kerElt g₁)) ⊤ : X.carrier) = kerElt g₁ := by
      rw [comp_apply', apply_top_of_isEquiv1 hφ]
      rfl
    have hB : kerElt (upProj (g₂ ⊤) ≫ ψ) = g₂ ⊤ := by
      rw [kerElt_comp_isEquiv1 _ hψ, kerElt_upProj]
    have h₁ : IsNormal (zeroSup C) ((φ ≫ segIncl (kerElt g₁)) ≫ (upProj (g₂ ⊤) ≫ ψ))
        ↔ Transposes (kerElt g₁) (g₂ ⊤) := by
      rw [show (φ ≫ segIncl (kerElt g₁)) ≫ (upProj (g₂ ⊤) ≫ ψ)
          = φ ≫ (segIncl (kerElt g₁) ≫ upProj (g₂ ⊤)) ≫ ψ from rfl,
        isNormal_transport_iff hφ hψ]
      exact isNormal_segIncl_comp_upProj_iff
    have h₂ : IsNormal (zeroSup C) (k ≫ q)
        ↔ Transposes (kerElt (upProj (g₂ ⊤) ≫ ψ)) ((φ ≫ segIncl (kerElt g₁)) ⊤) := by
      rw [hk', hq', show (φ' ≫ segIncl (kerElt (upProj (g₂ ⊤) ≫ ψ)))
            ≫ (upProj ((φ ≫ segIncl (kerElt g₁)) ⊤) ≫ ψ')
          = φ' ≫ (segIncl (kerElt (upProj (g₂ ⊤) ≫ ψ))
            ≫ upProj ((φ ≫ segIncl (kerElt g₁)) ⊤)) ≫ ψ' from rfl,
        isNormal_transport_iff hφ' hψ']
      exact isNormal_segIncl_comp_upProj_iff
    rw [h₁, h₂, hA, hB]
    exact ⟨hsym X _ _, hsym X _ _⟩

/-- **Proposition 9.29 `P:SupClass`, the (DPN) half, converse direction.** If `Sup_C` satisfies
(DPN) then every member is transposition-symmetric: (DPN) at the antinormal pair `(segIncl a, upProj
b)`, whose dinversion is `segIncl b ≫ upProj a`, turns `Transposes a b` into `Transposes b a`. -/
theorem transpositionSymmetric_of_dpn [DPN (zeroSup C)] (L : (SupOf C)) :
    TranspositionSymmetric L.carrier := fun a b hab =>
  isNormal_segIncl_comp_upProj_iff.1
    ((DPN.isNormal_comp_iff ⟨_, _, isTwoKernel_upProj_segIncl a⟩
      ⟨_, _, isTwoCokernel_segIncl_upProj b⟩ (isTwoKernel_upProj_segIncl b)
      (isTwoCokernel_segIncl_upProj a)).1 (isNormal_segIncl_comp_upProj_iff.2 hab))

/-- **Proposition 9.29 `P:SupClass`, the (DPN) half in full**: `Sup_C` satisfies condition (DPN)
exactly when every member of `C` is transposition-symmetric. -/
theorem dpn_iff_forall_transpositionSymmetric :
    DPN (zeroSup C) ↔ ∀ L : (SupOf C), TranspositionSymmetric L.carrier :=
  ⟨fun _ => transpositionSymmetric_of_dpn, dpn_of_forall_transpositionSymmetric⟩

/-- **Every class of complete lattices is homologically self-dual.** An antinormal decomposition of
the zero map is, up to equivalences, `(segIncl a, upProj b)` with `a ≤ b` — nullity of the composite
says exactly that — and its dinversion is `segIncl b ≫ upProj a`, which is normal because the
transposition of `b` and `a` is the identity of `[a, b]` (`transposes_of_le`). Together with
`normalEpiCompSup` and `normalMonoCompSup` this is Proposition 8.38 `P:SupNotDPN` short of its last
clause, that (DPN) fails for the class of all complete lattices, which is `not_dpn_supAll` in
`SnakeLean.Pentagon`. -/
theorem isHSD_sup : IsHSD (zeroSup C) := by
  intro K X R N Q m e hme k q hk hq
  obtain ⟨Y, g₁, hkm⟩ := hme.isNormalMono
  obtain ⟨Z, g₂, hqe⟩ := hme.isNormalEpi
  obtain ⟨φ, hφ, rfl⟩ := exists_isEquiv1_of_isTwoKernel hkm
  obtain ⟨ψ, hψ, rfl⟩ := exists_isEquiv1_of_isTwoCokernel hqe
  obtain ⟨φ', hφ', hk'⟩ := exists_isEquiv1_of_isTwoKernel hk
  obtain ⟨ψ', hψ', hq'⟩ := exists_isEquiv1_of_isTwoCokernel hq
  -- The composite is null, so the top of the 2-kernel lies below the bottom of the 2-cokernel.
  have hle : kerElt g₁ ≤ g₂ ⊤ := by
    obtain ⟨x, hx⟩ := (bijective_of_isEquiv1 hφ).2 ⟨kerElt g₁, le_rfl⟩
    have h1 : ψ (upProj (g₂ ⊤) (segIncl (kerElt g₁) (φ x))) = ⊥ :=
      isEssNull_iff_forall.mp hme.isEssNull_comp x
    have h2 : upProj (g₂ ⊤) (segIncl (kerElt g₁) (φ x)) = ⊥ :=
      (bijective_of_isEquiv1 hψ).1 (by rw [h1, map_bot])
    have h3 := congrArg Subtype.val h2
    rw [upProj_apply, Ici.coe_bot, segIncl_apply, hx] at h3
    exact sup_eq_right.1 h3
  have hA : ((φ ≫ segIncl (kerElt g₁)) ⊤ : X.carrier) = kerElt g₁ := by
    rw [comp_apply', apply_top_of_isEquiv1 hφ]
    rfl
  have hB : kerElt (upProj (g₂ ⊤) ≫ ψ) = g₂ ⊤ := by
    rw [kerElt_comp_isEquiv1 _ hψ, kerElt_upProj]
  rw [hk', hq', show (φ' ≫ segIncl (kerElt (upProj (g₂ ⊤) ≫ ψ)))
        ≫ (upProj ((φ ≫ segIncl (kerElt g₁)) ⊤) ≫ ψ')
      = φ' ≫ (segIncl (kerElt (upProj (g₂ ⊤) ≫ ψ))
        ≫ upProj ((φ ≫ segIncl (kerElt g₁)) ⊤)) ≫ ψ' from rfl,
    isNormal_transport_iff hφ' hψ', isNormal_segIncl_comp_upProj_iff, hA, hB]
  exact transposes_of_le hle

/-! ## The two composition closures -/

/-- An up-segment of an up-segment is an up-segment: joining twice is joining once. -/
theorem exists_isEquiv1_upProj_comp {L : (SupOf C)} (s : L.carrier) (r : upSeg s) :
    ∃ ι : upSeg (((r : Set.Ici s) : L.carrier)) ⟶ upSeg r, IsEquiv1 ι ∧
      upProj s ≫ upProj r = upProj (((r : Set.Ici s) : L.carrier)) ≫ ι := by
  have hsr : s ≤ ((r : Set.Ici s) : L.carrier) := r.2
  refine ⟨orderIsoHom
    { toFun := fun x => ⟨⟨(x : L.carrier), le_trans hsr x.2⟩, x.2⟩
      invFun := fun y => ⟨(((y : Set.Ici s) : L.carrier)), y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl },
    isEquiv1_orderIsoHom _, ?_⟩
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext; apply Subtype.ext
  change ((x : L.carrier) ⊔ s) ⊔ ((r : Set.Ici s) : L.carrier)
    = (x : L.carrier) ⊔ ((r : Set.Ici s) : L.carrier)
  rw [sup_assoc, sup_eq_right.2 hsr]

/-- **Proposition 9.29 `P:SupClass`: normal 2-epimorphisms compose.** They are the join-projections
up to equivalence, and joining twice is joining once. -/
instance normalEpiCompSup : NormalEpiComp (zeroSup C) where
  isNormalEpi_comp := by
    intro L M N e₁ e₂ h₁ h₂
    obtain ⟨Z₁, g₁, hq₁⟩ := h₁
    obtain ⟨Z₂, g₂, hq₂⟩ := h₂
    obtain ⟨ψ₁, hψ₁, rfl⟩ := exists_isEquiv1_of_isTwoCokernel hq₁
    obtain ⟨ψ₂, hψ₂, rfl⟩ := exists_isEquiv1_of_isTwoCokernel hq₂
    have hmid : IsNormalEpi (zeroSup C) (ψ₁ ≫ upProj (g₂ ⊤)) :=
      IsNormalEpi.isEquiv1_comp ⟨_, _, isTwoCokernel_segIncl_upProj _⟩ hψ₁
    obtain ⟨W, g₃, hq₃⟩ := hmid
    obtain ⟨ψ₃, hψ₃, hmid'⟩ := exists_isEquiv1_of_isTwoCokernel hq₃
    obtain ⟨ι, hι, hstep⟩ := exists_isEquiv1_upProj_comp (g₁ ⊤) (g₃ ⊤)
    have hcomp : (upProj (g₁ ⊤) ≫ ψ₁) ≫ (upProj (g₂ ⊤) ≫ ψ₂)
        = upProj (((g₃ ⊤ : Set.Ici (g₁ ⊤)) : L.carrier)) ≫ (ι ≫ ψ₃ ≫ ψ₂) := by
      have : (upProj (g₁ ⊤) ≫ ψ₁) ≫ (upProj (g₂ ⊤) ≫ ψ₂)
          = (upProj (g₁ ⊤) ≫ (ψ₁ ≫ upProj (g₂ ⊤))) ≫ ψ₂ := rfl
      rw [this, hmid']
      have : (upProj (g₁ ⊤) ≫ (upProj (g₃ ⊤) ≫ ψ₃)) ≫ ψ₂
          = ((upProj (g₁ ⊤) ≫ upProj (g₃ ⊤)) ≫ ψ₃) ≫ ψ₂ := rfl
      rw [this, hstep]
      rfl
    rw [hcomp]
    exact IsNormalEpi.comp_isEquiv1 ⟨_, _, isTwoCokernel_segIncl_upProj _⟩
      (hι.comp (hψ₃.comp hψ₂))

/-- A down-segment of a down-segment is a down-segment. -/
theorem exists_isEquiv1_segIncl_comp {L : (SupOf C)} (a : L.carrier) (t : seg a) :
    ∃ ι : seg t ⟶ seg (((t : Set.Iic a) : L.carrier)), IsEquiv1 ι ∧
      segIncl t ≫ segIncl a = ι ≫ segIncl (((t : Set.Iic a) : L.carrier)) :=
  ⟨orderIsoHom
    { toFun := fun x => ⟨(((x : Set.Iic a) : L.carrier)), x.2⟩
      invFun := fun y => ⟨⟨(y : L.carrier), le_trans y.2 t.2⟩, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl },
    isEquiv1_orderIsoHom _, DFunLike.ext _ _ fun _ => rfl⟩

/-- **Proposition 9.29 `P:SupClass`: normal 2-monomorphisms compose.** They are the down-segment
inclusions up to equivalence, and a down-segment of a down-segment is a down-segment. -/
instance normalMonoCompSup : NormalMonoComp (zeroSup C) where
  isNormalMono_comp := by
    intro L M N m₁ m₂ h₁ h₂
    obtain ⟨Y₁, g₁, hk₁⟩ := h₁
    obtain ⟨Y₂, g₂, hk₂⟩ := h₂
    obtain ⟨φ₁, hφ₁, rfl⟩ := exists_isEquiv1_of_isTwoKernel hk₁
    obtain ⟨φ₂, hφ₂, rfl⟩ := exists_isEquiv1_of_isTwoKernel hk₂
    have hmid : IsNormalMono (zeroSup C) (segIncl (kerElt g₁) ≫ φ₂) :=
      IsNormalMono.comp_isEquiv1 ⟨_, _, isTwoKernel_upProj_segIncl _⟩ hφ₂
    obtain ⟨W, g₃, hk₃⟩ := hmid
    obtain ⟨φ₃, hφ₃, hmid'⟩ := exists_isEquiv1_of_isTwoKernel hk₃
    obtain ⟨ι, hι, hstep⟩ := exists_isEquiv1_segIncl_comp (kerElt g₂) (kerElt g₃)
    have hcomp : (φ₁ ≫ segIncl (kerElt g₁)) ≫ (φ₂ ≫ segIncl (kerElt g₂))
        = ((φ₁ ≫ φ₃) ≫ ι) ≫ segIncl (((kerElt g₃ : Set.Iic (kerElt g₂)) : N.carrier)) := by
      have h : (φ₁ ≫ segIncl (kerElt g₁)) ≫ (φ₂ ≫ segIncl (kerElt g₂))
          = (φ₁ ≫ (segIncl (kerElt g₁) ≫ φ₂)) ≫ segIncl (kerElt g₂) := rfl
      rw [h, hmid']
      have h' : (φ₁ ≫ (φ₃ ≫ segIncl (kerElt g₃))) ≫ segIncl (kerElt g₂)
          = (φ₁ ≫ φ₃) ≫ (segIncl (kerElt g₃) ≫ segIncl (kerElt g₂)) := rfl
      rw [h', hstep]
      rfl
    rw [hcomp]
    exact IsNormalMono.isEquiv1_comp ⟨_, _, isTwoKernel_upProj_segIncl _⟩ ((hφ₁.comp hφ₃).comp hι)

end SnakeLean
