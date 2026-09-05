/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import SnakeLean.SerreJoin

/-!
# An asymmetric pair of Serre classes

This module is about abelian categories, not about the 2-categorical development. It is the
module-theoretic content of Section 9.21 `SS:NSDAbCat`: whether the 2-category `AbCat` of abelian
categories, exact functors and natural transformations satisfies **(DPN)**, dinversion preserves
normality. It does not — Proposition 9.25 `P:AbCatNotDPN`, and with it Corollary 9.26
`C:HSDstrict`.

By the reduction of Proposition 8.11 `P:DIabcat`, an antinormal 1-cell of `AbCat` is
`K ↣ A ↠ A/S` for Serre classes `K` and `S`, and it is normal exactly when the `S`-saturation of
`K` is a Serre class; its dinversion is `S ↣ A ↠ A/K`, normal exactly when the `K`-saturation of
`S` is one. So (DPN) asks the two saturations to be Serre together, and `asymmetry` below exhibits
an abelian category where one is and the other is not.

The example is the category of modules over the five-dimensional algebra `Λ = kQ/(αβ)`, where `Q`
is the cyclic quiver `1 → 2 → 1` and `αβ` is the path of length two from `2` to `2`. It is a
quotient of the six-dimensional Nakayama algebra with which Proposition 8.12 `P:AbCatFails`
refutes 2-di-exactness; the extra relation destroys the rotation symmetry of that example, which
is what made it useless here — Remark 9.24 `Rem NSD Symmetric`. We present `Λ` as the algebra of
matrices `!![a, 0, 0; e, a, d; c, 0, b]`, the image of its action on the indecomposable projective
at vertex `1`, and take `K` and `S` to be the modules annihilated by the two idempotents.

## Main results

* `isSerreClass_annBy` — the modules annihilated by an idempotent form a Serre class.
* `serreSaturation_KK_SS` — **every** `Λ`-module carries a filtration with successive
  subquotients in `K`, `S`, `K`, so the `K`-saturation of `S` is everything, hence Serre.
* `not_serreSaturation_SS_KK` — the free module of rank one carries no filtration with
  subquotients in `S`, `K`, `S`, so the `S`-saturation of `K` is not Serre.
* `asymmetry` — the two together: (DPN) fails in `AbCat`.

The first of the two is one line of ring theory: the relation makes `α · r` a scalar multiple of
`α` for every `r`, so the elements killed by `α` form a submodule, and modulo it `β` acts as zero.
The second uses no computation in the quotient category, unlike the counterexample it modifies:
the element `p = βα` acts as zero on every module in `K`, and being fixed by `e₁` on both sides it
is transported unchanged along morphisms that are isomorphisms modulo `S`.
-/

universe u

namespace CategoryTheory

open Limits ZeroObject ObjectProperty

namespace ObjectProperty

section Annihilator

variable {R : Type u} [Ring R] (e : R)

/-- The class of modules **annihilated by** a fixed ring element. -/
def annBy : ObjectProperty (ModuleCat.{u} R) := fun M => ∀ m : M, e • m = 0

lemma annBy_iff (M : ModuleCat.{u} R) : annBy e M ↔ ∀ m : M, e • m = 0 := Iff.rfl

instance : (annBy e).ContainsZero where
  exists_zero :=
    ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _, fun _ => Subsingleton.elim _ _⟩

instance : (annBy e).IsClosedUnderSubobjects where
  prop_of_mono := by
    intro X Y f hf hY m
    haveI := hf
    have hinj : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).1 hf
    apply hinj
    rw [map_smul, hY (f.hom m), map_zero]

instance : (annBy e).IsClosedUnderQuotients where
  prop_of_epi := by
    intro X Y f hf hX m
    haveI := hf
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective f).1 hf m
    rw [← map_smul, hX x, map_zero]

variable {e}

/-- **Closure under extensions**, and the only place idempotence is used: if `e · m` lies in the
subobject, then `e · (e · m) = e · m` vanishes there. -/
theorem isClosedUnderExtensions_annBy (he : IsIdempotentElem e) :
    (annBy e).IsClosedUnderExtensions where
  prop_X₂_of_shortExact := by
    intro S hS h₁ h₃ m
    haveI := hS.mono_f
    haveI := hS.epi_g
    have hex : Function.Exact S.f.hom S.g.hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
    have hg : S.g.hom (e • m) = 0 := by rw [map_smul, h₃ (S.g.hom m)]
    obtain ⟨x, hx⟩ := (hex (e • m)).1 hg
    calc e • m = e • e • m := by rw [smul_smul, he]
      _ = e • S.f.hom x := by rw [hx]
      _ = S.f.hom (e • x) := (map_smul _ _ _).symm
      _ = 0 := by rw [h₁ x, map_zero]

/-- **The modules annihilated by an idempotent form a Serre class.** -/
theorem isSerreClass_annBy (he : IsIdempotentElem e) : (annBy e).IsSerreClass :=
  haveI := isClosedUnderExtensions_annBy he
  { }

end Annihilator



end ObjectProperty

end CategoryTheory

namespace TwoVertex

variable (k : Type u) [CommRing k]

/-- The algebra `Λ = kQ/(αβ)` of the introduction, presented by its action on the indecomposable
projective at vertex `1`: the matrices
`!![a, 0, 0; e, a, d; c, 0, b]`, in the basis `x`, `z`, `y` of that projective, where `x` spans
the top, `z` the socle and `y` the middle layer. It is five-dimensional over `k`, with basis the
two idempotents `e₁`, `e₂`, the two arrows `α`, `β` and the length-two path `p = βα`. -/
def lam : Subalgebra k (Matrix (Fin 3) (Fin 3) k) where
  carrier := {M | M 0 1 = 0 ∧ M 0 2 = 0 ∧ M 2 1 = 0 ∧ M 1 1 = M 0 0}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3, ha4⟩ ⟨hb1, hb2, hb3, hb4⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, ha1, ha2, ha3, ha4, hb1, hb2, hb3, hb4]
  one_mem' := by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3, ha4⟩ ⟨hb1, hb2, hb3, hb4⟩
    exact ⟨by simp [ha1, hb1], by simp [ha2, hb2], by simp [ha3, hb3], by simp [ha4, hb4]⟩
  zero_mem' := by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  algebraMap_mem' := by
    intro r
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Algebra.algebraMap_eq_smul_one]

variable {k}

/-- Every element of `Λ` has the displayed shape; this is what makes the multiplication table
below a finite computation. -/
lemma lam_eq (r : lam k) :
    (r : Matrix (Fin 3) (Fin 3) k) =
      !![(r : Matrix (Fin 3) (Fin 3) k) 0 0, 0, 0;
         (r : Matrix (Fin 3) (Fin 3) k) 1 0, (r : Matrix (Fin 3) (Fin 3) k) 0 0,
           (r : Matrix (Fin 3) (Fin 3) k) 1 2;
         (r : Matrix (Fin 3) (Fin 3) k) 2 0, 0, (r : Matrix (Fin 3) (Fin 3) k) 2 2] := by
  obtain ⟨h1, h2, h3, h4⟩ := r.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

variable (k)

/-- The idempotent at vertex `1`. -/
def e₁ : lam k := ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 0], by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp⟩

/-- The idempotent at vertex `2`. -/
def e₂ : lam k := ⟨!![0, 0, 0; 0, 0, 0; 0, 0, 1], by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp⟩

/-- The arrow `α : 1 → 2`. -/
def al : lam k := ⟨!![0, 0, 0; 0, 0, 0; 1, 0, 0], by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp⟩

/-- The arrow `β : 2 → 1`. -/
def be : lam k := ⟨!![0, 0, 0; 0, 0, 1; 0, 0, 0], by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp⟩

/-- The length-two path `p = βα : 1 → 1`, the one the relation does *not* kill. -/
def pa : lam k := ⟨!![0, 0, 0; 1, 0, 0; 0, 0, 0], by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp⟩

variable {k}

/-- The scalar matrices, which lie in `Λ`; they serve as the coefficients in the multiplication
table below. -/
def sc (c : k) : lam k := ⟨!![c, 0, 0; 0, c, 0; 0, 0, c], by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp⟩

lemma coe_mul (x y : lam k) :
    ((x * y : lam k) : Matrix (Fin 3) (Fin 3) k) = (x : Matrix (Fin 3) (Fin 3) k) * y := rfl

lemma coe_add (x y : lam k) :
    ((x + y : lam k) : Matrix (Fin 3) (Fin 3) k) = (x : Matrix (Fin 3) (Fin 3) k) + y := rfl

/-- `e₁` is idempotent. -/
lemma isIdempotentElem_e₁ : IsIdempotentElem (e₁ k) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e₁, coe_mul, Matrix.mul_apply, Fin.sum_univ_three]

/-- `e₂` is idempotent. -/
lemma isIdempotentElem_e₂ : IsIdempotentElem (e₂ k) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e₂, coe_mul, Matrix.mul_apply, Fin.sum_univ_three]

lemma e₁_add_e₂ : e₁ k + e₂ k = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₁, e₂]

lemma e₂_mul_e₁ : e₂ k * e₁ k = 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e₁, e₂, coe_mul, Matrix.mul_apply, Fin.sum_univ_three]

lemma al_mul_e₁ : al k * e₁ k = al k := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [al, e₁, coe_mul, Matrix.mul_apply, Fin.sum_univ_three]

lemma al_mul_e₂ : al k * e₂ k = 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [al, e₂, coe_mul, Matrix.mul_apply, Fin.sum_univ_three]

lemma e₂_mul_al : e₂ k * al k = al k := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [al, e₂, coe_mul, Matrix.mul_apply, Fin.sum_univ_three]

/-- The path `p` is `β` after `α`. -/
lemma pa_eq : pa k = be k * al k := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pa, al, be, coe_mul, Matrix.mul_apply, Fin.sum_univ_three]

lemma e₁_mul_pa : e₁ k * pa k = pa k := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pa, e₁, coe_mul, Matrix.mul_apply, Fin.sum_univ_three]

lemma pa_mul_e₁ : pa k * e₁ k = pa k := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pa, e₁, coe_mul, Matrix.mul_apply, Fin.sum_univ_three]

/-- **The relation.** The other length-two path vanishes; this is the whole of the asymmetry. -/
lemma al_mul_be : al k * be k = 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [al, be, coe_mul, Matrix.mul_apply, Fin.sum_univ_three]

/-- **`α · Λ ⊆ k · α`**, the consequence of the relation that makes the elements killed by `α`
into a submodule. -/
lemma exists_al_mul (r : lam k) : ∃ c : lam k, al k * r = c * al k := by
  refine ⟨sc ((r : Matrix (Fin 3) (Fin 3) k) 0 0), ?_⟩
  apply Subtype.ext
  rw [coe_mul, coe_mul, lam_eq r]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [al, sc, Matrix.mul_apply, Fin.sum_univ_three]

/-- **`e₂ · Λ ⊆ k · α + k · e₂`.** -/
lemma exists_e₂_mul (r : lam k) : ∃ c d : lam k, e₂ k * r = c * al k + d * e₂ k := by
  refine ⟨sc ((r : Matrix (Fin 3) (Fin 3) k) 2 0), sc ((r : Matrix (Fin 3) (Fin 3) k) 2 2), ?_⟩
  apply Subtype.ext
  rw [coe_add, coe_mul, coe_mul, coe_mul, lam_eq r]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [al, e₂, sc, Matrix.mul_apply, Fin.sum_univ_three]

/-- `p` is nonzero, the one arithmetical fact the counterexample needs. -/
lemma pa_ne_zero [Nontrivial k] : pa k ≠ 0 := by
  intro h
  have : ((pa k : Matrix (Fin 3) (Fin 3) k)) 1 0 = 0 := by rw [h]; simp
  simp [pa] at this

end TwoVertex

namespace TwoVertex

open CategoryTheory ObjectProperty Limits

universe w

variable {k : Type u} [CommRing k]

/-- The Serre class `K`: the modules annihilated by the idempotent at vertex `1`, that is, the
modules all of whose composition factors are the simple `S₁`. -/
abbrev KK (k : Type u) [CommRing k] : ObjectProperty (ModuleCat.{u} (lam k)) := annBy (e₂ k)

/-- The Serre class `S`: the modules annihilated by the idempotent at vertex `2`. -/
abbrev SS (k : Type u) [CommRing k] : ObjectProperty (ModuleCat.{u} (lam k)) := annBy (e₁ k)

instance : (KK k).IsSerreClass := isSerreClass_annBy isIdempotentElem_e₂

instance : (SS k).IsSerreClass := isSerreClass_annBy isIdempotentElem_e₁

variable (M : ModuleCat.{u} (lam k))

/-- The middle step of the filtration: the elements annihilated by `α`. That this is a submodule
is exactly the relation `αβ = 0`, through `exists_al_mul`. -/
def nTwo : Submodule (lam k) M where
  carrier := {m | al k • m = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [smul_add, ha, hb, add_zero]
  smul_mem' := by
    intro c x hx
    obtain ⟨d, hd⟩ := exists_al_mul c
    have : al k • c • x = (al k * c) • x := (mul_smul _ _ _).symm
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [this, hd, mul_smul, hx, smul_zero]

/-- The first step: the elements annihilated by `α` and by `e₂`. -/
def nOne : Submodule (lam k) M where
  carrier := {m | al k • m = 0 ∧ e₂ k • m = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    exact ⟨by rw [smul_add, ha.1, hb.1, add_zero], by rw [smul_add, ha.2, hb.2, add_zero]⟩
  smul_mem' := by
    intro c x hx
    obtain ⟨d, hd⟩ := exists_al_mul c
    obtain ⟨d₁, d₂, hd'⟩ := exists_e₂_mul c
    refine ⟨?_, ?_⟩
    · rw [← mul_smul, hd, mul_smul, hx.1, smul_zero]
    · rw [← mul_smul, hd', add_smul, mul_smul, mul_smul, hx.1, hx.2, smul_zero, smul_zero,
        add_zero]

variable {M}

lemma nOne_le_nTwo : nOne M ≤ nTwo M := fun _ hm => hm.1

/-- The first layer lies in `K`. -/
lemma nOne_mem_KK {m : M} (hm : m ∈ nOne M) : e₂ k • m = 0 := hm.2

/-- The second layer lies in `S`: modulo `N₁`, the module `N₂` is annihilated by `e₁`. -/
lemma e₁_smul_mem_nOne {m : M} (hm : m ∈ nTwo M) : e₁ k • m ∈ nOne M := by
  refine ⟨?_, ?_⟩
  · rw [← mul_smul, al_mul_e₁]; exact hm
  · rw [← mul_smul, e₂_mul_e₁, zero_smul]

/-- The third layer lies in `K`: `e₂ · M` is contained in `N₂`, since `αe₂ = 0`. -/
lemma e₂_smul_mem_nTwo (m : M) : e₂ k • m ∈ nTwo M := by
  change al k • e₂ k • m = 0
  rw [← mul_smul, al_mul_e₂, zero_smul]

variable (M)

/-- The apex of the span witnessing the saturation: the submodule `N₂`. -/
def spanD : ModuleCat.{u} (lam k) := ModuleCat.of _ (nTwo M)

/-- Its middle layer `N₂/N₁`, which lies in `S`. -/
def spanA : ModuleCat.{u} (lam k) :=
  ModuleCat.of _ ((nTwo M) ⧸ ((nOne M).comap (nTwo M).subtype))

/-- The projection `N₂ ↠ N₂/N₁`, whose kernel `N₁` lies in `K`. -/
def spanF : spanD M ⟶ spanA M := ModuleCat.ofHom (Submodule.mkQ _)

/-- The inclusion `N₂ ↣ M`, whose cokernel `M/N₂` lies in `K`. -/
def spanG : spanD M ⟶ M := ModuleCat.ofHom (nTwo M).subtype

lemma SS_spanA : SS k (spanA M) := by
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact e₁_smul_mem_nOne x.2

lemma KK_isoModSerre_spanF : (KK k).isoModSerre (spanF M) := by
  haveI : Epi (spanF M) := by
    rw [ModuleCat.epi_iff_surjective]
    simp only [spanF, ModuleCat.hom_ofHom]
    exact Submodule.mkQ_surjective _
  refine (KK k).isoModSerre_of_epi (spanF M) ?_
  rw [monoModSerre_iff]
  refine ((KK k).prop_iff_of_iso (ModuleCat.kernelIsoKer (spanF M))).2 ?_
  rintro ⟨x, hx⟩
  have hx' : x ∈ (nOne M).comap (nTwo M).subtype := by
    have h : x ∈ LinearMap.ker ((nOne M).comap (nTwo M).subtype).mkQ := hx
    rwa [Submodule.ker_mkQ] at h
  apply Subtype.ext
  apply Subtype.ext
  exact (Submodule.mem_comap.mp hx').2
lemma KK_isoModSerre_spanG : (KK k).isoModSerre (spanG M) := by
  haveI : Mono (spanG M) := by
    rw [ModuleCat.mono_iff_injective]
    simp only [spanG, ModuleCat.hom_ofHom]
    exact Submodule.injective_subtype _
  refine (KK k).isoModSerre_of_mono (spanG M) ?_
  rw [epiModSerre_iff]
  refine ((KK k).prop_iff_of_iso (ModuleCat.cokernelIsoRangeQuotient (spanG M))).2 ?_
  intro q
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  simp only [spanG, ModuleCat.hom_ofHom]
  exact ⟨⟨e₂ k • m, e₂_smul_mem_nTwo m⟩, rfl⟩

/-- **Every `Λ`-module carries a filtration with subquotients in `K`, `S`, `K`**, so the
`K`-saturation of `S` is the whole category. No finiteness is used. -/
theorem serreSaturation_KK_SS : serreSaturation (KK k) (SS k) M :=
  ⟨spanA M, spanD M, spanF M, spanG M, SS_spanA M, KK_isoModSerre_spanF M,
    KK_isoModSerre_spanG M⟩

variable (k)

/-- The witness: the free module of rank one. Any module on which `p` acts nontrivially would
do. -/
abbrev reg : ModuleCat.{u} (lam k) := ModuleCat.of (lam k) (lam k)

variable {k}

/-- **`p` annihilates every module in `K`.** Indeed `α = e₂α`, so `α · a` lies in `e₂ · A`. -/
lemma pa_smul_eq_zero {A : ModuleCat.{u} (lam k)} (hA : KK k A) (a : A) : pa k • a = 0 := by
  have h : al k • a = 0 := by
    conv_lhs => rw [← e₂_mul_al]
    rw [mul_smul]
    exact hA _
  rw [pa_eq, mul_smul, h, smul_zero]

/-- **The `S`-saturation of `K` is not everything**: the free module of rank one carries no
filtration with successive subquotients in `S`, `K`, `S`.

The invariant is the action of `p = βα`. It vanishes on every module of `K`, and since `p` is
fixed by `e₁` on both sides it is carried along both legs of any span of morphisms that are
isomorphisms modulo `S`. On the free module it acts as multiplication by `p`, which is not
zero. -/
theorem not_serreSaturation_SS_KK [Nontrivial k] :
    ¬ serreSaturation (SS k) (KK k) (reg k) := by
  rintro ⟨A, D, f, g, hA, hf, hg⟩
  have hcoker : ∀ m : reg k, e₁ k • m ∈ LinearMap.range g.hom := by
    intro m
    have h := ((SS k).prop_iff_of_iso (ModuleCat.cokernelIsoRangeQuotient g)).1 hg.2
    have h' := h (Submodule.Quotient.mk m)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h'
    exact h'
  have hker : ∀ d : D, f.hom d = 0 → e₁ k • d = 0 := by
    intro d hd
    have h := ((SS k).prop_iff_of_iso (ModuleCat.kernelIsoKer f)).1 hf.1
    exact congrArg Subtype.val (h ⟨d, hd⟩)
  have key : ∀ m : reg k, pa k • m = 0 := by
    intro m
    obtain ⟨d, hd⟩ := hcoker m
    have h1 : f.hom (pa k • d) = 0 := by rw [map_smul, pa_smul_eq_zero hA]
    have h2 : pa k • d = 0 := by
      have h3 := hker _ h1
      rwa [← mul_smul, e₁_mul_pa] at h3
    calc pa k • m = (pa k * e₁ k) • m := by rw [pa_mul_e₁]
      _ = pa k • (e₁ k • m) := mul_smul _ _ _
      _ = pa k • g.hom d := by rw [hd]
      _ = g.hom (pa k • d) := (map_smul _ _ _).symm
      _ = 0 := by rw [h2, map_zero]
  have h1 := key (1 : lam k)
  rw [smul_eq_mul, mul_one] at h1
  exact pa_ne_zero h1

/-- **The asymmetry, and with it the failure of (DPN) in `AbCat`.** For the two Serre classes `K`
and `S` of `Λ`-modules, the `K`-saturation of `S` is a Serre class and the `S`-saturation of `K`
is not. Under the reduction of Proposition 8.11 `P:DIabcat` the first says that the
dinversion of the antinormal pair `(K ↣ A, A ↠ A/S)` is normal, and the second that the pair
itself is not: dinversion does not preserve normality. -/
theorem asymmetry [Nontrivial k] :
    (serreSaturation (KK k) (SS k)).IsSerreClass ∧
      ¬ (serreSaturation (SS k) (KK k)).IsSerreClass := by
  constructor
  · rw [isSerreClass_serreSaturation_iff]
    exact le_antisymm (serreSaturation_le_serreJoin (KK k) (SS k))
      (fun X _ => serreSaturation_KK_SS X)
  · intro h
    rw [isSerreClass_serreSaturation_iff] at h
    refine not_serreSaturation_SS_KK (k := k) ?_
    rw [h]
    intro R hR hKK hSS
    haveI := hR
    exact serreSaturation_le (KK k) (SS k) hSS hKK _ (serreSaturation_KK_SS (reg k))

end TwoVertex
