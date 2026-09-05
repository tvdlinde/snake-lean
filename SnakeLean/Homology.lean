/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.Dinversion

/-!
# Normal chain complexes, homology, and self-duality of homology

This module formalises Definition 4.14 `Def:Homology` and condition (ii) of Proposition 4.18
`Criteria HSD`, completing the three-way equivalence begun in `SnakeLean.Dinversion`.

## Indexing

`NormalChainComplex` carries `obj : ℤ → B` and `d : ∀ n : ℤ, obj (n + 1) ⟶ obj n`. Indexing the
differential by its codomain rather than its domain keeps every index of the form `n`, `n + 1`,
`n + 2`, with no subtraction, so the types reduce definitionally and no `eqToHom` ever appears.
Position `n` of the complex, in the paper's numbering, is the object `obj (n + 1)`, sitting
between the incoming `d (n + 1)` and the outgoing `d n`.

Mathlib's `HomologicalComplex` is 1-categorical and cannot be reused: its differentials commute
on the nose and its homology is built from kernels and images in an abelian category.

## Two steps the paper takes in passing

First, the converse half of (ii) ⟹ (i) puts an antinormal decomposition `(m, e)` of the zero map
at position `0` of a normal chain complex with a bizero object in every other degree. A
`ℤ`-indexed complex must be padded, and the padding differentials are null, so the construction
needs **null 1-cells to be normal**: this is Proposition 4.13 `P:NullNormal`, here
`isNormal_of_isEssNull`, which factors a null 1-cell as `2-cok(1_A)` followed by a null 1-cell
followed by `2-ker(1_{A'})`, using that any 1-cell between trivial objects is an equivalence.
Remark 4.15 `Rem Padding` records that this is the only place in Section 4 where 2-z-exactness
is used for something other than writing a statement down.

Second, the dinversion attached to position `n` is that of the antinormal pair
`(2-img(d_{n+1}), 2-coim(d_n))`, whose antinormal composite the paper says is null since
`d_n ∘ d_{n+1} ≅ 0`. Getting from one to the other is two reflections:
`2-coim(d_{n+1})` coreflects `d_{n+1} ∘ d_n ≅ 0` to `2-img(d_{n+1}) ∘ d_n ≅ 0`, and then
`2-img(d_n)` reflects that to `2-img(d_{n+1}) ∘ 2-coim(d_n) ≅ 0`. This is
`isEssNull_img_comp_coim`.

## Main results

* `isNormal_of_isEssNull` — Proposition 4.13 `P:NullNormal`: in a 2-z-exact 2-category with a
  strong bizero object, every null 1-cell is normal.
* `NormalChainComplex` and `IsHomologySelfDual` — Definition 4.14 `Def:Homology` and condition (ii).
* `isHomologySelfDual_of_isHSD` and `isHSD_of_isHomologySelfDual` — Proposition 4.18 `Criteria HSD`,
  (i) ⟺ (ii).

## Not formalised

The homology objects are not given names of their own. `Hcoker` and `Hker` are `2-Coim(w_n)` and
`2-Img(w_n)` by Definition 4.14 `Def:Homology` itself, so every statement about them is a statement
about the comparison of `w_n`, which is how condition (ii) is phrased here.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

section Basic

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {A A' X Y : B}

/-- A normal 2-monomorphism is a normal 1-cell. -/
theorem IsNormalMono.isNormal {f : A ⟶ A'} (h : IsNormalMono O f) : IsNormal O f :=
  ⟨A, 𝟙 A, f, (isEquiv1_id A).isNormalEpi, h, ⟨(eqToIso (Category.id_comp f)).symm⟩⟩

/-- A normal 2-epimorphism is a normal 1-cell. -/
theorem IsNormalEpi.isNormal {f : A ⟶ A'} (h : IsNormalEpi O f) : IsNormal O f :=
  ⟨A', f, 𝟙 A', h, (isEquiv1_id A').isNormalMono, ⟨(eqToIso (Category.comp_id f)).symm⟩⟩

/-- Every 1-cell between trivial objects is an equivalence. -/
theorem isEquiv1_of_isTrivial (hX : IsTrivial O X) (hY : IsTrivial O Y) (t : X ⟶ Y) :
    IsEquiv1 t := by
  refine ⟨zero1 O Y X, ?_, ?_⟩
  · obtain ⟨θ⟩ := (isEssNull_iff _).mp (hX.isEssNull_out (t ≫ zero1 O Y X))
    obtain ⟨ζ⟩ := (isEssNull_iff _).mp hX
    exact ⟨θ ≪≫ ζ.symm⟩
  · obtain ⟨θ⟩ := (isEssNull_iff _).mp (hY.isEssNull_out (zero1 O Y X ≫ t))
    obtain ⟨ζ⟩ := (isEssNull_iff _).mp hY
    exact ⟨θ ≪≫ ζ.symm⟩

/-- **Null 1-cells are normal**, Proposition 4.13 `P:NullNormal`. The 2-coimage of a null 1-cell
is `2-cok(1_A)` and its 2-image is `2-ker(1_{A'})`; both have trivial domain, so the comparison
between them is an equivalence and the composite is null, hence isomorphic to the 1-cell one
started from.

The padded chain complex in the proof of Proposition 4.18 `Criteria HSD` needs this, since its
padding differentials are null and a normal chain complex asks all its differentials to be
normal (Remark 4.15 `Rem Padding`). -/
theorem isNormal_of_isEssNull [TwoZExact O] {f : A ⟶ A'} (hf : IsEssNull O f) : IsNormal O f := by
  have ht : IsEquiv1 (zero1 O (twoCokernelObj O (𝟙 A)) (twoKernelObj O (𝟙 A'))) :=
    isEquiv1_of_isTrivial (isTrivial_twoCokernelObj (𝟙 A)) (isTrivial_twoKernelObj (𝟙 A')) _
  refine ⟨twoKernelObj O (𝟙 A'), twoCokernel O (𝟙 A) ≫ zero1 O _ _, twoKernel O (𝟙 A'),
    ⟨_, _, (isTwoCokernel_twoCokernel O (𝟙 A)).comp_isEquiv1 ht⟩,
    ⟨_, _, isTwoKernel_twoKernel O (𝟙 A')⟩, ?_⟩
  obtain ⟨θ⟩ := (isEssNull_iff _).mp hf
  obtain ⟨ζ⟩ := (isEssNull_iff _).mp
    (((isEssNull_zero1 (O := O) _ _).comp_left (twoCokernel O (𝟙 A))).comp
      (twoKernel O (𝟙 A')))
  exact ⟨θ ≪≫ ζ.symm⟩

end Basic

/-- **Definition 4.14 `Def:Homology`.** A **normal chain complex** is a sequence of normal 1-cells
with consecutive composites null. -/
structure NormalChainComplex (O : B) [HasBizero O] where
  /-- The objects of the complex. -/
  obj : ℤ → B
  /-- The differentials; `d n` has codomain `obj n`. -/
  d : ∀ n : ℤ, obj (n + 1) ⟶ obj n
  /-- Every differential is normal. -/
  isNormal : ∀ n : ℤ, IsNormal O (d n)
  /-- Consecutive differentials compose to a null 1-cell. -/
  isEssNull_comp : ∀ n : ℤ, IsEssNull O (d (n + 1) ≫ d n)

/-- **Condition (ii) of Proposition 4.18 `Criteria HSD`:** homology is self-dual. At every position
of every normal chain complex the comparison `j_n : H^cok_n → H^ker_n` is an equivalence.

Unfolded, `H^cok_n = 2-Coim(w_n)` and `H^ker_n = 2-Img(w_n)` for the dinversion
`w_n = 2-ker(d_n) ≫ 2-cok(d_{n+1})`, and `j_n` is the comparison of `w_n`; that is what the
quantifiers below spell out, with each 2-kernel and 2-cokernel universally quantified rather
than chosen. -/
def IsHomologySelfDual (O : B) [HasBizero O] : Prop :=
  ∀ (C : NormalChainComplex O) (n : ℤ) {N Q K₀ Q₀ I J : B} {k : N ⟶ C.obj (n + 1)}
    {q : C.obj (n + 1) ⟶ Q} {kw : K₀ ⟶ N} {qw : Q ⟶ Q₀} {e : N ⟶ I} {m : J ⟶ Q} {j : I ⟶ J},
    IsTwoKernel O (C.d n) k → IsTwoCokernel O (C.d (n + 1)) q → IsTwoKernel O (k ≫ q) kw →
    IsTwoCokernel O (k ≫ q) qw → IsTwoCokernel O kw e → IsTwoKernel O qw m →
    Nonempty (e ≫ j ≫ m ≅ k ≫ q) → IsEquiv1 j

section Position

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O]
  {X₀ X₁ X₂ Iu Iv N Q : B}

/-- The antinormal composite attached to a position of a normal chain complex is null. -/
theorem isEssNull_img_comp_coim {u : X₂ ⟶ X₁} {v : X₁ ⟶ X₀} {eu : X₂ ⟶ Iu} {mu : Iu ⟶ X₁}
    (θu : u ≅ eu ≫ mu) [IsTwoEpi eu] {ev : X₁ ⟶ Iv} {mv : Iv ⟶ X₀} (θv : v ≅ ev ≫ mv)
    [IsTwoMono mv] (huv : IsEssNull O (u ≫ v)) : IsEssNull O (mu ≫ ev) := by
  have h₁ : IsEssNull O (mu ≫ v) :=
    IsEssNull.of_comp_isTwoEpi eu (huv.of_iso
      (Bicategory.whiskerRightIso θu v ≪≫ eqToIso (Category.assoc eu mu v)))
  exact IsEssNull.of_comp_isTwoMono mv (h₁.of_iso
    (Bicategory.whiskerLeftIso mu θv ≪≫ (eqToIso (Category.assoc mu ev mv)).symm))

/-- A position of a normal chain complex gives an antinormal decomposition of the zero map. -/
theorem isZeroAntinormal_img_coim {u : X₂ ⟶ X₁} {v : X₁ ⟶ X₀} {eu : X₂ ⟶ Iu} {mu : Iu ⟶ X₁}
    (θu : u ≅ eu ≫ mu) (heu : IsNormalEpi O eu) (hmu : IsNormalMono O mu) {ev : X₁ ⟶ Iv}
    {mv : Iv ⟶ X₀} (θv : v ≅ ev ≫ mv) (hev : IsNormalEpi O ev) (hmv : IsNormalMono O mv)
    (huv : IsEssNull O (u ≫ v)) : IsZeroAntinormal O mu ev := by
  obtain ⟨W, gu, hgu⟩ := heu
  obtain ⟨Z, ℓv, hℓv⟩ := hmv
  haveI := hgu.isTwoEpi
  haveI := hℓv.isTwoMono
  exact ⟨hmu, hev, isEssNull_img_comp_coim θu θv huv⟩

/-- **Proposition 4.18 `Criteria HSD`, the content of (i) ⟹ (ii).** Homological self-duality makes
the dinversion attached to a position of a normal chain complex normal. -/
theorem isNormal_dinversion_of_isHSD (hHSD : IsHSD O) {u : X₂ ⟶ X₁} {v : X₁ ⟶ X₀} {eu : X₂ ⟶ Iu}
    {mu : Iu ⟶ X₁} (θu : u ≅ eu ≫ mu) (heu : IsNormalEpi O eu) (hmu : IsNormalMono O mu)
    {ev : X₁ ⟶ Iv} {mv : Iv ⟶ X₀} (θv : v ≅ ev ≫ mv) (hev : IsNormalEpi O ev)
    (hmv : IsNormalMono O mv) (huv : IsEssNull O (u ≫ v)) {k : N ⟶ X₁} (hk : IsTwoKernel O v k)
    {q : X₁ ⟶ Q} (hq : IsTwoCokernel O u q) : IsNormal O (k ≫ q) := by
  obtain ⟨W, gu, hgu⟩ := heu
  obtain ⟨Z, ℓv, hℓv⟩ := hmv
  haveI := hgu.isTwoEpi
  haveI := hℓv.isTwoMono
  have hkv : IsTwoKernel O ev k := (isTwoKernel_comp_isTwoMono_iff mv).mp (hk.of_iso θv)
  have hqu : IsTwoCokernel O mu q := (isTwoCokernel_isTwoEpi_comp_iff eu).mp (hq.of_iso θu)
  exact hHSD (isZeroAntinormal_img_coim θu ⟨W, gu, hgu⟩ hmu θv hev ⟨Z, ℓv, hℓv⟩ huv) hkv hqu

end Position

section Criteria

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O]

/-- **Proposition 4.18 `Criteria HSD`, (i) ⟹ (ii).** -/
theorem isHomologySelfDual_of_isHSD (hHSD : IsHSD O) : IsHomologySelfDual O := by
  intro C n N Q K₀ Q₀ I J k q kw qw e m j hk hq hkw hqw he hm ⟨θ⟩
  obtain ⟨Iu, eu, mu, heu, hmu, ⟨θu⟩⟩ := C.isNormal (n + 1)
  obtain ⟨Iv, ev, mv, hev, hmv, ⟨θv⟩⟩ := C.isNormal n
  exact (isNormal_iff_isEquiv1_comparison hkw he hqw hm θ).mp
    (isNormal_dinversion_of_isHSD hHSD θu heu hmu θv hev hmv (C.isEssNull_comp n) hk hq)

/-- The objects of the two-term normal chain complex on an antinormal decomposition of the zero
map: `K` in degree `2`, `X` in degree `1`, `R` in degree `0`, and the bizero object elsewhere. -/
def twoTermObj (O K X R : B) : ℤ → B
  | 0 => R
  | 1 => X
  | 2 => K
  | _ => O

/-- The differentials of the two-term normal chain complex. -/
def twoTermD (O : B) [HasBizero O] {K X R : B} (m : K ⟶ X) (e : X ⟶ R) :
    ∀ n : ℤ, twoTermObj O K X R (n + 1) ⟶ twoTermObj O K X R n
  | 0 => e
  | 1 => m
  | _ => zero1 O _ _

/-- **The two-term normal chain complex** in the proof of Proposition 4.18 `Criteria HSD`: an
antinormal decomposition `(m, e)` of the zero map, padded with null 1-cells, which are normal by
`isNormal_of_isEssNull`. -/
noncomputable def twoTermComplex [TwoZExact O] {K X R : B} {m : K ⟶ X} {e : X ⟶ R}
    (hme : IsZeroAntinormal O m e) : NormalChainComplex O where
  obj := twoTermObj O K X R
  d := twoTermD O m e
  isNormal n := by
    match n with
    | 0 => exact hme.isNormalEpi.isNormal
    | 1 => exact hme.isNormalMono.isNormal
    | Int.ofNat (k + 2) => exact isNormal_of_isEssNull (isEssNull_zero1 _ _)
    | Int.negSucc k => exact isNormal_of_isEssNull (isEssNull_zero1 _ _)
  isEssNull_comp n := by
    match n with
    | 0 => exact hme.isEssNull_comp
    | 1 => exact (isEssNull_zero1 _ _).comp m
    | Int.ofNat (k + 2) => exact (isEssNull_zero1 _ _).comp_left _
    | Int.negSucc k => exact (isEssNull_zero1 _ _).comp_left _

/-- **Proposition 4.18 `Criteria HSD`, (ii) ⟹ (i).** Every antinormal decomposition of the zero map
is position `0` of its two-term normal chain complex. Like (iii) ⟹ (i), this direction needs
2-z-exactness, both to pad the complex and to form the comparison that (ii) speaks about. -/
theorem isHSD_of_isHomologySelfDual [TwoZExact O] (H : IsHomologySelfDual O) : IsHSD O := by
  intro K X R N C m e hme k q hk hq
  obtain ⟨j, ⟨θ⟩⟩ := exists_comparison (isTwoKernel_twoKernel O (k ≫ q))
    (isTwoCokernel_twoCokernel O (twoKernel O (k ≫ q))) (isTwoCokernel_twoCokernel O (k ≫ q))
    (isTwoKernel_twoKernel O (twoCokernel O (k ≫ q)))
  have hj : IsEquiv1 j :=
    H (twoTermComplex hme) 0 hk hq (isTwoKernel_twoKernel O (k ≫ q))
      (isTwoCokernel_twoCokernel O (k ≫ q))
      (isTwoCokernel_twoCokernel O (twoKernel O (k ≫ q)))
      (isTwoKernel_twoKernel O (twoCokernel O (k ≫ q))) ⟨θ⟩
  exact (isNormal_iff_isEquiv1_comparison (isTwoKernel_twoKernel O (k ≫ q))
    (isTwoCokernel_twoCokernel O (twoKernel O (k ≫ q))) (isTwoCokernel_twoCokernel O (k ≫ q))
    (isTwoKernel_twoKernel O (twoCokernel O (k ≫ q))) θ).mpr hj

end Criteria

section ExactnessViaHomology

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O]
  {A H If Ig N Q Y Z : B}

omit [IsStrong O] in
/-- Two 2-monomorphisms over the same object that factor through each other differ by an
equivalence. -/
theorem isEquiv1_of_factor {U V : B} {u : U ⟶ Y} {v : V ⟶ Y} [IsTwoMono u] [IsTwoMono v]
    {t : V ⟶ U} {t' : U ⟶ V} (γ : t ≫ u ≅ v) (γ' : t' ≫ v ≅ u) : IsEquiv1 t := by
  refine ⟨t', ⟨IsTwoMono.preimageIso v ?_⟩, ⟨IsTwoMono.preimageIso u ?_⟩⟩
  · exact eqToIso (Category.assoc t t' v) ≪≫ Bicategory.whiskerLeftIso t γ' ≪≫ γ ≪≫
      (eqToIso (Category.id_comp v)).symm
  · exact eqToIso (Category.assoc t' t u) ≪≫ Bicategory.whiskerLeftIso t' γ ≪≫ γ' ≪≫
      (eqToIso (Category.id_comp u)).symm

/-- **Proposition 4.24 `Exactness via Homology`.** For a composable pair of normal 1-cells with null
composite, the induced 1-cell `e : A ⟶ 2-Ker(g)` is a 2-epimorphism exactly when the induced
`m : 2-Cok(f) ⟶ Z` is a 2-monomorphism, exactly when the pair is exact, and exactly when the
object `H` carrying the normal image factorisation of `2-ker(g) ≫ 2-cok(f)` is trivial.

Homological self-duality does not appear: it is needed only to know that `2-ker(g) ≫ 2-cok(f)` is
normal, so that `H` exists at all. Once the factorisation `θp` is given, the four conditions are
equivalent in any 2-category with a strong bizero object. -/
theorem exactness_via_homology_tfae {f : A ⟶ Y} {g : Y ⟶ Z} {ef : A ⟶ If} {mf : If ⟶ Y}
    (θf : f ≅ ef ≫ mf) (hef : IsNormalEpi O ef) (hmf : IsNormalMono O mf) {eg : Y ⟶ Ig}
    {mg : Ig ⟶ Z} (θg : g ≅ eg ≫ mg) (heg : IsNormalEpi O eg) (hmg : IsNormalMono O mg)
    {kg : N ⟶ Y} (hkg : IsTwoKernel O g kg) {qf : Y ⟶ Q} (hqf : IsTwoCokernel O f qf)
    {e : A ⟶ N} (θe : e ≫ kg ≅ f) {m : Q ⟶ Z} (θm : qf ≫ m ≅ g) {r : N ⟶ H} {s : H ⟶ Q}
    (θp : kg ≫ qf ≅ r ≫ s) (hr : IsNormalEpi O r) (hs : IsNormalMono O s) :
    List.TFAE [IsTwoEpi e, IsTwoMono m, IsExactAt O f g, IsTrivial O H] := by
  obtain ⟨W₁, g₁, hg₁⟩ := hef
  obtain ⟨W₂, ℓ₂, hℓ₂⟩ := hmf
  obtain ⟨W₃, g₃, hg₃⟩ := hr
  obtain ⟨W₄, ℓ₄, hℓ₄⟩ := hs
  haveI := hg₁.isTwoEpi
  haveI := hℓ₂.isTwoMono
  haveI := hg₃.isTwoEpi
  haveI := hℓ₄.isTwoMono
  haveI := hkg.isTwoMono
  haveI := hqf.isTwoEpi
  -- `H` is trivial exactly when the dinversion `2-ker(g) ≫ 2-cok(f)` is null.
  have hEq : IsTrivial O H ↔ IsEssNull O (kg ≫ qf) := by
    constructor
    · intro hH
      exact ((hH.isEssNull_in r).comp s).of_iso θp.symm
    · intro hp
      have h₁ : IsEssNull O r := IsEssNull.of_comp_isTwoMono s (hp.of_iso θp)
      exact IsEssNull.of_comp_isTwoEpi r (h₁.of_iso (eqToIso (Category.comp_id r)).symm)
  -- the composite `f ≫ g` is null.
  have hfg : IsEssNull O (f ≫ g) :=
    (hkg.isEssNull_comp.comp_left e).of_iso
      ((eqToIso (Category.assoc e kg g)).symm ≪≫ Bicategory.whiskerRightIso θe g)
  -- `2-img(f)` is a 2-kernel of `2-cok(f)`.
  have hmfq : IsTwoKernel O qf mf :=
    hℓ₂.of_isTwoCokernel ((isTwoCokernel_isTwoEpi_comp_iff ef).mp (hqf.of_iso θf))
  -- if the dinversion is null then `2-img(f)` is a 2-kernel of `g`.
  have key : IsEssNull O (kg ≫ qf) → IsTwoKernel O g mf := by
    intro hp
    obtain ⟨t, ⟨γ⟩⟩ := hmfq.fac kg hp
    have hmfg : IsEssNull O (mf ≫ g) := IsEssNull.of_comp_isTwoEpi ef
      (hfg.of_iso (Bicategory.whiskerRightIso θf g ≪≫ eqToIso (Category.assoc ef mf g)))
    obtain ⟨t', ⟨γ'⟩⟩ := hkg.fac mf hmfg
    exact IsTwoKernel.of_isEquiv1_comp (isEquiv1_of_factor γ γ') (hkg.of_iso_right γ.symm)
  tfae_have 1 → 4 := by
    intro he
    haveI := he
    refine hEq.mpr (IsEssNull.of_comp_isTwoEpi e (hqf.isEssNull_comp.of_iso ?_))
    exact (Bicategory.whiskerRightIso θe qf).symm ≪≫ eqToIso (Category.assoc e kg qf)
  tfae_have 2 → 4 := by
    intro hm
    haveI := hm
    refine hEq.mpr (IsEssNull.of_comp_isTwoMono m (hkg.isEssNull_comp.of_iso ?_))
    exact (Bicategory.whiskerLeftIso kg θm).symm ≪≫ (eqToIso (Category.assoc kg qf m)).symm
  tfae_have 4 → 3 := fun hH => ⟨If, ef, mf, ⟨W₁, g₁, hg₁⟩, ⟨θf⟩, key (hEq.mp hH)⟩
  tfae_have 4 → 2 := by
    intro hH
    have hcf : IsTwoCokernel O f eg :=
      ((exactness_tfae θf ⟨W₁, g₁, hg₁⟩ ⟨W₂, ℓ₂, hℓ₂⟩ θg heg hmg).out 0 1).mp (key (hEq.mp hH))
    obtain ⟨v, hv, ⟨δ⟩⟩ := hqf.exists_isEquiv1 hcf
    obtain ⟨W₅, ℓ₅, hℓ₅⟩ := hmg
    haveI := hℓ₅.isTwoMono
    haveI := hv.isTwoMono
    refine IsTwoMono.of_iso (f := v ≫ mg) ?_
    refine IsTwoEpi.preimageIso qf ?_
    exact (eqToIso (Category.assoc qf v mg)).symm ≪≫ Bicategory.whiskerRightIso δ mg ≪≫
      θg.symm ≪≫ θm.symm
  tfae_have 3 → 1 := by
    rintro ⟨I₀, e₀, m₀, ⟨W₆, g₆, hg₆⟩, ⟨θ₀⟩, hm₀⟩
    haveI := hg₆.isTwoEpi
    obtain ⟨u, hu, ⟨δ⟩⟩ := hkg.exists_isEquiv1 hm₀
    haveI := hu.isTwoEpi
    refine IsTwoEpi.of_iso (f := e₀ ≫ u) ?_
    refine IsTwoMono.preimageIso kg ?_
    exact eqToIso (Category.assoc e₀ u kg) ≪≫ Bicategory.whiskerLeftIso e₀ δ ≪≫ θ₀.symm ≪≫
      θe.symm
  tfae_finish

end ExactnessViaHomology

end SnakeLean
