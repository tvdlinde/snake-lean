/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Support
import SnakeLean.CondAS

/-!
# A witness for condition (AS): finitely generated modules

`SnakeLean.CondAS` proves that condition (AS) makes a noetherian abelian category saturated,
Proposition 8.21 `P:ASimplies`; this module is **Proposition 8.24 `P:ModAS`**, the first of the
paper's two witnesses that (AS) holds somewhere: **the finitely generated modules over a
commutative noetherian ring satisfy (AS)**, and the category is noetherian.

The proof does not classify the Serre classes of the category, and in particular uses neither
Gabriel's theorem nor Kanda's — which is what the paragraph after the proposition points out.
It runs, as the paper's does, through associated primes:

* for `p` associated to `M` there is a monomorphism `R ⧸ p ⟶ M`, so the hypothesis produces a
  nonzero submodule `J` of `R ⧸ p` lying in `T`; and `R ⧸ p` is a *domain*, so multiplication by
  a nonzero element of `J` embeds `R ⧸ p` into `J`, whence `R ⧸ p` lies in `T`;
* every prime in the support of `M` contains an associated prime `q`, and `R ⧸ p` is a *quotient*
  of `R ⧸ q`, so `R ⧸ p` lies in `T` for every `p` in the support;
* a maximal submodule of `M` lying in `T` must be everything, since otherwise an associated prime
  of the quotient produces a strictly larger one.

The first two steps are the paper's. The third replaces the paper's filtration of `M` by
primes (Matsumura, Theorem 6.4), which Mathlib does not have, with a maximality argument that
uses only the ascending chain condition.

## Main results

* `ObjectProperty.prop_of_subEssential` — (AS) for noetherian objects of `ModuleCat R`.
* `condAS_fgModuleCat` — **`CondAS (FGModuleCat R)`**, condition (AS) for the finitely generated
  modules over a commutative noetherian ring: the (AS) half of Proposition 8.24 `P:ModAS`.
* `isNoetherianObject_fgModuleCat` — the noetherian half, through
  `isNoetherianObject_of_fullyFaithful`, which is general: a fully faithful functor preserving
  monomorphisms reflects noetherian objects. Mathlib had no `IsNoetherianObject` instance for a
  module category before.
* `isSerreClass_serreSaturation_fgModuleCat` — the two combined with Proposition 8.21: the
  category is saturated, with no hypothesis left. That is the module half of Corollary 8.27
  `C:Populated`; the coherent-sheaf half, Lemma 8.25 `L:OneAss` and Proposition 8.26 `P:CohAS`,
  is not formalised.
-/

universe u

open CategoryTheory Limits ObjectProperty Module ZeroObject

section CommutativeAlgebra

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- An associated prime lies in the support. -/
lemma PrimeSpectrum.mem_support_of_mem_associatedPrimes {p : Ideal R} (hp : p.IsPrime)
    (hmem : p ∈ associatedPrimes R M) :
    (⟨p, hp⟩ : PrimeSpectrum R) ∈ Module.support R M := by
  obtain ⟨-, x, hx⟩ := hmem
  rw [Module.mem_support_iff']
  refine ⟨x, fun r hr h => hr ?_⟩
  change r ∈ p
  rw [hx, Submodule.mem_colon_singleton]
  simpa using h

open Module.associatedPrimes in
/-- **Every prime in the support contains an associated prime.** The proof localises at `p` and
transports an associated prime of the localisation back, as in `Mathlib`'s
`minimalPrimes_annihilator_subset_associatedPrimes`. -/
lemma exists_associatedPrimes_le_of_mem_support [IsNoetherianRing R] {p : Ideal R}
    (hp : p.IsPrime) (hmem : (⟨p, hp⟩ : PrimeSpectrum R) ∈ Module.support R M) :
    ∃ q ∈ associatedPrimes R M, q ≤ p := by
  have : Nontrivial (LocalizedModule p.primeCompl M) := hmem
  obtain ⟨q, hq⟩ :=
    associatedPrimes.nonempty (Localization.AtPrime p) (LocalizedModule p.primeCompl M)
  have q_prime : q.IsPrime := IsAssociatedPrime.isPrime hq
  rw [← preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    p.primeCompl (Localization.AtPrime p) (LocalizedModule.mkLinearMap p.primeCompl M)] at hq
  refine ⟨_, hq, ?_⟩
  have := (IsLocalization.disjoint_comap_iff p.primeCompl (Localization.AtPrime p) q).mpr
    q_prime.ne_top
  simpa only [Ideal.primeCompl, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
    Set.disjoint_compl_left_iff_subset] using this

/-- **The domain trick.** A nonzero submodule of `R ⧸ p`, for `p` prime, receives an injection
from `R ⧸ p`: multiplication by a nonzero element of it is injective, `R ⧸ p` being a domain, and
lands inside it, the submodule being an ideal. -/
lemma exists_injective_of_ne_bot {p : Ideal R} [hp : p.IsPrime] {J : Submodule R (R ⧸ p)}
    (hJ : J ≠ ⊥) : ∃ f : (R ⧸ p) →ₗ[R] J, Function.Injective f := by
  obtain ⟨x, hxJ, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hmem : ∀ d : R ⧸ p, x * d ∈ J := by
    intro d
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective d
    have : x * (Ideal.Quotient.mk p r) = r • x := by
      rw [mul_comm, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    rw [this]
    exact J.smul_mem r hxJ
  let g : (R ⧸ p) →ₗ[R] (R ⧸ p) :=
    { toFun := fun d => x * d
      map_add' := fun a b => mul_add x a b
      map_smul' := fun r a => by simp }
  refine ⟨g.codRestrict J hmem, fun a b hab => ?_⟩
  have : x * a = x * b := congrArg Subtype.val hab
  exact mul_left_cancel₀ hx this

end CommutativeAlgebra


section NoetherianObjects

/-- **A fully faithful functor preserving monomorphisms reflects noetherian objects.** Subobjects
of `X` map to subobjects of `F.obj X` order-embeddingly: monotonicity is the image of a
comparison morphism, and injectivity is fullness together with faithfulness. -/
lemma isNoetherianObject_of_fullyFaithful {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    [F.Full] [F.Faithful] [F.PreservesMonomorphisms] {X : C}
    [IsNoetherianObject (F.obj X)] : IsNoetherianObject X := by
  have hle : ∀ A B : Subobject X,
      A ≤ B ↔ Subobject.mk (F.map A.arrow) ≤ Subobject.mk (F.map B.arrow) := by
    intro A B
    constructor
    · intro h
      refine Subobject.mk_le_mk_of_comm (F.map (Subobject.ofLE A B h)) ?_
      rw [← F.map_comp, Subobject.ofLE_arrow]
    · intro h
      obtain ⟨u, hu⟩ := F.map_surjective (Subobject.ofMkLEMk _ _ h)
      refine Subobject.le_of_comm u (F.map_injective ?_)
      rw [F.map_comp, hu, Subobject.ofMkLEMk_comp]
  rw [isNoetherianObject_iff_not_strictMono]
  intro f hf
  refine not_strictMono_of_wellFoundedGT (fun n => Subobject.mk (F.map (f n).arrow)) ?_
  intro a b hab
  refine lt_of_le_of_ne ((hle _ _).1 (hf hab).le) (fun heq => ?_)
  exact absurd (le_antisymm ((hle _ _).2 heq.le) ((hle _ _).2 heq.ge)) (hf hab).ne

variable {R : Type u} [CommRing R]

instance isNoetherianObject_moduleCat (M : ModuleCat.{u} R) [IsNoetherian R M] :
    IsNoetherianObject M := by
  rw [isNoetherianObject_iff_not_strictMono]
  intro f hf
  exact not_strictMono_of_wellFoundedGT (fun n => ModuleCat.subobjectModule M (f n))
    (fun a b hab => (ModuleCat.subobjectModule M).lt_iff_lt.2 (hf hab))

instance isNoetherianObject_fgModuleCat [IsNoetherianRing R] (X : FGModuleCat.{u} R) :
    IsNoetherianObject X := by
  haveI : Module.Finite R X.obj := X.property
  haveI : IsNoetherian R X.obj := inferInstance
  haveI : IsNoetherianObject ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).obj X) :=
    isNoetherianObject_moduleCat X.obj
  exact isNoetherianObject_of_fullyFaithful (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))

end NoetherianObjects

namespace CategoryTheory.ObjectProperty

section ModuleCat

variable {R : Type u} [CommRing R] (T : ObjectProperty (ModuleCat.{u} R)) [T.IsSerreClass]

variable {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

lemma prop_of_linearEquiv (e : A ≃ₗ[R] B) (h : T (ModuleCat.of R A)) : T (ModuleCat.of R B) :=
  T.prop_of_iso e.toModuleIso h

lemma prop_of_injective (f : A →ₗ[R] B) (hf : Function.Injective f) (h : T (ModuleCat.of R B)) :
    T (ModuleCat.of R A) := by
  haveI : Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).2 hf
  exact T.prop_of_mono (ModuleCat.ofHom f) h

lemma prop_of_surjective (f : A →ₗ[R] B) (hf : Function.Surjective f) (h : T (ModuleCat.of R A)) :
    T (ModuleCat.of R B) := by
  haveI : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).2 hf
  exact T.prop_of_epi (ModuleCat.ofHom f) h

variable {C : Type u} [AddCommGroup C] [Module R C]

/-- Closure under extensions, in module language. -/
lemma prop_of_shortExact (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hexact : Function.Exact f g)
    (hA : T (ModuleCat.of R A)) (hC : T (ModuleCat.of R C)) : T (ModuleCat.of R B) := by
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (by
      ext x
      exact hexact.apply_apply_eq_zero x)
  have hS : S.ShortExact :=
    { mono_f := (ModuleCat.mono_iff_injective _).2 hf
      epi_g := (ModuleCat.epi_iff_surjective _).2 hg
      exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).2 hexact }
  exact T.prop_X₂_of_shortExact hS hA hC


variable {M : ModuleCat.{u} R}

/-- The hypothesis of condition (AS), read in submodule language: every nonzero submodule of `M`
contains a nonzero submodule lying in `T`. -/
lemma exists_le_prop_of_subEssential (h : T.SubEssential M) {N : Submodule R M} (hN : N ≠ ⊥) :
    ∃ N' : Submodule R M, N' ≤ N ∧ N' ≠ ⊥ ∧ T (ModuleCat.of R N') := by
  haveI : Mono (ModuleCat.ofHom N.subtype) :=
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  have hnz : ¬ IsZero (ModuleCat.of R (N : Type u)) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    intro hsub
    refine hN (Submodule.eq_bot_iff N |>.2 fun y hy => ?_)
    exact congrArg Subtype.val (Subsingleton.elim (⟨y, hy⟩ : (N : Type u)) 0)
  obtain ⟨V, v, hv, hv0, hV⟩ := h (ModuleCat.ofHom N.subtype) inferInstance hnz
  haveI := hv
  have hvinj : Function.Injective v.hom := (ModuleCat.mono_iff_injective v).1 hv
  have hcompinj : Function.Injective (N.subtype ∘ₗ v.hom) := Subtype.val_injective.comp hvinj
  refine ⟨LinearMap.range (N.subtype ∘ₗ v.hom), ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (v.hom x).2
  · intro hbot
    refine hv0 (ModuleCat.isZero_iff_subsingleton.2 ⟨fun a b => hcompinj ?_⟩)
    have hz : ∀ c : V, (N.subtype ∘ₗ v.hom) c = 0 := by
      intro c
      have hmem : (N.subtype ∘ₗ v.hom) c ∈ LinearMap.range (N.subtype ∘ₗ v.hom) := ⟨c, rfl⟩
      rw [hbot] at hmem
      exact (Submodule.mem_bot R).1 hmem
    rw [hz a, hz b]
  · exact T.prop_of_linearEquiv (LinearEquiv.ofInjective _ hcompinj) hV

/-- **The associated primes.** For `p` associated to `M`, the quotient `R ⧸ p` lies in `T`: the
hypothesis produces a nonzero submodule of `R ⧸ p` lying in `T`, and `R ⧸ p`, being a domain,
embeds into any of its nonzero submodules. -/
lemma prop_quotient_of_mem_associatedPrimes (h : T.SubEssential M) {p : Ideal R}
    (hp : p ∈ associatedPrimes R (M : Type u)) : T (ModuleCat.of R (R ⧸ p)) := by
  obtain ⟨hprime, f, hf⟩ := (isAssociatedPrime_iff_exists_injective_linearMap p (M : Type u)).1 hp
  haveI := hprime
  haveI : Nontrivial (R ⧸ p) := Submodule.Quotient.nontrivial_iff.2 hprime.ne_top
  have hN : LinearMap.range f ≠ ⊥ := by
    obtain ⟨d, hd⟩ := exists_ne (0 : R ⧸ p)
    intro hbot
    have hmem : f d ∈ LinearMap.range f := ⟨d, rfl⟩
    simp only [hbot, Submodule.mem_bot] at hmem
    exact hd (hf (by simp [hmem]))
  obtain ⟨N', hle, hN', hTN'⟩ := T.exists_le_prop_of_subEssential h hN
  have hmemJ : ∀ d ∈ N'.comap f, f d ∈ N' := fun d hd => hd
  have hJ : N'.comap f ≠ ⊥ := by
    obtain ⟨y, hyN', hy⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN'
    obtain ⟨d, rfl⟩ := hle hyN'
    intro hbot
    have hd : d ∈ N'.comap f := hyN'
    simp only [hbot, Submodule.mem_bot] at hd
    exact hy (by rw [hd, map_zero])
  have hTJ : T (ModuleCat.of R (N'.comap f : Type u)) := by
    refine T.prop_of_linearEquiv (LinearEquiv.ofBijective (f.restrict hmemJ) ⟨?_, ?_⟩).symm hTN'
    · intro a b hab
      exact Subtype.ext (hf (congrArg Subtype.val hab))
    · rintro ⟨y, hy⟩
      obtain ⟨d, rfl⟩ := hle hy
      exact ⟨⟨d, hy⟩, rfl⟩
  obtain ⟨g, hg⟩ := exists_injective_of_ne_bot hJ
  exact T.prop_of_injective g hg hTJ

/-- **Condition (AS) for the noetherian objects of `ModuleCat R`.** -/
theorem prop_of_subEssential [IsNoetherianRing R] [IsNoetherian R M] (h : T.SubEssential M) :
    T M := by
  have supp : ∀ (p : Ideal R) (hp : p.IsPrime),
      (⟨p, hp⟩ : PrimeSpectrum R) ∈ Module.support R (M : Type u) →
        T (ModuleCat.of R (R ⧸ p)) := by
    intro p hp hmem
    obtain ⟨q, hq, hqp⟩ := exists_associatedPrimes_le_of_mem_support hp hmem
    have hTq := T.prop_quotient_of_mem_associatedPrimes h hq
    have hcomap : q ≤ Submodule.comap (LinearMap.id : R →ₗ[R] R) p := by
      rwa [Submodule.comap_id]
    refine T.prop_of_surjective (Submodule.mapQ q p LinearMap.id hcomap) ?_ hTq
    intro y
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective p y
    exact ⟨Submodule.Quotient.mk r, rfl⟩
  have hbot : T (ModuleCat.of R ((⊥ : Submodule R M) : Type u)) := by
    have hz : IsZero (ModuleCat.of R ((⊥ : Submodule R M) : Type u)) :=
      ModuleCat.isZero_iff_subsingleton.2 inferInstance
    exact T.prop_of_iso hz.isoZero.symm T.prop_zero
  obtain ⟨N₀, hN₀, hmax⟩ :=
    (IsWellFounded.wf (r := ((· > ·) : Submodule R M → Submodule R M → Prop))).has_min
      {N : Submodule R M | T (ModuleCat.of R (N : Type u))} ⟨⊥, hbot⟩
  have htop : N₀ = ⊤ := by
    by_contra hne
    haveI : Nontrivial ((M : Type u) ⧸ N₀) := Submodule.Quotient.nontrivial_iff.2 hne
    obtain ⟨p, hp⟩ := associatedPrimes.nonempty R ((M : Type u) ⧸ N₀)
    haveI hprime : p.IsPrime := hp.1
    have hmem : (⟨p, hprime⟩ : PrimeSpectrum R) ∈ Module.support R (M : Type u) :=
      Module.support_subset_of_surjective N₀.mkQ N₀.mkQ_surjective
        (PrimeSpectrum.mem_support_of_mem_associatedPrimes hprime hp)
    have hTp : T (ModuleCat.of R (R ⧸ p)) := supp p hprime hmem
    obtain ⟨-, f, hf⟩ :=
      (isAssociatedPrime_iff_exists_injective_linearMap p ((M : Type u) ⧸ N₀)).1 hp
    have hres : ∀ x ∈ (LinearMap.range f).comap N₀.mkQ, N₀.mkQ x ∈ LinearMap.range f :=
      fun _ hx => hx
    have hle : N₀ ≤ (LinearMap.range f).comap N₀.mkQ := by
      intro x hx
      have hzero : N₀.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero N₀).2 hx
      simp [Submodule.mem_comap, hzero]
    have hTK : T (ModuleCat.of R (LinearMap.range f : Type u)) :=
      T.prop_of_linearEquiv (LinearEquiv.ofInjective f hf) hTp
    have hTN₁ : T (ModuleCat.of R ((LinearMap.range f).comap N₀.mkQ : Type u)) := by
      refine T.prop_of_shortExact (Submodule.inclusion hle) (N₀.mkQ.restrict hres)
        (Submodule.inclusion_injective hle) ?_ ?_ hN₀ hTK
      · rintro ⟨y, hy⟩
        obtain ⟨m, rfl⟩ := N₀.mkQ_surjective y
        exact ⟨⟨m, hy⟩, rfl⟩
      · intro b
        constructor
        · intro hb
          have hb' : N₀.mkQ b.1 = 0 := congrArg Subtype.val hb
          exact ⟨⟨b.1, (Submodule.Quotient.mk_eq_zero N₀).1 hb'⟩, rfl⟩
        · rintro ⟨a, rfl⟩
          exact Subtype.ext ((Submodule.Quotient.mk_eq_zero N₀).2 a.2)
    refine hmax _ hTN₁ (lt_of_le_of_ne hle ?_)
    intro heq
    obtain ⟨d, hd⟩ := exists_ne (0 : R ⧸ p)
    have hfd : f d ∈ LinearMap.range f := ⟨d, rfl⟩
    obtain ⟨m, hm⟩ := N₀.mkQ_surjective (f d)
    have hmem₁ : m ∈ (LinearMap.range f).comap N₀.mkQ := by simp [Submodule.mem_comap, hm]
    rw [← heq] at hmem₁
    refine hd (hf ?_)
    rw [map_zero, ← hm, Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero N₀).2 hmem₁
  have := hN₀
  rw [htop] at this
  exact T.prop_of_linearEquiv Submodule.topEquiv this

end ModuleCat


section FGModuleCat

open ModuleCat

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The Serre class of `ModuleCat R` determined by a Serre class of `FGModuleCat R`: the finitely
generated modules lying in it. Serre classes of the two categories correspond, and this is the
direction the witness needs. -/
def ofFG (T : ObjectProperty (FGModuleCat.{u} R)) : ObjectProperty (ModuleCat.{u} R) :=
  fun M => ∃ h : ModuleCat.isFG R M, T ⟨M, h⟩

variable (T : ObjectProperty (FGModuleCat.{u} R)) [T.IsSerreClass]

omit [IsNoetherianRing R] [T.IsSerreClass] in
lemma ofFG_iff {M : ModuleCat.{u} R} (h : ModuleCat.isFG R M) : ofFG T M ↔ T ⟨M, h⟩ :=
  ⟨fun ⟨_, hT⟩ => hT, fun hT => ⟨h, hT⟩⟩

instance : (ofFG T).ContainsZero where
  exists_zero :=
    ⟨(0 : FGModuleCat.{u} R).obj,
      Functor.map_isZero (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) (isZero_zero _),
      ⟨(0 : FGModuleCat.{u} R).property, T.prop_zero⟩⟩

instance : (ofFG T).IsClosedUnderSubobjects where
  prop_of_mono := by
    rintro X Y f hf ⟨hYfg, hTY⟩
    haveI := hf
    haveI : Module.Finite R Y := hYfg
    haveI : IsNoetherian R X :=
      isNoetherian_of_injective f.hom ((ModuleCat.mono_iff_injective f).1 hf)
    have hXfg : ModuleCat.isFG R X := inferInstanceAs (Module.Finite R X)
    refine ⟨hXfg, ?_⟩
    haveI : Mono (ObjectProperty.homMk (X := (⟨X, hXfg⟩ : FGModuleCat.{u} R))
        (Y := (⟨Y, hYfg⟩ : FGModuleCat.{u} R)) f) :=
      (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).mono_of_mono_map hf
    exact T.prop_of_mono (ObjectProperty.homMk (X := (⟨X, hXfg⟩ : FGModuleCat.{u} R))
      (Y := (⟨Y, hYfg⟩ : FGModuleCat.{u} R)) f) hTY

instance : (ofFG T).IsClosedUnderQuotients where
  prop_of_epi := by
    rintro X Y f hf ⟨hXfg, hTX⟩
    haveI := hf
    haveI : Module.Finite R X := hXfg
    haveI : IsNoetherian R Y :=
      isNoetherian_of_surjective X f.hom
        (LinearMap.range_eq_top.2 ((ModuleCat.epi_iff_surjective f).1 hf))
    have hYfg : ModuleCat.isFG R Y := inferInstanceAs (Module.Finite R Y)
    refine ⟨hYfg, ?_⟩
    haveI : Epi (ObjectProperty.homMk (X := (⟨X, hXfg⟩ : FGModuleCat.{u} R))
        (Y := (⟨Y, hYfg⟩ : FGModuleCat.{u} R)) f) :=
      (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).epi_of_epi_map hf
    exact T.prop_of_epi (ObjectProperty.homMk (X := (⟨X, hXfg⟩ : FGModuleCat.{u} R))
      (Y := (⟨Y, hYfg⟩ : FGModuleCat.{u} R)) f) hTX

instance : (ofFG T).IsClosedUnderExtensions where
  prop_X₂_of_shortExact := by
    rintro S hS ⟨h1fg, hT1⟩ ⟨h3fg, hT3⟩
    haveI := hS.mono_f
    haveI := hS.epi_g
    haveI : Module.Finite R S.X₁ := h1fg
    haveI : Module.Finite R S.X₃ := h3fg
    haveI : IsNoetherian R S.X₂ :=
      isNoetherian_of_range_eq_ker S.f.hom S.g.hom
        (((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1
          hS.exact).linearMap_ker_eq).symm
    have h2fg : ModuleCat.isFG R S.X₂ := inferInstanceAs (Module.Finite R S.X₂)
    refine ⟨h2fg, ?_⟩
    let S' : ShortComplex (FGModuleCat.{u} R) :=
      ShortComplex.mk
        (ObjectProperty.homMk (X := (⟨S.X₁, h1fg⟩ : FGModuleCat.{u} R))
          (Y := (⟨S.X₂, h2fg⟩ : FGModuleCat.{u} R)) S.f)
        (ObjectProperty.homMk (X := (⟨S.X₂, h2fg⟩ : FGModuleCat.{u} R))
          (Y := (⟨S.X₃, h3fg⟩ : FGModuleCat.{u} R)) S.g)
        (by
          apply (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).map_injective
          rw [Functor.map_comp, Functor.map_zero]
          exact S.zero)
    have hmap : S'.map (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) = S := rfl
    have hS' : S'.ShortExact :=
      { mono_f := (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).mono_of_mono_map hS.mono_f
        epi_g := (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).epi_of_epi_map hS.epi_g
        exact := by
          rw [← ShortComplex.exact_map_iff_of_faithful S'
            (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)), hmap]
          exact hS.exact }
    exact T.prop_X₂_of_shortExact hS' hT1 hT3

instance : (ofFG T).IsSerreClass where

/-- **Proposition 8.24 `P:ModAS`, the (AS) half.** Condition (AS) holds for the finitely
generated modules over a commutative noetherian ring. With `isNoetherianObject_fgModuleCat`,
this is the witness that `CondAS` is not an empty hypothesis. -/
theorem condAS_fgModuleCat : CondAS (FGModuleCat.{u} R) := by
  intro T hT X hX
  haveI := hT
  haveI : Module.Finite R X.obj := X.property
  haveI : IsNoetherian R X.obj := inferInstance
  refine ((ofFG_iff T X.property).1 ?_)
  refine (ofFG T).prop_of_subEssential ?_
  intro Y i hi hi0
  haveI : Module.Finite R Y := by
    haveI : IsNoetherian R X.obj := inferInstance
    exact (isNoetherian_of_injective i.hom ((ModuleCat.mono_iff_injective i).1 hi)).finite
  have hYfg : ModuleCat.isFG R Y := inferInstanceAs (Module.Finite R Y)
  haveI : Mono (ObjectProperty.homMk (X := (⟨Y, hYfg⟩ : FGModuleCat.{u} R)) (Y := X) i) :=
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).mono_of_mono_map hi
  obtain ⟨V, v, hv, hv0, hV⟩ := hX (ObjectProperty.homMk (X := ⟨Y, hYfg⟩) (Y := X) i) ‹_› (by
    intro h0
    exact hi0 (Functor.map_isZero (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)) h0))
  refine ⟨V.obj, v.hom, ?_, ?_, ⟨V.property, hV⟩⟩
  · exact (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).map_mono v
  · intro h0
    refine hv0 ?_
    rw [IsZero.iff_id_eq_zero]
    apply (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).map_injective
    rw [Functor.map_id, Functor.map_zero]
    exact (IsZero.iff_id_eq_zero _).1 h0

/-- **The saturation theorem, fully instantiated** — Proposition 8.24 `P:ModAS` followed by
Proposition 8.21 `P:ASimplies`, as in Corollary 8.27 `C:Populated`. For the finitely generated
modules over a commutative noetherian ring, the `S`-saturation of a Serre class `K` is a Serre
class, for every pair `K` and `S`. No hypotheses remain: `CondAS` is `condAS_fgModuleCat` and
the noetherianness of the objects is `isNoetherianObject_fgModuleCat`.

Unwound through Proposition 8.11 `P:DIabcat`, this says that the composite of the inclusion of a
Serre subcategory and a Serre quotient factors as a normal 2-epimorphism followed by a normal
2-monomorphism, which is condition (DI2) for these categories. -/
theorem isSerreClass_serreSaturation_fgModuleCat (S K : ObjectProperty (FGModuleCat.{u} R))
    [S.IsSerreClass] [K.IsSerreClass] : (serreSaturation S K).IsSerreClass :=
  isSerreClass_serreSaturation_of_condAS S K condAS_fgModuleCat

end FGModuleCat

end CategoryTheory.ObjectProperty
