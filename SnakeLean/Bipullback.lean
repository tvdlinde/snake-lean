/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.ZExact

/-!
# Bipullbacks

This module formalises Definition 5.2 `Def Bipullback` and Proposition 5.3
`Kernel vs pullback`: a 2-kernel is exactly a bipullback along a null 1-cell.

Mathlib has no bicategorical limit theory at all, so the definition is built from nothing. It is
the paper's verbatim: an apex with two projections and an invertible filler, a 1-dimensional
universal property whose factorisation 2-cells are required to paste to the given square, and a
2-dimensional universal property.

## Where this sits

Nothing in `SnakeLean.Null` through `SnakeLean.ThirdIso` imports this module. Sections 2, 3 and 4
of the paper are machine-checked with no notion of bipullback anywhere in scope. That is the
formal content of the paper's own arrangement: bipullbacks are gathered into Section 5, after all
the material that does not need them.

## Strictness

`Bicategory.Strict` makes reassociation a propositional equality of 1-cells rather than a
coherent isomorphism, so pastings still need `eqToIso` to move between `(u ≫ p₂) ≫ g` and
`u ≫ p₂ ≫ g`. `squareIso` packages the one reassociated whiskering that both universal
properties refer to, which keeps the two conditions readable.

## Main results

* `IsBipullback` and `IsBipushout` — Definition 5.2 `Def Bipullback` and its dual.
* `isBipullback_of_isTwoMono` — a criterion that reduces a bipullback to a single factorisation
  property, used throughout `SnakeLean.Squares`.
* `isBipullback_of_isTwoKernel` and `isTwoKernel_of_isBipullback` — Proposition
  5.3 `Kernel vs pullback`, in both directions.

## Not formalised

The dual of Proposition 5.3 `Kernel vs pullback`, that a 2-cokernel is a bipushout along a null
1-cell, is not stated, since nothing consumes it. Proposition 5.4 `P:NormalMonoBipullback` and
the two squares of a morphism of short 2-exact sequences are in `SnakeLean.Squares`.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.Strict B]

/-- The structure 2-cell of a square, whiskered by a 1-cell into its apex and reassociated. -/
def squareIso {P A A' C : B} {p₁ : P ⟶ A} {p₂ : P ⟶ A'} {f : A ⟶ C} {g : A' ⟶ C}
    (φ : p₂ ≫ g ≅ p₁ ≫ f) {Z : B} (u : Z ⟶ P) : (u ≫ p₂) ≫ g ≅ (u ≫ p₁) ≫ f :=
  eqToIso (Category.assoc u p₂ g) ≪≫ Bicategory.whiskerLeftIso u φ ≪≫
    (eqToIso (Category.assoc u p₁ f)).symm

/-- **Definition 5.2 `Def Bipullback`.** A square filled by an invertible 2-cell `φ` is a
**bipullback** when every square over the same cospan factors through it, by a 1-cell whose two
factorisation 2-cells paste to the given filler, and when the 2-cells into the apex are detected
by the two projections. -/
structure IsBipullback {P A A' C : B} (p₁ : P ⟶ A) (p₂ : P ⟶ A') (f : A ⟶ C) (g : A' ⟶ C)
    (φ : p₂ ≫ g ≅ p₁ ≫ f) : Prop where
  /-- The 1-dimensional universal property, with the pasting condition. -/
  fac {Z : B} (a : Z ⟶ A) (b : Z ⟶ A') (ψ : b ≫ g ≅ a ≫ f) :
    ∃ (u : Z ⟶ P) (γ₁ : u ≫ p₁ ≅ a) (γ₂ : u ≫ p₂ ≅ b),
      ψ = (Bicategory.whiskerRightIso γ₂ g).symm ≪≫ squareIso φ u ≪≫
        Bicategory.whiskerRightIso γ₁ f
  /-- The 2-dimensional universal property. -/
  ext {Z : B} {u v : Z ⟶ P} (ℓ₁ : u ≫ p₁ ⟶ v ≫ p₁) (ℓ₂ : u ≫ p₂ ⟶ v ≫ p₂)
    (hcompat : (ℓ₂ ▷ g) ≫ (squareIso φ v).hom = (squareIso φ u).hom ≫ (ℓ₁ ▷ f)) :
    ∃! μ : u ⟶ v, μ ▷ p₁ = ℓ₁ ∧ μ ▷ p₂ = ℓ₂

section General

variable {P A A' C : B} {p₁ : P ⟶ A} {p₂ : P ⟶ A'} {f : A ⟶ C} {g : A' ⟶ C}

/-- The whiskered structure 2-cell is natural in the 1-cell into the apex. -/
theorem squareIso_naturality (φ : p₂ ≫ g ≅ p₁ ≫ f) {Z : B} {u v : Z ⟶ P} (μ : u ⟶ v) :
    ((μ ▷ p₂) ▷ g) ≫ (squareIso φ v).hom = (squareIso φ u).hom ≫ ((μ ▷ p₁) ▷ f) := by
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, ← Bicategory.Strict.associator_eqToIso,
    Bicategory.whiskerLeftIso_hom]
  rw [← Category.assoc, Bicategory.associator_naturality_left]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc (μ ▷ (p₂ ≫ g)), ← Bicategory.whisker_exchange]
  simp only [Category.assoc]
  congr 1
  simp

/-- A square whose right-hand leg and whose left-hand projection are 2-monomorphisms is a
bipullback as soon as the projection `p₂` has the factorisation property. Both halves of the
universal property then come for free: the 2-cell `γ₁` is forced, and with it the pasting
condition, while the 2-dimensional property is `p₂` being fully faithful together with
`squareIso_naturality`. -/
theorem isBipullback_of_isTwoMono (φ : p₂ ≫ g ≅ p₁ ≫ f) [IsTwoMono f] [IsTwoMono p₂]
    (hfac : ∀ {Z : B} (a : Z ⟶ A) (b : Z ⟶ A'), (b ≫ g ≅ a ≫ f) →
      ∃ u : Z ⟶ P, Nonempty (u ≫ p₂ ≅ b)) :
    IsBipullback p₁ p₂ f g φ := by
  constructor
  · intro Z a b ψ
    obtain ⟨u, ⟨γ₂⟩⟩ := hfac a b ψ
    refine ⟨u, IsTwoMono.preimageIso f ((squareIso φ u).symm ≪≫
      Bicategory.whiskerRightIso γ₂ g ≪≫ ψ), γ₂, ?_⟩
    have hpre : (IsTwoMono.preimageIso f ((squareIso φ u).symm ≪≫
        Bicategory.whiskerRightIso γ₂ g ≪≫ ψ)).hom ▷ f =
        ((squareIso φ u).symm ≪≫ Bicategory.whiskerRightIso γ₂ g ≪≫ ψ).hom :=
      (Bicategory.postcomp Z f).map_preimage _
    refine Iso.ext ?_
    simp only [Iso.trans_hom, Iso.symm_hom, Bicategory.whiskerRightIso_hom, hpre]
    simp
  · intro Z u v ℓ₁ ℓ₂ hcompat
    obtain ⟨μ, hμ⟩ := (Bicategory.postcomp Z p₂).map_surjective ℓ₂
    refine ⟨μ, ⟨(Bicategory.postcomp Z f).map_injective ?_, hμ⟩, ?_⟩
    · have hnat := squareIso_naturality φ μ
      rw [show μ ▷ p₂ = ℓ₂ from hμ] at hnat
      exact (Iso.cancel_iso_hom_left (squareIso φ u) _ _).mp (hnat.symm.trans hcompat)
    · rintro ν ⟨-, hν⟩
      exact (Bicategory.postcomp Z p₂).map_injective (hν.trans hμ.symm)

/-- Two 1-cells into the apex of a bipullback that agree, compatibly, on both projections are
isomorphic. -/
theorem IsBipullback.nonempty_ext_iso {φ : p₂ ≫ g ≅ p₁ ≫ f} (h : IsBipullback p₁ p₂ f g φ)
    {Z : B} {u v : Z ⟶ P} (α : u ≫ p₁ ≅ v ≫ p₁) (β : u ≫ p₂ ≅ v ≫ p₂)
    (hcompat : (β.hom ▷ g) ≫ (squareIso φ v).hom = (squareIso φ u).hom ≫ (α.hom ▷ f)) :
    Nonempty (u ≅ v) := by
  have hinv : (β.inv ▷ g) ≫ (squareIso φ u).hom = (squareIso φ v).hom ≫ (α.inv ▷ f) := by
    change (Bicategory.whiskerRightIso β g).inv ≫ _ = _ ≫ (Bicategory.whiskerRightIso α f).inv
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact hcompat.symm
  obtain ⟨μ, ⟨hμ₁, hμ₂⟩, -⟩ := h.ext α.hom β.hom hcompat
  obtain ⟨ν, ⟨hν₁, hν₂⟩, -⟩ := h.ext α.inv β.inv hinv
  refine ⟨⟨μ, ν, ?_, ?_⟩⟩
  · obtain ⟨w, -, huniq⟩ := h.ext (𝟙 (u ≫ p₁)) (𝟙 (u ≫ p₂)) (by simp)
    exact (huniq (μ ≫ ν) (by simp [Bicategory.comp_whiskerRight, hμ₁, hμ₂, hν₁, hν₂])).trans
      (huniq (𝟙 u) (by simp)).symm
  · obtain ⟨w, -, huniq⟩ := h.ext (𝟙 (v ≫ p₁)) (𝟙 (v ≫ p₂)) (by simp)
    exact (huniq (ν ≫ μ) (by simp [Bicategory.comp_whiskerRight, hμ₁, hμ₂, hν₁, hν₂])).trans
      (huniq (𝟙 v) (by simp)).symm

end General

/-- The structure 2-cell of a cosquare, whiskered by a 1-cell out of its apex and reassociated. -/
def cosquareIso {C A A' P : B} {i₁ : A ⟶ P} {i₂ : A' ⟶ P} {f : C ⟶ A} {g : C ⟶ A'}
    (φ : g ≫ i₂ ≅ f ≫ i₁) {Z : B} (u : P ⟶ Z) : g ≫ i₂ ≫ u ≅ f ≫ i₁ ≫ u :=
  (eqToIso (Category.assoc g i₂ u)).symm ≪≫ Bicategory.whiskerRightIso φ u ≪≫
    eqToIso (Category.assoc f i₁ u)

/-- The dual of `IsBipullback`.

This is the **one** notion in the development whose dual is still written out rather than
transported through `Bᵒᵖ` (see `SnakeLean.Op`). The reason is that `IsBipullback` is the only
definition here whose fields are *equations between 2-cells* rather than propositions about
1-cells: transporting it would need `op2` to be shown compatible with `▷`, `◁`, `squareIso` and
the pasting condition, which costs at least as much as the second proof it would save.

Everywhere else in the development a dual whose proof runs to more than a line or two is a
transport; what remains hand-written is only the duals a transport would not shorten. -/
structure IsBipushout {C A A' P : B} (i₁ : A ⟶ P) (i₂ : A' ⟶ P) (f : C ⟶ A) (g : C ⟶ A')
    (φ : g ≫ i₂ ≅ f ≫ i₁) : Prop where
  /-- The 1-dimensional universal property, with the pasting condition. -/
  fac {Z : B} (a : A ⟶ Z) (b : A' ⟶ Z) (ψ : g ≫ b ≅ f ≫ a) :
    ∃ (u : P ⟶ Z) (γ₁ : i₁ ≫ u ≅ a) (γ₂ : i₂ ≫ u ≅ b),
      ψ = (Bicategory.whiskerLeftIso g γ₂).symm ≪≫ cosquareIso φ u ≪≫
        Bicategory.whiskerLeftIso f γ₁
  /-- The 2-dimensional universal property. -/
  ext {Z : B} {u v : P ⟶ Z} (ℓ₁ : i₁ ≫ u ⟶ i₁ ≫ v) (ℓ₂ : i₂ ≫ u ⟶ i₂ ≫ v)
    (hcompat : (g ◁ ℓ₂) ≫ (cosquareIso φ v).hom = (cosquareIso φ u).hom ≫ (f ◁ ℓ₁)) :
    ∃! μ : u ⟶ v, i₁ ◁ μ = ℓ₁ ∧ i₂ ◁ μ = ℓ₂

section GeneralOp

variable {C A A' P : B} {i₁ : A ⟶ P} {i₂ : A' ⟶ P} {f : C ⟶ A} {g : C ⟶ A'}

/-- The dual of `squareIso_naturality`. -/
theorem cosquareIso_naturality (φ : g ≫ i₂ ≅ f ≫ i₁) {Z : B} {u v : P ⟶ Z} (μ : u ⟶ v) :
    (g ◁ (i₂ ◁ μ)) ≫ (cosquareIso φ v).hom = (cosquareIso φ u).hom ≫ (f ◁ (i₁ ◁ μ)) := by
  simp only [cosquareIso, Iso.trans_hom, Iso.symm_hom, ← Bicategory.Strict.associator_eqToIso,
    Bicategory.whiskerRightIso_hom]
  simp only [← Category.assoc]
  rw [Bicategory.associator_inv_naturality_right]
  simp only [Category.assoc]
  congr 1
  simp only [← Category.assoc]
  rw [Bicategory.whisker_exchange]
  simp only [Category.assoc]
  congr 1
  simp

/-- The dual of `IsBipullback.nonempty_ext_iso`. -/
theorem IsBipushout.nonempty_ext_iso {φ : g ≫ i₂ ≅ f ≫ i₁} (h : IsBipushout i₁ i₂ f g φ)
    {Z : B} {u v : P ⟶ Z} (α : i₁ ≫ u ≅ i₁ ≫ v) (β : i₂ ≫ u ≅ i₂ ≫ v)
    (hcompat : (g ◁ β.hom) ≫ (cosquareIso φ v).hom = (cosquareIso φ u).hom ≫ (f ◁ α.hom)) :
    Nonempty (u ≅ v) := by
  have hinv : (g ◁ β.inv) ≫ (cosquareIso φ u).hom = (cosquareIso φ v).hom ≫ (f ◁ α.inv) := by
    change (Bicategory.whiskerLeftIso g β).inv ≫ _ = _ ≫ (Bicategory.whiskerLeftIso f α).inv
    rw [Iso.inv_comp_eq]
    simp only [← Category.assoc]
    rw [Iso.eq_comp_inv]
    exact hcompat.symm
  obtain ⟨μ, ⟨hμ₁, hμ₂⟩, -⟩ := h.ext α.hom β.hom hcompat
  obtain ⟨ν, ⟨hν₁, hν₂⟩, -⟩ := h.ext α.inv β.inv hinv
  refine ⟨⟨μ, ν, ?_, ?_⟩⟩
  · obtain ⟨w, -, huniq⟩ := h.ext (𝟙 (i₁ ≫ u)) (𝟙 (i₂ ≫ u)) (by simp)
    exact (huniq (μ ≫ ν) (by simp [Bicategory.whiskerLeft_comp, hμ₁, hμ₂, hν₁, hν₂])).trans
      (huniq (𝟙 u) (by simp)).symm
  · obtain ⟨w, -, huniq⟩ := h.ext (𝟙 (i₁ ≫ v)) (𝟙 (i₂ ≫ v)) (by simp)
    exact (huniq (ν ≫ μ) (by simp [Bicategory.whiskerLeft_comp, hμ₁, hμ₂, hν₁, hν₂])).trans
      (huniq (𝟙 v) (by simp)).symm

end GeneralOp

section KernelVsPullback

variable {O : B} [HasBizero O] [IsStrong O] {K A A' : B}

omit [Strict B] [HasBizero O] in
/-- Any two parallel 2-cells between null 1-cells agree. -/
theorem null_hom_ext {a b : B} {m n : a ⟶ b} (hm : IsNull O m) (hn : IsNull O n) (α β : m ⟶ n) :
    α = β :=
  (IsStrong.subsingleton_hom hm hn).elim α β

/-- **Proposition 5.3 `Kernel vs pullback`, forward direction.** A 2-kernel is a bipullback along
a null 1-cell. -/
theorem isBipullback_of_isTwoKernel {f : A ⟶ A'} {k : K ⟶ A} (h : IsTwoKernel O f k)
    (t : K ⟶ O) (φ : t ≫ HasBizero.fromZero (O := O) A' ≅ k ≫ f) :
    IsBipullback k t f (HasBizero.fromZero (O := O) A') φ := by
  haveI := h.isTwoMono
  constructor
  · intro Z a b ψ
    have hb : IsNull O (b ≫ HasBizero.fromZero (O := O) A') := ⟨b, _, rfl⟩
    obtain ⟨u, ⟨γ₁⟩⟩ := h.fac a ⟨_, hb, ⟨ψ.symm⟩⟩
    obtain ⟨γ₂⟩ := (isNull_to (u ≫ t)).nonempty_iso (isNull_to b)
    refine ⟨u, γ₁, γ₂, ?_⟩
    -- both sides are invertible 2-cells out of a null 1-cell, so they agree.
    have hsymm : ψ.symm = ((Bicategory.whiskerRightIso γ₂ _).symm ≪≫ squareIso φ u ≪≫
        Bicategory.whiskerRightIso γ₁ f).symm :=
      hb.iso_ext _ _
    simpa using congrArg Iso.symm hsymm
  · intro Z u v ℓ₁ _ _
    obtain ⟨μ, hμ⟩ := (Bicategory.postcomp Z k).map_surjective ℓ₁
    refine ⟨μ, ⟨hμ, null_hom_ext (isNull_to _) (isNull_to _) _ _⟩, ?_⟩
    rintro ν ⟨hν, -⟩
    exact (Bicategory.postcomp Z k).map_injective (hν.trans hμ.symm)

/-- **Proposition 5.3 `Kernel vs pullback`, converse direction.** A bipullback along a null 1-cell
is a 2-kernel. -/
theorem isTwoKernel_of_isBipullback {f : A ⟶ A'} {k : K ⟶ A} {t : K ⟶ O}
    {φ : t ≫ HasBizero.fromZero (O := O) A' ≅ k ≫ f}
    (h : IsBipullback k t f (HasBizero.fromZero (O := O) A') φ) : IsTwoKernel O f k := by
  have hnull : ∀ {Z : B} (z : Z ⟶ O), IsNull O (z ≫ HasBizero.fromZero (O := O) A') :=
    fun z => ⟨z, _, rfl⟩
  have compat : ∀ {Z : B} {u v : Z ⟶ K} (ℓ₁ : u ≫ k ⟶ v ≫ k) (ℓ₂ : u ≫ t ⟶ v ≫ t),
      (ℓ₂ ▷ HasBizero.fromZero (O := O) A') ≫ (squareIso φ v).hom
        = (squareIso φ u).hom ≫ (ℓ₁ ▷ f) := by
    intro Z u v ℓ₁ ℓ₂
    have hstep : ℓ₂ ▷ HasBizero.fromZero (O := O) A'
        = (squareIso φ u).hom ≫ (ℓ₁ ▷ f) ≫ (squareIso φ v).inv :=
      null_hom_ext (hnull (u ≫ t)) (hnull (v ≫ t)) _ _
    rw [hstep]
    simp
  refine ⟨⟨_, hnull t, ⟨φ.symm⟩⟩, ?_, ?_⟩
  · intro Z z hz
    obtain ⟨n, hn, ⟨ζ⟩⟩ := hz
    obtain ⟨ψ⟩ := (hnull (HasBizero.toZero (O := O) Z)).nonempty_iso hn
    obtain ⟨u, γ₁, -, -⟩ := h.fac z (HasBizero.toZero (O := O) Z) (ψ ≪≫ ζ.symm)
    exact ⟨u, ⟨γ₁⟩⟩
  · refine ⟨fun Z => ⟨fun {u v} ℓ₁ => ?_⟩, fun Z => ⟨fun {u v} μ ν hμν => ?_⟩⟩
    · obtain ⟨ℓ₂⟩ := IsStrong.nonempty_hom (Z := O) (isNull_to (u ≫ t)) (isNull_to (v ≫ t))
      obtain ⟨μ, ⟨hμ, -⟩, -⟩ := h.ext ℓ₁ ℓ₂ (compat ℓ₁ ℓ₂)
      exact ⟨μ, hμ⟩
    · obtain ⟨w, -, huniq⟩ := h.ext (μ ▷ k) (μ ▷ t) (compat _ _)
      have : ∀ x : u ⟶ v, x ▷ k = μ ▷ k → x = w := fun x hx =>
        huniq x ⟨hx, null_hom_ext (isNull_to _) (isNull_to _) _ _⟩
      exact (this μ rfl).trans (this ν hμν.symm).symm

end KernelVsPullback

end SnakeLean
