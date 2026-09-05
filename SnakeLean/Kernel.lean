/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.Null
import SnakeLean.Mono
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.PUnit

/-!
# 2-kernels and 2-cokernels

This module formalises the 2-kernels and 2-cokernels of Section 2 of *A two-categorical Snake
Lemma*, together with the results of Section 3 that concern them directly.

Mathlib has no bicategorical limit theory whatsoever, so everything here is built from scratch.
Following the paper, we work in a **2-category**, that is, a strict bicategory: a null 1-cell is
one that factors through the bizero object `O` on the nose, and that is only stable under
composition when composition is strictly associative.

## The structure 2-cell is not structure

The paper's 2-kernel is a 1-cell `k` **together with** an invertible 2-cell `κ : k ≫ f ≅ 0`. By
`IsNull.eq_of_isIso` from `SnakeLean.Null`, such a 2-cell into a fixed null 1-cell is unique as
soon as it exists. So being a 2-kernel is a proposition, not structure, and `IsTwoKernel` is
stated as one.

Two consequences for the paper, both of which it now takes. First, Definition 3.12 `Def:SES` does
not ask that *the same* invertible 2-cell exhibit `k` as a 2-kernel of `q` and `q` as a 2-cokernel
of `k`; it simply writes `κ : q ∘ k ≅ 0` for the 2-cell exhibiting both, there being only one to
begin with. An earlier draft had to argue the point in a separate remark. Second, condition (1) of
Definition 2.18 `Def 2-kernel` imposes no compatibility between
the factorisation 2-cell `γ` and the structure 2-cell `κ`, and needs none: any compatibility one
might ask for is an equation between invertible 2-cells into a null 1-cell.

## Deviations from the paper

Condition (2) of Definition 2.18 `Def 2-kernel` says that whiskering with `k` is a bijection on
2-cells, which is verbatim `IsTwoMono k`. It is taken as the definition here, so that Proposition
2.21 `Prop Kernel Is Mono`, that 2-kernels are 2-monomorphisms, becomes definitional.

The vanishing hypothesis is phrased as `IsEssNull`, "isomorphic to some null 1-cell", rather
than as "isomorphic to the chosen null 1-cell `zero1`". `isEssNull_iff` shows the two agree, so
this is a matter of convenience; the paper is implicitly using that agreement whenever it writes
`0` for a null morphism without saying which.

## Main results

* `isTwoKernel_comp_isTwoMono_iff` — Proposition 3.9 `CoKernel of Composite`: postcomposing with a
  2-monomorphism does not change the 2-kernel, and dually.
* `IsEssNull.of_comp_isTwoMono` — Proposition 2.16 `prop2monoreflectsnull`: every 2-monomorphism
  reflects null morphisms, and dually. `ReflectsNull` and `CoreflectsNull` are Definition 2.11
  `Def Reflects Null`, and `IsTwoMono.reflectsNull` restates the proposition in those terms.
* `IsTwoKernel.equivalence` — Corollary 2.22 `corollkeruniqueuptoequiv`: 2-kernels are unique up to
  equivalence, and dually.

## Not formalised

Nothing of Section 2 that belongs here. That the 2-kernel is the bipullback along a null 1-cell
(Proposition 5.3 `Kernel vs pullback`) is in `SnakeLean.Bipullback`; that a 2-monomorphism has
trivial 2-kernel (Lemma 2.24 `2-Mono Trivial Kernel`), with the notion of trivial object, in
`SnakeLean.Exact`, as are short 2-exact sequences and everything above them.

## Duality

`isTwoCokernel_op` and `isTwoKernel_op` transport 2-kernels and 2-cokernels through the 1-cell
dual, and the dual results below are obtained from their primal forms by applying them in `Bᵒᵖ`
rather than by a second proof. See `SnakeLean.Op`.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.Strict B]

/-- A choice of 1-cell into and out of `O`, witnessing that the hom-categories of a bizero object
are nonempty. Together with `IsStrong O` this is all the paper's bizero condition is used for. -/
class HasBizero (O : B) where
  /-- The chosen 1-cell into `O`. -/
  toZero : ∀ a : B, a ⟶ O
  /-- The chosen 1-cell out of `O`. -/
  fromZero : ∀ b : B, O ⟶ b

/-- The chosen null 1-cell `a ⟶ b`, written `0` in the paper. -/
def zero1 (O : B) [inst : HasBizero O] (a b : B) : a ⟶ b :=
  inst.toZero a ≫ inst.fromZero b

omit [Strict B] in
theorem isNull_zero1 (O : B) [HasBizero O] (a b : B) : IsNull O (zero1 O a b) :=
  ⟨_, _, rfl⟩

/-- **Definition 2.3 `Def Bizero Object`**, verbatim: `O` is a **bizero object** when every
hom-category into it and every hom-category out of it is equivalent to the terminal category. -/
def IsBizero (O : B) : Prop :=
  ∀ a : B, Nonempty ((a ⟶ O) ≌ Discrete PUnit.{w + 1}) ∧
    Nonempty ((O ⟶ a) ≌ Discrete PUnit.{w + 1})

/-- **`HasBizero` together with `IsStrong` is the paper's strong bizero object.** In a 2-category
every 1-cell into `O` is null, so `IsStrong` makes each hom-category into `O` chaotic — exactly one
2-cell between any two objects — and `HasBizero` makes it nonempty; a nonempty chaotic category is
equivalent to the terminal one. Dually for the hom-categories out of `O`. This is why the
development never carries the bizero condition as a hypothesis of its own: the two classes it does
carry are together Definition 2.5 `Def Strong`. -/
theorem isBizero_of_isStrong (O : B) [HasBizero O] [IsStrong O] : IsBizero O := fun a =>
  ⟨(equiv_punit_iff_unique (a ⟶ O)).2 ⟨⟨HasBizero.toZero a⟩, fun t t' =>
      ⟨@Unique.mk' _ ⟨(IsStrong.nonempty_hom (isNull_to t) (isNull_to t')).some⟩
        (IsStrong.subsingleton_hom (isNull_to t) (isNull_to t'))⟩⟩,
    (equiv_punit_iff_unique (O ⟶ a)).2 ⟨⟨HasBizero.fromZero a⟩, fun i i' =>
      ⟨@Unique.mk' _ ⟨(IsStrong.nonempty_hom (isNull_from i) (isNull_from i')).some⟩
        (IsStrong.subsingleton_hom (isNull_from i) (isNull_from i'))⟩⟩⟩

omit [Strict B] in
/-- Conversely, a bizero object can be pointed: each hom-category into or out of it is nonempty. -/
theorem HasBizero.of_isBizero {O : B} (h : IsBizero O) : Nonempty (HasBizero O) :=
  ⟨{ toZero := fun a => (h a).1.some.inverse.obj (Discrete.mk PUnit.unit)
     fromZero := fun b => (h b).2.some.inverse.obj (Discrete.mk PUnit.unit) }⟩

/-- A 1-cell is **essentially null** when it is isomorphic to a null 1-cell. This is what the
paper writes as `f ≅ 0`. -/
def IsEssNull (O : B) {a b : B} (f : a ⟶ b) : Prop :=
  ∃ n : a ⟶ b, IsNull O n ∧ Nonempty (f ≅ n)

section Opposite

open Opposite Bicategory.Opposite

/-- The bizero object of `B` is a bizero object of `Bᵒᵖ`. -/
instance bizeroOp (O : B) [HasBizero O] : HasBizero (op O) where
  toZero a := (HasBizero.fromZero (O := O) a.unop).op
  fromZero b := (HasBizero.toZero (O := O) b.unop).op

variable {O : B} {a b : B}

omit [Strict B]

/-- Being essentially null is self-dual. -/
theorem isEssNull_op {f : a ⟶ b} (h : IsEssNull O f) : IsEssNull (op O) f.op := by
  obtain ⟨n, hn, ⟨θ⟩⟩ := h
  exact ⟨n.op, isNull_op hn, ⟨θ.op2⟩⟩

theorem isEssNull_of_op {f : a ⟶ b} (h : IsEssNull (op O) f.op) : IsEssNull O f := by
  obtain ⟨n, hn, ⟨θ⟩⟩ := h
  exact ⟨n.unop, isNull_of_op (by simpa using hn), ⟨θ.unop2⟩⟩

theorem isEssNull_op_iff (f : a ⟶ b) : IsEssNull (op O) f.op ↔ IsEssNull O f :=
  ⟨isEssNull_of_op, isEssNull_op⟩

end Opposite

section EssNull

variable {O : B} [HasBizero O] [IsStrong O] {a b c : B}

omit [Strict B] in
/-- Being isomorphic to some null 1-cell is the same as being isomorphic to the chosen one. -/
theorem isEssNull_iff (f : a ⟶ b) : IsEssNull O f ↔ Nonempty (f ≅ zero1 O a b) := by
  refine ⟨fun ⟨n, hn, ⟨θ⟩⟩ => ?_, fun ⟨θ⟩ => ⟨_, isNull_zero1 O a b, ⟨θ⟩⟩⟩
  obtain ⟨ζ⟩ := hn.nonempty_iso (isNull_zero1 O a b)
  exact ⟨θ ≪≫ ζ⟩

omit [Strict B] [IsStrong O] in
theorem isEssNull_zero1 (a b : B) : IsEssNull O (zero1 O a b) :=
  ⟨_, isNull_zero1 O a b, ⟨Iso.refl _⟩⟩

omit [Strict B] [HasBizero O] [IsStrong O] in
theorem IsEssNull.of_iso {f g : a ⟶ b} (θ : f ≅ g) (h : IsEssNull O f) : IsEssNull O g := by
  obtain ⟨n, hn, ⟨ζ⟩⟩ := h
  exact ⟨n, hn, ⟨θ.symm ≪≫ ζ⟩⟩

theorem nonempty_zero1_comp (m : b ⟶ c) : Nonempty (zero1 O a b ≫ m ≅ zero1 O a c) := by
  obtain ⟨η⟩ := (isNull_from (HasBizero.fromZero (O := O) b ≫ m)).nonempty_iso
    (isNull_from (HasBizero.fromZero (O := O) c))
  refine ⟨eqToIso ?_ ≪≫ Bicategory.whiskerLeftIso (HasBizero.toZero (O := O) a) η⟩
  simp [zero1]

theorem nonempty_comp_zero1 (f : a ⟶ b) : Nonempty (f ≫ zero1 O b c ≅ zero1 O a c) := by
  obtain ⟨η⟩ := (isNull_to (f ≫ HasBizero.toZero (O := O) b)).nonempty_iso
    (isNull_to (HasBizero.toZero (O := O) a))
  refine ⟨eqToIso ?_ ≪≫ Bicategory.whiskerRightIso η (HasBizero.fromZero (O := O) c)⟩
  simp [zero1]

theorem IsEssNull.comp {f : a ⟶ b} (h : IsEssNull O f) (m : b ⟶ c) : IsEssNull O (f ≫ m) := by
  rw [isEssNull_iff] at h ⊢
  obtain ⟨θ⟩ := h
  obtain ⟨ζ⟩ := nonempty_zero1_comp (O := O) (a := a) m
  exact ⟨Bicategory.whiskerRightIso θ m ≪≫ ζ⟩

theorem IsEssNull.comp_left {f : b ⟶ c} (h : IsEssNull O f) (e : a ⟶ b) :
    IsEssNull O (e ≫ f) :=
  isEssNull_of_op ((isEssNull_op h).comp e.op)

/-- **Proposition 2.16 `prop2monoreflectsnull`.** Every 2-monomorphism reflects null
morphisms. -/
theorem IsEssNull.of_comp_isTwoMono (m : b ⟶ c) [IsTwoMono m] {f : a ⟶ b}
    (h : IsEssNull O (f ≫ m)) : IsEssNull O f := by
  rw [isEssNull_iff] at h ⊢
  obtain ⟨θ⟩ := h
  obtain ⟨ζ⟩ := nonempty_zero1_comp (O := O) (a := a) m
  exact ⟨IsTwoMono.preimageIso m (θ ≪≫ ζ.symm)⟩

/-- Every 2-epimorphism coreflects null morphisms. -/
theorem IsEssNull.of_comp_isTwoEpi (e : a ⟶ b) [IsTwoEpi e] {f : b ⟶ c}
    (h : IsEssNull O (e ≫ f)) : IsEssNull O f :=
  haveI := isTwoMono_op e
  isEssNull_of_op (IsEssNull.of_comp_isTwoMono e.op (isEssNull_op h))

theorem isEssNull_comp_isTwoMono_iff (m : b ⟶ c) [IsTwoMono m] (f : a ⟶ b) :
    IsEssNull O (f ≫ m) ↔ IsEssNull O f :=
  ⟨IsEssNull.of_comp_isTwoMono m, fun h => h.comp m⟩

theorem isEssNull_isTwoEpi_comp_iff (e : a ⟶ b) [IsTwoEpi e] (f : b ⟶ c) :
    IsEssNull O (e ≫ f) ↔ IsEssNull O f :=
  ⟨IsEssNull.of_comp_isTwoEpi e, fun h => h.comp_left e⟩

end EssNull

section Reflection

/-- **Definition 2.11 `Def Reflects Null`.** A 1-cell `h` **reflects null morphisms** when a
composite ending in `h` is essentially null only if its first factor already is.

The paper's "isomorphic to a null morphism" is `IsEssNull`, which is what the rest of the
development uses. -/
def ReflectsNull (O : B) {b c : B} (h : b ⟶ c) : Prop :=
  ∀ ⦃a : B⦄ (f : a ⟶ b), IsEssNull O (f ≫ h) → IsEssNull O f

/-- The dual condition of Definition 2.11 `Def Reflects Null`: a 1-cell `h` **coreflects null
morphisms** when a composite beginning with `h` is essentially null only if its second factor
already is. -/
def CoreflectsNull (O : B) {a b : B} (h : a ⟶ b) : Prop :=
  ∀ ⦃c : B⦄ (f : b ⟶ c), IsEssNull O (h ≫ f) → IsEssNull O f

section

open Opposite Bicategory.Opposite

omit [Strict B] in
/-- Reflecting and coreflecting null morphisms are dual to one another. -/
theorem coreflectsNull_op {O : B} {a b : B} {h : a ⟶ b} (H : ReflectsNull O h) :
    CoreflectsNull (op O) h.op :=
  fun _ f hf => isEssNull_op (H f.unop (isEssNull_of_op (by simpa using hf)))

omit [Strict B] in
theorem reflectsNull_op {O : B} {a b : B} {h : a ⟶ b} (H : CoreflectsNull O h) :
    ReflectsNull (op O) h.op :=
  fun _ f hf => isEssNull_op (H f.unop (isEssNull_of_op (by simpa using hf)))

end

variable {O : B} [HasBizero O] [IsStrong O] {a b c : B}

/-- **Proposition 2.16 `prop2monoreflectsnull`**, in the language of Definition 2.11
`Def Reflects Null`: a 2-monomorphism reflects null morphisms. -/
theorem IsTwoMono.reflectsNull (m : b ⟶ c) [IsTwoMono m] : ReflectsNull O m :=
  fun _ _ h => IsEssNull.of_comp_isTwoMono m h

/-- Dually, a 2-epimorphism coreflects null morphisms. -/
theorem IsTwoEpi.coreflectsNull (e : a ⟶ b) [IsTwoEpi e] : CoreflectsNull O e :=
  fun _ _ h => IsEssNull.of_comp_isTwoEpi e h

end Reflection

/-- `k : K ⟶ A` is a **2-kernel** of `f : A ⟶ A'`. -/
structure IsTwoKernel (O : B) [HasBizero O] {K A A' : B} (f : A ⟶ A') (k : K ⟶ A) : Prop where
  /-- The composite `k ≫ f` is null. -/
  isEssNull_comp : IsEssNull O (k ≫ f)
  /-- Every 1-cell on which `f` vanishes factors through `k`, up to an invertible 2-cell. -/
  fac {Z : B} (z : Z ⟶ A) (hz : IsEssNull O (z ≫ f)) : ∃ u : Z ⟶ K, Nonempty (u ≫ k ≅ z)
  /-- Whiskering with `k` is bijective on 2-cells. -/
  isTwoMono : IsTwoMono k

/-- `q : A' ⟶ Q` is a **2-cokernel** of `f : A ⟶ A'`. -/
structure IsTwoCokernel (O : B) [HasBizero O] {A A' Q : B} (f : A ⟶ A') (q : A' ⟶ Q) : Prop where
  /-- The composite `f ≫ q` is null. -/
  isEssNull_comp : IsEssNull O (f ≫ q)
  /-- Every 1-cell that kills `f` factors through `q`, up to an invertible 2-cell. -/
  fac {Z : B} (z : A' ⟶ Z) (hz : IsEssNull O (f ≫ z)) : ∃ u : Q ⟶ Z, Nonempty (q ≫ u ≅ z)
  /-- Whiskering with `q` is bijective on 2-cells. -/
  isTwoEpi : IsTwoEpi q

section OppositeKernel

open Opposite Bicategory.Opposite

variable {O : B} [HasBizero O] {K A A' Q : B}

omit [Strict B]

/-- **2-kernels dualise to 2-cokernels.** -/
theorem isTwoCokernel_op {f : A ⟶ A'} {k : K ⟶ A} (h : IsTwoKernel O f k) :
    IsTwoCokernel (op O) f.op k.op where
  isEssNull_comp := isEssNull_op h.isEssNull_comp
  fac z hz := by
    obtain ⟨u, ⟨θ⟩⟩ := h.fac z.unop (isEssNull_of_op (by simpa using hz))
    exact ⟨u.op, ⟨θ.op2⟩⟩
  isTwoEpi := haveI := h.isTwoMono; isTwoEpi_op k

/-- **2-cokernels dualise to 2-kernels.** -/
theorem isTwoKernel_op {f : A ⟶ A'} {q : A' ⟶ Q} (h : IsTwoCokernel O f q) :
    IsTwoKernel (op O) f.op q.op where
  isEssNull_comp := isEssNull_op h.isEssNull_comp
  fac z hz := by
    obtain ⟨u, ⟨θ⟩⟩ := h.fac z.unop (isEssNull_of_op (by simpa using hz))
    exact ⟨u.op, ⟨θ.op2⟩⟩
  isTwoMono := haveI := h.isTwoEpi; isTwoMono_op q

theorem isTwoKernel_of_op {f : A ⟶ A'} {k : K ⟶ A} (h : IsTwoCokernel (op O) f.op k.op) :
    IsTwoKernel O f k where
  isEssNull_comp := isEssNull_of_op (by simpa using h.isEssNull_comp)
  fac z hz := by
    obtain ⟨u, ⟨θ⟩⟩ := h.fac (Z := op _) z.op (by simpa using isEssNull_op hz)
    exact ⟨u.unop, ⟨θ.unop2⟩⟩
  isTwoMono := isTwoMono_of_isTwoEpi_op h.isTwoEpi

theorem isTwoCokernel_of_op {f : A ⟶ A'} {q : A' ⟶ Q} (h : IsTwoKernel (op O) f.op q.op) :
    IsTwoCokernel O f q where
  isEssNull_comp := isEssNull_of_op (by simpa using h.isEssNull_comp)
  fac z hz := by
    obtain ⟨u, ⟨θ⟩⟩ := h.fac (Z := op _) z.op (by simpa using isEssNull_op hz)
    exact ⟨u.unop, ⟨θ.unop2⟩⟩
  isTwoEpi := isTwoEpi_of_isTwoMono_op h.isTwoMono

theorem isTwoCokernel_op_iff {f : A ⟶ A'} {k : K ⟶ A} :
    IsTwoCokernel (op O) f.op k.op ↔ IsTwoKernel O f k :=
  ⟨isTwoKernel_of_op, isTwoCokernel_op⟩

theorem isTwoKernel_op_iff {f : A ⟶ A'} {q : A' ⟶ Q} :
    IsTwoKernel (op O) f.op q.op ↔ IsTwoCokernel O f q :=
  ⟨isTwoCokernel_of_op, isTwoKernel_op⟩

end OppositeKernel

section Kernel

variable {O : B} [HasBizero O] [IsStrong O] {K K' A A' A'' : B}

omit [Strict B] in
/-- The structure 2-cell of a 2-kernel is unique: this is what lets Definition 3.12 `Def:SES`
name one 2-cell for both universal properties. -/
theorem IsTwoKernel.iso_ext {f : A ⟶ A'} {k : K ⟶ A} (α β : k ≫ f ≅ zero1 O K A') : α = β :=
  (isNull_zero1 O K A').iso_ext α β

omit [Strict B] in
theorem IsTwoCokernel.iso_ext {f : A ⟶ A'} {q : A' ⟶ K} (α β : f ≫ q ≅ zero1 O A K) : α = β :=
  (isNull_zero1 O A K).iso_ext α β

omit [Strict B] [IsStrong O] in
/-- A 2-kernel of `f` is a 2-kernel of anything isomorphic to `f`. -/
theorem IsTwoKernel.of_iso {f g : A ⟶ A'} (θ : f ≅ g) {k : K ⟶ A} (h : IsTwoKernel O f k) :
    IsTwoKernel O g k where
  isEssNull_comp := h.isEssNull_comp.of_iso (Bicategory.whiskerLeftIso k θ)
  fac z hz := h.fac z (hz.of_iso (Bicategory.whiskerLeftIso z θ).symm)
  isTwoMono := h.isTwoMono

omit [Strict B] [IsStrong O] in
/-- A 2-cokernel of `f` is a 2-cokernel of anything isomorphic to `f`. -/
theorem IsTwoCokernel.of_iso {f g : A ⟶ A'} (θ : f ≅ g) {q : A' ⟶ K} (h : IsTwoCokernel O f q) :
    IsTwoCokernel O g q :=
  isTwoCokernel_of_op ((isTwoKernel_op h).of_iso θ.op2)

/-- **Proposition 3.9 `CoKernel of Composite`.** Postcomposing with a 2-monomorphism does not
change
the 2-kernel. -/
theorem isTwoKernel_comp_isTwoMono_iff (m : A' ⟶ A'') [IsTwoMono m] {f : A ⟶ A'} {k : K ⟶ A} :
    IsTwoKernel O (f ≫ m) k ↔ IsTwoKernel O f k := by
  have key : ∀ {Z : B} (z : Z ⟶ A), IsEssNull O (z ≫ f ≫ m) ↔ IsEssNull O (z ≫ f) := by
    intro Z z
    rw [← Category.assoc, isEssNull_comp_isTwoMono_iff]
  exact ⟨fun h => ⟨(key k).mp h.isEssNull_comp, fun z hz => h.fac z ((key z).mpr hz), h.isTwoMono⟩,
    fun h => ⟨(key k).mpr h.isEssNull_comp, fun z hz => h.fac z ((key z).mp hz), h.isTwoMono⟩⟩

/-- The dual: precomposing with a 2-epimorphism does not change the 2-cokernel. -/
theorem isTwoCokernel_isTwoEpi_comp_iff (e : A ⟶ A') [IsTwoEpi e] {f : A' ⟶ A''} {q : A'' ⟶ K} :
    IsTwoCokernel O (e ≫ f) q ↔ IsTwoCokernel O f q := by
  haveI := isTwoMono_op e
  rw [← isTwoKernel_op_iff (f := e ≫ f) (q := q), ← isTwoKernel_op_iff (f := f) (q := q)]
  exact isTwoKernel_comp_isTwoMono_iff e.op

/-- **Corollary 2.22 `corollkeruniqueuptoequiv`.** Any two 2-kernels of the same 1-cell are
related by
an equivalence over `A`. -/
noncomputable def IsTwoKernel.equivalence {f : A ⟶ A'} {k : K ⟶ A} {k' : K' ⟶ A}
    (h : IsTwoKernel O f k) (h' : IsTwoKernel O f k') : K' ≌ K :=
  haveI := h.isTwoMono
  haveI := h'.isTwoMono
  let u : K' ⟶ K := (h.fac k' h'.isEssNull_comp).choose
  let θ : u ≫ k ≅ k' := (h.fac k' h'.isEssNull_comp).choose_spec.some
  let u' : K ⟶ K' := (h'.fac k h.isEssNull_comp).choose
  let θ' : u' ≫ k' ≅ k := (h'.fac k h.isEssNull_comp).choose_spec.some
  let e₁ : u' ≫ u ≅ 𝟙 K :=
    IsTwoMono.preimageIso k (eqToIso (Category.assoc u' u k) ≪≫
      Bicategory.whiskerLeftIso u' θ ≪≫ θ' ≪≫ (eqToIso (Category.id_comp k)).symm)
  let e₂ : u ≫ u' ≅ 𝟙 K' :=
    IsTwoMono.preimageIso k' (eqToIso (Category.assoc u u' k') ≪≫
      Bicategory.whiskerLeftIso u θ' ≪≫ θ ≪≫ (eqToIso (Category.id_comp k')).symm)
  Bicategory.Equivalence.mkOfAdjointifyCounit e₂.symm e₁

/-- The dual: any two 2-cokernels of the same 1-cell are related by an equivalence. -/
noncomputable def IsTwoCokernel.equivalence {f : A ⟶ A'} {q : A' ⟶ K} {q' : A' ⟶ K'}
    (h : IsTwoCokernel O f q) (h' : IsTwoCokernel O f q') : K ≌ K' :=
  haveI := h.isTwoEpi
  haveI := h'.isTwoEpi
  let u : K ⟶ K' := (h.fac q' h'.isEssNull_comp).choose
  let θ : q ≫ u ≅ q' := (h.fac q' h'.isEssNull_comp).choose_spec.some
  let u' : K' ⟶ K := (h'.fac q h.isEssNull_comp).choose
  let θ' : q' ≫ u' ≅ q := (h'.fac q h.isEssNull_comp).choose_spec.some
  let e₁ : u ≫ u' ≅ 𝟙 K :=
    IsTwoEpi.preimageIso q ((eqToIso (Category.assoc q u u')).symm ≪≫
      Bicategory.whiskerRightIso θ u' ≪≫ θ' ≪≫ (eqToIso (Category.comp_id q)).symm)
  let e₂ : u' ≫ u ≅ 𝟙 K' :=
    IsTwoEpi.preimageIso q' ((eqToIso (Category.assoc q' u' u)).symm ≪≫
      Bicategory.whiskerRightIso θ' u ≪≫ θ ≪≫ (eqToIso (Category.comp_id q')).symm)
  Bicategory.Equivalence.mkOfAdjointifyCounit e₁.symm e₂

omit [IsStrong O] in
/-- **Non-vacuity.** The identity is a 2-kernel of a null 1-cell. -/
theorem isTwoKernel_id (A A' : B) : IsTwoKernel O (zero1 O A A') (𝟙 A) where
  isEssNull_comp := (isEssNull_zero1 A A').of_iso (eqToIso (Category.id_comp _)).symm
  fac z _ := ⟨z, ⟨eqToIso (Category.comp_id z)⟩⟩
  isTwoMono := isTwoMono_id A

omit [IsStrong O] in
/-- The identity is a 2-cokernel of a null 1-cell. -/
theorem isTwoCokernel_id (A A' : B) : IsTwoCokernel O (zero1 O A A') (𝟙 A') where
  isEssNull_comp := (isEssNull_zero1 A A').of_iso (eqToIso (Category.comp_id _)).symm
  fac z _ := ⟨z, ⟨eqToIso (Category.id_comp z)⟩⟩
  isTwoEpi := isTwoEpi_id A'

end Kernel

end SnakeLean
