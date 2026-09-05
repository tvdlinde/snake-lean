/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.FiveLemma

/-!
# 2-z-exactness and chosen 2-kernels

This module introduces Definition 3.2 `Def ZExact`, a **2-z-exact 2-category**: a
2-category with a strong bizero object that has all 2-kernels and all 2-cokernels. Sections 2 and
3 were formalised without it, each result taking as an explicit hypothesis the one 2-kernel or
2-cokernel named in its own statement. Section 4 forces the change: the coimage
`2-Coim(f) = 2-Cok(2-ker(f))` and the image `2-Img(f) = 2-Ker(2-cok(f))` cannot even be *written*
without a choice of 2-kernel and 2-cokernel for every 1-cell.

## What is separated from what

The paper bundles three things into 2-z-exactness: a bizero object, its strongness, and the
existence of all 2-kernels and 2-cokernels. They are kept apart here — `HasBizero O`,
`IsStrong O` and `TwoZExact O` — so that the linter keeps reporting which of the three each
result actually consumes. So far the answer has been informative: see the wrappers at the end of
this module, none of which needs `TwoZExact`.

## Chosen 2-kernels

`HasTwoKernel O f` is a `Prop`-valued class wrapping the existence statement, and `twoKernelObj`,
`twoKernel` choose a witness. The choice is genuine — `Classical.choice` becomes load-bearing
here for the first time in this development, rather than incidental — but it is harmless: any two
2-kernels of the same 1-cell are related by an equivalence over the codomain, which is
`IsTwoKernel.exists_isEquiv1`, a restatement of Corollary 2.22 `corollkeruniqueuptoequiv` in the
form
the results downstream consume.

## Chosen 2-kernels

The paper writes `2-Ker(f)` for the object and `2-ker(f)` for the 1-cell, a notation it notes is
unambiguous up to equivalence by Corollary 2.22 `corollkeruniqueuptoequiv`. Here a 2-kernel is
chosen once, by `twoKernel`, and every statement below is either invariant under
`IsTwoKernel.exists_isEquiv1` or is proved from the hypothesis form rather than from the chosen
2-kernel.

## Main definitions

* `HasTwoKernel`, `HasTwoCokernel`, and the choice operators `twoKernelObj`, `twoKernel`,
  `twoCokernelObj`, `twoCokernel`.
* `TwoZExact` — all 2-kernels and all 2-cokernels exist.
* `twoCoim` and `twoImg` — the normal image factorisation of Section 3.21
  `SS:ImageFactorisation`, in the notation of Lemma 4.2 `Normal Iff Comparison Iso`.

## Not formalised

The comparison 1-cell `j_f` and Lemma 4.2 `Normal Iff Comparison Iso` are in
`SnakeLean.Comparison`.
Nothing here asserts that the two chosen 2-kernels of a 1-cell and of an isomorphic 1-cell are
*equal*; they are only equivalent, and that is all the paper needs.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- `f` **has a 2-kernel**. -/
class HasTwoKernel (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A') : Prop where
  /-- Some 1-cell into `A` is a 2-kernel of `f`. -/
  exists_isTwoKernel : ∃ (K : B) (k : K ⟶ A), IsTwoKernel O f k

/-- `f` **has a 2-cokernel**. -/
class HasTwoCokernel (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A') : Prop where
  /-- Some 1-cell out of `A'` is a 2-cokernel of `f`. -/
  exists_isTwoCokernel : ∃ (Q : B) (q : A' ⟶ Q), IsTwoCokernel O f q

/-- A 2-category is **2-z-exact** when every 1-cell has a 2-kernel and a 2-cokernel.

Definition 3.2 `Def ZExact` asks in addition for a strong bizero object; that is
`HasBizero O` together with `IsStrong O`, and is kept separate here. -/
class TwoZExact (O : B) [HasBizero O] : Prop where
  /-- Every 1-cell has a 2-kernel. -/
  hasTwoKernel {A A' : B} (f : A ⟶ A') : HasTwoKernel O f
  /-- Every 1-cell has a 2-cokernel. -/
  hasTwoCokernel {A A' : B} (f : A ⟶ A') : HasTwoCokernel O f

instance (priority := 100) TwoZExact.toHasTwoKernel {O : B} [HasBizero O] [h : TwoZExact O]
    {A A' : B} (f : A ⟶ A') : HasTwoKernel O f :=
  h.hasTwoKernel f

instance (priority := 100) TwoZExact.toHasTwoCokernel {O : B} [HasBizero O] [h : TwoZExact O]
    {A A' : B} (f : A ⟶ A') : HasTwoCokernel O f :=
  h.hasTwoCokernel f

section Choice

variable {O : B} [HasBizero O] {K A A' Q : B}

theorem IsTwoKernel.hasTwoKernel {f : A ⟶ A'} {k : K ⟶ A} (h : IsTwoKernel O f k) :
    HasTwoKernel O f :=
  ⟨K, k, h⟩

theorem IsTwoCokernel.hasTwoCokernel {f : A ⟶ A'} {q : A' ⟶ Q} (h : IsTwoCokernel O f q) :
    HasTwoCokernel O f :=
  ⟨Q, q, h⟩

/-- The chosen 2-kernel object of `f`, written `2-Ker(f)` in the paper. -/
noncomputable def twoKernelObj (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A')
    [h : HasTwoKernel O f] : B :=
  h.exists_isTwoKernel.choose

/-- The chosen 2-kernel of `f`, written `2-ker(f)` in the paper. -/
noncomputable def twoKernel (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A')
    [h : HasTwoKernel O f] : twoKernelObj O f ⟶ A :=
  h.exists_isTwoKernel.choose_spec.choose

theorem isTwoKernel_twoKernel (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A')
    [h : HasTwoKernel O f] : IsTwoKernel O f (twoKernel O f) :=
  h.exists_isTwoKernel.choose_spec.choose_spec

/-- The chosen 2-cokernel object of `f`, written `2-Cok(f)` in the paper. -/
noncomputable def twoCokernelObj (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A')
    [h : HasTwoCokernel O f] : B :=
  h.exists_isTwoCokernel.choose

/-- The chosen 2-cokernel of `f`, written `2-cok(f)` in the paper. -/
noncomputable def twoCokernel (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A')
    [h : HasTwoCokernel O f] : A' ⟶ twoCokernelObj O f :=
  h.exists_isTwoCokernel.choose_spec.choose

theorem isTwoCokernel_twoCokernel (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A')
    [h : HasTwoCokernel O f] : IsTwoCokernel O f (twoCokernel O f) :=
  h.exists_isTwoCokernel.choose_spec.choose_spec

instance isTwoMono_twoKernel (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A') [HasTwoKernel O f] :
    IsTwoMono (twoKernel O f) :=
  (isTwoKernel_twoKernel O f).isTwoMono

instance isTwoEpi_twoCokernel (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A')
    [HasTwoCokernel O f] : IsTwoEpi (twoCokernel O f) :=
  (isTwoCokernel_twoCokernel O f).isTwoEpi

theorem isNormalMono_twoKernel (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A')
    [HasTwoKernel O f] : IsNormalMono O (twoKernel O f) :=
  ⟨A', f, isTwoKernel_twoKernel O f⟩

theorem isNormalEpi_twoCokernel (O : B) [HasBizero O] {A A' : B} (f : A ⟶ A')
    [HasTwoCokernel O f] : IsNormalEpi O (twoCokernel O f) :=
  ⟨A, f, isTwoCokernel_twoCokernel O f⟩

end Choice

section OppositeZExact

open Opposite Bicategory.Opposite

variable {O : B} [HasBizero O]

/-- 2-z-exactness is self-dual. -/
instance twoZExactOp [TwoZExact O] : TwoZExact (op O) where
  hasTwoKernel f := ⟨_, (twoCokernel O f.unop).op,
    isTwoKernel_op (isTwoCokernel_twoCokernel O f.unop)⟩
  hasTwoCokernel f := ⟨_, (twoKernel O f.unop).op,
    isTwoCokernel_op (isTwoKernel_twoKernel O f.unop)⟩

end OppositeZExact

section Transport

open Opposite Bicategory.Opposite

variable [Bicategory.Strict B] {O : B} [HasBizero O] {K K' A A' Q Q' : B}

/-- **Corollary 2.22 `corollkeruniqueuptoequiv`, in the form used downstream.** Any two 2-kernels
of
the same 1-cell are related by an equivalence commuting with the two 2-kernel 1-cells.

`IsTwoKernel.equivalence` packages the same data as a `Bicategory.Equivalence`; this version
keeps the comparison 1-cell and its compatibility 2-cell in reach, which is what the arguments of
Section 4 need. Neither version uses the bizero object's strongness. -/
theorem IsTwoKernel.exists_isEquiv1 {f : A ⟶ A'} {k : K ⟶ A} {k' : K' ⟶ A}
    (h : IsTwoKernel O f k) (h' : IsTwoKernel O f k') :
    ∃ u : K' ⟶ K, IsEquiv1 u ∧ Nonempty (u ≫ k ≅ k') := by
  haveI := h.isTwoMono
  haveI := h'.isTwoMono
  obtain ⟨u, ⟨θ⟩⟩ := h.fac k' h'.isEssNull_comp
  obtain ⟨u', ⟨θ'⟩⟩ := h'.fac k h.isEssNull_comp
  have e₁ : u' ≫ u ≅ 𝟙 K :=
    IsTwoMono.preimageIso k (eqToIso (Category.assoc u' u k) ≪≫
      Bicategory.whiskerLeftIso u' θ ≪≫ θ' ≪≫ (eqToIso (Category.id_comp k)).symm)
  have e₂ : u ≫ u' ≅ 𝟙 K' :=
    IsTwoMono.preimageIso k' (eqToIso (Category.assoc u u' k') ≪≫
      Bicategory.whiskerLeftIso u θ' ≪≫ θ ≪≫ (eqToIso (Category.id_comp k')).symm)
  exact ⟨u, ⟨u', ⟨e₂⟩, ⟨e₁⟩⟩, ⟨θ⟩⟩

/-- The dual: any two 2-cokernels of the same 1-cell are related by an equivalence. -/
theorem IsTwoCokernel.exists_isEquiv1 {f : A ⟶ A'} {q : A' ⟶ Q} {q' : A' ⟶ Q'}
    (h : IsTwoCokernel O f q) (h' : IsTwoCokernel O f q') :
    ∃ u : Q ⟶ Q', IsEquiv1 u ∧ Nonempty (q ≫ u ≅ q') := by
  obtain ⟨u, hu, ⟨θ⟩⟩ := (isTwoKernel_op h).exists_isEquiv1 (isTwoKernel_op h')
  exact ⟨u.unop, isEquiv1_of_op hu, ⟨θ.unop2⟩⟩

/-- Every 2-kernel of `f` is equivalent to the chosen one. -/
theorem IsTwoKernel.exists_isEquiv1_twoKernel {f : A ⟶ A'} [HasTwoKernel O f] {k : K ⟶ A}
    (h : IsTwoKernel O f k) :
    ∃ u : K ⟶ twoKernelObj O f, IsEquiv1 u ∧ Nonempty (u ≫ twoKernel O f ≅ k) :=
  (isTwoKernel_twoKernel O f).exists_isEquiv1 h

/-- Every 2-cokernel of `f` is equivalent to the chosen one. -/
theorem IsTwoCokernel.exists_isEquiv1_twoCokernel {f : A ⟶ A'} [HasTwoCokernel O f] {q : A' ⟶ Q}
    (h : IsTwoCokernel O f q) :
    ∃ u : twoCokernelObj O f ⟶ Q, IsEquiv1 u ∧ Nonempty (twoCokernel O f ≫ u ≅ q) :=
  (isTwoCokernel_twoCokernel O f).exists_isEquiv1 h

/-- **Non-vacuity.** A null 1-cell has a 2-kernel, namely the identity. -/
theorem hasTwoKernel_zero1 (A A' : B) : HasTwoKernel O (zero1 O A A') :=
  (isTwoKernel_id (O := O) A A').hasTwoKernel

/-- A null 1-cell has a 2-cokernel, namely the identity. -/
theorem hasTwoCokernel_zero1 (A A' : B) : HasTwoCokernel O (zero1 O A A') :=
  (isTwoCokernel_id (O := O) A A').hasTwoCokernel

end Transport

section SESForms

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {K A A' Q : B}

/-- A normal 2-monomorphism, together with its chosen 2-cokernel, is a short 2-exact sequence. -/
theorem isSES_twoCokernel {f : A ⟶ A'} {k : K ⟶ A} (hk : IsTwoKernel O f k)
    [HasTwoCokernel O k] : IsSES O k (twoCokernel O k) :=
  isSES_of_isTwoKernel hk (isTwoCokernel_twoCokernel O k)

/-- A normal 2-epimorphism, together with its chosen 2-kernel, is a short 2-exact sequence. -/
theorem isSES_twoKernel {f : A ⟶ A'} {q : A' ⟶ Q} (hq : IsTwoCokernel O f q)
    [HasTwoKernel O q] : IsSES O (twoKernel O q) q :=
  isSES_of_isTwoCokernel hq (isTwoKernel_twoKernel O q)

end SESForms

section CoimImg

variable {O : B} [HasBizero O] [TwoZExact O] {A A' : B}

/-- The **2-coimage** object of `f`: the 2-cokernel object of its 2-kernel. -/
noncomputable def twoCoimObj (O : B) [HasBizero O] [TwoZExact O] {A A' : B} (f : A ⟶ A') : B :=
  twoCokernelObj O (twoKernel O f)

/-- The **2-coimage** of `f`, written `2-coim(f)` in the paper. -/
noncomputable def twoCoim (O : B) [HasBizero O] [TwoZExact O] {A A' : B} (f : A ⟶ A') :
    A ⟶ twoCoimObj O f :=
  twoCokernel O (twoKernel O f)

/-- The **2-image** object of `f`: the 2-kernel object of its 2-cokernel. -/
noncomputable def twoImgObj (O : B) [HasBizero O] [TwoZExact O] {A A' : B} (f : A ⟶ A') : B :=
  twoKernelObj O (twoCokernel O f)

/-- The **2-image** of `f`, written `2-img(f)` in the paper. -/
noncomputable def twoImg (O : B) [HasBizero O] [TwoZExact O] {A A' : B} (f : A ⟶ A') :
    twoImgObj O f ⟶ A' :=
  twoKernel O (twoCokernel O f)

theorem isTwoCokernel_twoCoim (f : A ⟶ A') : IsTwoCokernel O (twoKernel O f) (twoCoim O f) :=
  isTwoCokernel_twoCokernel O (twoKernel O f)

theorem isTwoKernel_twoImg (f : A ⟶ A') : IsTwoKernel O (twoCokernel O f) (twoImg O f) :=
  isTwoKernel_twoKernel O (twoCokernel O f)

instance isTwoEpi_twoCoim (f : A ⟶ A') : IsTwoEpi (twoCoim O f) :=
  (isTwoCokernel_twoCoim f).isTwoEpi

instance isTwoMono_twoImg (f : A ⟶ A') : IsTwoMono (twoImg O f) :=
  (isTwoKernel_twoImg f).isTwoMono

/-- The 2-coimage of `f` is a normal 2-epimorphism. -/
theorem isNormalEpi_twoCoim (f : A ⟶ A') : IsNormalEpi O (twoCoim O f) :=
  ⟨_, _, isTwoCokernel_twoCoim f⟩

/-- The 2-image of `f` is a normal 2-monomorphism. -/
theorem isNormalMono_twoImg (f : A ⟶ A') : IsNormalMono O (twoImg O f) :=
  ⟨_, _, isTwoKernel_twoImg f⟩

end CoimImg

section CoimImgSES

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] [TwoZExact O] {A A' : B}

/-- The 2-kernel and the 2-coimage of `f` form a short 2-exact sequence. -/
theorem isSES_twoCoim (f : A ⟶ A') : IsSES O (twoKernel O f) (twoCoim O f) :=
  isSES_of_isTwoKernel (isTwoKernel_twoKernel O f) (isTwoCokernel_twoCoim f)

/-- The 2-image and the 2-cokernel of `f` form a short 2-exact sequence. -/
theorem isSES_twoImg (f : A ⟶ A') : IsSES O (twoImg O f) (twoCokernel O f) :=
  isSES_of_isTwoCokernel (isTwoCokernel_twoCokernel O f) (isTwoKernel_twoImg f)

end CoimImgSES

section Wrappers

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {X Y K I I' A A' Q : B}

/-- Choice form of `SnakeLean.isNormalMono_iff`. -/
theorem isNormalMono_iff' (f : A ⟶ Y) [HasTwoKernel O f] :
    IsNormalMono O f ↔ IsTwoMono f ∧ IsNormal O f :=
  isNormalMono_iff (isTwoKernel_twoKernel O f)

/-- Choice form of `SnakeLean.isNormalEpi_iff`. -/
theorem isNormalEpi_iff' (f : X ⟶ A) [HasTwoCokernel O f] :
    IsNormalEpi O f ↔ IsTwoEpi f ∧ IsNormal O f :=
  isNormalEpi_iff (isTwoCokernel_twoCokernel O f)

/-- Choice form of `SnakeLean.IsTwoKernel.isTrivial_of_isTwoMono`, which is Lemma 2.24
`2-Mono Trivial Kernel`. -/
theorem isTrivial_twoKernelObj (m : A ⟶ A') [IsTwoMono m] [HasTwoKernel O m] :
    IsTrivial O (twoKernelObj O m) :=
  (isTwoKernel_twoKernel O m).isTrivial_of_isTwoMono

/-- Choice form of `SnakeLean.IsTwoCokernel.isTrivial_of_isTwoEpi`. -/
theorem isTrivial_twoCokernelObj (e : A ⟶ A') [IsTwoEpi e] [HasTwoCokernel O e] :
    IsTrivial O (twoCokernelObj O e) :=
  (isTwoCokernel_twoCokernel O e).isTrivial_of_isTwoEpi

/-- Choice form of Proposition 3.22 `Image Factorisation of Normal Map is Unique`. -/
theorem imageFactorisation_unique' {f : A ⟶ A'} {e : A ⟶ I} {m : I ⟶ A'} {e' : A ⟶ I'}
    {m' : I' ⟶ A'} (θ : f ≅ e ≫ m) (θ' : f ≅ e' ≫ m') (he : IsNormalEpi O e)
    (hm : IsNormalMono O m) [IsTwoEpi e'] [IsTwoMono m'] [HasTwoKernel O f] :
    ∃ t : I ⟶ I', IsEquiv1 t ∧ Nonempty (e ≫ t ≅ e') ∧ Nonempty (t ≫ m' ≅ m) :=
  imageFactorisation_unique θ θ' he hm (isTwoKernel_twoKernel O f)

/-- Choice form of Proposition 3.20 `Normal Equivalence Trivial`: a normal 1-cell is an
equivalence exactly when its 2-kernel and its 2-cokernel are trivial. -/
theorem isEquiv1_iff_isTrivial' {f : A ⟶ A'} {e : A ⟶ I} {m : I ⟶ A'} (θ : f ≅ e ≫ m)
    (he : IsNormalEpi O e) (hm : IsNormalMono O m) [HasTwoKernel O f] [HasTwoCokernel O f] :
    IsEquiv1 f ↔ IsTrivial O (twoKernelObj O f) ∧ IsTrivial O (twoCokernelObj O f) :=
  isEquiv1_iff_isTrivial θ he hm (isTwoKernel_twoKernel O f) (isTwoCokernel_twoCokernel O f)

end Wrappers

section NSFL

variable [Bicategory.Strict B] {O : B} [HasBizero O] [IsStrong O] {K' A' Q' K A Q : B}
  {k' : K' ⟶ A'} {q' : A' ⟶ Q'} {k : K ⟶ A} {q : A ⟶ Q}

/-- **Theorem 3.28 `NSFL`(1)** as the paper states it: for a morphism of short 2-exact sequences
whose
outer verticals are 2-monomorphisms and whose middle vertical is normal, the middle vertical is a
normal 2-monomorphism. -/
theorem nsfl_isNormalMono' (S : MorphismSES k' q' k q) (h' : IsSES O k' q') (h : IsSES O k q)
    [HasTwoKernel O S.g] (hf : IsTwoMono S.f) (hh : IsTwoMono S.h) (hg : IsNormal O S.g) :
    IsNormalMono O S.g :=
  nsfl_isNormalMono S h'.isTwoKernel h.isTwoKernel hf hh hg (isTwoKernel_twoKernel O S.g)

/-- **Theorem 3.28 `NSFL`(2)** as the paper states it. -/
theorem nsfl_isNormalEpi' (S : MorphismSES k' q' k q) (h' : IsSES O k' q') (h : IsSES O k q)
    [HasTwoCokernel O S.g] (hf : IsTwoEpi S.f) (hh : IsTwoEpi S.h) (hg : IsNormal O S.g) :
    IsNormalEpi O S.g :=
  nsfl_isNormalEpi S h'.isTwoCokernel h.isTwoCokernel hf hh hg (isTwoCokernel_twoCokernel O S.g)

/-- **Theorem 3.28 `NSFL`(3)** as the paper states it. -/
theorem nsfl_isEquiv1' (S : MorphismSES k' q' k q) (h' : IsSES O k' q') (h : IsSES O k q)
    [HasTwoKernel O S.g] [HasTwoCokernel O S.g] (hf : IsEquiv1 S.f) (hh : IsEquiv1 S.h)
    (hg : IsNormal O S.g) : IsEquiv1 S.g :=
  nsfl_isEquiv1 S h'.isTwoKernel h.isTwoKernel h'.isTwoCokernel h.isTwoCokernel hf hh hg
    (isTwoKernel_twoKernel O S.g) (isTwoCokernel_twoCokernel O S.g)

end NSFL

end SnakeLean
