/-
Copyright (c) 2026 Elena Caviglia, Luca Mesiti, Tim Van der Linden.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SnakeLean.SnakeConnecting

/-!
# The rows of the third pure configuration

The third and last application of the Pure Snake Lemma in the proof of Theorem 6.9
`Snake General 2D` has rows

```
2-Img(f) ↣ 2-Img(g) ↠ Q          K ↣ 2-Img(g) ↠ 2-Img(h)
```

sharing the middle object `2-Img(g)`, with `Q = C/I` the object constructed in
`SnakeLean.SnakeConnecting`. That the top row is short 2-exact is, in the paper's words, "the
step the paper of record calls a routine verification", and Section 6.11 `SS:Connecting` writes
it out in two halves: Lemma 6.12 `L:ImgMapNormal`, that the comparison `ℓ : 2-Img(f) ↣ 2-Img(g)`
(`j` below) is a normal 2-monomorphism, and Proposition 6.13 `P:RoutineVerification`, that
`π : 2-Img(g) ↠ Q` is its 2-cokernel. This module is both halves, with the paper's proofs.

## The identification

`isTwoCokernel_imgMap` is Proposition 6.13 `P:RoutineVerification`. It is a four-step chase:

1. `2-img(f) ≫ π` is null, because `a ≫ b` is and `2-coim(f)` is a 2-epimorphism.
2. Given `w` killing the comparison, `2-coim(g) ≫ w` kills `a`, so it factors through
   `b = 2-cok(a)` as `v`.
3. `i ≫ v` is null, because `r` is a 2-epimorphism and `2-ker(g) ≫ 2-coim(g)` is null. Here the
   factorisation `2-ker(g) ≫ b ≅ r ≫ i` of the top-left corner of the figure enters, and it is
   the only place where it does.
4. So `v` factors through `2-cok(i) = Q`, and cancelling the 2-epimorphism `2-coim(g)` gives the
   required factorisation through `π`.

**No hypothesis on the ambient 2-category beyond a strong bizero object is used**, and the
paper states the proposition at that cost. The identification needs neither 2-di-exactness nor
homological self-duality, and of the upper row of the ladder only that `b` is a 2-cokernel of
`a` — that `a` is a 2-kernel of `b` is never used. Nor does `i` have to be a normal
2-monomorphism, or `r` a normal 2-epimorphism: plain 2-epimorphy of `r` and of `e = 2-coim(f)`
suffices, which is what Proposition 6.13 asks.

## Why the shortcut is closed, and why it does not matter

The tempting route is to induce `2-Img(g) ↠ Q` and observe that `2-coim(g) ≫ π ≅ b ≫ 2-coker(i)`
exhibits it as a composite of two normal 2-epimorphisms. That would make `π` a normal
2-epimorphism, and its 2-kernel would be the top row — but only if normal 2-epimorphisms were
closed under composition, which 2-di-exactness does *not* give. The paper adds that closure by
hand wherever it needs it, most visibly as Definition 9.4 `Def:NEC`, the second standing
hypothesis of the non-self-dual Snake Lemma.

The chase above avoids the question entirely. It never asks whether `π` is a *normal* 2-epi; it
verifies the universal property of the 2-cokernel directly, and normality of the top row's
2-monomorphism comes from elsewhere — see `isNormalMono_imgMap`.

## Normality of the comparison

`isNormalMono_imgMap` is Lemma 6.12 `L:ImgMapNormal`, by the paper's proof: the appeal to the
second assertion of Proposition 3.22 `Image Factorisation of Normal Map is Unique`. The 1-cell
whose image factorisation is being compared is `a ≫ 2-coim(g)`, and the point is that it is a
normal 2-monomorphism followed by a normal 2-epimorphism, hence *antinormal*, hence normal by
(DI2). Its two factorisations are then its normal one and `2-coim(f) ≫ j`, so `j` is a normal
2-monomorphism — and `2-coim(f)` is a normal 2-epimorphism into the bargain, the lemma's second
clause. This is the second place in the snake construction where (DI2) is used, the first being
`snakeTop`.

## Main results

* `isTwoCokernel_imgMap` — Proposition 6.13 `P:RoutineVerification`, the identification of
  `2-Cok(2-Img(f) ↣ 2-Img(g))` with `Q`.
* `isNormalMono_imgMap` — Lemma 6.12 `L:ImgMapNormal`, the comparison is a normal
  2-monomorphism and `2-coim(f)` a normal 2-epimorphism.
* `isSES_imgRow` — the top row is short 2-exact.
* `isTwoKernel_imgMapDual`, `isNormalEpi_imgMapDual`, `isSES_imgRowDual` — the bottom row, which
  the paper obtains by saying "the bottom row is short 2-exact by duality". Here that is
  literal: each is its primal form read in `Bᵒᵖ`.
-/

universe w v u

namespace SnakeLean

open CategoryTheory Bicategory Opposite

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.Strict B]

section Quotient

variable {O : B} [HasBizero O] [IsStrong O]

/-- **Proposition 6.13 `P:RoutineVerification`.** The comparison `j : 2-Img(f) ⟶ 2-Img(g)`
(the paper's `ℓ`) has 2-cokernel `π`, whose codomain is the object `Q = C/I` of Figure
1 `Fig Constructing Snake`. The proof is the paper's.

The data is that figure, in hypothesis form: `b` is the 2-cokernel of `a`, the composite
`2-ker(g) ≫ b` factors as `r ≫ i`, `qi` is `2-coker(i)`, `eg` is `2-coim(g)`, `ef` is
`2-coim(f)`, and the two squares `ψj`, `ψπ` say that `j` and `π` are the induced comparisons. -/
theorem isTwoCokernel_imgMap {A M C KG I IF IG Q : B}
    {a : A ⟶ M} {b : M ⟶ C} (hab : IsTwoCokernel O a b)
    {kg : KG ⟶ M} {r : KG ⟶ I} [IsTwoEpi r] {i : I ⟶ C} (θ : kg ≫ b ≅ r ≫ i)
    {qi : C ⟶ Q} (hqi : IsTwoCokernel O i qi)
    {eg : M ⟶ IG} (heg : IsTwoCokernel O kg eg)
    {ef : A ⟶ IF} [IsTwoEpi ef] {j : IF ⟶ IG} {π : IG ⟶ Q}
    (ψj : ef ≫ j ≅ a ≫ eg) (ψπ : eg ≫ π ≅ b ≫ qi) :
    IsTwoCokernel O j π := by
  haveI : IsTwoEpi eg := heg.isTwoEpi
  haveI : IsTwoEpi b := hab.isTwoEpi
  haveI : IsTwoEpi qi := hqi.isTwoEpi
  refine ⟨?_, ?_, isTwoEpi_of_comp ψπ.symm⟩
  · -- Step 1: `j ≫ π` is null, because `a ≫ b` is and `ef` is a 2-epimorphism.
    refine IsEssNull.of_comp_isTwoEpi ef ((hab.isEssNull_comp.comp qi).of_iso ?_)
    exact eqToIso (Category.assoc a b qi) ≪≫ Bicategory.whiskerLeftIso a ψπ.symm ≪≫
      (eqToIso (Category.assoc a eg π)).symm ≪≫ Bicategory.whiskerRightIso ψj.symm π ≪≫
      eqToIso (Category.assoc ef j π)
  · intro W w hw
    -- Step 2: `eg ≫ w` kills `a`, so it factors through `b = 2-cok(a)`.
    have h1 : IsEssNull O (a ≫ eg ≫ w) := (hw.comp_left ef).of_iso
      ((eqToIso (Category.assoc ef j w)).symm ≪≫ Bicategory.whiskerRightIso ψj w ≪≫
        eqToIso (Category.assoc a eg w))
    obtain ⟨v, ⟨γ⟩⟩ := hab.fac (eg ≫ w) h1
    -- Step 3: `i ≫ v` is null, by cancelling the 2-epimorphism `r`.
    have h2 : IsEssNull O (i ≫ v) := IsEssNull.of_comp_isTwoEpi r
      ((heg.isEssNull_comp.comp w).of_iso
        (eqToIso (Category.assoc kg eg w) ≪≫ Bicategory.whiskerLeftIso kg γ.symm ≪≫
          (eqToIso (Category.assoc kg b v)).symm ≪≫ Bicategory.whiskerRightIso θ v ≪≫
          eqToIso (Category.assoc r i v)))
    -- Step 4: so `v` factors through `qi`, and `eg` cancels.
    obtain ⟨w', ⟨δ⟩⟩ := hqi.fac v h2
    refine ⟨w', ⟨IsTwoEpi.preimageIso eg ?_⟩⟩
    exact (eqToIso (Category.assoc eg π w')).symm ≪≫ Bicategory.whiskerRightIso ψπ w' ≪≫
      eqToIso (Category.assoc b qi w') ≪≫ Bicategory.whiskerLeftIso b δ ≪≫ γ

omit [Strict B] in
/-- The comparison `j` is a 2-monomorphism, because `j ≫ 2-img(g) ≅ 2-img(f) ≫ c` is one. -/
theorem isTwoMono_imgMap {X Y IF IG : B} {mf : IF ⟶ X} {c : X ⟶ Y} {mg : IG ⟶ Y} [IsTwoMono mf]
    [IsTwoMono c] [IsTwoMono mg] {j : IF ⟶ IG} (ψ : j ≫ mg ≅ mf ≫ c) : IsTwoMono j :=
  isTwoMono_of_comp ψ.symm

variable [TwoDiExact O] [TwoZExact O]

/-- **Lemma 6.12 `L:ImgMapNormal`: `j` is a normal 2-monomorphism.** The proof is the paper's,
by the second assertion of Proposition 3.22 `Image Factorisation of Normal Map is Unique`: the
1-cell being factorised is `a ≫ 2-coim(g)`, which is antinormal and hence normal by (DI2).
Comparing its normal image factorisation with `2-coim(f) ≫ j` makes `2-coim(f)` a normal
2-epimorphism and `j` a normal 2-monomorphism. -/
theorem isNormalMono_imgMap {A M IF IG : B} {a : A ⟶ M} (ha : IsNormalMono O a)
    {eg : M ⟶ IG} (heg : IsNormalEpi O eg) {ef : A ⟶ IF} [IsTwoEpi ef] {j : IF ⟶ IG}
    [IsTwoMono j] (ψj : ef ≫ j ≅ a ≫ eg) : IsNormalEpi O ef ∧ IsNormalMono O j := by
  obtain ⟨_, e, m, he, hm, ⟨θ⟩⟩ := isNormal_of_normalMono_comp_normalEpi ha heg
  exact isNormal_of_factorisation θ ψj.symm he hm (isTwoKernel_twoKernel O (a ≫ eg))

/-- **The top row of the third pure configuration is short 2-exact.** Lemma 6.12 and
Proposition 6.13 together, as the paragraph after Proposition 6.13 `P:RoutineVerification`
assembles them. -/
theorem isSES_imgRow {A M C KG I IF IG Q : B}
    {a : A ⟶ M} {b : M ⟶ C} (hab : IsSES O a b)
    {kg : KG ⟶ M} {r : KG ⟶ I} [IsTwoEpi r] {i : I ⟶ C} (θ : kg ≫ b ≅ r ≫ i)
    {qi : C ⟶ Q} (hqi : IsTwoCokernel O i qi)
    {eg : M ⟶ IG} (heg : IsTwoCokernel O kg eg)
    {ef : A ⟶ IF} [IsTwoEpi ef] {j : IF ⟶ IG} [IsTwoMono j] {π : IG ⟶ Q}
    (ψj : ef ≫ j ≅ a ≫ eg) (ψπ : eg ≫ π ≅ b ≫ qi) :
    IsSES O j π := by
  obtain ⟨_, ℓ, hℓ⟩ :=
    (isNormalMono_imgMap ⟨_, b, hab.isTwoKernel⟩ ⟨_, kg, heg⟩ ψj).2
  exact isSES_of_isTwoKernel hℓ (isTwoCokernel_imgMap hab.isTwoCokernel θ hqi heg ψj ψπ)

end Quotient

section Dual

variable {O : B} [HasBizero O] [IsStrong O]

/-- **The bottom row's 2-kernel**, the dual of `isTwoCokernel_imgMap`, obtained by transport
through `Bᵒᵖ`. Read in `B`: `c` is the 2-kernel of `d`, the composite `c ≫ 2-coker(g)` factors as
`σ ≫ u` (the bottom-left corner of Figure 1 `Fig Constructing Snake`), `κ` is `2-ker(σ)`, `mg` is
`2-img(g)` and `mf` is `2-img(h)`; then the comparison `kK : K ⟶ 2-Img(g)` is a 2-kernel of the
induced `dBar : 2-Img(g) ⟶ 2-Img(h)`. -/
theorem isTwoKernel_imgMapDual {X Y Z QG J KK IF IG : B}
    {d : Y ⟶ Z} {c : X ⟶ Y} (hcd : IsTwoKernel O d c)
    {qg : Y ⟶ QG} {u : J ⟶ QG} [IsTwoMono u] {σ : X ⟶ J} (θ : c ≫ qg ≅ σ ≫ u)
    {κ : KK ⟶ X} (hκ : IsTwoKernel O σ κ)
    {mg : IG ⟶ Y} (hmg : IsTwoKernel O qg mg)
    {mf : IF ⟶ Z} [IsTwoMono mf] {dBar : IG ⟶ IF} {kK : KK ⟶ IG}
    (ψj : dBar ≫ mf ≅ mg ≫ d) (ψπ : kK ≫ mg ≅ κ ≫ c) :
    IsTwoKernel O dBar kK := by
  haveI : IsTwoEpi u.op := isTwoEpi_op u
  haveI : IsTwoEpi mf.op := isTwoEpi_op mf
  exact isTwoKernel_of_op (isTwoCokernel_imgMap (r := u.op) (ef := mf.op)
    (isTwoCokernel_op hcd) θ.op2 (isTwoCokernel_op hκ) (isTwoCokernel_op hmg) ψj.op2 ψπ.op2)

variable [TwoDiExact O] [TwoZExact O]

/-- The dual of `isNormalMono_imgMap`: `dBar` is a normal 2-epimorphism. -/
theorem isNormalEpi_imgMapDual {Y Z IF IG : B} {d : Y ⟶ Z} (hd : IsNormalEpi O d)
    {mg : IG ⟶ Y} (hmg : IsNormalMono O mg) {mf : IF ⟶ Z} [IsTwoMono mf] {dBar : IG ⟶ IF}
    [IsTwoEpi dBar] (ψj : dBar ≫ mf ≅ mg ≫ d) : IsNormalMono O mf ∧ IsNormalEpi O dBar := by
  haveI : IsTwoEpi mf.op := isTwoEpi_op mf
  haveI : IsTwoMono dBar.op := isTwoMono_op dBar
  obtain ⟨h1, h2⟩ := isNormalMono_imgMap (O := op O) (isNormalMono_op hd) (isNormalEpi_op hmg)
    (ef := mf.op) (j := dBar.op) ψj.op2
  exact ⟨isNormalMono_of_op h1, isNormalEpi_of_op h2⟩

/-- **The bottom row of the third pure configuration is short 2-exact**, which the paper records
as "the bottom row is short 2-exact by duality". -/
theorem isSES_imgRowDual {X Y Z QG J KK IF IG : B}
    {d : Y ⟶ Z} {c : X ⟶ Y} (hcd : IsSES O c d)
    {qg : Y ⟶ QG} {u : J ⟶ QG} [IsTwoMono u] {σ : X ⟶ J} (θ : c ≫ qg ≅ σ ≫ u)
    {κ : KK ⟶ X} (hκ : IsTwoKernel O σ κ)
    {mg : IG ⟶ Y} (hmg : IsTwoKernel O qg mg)
    {mf : IF ⟶ Z} [IsTwoMono mf] {dBar : IG ⟶ IF} [IsTwoEpi dBar] {kK : KK ⟶ IG}
    (ψj : dBar ≫ mf ≅ mg ≫ d) (ψπ : kK ≫ mg ≅ κ ≫ c) :
    IsSES O kK dBar := by
  haveI : IsTwoEpi u.op := isTwoEpi_op u
  haveI : IsTwoEpi mf.op := isTwoEpi_op mf
  haveI : IsTwoMono dBar.op := isTwoMono_op dBar
  exact isSES_of_op (isSES_imgRow (r := u.op) (ef := mf.op) (isSES_op hcd) θ.op2
    (isTwoCokernel_op hκ) (isTwoCokernel_op hmg) ψj.op2 ψπ.op2)

end Dual

end SnakeLean
