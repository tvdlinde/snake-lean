# A two-categorical Snake Lemma — Lean formalisation

Machine-checked companions, in Lean 4 with Mathlib, to results from

> E. Caviglia, L. Mesiti and T. Van der Linden,
> *A two-categorical Snake Lemma*.

The paper does homological algebra in a 2-category with a strong bizero object: 2-kernels and
2-cokernels, 2-monomorphisms and 2-epimorphisms as (co)fully faithful 1-cells, short 2-exact
sequences and normal image factorisations; from there the Pure Snake Lemma, the Snake Lemma in a
2-di-exact 2-category and its 2-naturality; three models; and a second Snake Lemma resting on two
hypotheses that are not self-dual.

This repository is **supplementary**. The paper stands on its own and makes no formalisation
claims; these files exist to stress-test its proofs. Nothing here is required for the paper,
which points to it once, from the introduction.

Everything below refers to the paper and to nothing else. Results are given by their number and,
in backticks, by the internal name they carry in the source — the paper has been renumbered once
already, and the names survived it where the numbers did not.

## Contents

- [What Mathlib supplies, and what it does not](#what-mathlib-supplies-and-what-it-does-not)
- [What is formalised](#what-is-formalised) — the module table
- Sections 2–4, the ground floor: [null 1-cells](#null-1-cells-and-strong-bizero-objects),
  [2-monomorphisms](#2-monomorphisms-and-2-epimorphisms), [2-kernels](#2-kernels-and-2-cokernels),
  [short 2-exact sequences](#trivial-objects-and-short-2-exact-sequences),
  [normality](#normal-1-cells-and-the-normal-image-factorisation),
  [the Normal Short Five Lemma](#the-normal-short-five-lemma),
  [2-z-exactness](#2-z-exactness-and-chosen-2-kernels),
  [the comparison](#the-comparison-and-self-duality-of-exactness),
  [dinversion](#dinversion-and-the-pure-snake-lemma),
  [homology](#homology-and-the-self-duality-criterion),
  [the Third Isomorphism Property](#the-third-isomorphism-property)
- Sections 5–7: [bipullbacks](#bipullbacks), [2-di-exactness](#2-di-exactness),
  [duality](#duality-through-the-1-cell-dual), [the comparison as data](#the-pure-snake-lemma-as-data),
  [exactness at the middle](#exactness-of-the-snake-sequence-at-the-middle),
  [the top half](#the-top-half-of-the-snake-construction),
  [the routine verification](#the-routine-verification),
  [the connecting 1-cell](#the-connecting-1-cell), [the general case](#the-general-case),
  [naturality](#2-naturality-of-the-comparison)
- Section 8, the models: [`AbCat` and where (DI2) bites](#serre-classes-and-where-di2-bites-in-abcat),
  [`AbCat` is not (DPN)](#abcat-is-not-dpn-an-asymmetric-pair-of-serre-classes),
  [condition (AS)](#condition-as-and-where-the-saturation-is-a-serre-class),
  [the witness](#the-witness-finitely-generated-modules),
  [(SAT)](#sat-and-its-two-closure-properties), [the 2-category](#the-2-category-and-how-far-it-can-be-checked),
  [the locally discrete model](#a-model), [the classical Snake Lemma](#the-classical-snake-lemma),
  [the lattices](#a-second-model-modular-lattices)
- Section 9: [modular pairs](#modular-pairs-and-transpositions),
  [Birkhoff](#semimodularity-and-birkhoffs-theorem), [the parametrised model](#the-lattice-model-parametrised), [the pentagon](#the-pentagon),
  [the Snake Lemma without self-duality](#the-snake-lemma-without-self-duality),
  [Hilbert lattices](#hilbert-lattices)
- [The blueprint](#the-blueprint) — the paper's statements as a dependency graph

## The blueprint

**Read it at <https://tvdlinde.github.io/snake-lean/>.** It is rebuilt and republished from CI on
every push to `master`, by `.github/workflows/blueprint.yml`.

`blueprint/` holds a [leanblueprint](https://github.com/PatrickMassot/leanblueprint) view of the
paper: its statements as a web document, with a dependency graph coloured by what is formalised
and by what is ready to be. It is generated from the paper's source, so its numbering is the
paper's, and its edges are read off the Lean environment rather than guessed. `blueprint/README.md`
says how to build it and where each kind of edge comes from.

## What Mathlib supplies, and what it does not

Mathlib has bicategories, the `bicategory` coherence tactic, `Bicategory.Strict` (which yields an
honest `Category` of objects and 1-cells, so that pastings are ordinary composites),
`Bicategory.IsLocallyDiscrete`, the 1-cell dual `Bᵒᵖ` with 2-cells preserved, and
`Bicategory.Equivalence`. Those last three matter especially: local discreteness is the paper's
discretisation, made checkable; the 1-cell dual is the paper's duality, so that "dually" becomes
a transport rather than a second proof.

Mathlib has **no bicategorical limit theory at all** — no bilimits, no bipullbacks, no bizero
objects, no representably fully faithful 1-cells. Everything above the ground floor is built
here.

## What is formalised

| Module | Statement | Paper |
| --- | --- | --- |
| `SnakeLean/Op.lean` | The 1-cell dual `Bᵒᵖ`: the strictness instance Mathlib lacks, on which the duality of the whole development rests. Each notion is then transported in the module that defines it, so that a dual statement follows from the primal one instead of being reproved | Duality, throughout |
| `SnakeLean/Null.lean` | Null 1-cells and strong bizero objects; a 1-cell carries at most one 2-cell into a given null 1-cell once one such 2-cell is invertible. Hence any two invertible 2-cells with the same null codomain agree, and the coherence condition on a morphism of short 2-exact sequences is automatic | Definitions 2.3 `Def Bizero Object` and 2.5 `Def Strong`; Lemma 2.6 `L:UniqueNull`; Proposition 3.26 `P:CoherenceFree` |
| `SnakeLean/Mono.lean` | 2-monomorphisms and 2-epimorphisms as representably (co)fully faithful 1-cells: identities, closure under composition, invariance under invertible 2-cells, lifting of invertible 2-cells, and the cancellation property — for which faithfulness in the middle position suffices | Section 2; Proposition 3.6 `Composites of Normal Monos`(i) |
| `SnakeLean/Kernel.lean` | 2-kernels and 2-cokernels, as propositions rather than structure; that 2-monomorphisms reflect null morphisms; that postcomposing with a 2-monomorphism does not change the 2-kernel; uniqueness of 2-kernels up to equivalence | Definitions 2.18 `Def 2-kernel` and 2.19 `Def 2-cokernel`; Propositions 2.16 `prop2monoreflectsnull` and 3.9 `CoKernel of Composite`; Corollary 2.22 `corollkeruniqueuptoequiv` |
| `SnakeLean/Exact.lean` | Trivial objects, short 2-exact sequences, normal 2-monomorphisms and 2-epimorphisms; that a 2-cokernel is a 2-cokernel of its own 2-kernel; that the kernel object of a short 2-exact sequence is trivial exactly when the 2-cokernel is an equivalence | Definitions 2.9 `Def Trivial` and 3.12 `Def:SES`; Lemma 2.24 `2-Mono Trivial Kernel`; Propositions 3.11 `kernel is kernel of its cokernel` and 3.15 `Prop Equivalence CoKernel`; Corollary 3.16 `Trivial Kernel Normal Mono` |
| `SnakeLean/Normal.lean` | Normal 1-cells; the characterisation of equivalences as the 1-cells that are at once normal 2-monomorphisms and normal 2-epimorphisms; uniqueness of the normal image factorisation; invariance of normality under composition with equivalences | Definitions 3.3 `Def Normal Mono` and 3.4 `Def Normal`; Propositions 3.6 `Composites of Normal Monos`(ii), and 3.22 `Image Factorisation of Normal Map is Unique`; Corollaries 3.8 `C:NormalTransport` and 3.18 `Equivalence Is Mono Plus Normal Epi` |
| `SnakeLean/FiveLemma.lean` | Morphisms of short 2-exact sequences, with the paper's coherence condition proved rather than imposed; the Normal Short Five Lemma, in all three parts, without bipullbacks | Definition 3.25 `Def:morphism of SES`; Proposition 3.26 `P:CoherenceFree`; Theorem 3.28 `NSFL` |
| `SnakeLean/ZExact.lean` | 2-z-exactness: chosen 2-kernels and 2-cokernels, the 2-coimage and the 2-image, and the transport of any 2-kernel onto the chosen one; the Section 3 results restated in the paper's choice-based notation | Definition 3.2 `Def ZExact`; Section 3.21 `SS:ImageFactorisation` |
| `SnakeLean/Comparison.lean` | The canonical comparison from the 2-coimage to the 2-image, its existence and uniqueness, and the characterisation of normal 1-cells by it; self-duality of exactness for a composable pair of normal 1-cells, and the definition of an exact sequence | Lemma 4.2 `Normal Iff Comparison Iso`; Proposition 4.4 `Exactness Self-Dual`; Definition 4.5 `Def:ExactSequence` |
| `SnakeLean/Dinversion.lean` | Antinormal decompositions of the zero map and their dinversion; homological self-duality; the equivalence of homological self-duality with the Pure Snake condition; the Pure Snake Lemma; exactness as nullity of the dinversion | Definitions 4.7 `Def:Dinversion` and 4.17 `Def:HSD`; Proposition 4.18 `Criteria HSD` (i) ⟺ (iii); Lemma 4.27 `Pure Snake Lemma`; Proposition 4.4 `Exactness Self-Dual` |
| `SnakeLean/Homology.lean` | Normal chain complexes and the self-duality of homology, completing the three-way criterion for homological self-duality; that null 1-cells are normal; the four-way characterisation of exactness by the induced 1-cells and by the homology object | Definition 4.14 `Def:Homology`; Proposition 4.18 `Criteria HSD` (i) ⟺ (ii); Proposition 4.24 `Exactness via Homology` |
| `SnakeLean/ThirdIso.lean` | Totally normal sequences, and the equivalence of homological self-duality with the Third Isomorphism Property for towers of normal 2-monomorphisms and for towers of normal 2-epimorphisms | Definition 4.21 `Def:TotallyNormal`; Proposition 4.22 `Third Iso` |
| `SnakeLean/Bipullback.lean` | Bipullbacks and bipushouts, built from nothing; a criterion reducing a bipullback to a single factorisation property; that a 2-kernel is exactly a bipullback along a null 1-cell | Definition 5.2 `Def Bipullback`; Proposition 5.3 `Kernel vs pullback` |
| `SnakeLean/Squares.lean` | The two squares of a morphism of short 2-exact sequences: the left one is a bipullback when the right-hand vertical is a 2-monomorphism; the outer verticals are equivalences when the opposite square is a bilimit | Propositions 5.7 `Mono Implies Left Pullback`, 5.9 `Right Square Pullback` and 5.10 `Left Square Pushout` |
| `SnakeLean/DiExact.lean` | Condition (DI2) of 2-di-exactness, and that it implies homological self-duality, in the stronger form that the dinversion of every antinormal pair is normal | Definition 6.2 `Def:DiExact`; Proposition 6.3 `P:DiExactHSD` |
| `SnakeLean/PureSnake.lean` | The Pure Snake Lemma with its comparison as data, and the uniqueness clause that makes naturality statable | Lemma 4.27 `Pure Snake Lemma`, restated for Section 6 |
| `SnakeLean/Snake.lean` | The 1-cells induced on 2-kernels and 2-cokernels by a ladder, and that `ā` is a 2-kernel of `b̄` when `a` is a 2-kernel of `b` — 2-exactness of the snake sequence at `2-Ker(g)` and `2-Cok(g)` | Proposition 6.17 `P:KerBarA`, the second assertion of Theorem 6.9 `Snake General 2D`, at the hypotheses of Remark 6.18 `Rem BarA Cost` |
| `SnakeLean/SnakeConnecting.lean` | The top half of the snake construction: the normal image factorisation of `b ∘ 2-ker(g)` supplied by (DI2), the induced `t`, that `(r, ī)` is a normal image factorisation of `b̄`, and the first of the three connecting equivalences | Section 6.8 `SS:Construction`, Figure 1 `Fig Constructing Snake`; Lemma 6.10 `L:ImageOfBBar` |
| `SnakeLean/SnakeQuotient.lean` | The routine verification: that the 2-cokernel of `2-Img(f) ↣ 2-Img(g)` is `Q = C/I`, together with the normality of that 2-monomorphism, so that both rows of the third pure configuration are short 2-exact | Lemma 6.12 `L:ImgMapNormal`; Proposition 6.13 `P:RoutineVerification` |
| `SnakeLean/SnakeDelta.lean` | The connecting 1-cell `∂`, assembled from the three applications of the Pure Snake Lemma; 2-exactness of the snake sequence at all four inner positions in the special case; and that `∂` does not depend on which comparisons those applications produce | Proposition 6.14 `P:Shape`; Remark 6.15 `Rem Partial Choices`; Theorem 6.9 `Snake General 2D`, the special case |
| `SnakeLean/SnakeGeneral.lean` | The reduction of the general case to the special one — Figure 2 `Fig Snake General` — and the Snake Lemma itself, with all six 1-cells of the snake sequence normal | Section 6.19 `SS:GeneralCase`: Lemma 6.20 `L:Restriction`, Proposition 6.21 `P:KerComparison`; Theorem 6.9 `Snake General 2D` |
| `SnakeLean/NonSelfDual.lean` | The two hypotheses that replace 2-di-exactness — (DPN), that dinversion preserve normality, and closure of normal 2-epimorphisms under composition — and their place between 2-di-exactness and homological self-duality. The Snake Lemma consumes (DI2) at exactly two sites, and those two 1-cells are each other's dinversions, so (DPN) alone is circular; the way out is `t`, the induced 1-cell on 2-images, and the row `2-Ker(t) ↣ X`, a 2-kernel by bipullback stability; also the cancellation of a 2-monomorphism out of a normal 1-cell | Definitions 9.2 `Def:DPN` and 9.4 `Def:NEC`; Proposition 9.3 `P:DPNPlace`; Lemma 9.10 `L:NSDEpi`; Proposition 9.11 `P:NSDKappa`; Proposition 3.23 `P:NormalCancel` |
| `SnakeLean/NSDNormal.lean` | The two normality statements of the non-self-dual Snake Lemma: `c̲` is normal because the dinversion of `(c, 2-coker(g))` *is* `2-img(h) ∘ t`, and `b̄` is normal because its antinormal decomposition through `2-Ker(e)` has dinversion `f` corestricted along `κ` | Propositions 9.12 `P:NSDcbar` and 9.13 `P:NSDbbar` |
| `SnakeLean/NSDConnecting.lean` | **The Snake Lemma without self-duality**: under (DPN) and closure of normal 2-epimorphisms under composition, the connecting 1-cell exists and the snake sequence is 2-exact at all four places; and the same with normal 2-monomorphisms closed under composition instead, by transport through `Bᵒᵖ` | Lemma 4.10 `L:DinversionCoker`; Proposition 9.16 `P:NSDLambda`; Lemma 9.17 `L:NSDChain`; Theorem 9.19 `T:SnakeNonSelfDual` |
| `SnakeLean/Naturality.lean` | Morphisms of pure configurations, and 2-naturality of the Pure Snake comparison in them; the comparisons induced on the verticals, on 2-kernels and 2-cokernels, and on normal images; and the pasting that turns naturality of the three Pure Snake comparisons into naturality of `∂` | Section 7; Lemma 7.4 `L:InducedVerticals`; Theorem 7.6 `T:NaturalComparison`; towards Theorem 7.10 `T:NaturalSnake` — its four squares, the comparison on normal images and the pasting, but not the assembly of the three morphisms of pure configurations out of a morphism of ladders |
| `SnakeLean/SerreJoin.lean` | Not about the 2-categorical development but about the candidate model `AbCat`: meets and joins of Serre classes in an abelian category, and the module-theoretic side of the reduction of condition (DI2) for `AbCat` to a single question — whether the `S`-saturation of a Serre class `K` is again a Serre class | The reduction 8.11 `P:DIabcat` and the counterexample 8.12 `P:AbCatFails`, both of which the blueprint leaves unclaimed: the passage from Serre classes to `AbCat` is the Serre-quotient bridge |
| `SnakeLean/SerreAsymmetry.lean` | The same question in the other order: an abelian category with two Serre classes whose saturations are *not* Serre together, so that `AbCat` does not satisfy (DPN) either | Proposition 9.25 `P:AbCatNotDPN`; Corollary 9.26 `C:HSDstrict` |
| `SnakeLean/CondAS.lean` | Condition (AS) — every Serre class meeting all nonzero subobjects of an object contains it — and the theorem that it implies the `S`-saturation of a Serre class `K` is again one, for every `K` and `S` at once — the category is saturated in the sense of Definition 8.15 `D:SAT` | Definition 8.20 `D:AS`; Proposition 8.21 `P:ASimplies` |
| `SnakeLean/CondASModule.lean` | The witness: the finitely generated modules over a commutative noetherian ring satisfy (AS), so their saturations of Serre classes are Serre classes — they are saturated, with no hypotheses left | Proposition 8.24 `P:ModAS` |
| `SnakeLean/SerreSubcategory.lean` | That the full subcategory on a Serre class is abelian, the dictionary between its Serre classes and those of the ambient category lying below it, and the conclusion that condition (SAT) is inherited by Serre subcategories | Definition 8.15 `D:SAT`; Proposition 8.16 `P:SATclosed`, first half |
| `SnakeLean/SerreQuotient.lean` | What a Serre quotient is asked to supply, and that condition (SAT) is inherited by Serre quotients — using one half of Gabriel's correspondence and nothing else | Proposition 8.16 `P:SATclosed`, second half |
| `SnakeLean/AbCatModel.lean` | The 2-categories of abelian categories, exact functors and natural transformations, one for each class of abelian categories containing the zero category and closed under Serre subcategories: a strict bicategory with the zero category as a strong bizero object, in which the 2-kernel of an exact functor is the full subcategory of the objects it annihilates, and every normal 2-monomorphism is the inclusion of a Serre subcategory. `AbCat` and `Sat` are two instances | Propositions 8.3 `P:AbCatBizero` and 8.4 `P:AbCatKernel`, for every class and so in `AbCat`; the 2-kernel half of (DI1) for Theorem 8.17 `T:SatModel`, whose 2-cokernel half and (DI2) are not formalised, so that neither `T:SatModel` nor Corollary 8.27 `C:Populated` is claimed |
| `SnakeLean/LocallyDiscreteModel.lean` | A model: every abelian category, viewed as a locally discrete 2-category, has a strong bizero object and satisfies (DI1) and (DI2), so the standing hypotheses of Section 6 are consistent | Example 6.5 `Ex DiExact`; the model it replaces is refuted in Proposition 8.12 `P:AbCatFails` |
| `SnakeLean/Classical.lean` | The Snake Lemma of homological algebra, deduced from the 2-categorical one by reading an abelian category as a locally discrete 2-category: a commutative ladder becomes a `MorphismSES`, and `IsExactAt` becomes `ShortComplex.Exact` in both directions | Corollary 6.24 `Snake General` |
| `SnakeLean/ModularPair.lean` | Modular pairs and transpositions, on a bare lattice: the transposition `[a ⊓ b, a] → [b, a ⊔ b]` is invertible exactly when `(b, a)` is a modular pair and `(a, b)` a dual modular pair; a lattice is modular exactly when all of its transpositions are invertible; transposition-symmetry is self-dual and is inherited by intervals | Lemma 9.30 `L:ModularPairs`; Proposition 8.36 `P:SupModular` at lattice level |
| `SnakeLean/Semimodular.lean` | A transposition-symmetric lattice satisfying the ascending chain condition is semimodular, and dually — the half of Proposition 9.34 `P:FiniteLength` that is the paper's own | Proposition 9.34 `P:FiniteLength`, first half |
| `SnakeLean/Birkhoff.lean` | Birkhoff's theorem: a lattice which is semimodular and dually semimodular, satisfies both chain conditions and has all heights finite is modular; hence a transposition-symmetric lattice of finite length is modular, so on such lattices (DPN) and (DI2) agree | Proposition 9.34 `P:FiniteLength`; Birkhoff, *Lattice Theory* II.16 |
| `SnakeLean/LatticeModel.lean` | The locally ordered model, for any class of complete lattices closed under segments: 2-kernels and 2-cokernels are the segments, and an antinormal 1-cell is normal exactly when the corresponding transposition is invertible, so condition (DI2) is Dedekind's transposition principle and the modular lattices form a 2-di-exact 2-category | Section 8.30 `SS:ModelLattices` and Proposition 9.29 `P:SupClass`: 8.32 `P:SupBizero`, 8.33 `P:SupKernels`, 8.34 `C:SupNormal`, 8.35 `P:SupAntinormal`, 8.36 `P:SupModular` both ways, 8.37 `T:LatticeModel` |
| `SnakeLean/HilbertLattice.lean` | Mackey's theorem, both directions: two closed subspaces of a Hilbert space form a dual modular pair exactly when their sum is closed. Hence the transposition of `A` and `B` is invertible exactly when `A + B` and `Aᗮ + Bᗮ` are closed — a symmetric criterion, so the lattice is transposition-symmetric | Proposition 9.31 `P:HilbertSymmetric`; Mackey, Theorem III-6 |
| `SnakeLean/LatticeNSD.lean` | The non-self-dual hypotheses on a class of lattices: condition (DPN) holds as soon as every member is transposition-symmetric, and normal 2-monomorphisms and normal 2-epimorphisms always compose | Proposition 9.29 `P:SupClass`, the (DPN) and composition halves |
| `SnakeLean/Pentagon.lean` | The pentagon `N₅` as a complete lattice, with the two transpositions that matter decided: `y` and `z` transpose, `z` and `y` do not. Hence `N₅` is neither modular nor transposition-symmetric, and `Sup` is neither 2-di-exact nor (DPN), at the paper's witness pair | Proposition 8.36 `P:SupModular`, last clause; Proposition 8.38 `P:SupNotDPN`, last clause; Remark 9.5 `Rem NSD Strict` |

## Null 1-cells and strong bizero objects

`SnakeLean/Null.lean`. A 1-cell is null relative to `Z` when it factors through `Z`; the object
`Z` is strong when any two parallel null 1-cells admit exactly one 2-cell between them. The
module proves `IsNull.eq_of_isIso`: if `n` is null and some 2-cell `β : x ⟶ n` is invertible,
then every 2-cell `x ⟶ n` equals `β`. Note that `x` is arbitrary — it is not assumed null, and
that is what makes the lemma useful, since the paper's structure 2-cells are invertible 2-cells
into a null 1-cell out of a 1-cell that is not null.

This is Lemma 2.6 `L:UniqueNull`. The consequence the paper cares about is
`IsNull.eq_of_isIso_of_isIso`: two invertible 2-cells with the same domain and the same null
codomain are equal. The coherence condition one might expect Definition 3.25
`Def:morphism of SES` to impose equates two such 2-cells `q ∘ g ∘ k' ⟹ 0`, so it holds
automatically — Proposition 3.26 `P:CoherenceFree` — and the definition does not impose it.

The theorem is stated at the paper's hypotheses and a little below them: it uses neither the
bizero condition on `Z` (that its hom-categories are equivalent to the terminal category) nor
strictness of the 2-category. The bizero condition is accordingly not defined in this module,
since nothing here consumes it; it is `IsBizero` in `SnakeLean/Kernel.lean`, Definition 2.3
verbatim, and `isBizero_of_isStrong` there shows that `HasBizero` with `IsStrong` — the two
classes every result of the development is stated with — is exactly the paper's strong bizero
object.

Non-vacuity is supplied by `isStrong_locallyDiscrete`: a zero object of an ordinary category, in
Mathlib's sense `Limits.IsZero`, is a strong bizero object of the associated locally discrete
2-category. This is the paper's remark that in a 1-category there is no difference between a
bizero object and a strong bizero object.

Elsewhere: the bizero condition itself is `IsBizero` in `SnakeLean/Kernel.lean`, as said;
2-monomorphisms and 2-epimorphisms are `SnakeLean/Mono.lean`, 2-kernels and 2-cokernels
`SnakeLean/Kernel.lean`, short 2-exact sequences `SnakeLean/Exact.lean`.

## 2-monomorphisms and 2-epimorphisms

`SnakeLean/Mono.lean`. A 2-monomorphism is a representably fully faithful 1-cell: postcomposition
with it is a fully faithful functor on every hom-category. Mathlib supplies those functors as
`Bicategory.postcomp` and `Bicategory.precomp`, together with the natural isomorphisms relating
them to composition, so the module is largely a translation into Mathlib's `Full`/`Faithful` API.
Faithful and cofaithful 1-cells — the weaker notion, which the paper does not take as its
definition but uses as a hypothesis where it is all a proof consumes — are defined alongside.

Proposition 3.6 `Composites of Normal Monos`(i) says that if `k ≅ f ≫ g` with `k` a
2-monomorphism and `g` faithful, then `f` is a 2-monomorphism. `isTwoMono_of_comp` is that
statement, assuming only `IsFaithful₁ g`; Remark 3.7 `Rem Faithful Enough` is the paper's own
note that fullness of `g` never enters. The dual `isTwoEpi_of_comp` has `f` cofaithful.

Non-vacuity and the discretisation come together in `isTwoMono_locallyDiscrete_iff`: in a locally
discrete 2-category a 1-cell is a 2-monomorphism exactly when it is a monomorphism of the
underlying category.

Equivalences are shown to be both 2-monomorphisms and 2-epimorphisms.

Proposition 3.6 `Composites of Normal Monos`(ii), which is about *normal* 2-monomorphisms, is in
`SnakeLean/Normal.lean`.

## 2-kernels and 2-cokernels

`SnakeLean/Kernel.lean`. Mathlib has no bicategorical limit theory, so this is built from
nothing. Following the paper we work in a strict bicategory: a null 1-cell is one that factors
through the bizero object on the nose, and that is only stable under composition when
composition is strictly associative.

**The structure 2-cell is not structure.** The paper's 2-kernel is a 1-cell `k` *together with*
an invertible 2-cell `κ : k ≫ f ≅ 0`. By `IsNull.eq_of_isIso` such a 2-cell is unique once it
exists, so `IsTwoKernel` is a `Prop`. Two consequences for the paper, both of which it now
takes: Definition 3.12 `Def:SES` does not require that *the same* 2-cell exhibit both universal
properties, and condition (1) of Definition 2.18 `Def 2-kernel` carries no compatibility clause
relating the factorisation 2-cell to the structure 2-cell.

Condition (2) of the paper's definition is verbatim `IsTwoMono k`, so it is taken as the
definition, and the paper's Proposition that 2-kernels are 2-monomorphisms becomes definitional.

Proved here: `IsEssNull.of_comp_isTwoMono` (Proposition 2.16 `prop2monoreflectsnull`, that every
2-monomorphism reflects null morphisms), `isTwoKernel_comp_isTwoMono_iff` (Proposition
3.9 `CoKernel of Composite`), and `IsTwoKernel.equivalence` (Corollary 2.22 `corollkeruniqueuptoequiv`,
built as a Mathlib adjoint equivalence through `mkOfAdjointifyCounit`). Each has its dual.

The linter's unused-hypothesis reports: invariance of a 2-kernel under an invertible 2-cell needs
neither strictness nor strongness, and strictness is used only where null 1-cells have to be
stable under composition. Those hypotheses are `omit`ted where unused.

Elsewhere: that a 2-kernel is the bipullback along a null 1-cell is `SnakeLean/Bipullback.lean`
(Proposition 5.3 `Kernel vs pullback`); that a 2-monomorphism has trivial 2-kernel, with the
notion of trivial object, and short 2-exact sequences are `SnakeLean/Exact.lean`. Duality is by
transport through Mathlib's 1-cell dual `Bᵒᵖ`, set up in `SnakeLean/Op.lean` — see
"Duality by transport" below.

## Trivial objects and short 2-exact sequences

`SnakeLean/Exact.lean`. An object is trivial when its identity 1-cell is essentially null,
which is Definition 2.9 `Def Trivial` verbatim; `IsTrivial.isEquiv1_toZero` is the half of Remark
2.10 `Rem Trivial` that makes such an object equivalent to the bizero object. As the remark
explains, taking the identity condition as the definition is what makes the arguments short:
one reflection step by a 2-monomorphism turns "this 1-cell is null" into "its domain is trivial".

That shows up first in `IsTwoKernel.isTrivial_of_isTwoMono`, Lemma 2.24 `2-Mono Trivial Kernel`.
The proof is the paper's: it reflects nullity twice — `k ≫ m` null, so `k` null, so `𝟙 K ≫ k`
null, so `𝟙 K` null — inspects no hom-category, and never uses the bizero condition, which the
paper points out after the proof. The same shape then does both directions of
`IsSES.isTrivial_iff_isEquiv1` (Proposition 3.15 `Prop Equivalence CoKernel`).

`IsSES O k q` asks that `k` be a 2-kernel of `q` and `q` a 2-cokernel of `k`, which is
Definition 3.12 `Def:SES`; the definition writes one invertible 2-cell `κ : q ∘ k ≅ 0` for both
universal properties, there being only one, as explained under `SnakeLean/Kernel.lean` above.

Also here: `IsTwoCokernel.of_isTwoKernel` and its dual (Proposition
3.11 `kernel is kernel of its cokernel`), `isNormalMono_of_isTrivial` (Corollary
3.16 `Trivial Kernel Normal Mono`), and the two corollaries that a normal 2-epimorphism which is a
2-monomorphism is an equivalence, and dually.

Those two — Proposition 3.17 `Normal Epi Mono Equivalence`, a normal 2-epimorphism which is a
2-monomorphism is an equivalence, and dually — are proved as in the paper, directly and without
`Prop Equivalence CoKernel`, so without needing the 2-kernel that detour would require. A normal
2-epimorphism `q` is the 2-cokernel of some `g`; being a 2-monomorphism it reflects `g ≫ q ≅ 0`
to `g ≅ 0`, so the identity factors through `q`. `isEquiv1_of_isNormalEpi` carries no 2-kernel
hypothesis at all, which is what the paper's sentence after the proof records.

Elsewhere: the Normal Short Five Lemma is `SnakeLean/FiveLemma.lean`, and the class asserting
that all 2-kernels and 2-cokernels exist — the paper's 2-z-exactness, `TwoZExact` — is
`SnakeLean/ZExact.lean`; the results here take the 2-kernel they need as an explicit hypothesis.

## Normal 1-cells and the normal image factorisation

`SnakeLean/Normal.lean`. A 1-cell is normal when it factors as a normal 2-epimorphism followed by
a normal 2-monomorphism. An earlier draft defined it by an equality, with a
marginal note asking that this be relaxed to an invertible 2-cell and every proof about normal
1-cells rechecked at the weaker hypothesis. `IsNormal` is defined with the invertible 2-cell from
the start, so this module is that recheck. Nothing breaks, and Definition 3.4 `Def Normal` now
reads that way.

Corollary 3.8 `C:NormalTransport` says that normal 2-monomorphisms and normal 2-epimorphisms survive
composition with an equivalence on either side, and hence that normality and antinormality are
invariant under replacing a 1-cell by `u ≫ w ≫ v` with `u` and `v` equivalences
(`IsNormal.transport`, `IsAntinormal.transport`, `isNormal_transport_iff`,
`isAntinormal_transport_iff`). It was written for Section 8, where it licenses the
reduction of condition (DI2) in the 2-category of abelian categories to the single composite of a
Serre inclusion with a Serre projection. It does not
follow from `Composites of Normal Monos`(ii), which concludes normality of a *factor* from
normality of the composite, whereas what is wanted is the converse direction. Two of the four
halves were already present as `IsTwoKernel.isEquiv1_comp` and `IsTwoCokernel.comp_isEquiv1`;
the other two are proved here, and need only a bizero object and not a strong one.

`IsNormalMono.of_comp` is Proposition 3.6 `Composites of Normal Monos`(ii). Part (i) is in
`SnakeLean/Mono.lean` at the faithfulness the paper's Remark 3.7 `Rem Faithful Enough` records;
part (ii) admits no such weakening, because its proof lifts an invertible 2-cell along that
1-cell, which is exactly fullness. It does, however, need only a bizero object and not a strong one — the
linter reports `IsStrong O` unused in both (ii) and its dual, so the hypothesis is dropped.

`isEquiv1_tfae` assembles Corollary 3.18 `Equivalence Is Mono Plus Normal Epi`, the new content being
that an equivalence is a normal 2-monomorphism: it is a 2-kernel of a null 1-cell, since the
identity is one and 2-kernels are stable under precomposition with an equivalence.

`imageFactorisation_unique` and `isNormal_of_factorisation` are Proposition
3.22 `Image Factorisation of Normal Map is Unique`, following the paper's proof. The comparison
1-cell `t` is obtained from the 2-cokernel property of `e`, shown to be a normal 2-monomorphism
by `IsNormalMono.of_comp` and a 2-epimorphism by the dual of part (i), and is therefore an
equivalence.

**No 2-z-exactness anywhere.** The paper states all of this in a 2-z-exact 2-category. No result
in this module needs more than the single 2-kernel or 2-cokernel named in its own statement, and
two of them need none.

**Not formalised:** morphisms of short 2-exact sequences and the Normal Short Five Lemma, which
are in `SnakeLean/FiveLemma.lean`.

## The Normal Short Five Lemma

`SnakeLean/FiveLemma.lean`. The paper proves Theorem 3.28 `NSFL`(1) by a nullity chase along
the ladder, and Remark 3.29 `Rem NSFL Hypotheses` records that no bilimit is involved; the proof
here is that chase. `isTrivial_of_isTwoMono_ladder` reflects nullity five times. Given a
2-kernel `n` of `g`: `n ≫ g ≅ 0`, so `n ≫ q' ≫ h ≅ 0` through `φQ`, so `n ≫ q' ≅ 0` since `h`
reflects nullity, so `n` factors as `m ≫ k'` through the 2-kernel `k'`; then
`(m ≫ f) ≫ k ≅ n ≫ g ≅ 0` through `φK`, so `m ≫ f ≅ 0` since `k` reflects nullity, so `m ≅ 0`
since `f` does, so `n ≅ 0`, so `𝟙 N ≅ 0` since `n` reflects nullity. Part (2) is deduced by
duality through `SnakeLean/Op.lean`.

Stated at the strength the chase consumes, as in Remark 3.29, part (1) does not need either row
to be a short 2-exact sequence: `q` is an arbitrary 1-cell, `q'` need not be a 2-cokernel, `k`
need only be a 2-monomorphism rather than a 2-kernel. Part (2) needs the mirror halves.
2-z-exactness is not used: the 2-kernel or 2-cokernel of `g` is an explicit hypothesis.

In the paper, Proposition 5.7 `Mono Implies Left Pullback` is cited exactly once, in the proof
of Proposition 9.11 `P:NSDKappa`; Proposition 5.9 `Right Square Pullback` is cited only by its
own dual.

`MorphismSES` carries the two invertible square-fillers and no coherence condition, as
Definition 3.25 `Def:morphism of SES` does. `MorphismSES.coherence` is Proposition 3.26
`P:CoherenceFree`: the condition one might expect to impose holds automatically, since both
sides are invertible 2-cells out of `k' ≫ g ≫ q` into a null 1-cell, and there is at most one
such.

**Not formalised:** 2-cells between morphisms of short 2-exact sequences, which nothing here
consumes. Everything in Sections 2 and 3 of the paper is machine-checked except the two
examples, 3.13 `Ex SES` and 3.14 `Ex Hypoabelianisation`.

## 2-z-exactness and chosen 2-kernels

`SnakeLean/ZExact.lean`. Sections 2 and 3 were formalised with no notion of 2-z-exactness: each
result takes as an explicit hypothesis the one 2-kernel or 2-cokernel named in its own statement,
and several need none. Section 4 forces the change, because `2-Coim(f) = 2-Cok(2-ker(f))` and
`2-Img(f) = 2-Ker(2-cok(f))` cannot be written down without a 2-kernel and a 2-cokernel for every
1-cell.

The paper bundles three conditions into 2-z-exactness — a bizero object, its strongness, and the
existence of all 2-kernels and 2-cokernels. They are kept apart here as `HasBizero O`,
`IsStrong O` and `TwoZExact O`, so that the linter keeps reporting which of the three each result
consumes. The answer for everything below Section 4 is that `TwoZExact` is never consumed: the
choice-form statements at the end of the module — `isNormalMono_iff'`, `imageFactorisation_unique'`,
`isEquiv1_iff_isTrivial'`, `nsfl_isNormalMono'`, `nsfl_isNormalEpi'`, `nsfl_isEquiv1'` — are
proved from `HasTwoKernel O f` for the single `f` in question, and each reads as the paper states
it while assuming strictly less.

`Classical.choice` becomes load-bearing here for the first time, since `twoKernel O f` chooses a
2-kernel. `IsTwoKernel.exists_isEquiv1` is Corollary 2.22 `corollkeruniqueuptoequiv` in the form the
downstream arguments need: it yields the comparison 1-cell together with the invertible 2-cell
over the codomain, rather than a bare `Bicategory.Equivalence`. It needs neither a strong bizero
object nor 2-z-exactness.

**Not formalised:** that the chosen 2-kernels of isomorphic 1-cells are equal. They are only
equivalent, which is all the paper's arguments use.

## The comparison, and self-duality of exactness

`SnakeLean/Comparison.lean`. Lemma 4.2 `Normal Iff Comparison Iso` builds `j_f` in two steps:
`2-ker(f) ≫ f ≅ 0` factors `f` through the 2-coimage as some `v`, and then `v ≫ 2-cok(f) ≅ 0`
because the 2-coimage is a 2-epimorphism and so coreflects nullity, which factors `v` through the
2-image. Uniqueness is one preimage along a 2-epimorphism followed by one along a
2-monomorphism, and needs neither a bizero object nor strictness.

Every statement here is proved first with its 2-kernels and 2-cokernels named explicitly, and
only then specialised to the chosen ones; the primed names are the choice forms. This is not
housekeeping. Proposition 4.18 `Criteria HSD` and Proposition 4.22 `Third Iso` both identify
the 2-kernel of a dinversion with a 1-cell that is not the chosen one — the paper writes
`2-Ker(w) ≃ f` — so the hypothesis form is the one that can actually be applied, and
`IsTwoKernel.of_isEquiv1_comp` is what moves a result from one 2-kernel to another.

The converse half of Lemma 4.2 `Normal Iff Comparison Iso` — a normal 1-cell has an
equivalence for comparison — is proved as in the paper: Proposition 3.9 `CoKernel of Composite`
identifies `2-ker(f)` with `2-ker(e)`, so `2-coim(f) ≃ e`, and dually, after which the defining
relation of the comparison is read under these equivalences.

`exactness_tfae` is Proposition 4.4 `Exactness Self-Dual` as a three-way `List.TFAE`. As in the
paper, it reduces to two applications of `CoKernel of Composite` — a 2-monomorphism after `g`
does not change the 2-kernel, a 2-epimorphism before `f` does not change the 2-cokernel — after
which each of the outer conditions gives the other half of the short 2-exact sequence by
Proposition 3.11 `kernel is kernel of its cokernel`.

**`IsExactAt` is asymmetric, and the paper's definition is not.** Definition 4.5
`Def:ExactSequence` quantifies over pairs of composable *normal* morphisms, so the conditions it
asks for are visibly symmetric in the two. `IsExactAt f g` renders condition (i) as a property of the pair — `f` factors as a
normal 2-epimorphism followed by a 2-kernel of `g` — and that implies `IsNormal O f` while saying
nothing about `g`. The two differ by exactly that: `isExactAt_and_isNormal_op_iff` is an
unconditional equivalence between `IsExactAt f g` together with `IsNormal g` and its opposite
together with `IsNormal f`, and `isExactAt_op_iff` is the same statement for a pair that is normal
on both sides. **No homological self-duality is involved** — Proposition 4.4 `Exactness
Self-Dual` comes before Definition 4.17 `Def:HSD` and does not depend on it — and this is what makes "dually" literal for 2-exactness of
the snake sequence at `2-Cok(g)`.

A by-product: `isExactAt_iff` needs a 2-kernel of `f`, but only to compare two normal image
factorisations of `f`. Once `g` is normal the comparison can be routed through the 2-cokernel of
`f` instead, and `isExactAt_iff_of_isNormal` needs no 2-kernel at all.

Elsewhere: homological self-duality, dinversion and the Pure Snake Lemma are
`SnakeLean/Dinversion.lean`, next.

## Dinversion and the Pure Snake Lemma

`SnakeLean/Dinversion.lean`. The paper writes the dinversion of `(m, e)` as
`w = 2-cok(m) ∘ 2-ker(e)`; in Lean's diagrammatic order that is `2-ker(e) ≫ 2-cok(m)`, and for a
morphism of short 2-exact sequences with rows `A →a Y →b C` and `X →c Y →d Z` the dinversion of
`(a, d)` is `c ≫ b : X ⟶ C`.

The proof of Proposition 4.18 `Criteria HSD` establishes the identification `2-Ker(w) ≃ f` and
`2-Cok(w) ≃ h` and its converse, that every antinormal decomposition of the zero map arises
from such a morphism, both in two dimensions. Both halves are carried out here as there.
`isTwoKernel_dinversion_of_ladder` and `isTwoCokernel_dinversion_of_ladder` are the
identification; `isHSD_of_isPureSnake` is the converse, which takes the top row
`K → X → 2-Cok(m)`, the bottom row `2-Ker(e) → X → R` and the identity of `X` in the middle.

Two things the paper records in its remarks. First, **the two directions do not cost the
same** (Remark 4.19 `Rem HSD Cost`): `(i) ⟹ (iii)` needs no 2-z-exactness, since the comparison
and the 2-kernels it compares are given in the statement of (iii); `(iii) ⟹ (i)` does need it,
because the reconstructed morphism has verticals `t` and `r` whose 2-cokernel and 2-kernel must
exist before (iii) can be applied. Second, **the strongness of the bizero object is unused**
(Remark 4.28 `Rem Pure Snake Cost`) in both identifications and hence in the two assertions of
the Pure Snake Lemma that `f` is a normal 2-monomorphism and `h` a normal 2-epimorphism: they
are factorisation arguments through the universal properties of the two rows and nothing else.

`IsHSD` quantifies over the 2-kernel and the 2-cokernel rather than choosing them, so the
condition can be stated without 2-z-exactness and applied at whichever 2-kernel is in hand — which
is what both directions above need.

Within the Pure Snake Lemma, homological self-duality is used at exactly one point, exactness at
`C`, as Remark 4.28 says. Exactness at `X` is unconditional, since `f` is itself a 2-kernel of
`c ≫ b`.

**Exactness is the degenerate case of the condition.** An antinormal pair `(m, e)` is short
2-exact exactly when its dinversion `2-ker(e) ≫ 2-cok(m)` is *null* — Proposition 4.8
`P:NullDinversion`, here `IsZeroAntinormal.isSES_iff_isEssNull_dinversion`; homological
self-duality asks the dinversion of every antinormal pair to be *normal*; and a null 1-cell is
normal. So the two conditions live on the same 1-cell, one asking much more than the other, and
the criterion supplies a fourth condition for Proposition 4.4 `Exactness Self-Dual` — Corollary
4.9 `Cor Exact Null Dinversion`, here `isExactAt_iff_isEssNull_dinversion` — which, unlike the
paper's (i) and (ii), is fixed rather than exchanged by duality. Both directions are one
three-line chase read in the two possible orders, and neither uses homological self-duality, so
the symmetry of exactness costs nothing, which is the paragraph after the corollary.

Elsewhere: condition (ii) of Proposition 4.18 `Criteria HSD`, which needs normal chain
complexes, is `SnakeLean/Homology.lean`, next.

## Homology and the self-duality criterion

`SnakeLean/Homology.lean`. `NormalChainComplex` carries `obj : ℤ → B` and
`d : ∀ n : ℤ, obj (n + 1) ⟶ obj n`. Indexing the differential by its codomain keeps every index
of the form `n`, `n + 1`, `n + 2`, with no subtraction, so all the types reduce definitionally and
no `eqToHom` appears anywhere — including in the two-term complex, whose three differentials are
picked out by literal patterns and whose padding is `zero1`. Mathlib's `HomologicalComplex` is
1-categorical and not reusable.

Two steps the proof of Proposition 4.18 `Criteria HSD` takes in passing, both of which the
formalisation writes out.

**Null 1-cells have to be normal.** The converse half of (ii) ⟹ (i) puts an antinormal
decomposition `(m, e)` of the zero map at position `0` of a normal chain complex with a bizero
object in every other degree. A `ℤ`-indexed complex must be padded, the padding differentials
are null, and a normal chain complex asks every differential to be normal; the paper's proof
cites Proposition 4.13 `P:NullNormal` for this, and Remark 4.15 `Rem Padding` says why it
matters. `isNormal_of_isEssNull` is that proposition: a null `f : A ⟶ A'` factors as
`2-cok(1_A)`, then a null 1-cell, then `2-ker(1_{A'})`, and the middle one is an equivalence
because both its endpoints are trivial objects and every 1-cell between trivial objects is an
equivalence. As the remark says, this is the only place in Section 4 where 2-z-exactness does
more than let a statement be written down.

**The antinormal composite at a position needs two reflections.** The paper says the composite
`2-img(d_{n+1}) ∘ 2-coim(d_n)` is null since `d_n ∘ d_{n+1} ≅ 0`. Getting there is
`isEssNull_img_comp_coim`: `2-coim(d_{n+1})` coreflects the hypothesis to
`2-img(d_{n+1}) ∘ d_n ≅ 0`, and then `2-img(d_n)` reflects that to the claim.

As with (iii), the two directions of (i) ⟺ (ii) cost different things, which is Remark 4.19
`Rem HSD Cost`: (i) ⟹ (ii) needs no 2-z-exactness, (ii) ⟹ (i) needs it twice over, to pad the
complex and to form the comparison.

`exactness_via_homology_tfae` is Proposition 4.24 `Exactness via Homology`. The paper states it
in a homologically self-dual 2-category; the hypothesis is not used. Self-duality is what
guarantees that `2-ker(g) ≫ 2-cok(f)` is normal, so that the homology object `H` exists — but
once its normal image factorisation is given, the equivalence of the four conditions holds in
any 2-category with a strong bizero object.

**Not formalised:** the homology objects under separate names. `H^cok_n` and `H^ker_n` are
`2-Coim(w_n)` and `2-Img(w_n)` by Definition 4.14 `Def:Homology` itself, so every statement
about them is a statement about the comparison of `w_n`.

## The Third Isomorphism Property

`SnakeLean/ThirdIso.lean`. The proof of Proposition 4.22 `Third Iso` establishes (ii) ⟹ (i) by
corestricting an antinormal decomposition `(m, e)` of the zero map to the totally normal sequence
`K → 2-Ker(e) → X` — the corestriction `t` is a normal 2-monomorphism by Proposition 3.6
`Composites of Normal Monos`(ii), cancelling the 2-monomorphism `2-ker(e)` off the normal
2-monomorphism `m` — and applying (ii) to it. That returns a short 2-exact sequence whose
2-monomorphism part is `c'`, and `2-cok(t) ≫ c' ≅ w` holds by the construction of `c'`. A
2-cokernel followed by a 2-kernel is a normal image factorisation, so `w` is normal on the spot;
as the paper notes, nothing about `2-ker(w)` is used. The proof here is the same.

Both (i) ⟹ (ii) and (i) ⟹ (iii) use no 2-z-exactness: the normal image factorisation that
homological self-duality hands over already contains the 2-kernel the conclusion asks for. The two
converses need it, to form one further 2-cokernel or 2-kernel. This is the same asymmetry that
Remark 4.19 `Rem HSD Cost` records for the other two criteria of Proposition 4.18.

**Duality.** Condition (iii) is condition (ii) read in `Bᵒᵖ`. `isThirdIsoDual_iff_isThirdIso_op`
translates a totally normal sequence of 2-epimorphisms into a totally normal sequence of
2-monomorphisms with its two 1-cells exchanged, and the induced sequence of 2-kernels into the
induced sequence of 2-cokernels; both dual halves of Proposition 4.22 `Third Iso` are then one-line
consequences of their primal halves. This is where the transport pays best, since the two
directions are the longest arguments in Section 4.

## Bipullbacks

`SnakeLean/Bipullback.lean` and `SnakeLean/Squares.lean`. Mathlib has no bicategorical limit
theory at all, so `IsBipullback` is the paper's Definition built from nothing: an apex with two
projections and an invertible filler, a 1-dimensional universal property whose two factorisation
2-cells are required to paste to the given square, and a 2-dimensional universal property.
`IsBipushout` mirrors it, and is the **one** notion in the development whose dual is still written
out rather than transported. `IsBipullback` is the only definition here whose fields are equations
between 2-cells rather than propositions about 1-cells, so transporting it would need `op2` shown
compatible with `▷`, `◁`, `squareIso` and the pasting condition — at least as much work as the
second proof it would save.

**Nothing in `Null` through `ThirdIso` imports either module.** Sections 2, 3 and 4 of the paper
are machine-checked with no notion of bipullback anywhere in scope. That is the formal content of the paper's own
arrangement: bipullbacks are gathered into Section 5, after all the material that does not need
them.

Three things about the proofs, each of which the paper records in a remark.

**Proposition 5.7 `Mono Implies Left Pullback` needs no other bipullback.** The paper's proof
verifies the universal property directly, and Remark 5.8 `Rem Left Pullback Cost` says that it
forms no bipullback other than the one it asserts; the proof here is the same. Given a square
over the cospan, its `A'`-component `b` satisfies `b ∘ q' ∘ h ≅ 0`, so `b ∘ q' ≅ 0` because `h`
reflects null morphisms, so `b` factors through the 2-kernel `k'`; the second factorisation
2-cell and the pasting condition are then forced, because `k` is a 2-monomorphism. That last
step is `isBipullback_of_isTwoMono`, which reduces any such square to a single factorisation
property.

**The hypotheses are those of Remark 5.8, the same shape as Remark 3.29 for the Normal Short Five
Lemma.** Neither row need be a short 2-exact sequence: `q` may be an arbitrary 1-cell with `k` a
2-kernel of it, and `q'` need not be a 2-cokernel.

**No coherence condition.** The proof of Proposition 5.9 `Right Square Pullback` has to make two
comparison 2-cells compatible before the uniqueness half of the bipullback property can be
applied. The compatibility is an equation between invertible 2-cells whose common codomain is
essentially null, and any two such agree — Lemma 2.6 `L:UniqueNull`, `isEssNull_hom_ext`. The
paper appeals to that lemma and notes that this is the one place a coherence condition on
morphisms of short 2-exact sequences would ever have been used as a fact.

**Not formalised:** the dual of Proposition 5.3 `Kernel vs pullback`, which nothing consumes.

## 2-di-exactness

`SnakeLean/DiExact.lean`. Condition (DI2) of Definition 6.2 `Def:DiExact` is
`IsAntinormal O f → IsNormal O f`. Condition (DI1) is kept separate, as `TwoZExact`, so that the
linter keeps reporting which of the two each result consumes.

**The bridge to homological self-duality.** Section 6 works in a 2-di-exact 2-category and
invokes the Pure Snake Lemma five times; the Pure Snake Lemma is stated for a homologically
self-dual one. The bridge is Proposition 6.3 `P:DiExactHSD`, here `isHSD_of_twoDiExact`, and
the route is the paper's, not the obvious one. Specialising (DI2) to a null composite yields only
that null 1-cells are normal, which is a different statement. What works is that the
*dinversion* of an antinormal pair is itself an antinormal composite: `2-ker(e)` is a normal
2-monomorphism and `2-cok(m)` a normal 2-epimorphism, so (DI2) applies to `2-ker(e) ≫ 2-cok(m)`
on the nose.

**The bridge is cheaper than the definitions suggest**, which is Remark 6.4 `Rem Bridge Cost`.
Its statement carries no `Bicategory.Strict`, no `IsStrong`, and no `TwoZExact`: it holds in an
arbitrary bicategory with a bizero object that need not even be strong. It also never touches the
nullity of `m ≫ e`, which is a hypothesis of `IsHSD`. So the same one line proves the stronger
fact that the dinversion of *every* antinormal pair is normal — which is exactly condition
(DPN), Definition 9.2 `Def:DPN`, the weaker replacement for di-exactness that Section 9 runs on.
The paper states the proposition in that stronger form.

With the bridge in place, all four equivalents of homological self-duality — the Pure Snake Lemma,
self-duality of homology, and the two forms of the Third Isomorphism Property — become available
under Section 6's standing hypothesis.

Models: Example 6.5 `Ex DiExact` is `SnakeLean/LocallyDiscreteModel.lean`, Theorem 8.37
`T:LatticeModel` is `SnakeLean/LatticeModel.lean`, and Theorem 8.17 `T:SatModel` has its
2-category in `SnakeLean/AbCatModel.lean` and its (DI2) behind the Serre-quotient bridge. The
2-category of all abelian categories and exact functors is *not* one — Proposition 8.12
`P:AbCatFails` — and the ingredient its 2-categorical reading needs, that the Serre quotient of
an abelian category is abelian, is listed as future work in Mathlib's
`CategoryTheory/Abelian/SerreClass/Basic.lean`.

## Duality through the 1-cell dual

`SnakeLean/Op.lean`, and an `Opposite` section in each module that defines a notion. Every result
of the paper comes in a dual pair, and the paper discharges the second half by saying "dually".
The development makes that word literal: each notion is transported through Mathlib's 1-cell dual
`Bᵒᵖ` in the module that introduces it, and the dual statements are then applications of the
primal ones in `Bᵒᵖ`.

**Mathlib has `Bᵒᵖ` but not `Bicategory.Strict Bᵒᵖ`**, and every module here assumes strictness.
`strictOp` supplies it, and is all that `SnakeLean/Op.lean` contains. Its three isomorphism fields
reduce to `op2_eqToIso`, the observation that the dual sends `eqToIso` to `eqToIso`, proved by
`cases` on the equality; the associator field additionally needs `Iso.symm_symm_eq`, since
`op2_associator` reverses the triple.

Under `ᵒᵖ`, 2-monomorphisms and 2-epimorphisms swap, as do 2-kernels and 2-cokernels, normal
2-monomorphisms and normal 2-epimorphisms, and the two halves of a short 2-exact sequence. Being
null, essentially null, trivial, an equivalence, normal or antinormal is self-dual — and so are
2-z-exactness, homological self-duality and 2-di-exactness, which is the point: a theorem
hypothesising `IsHSD O` applies in `Bᵒᵖ` with no further argument.

The representable definitions transport directly rather than through a functor comparison. `Bᵒᵖ`
keeps the direction of 2-cells and wraps them in `Hom2`, whose `op2` and `unop2` are mutually
inverse by `rfl`, so `(precomp w f.op).Full` unwraps to `(postcomp w.unop f).Full` in four lines.

**`IsNull` and `IsEssNull` never mention the `HasBizero` instance** — they quantify over
factorisations through the object — so they transport with no reference to `bizeroOp`, and no
instance-mismatch arises between the bizero structure of `B` and the one induced on `Bᵒᵖ`.

Twenty-one results are derived rather than reproved this way, among them
`IsSES.isTrivial_iff_isEquiv1'`, `isNormalEpi_of_isTrivial`, `isTrivial_of_isTwoEpi_ladder` and
both dual halves of Proposition 4.22 `Third Iso`. What remains hand-written is `IsBipushout` — see
above — and duals whose proofs are a line or two, where a transport would not be shorter.

**A caution on implicit arguments.** `Quiver.Hom.op` is a wrapper that unification unfolds to
`Opposite.op`, so an instance argument determined by unifying an `op2`'d 2-cell may be sought at
the unfolded form and miss a `haveI` stated at the folded one. Passing the 1-cell explicitly
(`(r := u.op)`) fixes it. This bites three times in the development.

## The Pure Snake Lemma as data

`SnakeLean/PureSnake.lean`. Lemma 4.27 `Pure Snake Lemma` names its comparison: the "in
particular" clause says that `j : 2-Cok(f) → 2-Ker(h)`, characterised by
`2-ker(h) ∘ j ∘ 2-coker(f) ≅ b ∘ c`, is an equivalence, unique up to a unique invertible 2-cell
with that property. `IsPureSnake` in `SnakeLean/Dinversion.lean` records only that the
equivalence exists, which is all Section 4 needs.

**Section 6 needs the name, twice over.** The connecting 1-cell of the Snake Lemma is *defined*
as a composite of three such comparisons, so they must be nameable; and Section 7 proves them
2-natural, which is not a statement one can make about an equivalence with no name.
`PureSnakeComparison` bundles the comparison `j`, the 2-cell `e ≫ j ≫ m ≅ c ≫ b` characterising
it, and the proof that it is an equivalence. The uniqueness clause is
`PureSnakeComparison.nonempty_iso`, and it holds for the reason the paper gives — `e` is a
2-epimorphism and `m` a 2-monomorphism, so `comparison_unique` applies. It costs one line and it
is what makes the naturality of Section 7 statable.

No new mathematics: `exists_comparison` and `comparison_unique` already did the work in
`SnakeLean.Comparison`. What is new is that they are packaged with `IsPureSnake` into one object
that can be composed and compared.

Naturality of the comparison in a morphism of pure configurations is `SnakeLean/Naturality.lean`,
built on this hook; the notion of morphism it needs is the one Section 7 isolates.

## Exactness of the snake sequence at the middle

`SnakeLean/Snake.lean`. `exists_kerMap` produces the 1-cell induced on 2-kernels by a square
commuting up to an invertible 2-cell; `ā` and `b̄` are its two instances, for the left and right
squares of the ladder. `snake_isTwoKernel_barA` is Proposition 6.17 `P:KerBarA`, the second
assertion of Theorem 6.9 `Snake General 2D`: if `a = 2-ker(b)` and `c` is a 2-monomorphism, then
`ā = 2-ker(b̄)`. The proof is the paper's.

**Where the 2-dimensionality is essential.** The chase reaches `c ∘ f ∘ y ≅ 0` and needs
`f ∘ y ≅ 0`. That step is `IsEssNull.of_comp_isTwoMono` — the paper's `prop2monoreflectsnull` —
and it is the only move in the argument with no 1-categorical content, which is what the proof
of Proposition 6.17 says at that point. It is also the only place strongness of the bizero
object is used, as Remark 6.18 `Rem BarA Cost` records.

**The hypotheses are those of Remark 6.18.** No 2-di-exactness, no 2-z-exactness, no Pure Snake
Lemma, no normality of the verticals. Of the lower row only that `c` is a 2-monomorphism: it
need not be a 2-kernel, and `d` does not appear in the proof at all. So this half of the Snake
Lemma is available long before Section 6's standing hypotheses are in force, and the Lean
statement carries none of them.

**Both duals come from the transport.** `exists_cokMap` and `snake_isTwoCokernel_barD` are
three-line applications of their primal forms in `Bᵒᵖ` — the dual ladder is
`MorphismSES d.op c.op b.op a.op` with the verticals reversed and the two filling 2-cells
transposed. This is the sharpest return on the `Bᵒᵖ` transport, and it is why everything
here is stated in hypothesis form: a *given* 2-cokernel dualises to a 2-kernel on the nose,
whereas the *chosen* 2-kernel of `f.op` in `Bᵒᵖ` is only equivalent to the opposite of the chosen
2-cokernel of `f` in `B`.

**Elsewhere:** the connecting 1-cell is `SnakeLean/SnakeConnecting.lean`,
`SnakeLean/SnakeQuotient.lean` and `SnakeLean/SnakeDelta.lean`, next; the general case is
`SnakeLean/SnakeGeneral.lean`.

## The top half of the snake construction

`SnakeLean/SnakeConnecting.lean`. `snakeTop` builds the top-left corner of Figure
1 `Fig Constructing Snake`, as Section 6.8 `SS:Construction` does: `b ∘ 2-ker(g)` is a normal
2-monomorphism followed by a normal 2-epimorphism, hence antinormal, hence normal by (DI2);
factor it as `r : 2-Ker(g) ↠ I` then `i : I ↣ C`, and corestrict `i` to `ī : I ⟶ 2-Ker(h)`. This
is the only use of (DI2) in the top half.

**Lemma 6.10 `L:ImageOfBBar`.** That `(r, ī)` is a normal image factorisation of `b̄` is
`SnakeTop.nonempty_iso_bBar` together with `SnakeTop.isNormal_bBar`, and the proof is the
paper's: `r ≫ ī` and `b̄` both become `2-ker(g) ≫ b` after composing with the 2-monomorphism
`2-ker(h)`, so they agree up to an invertible 2-cell; and a normal 2-epimorphism followed by a
normal 2-monomorphism *is* a normal image factorisation. It is one line, but the next step —
`2-Cok(b̄) ≃ 2-Cok(ī)` by `CoKernel of Composite`, the lemma's last assertion — stands on it, and
so, further on, does the second half of Proposition 6.14 `P:Shape`.

`SnakeTop.comparison` is the first of the three connecting equivalences, `z₁`, obtained from the
Pure Snake Lemma applied to the rows `I ↣ C ↠ Q` and `2-Ker(h) ↣ C ↠ 2-Coim(h)`, which share the
middle object `C` with identity middle component. Because the comparison is now data
(`PureSnakeComparison`), it can be composed, which is what the connecting 1-cell needs.

**The bottom half is one line.** The paper obtains `s : 2-Img(f) → K` and `z₃` "by the mirror
construction in the lower half of Figure 1 `Fig Constructing Snake`". Here that is literal:
`snakeBot` is `snakeTop` applied to the ladder read in `Bᵒᵖ`, where the two rows exchange places
and the verticals reverse. Read back in `B` it factors `c ≫ 2-coker(g)` and produces the bottom
row `2-Cok(f) ↠ J ↣ 2-Cok(g)` of the figure, and the normality of `c̲` the paper notes there.

**Elsewhere.** The two rows of the third application of the Pure Snake Lemma are in
`SnakeLean/SnakeQuotient.lean`; the connecting 1-cell itself and 2-exactness at `2-Ker(h)` and
`2-Cok(f)` are in `SnakeLean/SnakeDelta.lean`.

## The routine verification

`SnakeLean/SnakeQuotient.lean`. The third and last application of the Pure Snake Lemma has rows
`2-Img(f) ↣ 2-Img(g) ↠ Q` and `K ↣ 2-Img(g) ↠ 2-Img(h)`. That the first is short 2-exact is,
in the paper's words, "the step the paper of record calls a routine verification", and Section
6.11 `SS:Connecting` writes it out in two halves: Lemma 6.12 `L:ImgMapNormal`, that the
comparison `ℓ : 2-Img(f) ↣ 2-Img(g)` (`j` here) is a normal 2-monomorphism, and Proposition
6.13 `P:RoutineVerification`, that `π : 2-Img(g) ↠ Q` is its 2-cokernel. Both are here, with
the paper's proofs.

`isTwoCokernel_imgMap` is Proposition 6.13. It is a four-step chase: `2-coim(f) ≫ j ≫ π` is null
because `a ≫ b` is; a 1-cell `w` killing `j` gives `2-coim(g) ≫ w`, which kills `a` and so
factors through `b = 2-cok(a)` as `v`; then `i ≫ v` is null because `r` is a 2-epimorphism and
`2-ker(g) ≫ 2-coim(g)` is null — this is the only place the factorisation `2-ker(g) ≫ b ≅ r ≫ i`
of the top-left corner is used; so `v` factors through `2-cok(i) = Q`, and cancelling the
2-epimorphism `2-coim(g)` finishes.

**It costs nothing**, and the paper states it at that cost: no 2-di-exactness, no homological
self-duality, no Pure Snake Lemma; of the upper row of the ladder only that `b` is a 2-cokernel
of `a`, never that `a` is a 2-kernel of `b`; and `i` need not be a normal 2-monomorphism nor `r`
a normal 2-epimorphism — Proposition 6.13 asks only that `r` and `e` be 2-epimorphisms.

**Why the shortcut is closed, and why it does not matter.** The tempting route is to observe that
`2-coim(g) ≫ π ≅ b ≫ 2-coker(i)` exhibits `π` as a composite of two normal 2-epimorphisms. That
would make `π` a normal 2-epimorphism and its 2-kernel the top row — but only if normal
2-epimorphisms were closed under composition, and that is **not** implied by 2-di-exactness. The
paper adds the closure by hand wherever it needs it, most visibly as Definition 9.4 `Def:NEC`, the
second standing hypothesis of the non-self-dual Snake Lemma. The chase never raises the question: it verifies the universal property directly.

**Normality of the comparison.** `isNormalMono_imgMap` is Lemma 6.12 `L:ImgMapNormal`, by the
paper's proof. The 1-cell being factorised is `a ≫ 2-coim(g)`, which is a normal 2-monomorphism
followed by a normal 2-epimorphism, hence antinormal, hence normal by (DI2). Comparing its normal
image factorisation with `2-coim(f) ≫ j` through the second assertion of Proposition 3.22
`Image Factorisation of Normal Map is Unique` makes `j` a normal 2-monomorphism, and `2-coim(f)`
a normal 2-epimorphism into the bargain — the lemma's second clause. This is the second and last
use of (DI2) in the construction.

**The bottom row is the dual**, and the paper's "the bottom row is short 2-exact by duality" is
literal here: `isTwoKernel_imgMapDual`, `isNormalEpi_imgMapDual` and `isSES_imgRowDual` are each
their primal form read in `Bᵒᵖ`.

## The connecting 1-cell

`SnakeLean/SnakeDelta.lean`. The paper sets `∂ = 2-ker(c̲) ∘ z ∘ 2-coker(b̄)`, where `z` is the
composite of the three connecting equivalences, and remarks that "we immediately have exactness of
the Snake Sequence in `2-Ker(h)` and `2-Cok(f)`". That is exactly right, and
`isExactAt_left_of_shape` and `isExactAt_right_of_shape` say how right: both are formal
consequences of the *shape* `∂ ≅ q ≫ z ≫ m` with `q` a 2-cokernel of `b̄`, `z` an equivalence and
`m` a 2-kernel of `c̲`. Neither statement mentions the snake.

They do not cost the same. 2-exactness at `2-Cok(f)` is a one-line term — a 2-cokernel followed by
an equivalence is a 2-cokernel, so `∂` already *is* a normal 2-epimorphism followed by
`2-ker(c̲)`, and nothing about `b̄` is used at all. 2-exactness at `2-Ker(h)` needs one thing more,
that `b̄` is normal, and that is where the identification of `ī` as the 2-image of `b̄` is finally
consumed.

`SnakeHalf` packages half of Figure 1 `Fig Constructing Snake` — the 2-image `I` of `b ∘ 2-ker(g)`,
the quotient `Q = C/I`, the induced `t`, the 2-cokernel of `b̄` and the first Pure Snake comparison,
together with the two comparisons `2-Img(g) ↠ Q` and `2-Img(g) ↠ 2-Img(h)`. The other half is this
one read in `Bᵒᵖ`, and `exists_snakeConnecting` runs both and assembles `∂`.

**`IsHSD` never appears as a hypothesis.** Every application of the Pure Snake Lemma below Section
6 is at `isHSD_of_twoDiExact`, so Proposition 6.3 `P:DiExactHSD` discharges it.

**A place where "dually" is not literal.** `snake_isExactAt_twoCokG` is *not* the `Bᵒᵖ` reading of
`snake_isExactAt_twoKerG`: `IsExactAt` asks for a normal image factorisation of its **first**
argument, so dualising exchanges the arguments too. What `Bᵒᵖ` delivers at `2-Cok(g)` is that `d̲`
is a 2-cokernel of `c̲` followed by a 2-monomorphism, and converting that into `IsExactAt O c̲ d̲`
goes through Proposition 4.4 `Exactness Self-Dual` — and needs `c̲` to be **normal**. The paper asserts
2-exactness of the snake sequence without ever saying that its six 1-cells are normal. Here
`IsNormal O c̲` comes out of the construction itself, as `SnakeTop.isNormal_bBar` read in `Bᵒᵖ`,
and the statement of `exists_snakeGeneral` asserts the normality of `d̲` as well — the one of
the six that no `IsExactAt` covers.

The linter reports that 2-exactness at `2-Ker(g)` and at `2-Cok(g)` in the special case uses
**neither (DI1) nor (DI2)**; both instances are `omit`ted.

2-naturality of `∂` in a morphism of ladders is `SnakeLean/Naturality.lean`.
`nonempty_iso_snakeComparison` — that `∂` does not depend on which comparisons the three
applications of the Pure Snake Lemma produce — is the hook it is built on, and the notion of
morphism it needs is the one Section 7 isolates.

## The general case

`SnakeLean/SnakeGeneral.lean`. Section 6.19 `SS:GeneralCase` reduces the general case of Theorem
6.9 `Snake General 2D` to the special one along Figure 2 `Fig Snake General`, in two steps — Lemma
6.20 `L:Restriction` and Proposition 6.21 `P:KerComparison` — and the module is those two steps
and the assembly, with the paper's proofs.

The reduction factors `a ≅ 2-coim(a) ≫ a'` and `d ≅ d' ≫ 2-img(d)`, so that `a'` is a 2-kernel of
`b` and `d'` a 2-cokernel of `c`, restricts `f` to `f' : 2-Coim(a) ⟶ X` and corestricts `h` to
`h' : C ⟶ 2-Img(d)`, and applies the special case to the middle ladder.

**The one genuinely 2-categorical step** is `isEssNull_comp_left_of_square`, used three times —
the count of Remark 6.22 `Rem General Cost`: a 1-cell killed by `a` is killed by `f`, because `c`
is a 2-monomorphism and therefore *reflects* null 1-cells. It produces `f'`, it produces the
comparison `2-Ker(2-coim(a)) ⟶ 2-Ker(f)`, and dually it produces `h'`.

**Lemma 6.20 `L:Restriction`** is `exists_restriction`: `f` restricts along `2-coim(a)` to a
normal `f'`, by the paper's proof — `f' ≅ 2-img(f) ∘ w` with `w ∘ 2-coim(a) ≅ 2-coim(f)`, and `w`
is a normal 2-epimorphism by the dual of Proposition 3.6 (ii). The two identifications
`2-Cok(f') ≃ 2-Cok(f)` and `2-Ker(h') ≃ 2-Ker(h)` the paper takes from Proposition 3.9 `CoKernel
of Composite` "in the form in which neither factor is required to be normal"; that form is
`isTwoCokernel_isTwoEpi_comp_iff`, stated for an arbitrary 2-epimorphism, and
`isTwoKernel_comp_isTwoMono_iff` for an arbitrary 2-monomorphism.

**Proposition 6.21 `P:KerComparison`** is `isNormalEpi_kerComparison`: `ā''` is a normal
2-epimorphism, by the paper's fourth application of the Pure Snake Lemma, to the rows

```
2-Ker(2-coim(a)) ↣ A ↠ 2-Coim(a)          2-Ker(f) ↣ A ↠ 2-Coim(f)
```

through the shared middle object `A`. Its comparison equivalence `2-Cok(v) ≃ 2-Ker(f')` is
characterised by exactly the triangle that characterises `ā''`, so `ā''` is a 2-cokernel followed
by an equivalence, hence a normal 2-epimorphism. As Remark 6.22 records, this needs no (DI2)
beyond homological self-duality, no image identification, and no 2-z-exactness — only a
2-cokernel of the comparison `v : 2-Ker(2-coim(a)) ⟶ 2-Ker(f)`.

`exists_snakeGeneral` is the Snake Lemma: a connecting 1-cell exists, the snake sequence is
2-exact at `2-Ker(g)`, `2-Ker(h)`, `2-Cok(f)` and `2-Cok(g)`, and `d̲` is normal. The last
conjunct is there because Definition 4.5 `Def:ExactSequence` asks every 1-cell of an exact
sequence to be normal, and `IsExactAt` supplies that only for its first argument: the four
exactness statements cover `ā`, `b̄`, `∂` and `c̲`, and the sixth 1-cell has to be said
separately. It comes free from the reduction, which exhibits `d̲` as a 2-cokernel of `c̲` followed
by a normal 2-monomorphism, and it is what makes the dual half of Theorem 9.19
`T:SnakeNonSelfDual` a transport (see below).

**Elsewhere.** The classical Snake Lemma, Corollary 6.24 `Snake General`, is deduced from
`exists_snakeGeneral` in `SnakeLean/Classical.lean`. The Normal Short Five Lemma, which the theorem
contains as the case in which the outer 2-kernels and 2-cokernels are trivial, is proved directly
in `SnakeLean/FiveLemma.lean` at strictly weaker hypotheses — it needs neither 2-di-exactness nor
2-z-exactness — and is not re-derived from here. 2-naturality is in `SnakeLean/Naturality.lean`.

## 2-naturality of the comparison

Naturality of the connecting 1-cell needs a notion of morphism between pure configurations, and
the paper isolates one, Definition 7.3 `Def:MorphismPure`. `SnakeLean/Naturality.lean` formalises
it, and it is cheaper than one would expect.

**A morphism of pure configurations carries no extra data.** A pure configuration is a morphism of
short 2-exact sequences whose middle component is an identity; a morphism of pure configurations is
a pair of morphisms of short 2-exact sequences, one between the two top rows and one between the
two bottom rows, **sharing their middle component**. `MorphismPure` has five 1-cells, four
invertible 2-cells and no axiom. In particular it imposes nothing on the verticals `f` and `h` of
the two configurations, because it does not have to: `MorphismPure.exists_piF` obtains
`πf : f ≫ πX ≅ πA ≫ f'` by reflecting a pasting of `ψc`, `θf`, `ψa` and `θf'` along the
2-monomorphism `c'`, and `MorphismPure.exists_piH` obtains `πh` by coreflecting along the
2-epimorphism `b`. Both reflections are unique, so both comparisons are determined by the data
already present. `MorphismPure.op` transports the notion, and `exists_piH` is `exists_piF` read in
`Bᵒᵖ`.

**Naturality of the comparison is `comparison_unique` in disguise.** `natural_comparison` whiskers
the two candidate 1-cells `u ≫ j'` and `j ≫ w` by the 2-epimorphism `e = 2-coker(f)` on the left
and the 2-monomorphism `m' = 2-ker(h')` on the right; both composites reduce to `c ≫ b ≫ πC`, one
through `P'.θ`, `ψc` and `ψb`, the other through `P.θ` alone. The 2-cell itself is
`naturalComparisonIso`, and `natural_comparison_whisker` is the paper's compatibility clause:
whiskered by `e` and `m'` it is the first pasting followed by the inverse of the second, so the
two pastings displayed in the paper's proof compose to the identity. Homological self-duality
enters only through the existence of the two comparisons — that they are *equivalences* plays no
part — and no 2-di-exactness is used anywhere in the module. `natural_comparison_unique` is the
injectivity half of the same full faithfulness.

**The four squares of the snake sequence that avoid `∂` need none of this.**
`nonempty_iso_kerMap_square` is a cube with a 2-monomorphism at one corner: five commuting faces
force the sixth. It is stated for an arbitrary 2-monomorphism rather than for a 2-kernel, since
that is all the proof consumes, and `nonempty_iso_cokMap_square` is its `Bᵒᵖ` reading.

**What remains.** `exists_normalImageMap` supplies the comparison induced on normal images, which
is the one step in building a morphism of pure configurations out of a morphism of ladders that is
more than bookkeeping: `pA ≫ e'` is factored through the 2-cokernel `e` after reflecting nullity
along `m'`, and the second square follows by coreflecting along `e`.
`nonempty_iso_snakeComparison_square` and `nonempty_iso_connecting_snake` then paste the three
Pure Snake comparisons — with `nonempty_iso_inv_square` handling the inverted middle one — into
2-naturality of `∂` itself. What is *not* formalised is the assembly of the three morphisms of pure
configurations out of a single morphism of ladders, which is the one paragraph the paper compresses
into "the other two configurations are handled in the same way"; everything the pasting needs of
them appears as explicit hypotheses.

## Serre classes and where (DI2) bites in `AbCat`

`SnakeLean/SerreJoin.lean`. This module is not part of the 2-categorical development: it imports
Mathlib alone and nothing from `SnakeLean`. It exists because the candidate model of a 2-di-exact
2-category that suggests itself — the 2-category `AbCat` of abelian categories, exact functors and
natural transformations — fails condition (DI2), which is Proposition 8.12 `P:AbCatFails`, and
this module locates where.

Unwound in `AbCat`, condition (DI2) says this. A normal 2-monomorphism is the inclusion of a
Serre subcategory `K ⊆ C` and a normal 2-epimorphism is a Serre quotient `C ↠ C/S`, so the
antinormal composite is `K ↪ C ↠ C/S`. It always factors as the Serre quotient `K ↠ K/(K ⊓ S)`
followed by an exact functor `K/(K ⊓ S) → C/S`, and that second functor is always fully faithful
(Lemma 8.10 `L:FullyFaithful`), because for `a` in `K` every subobject and every quotient of `a`
in `C` is already in `K`, so the two filtered colimits computing the hom-sets have the same index
category and the same terms. The first factor is a normal 2-epimorphism, which needs `K ⊓ S` to be
a Serre class. So (DI2) holds in `AbCat` if and only if the second factor is a normal
2-monomorphism — that is, if and only if its essential image is a Serre subcategory of `C/S`.

Mathlib has `ObjectProperty.IsSerreClass` but records no closure of Serre classes under the
lattice operations, so neither `K ⊓ S` nor the join is available. Both are proved here:
`IsSerreClass (P ⊓ Q)` and `serreJoin`, the latter defined by its universal property rather than
as a lattice-theoretic infimum, which keeps every closure proof a one-liner.

The essential image is `serreSaturation S K`, the `S`-saturation of `K` of Definition 8.8
`D:Saturation` in its second form: the objects joined to an object of `K` by a span of morphisms
that are isomorphisms modulo `S`, which is exactly what it means to become isomorphic to an
object of `K` in `C/S`. The module proves `K ≤ serreSaturation S K`, `S ≤ serreSaturation S K`
and `serreSaturation_le`, that the saturation is contained in every Serre class containing `K`
and `S`; hence `isSerreClass_serreSaturation_iff`, that the saturation is a Serre class exactly
when it equals the join — Proposition 8.9 `P:Saturation`, except for its clause that the
saturation is closed under subobjects and under quotients, which is not formalised.

That is the reduction, Proposition 8.11 `P:DIabcat`. **Condition (DI2) holds in `AbCat` if and
only if, for all Serre classes `K` and `S` in an abelian category, the `S`-saturation of `K` is
again a Serre class** — equivalently, if and only if every object carrying a finite filtration
with subquotients alternately in `K` and `S` already carries one with just three steps, in `S`,
`K` and `S`. Only closure under extensions is at stake, and it is not proved here: it is false,
which is Proposition 8.12 `P:AbCatFails`.

The chase that `serreSaturation_le` needs turns out to cost nothing. `prop_iff_of_isoModSerre`
says that membership in a Serre class transfers along any morphism whose kernel and cokernel lie
in that class, and it needs no image factorisation: `isoModSerre` is multiplicative, so composing
with a zero morphism on either side reduces the statement to `isoModSerre_zero_iff`. The linter
then reports that neither `serreSaturation_le` nor `serreSaturation_le_serreJoin` uses that `K`
is a Serre class at all.

`isSerreClass_serreSaturation_of_twoStep` is the criterion in the form in which it is checkable:
if every object of the join carries a *two-step* filtration, in either order — a subobject in `S`
with quotient in `K`, or a subobject in `K` with quotient in `S` — then the saturation is Serre
and (DI2) holds. Stated with the right primitive (an epimorphism whose kernel lies in `S`, or a
monomorphism whose cokernel lies in `S`) each half is three lines, because that primitive *is*
the `isoModSerre` condition. For finitely generated modules over a commutative Noetherian ring
the first half holds, with the `S`-torsion submodule as the subobject; the counterexample fails
it, as it must.

**Not formalised.** That `serreSaturation S K` really is the preimage of the essential image of
`K` in `C/S`, and the identification of 2-cokernels in `AbCat` with Serre quotients (Proposition
8.5 `P:AbCatCokernel`). Both need the Serre quotient as an abelian category, which Mathlib lists
as future work in `Mathlib/CategoryTheory/Abelian/SerreClass/Basic.lean`. The 2-kernel half,
Proposition 8.4 `P:AbCatKernel`, needs no quotient and is `isTwoKernel_kerIncl` in
`SnakeLean/AbCatModel.lean` below. Whether
the saturation is closed under extensions is settled in `SnakeLean/CondAS.lean` below, under a
hypothesis on the ambient category that the counterexample violates.

## `AbCat` is not (DPN): an asymmetric pair of Serre classes

`SnakeLean/SerreAsymmetry.lean`, also Mathlib-only: the module-theoretic content of Section 9.21
`SS:NSDAbCat`, Proposition 9.25 `P:AbCatNotDPN`. Once `AbCat` is known not to be 2-di-exact, the
natural fallback is the weaker hypothesis **(DPN)** of `SnakeLean/NonSelfDual.lean` — dinversion
preserves normality — under which the Pure Snake Lemma is still available. Unwound in `AbCat` by
the reduction above, (DPN) says that for all Serre classes `K` and `S`, the `S`-saturation of `K`
is a Serre class **if and only if** the `K`-saturation of `S` is: the join is reached by an
`S,K,S` filtration exactly when it is reached by a `K,S,K` one. `asymmetry` refutes it.

The counterexample of Proposition 8.12 `P:AbCatFails`, the Nakayama algebra on the cyclic quiver
`1 → 2 → 1` with `rad³ = 0`, cannot do the job (Remark 9.24 `Rem NSD Symmetric`): the rotation of
the quiver exchanges its two vertices and carries `K` to `S`, so the two saturations are carried
into one another and both fail together. What breaks the tie is one further relation. `lam` is the five-dimensional algebra
`Λ = kQ/(αβ)`, presented here as the matrices `!![a, 0, 0; e, a, d; c, 0, b]` — its action on the
indecomposable projective at vertex `1` — with `K` and `S` the modules annihilated by the two
idempotents.

Both halves are short, and neither mentions the quotient category, which is why this counterexample
is formalisable where the earlier one is not.

* `serreSaturation_KK_SS`: **every** `Λ`-module carries a filtration with subquotients in `K`, `S`,
  `K`. The middle step is `nTwo`, the elements annihilated by `α`, and that this is a submodule at
  all is the relation, through `exists_al_mul`: `α · r` is a scalar multiple of `α` for every `r`,
  because the only path that could interfere is the one the relation kills. Modulo `nTwo` the
  arrow `β` then acts as zero, which supplies the remaining two layers. No finiteness is used
  anywhere, so this holds for arbitrary modules, not just finite-dimensional ones.
* `not_serreSaturation_SS_KK`: the free module of rank one carries no filtration in the order
  `S`, `K`, `S`. The invariant is the action of the length-two path `p = βα`. It annihilates every
  module in `K` (`pa_smul_eq_zero`), and being fixed by `e₁` on both sides it is carried unchanged
  along both legs of any span of morphisms that are isomorphisms modulo `S` — four lines, with no
  subobject lattice to inspect. On the free module `p` acts as multiplication by `p ≠ 0`.

`asymmetry` puts the two together through `isSerreClass_serreSaturation_iff`. A by-product,
proved in the paper and not here: `AbCat` *is* homologically self-dual (Proposition 9.23
`P:AbCatHSD`), since an essentially null antinormal composite forces `K ⊆ S` and then the
`K`-saturation of `S` is `S` itself. So `AbCat` separates `IsHSD` from `DPN`, and `isHSD_of_dpn`
is not reversible — Corollary 9.26 `C:HSDstrict`.

`isSerreClass_annBy`, that the modules annihilated by an idempotent form a Serre class, is general
and independent of all of this; idempotence enters only in closure under extensions.

## Condition (AS), and where the saturation is a Serre class

`SnakeLean/CondAS.lean`. The reduction above leaves one question: for which abelian categories is
the `S`-saturation of a Serre class `K` again a Serre class — which abelian categories are
*saturated*, Definition 8.15 `D:SAT`? The counterexample says that "all of them" is wrong, so the
answer has to be a condition, and this module is Section 8.18 `SS:ModelAS`, where the paper
proves that one condition suffices:

> **(AS)** For every Serre class `T` and every object `X`: if every nonzero subobject of `X` has a
> nonzero subobject in `T`, then `X` lies in `T`.

This is `CondAS`, Definition 8.20 `D:AS`. The converse holds in any abelian category — `subEssential_of_prop` — so under
(AS) the two properties coincide and the condition is not vacuous.

(AS) is the classical statement that the support of an object is the specialisation-closure of
its associated points, written without mentioning either. In Kanda's atom spectrum
(*Classifying Serre subcategories via atom spectrum*, Adv. Math. **231** (2012), 1572–1588) the
translation runs: Serre classes of a noetherian abelian category correspond to the open subclasses
of `ASpec` (Theorem 4.3); an atom lies in the open subclass of `T` exactly when some monoform
representative has a nonzero subobject in `T`; and every nonzero subobject of a noetherian object
has a monoform subobject (Theorem 2.9), so "every nonzero subobject of `X` meets `T`" is
`AAss X ⊆ ASupp T` and "`X` lies in `T`" is `ASupp X ⊆ ASupp T`. That dictionary, and the two
traps it walks into, is Remark 8.22 `R:Atoms`; nothing uses it, there or here. For `mod R` over a
commutative noetherian ring, and for `Coh X` over a noetherian scheme, (AS) holds (Propositions
8.24 `P:ModAS` and 8.26 `P:CohAS`); in a category of finite length it forces every simple
subquotient to be a subobject, and so holds only in the semisimple case (Remark 8.28
`Rem WhereNot`). The counterexample is a length-three uniserial object, and
`prop_of_condAS_of_forall_mono` is (AS) in exactly the shape it violates.

`isSerreClass_serreSaturation_of_condAS` is Proposition 8.21 `P:ASimplies`: **a noetherian
abelian category satisfying (AS) is saturated** — the `S`-saturation of `K` is a Serre class, for
every pair of Serre classes. The proof is the paper's, and its two ingredients are each proved
here.

`exists_epi_torsionFree` is the `S`-torsion presentation. A noetherian object has a *maximal*
subobject lying in `S` (`exists_maximalSerreSub`; maximal is enough, and the largest — which
would need the sum of two subobjects in `S` to lie in `S` — is never used), and the cokernel of a
maximal one has no nonzero subobject in `S`: such a subobject pulls back to a strictly larger
subobject of `M` lying in `S`, and the pullback lies in `S` because `isoModSerre` is stable under
base change and `prop_iff_of_isoModSerre` transfers membership along it. That presentation is
exactly the `TwoStepSK` half of `isSerreClass_serreSaturation_of_twoStep`, Proposition 8.19
`P:TwoStep`.

`exists_nonzeroSub_of_serreJoin` supplies what (AS) is then applied to: a nonzero object of the
join of `K` and `S` has a nonzero subobject lying in `K` or in `S`. The paper reads this off the
first nonzero step of a finite filtration with subquotients in `K` or `S`, the join being the
class of objects carrying one. Here the join is defined by its universal property, so this means
producing a Serre class with that property, and the naive candidate — every nonzero *subobject* meets `K ∪ S` — is closed under subobjects and extensions
but not under quotients. `SQEssential` repairs it by quantifying over sub*quotients*, and is a
Serre class for any `P` whatever. Its closure under extensions is the one real diagram chase in
the file: for a nonzero subquotient `Z` of the middle term, either the kernel part survives in
`Z`, and its image is a nonzero subquotient of `X₁` sitting inside `Z`, or it dies, and then `Z`
is a quotient of the coimage of `Y ⟶ X₃`, hence a subquotient of `X₃`.

The main theorem then reads: present `c` as `S`-torsion over a torsion-free `N`, take a nonzero
subobject `W` of `N`, find in it a nonzero subobject lying in `K` or in `S`, exclude `S` because
`N` is torsion-free, and conclude `N ∈ K` by (AS).

**Not formalised.** The atom dictionary above, so the equivalence of `CondAS` with the statement
about `ASupp` and `AAss`; that `Coh X` satisfies (AS) — Lemma 8.25 `L:OneAss` and Proposition
8.26 `P:CohAS`, which need Gabriel's classification, the description of the support of a coherent
sheaf by its associated points, and the Artin–Rees lemma, none of which Mathlib has for sheaves;
and the counterexample of Proposition 8.12, which lives in a Serre quotient category. What (AS)
buys the paper is Proposition 8.21 `P:ASimplies`, hence — with Propositions 8.24 `P:ModAS` and
8.26 `P:CohAS` — Corollary 8.27 `C:Populated`: Theorem 8.17 `T:SatModel` makes the saturated
abelian categories a 2-di-exact 2-category on the strength of `P:SATclosed` alone, and (AS) is
what puts every `mod R` and every `Coh X` into it.

## The witness: finitely generated modules

`SnakeLean/CondASModule.lean`. `CondAS.lean` shows what (AS) buys but not that anything satisfies
it, and (AS) is not a vacuous condition to check: it fails for `ModuleCat ℤ`, where `ℚ` has every
nonzero submodule meeting the Serre class of finitely generated modules without being finitely
generated itself — the example after Definition 8.20. The noetherian restriction is the point,
and this module is Proposition 8.24 `P:ModAS`:

**`condAS_fgModuleCat` — `CondAS (FGModuleCat R)` for `R` commutative noetherian**

together with `isSerreClass_serreSaturation_fgModuleCat`, which composes it with
`isSerreClass_serreSaturation_of_condAS` into an unconditional statement, the module half of
Corollary 8.27 `C:Populated`: for finitely generated modules over a commutative noetherian ring,
the `S`-saturation of a Serre class `K` is a Serre class, for every pair.

The proof classifies nothing, as the paper's does not — the paragraph after Proposition 8.24
makes the point. Gabriel's theorem is not used, and neither is Kanda's; associated primes do all
the work, in three steps, of which the first two are the paper's.

1. `prop_quotient_of_mem_associatedPrimes`. For `p` associated to `M` there is an injection
   `R ⧸ p ↪ M`, so the hypothesis of (AS) hands back a nonzero submodule `J` of `R ⧸ p` lying in
   `T`. Now `R ⧸ p` is a **domain** and `J` is an ideal of it, so multiplication by any nonzero
   element of `J` embeds `R ⧸ p` into `J`; closure under subobjects puts `R ⧸ p` in `T`. That is
   `exists_injective_of_ne_bot`.
2. `exists_associatedPrimes_le_of_mem_support`. Every prime in the support of `M` contains an
   associated prime — localise at it, take an associated prime of the localisation and comap it,
   the pattern of Mathlib's `minimalPrimes_annihilator_subset_associatedPrimes`. Since `R ⧸ p` is
   then a **quotient** of `R ⧸ q`, closure under quotients gives `R ⧸ p ∈ T` for every `p` in the
   support.
3. `prop_of_subEssential`. A *maximal* submodule `N₀` of `M` lying in `T` exists, `M` being
   noetherian, and it is everything: otherwise `M ⧸ N₀` is nonzero, hence has an associated prime
   `p`, which lies in the support of `M`; the preimage of the copy of `R ⧸ p` inside `M ⧸ N₀` is
   an extension of `R ⧸ p` by `N₀`, so it lies in `T` and is strictly larger. This replaces the
   paper's last step, the filtration of `M` by primes (Matsumura, Theorem 6.4), which Mathlib
   does not have, and uses only the ascending chain condition.

Steps 1 and 3 both need the hypothesis of (AS) read in submodule language rather than in terms of
monomorphisms; `exists_le_prop_of_subEssential` does that translation once.

Two pieces of infrastructure come with it. `ofFG` transports a Serre class of `FGModuleCat R` to
one of `ModuleCat R` — the finitely generated modules lying in it — which is what lets the
mathematics be done in `ModuleCat`, where `mono_iff_injective` and the short-exact-sequence
dictionary are available, and then transferred back along the fully faithful `forget₂`. And
`isNoetherianObject_of_fullyFaithful` proves that a fully faithful functor preserving monomorphisms
reflects noetherian objects, which with `ModuleCat.subobjectModule` gives
`isNoetherianObject_fgModuleCat` — the noetherian half of Proposition 8.24 — and so discharges
the other hypothesis of the saturation theorem. Mathlib has no `IsNoetherianObject` instance for
module categories; these two are the general statements behind it.

**Not formalised.** The geometric half of Corollary 8.27 — Lemma 8.25 `L:OneAss` and Proposition
8.26 `P:CohAS`, that `Coh X` is a noetherian abelian category satisfying (AS) — for which Mathlib
has no coherent sheaves at all.

## (SAT), and its two closure properties

`SnakeLean/SerreSubcategory.lean` and `SnakeLean/SerreQuotient.lean`. The two modules above settle
where (DI2) bites and exhibit a category where it holds. What makes a *2-category* out of that is
Proposition 8.16 `P:SATclosed`: the class cut out by

**(SAT)** — for all Serre classes `K` and `S`, the `S`-saturation of `K` is a Serre class

is closed under the two constructions that produce 2-kernels and 2-cokernels. `CondSAT` is that
condition, and the two modules prove the two halves.

**The Serre subcategory half** is unconditional. It needs the statement to be expressible first,
and Mathlib does not record that a Serre subcategory is an abelian category, so
`abelianFullSubcategory` proves it: a Serre class is closed under binary products, being closed
under extensions and a binary product being a biproduct, and under equalisers and coequalisers,
those being a subobject and a quotient; the inclusion then creates finite limits and colimits, and
`Abelian.ofCoimageImageComparisonIsIso` transfers the comparison isomorphism back along the fully
faithful inclusion. What follows is the dictionary — `isSerreClass_inverseImage` in `SerreJoin.lean`
for the preimage, which needs only exactness and so serves the quotient as well, and
`isSerreClass_map_ι` for the essential image — and then

**`condSAT_fullSubcategory` — `CondSAT C → CondSAT B.FullSubcategory` for `B` a Serre class**

The proof is not the paper's, which goes through Lemma 8.10 `L:FullyFaithful` — the induced
`B/S → A/S` is fully faithful and reflects isomorphisms, so the saturation in `B` is the trace of
the one in `A` — and so through Serre quotients. The one here needs no theory of Serre quotients at
all: the saturation is defined by a span of morphisms that are isomorphisms modulo `S`, and both
the span and the two Serre classes transport along the inclusion. Push `K'` and `S'` forward, saturate upstairs, pull
back; that is a Serre class containing `K'` and `S'`, hence their join, and an object of it lies in
the saturation computed downstairs because the apex of its span is already in `B` — being joined to
an object of `B` by a morphism whose kernel and cokernel lie in `B`.

**The Serre quotient half** is where Mathlib's gap is. The Serre quotient exists there only as a
localisation; that it is abelian is listed as future work. So the quotient enters as `IsSerreQuotient`,
a three-field hypothesis: the projection is essentially surjective, it annihilates `S`, and a Serre
class of `A` containing `S` has a Serre class as its essential image. The third field is one half of
Gabriel's correspondence.

**`condSAT_of_isSerreQuotient` — `IsSerreQuotient S q → CondSAT A → CondSAT D`**

The proof is the paper's: pull the two Serre classes back along `q`, saturate upstairs, push
forward by the correspondence, and read the containment off a span to which `q` is applied. An
earlier proof went through the identification `(A/S)/q(T) ≃ A/T`; neither the paper nor the module
uses it any more, and the proof below consumes nothing but the three fields.

**Not formalised.** That the Serre quotient is abelian, and so that `IsSerreQuotient` is satisfied
by anything: the hypothesis is discharged nowhere in the development, which is the Mathlib gap
above. Size (Convention 8.1 `Conv Size`) is not tracked in Lean at all.

## The 2-category, and how far it can be checked

`SnakeLean/AbCatModel.lean`. Theorem 8.17 `T:SatModel` asserts that the abelian categories
satisfying (SAT), with exact functors and natural transformations, form a 2-di-exact 2-category
`Sat`, a full sub-2-category of the paper's `AbCat`. This module builds both, as two instances of
one construction, and proves what does not depend on Serre quotients.

`AbCatClass` is a class of abelian categories — a property containing the zero category and
inherited by Serre subcategories, the two closure conditions the constructions consume, exactly as
`LatticeClass` is for the lattice model — and `AbCatOf C` bundles an abelian category with its
membership; `AbCatClass.all` gives `AbCat` and `AbCatClass.sat` gives `Sat`. `AbCatHom` bundles a
functor with its additivity and its preservation of finite limits and colimits; the 2-cells are
natural transformations of the underlying functors. Mathlib's `InducedBicategory` gives *full*
sub-bicategories only — its own TODO notes that cutting the 1-cells down needs more thought — so
the `Bicategory` instance is written out, with the composition, whiskering and coherence data of
`Cat` and the associators and unitors identities; `strictAbCatOf` then holds by `rfl`.

The bizero object needs an abelian category with one object, which Mathlib does not have either;
`ZeroCat` is built from `PUnit` and made abelian through `Abelian.ofCoimageImageComparisonIsIso`,
every morphism being an isomorphism. `isStrong_zeroAbCatOf`, for every class and so in `AbCat` (Proposition 8.3
`P:AbCatBizero`), is then the observation that a null
1-cell factors through it, so takes every object to a zero object, so admits exactly one natural
transformation to any parallel null 1-cell.

**`isTwoKernel_kerIncl` — the 2-kernel of an exact functor `F` is the full subcategory of the
objects `F` annihilates — Proposition 8.4 `P:AbCatKernel`, for every class and so in `AbCat`**

The class is Serre by `isSerreClass_inverseImage`, the subcategory is again an object of the
2-category by the closure condition of the class (`condSAT_fullSubcategory` for `Sat`), the
universal property is `ObjectProperty.lift` — exact,
because the inclusion reflects finite limits and colimits — and `IsTwoMono` is
`Functor.FullyFaithful.whiskeringRight`. With the uniqueness of 2-kernels already in the
development this gives `exists_serreClass_of_isNormalMono`: **a normal 2-monomorphism is, up to
equivalence, the inclusion of a Serre subcategory** — the 2-monomorphism half of Corollary 8.6
`C:AbCatNormal`, and the step the proof of Proposition 8.11 `P:DIabcat` opens with.

**Not formalised, and why.** The 2-cokernel (Proposition 8.5 `P:AbCatCokernel`) is a Serre
quotient, which Mathlib has only as a localisation; hypothesising it would mean hypothesising its
universal property, which is the whole statement. Condition (DI2) — the reduction of Proposition
8.11 — needs four further facts, all about Serre quotients: that the projection is a 2-cokernel
(8.5), that the essential image of `K` in `A / S` is the `S`-saturation of `K` (Definition 8.8
`D:Saturation` with Proposition 8.9 `P:Saturation`), that a fully faithful exact functor with
Serre essential image is an equivalence onto the corresponding subcategory (Lemma 8.10
`L:FullyFaithful`), and Gabriel's correspondence. What is left of (DI2) once those are set aside
is exactly condition (SAT), and that is machine-checked. So `T:SatModel` is not claimed, and
neither are Corollary 8.6, Proposition 8.11 and Proposition 8.12, all of which sit behind the
same bridge.

## A model

`SnakeLean/LocallyDiscreteModel.lean`. Every result of Sections 2 to 6 is conditional on a
strong bizero object satisfying (DI1) and (DI2). `AbCat` is not one — Proposition 8.12
`P:AbCatFails`, whose module-theoretic content is `SnakeLean/SerreJoin.lean`.

A model does exist, and cheaply: Example 6.5 `Ex DiExact`. Take any abelian category `C` and give it the locally discrete
2-category structure, in which the only 2-cells are identities. Then the zero object is a strong
bizero object — two parallel null 1-cells are both zero, hence equal, hence carry exactly one
2-cell — and everything else discretises: `isEssNull_locallyDiscrete_iff` says a 1-cell is
essentially null exactly when it names a zero morphism, `isTwoKernel_of_lift` and
`isTwoCokernel_of_desc` say 2-kernels are kernels and 2-cokernels cokernels, and
`isTwoMono_locallyDiscrete_iff` and its new dual say 2-monomorphisms are monomorphisms and
2-epimorphisms epimorphisms.

Condition (DI1) is then that every morphism has a kernel and a cokernel. Condition (DI2) is the
epi-mono factorisation: `isNormal_locallyDiscrete` proves that **every** 1-cell is normal, since
in an abelian category every monomorphism is the kernel of its cokernel and every epimorphism
the cokernel of its kernel, so the image factorisation of a morphism is a normal 2-epimorphism
followed by a normal 2-monomorphism. (DI2) asks less than that and follows at once.

So `HasBizero`, `IsStrong`, `TwoZExact` and `TwoDiExact` are all instances for this object, and
with them `isHSD_locallyDiscrete` and `isPureSnake_locallyDiscrete`: homological self-duality
and the Pure Snake Lemma are not vacuous, and `exists_snakeGeneral` has all four of its
typeclass hypotheses discharged.

The model is one-dimensional, so it does not show that the theory has content beyond the
classical Snake Lemma. It does show that the axioms are consistent, which is what was missing.

That `exists_snakeGeneral` read in this model *is* the classical Snake Lemma, Corollary 6.24
`Snake General`, is `exists_snakeClassical` in `SnakeLean/Classical.lean`: the translation of a
commutative ladder into a `MorphismSES` and of `IsExactAt` back into `ShortComplex.Exact`
(see [the classical Snake Lemma](#the-classical-snake-lemma)).

## The classical Snake Lemma

`SnakeLean/Classical.lean`, checking Corollary 6.24 `Snake General`. The corollary recovers the
Snake Lemma of homological algebra from Theorem 6.9 by reading an abelian category as a locally
discrete 2-category, and `exists_snakeClassical` is that reading carried out over the model of
`SnakeLean/LocallyDiscreteModel.lean`: a commutative ladder in an abelian category with exact
rows, `b` an epimorphism and `c` a monomorphism, has a connecting morphism `δ : Ker h ⟶ Cok f`
with the six-term sequence exact at its four interior objects. No part of the argument is
repeated; the mathematics is `exists_snakeGeneral`, and the classical statement is obtained from
it rather than alongside it. Mathlib's own Snake Lemma
(`Mathlib.Algebra.Homology.ShortComplex.SnakeLemma`) is not used, which is the point.

The work is a translation in both directions. Going in, a commutative ladder becomes a
`MorphismSES` — in a locally discrete 2-category the two filling 2-cells *are* the commuting
squares — and kernels become 2-kernels by `isTwoKernel_of_lift`; the bottom row has to be handed
over in coimage form, `d = cokernel.π c ≫ cokernel.desc c d w`, with the mono half from
`exact_iff_mono_cokernel_desc`. Coming out, `isExactAt_locallyDiscrete_iff` turns `IsExactAt`
back into Mathlib's `ShortComplex.Exact`, in both directions: `IsExactAt f g` says `f` factors
as a normal 2-epimorphism followed by a 2-kernel of `g`, and in an abelian category that is
exactly `exact_iff_epi_kernel_lift`. **The verticals need no hypothesis**: every morphism of an
abelian category is normal (`isNormal_locallyDiscrete`), so the theorem's normality condition on
`f`, `g`, `h` is automatic, which is what the corollary says.

**Not carried across:** the corollary's last clause, that `ā` is a kernel of `b̄` when `a` is a
kernel of `b`, and dually. It is Proposition 6.17 `P:KerBarA`, machine-checked as
`snake_isTwoKernel_barA`, and costs another translation of the same kind, no further mathematics.

## A second model: modular lattices

`SnakeLean/LatticeModel.lean`, checking Section 8.30. The complete modular
lattices, join-preserving maps and instances of the pointwise order form a locally ordered
2-category `ModSup` — hom-categories are posets, built on `Preorder.smallCategory`, so every
coherence datum is discharged by thinness — and it is 2-di-exact. Unlike the locally discrete
model its 2-cells are not all identities, so the two-dimensional universal properties quantify
over something; unlike `Sat` its invertible 2-cells are all identities, so the two models are
complementary.

The one-element lattice is a strong bizero object (`isStrongSup`, Proposition 8.32 `P:SupBizero`). The 2-kernel of `f` is
the inclusion of the down-segment `↓(⋁{x | f x = ⊥})` and the 2-cokernel is `x ↦ x ⊔ f ⊤`
onto the up-segment `↑(f ⊤)` (`isTwoKernel_segIncl`, `isTwoCokernel_upProj`, giving
`twoZExactSup`, Proposition 8.33 `P:SupKernels` — Mathlib has the complete lattice on `Set.Iic`
but not on `Set.Ici`, which the module supplies). Up to isomorphism these are *all* the normal 2-monomorphisms and normal
2-epimorphisms (`exists_isEquiv1_of_isTwoKernel` and its dual, Corollary 8.34 `C:SupNormal`; the
key step is that in a locally ordered 2-category fully faithful 1-cells cancel on 1-cells,
`cancel_isTwoMono`). An antinormal 1-cell is therefore, up to isomorphism, a map
`↓a ⟶ ↑b`, `x ↦ x ⊔ b` (Proposition 8.35 `P:SupAntinormal`, `exists_form_of_isAntinormal`),
and `isNormal_segIncl_comp_upProj` factors it as the join-projection onto `[a ⊓ b, a]` followed
by the transposition `[a ⊓ b, a] ≅ [b, a ⊔ b]` and the inclusion of `[b, a ⊔ b]`: **condition
(DI2) is Dedekind's transposition principle** (Proposition 8.36 `P:SupModular`), and
`transposeIso` is the one place modularity is used. `twoDiExactModSup` then discharges (DI2)
(Theorem 8.37 `T:LatticeModel`), and
`isHSD_modSup`, `isPureSnake_modSup` follow; `exists_snakeGeneral` has all four typeclass
hypotheses discharged over `ModSup`, a Snake Lemma for modular lattices.

The 'only if' half of Proposition 8.35 — a normal `c_{a,b}` has an invertible transposition —
is `transposes_of_isNormal`, read off at `⊥` rather than through the 2-kernel of `c_{a,b}` as
in the paper; with `isModularLattice_iff_forall_transposes` that gives the converse direction of
Proposition 8.36, a lattice all of whose antinormal 1-cells are normal is modular, and lifted to a
class of lattices it is `isModularLattice_of_twoDiExact`: with
`twoDiExact_iff_forall_isModularLattice` the (DI2) half of Proposition 9.29 `P:SupClass` holds
in both directions. The class of *all* complete lattices is `allClass`, and `SupAll` is the
paper's `Sup`; that it is *not* 2-di-exact, the last clause of Proposition 8.36, is
`not_twoDiExact_supAll` in `SnakeLean/Pentagon.lean` ([below](#the-pentagon)).

**Not formalised.** As in the locally discrete model, reading `exists_snakeGeneral` back into a
concrete statement about ladders of lattices — the element-level Snake Lemma of Remark 8.40
`Rem Lattice Snake`, and the counterexample of Remark 8.43 `Rem Lattice Sharp` — is not
attempted. The last clause of Proposition 8.38 `P:SupNotDPN`, that `Sup` fails (DPN) with the
pentagon as a five-element witness, is `SnakeLean/Pentagon.lean` ([below](#the-pentagon)); the
rest of that proposition — homological self-duality and both composition properties — is
`isHSD_sup`, `normalEpiCompSup` and `normalMonoCompSup` in `SnakeLean/LatticeNSD.lean`.

## Modular pairs and transpositions

`SnakeLean/ModularPair.lean`, checking Lemma 9.30 `L:ModularPairs` and the lattice-theoretic
content of Proposition 8.36 `P:SupModular`. Mathlib has `IsModularLattice` and the four semimodularity classes
but no notion of a **modular pair**, which is what both hypotheses of the Snake Lemma turn into
on a lattice; everything in the module is new.

The transposition of `a` and `b` is `T(a, b) : [a ⊓ b, a] → [b, a ⊔ b]`, `x ↦ x ⊔ b`, with right
adjoint `z ↦ z ⊓ a` (`transpose_gc`). `Transposes a b` says that the unit and the counit of that
adjunction are equalities, and it is stated **elementwise** — as inequalities constraining
elements of the ambient lattice, not as invertibility of a map between bundled interval types.
That convention is what makes `transposes_coe_Icc` true (the definition quantifies only over
elements between `x ⊓ y` and `x ⊔ y`, so an interval containing `x` and `y` contains all of
them) and what reduces the passage to the order dual, `transposes_toDual`, to exchanging the
unit with the counit. `transposes_iff_bijective` and `transposeOrderIso` recover the bundled
form, so nothing is lost.

`transposes_iff` is Lemma 9.30 `L:ModularPairs`: the transposition at `(a, b)` is invertible if and only if
`ModularPair b a` and `DualModularPair a b` — the unit is an equality in the first case, the
counit in the second. `isModularLattice_iff_forall_transposes` is Dedekind's transposition
principle, and in the paper it is condition (DI2) read on a lattice; only the units are used in
the direction that builds `IsModularLattice`, so the hypothesis could be weakened to
`∀ a b, ModularPair a b`. `transpositionSymmetric_orderDual` records that condition (DPN), read
on a lattice, is self-dual.

**Not formalised.** Nothing of the module's own content. It is stated for an arbitrary `Lattice`,
with no completeness and no chain conditions, so it applies to every lattice the paper considers;
the 2-categorical consequences are `SnakeLean/LatticeModel.lean`'s business.

## Semimodularity, and Birkhoff's theorem

`SnakeLean/Semimodular.lean` and `SnakeLean/Birkhoff.lean`, checking Proposition 9.34
`P:FiniteLength`: a lattice of finite length which is transposition-symmetric is modular, so that
on such lattices condition (DPN) collapses to condition (DI2). The two halves are separated
because only the first is the paper's own; the second is Theorem 16 of Chapter II, §8 of
Birkhoff's *Lattice Theory* (3rd edition, 1967, p. 41), which the paper cites and which Mathlib
does not have.

`isUpperModularLattice_of_transpositionSymmetric` is the paper's atom-and-coatom argument. The
elementwise `Transposes` of `SnakeLean/ModularPair.lean` pays off here: the paper localises to the
interval `[a ⊓ b, a ⊔ b]`, and in Lean that is a constraint on elements rather than a change of
type, so no interval lattice is built. **The hypothesis is weaker than the paper's**: only the
*ascending* chain condition is used, and only to ascend from the witness `w` to a maximal element
below `a ⊔ b`. The dual half is a transport along `transpositionSymmetric_orderDual`, not a second
proof.

`SnakeLean/Birkhoff.lean` follows Birkhoff's own route through the height function, with
Mathlib's `Order.height` in place of a hand-built grading. `covBy_height_eq` is the
Jordan–Dedekind content — along a covering the height rises by exactly one — and it comes out of
`Order.height_eq_iSup_lt_height` by one well-founded induction, needing **only dual
semimodularity and no finiteness at all**. `sup_eq_or_covBy_sup` and its dual then convert the
two semimodularities into the two halves of Birkhoff's identity
`height (a ⊔ c) + height (a ⊓ c) = height a + height c`, each by an induction that walks a single
covering at a time; the arithmetic stays inside `ℕ∞` with no subtraction, and the one cancellation
is licensed by `1 ≠ ⊤`. Modularity then follows from the pentagon:
`isModularLattice_of_forall_pentagon` extracts from a failure of the modular law two elements
`x < z` with the same meet and the same join against `y`, and the identity makes their heights
equal.

**The finiteness hypothesis.** `isModularLattice_of_isUpperModular_of_isLowerModular` assumes
both chain conditions and `∀ a, height a ≠ ⊤`, the latter being what the final cancellation
consumes. That is weaker than Birkhoff's "finite length", which bounds the lengths of chains
uniformly: `height_ne_top_of_krullDim_lt_top` derives it from `krullDim α < ⊤`, and
`isModularLattice_of_transpositionSymmetric_of_krullDim` is Proposition 9.34 `P:FiniteLength`
at the paper's own hypothesis.

**Not formalised.** Whether the two chain conditions alone already force the heights to be finite
in the presence of both semimodularities; it is not needed, since the paper assumes finite length
anyway.

## The lattice model, parametrised

`SnakeLean/LatticeModel.lean` and `SnakeLean/LatticeNSD.lean`, checking Proposition 9.29 `P:SupClass`.
The module builds one 2-category for each `LatticeClass` — a property of complete lattices closed
under down-segments, up-segments and order isomorphism, and containing a one-element lattice,
which are exactly the closure conditions the constructions consume. `ModSup` is the instance at
the modular lattices; the same construction is what a Hilbert-lattice model would use.

The classification of the normal 1-cells is as before, but `isNormal_segIncl_comp_upProj_iff` is
new and is the point: **`c_{a,b}` is normal if and only if `a` and `b` transpose**. The forward
direction is the one the paper's `P:SupModular` gets from the pentagon and this development
previously left unformalised. It runs through `transposes_of_factorisation`: a normal image
factorisation of `c_{a,b}` is a join-projection onto `[s, a]`, then a bijection, then the
inclusion of `[b, t]`; evaluating at the bottom of `↓a` forces `s = a ⊓ b`, asking which elements
are hit forces `t = a ⊔ b`, and the bijection in the middle is then the transposition itself.

`SnakeLean/LatticeNSD.lean` reads the two hypotheses of the non-self-dual Snake Lemma off that
equivalence. An antinormal pair is a segment inclusion followed by a join-projection up to
equivalences, its composite is `c_{a,b}` and its dinversion is `c_{b,a}`, so **(DPN) holds as
soon as every member of the class is transposition-symmetric**
(`dpn_of_forall_transpositionSymmetric`). Both composition closures hold unconditionally
(`normalEpiCompSup`, `normalMonoCompSup`), because an up-segment of an up-segment is an
up-segment and a down-segment of a down-segment is a down-segment.


## The pentagon

`SnakeLean/Pentagon.lean`, checking the last clauses of Proposition 8.36 `P:SupModular` and
Proposition 8.38 `P:SupNotDPN`, and supplying the five-element witness of Remark 9.5
`Rem NSD Strict`. Both say something negative about `Sup`, the 2-category of all complete
lattices: that it is not 2-di-exact, and that it does not satisfy (DPN). By the two biconditionals
of Proposition 9.29 `P:SupClass` — `twoDiExact_iff_forall_isModularLattice` and
`dpn_iff_forall_transpositionSymmetric` — each comes down to one complete lattice that is not
modular, respectively not transposition-symmetric, and the pentagon is both.

Mathlib has no pentagon, so `Pentagon` is built: five constructors, the order a Boolean table,
`PartialOrder`, `Lattice` and `BoundedOrder` with every axiom by `decide`, and
`Fintype.toCompleteLattice` for completeness. `Transposes` being stated elementwise, the two facts
that matter are decided the same way: `transposes_y_z` (both intervals are two-element chains) and
`not_transposes_z_y` (a three-element chain onto a two-element one). Read through
`isNormal_segIncl_comp_upProj_iff`, these are exactly the paper's witness pair: the antinormal
1-cell `c_{z,y} : ↓z ⟶ ↑y` is not normal (`not_isNormal_pentagon`) while its dinversion `c_{y,z}`
is (`isNormal_pentagon_dinversion`), so the biconditional of (DPN) fails (`not_dpn_supAll`); and
the first alone exhibits a non-normal antinormal 1-cell (`exists_isAntinormal_not_isNormal`), so
(DI2) fails (`not_twoDiExact_supAll`). With `isHSD_sup`, `Sup` is the machine-checked five-element
separation of homological self-duality from (DPN).

**Not formalised.** Nothing of the module's own content.

## The Snake Lemma without self-duality

`SnakeLean/NSDNormal.lean` and `SnakeLean/NSDConnecting.lean`, checking Sections 9.9
`SS:NSDNormal` and 9.15 `SS:NSDConnecting`, and with them Theorem 9.19 `T:SnakeNonSelfDual`.
`SnakeLean/NonSelfDual.lean` ([above](#2-di-exactness)) isolates the two sites at which the Snake
Lemma of Section 6 consumes (DI2) and shows that (DPN) alone cannot supply them (Section 9.7
`SS:NSDCircular`), and proves the two hard steps, Propositions 9.11 `P:NSDKappa` and 3.23
`P:NormalCancel`. The rest is not a second construction the size of Section 6, because — as the
proof of Theorem 9.19 says — the reduction of the general case to the special one is independent
of why the special case holds.

**`exists_snakeGeneralNSD` is the theorem**, at `[TwoZExact O] [DPN O] [NormalEpiComp O]` and no
`[TwoDiExact O]`. `IsHSD` is again absent from the hypotheses, discharged by `isHSD_of_dpn`.

`SnakeLean/NSDNormal.lean` proves the two normality statements. `isNormal_cLower` is
Proposition 9.12 `P:NSDcbar`, cheap, as the paper says: the pair `(c, 2-coker(g))` is antinormal and its dinversion *is* `2-img(h) ∘ t`,
already a normal 2-epimorphism followed by a normal 2-monomorphism, so (DPN) applies directly.
`isNormal_bBar_full` is Proposition 9.13 `P:NSDbbar`, the expensive one. Its inputs — `α`, `m₁`, `e₁`, `ρ` — are built here:
`α` and `m₁` by factoring `a` and `2-ker(g)` through `2-ker(e)`, and `e₁` and `ρ` as the
comparisons of the two pure configurations with middle object `M`, so that `b̄ ≅ m₁ ≫ e₁` and
the dinversion `α ≫ ρ` composed with `κ` is the vertical `f`.

`SnakeLean/NSDConnecting.lean` builds the connecting 1-cell from a pure configuration with middle
object `X` rather than `C` (Proposition 9.16 `P:NSDLambda`, `exists_lambda`). Its
`exists_isEquiv1_cokernel_dinversion` is Lemma 4.10 `L:DinversionCoker`: an antinormal composite
and its dinversion have the same 2-cokernel, by a pure universal-property argument. Of the four
identifications of Lemma 9.17 `L:NSDChain`, **two are equalities of objects rather than
equivalences** in Lean — a 2-cokernel of `λ ∘ 2-coim(f)` is a 2-cokernel of `λ`, and a 2-kernel
of `μ ∘ v` is a 2-kernel of `v` — so only Lemma 4.10 and the Pure Snake comparison contribute
equivalences; they are run inside `exists_snakeConnectingNSD`, and only their composite is
stated, which is why the blueprint marks Lemma 9.17 as partial.

**The general case is shared, not duplicated.** `SnakeLean/SnakeGeneral.lean` now states the
reduction as `exists_snakeGeneral_of_special`, taking homological self-duality and the special
case as hypotheses; `snakeSpecial_of_twoDiExact` and `snakeSpecial_of_dpn` supply the latter in
the two settings, and `exists_snakeGeneral` is unchanged as a statement.

**Both halves.** `exists_snakeGeneralNSD'` is the last sentence of Theorem 9.19, with
(NEC) replaced by its dual, and it is a transport: `dpnOp`, `normalEpiCompOp` and
`normalMonoCompOp` in `SnakeLean/NonSelfDual.lean` dualise the hypotheses, `MorphismSES.op` turns
the ladder upside down, and each `IsExactAt` of the dual conclusion comes back through
`isExactAt_of_op`. That last step needs the normality of the 1-cell it lands on, and for `ā` the
only thing in the dual conclusion that supplies it is the normality of the *last* map of the dual
snake sequence — which is why `exists_snakeGeneral` and `exists_snakeGeneralNSD` now assert
`IsNormal O d̲` alongside the four 2-exactness statements.

The converse of `dpn_of_forall_transpositionSymmetric` is `transpositionSymmetric_of_dpn`, so
`dpn_iff_forall_transpositionSymmetric` is the (DPN) half of Proposition 9.29 `P:SupClass` in
both directions;
and `isHSD_sup` shows every class homologically self-dual, since the dinversion of an antinormal
decomposition of the zero map is a transposition `[a, b] → [a, b]` with `a ≤ b`, the identity
(`transposes_of_le`).

## Hilbert lattices

`SnakeLean/HilbertLattice.lean`, checking Proposition 9.31 `P:HilbertSymmetric`. Mathlib supplies the
lattice — `ClosedSubmodule 𝕜 E` is complete, with intersection as meet and the closure of the sum
as join, and carries the orthogonal complement with both De Morgan laws — so nothing has to be
bundled by hand.

`dualModularPair_iff_isClosed_sup` is **Mackey's Theorem III-6**: `(A, B)` is a dual modular pair
if and only if `A + B` is closed. Both directions are elementary, as the paper says, and the
converse is Mackey's own argument:
if `A + B` is not closed, pick `x` in the closure but not in the sum, and test the dual modular
law at `K = B + ⟨x⟩`; then `K ⊓ A ≤ B`, because a nonzero multiple of `x` inside `K ⊓ A` would
put `x` back into `A + B`. What that argument needs is `isClosed_sup_span_singleton`, that a
closed subspace plus a line is closed — Mathlib has that a finite-dimensional subspace is closed
but not this — and it is the one place the inner product is used: the line may be taken
orthogonal to the subspace, and then the sum is the kernel of `1 - P - Q`, a continuous map.

`modularPair_iff_dualModularPair_orthogonal` is the `ᗮ`-flip, Theorem 5(i) of Schreiner.
Together the two give `transposes_iff_isClosed`: the transposition of `A` and `B` is invertible
exactly when `A + B` **and** `Aᗮ + Bᗮ` are closed. That criterion is symmetric in `A` and `B`,
whence `transpositionSymmetric_closedSubmodule`.

**Not formalised.** Two things, and the model of Theorem 9.32 `T:HilbertModel` needs both — which
is why the blueprint marks that theorem as partial. That `L(H)` is *not* modular — the paper's
explicit `A`, `B`, `v`, `Z` in `ℓ²` — which is what makes the 2-category not 2-di-exact;
and the `LatticeClass` plumbing that turns transposition-symmetry into `DPN` for a 2-category of
Hilbert lattices, which needs the intervals of `L(H)` identified as `L(H')` (`↓A ≅ L(A)` and
`↑B ≅ L(Bᗮ)`). With those two, `dpn_of_forall_transpositionSymmetric` gives the model.
