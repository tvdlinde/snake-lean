# Blueprint

A [leanblueprint](https://github.com/PatrickMassot/leanblueprint) view of the paper: the
mathematics as a web document, with a dependency graph coloured by what is formalised and by
what is ready to be.

**It is published at <https://tvdlinde.github.io/snake-lean/>**, built from this directory by
`.github/workflows/blueprint.yml` on every push to `master`.  The build needs no LaTeX run --- the
diagrams ship as cached SVGs and MathJax sets the mathematics --- but it does need `kpsewhich`,
which is why the workflow installs `texlive-base`: plasTeX resolves `\input{macros/common}`
through it, and without it the macro files are skipped in silence and every theorem environment
becomes an unknown macro.

**This is a work in progress.** It builds, the numbering is right and the graph is now a real
dependency graph, but see the limitations below before relying on it.

## Building

```
pipx install leanblueprint   # brings plasTeX with it
PATH="$HOME/.local/share/pipx/venvs/leanblueprint/bin:$PATH" leanblueprint web
```

Run it from the repository root; the output lands in `blueprint/web/`, which is not tracked. The
`PATH` prefix is needed because pipx exposes the `leanblueprint` entry point but not `plastex`,
which `leanblueprint web` shells out to.

## The bibliography

`src/snake.bib` holds the entries the paper cites, extracted from the paper's own bibliography
database; only the cited ones are kept, and the local `file`/`date-added`/`date-modified` fields
are stripped, since this file is published. plasTeX does not run BibTeX --- it reads a `.bbl` --- so `web.bbl`
and `print.bbl` are committed beside it, copied from the paper's own `snake.bbl`. Re-copy them
whenever an entry changes.

## Macros and MathJax

`src/macros/common.tex` is maintained by hand, and its definitions have to be ones **MathJax**
understands as well as LaTeX. `\mathpzc` (a `\DeclareMathAlphabet`), `\xspace` and lengths such
as `\horspace` are not, and leak into the page as literal text; `\catfont` is therefore
`\mathit` here rather than the paper's chancery, which still contrasts with `\onecat`'s
`\mathsf`. For the same reason the generator moves any display holding a diagram out of math
mode: MathJax has no `\includegraphics`.

MathJax has the base and AMS packages and nothing else, so a macro that can only expand to
**mathtools** keeps its mathtools spelling in `common.tex`, where the pdf version reads it, and is
shimmed for the web in `src/macros/web.tex`: `\aR` (the paper's labelled double arrow, never
labelled in practice) becomes `\Longrightarrow` and `\coloneq` becomes `\mathrel{:=}`. Nothing in
the build reports such a leak --- plasTeX passes the unknown macro through and MathJax prints it in
red, so it is visible only in a browser. `check-mathjax.py` in the paper repository reads the
rendered pages and reports any macro outside a verified list; run it after `leanblueprint web`.

## Where the content comes from

`src/content.tex` is **generated, not written**, by `genblueprint.py` in the paper repository:

```
lake env lean blueprint/deps.lean > blueprint/deps.tsv   # only after the Lean side changes
./genblueprint.py path/to/blueprint/src/content.tex path/to/snake-lean
```

`content.tex` and `src/diagrams/*.svg` are both generated and both tracked, so a clean checkout
builds without the paper repository present.

Statements come from the paper's labelled environments, lifted verbatim. Regenerate whenever the
paper changes; do not edit `content.tex` by hand. `src/macros/common.tex` is likewise lifted from
the paper's preamble, minus the xy-pic and tikz-cd definitions.

### The dependency edges

leanblueprint keeps two graphs, not one. `\uses` inside a *statement* records the definitions the
statement is phrased in, and drives `can_state`: this result can be *stated* in Lean once they are
all formalised. `\uses` inside a *proof* records the results the proof invokes, and drives
`can_prove`. The two show as solid and dashed edges, and as a node's border and fill colour. A
blue-bordered, unfilled node is the useful one: everything it needs is in place, so it is ready to
be formalised next.

Edges come from three sources, each overriding the one below it.

1. **`blueprint-uses.txt`**, in the paper repository. Hand-written stanzas, one per paper label.
   Statement dependencies, which nothing can derive — a statement almost never cross-references
   the definitions it uses — and the `lean =` lines, which are the *only* thing that decides
   which paper result a declaration is — see below.
2. **The Lean environment**, through `blueprint/deps.lean`, which dumps every declaration of this
   development with the constants of its type and the constants of its value. That split is
   exactly leanblueprint's: a declaration's type is its statement and its value is its proof.
   Declarations that no paper label claims are expanded through until a labelled one is reached.
   These edges are not a heuristic — they are what the kernel checked. Membership is by defining
   module, not by namespace, since the Section 8 modules declare into `CategoryTheory`.
3. **The paper's own `\ref{}`s**, as a fallback. A `\ref` records a mention and a `\uses` records
   a need; only the second is guaranteed acyclic, so these have to be restricted to references
   pointing backwards in the document. Nothing currently falls back this far.

### Which result a declaration is

A docstring cites paper results; it never says which one the declaration *is*. Reading a citation
as a claim gets it wrong wherever a docstring opens by naming the result it builds on — a class
stating a hypothesis of Theorem 9.19 `T:SnakeNonSelfDual` is not that theorem — and wherever it
mentions a result it does *not* prove, such as a "Not formalised" paragraph naming what is
missing. So **a result is linked only through a `lean =` line in `blueprint-uses.txt`**, one
stanza per paper result; the docstring heuristic survives only as a suggester
(`./genblueprint.py --suggest` lists the declarations that cite a label no stanza claims them
for, `--dump-claims` prints stanza skeletons for them), and `genblueprint.py` reports any
declaration the environment does not have. A stanza may say `partial = yes`: its `\lean{}` links
are emitted but no `\leanok`, which is how a result whose declarations prove only part of it —
the five so marked each say in a comment what is missing — is kept visible without being coloured
as done.

## Current limitations

- ~~**Diagrams are placeholders.**~~ Fixed. plasTeX parses neither xy-pic nor tikz-cd, so each
  diagram is compiled to SVG by real LaTeX with the paper's own preamble and included as an image;
  `src/diagrams/` holds the results, cached on a hash of the diagram source. This is also what
  brings the custom `\newdir` arrowheads back — they cannot live in `macros/common.tex`, because
  plasTeX stops reading at the first one, but the compiler here never sees plasTeX. Regenerating
  needs `pdflatex` and `dvisvgm`; `--no-diagrams` skips it and restores the placeholders.
  With the diagrams handled, `blueprint/` no longer carries `export-ignore`: the released copy
  of this repository ships the blueprint sources.
- **The Lean edges are the Lean proof's.** Where a Lean proof takes a different route from the
  paper's, the graph shows the Lean route.
- **A dozen edges are dropped to keep the graph acyclic.** leanblueprint walks ancestors
  recursively and does not survive a cycle. Label-level cycles arise because one paper result can
  own several declarations; the generator lists every edge it drops.
- **Grey still does not mean unformalised**, only that nothing claims the result. The gap is
  small: 102 of the 117 nodes are linked, and most of what is left sits behind one unformalised
  bridge — the 2-categorical reading of the Serre-class results of Sections 8 and 9.20.

Numbering does match the paper: 161 of its 164 numbered environments come out with the number the
paper prints, the three exceptions being equation labels rather than results.
