# Visualizations

This folder holds every visual artifact in the program. Visuals are
organized by **function**, not by source format or by paper section,
because the same diagram may appear in the paper, in a talk, and in a
notebook, and because the *role* a visual plays determines how it
should be built and maintained.

There are four functional categories, each with its own subfolder.

---

## `structure/` — Mathematical structure diagrams

Diagrams of the formal apparatus: the site, the sheaves
$\mathcal{A}_k$ and $\mathcal{S}_k$, the block-spin morphism, the
2-cell $\Theta_k$, the inductive state package $\mathcal{I}_k$, and
the RG flow of $\widehat{\sigma}_k$.

These are **paper-figure candidates**. They are authored in TikZ so
their typography matches the LaTeX in `formal/`. They change only
when the formal definitions change.

Contents:
- `site-cover.tikz` — the small/large/buffer cover of $\Omega_k$.
- `sheaf-gluing.tikz` — the coupling between $\mathcal{A}_k$ and $\mathcal{S}_k$.
- `block-spin-2cell.tikz` — the degradation 2-cell $\Theta_k$.
- `inductive-state.tikz` — the package $\mathcal{I}_k$ as a labeled tuple.
- `rg-flow.tikz` — the $\widehat{\sigma}_k$ trajectory with the $\eta_k$ budget.

---

## `pilot/` — Numerical pilot output

Plots produced by the code in `computations/`: heat-kernel tails, KP
constants across RG steps, the $\widehat{\sigma}_k$ trajectory, the
overlap measure, the matching curve $K(G; k_*)$ vs $r(g_{k_*})$.

These are **experimental artifacts**. Each plot has a sibling script
in `computations/` that produces it. The script is the source of
truth; the plot is regenerable. Plots that are *not* canonical paper
figures live in `_generated/` (gitignored); plots that *are* canonical
are committed here.

Organized by gauge group, set up in parallel from day one even though
only SU(2) is populated initially:
- `su2/` — the SU(2) pilot (active).
- `su3/` — SU(3) generalization (planned).
- `so3/`, `su3_z3/` — adjoint forms for approach (iii) (planned).
- `general/` — group-independent plots (e.g. $\beta$-function running).

Naming within each group folder mirrors the producing script:
`computations/overlap_measure.py` $\to$
`pilot/su2/overlap-vs-rg-step.svg`.

---

## `cartoons/` — Pedagogical pictures

Illustrative, non-rigorous pictures of configuration-space regions:
the small-field region, the buffer shell, the polymer decomposition.
Their job is to build intuition in the paper's introduction and in
talks.

These are **explanatory artifacts**. They may be hand-drawn (SVG) or
code-drawn, whichever communicates best. They are allowed to be
schematic and dimensionally dishonest (e.g. drawing $\Omega_k$ as a
2D blob) in a way the `structure/` diagrams are not.

Contents:
- `small-field-region.svg`
- `buffer-shell.svg`
- `polymer-decomposition.svg`

---

## `transfer/` — Codynamic bridge artifacts

Diagrams of the correspondence between the `codynamic-sensor-data`
inductive machinery and the Yang–Mills inductive step: the
type-signature port, the correspondence table as a typeset object,
the RewindBudget $\leftrightarrow \Delta_{\cap}$ mapping.

These are **bridge artifacts**. They are a different *kind* of object
than the within-YM `structure/` diagrams because they cross between
two theories. Authored in TikZ for the paper.

Contents:
- `ekf-to-ym-types.tikz` — the type-signature port.
- `correspondence-table.tex` — the §6 table of `docs/context.md`, typeset.
- `rewind-budget.tikz` — the RewindBudget $\leftrightarrow \Delta_{\cap}$ correspondence.

(If this folder stays sparse, it may be folded into `structure/`. It
is kept separate for now because the type-signature port is genuinely
cross-theory.)

---

## `_generated/` — Build outputs (gitignored)

Anything produced by `make figures` or by re-running a `computations/`
script: compiled TikZ PDFs, regenerated plots, intermediate PNGs.
Nothing here is committed. The committed source is the `.tikz` /
`.py` file; the canonical committed output (if any) lives in the
functional subfolder above, not here.

---

## Conventions

- **File naming.** `kebab-case` for all visual files. Python modules
  in `computations/` are `snake_case`.
- **Format choice.** TikZ for paper figures (`structure/`,
  `transfer/`); SVG/PNG for numerical output (`pilot/`) and cartoons.
- **Source/output split.** TikZ source and Python scripts are
  committed; their compiled output goes to `_generated/` unless it is
  a canonical paper figure.
- **One script, one figure.** Each `pilot/` figure is produced by
  exactly one `computations/` script, and the filenames correspond.
- **Regenerability.** Every committed `pilot/` figure must be
  reproducible by running `make figures`. If a figure cannot be
  regenerated from committed code, it does not belong here.