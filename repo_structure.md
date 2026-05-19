ym-mass-gap-sheaf/
├── README.md                    # Project overview, current status
├── docs/
│   ├── context.md               # The seed doc above
│   ├── outline.md               # The depth-5 outline, kept as the spec
│   ├── ual-statement.md         # UAL(G) precise statement
│   └── sheaf-framework.md       # 𝒜_k, 𝒮_k definitions in formal prose
├── notes/
│   ├── overlap-bound-su2.md     # Working notes on the §4 calculation
│   ├── matching-scale.md        # Why approach (i) is the classical obstruction
│   └── codynamic-transfer.md    # The structural analogy with sensor fusion
├── computations/
│   ├── su2_representations.py   # Symbolic + numerical rep theory for SU(2)
│   ├── heat_kernel_tail.py      # Explicit κ, β, C constants
│   ├── kp_constants.py          # Kotecký–Preiss bookkeeping
│   └── overlap_measure.py       # Numerical sanity check on μ_k(Ω_k^∩)
├── visualizations/
│   ├── README.md                    # What each subfolder is for, naming conventions
│   ├── structure/                   # (1) Mathematical structure diagrams
│   │   ├── site-cover.tikz          # Small/large/buffer cover of Ω_k
│   │   ├── sheaf-gluing.tikz        # 𝒜_k / 𝒮_k coupling
│   │   ├── block-spin-2cell.tikz    # The Θ_k 2-cell
│   │   ├── inductive-state.tikz     # Package ℐ_k as a labeled tuple
│   │   └── rg-flow.tikz             # σ̂_k trajectory with η_k budget
│   ├── pilot/                       # (2) Numerical pilot output
│   │   ├── su2/
│   │   ├── heat-kernel-tail.{py,svg}      # μ_k(Ω_k^∩) vs g_k for SU(2)
│   │   │   ├── kp-constants.{py,svg}          # (ρ, K) tuples across k
│   │   │   ├── sigma-hat-trajectory.{py,svg}  # σ̂_k vs k
│   │   │   └── matching-curve.{py,svg}        # K(SU(2); k_*) vs r(g_{k_*})
│   │   └── general/                           # Filled in as program generalizes
│   ├── cartoons/                    # (3) Pedagogical pictures
│   │   ├── small-field-region.svg
│   │   ├── buffer-shell.svg
│   │   └── polymer-decomposition.svg
│   ├── transfer/                    # (4) Codynamic bridge artifacts
│   │   ├── ekf-to-ym-types.tikz     # Type-signature port diagram
│   │   ├── correspondence-table.tex # The §6 table as a typeset object
│   │   └── rewind-budget.tikz       # RewindBudget ↔ Δ_∩ correspondence
│   └── _generated/                  # Auto-generated outputs, gitignored
├── formal/
│   ├── site-definition.tex      # Formal categorical setup
│   ├── sheaf-axioms.tex         # Sheaf and presheaf definitions
│   └── inductive-step.tex       # The §3 inductive step theorem
└── pyproject.toml