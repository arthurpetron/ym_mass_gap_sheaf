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
│   ├── to be determined
├── formal/
│   ├── site-definition.tex      # Formal categorical setup
│   ├── sheaf-axioms.tex         # Sheaf and presheaf definitions
│   └── inductive-step.tex       # The §3 inductive step theorem
└── pyproject.toml