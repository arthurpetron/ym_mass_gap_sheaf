# Stage 1 completion ledger — the loop's honest terminal state (2026-06-22)

Stage 1 = the Λ→∞ thermodynamic limit at FIXED lattice spacing (KNOWN mathematics; the wall is
formalization). After a multi-wave loop (worktree → axiom-clean → merge → commit → consolidate →
reflect → research), this records what is now PROVED and the precisely-named residual walls, with
research-informed tractability verdicts. Audit grew 2440 → 2494; everything `[propext]`/`[Quot.sound]`.

## What Stage 1 now has (PROVED, axiom-clean)

- **H1 real Wilson functional** (`WilsonProbFunctional.lean`): real single-edge Wilson *-algebra
  (Clebsch–Gordan fusion product, star=id) + real heat-kernel functional `ProbFunctionalC`;
  normalization proved; cone positivity UNCONDITIONAL; full positivity reduced to the named all-order
  Gram PSD.
- **MomentSquarePos** (`MomentSquarePSD.lean`): finite-order Gram PSD (N≤3, form level) UNCONDITIONAL;
  all-order REDUCED to one named residual `UniformGramSOS` with the reduction proved; the perfect-square
  S_N factor's uniform half re-exported as proved.
- **H2.1 + interacting tower** (`WilsonConsistency.lean`, `WilsonRGTower.lean`): genuine inverse-limit
  Wilson measure (real non-constant moments, Kolmogorov consistency PROVED); upgraded to a MULTI-EDGE,
  non-stationary tower (growing `EdgeVec` carrier, block-spin vacuum-adjoining *-hom, consistency proved
  via a non-`rfl` telescope) with its inverse-limit measure + projection law. Supersedes the trivial
  placeholder.
- **H2.2 polymer identity** (`PolymerPartition.lean`, `MayerTwoPlaquette.lean`): the partition-function ↔
  polymer-sum identity `Z = Σ_configs ∏ activity` PROVED for the single-plaquette, disjoint, AND the first
  INTERACTING (two-plaquette shared-link) case — the shared-link Haar δ_{a,b} matched to the single-rep
  connected-polymer constraint; `MayerExpansion` inhabited for the connected leading term.
- **H2.3 RealCorrelatorLink** (`WilsonCorrelator.lean`): the real Wilson connected correlator
  `wilsonCorr = Σ_reps (weight)·(eigenvalue)ⁿ`; `matches_abstract` PROVED ⇒ `RealCorrelatorLink`
  INHABITED for the single-edge / stationary transfer model.
- **1a genuine UniformClusterBound** (`UniformClusterFromKP.lean`): NON-DEGENERATE bound (real Λ-dependent
  margin 3/4→7/8, positive floor, nonzero geometric tail) ⇒ strictly-positive infinite-volume mass.

So the TRACTABLE Stage-1 formalization — everything the discrete character/Haar structure makes reachable
— is complete and genuine.

## The residual walls (research-informed tractability)

**R1 — uniform (all-N) heat-kernel Gram PSD** (`UniformGramSOS`).
- KNOWN. The naive "positive-functional ⟹ PSD via Clebsch–Gordan integers" bypass is CIRCULAR:
  `vᵀGv = Σ_c m_c (vᵀN^c v)` and `vᵀN^c v` is NOT term-wise nonnegative (the 2×2 minor `1+3q⁸−4q⁶`
  needs AM–GM). Genuine routes: (a) the P_N / q-total-positivity vicious-walker–LGV wall (research-grade
  to formalize); (b) Gauss–Chebyshev quadrature — finite positive weights × pointwise `K_t≥0` at the
  nodes ⟹ `vᵀGv = Σ_i λ_i (Σ_a v_a U_a(x_i))² ≥ 0` — genuinely constructive per N, but rests on
  `HeatKernelPos`'s pointwise positivity (its own named `DiffJTP` gap). **Verdict: FORMALIZABLE-HARD.**
  The quadrature route (b) is the recommended one and a NEW idea worth recording — it bypasses the P_N
  wall but inherits the heat-kernel-positivity gap.
- Refs: Schmüdgen, *Ten Lectures on the Moment Problem*; Pétréolle–Sokal–Zhu, Mem. AMS 1450; theta-PSD
  arXiv:1603.05512.

**R2 — full Mayer/Ursell cluster-expansion convergence** (`MayerExpansion`, the log-Z reorganization).
- KNOWN, sharp modern form. Best route: the Penrose tree-graph identity + Kotecký–Preiss / Fernández–
  Procacci bound — combinatorial (spanning-tree counting), not analytic. No prior cluster-expansion
  formalization exists in any prover. **Verdict: FORMALIZABLE-HARD** (multi-month: abstract polymers,
  Ursell-as-signed-graph-sum, Penrose scheme, KP induction, clustering deduction).
- Refs: Procacci–Yuhjtman arXiv:1508.07379; Ueltschi arXiv:1705.05353; Fernández–Procacci
  arXiv:math-ph/0605041.

**R3 — interacting plaquette-coupled block-spin RG** (the `WilsonRGTower` named residual).
- IMPORTANT REFRAMING (research finding): this is a CONTINUUM (a→0, Balaban-class) multiscale problem and
  is **OFF the fixed-spacing critical path**. At fixed spacing the interacting plaquette coupling is
  absorbed by the CLUSTER EXPANSION (R2), not by block-spin decimation — Osterwalder–Seiler and every
  modern strong-coupling construction (e.g. the SU(3) Kotecký–Preiss construction arXiv:2506.00284) get
  the fixed-spacing gap from cluster convergence alone, using RG only for the continuum limit.
  **Verdict: RESEARCH-GRADE, but belongs to Stage 2 (continuum), not Stage 1.** Do not invest here for
  the fixed-spacing gap; leave precisely named as a Stage-2 item.

## Honest terminal verdict

The loop has reached its fixed point. **Stage 1's tractable formalization is COMPLETE**; the remaining
content is exactly two known FORMALIZABLE-HARD walls — R1 (all-order Gram PSD; best route = quadrature
via heat-kernel positivity) and R2 (Mayer/Ursell convergence; route = Penrose tree-graph + KP) — neither
closeable by a quick wave (each is a multi-month formalization of genuine combinatorial/analytic
machinery), plus R3 which is correctly a Stage-2 continuum item off the fixed-spacing path.

Continued looping would spin on these without closing them. The responsible terminal state: the
fixed-spacing infinite-volume gap is reduced to TWO precisely-named, known, FORMALIZABLE-HARD obligations
(R1, R2). Closing either is a deliberate, scoped, multi-wave campaign — the natural next *project*, not a
loop iteration. Stage 2 (the a→0 continuum core) remains the open research frontier.
