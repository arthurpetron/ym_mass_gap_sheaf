# State of the Yang–Mills Clay attempt, and the best path forward (2026-06-23)

Capstone synthesis after a full exhaustive review of the Lean (6 parallel read-only passes over all 238
modules + 64 docs). This is the single "where we are / where to go" document. For the geography of the
wall see `where-the-wall-sits-2026-06-22.md`; for the honest proved-vs-open ledger see
`clay-open-boundary-ledger.md`; this doc consolidates and gives the forward plan.

## 0. One-paragraph verdict

The project is a large, **genuinely axiom-clean, Mathlib-free, constructive** Lean development (~238
modules, ~2646 tracked theorems, every load-bearing theorem reporting only `propext`/`Quot.sound`; no
`sorry`/`admit`/`Classical.choice`/`native_decide`/`Prop:=True` content-stubs; degenerate placeholders and
the one honesty correction are explicitly flagged). It does **not** solve the Clay problem and does not
claim to. What it HAS achieved is (a) a machine-checked proof of the structural spine — the worst-case
reduction to SU(2), the fixed-spacing finite-volume located mass gap, and OS2 reflection positivity — and
(b) a precise reduction of the continuum gap to a small set of **named, honestly-open** analytic inputs,
expressed in three independent languages (cluster expansion / dimensionless RG ratio / Bakry–Émery
curvature). The remaining content splits cleanly into KNOWN-but-hard-to-formalize (Stage 1) and
genuinely-OPEN research mathematics (Stage 2).

## 1. Soundness posture (confirmed by the review)

- Mathlib-free; intuitionistic (no LEM/AC); axiom-clean (`propext`, `Quot.sound` only) — verified against
  `AXIOM_AUDIT.md` (no `Classical.choice`/`sorryAx`/`nativeDecide` entries).
- No fakes: the review found NO `sorry`/`admit`/new `axiom`/`Prop:=True` content-stub in load-bearing code.
  The three `:= True` occurrences are an honestly-documented smoke-test predicate and a `Unit` typeclass
  model (not content). Documented avoidances (e.g. "we avoid `Rat`'s `Classical.choice`") are genuine.
- Honesty discipline holds: every open thing is a NAMED Type-level obligation or `Prop` hypothesis with a
  proved reduction to it; degenerate inhabitants (`degenerate*ClusterBound`) carry ⚠ banners; the SZZ
  surrogate inadequacy is corrected in-file and in `szz-surrogate-correction-2026-06-23.md`.
- Code hygiene: no dead code or duplicate-logic modules found; headers accurate after this pass's doc
  fixes (the only genuine staleness was the `SU2KP.lean` header value, now corrected; the long-flagged
  `rho_sf`/`K_sf` "conflict" was NOT a bug — the constants are consistent).

## 2. What is PROVED (unconditional, machine-checked)

- **Worst-case reduction to SU(2)** (`MassGap/SimpleGroup`, `RG/*`, `RepTheory/*`): every compact simple
  group's strong-coupling budget is dominated by SU(2) via Casimir floors (`C₂_fund ≥ 3/4`, `C₂_adj ≥ 2`,
  equality only at SU(2); every SU(N) fundamental weight clears 3/4). The all-groups requirement reduces
  to one worst case. (η-domination now PROVEN via `EtaPackaging`, not posited.)
- **Fixed-spacing, finite-volume located mass gap** (`LocatedSpectralGap`, `HeatKernelGap`): the compact
  (finite) transfer operator has a constructively LOCATED second eigenvalue `sep = w³ < 1`, margin
  `1 − w³ > 0` — a genuine gap, decidable, no Stone/unbounded machinery.
- **OS2 reflection positivity** (`ReflectionPositivity`, `OSAxioms`): unconditional, via Schur /
  Osterwalder–Seiler diagonalization (a weighted sum of squares); finite-order Gram PSD proved at N ≤ 3.
- **Free Bakry–Émery curvature anchor** (`CharChainFree`, `HeatKernelCurvature`): the free SU(2)
  heat-kernel generator has `CD(3/4)` (lowest Casimir = curvature) — genuine, axiom-clean.
- **Fixed-spacing nontriviality dichotomy** (`Nontriviality`): trivial ⇒ Λ collapses; genuine running
  (β≠0, discharged via `AFScaleCocycle.af_BetaNonzero`) ⇒ Λ-class nontrivial.

## 3. The reduction structure: THREE routes to the continuum gap

The continuum mass gap is reduced — each reduction PROVED-to-suffice, each bottoming out at ONE named
open input — in three independent languages:

1. **Cluster route** — `ClusterGapReduction.UniformClusterBound` ⇒ positive continuum-rate mass (bridge
   proved). Open input: the volume-uniform strong-coupling cluster bound (genuine non-degenerate
   inhabitant; the degenerate one is flagged).
2. **AF / dimensionless-ratio route** — `ContinuumCertificate` bundles three sharp single-step inputs
   (`UniformRatioVariation`, `ScalingDimensionDecay`, `LambdaPositiveLimit`) routed through the PROVED AF
   schedule ⇒ gap + nontriviality + O(4) jointly.
3. **Geometric / Bakry–Émery route** — `UniformCurvatureBound.uniform_CD` (a single curvature `K>0`
   uniformly) ⇒ positive continuum mass (via `toUniformClusterBound`).

All three bottom out at the SAME mathematical content: **uniform-in-lattice-spacing control of the YM
measure as a→0**. The three languages illuminate it differently and connect to different external
literatures.

## 4. The honest walls

### Stage 1 — Λ→∞ infinite volume at FIXED spacing — KNOWN mathematics
Closing it gives a rigorous, constructive, machine-checked fixed-spacing infinite-volume mass gap for all
compact simple groups (a real, citable result; NOT the continuum). Two residuals, both formalizable-hard:
- **All-order heat-kernel Gram PSD** (`MomentSquarePSD.UniformGramSOS`): the uniform `P_N ≥ 0` in
  `Δ_N = S_N²·P_N` (the perfect-square `S_N` is already uniform; `P_N` exact through N=8). This is the
  q-total-positivity / vicious-walker–LGV wall (research-grade to formalize). Alternative route: Gauss–
  Chebyshev quadrature via pointwise `K_t ≥ 0`, which rests on `HeatKernelPos`'s named `DiffJTP` analytic gap.
- **Mayer/Ursell cluster-expansion convergence** (`PolymerPartition.MayerExpansion`): the full
  `log Z = Σ Ursell` reorganization. Known via the Penrose tree-graph identity + Kotecký–Preiss
  (combinatorial, not analytic); no proof assistant has formalized a cluster expansion.

### Stage 2 — a→0 continuum limit — genuinely OPEN research mathematics
The uniform-in-a RG/gap control (the three certificate fields). This is the real Clay-hard content; not
proven by anyone in any framework for 4D YM. Bałaban controlled the partition function there; the gap's
survival is open.

## 5. Negative results that constrain direction (proved/established here)

- **Topology cannot bound the gap MAGNITUDE** (`GapStability`, `CenterSymmetry`): index theory gives
  existence, K-theory gives stability, persistent homology gives nothing for a lower bound — confirmed
  in-Lean (`belowCount_blind_to_margin`; the `Role` ledger). Useful only for after-the-fact stability /
  phase diagnosis. Do NOT pursue topology for magnitude.
- **Curvature is the WRONG FUNCTIONAL FORM for the continuum**: a Bakry–Émery constant `K(g²)` is analytic
  at g=0, so a curvature-derived gap is polynomial in `g²`, but dimensional transmutation makes the gap
  `~ exp(−c/g²)` (essential singularity). Convexity/curvature cannot close the continuum (SZZ's `K_S` goes
  negative at weak coupling). Do NOT pursue curvature-by-convexity for the continuum.
- **The SZZ character-surrogate is inadequate as built** (`szz-surrogate-correction`): the off-diagonal-only
  `chainW` makes `WilsonHessianSmall` unsatisfiable at strong coupling. A faithful surrogate needs the
  COMBINED generator (free Casimir diagonal + Wilson off-diagonal) with multi-mode `CD` proved on it.
- **The P_N wall's algebraic routes are exhausted** (the `pn-wall1-*` sealed case study): only the
  non-principal vicious-walker LGV survives.

## 6. Best path forward (honest prioritization)

**A. Publish the formalization artifacts NOW (highest value-to-cost, ready).** Per
`publishable-results-audit-2026-06-22.md`: (1) the Mathlib-free, intuitionistic, axiom-clean constructive
real-analysis library (sqrt/cbrt/exp/trig from scratch) — first of its kind in Lean; (2) OS2 reflection
positivity for an interacting/lattice-gauge functional (vs OSforGFF's free field); (3) the constructive
Kotecký–Preiss/polymer + Bakry–Émery reductions (content-derived, vs the classical assumption-loaded
competitor). These are genuine, defensible ITP/CPP/JAR contributions. They do not require closing any wall.

**B. Finish Stage 1 → a complete rigorous fixed-spacing infinite-volume gap (the best reachable THEOREM).**
The single most concrete known-math target is the **Mayer/Ursell convergence via the Penrose tree-graph
identity** (combinatorial, modern, formalizable; Procacci–Yuhjtman / Ueltschi) → a genuine non-degenerate
`UniformClusterBound` → the fixed-spacing infinite-volume mass gap for all compact simple groups. This is a
multi-month build but it is KNOWN mathematics with a clear route, and it would be a real, first-of-its-kind
machine-checked result. (Secondary Stage-1 target: the all-order Gram PSD via LGV q-total-positivity, or
the quadrature route once `HeatKernelPos.DiffJTP` is closed.)

**C. Treat Stage 2 (the Clay continuum) as a research program, not a formalization task.** The project's
genuine contribution to the continuum is the precise three-language reduction + the negative results that
map which methods cannot work. Do NOT encode the open conjecture. Any real progress requires new
mathematics (a uniform-in-a RG/gap control), most plausibly the Bauerschmidt–Bodineau–Dagallier multiscale
program ported to gauge theory — which has no gauge instance, needs scale-integration this substrate lacks,
and hits the same susceptibility wall. Worth tracking the external literature; not worth formalizing today.

**Recommended immediate sequence:** (A) in parallel with (B). (A) banks the genuine publishable value now;
(B) is the one reachable theorem that would make the scaffold a complete rigorous result at fixed spacing.
(C) stays an honest open frontier.

## 7. Bottom line

This is an exemplary-honesty, axiom-clean formalization that has proved the structural spine of the YM gap
and reduced the rest to precisely-named walls in three languages, with negative results delineating the
terrain. It is NOT a Clay solution. Its best forward value is: publish the formalization artifacts now,
finish Stage 1 to a complete fixed-spacing infinite-volume gap (known math, Penrose/KP route), and hold the
continuum (Stage 2) as the open research frontier it genuinely is.
