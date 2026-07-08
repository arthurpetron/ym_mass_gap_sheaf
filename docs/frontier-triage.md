# Frontier triage — known-math-to-constructivize vs. genuinely-new-math

*Generated 2026-07-08 (item 7 of the strategic roadmap). Purpose: sequence the open
frontier atoms by the KIND of difficulty, so that tractable-but-hard work (constructivizing
established proofs, which closes real atoms and moves the burn-down metric off D=0) is burned
down systematically, while the genuinely-new mathematics is scoped explicitly as the research
campaign — the place where an expert collaborator has the most leverage.*

The burn-down metric (`docs/frontier-burndown.md`) is the motivation: **D=0 every month** —
a large volume of genuine analytic work has discharged zero guard-verified atoms, because the
work reduces *to* `singleStep` (the C-loop) without going below it. Not all atoms are like that.
Several are established classical theorems whose only obstruction is the constructive rewrite —
those are the ones to close first, because closing them actually moves D.

---

## Category A — known mathematics to constructivize (tractable; closes real atoms)

These have literature proofs. The difficulty is *constructivizing* a known argument in the
Q'/CReal substrate (real, but bounded and finite in scope), not inventing mathematics. Each
closure is a genuine atom discharge — a D-move.

### A1. `(T′)` — tree-graph / Penrose–Poghosyan–Ueltschi bound  **[~90% done]**
- **Classical source:** Penrose (1967) tree-graph inequality; Poghosyan–Ueltschi (2009)
  "Abstract cluster expansion with applications." `|C(G)| ≤ Σ_{spanning trees} ∏ |weights|`.
- **State:** the const-weight Penrose deletion–contraction inequality is now a *theorem*
  (`penroseIneqConst`, `PenroseConstInRange.lean`) — the refuted `DCHyp` is eliminated. The
  loose Cayley bound `τ(Y) ≤ n^{n-1}` is proved (`cayleyLooseBound_closed`, suffices via
  `toBoundLoose`); `cubicEulerBound` `(1+1/n)^n ≤ 3` is proved.
- **Sole residual:** the **Ursell pin** `UrsellPinConst` — the Ursell/Mayer coefficient
  identity tying the abstract `phiT` to `|C(adjGraph Y)|`. Also classical (Ursell 1927).
- **Verdict:** closest atom to a genuine discharge on the board. Priority target.

### A2. `(D1)` — Mayer–Ursell cluster expansion
- **Classical source:** Mayer (1940s), Ursell; modern: Brydges' lecture notes, Kotecký–Preiss
  (1986) convergence criterion. The connected-graph / Ursell-function identity.
- **State:** the Kotecký–Preiss convergence layer is present and consumes the polymer result
  either way. The Brydges–Kennedy forest-interpolation *swap* was refuted (integral heavier than
  the finite identity), so the route is the direct Mayer–Ursell identity.
- **Residual:** constructivize the Mayer–Ursell coefficient identity in 4D (bounded combinatorics
  — the `D1` representation). Tractable; shares machinery with A1's Ursell pin.

### A3. `hadd` — eigenvalue ↔ margin dictionary
- **Classical source:** transfer-matrix / Perron–Frobenius spectral theory; the mass gap =
  `−log(λ₂/λ₁)` of the transfer operator. Textbook (Seiler, Osterwalder–Seiler).
- **State:** the located-spectral-gap layer (`LocatedSpectralGap`, `boundedH`) + the 2D adequacy
  inhabitant (`twoDLocatedGap`, this session) exercise the dictionary in a real theory.
- **Residual:** the `hadd` bridge lemma — the exact eigenvalue↔margin correspondence at fixed
  spacing. Classical; the 2D adequacy test shows the interface composes.

**A-category sequencing:** A1 (Ursell pin) → A3 (hadd, dictionary — the 2D inhabitant de-risks it)
→ A2 (D1). Each is a bounded, literature-backed constructivization. Closing any one moves D off 0
for the first time — the single most valuable thing the burn-down says is missing.

---

## Category B — genuinely new mathematics (the research campaign)

No literature proof closes these. The MK bond-moving defect control is absent from the local-CLT
literature (per `reference_localclt_literature`); the 4D non-perturbative gap generation is the
open Clay content. This is where an **expert collaborator has the most leverage** — and where the
project should be explicit that it is doing research, not transcription.

### B1. `singleStep` / true-margin recursion through the crossover  **[THE binding wall]**
- **What:** the real 4D SU(N) block-spin defects satisfy `step` + summable `(δ+ε)` +
  `(1−Σδ)·m₀ > Σε` — the Balaban-class estimate, uniform through the strong-to-weak crossover.
- **Why new:** this is the non-perturbative Λ-generation. Everything folds to it (F=1, the C-loop).
- **Live attack (item 12, the top bet):** Koch–Wittwer-style **computer-assisted rigorous RG** —
  project the block-spin map onto a finite truncation, certify contraction/defect bounds on the
  truncation by exact interval arithmetic (the Q' substrate *is* a certified-arithmetic engine),
  and prove ONE analytic truncation-error lemma. Concentrates all Balaban hardness into that
  single lemma; composes with the hierarchical program (`HierarchicalMassGap`). De-risk first via
  item 9 (Python MCMC scouting of the defect scaling per scheme).

### B2. `hlocalize` / Core B — the p≥2 fusion local-CLT
- **What:** the uniform-in-`s` theta-moment second-difference lower bound `Δ²V(s)+2 ≥
  (144/25)w²(1−w²)` (the R1 `UniformCurvatureEnvelope` / `ThetaTailSecondDiffMargin`) — a
  log-concavity / discrete-Gaussian variance-parity statement with matched corner-vanishing.
- **Why new:** the uniform-in-`s` core persists through every reduction (the R1 corner, the tail
  two-region); windows `s=0..6` proved, the tail open. Not in the literature.
- **Leverage:** Lorentzian-polynomial / Karlin PF₂ / Tate–Zelditch theta-saddle machinery
  (research leads in `reference_localclt_literature`).

**B-category stance:** treat as the campaign, not a checklist. Item 12 is the load-bearing bet on
B1; B2 is a parallel deep front. The route-adjudications (items 13 resurgence, 15 two-scale LSI)
test whether alternative decompositions of B1 are strictly weaker than `singleStep` (a legal new
decomposition) or equi-inhabit it (a C++, recorded and moved past).

---

## The one-line sequencing decision

**Burn down Category A systematically (A1→A3→A2) to move D off 0 — those are real discharges of
established theorems. Run Category B as the research campaign, with item 12 (certified RG) as the
primary bet on the binding wall and the collaborator net (item 10) aimed squarely at B1/B2.**
Do not let Category-B difficulty stall Category-A closures: they are independent, and A-closures
are the honest progress the metric is asking for.
