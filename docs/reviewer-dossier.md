# Reviewer & collaborator dossier — what this is, what to check, and where to help

*2026-07-08 (item 10). This is the bus-factor document: it exists so that the project's state,
verification procedure, and open frontier are legible to someone who is not the author. Written as
onboarding for a collaborator, because the realistic success path for the hard frontier atoms
involves one. Read top to bottom once; thereafter use it as an index.*

---

## 1. What this project is (and what it claims)

A machine-checked, **constructive/intuitionistic** Lean development of lattice SU(N) Yang–Mills,
targeting the Clay mass-gap problem. What is *proved* is deliberately smaller than the Clay
statement and must always be framed with its qualifiers (`docs/regime-qualifiers.md`):

> A mass gap for **fixed-spacing, strong-coupling** lattice SU(N) at a **specific coupling**, plus
> a reduction of all simple groups to the SU(2) worst case. **The continuum limit — the Clay
> problem — is OPEN**, isolated as `ClayContinuumExistence`, named and machine-guarded.

The genuinely novel contributions are the **method**: the constructive mechanization, the Q'/CReal
certified-arithmetic substrate, the uniform-group reduction, and the anti-vacuity guard
architecture. The physics claim is exactly the size of the checked kernel — no larger.

## 2. How to verify (what to check and how) — do this first

Everything below runs from the repo root. If these pass, the claims are real; if any fails, that is
a finding.

| Check | Command | Expected |
|---|---|---|
| Build | `cd lean && lake build` | exit 0, ~780 jobs |
| **Inhabitation guard** | `cd lean && lake build YMGapGuard` | `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited` |
| **Statement-hash guard** (item 5) | `cd lean && lake build YMGapStatementGuard` | `statement-guard OK` (catches silent weakening of the pinned statements) |
| Axiom gate | `make lean-audit` | `Axiom-gate audit: PASS` (no axiom outside `{propext, Quot.sound}` unless a reviewed exception) |
| Axiom digest (strict) | `make lean-audit-strict` | PASS (per-namespace digest unchanged) |
| Frontier ledger | `python3 scripts/frontier_status.py` | regenerates `docs/frontier-status.md`; every Clay-frontier bundle stays OPEN |
| Burn-down metric | `python3 scripts/frontier_burndown.py` | atoms opened/reduced/closed; **currently D=0** |

**The three anti-self-deception invariants**, and why each matters:
1. **The frontier types must stay UNINHABITED.** An inhabitant would "close" a fragment of Clay; the
   guard fails the build on any unconditional inhabitant. A *conditional* reduction `… → F` is fine
   — only an unconditional term is flagged. This catches a vacuous/circular "proof."
2. **The pinned statements must not DRIFT.** The statement-hash guard fails the build if
   `ClayTargetPinned` / `FrontierDAG` bundles are silently weakened (a loosened field). This catches
   the "make the target easier" attack that the inhabitation guard cannot see.
3. **The axiom gate must hold.** No `sorryAx`/`Classical`/`native_decide` in any gated decl; the
   substrate is intuitionistic with a tiny trusted base (`propext`, `Quot.sound`).

To audit honesty as a reviewer: run all seven checks, then read `docs/clay-open-boundary-ledger.md`
(the canonical proved-vs-open accounting) and `docs/frontier-burndown.md` (the honest work-vs-
discharge picture). The project *underclaims* by policy; the ledger is where the true boundary is.

## 3. Architecture

- **Substrate** (`YMGap/Constructive/`): `Q'` exact rationals with `decide`-checkable order;
  `CReal` constructive reals (for genuine irrationals — θ values, `exp`, `√`, eigenvalues);
  `RingNormaliser` (a sound multivariate polynomial-identity decider); WZ/telescoping tooling. This
  is a reusable certified-arithmetic engine — the basis for the item-12 route.
- **The pipeline** (`YMGap/Continuum/`, ~460 files): OS reflection positivity
  (`ReflectionPositivity`), the located spectral gap of the compact finite transfer operator
  (`LocatedSpectralGap`), the functional continuum target (`FunctionalContinuumTarget`, OS0–OS4 +
  GNS, *not* a σ-additive measure — the Minlos atom was deleted by architecture), the defect-
  recursion / Grönwall fold (`DefectGapRecursion`, `HierarchicalMassGap`).
- **The frontier** (`YMGap/Rubric/`, `YMGapGuard`, `Tier0Scorecard`): the guarded Clay-frontier
  types + `FrontierDAG` as the single source of truth for open atoms (anti-proliferation Rule 9.8).
- **2D adequacy** (`TwoDYangMillsAdequacy`, new): a genuinely-inhabited d=2 analogue certifying the
  interfaces compose with real field theory — the interface-debt defense.

## 4. Proved vs. open (the honest ledger)

**Proved (axiom-clean, non-vacuous):** fixed-spacing strong-coupling gap kernel; OS2 reflection
positivity (unconditional, via Osterwalder–Seiler/Schur); the uniform all-simple-groups → SU(2)
reduction; the hierarchical (Dyson/MK) mass gap with exact quadratic defect and Weierstrass floor;
the 2D YM adequacy inhabitant; the Penrose const-weight deletion–contraction inequality
(`penroseIneqConst`); the θ₄ anchor; the located spectral gap machinery.

**Open (the frontier):** see §5. The binding wall is `singleStep`; the continuum obstruction is
`ClayContinuumExistence`; D=0 (no guard-verified atom discharged yet).

## 5. The frontier atoms and how to attack them (`docs/frontier-triage.md`)

**Category A — known math to constructivize (tractable; closes real atoms; MOVES D off 0):**
- **A1 `(T′)` tree-graph bound** [~90%]: Penrose/Poghosyan–Ueltschi. Sole residual = the **Ursell
  pin** (`UrsellPinConst`) — the classical Ursell/Mayer coefficient identity. *Closest discharge.*
- **A3 `hadd`**: the eigenvalue↔margin dictionary (transfer-matrix/Perron–Frobenius; textbook). The
  2D adequacy test shows the interface composes.
- **A2 `(D1)`**: Mayer–Ursell cluster expansion (Brydges; Kotecký–Preiss convergence layer present).

**Category B — genuinely new math (the research campaign; collaborator leverage is here):**
- **B1 `singleStep`**: the real 4D SU(N) defect budget — `step` + summable `(δ+ε)` + `(1−Σδ)m₀>Σε`.
  Primary attack = **item 12 Koch–Wittwer certified RG** (`docs/alternative-routes-to-singlestep.md`):
  finite truncation + exact interval arithmetic (Q' substrate) + one analytic truncation-error
  lemma. De-risked by item 9 Python scouting.
- **B2 `hlocalize`**: the p≥2 fusion local-CLT = the R1 uniform-in-`s` `UniformCurvatureEnvelope`
  `Δ²V(s)+2 ≥ (144/25)w²(1−w²)` (log-concavity/discrete-Gaussian; windows `s=0..6` proved, tail open).

## 6. Where a collaborator has the most leverage

**Category B, and specifically the item-12 truncation-error lemma.** The certified-arithmetic and
guard scaffolding is built and reusable; what needs a domain expert is the one analytic lemma
bounding the truncation error of the block-spin map (Balaban-class analysis) and the B2 theta-saddle
log-concavity. An expert in constructive/rigorous RG (Koch–Wittwer lineage), cluster expansions
(Brydges, Ueltschi), or resurgence (Dunne–Ünsal) plugs directly into a scaffold that already turns
their estimates into machine-checkable objects. The reviewer-recruitment net should also include the
stochastic-quantization community (Chandra–Chevyrev–Hairer–Shen) as a watch-and-inform channel
(`docs/alternative-routes-to-singlestep.md`, item 14).

## 7. Key files (index)

- Verify: `Makefile` (`lean-audit`, `lean-frontier-guard`, `lean-rubric`), `scripts/lean_axiom_audit.py`,
  `scripts/frontier_status.py`, `scripts/frontier_burndown.py`.
- Guards: `lean/YMGapGuard.lean`, `lean/YMGap/YMGapStatementGuard.lean`, `lean/AXIOM_AUDIT.md` (hashed).
- Frontier truth: `lean/YMGap/Rubric/FrontierDAG.lean`, `Tier0Scorecard.lean`, `ClayScorecard.lean`.
- Substrate: `lean/YMGap/Constructive/Rationals.lean`, `CReal*`, `RingNormaliser.lean`.
- Honest accounting: `docs/clay-open-boundary-ledger.md`, `docs/frontier-burndown.md`,
  `docs/frontier-triage.md`, `docs/regime-qualifiers.md`, `docs/q-representability-audit.md`,
  `docs/alternative-routes-to-singlestep.md`, `docs/mathlib-freedom-memo.md`.

## 8. The honesty discipline (how the project avoids fooling itself)

Every agent deliverable is adversarially verified (build green, guard OK, axiom-clean, non-vacuous);
dead routes are machine-refuted and recorded (SixJ pentagon channel-mismatch, Brydges–Kennedy forest
swap, single-scale Bakry–Émery curvature, the univariate Racah route — all refuted with the reason);
reductions are never presented as endpoints. The burn-down metric (D/F/C) is the guard against
mistaking reduction-churn for progress. The standing rule: **never claim closure that is not
machine-checked and axiom-clean, and never present a reduction as an ending.** The problem is OPEN;
the discipline is what makes the "open" trustworthy.
