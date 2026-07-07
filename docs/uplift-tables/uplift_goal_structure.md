# Codynamic-tool uplift survey — GOAL / FRONTIER / CATEGORICAL subtree

**Scope walked (26 modules, all read):** `lean/YMGap/MassGap/*` (3), `lean/YMGap/Rubric/*` (8),
`lean/YMGap/Sheaf/*` (6), `lean/YMGap/Categorical/*` (5), `lean/YMGap/Classical/MinlosQuarantine.lean` (1),
`lean/YMGap/HigherCategorical.lean`, `lean/YMGap/Codynamic.lean`, `lean/YMGap/BufferShell.lean` (3).
Read-only. No Lean modified, nothing committed.

**Tools:** T1 reflection-unit defect · T2 nonlinear monotone modulus · T3 compositional error law ·
T4 n-step Grönwall fold · T5 islands (free/discrete cost-collapse) · T6 evolution monad (graded, DEFECT-FREE) ·
T7 complexity budget.

**Headline for this subtree:** This is the layer where the codynamic tools are ALREADY INSTANTIATED
(Codynamic.lean = the additive fold; CodynCat/BudgetDomination = worst-case domination transport;
HigherCategorical = the graded fold as a 2-functor) or are pure bookkeeping / plumbing / rational-arithmetic
guards. The core-moving codynamic route (SITE 1, intra-block reflection-unit-defect decomposition of
`singleStep`) lives in `Continuum/*`, NOT here. Consistent with `codynamic-application-map-2026-07-07.md`,
NO node in my subtree is a core-shrinking GENUINE-GAIN. The only genuine (non-core) gains are consolidation /
expressive-reach edges on the fold and the island-boundary cocycle — flagged honestly below.

---

## Node-by-node table

| module | role (1 line) | applicable tool(s) | verdict | note |
|---|---|---|---|---|
| MassGap/SU2.lean | SU(2) mass-gap statement; Q'-rational `m₀=999/1000`, `m₀²≤σ̂∞`, OS-reconstruction interface | T7 (budget output consumed) | N/A | Consumes the fold's OUTPUT (`σ̂∞ = 1−Σηₖ`) as a `decide` constant; no fold/defect of its own. Pure arithmetic + interface plumbing. |
| MassGap/SimpleGroup.lean | Lifts SU(2) gap to every admissible simple group via `monotone_budget` (SU(2) = worst case dominates) | T5 (island/worst-case), T7 | DEDUP/BOOKKEEPING | "SU(2) budget dominates all `R`" IS the domination/cost-collapse pattern, but already fully proved (`budget_closes_uniform` via `RG.monotone_budget`). Codynamic naming re-expresses it; same content as CodynCat transport. |
| MassGap/AllSimpleTypes.lean | Per-Cartan-type (`A..E₈`) `RepData` witnesses + faithfulness; per-type Casimir floors | — | N/A | Rep-theory / `decide` instantiation of SimpleGroup's reduction. No metric, no defect, no fold. Group-enumeration bookkeeping. |
| Rubric/ClayScorecard.lean | Transcribes external Clay rubric into constructive vocab; `ClayTarget` carried UNINHABITED (guard) | — | N/A | Guard node. Codynamic tools cannot inhabit `ClayTarget`; the tools that could touch the core (T1) are the *hypothesis* the guard protects, not a producer. Bookkeeping-with-teeth. |
| Rubric/ClayTargetPinned.lean | Pins all Clay clauses to ONE shared OS/GNS stack (closes surrogate hole) | — | N/A | Structural pinning (shared-object identity). Orthogonal to metric/defect content. Plumbing. |
| Rubric/ContinuumScorecard.lean | Reduces open a→0 half to {SU(2) fusion local-CLT} + {cited Minlos lift} | T1 (names the defect target) | DEDUP/BOOKKEEPING | The reduction target is exactly the `singleStep`/reflection-defect object already adjudicated in `codynamic-recast-2026-07-07.md` (defect ≡ singleStep, needs interacting measure). Records, does not shrink. |
| Rubric/FrontierDAG.lean | All open continuum atoms as ONE uninhabited product node; `minlos` = guarded `ClayContinuumExistence` | — | N/A | Type-level inventory of residuals. No accumulation/composition to fold; a DAG of *distinct* atoms, not a trajectory. Bookkeeping. |
| Rubric/FrontierDAGBridges.lean | Adjudicates 4 suspected cross-list atom identifications (1 merge, 1 refute, 2 supplies) | — | N/A | Node-identity adjudication (rfl / refutation). No codynamic structure. Bookkeeping. |
| Rubric/LoopScorecard.lean | Consolidates r1→r8 parallel-loop tracks; names open cores (Core A/B) | — | N/A | Consumer record. Cores named are theta/fusion analytic walls, off this subtree. Bookkeeping. |
| Rubric/ReconstructionScorecard.lean | 3-way ledger (proved / proved-mod-residual / open) for Wilson-GNS reconstruction | — | N/A | Ledger. Residuals A/B are FC/Schur operator objects, not fold/defect. Bookkeeping. |
| Rubric/ReconstructionScorecardFinal.lean | Final OS/reconstruction status record consuming discharged witnesses | — | N/A | Consumer record. Bookkeeping. |
| Sheaf/Summability.lean | KP-certificate presheaf 𝒮ₖ scaffold; `KPCertificate (ρ,K)`, `restrict = c` | T7 (budget), T4 (weak) | DEDUP/BOOKKEEPING | The KP `K` IS the codynamic budget summand, but this module holds ONE cert with identity restriction — no accumulation. The actual Σδ fold lives in Codynamic.lean, not here. Scaffold only. |
| Sheaf/Gluing.lean | Buffer-overlap domination glue `domGlue = sup`; `domGlue_preserves_KP: K∩ ≤ K_sf+K_lf` | T3 (compositional error law) | DEDUP | `K∩ ≤ K_sf+K_lf` is a genuine additive-composition-of-defects instance (T3 `eqBound-◅◅`). But it is a hand-proved 2-object union bound over one overlap, not a naturality-derived law over a trajectory. T3 would give a marginally cleaner derivation; content already proved. |
| Sheaf/PolymerDomination.lean | Tightness of the union bound (`K_lf ≤ K_sf`, factor-2 `C≤2`) | — | N/A | Q'-arithmetic domination `s_sf(X) ≥ s_lf(X)`. Rational bookkeeping; no metric/fold. |
| Sheaf/Site.lean | Configuration site categorical scaffold (opens as Prop-predicates, cover, restriction) | T6 (site, defect-free) | N/A | Group-independent categorical plumbing. Defect-free; no analytic content. |
| Sheaf/SU2KP.lean | Concrete SU(2) KP certs from Casimir + normalization data (`ρ_sf`, `ρ_lf`, `decide`) | — | N/A | Pure Q'-rational `decide` derivation of certificate constants. Arithmetic. |
| Sheaf/BoundWitness.lean | Bound-witness presheaf 𝒜ₖ scaffold (flabby, domination gluing over `⊔`/`⊤`) | T5 (flabby/domination), T3 | N/A | Typeclass-level presheaf scaffold, empty axiom set, no concrete activity. Defect-free structure. |
| Categorical/BudgetDomination.lean | SU(2) = terminal worst-case object of a budget-domination category; closure transports to all groups | T5 (island/cost-collapse), T6 | DEDUP/BOOKKEEPING | Universal-property re-statement of `monotone_budget`; explicitly "NOT arithmetically independent," shares `truncatedConst_le`. Already-proved worst-case domination, categorically organized. |
| Categorical/CodynCat.lean | Budget systems as a category `CodynCat`; morphisms = budget-domination; `transportClosure` | T5, T6 (defect-free) | DEDUP/BOOKKEEPING | This module already IS the "worst case dominates ⇒ all close" transport = the codynamic domination pattern, hand-built. Thin, laws `rfl`, defect-free. Re-expresses proved content. |
| Categorical/Core.lean | Minimal `Eq`-Hom `Cat`/`Functor` substrate (non-Mathlib, MLTT-valid) | — | N/A | Category-theory plumbing shared by ObsCat/CodynCat. No analytic content. |
| Categorical/RGCategory.lean | RG site as category; coarsening `restrict` as genuine presheaf (`restrict_comp` for free) | T6 (evolution monad candidate, DEFECT-FREE) | MISMATCH | Functoriality-for-free is real reuse, but the presheaf carries NO metric; the codynamic monad (`Coherence`) cannot transport the error that IS the mass-gap content. Magnitude ≠ composition (category error for the core). |
| Categorical/ScaleSheaf.lean | Running Λ = ∏tₖ as a Čech 1-cocycle: locally trivial, globally nontrivial | T5 (island boundary), T6 (graded) | DEDUP (borderline GAIN) | The "locally-trivial / globally-nontrivial ∏tₖ" IS structurally the T5 island-boundary + T6 graded evolution. Defect-free, so no core movement, but T5's `island-free` boundary is the *principled name* for this anomaly (see gains list). Currently hand-built at `eqv`. |
| Categorical/RGCategory + ScaleSheaf (monad view) | n-step RG evolution as graded monad over fixed points | T6 (DEFECT-FREE) | MISMATCH | Per SITE 5: the graded monad carries no metric, cannot supply the defect. Keep as organization only. |
| Classical/MinlosQuarantine.lean | Cited-classical Bochner–Minlos σ-additive a→0 lift; UNINHABITED interface | T1 (the object the defect needs) | N/A | This IS the interacting a→0 measure that T1's reflection defect `d(⟦bs⟧fine, coarse)` requires — but it is an external cited input the tools cannot supply, deliberately uninhabited. Not a tooling site. |
| HigherCategorical.lean | RG flow as a thin 2-functor `F_RG: RG → SheafBudget`; lifts the fold's Θ-cells | T6 (graded evolution monad), T4 (the fold it lifts) | MISMATCH | The 2-functor is the graded-monad packaging of the additive fold — DEFECT-FREE. Composition-of-Θ-cells = partial sums is real structure but transports no error. Category error for gap magnitude. |
| Codynamic.lean | The abstract `InductiveBoundWitnessSystem`; `terminal_invariant_bound` = the ADDITIVE fold; SU(2)+EKF instances | T4 (fold), T3, T7 (budget) | DEDUP/BOOKKEEPING (with T2 GAIN edge) | This module literally IS the codynamic additive `nstep-d` fold (`scale=id`, `η=degradation`), hand-rolled. SITE-2 gain: it is the fold that PROVABLY FAILS on the middle window (`Σδ≈2.54>1`); a T2 nonlinear/product-modulus fold strictly subsumes it AND survives (`Σδ<∞`). See gains list #1. |
| BufferShell.lean | Single-plaquette buffer-shell bound; `decide` over a Q'-rational grid sample | — | N/A | Pure interval-arithmetic `decide` certificate. No metric/fold/defect. |

---

## GENUINE-GAIN nodes (ranked) — honest, none core-moving

Consistent with the two application docs: **no module in this subtree yields a strictly-weaker
reduction below `singleStep`.** The core-mover (SITE 1) is in `Continuum/*`. Within my subtree the
only genuine (consolidation / expressive-reach) gains are:

1. **`Codynamic.lean` — T2 nonlinear-modulus upgrade of the additive fold (value: LOW, consolidation).**
   Concrete reason: `terminal_invariant_bound` is the additive fold (`scale=id`, per-step `η=degradation`),
   and this exact additive form is the one that **provably fails** on the finite middle window
   (`CrossoverDefectUnification.middle_additive_budget_exceeds_one`, `Σδ≈2.54>1`). A single T2 monotone-modulus
   `nstep-d` theorem (`scale : Nat → Q' → Q'` monotone) would **subsume both** this additive fold AND the
   product fold `DefectGapRecursion.prodPrefix_le_physGap` (in `Continuum/`) under one calculus, and covers the
   failing-middle regime (product survives on `Σδ<∞`). This is "for-free composition + a cleaner proof not
   already present in one place." NOT core-moving (the atomic `singleStep` remains the fold's hypothesis) —
   an axiom-clean hardening artifact, exactly SITE 2 of the application map.

2. **`Categorical/ScaleSheaf.lean` — T5 island-boundary as the principled name for the ∏tₖ cocycle
   (value: LOW, organizational; borderline DEDUP).**
   Concrete reason: the module's central object — Λ = ∏tₖ "locally trivial, globally nontrivial" — is
   structurally the codynamic T5 island boundary (`no-step ⇒ unit-defect = 0` on each local trivialization,
   nontrivial global running). Porting `lem:island-free` would give this anomaly its general theorem rather
   than the hand-built `eqv`-cocycle, and license the "free deep-UV island ⊕ finite Bałaban core" trajectory
   split as a NAMED move. Defect-free, so no core movement; pure organization. Feeds, but does not supply,
   the finite core (SITE 3).

3. **`Sheaf/Gluing.lean` — T3 compositional-error-law reading of `domGlue_preserves_KP` (value: MINIMAL).**
   Concrete reason: `K∩ ≤ K_sf + K_lf` is a bona-fide additive composition of two defect certificates (the
   T3 `eqBound-◅◅` shape). T3 derives such additivity from naturality for free; here it is a hand-proved
   union bound. A marginally cleaner derivation only — the content is already proved; not core-moving.

**Everything else** is DEDUP/BOOKKEEPING (scorecards, worst-case-domination transport already proved) or
N/A (rational-arithmetic guards, categorical plumbing, defect-free monad/presheaf structure). The two
defect-free categorical nodes that were hoped to help the core — `RGCategory`, `HigherCategorical`,
and the graded-monad view of `ScaleSheaf` — are **MISMATCH**: the codynamic evolution monad (T6) carries no
metric and cannot transport the mass-gap error, so pursuing them for gap magnitude is a category error
(re-confirming the standing "structure/reuse only, not analytic" verdict for the categorical layer).

**Guarded-frontier answer (asked in the brief):** the guarded nodes `ClayScorecard.ClayTarget`,
`FrontierDAG`, `Tier0`/`ContinuumScorecard` do **NOT** gain from the codynamic structure — the codynamic
construct that could touch the core (T1 reflection-unit defect) is precisely the *hypothesis* those guards
protect (`singleStep` ≡ the interacting per-block defect), not a producer that could inhabit them. The
Categorical/Codynamic layer already instantiates T4 (Codynamic.lean), T5/T6 (CodynCat, BudgetDomination,
HigherCategorical, ScaleSheaf); what is missing is only the T2 monotone-modulus unification (gain #1) — and
that is consolidation, not closure.

Modules I could not read: none — all 26 assigned modules were read (headers + main signatures).
