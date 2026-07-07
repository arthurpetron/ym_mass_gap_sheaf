# Codynamic-tool application map across the YM mass-gap proof

Top-down survey of where the seven codynamic tools (from the verified Agda spec
`Codynamic/{Metric,Trajectory,Island,Coherence,Complexity}.agda`) apply to the
YM mass-gap Lean program. Ranked most-load-bearing first. Each site carries an
honest verdict: **(i) genuine structural gain**, **(ii) bookkeeping** (re-expresses
proved content), or **(iii) mismatch**.

The seven tools:
1. **Reflection-unit defect** (`Metric.unit-defect`, `εX`) — error = metric size of what a coarse-graining identifies.
2. **Monotone (nonlinear) modulus** (`Metric.Lipschitz.scale : Q→Q`) — per-step degradation as a monotone map, subsuming multiplicative Lipschitz.
3. **Compositional error law** (`Metric.eqBound-◅◅`) — defects compose additively along substitution.
4. **n-step Grönwall fold** (`Trajectory.nstep-d`) — `e_n ≤ (∏scale)e_0 + Σ(∏scale)η_i` as a monotone-scaling left fold that transports certificates.
5. **Islands of predictability** (`Island.lem:island-free`) — regions where the completion is free/discrete, cost collapses.
6. **Evolution monad / graded** (`Coherence.extendsBy`) — n-step evolution as a graded monad, descending to a monad on kernel-stable states.
7. **Complexity-as-budget** (`Complexity.cert-budget`) — the tameness measure = a step-count / summable budget.

---

## 0. The one-paragraph verdict (read this first)

The entire proved part of the YM continuum floor **already IS** the codynamic
`nstep-d` fold, hand-rolled twice in Lean:
`DefectGapRecursion.prodPrefix_le_physGap` (multiplicative form, `scale_k(b)=(1−δ_k)·b`,
per-step `η=0`) and `Codynamic.InductiveBoundWitnessSystem.terminal_invariant_bound`
(additive form, `scale=id`, `η_k=degradation_k`). The single open atom `singleStep`
(`realδ_k ≤ δ_model(w_k)`, i.e. `(1−δ_model_k)·trueMargin_k ≤ trueMargin_{k+1}`) is
**exactly the `lip` / `unit-defect` hypothesis** that the codynamic fold *consumes and
never proves*. Consequence, stated bluntly against the anti-loop ledger: porting the
codynamic fold as a fresh "whole-gap ⇐ singleStep" reduction would emit another
`:= SingleStepDefectBound` alias — a **provable loop, forbidden**. The codynamic
toolkit's genuine value is therefore **not** a new top-level reduction. It is two
things: **(A) a real dedup/generalization** — one monotone-modulus fold subsumes the
two separate Lean folds and, unlike the linear `InductiveBoundWitnessSystem`, closes
where the additive middle budget provably fails (`Σδ≈2.54>1`); and **(B) the only
codynamic construct that can touch the atomic core** — the *reflection-unit-defect =
certificate-weight* route (tools 1+3+4 at the **intra-block** scale), which would
DERIVE the per-block defect `realδ_k` from summable per-*move* (per-bond) local
defects. (B) is the sole candidate for a genuinely-new, ledger-legal (clause b) attack
on `singleStep`.

---

## 1. Critical-path DAG, codynamically annotated

```
mass_gap  ⇐  rgFlow_gap_conditional ∧ MultiScalePolymerExpansion        [PROVED assembly]
          ⇐  additiveErosion_uniform_floor                             [= Grönwall fold, ADDITIVE form  → tool 4/3/7]
          ⇐  DefectGapRecursion (fullFloor_of_defectRecursion)         [= Grönwall fold, PRODUCT form   → tool 4/2]
                 └ prodPrefix_le_physGap                                [= nstep-d, scale_k(b)=(1−δ_k)·b, η=0]
          ⇐  singleStep : realδ_k ≤ δ_model(w_k)                       [ATOMIC CORE  → tool 1 (unit-defect) = the `lip` INPUT]
                 ├ free/AF deep-UV tail  (δ_k→0 ~1/k²)                  [→ tool 5 ISLAND: cost collapses, Σδ<∞]
                 ├ hierarchical lattice  (δ=0 exact)                    [→ tool 5 ISLAND: free-discrete, no-step]
                 └ finite middle window  (K_mid=3, the Bałaban residual)[→ NON-island core; tool 4 at intra-block = route (B)]
```

Supporting/organizational nodes:
```
RG scales / running Λ = ∏ t_k        [ScaleSheaf: locally-trivial-globally-nontrivial → tool 5 island boundary + tool 6 graded]
CodynCat budget-domination transport [Categorical/{CodynCat,BudgetDomination}: worst-case domination → tool 5 island / tool 6]
RGCategory coarsening presheaf       [→ tool 6 evolution monad candidate; currently metric-free]
```

---

## 2. Ranked application sites

### SITE 1 — the atomic core `singleStep` as a REFLECTION-UNIT DEFECT, and its intra-block Grönwall decomposition  ★ highest value

- **Node:** `SingleStepDefectReduction.singleStep` (`realδ_k ≤ δ_model(w_k)`), the F=1 core.
- **Tools:** #1 (unit-defect / εX) + #3 (compositional error law) + #4 (nstep-d), applied at the **intra-block (per-bond-move)** scale.
- **Precise mapping.** One 4D SU(N) block-spin step is a coarse-graining / lawful
  completion `φ` (the block map `nfOf`). `realδ_k = d(eval(fine), eval(nfOf fine))` is
  *verbatim* the codynamic `unit-defect`: the metric size of what the block map
  identifies. The `unit-defect` corollary prices it by the **weight of its own
  normalizer certificate**: `realδ_k ≤ derivBound(normalize) = Σ_moves stepBound(move)`.
  A block-spin step on ℝ⁴ = decimation ∘ bond-moving, and bond-moving = a *finite
  sequence of local Migdal–Kadanoff bond-moves*. Model each move as one rewrite step;
  `stepBound(move) = scale_move(η_move)` with `η_move` the local heat-kernel
  interpolation defect and `scale_move` the (favorable, `<1`) decimation Lipschitz
  factor `ρ_dec`. Then `nstep-d` over the intra-block move-trajectory gives
  `realδ_block ≤ Σ_moves (∏ downstream ρ_dec)·η_move`.
- **What it would buy.** This DECOMPOSES the atomic per-**block** defect into per-**move**
  local defects + the fold (free). The per-move object is single-local-heat-kernel,
  finite, and on the hierarchical lattice is provably **zero** (`CodynamicHierarchical`,
  `exactLoss=0`). The ℝ⁴ residual is then localized to *one bond-move* interpolation
  error rather than the whole multi-link non-abelian block — a strictly smaller,
  single-scale object.
- **Verdict: (i) genuine — the ONLY codynamic route that can legally attack the core.**
  Under the ledger this is a legitimate **clause-(b)** move (decompose into
  strictly-weaker independent pieces + a proved `(⋀ per-move) → singleStep`), *provided*
  the per-move bound is certified strictly weaker (single local move / finite vs
  all-scale block). **Honest caveat / failure mode:** if the per-move defects merely
  re-aggregate to the same whole-block object with no independent per-move handle, the
  "decomposition" collapses back to `singleStep` and it is a **loop (clause fails)** —
  exactly the trap the ledger's `SingleStepDecompositionAdjudication` already caught
  once. The gain is real *iff* the local-move interpolation defect is a genuinely
  simpler analytic object than the block defect (it plausibly is: one plaquette
  heat-kernel interpolation vs the full 4D multi-link fusion). This is where to point
  a new Lean codynamic tool.

### SITE 2 — the product-floor fold `DefectGapRecursion` as a monotone-modulus `nstep-d`  ★ high (dedup + strict generalization)

- **Node:** `ContinuumClosureProgram.DefectGapRecursion.prodPrefix_le_physGap` / `uniform_floor` / `fullFloor_of_defectRecursion`.
- **Tools:** #4 (nstep-d) + #2 (monotone nonlinear modulus).
- **Precise mapping.** `prodPrefix_le_physGap` is **exactly** `Trajectory.nstep-d`
  specialized to a **linear multiplicative** modulus `scale_k(b) = (1−δ_k)·b = ρ_k·b`,
  per-step defect `η_k = 0` (homogeneous recursion `(1−δ_k)·physGap_k ≤ physGap_{k+1}`),
  initial certificate `b_0 = physGap 0`. The Lean `prodPrefix` product IS the codynamic
  `∏ scale`; `uniform_floor` composed with `prodFloor_le` is the closed-form
  `(∏scale)·e_0` reading. The proof structure (induction, `mul_le_mul_of_nonneg`,
  associativity juggling) reproduces `nstep-d`'s `≤-trans (triangle) (+-mono (lip …) …)`
  in the `η=0` degenerate case.
- **What it would buy.** A single Lean `nstep-d`-style theorem parameterized by an
  abstract monotone `scale : Nat → Q' → Q'` would **subsume both** `prodPrefix_le_physGap`
  (product form) **and** `InductiveBoundWitnessSystem.terminal_invariant_bound` (additive
  form, `scale=id`, `η=degradation`), which are currently two independent hand-rolled
  developments. Crucially, it also **covers the regime where the linear/additive fold
  provably fails**: `CrossoverDefectUnification.middle_additive_budget_exceeds_one`
  proves `Σδ≈2.54>1`, killing the additive `1−Σδ` coefficient; the *product* fold
  (monotone `scale=ρ_k·(−)`) survives because it needs only `Σδ<∞`. A nonlinear `scale`
  further allows scale-dependent moduli the current linear `ρ_k` cannot express (e.g. a
  saturating modulus for large-field steps).
- **Verdict: (ii) mostly bookkeeping, with a (i) generalization edge.** The *content*
  (per-step ⇒ uniform distillation) is already fully proved in Lean; a port re-expresses
  it. The genuine gains are (a) **dedup** of the two folds under one theorem, and (b)
  **expressive reach** — a monotone/nonlinear `scale` is strictly more general than
  `ρ_k·(−)` and is the honest home for the "product beats additive" insight the codebase
  discovered ad hoc. Not new analytic content; a real consolidation + future-proofing.

### SITE 3 — the AF deep-UV tail and the hierarchical lattice as ISLANDS  ★ medium-high

- **Nodes:** `SingleStepDefectReduction.freeEnd_defect_scaleExact` (δ_ren=0 at w=1);
  `CodynamicHierarchical` D1 (`exactLoss=0`, bond-moving = decimation on the diamond
  lattice); the deep-UV `Σ1/k²` summable tail; `CondensateGeometricErosion` (geometric
  `ε_k = K·r^k`).
- **Tool:** #5 (islands of predictability, `lem:island-free` / `no-step` / `free-discrete`).
- **Precise mapping.** An island = a region where the completion's saturation is *empty*
  (no identities, no witness relations to price), so the congruence is discrete and
  prediction is canonical at **zero cost**. The **free/Gaussian UV fixed point** (w→1)
  and the **hierarchical lattice** are exactly islands: the reflection-unit defect
  collapses to `0` (`no-step` ⇒ `unit-defect = 0`). The whole RG trajectory then splits
  codynamically into a **free island** (deep UV, where `δ_k→0~1/k²` gives a convergent
  tail — cost collapses to a finite budget) **plus a finite non-island core** (the
  middle `K_mid=3` steps = the genuine Bałaban residual, `middle_is_three_steps`,
  `no_uncovered_middle_step`).
- **What it would buy.** The abstract `lem:island-free` is the general theorem behind
  "the free UV / hierarchical step erodes nothing," currently proved as separate ad-hoc
  instances. It also gives the *principled* trajectory decomposition: **island tail
  (free) ⊕ finite core (hard)** — which is precisely the shape the codebase already
  arrived at, and which localizes the hard problem to a finite decidable window.
- **Verdict: (ii) bookkeeping that cleanly organizes, borderline (i).** The specific
  islands (w=1, hierarchical, `1/k²` tail) are already proved. The island *theorem*
  would unify them and license the tail/core split as a general move rather than a
  hand-built one. It does **not** supply the finite-core estimate (that is SITE 1). Its
  value is organizational + a reusable "cost-collapse on free boundary" lemma.

### SITE 4 — additive erosion / summability as COMPOSITIONAL ERROR LAW + COMPLEXITY BUDGET  ★ medium

- **Nodes:** `AdditiveErosionAdequacy.additiveErosion_uniform_floor`;
  `Codynamic.InductiveBoundWitnessSystem` (`budget_summable`, `terminal_invariant_bound`);
  `MultiScalePolymerAssembly`; `SummabilityCapstone` (`renDefect_summable`).
- **Tools:** #3 (compositional error law `eqBound-◅◅`, defects add along composition) + #7 (complexity-as-budget, `cert-budget`).
- **Precise mapping.** The total defect over a composite of block steps = the sum of
  per-step defects (`eqBound (e ◅◅ e') ≡ eqBound e + eqBound e'`), which is exactly
  `finSum degradation N` / `Σδ_k` = the **log of the product floor**. The summability
  hypothesis `Σδ_k ≤ budget` is the codynamic **step-count/measure budget** `μ t`
  bounding the certificate length; `additiveErosion_uniform_floor` is `terminal_invariant`
  (running total + gap ≤ initial).
- **Verdict: (ii) bookkeeping.** This is a faithful match, but every piece
  (`InductiveBoundWitnessSystem`, `additiveErosion_uniform_floor`) is *already* the Lean
  realization of these two tools — indeed `YMGap/Codynamic.lean` is explicitly named
  after this correspondence. Re-expresses proved content; no new handle. (Its one live
  edge is the SITE-2 observation that the additive form *fails* on the middle and must be
  upgraded to the product/monotone fold.)

### SITE 5 — the RG evolution as a GRADED EVOLUTION MONAD (categorical layer)  ★ low-medium

- **Nodes:** `Categorical/RGCategory.lean` (coarsening presheaf `obsPresheaf`,
  `restrict_comp`), `Categorical/ScaleSheaf.lean` (running Λ = `∏ t_k`, cocycle),
  `Categorical/CodynCat.lean` (`transportClosure`), `HigherCategorical.lean`.
- **Tool:** #6 (evolution monad / graded, `extendsBy`) — and #5 at the sheaf boundary.
- **Precise mapping.** n-step RG evolution composes block steps; `Coherence.extendsBy`
  models this as an ℕ-graded monad whose laws are literal equalities, descending to a
  genuine monad on **kernel-stable states** = RG **fixed points** (UV free + IR). The
  coarsening functoriality `restrict_comp` and the scale cocycle `Lambda lo hi = ∏ t_k`
  (locally trivial = island boundary, globally nontrivial = genuine running) are the
  categorical shadows.
- **Verdict: (iii) mismatch for the analytic core / (ii) at best for organization.** The
  codynamic `Coherence` monad is **defect-free** (purely syntactic — it carries no
  metric). So the evolution monad does **not** transport the error, which is the entire
  content of the mass-gap problem. This is precisely why the categorical layer was
  previously judged "structure/reuse only, not analytic," and the **metric layer does
  not change that here**: the monad and the metric live in *different* codynamic modules,
  and the metric content attaches to the *trajectory fold* (`nstep-d`, SITE 2), not to
  the monad. Pursuing the monad for gap magnitude is a category error (magnitude ≠
  composition structure). Keep as organization only.

---

## 3. Does the metric/error layer upgrade the categorical layer beyond "structure/reuse only"?

**Partly, and only at SITE 2 — not at the categorical/monadic layer.** The previous
verdict ("CodynCat/RGCategory/ScaleSheaf = structure/reuse, not analytic") stands for
the *categorical* constructs, because the codynamic **monad** (`Coherence`) is
defect-free. The codynamic **metric** (`Metric`/`Trajectory`) *does* carry genuine
analytic content (real inequalities: `triangle`, `lip`, monotone `scale`, the fold) —
but the Lean development **already contains that content**, hand-rolled, in
`DefectGapRecursion` and `InductiveBoundWitnessSystem`. So the metric layer would give
the *fold* a principled home and unify/generalize it (SITE 2), and it would give the
*core* its correct name (unit-defect, SITE 1) — but it supplies **no new analytic
input**. The atomic bound `realδ_k ≤ δ_model` is the fold's *hypothesis*, forever. Net:
the metric layer promotes the fold from "two ad-hoc inductions" to "one calculus," which
is real but is **bookkeeping/consolidation**, not a shrink of the hard core. The honest
"structure/reuse only" label is correct for everything **except** the SITE-1
intra-block route, which is the one place a codynamic construct could produce a
genuinely-new, strictly-weaker obligation.

---

## 4. Prioritized short-list (where to point new Lean codynamic tools)

1. **[SITE 1 — pursue] Intra-block reflection-unit-defect decomposition of `singleStep`.**
   Build a Lean `nstep-d`/`unit-defect` fold at the *per-bond-move* scale that proves
   `realδ_block ≤ Σ_moves (∏ρ_dec)·η_move`, reusing `CodynamicHierarchical`'s
   `exactLoss=0` (η_move=0 hierarchical) and `CodynamicBondMoving`/`FullModeQuadratic`'s
   per-mode quadratic envelope. **Ledger gate before spawning:** it is legal ONLY if it
   yields a proved `(⋀ per-move bounds) → singleStep` **and** a certificate that the
   per-move defect is strictly weaker (single local heat-kernel move / finite vs
   all-scale block). If the honest prediction is "the per-move defects just re-sum to the
   block defect," it is a **loop — do not spawn** (SITE 1 caveat). This is the only
   codynamic item that can move D/F.

2. **[SITE 2 — build, low risk] Unify the two folds under one monotone-modulus `nstep-d`.**
   A single abstract theorem `scale : Nat → Q' → Q'` (monotone) subsuming
   `prodPrefix_le_physGap` (product) and `terminal_invariant_bound` (additive), with the
   `middle_additive_budget_exceeds_one` fact recorded as *why* the nonlinear/product
   modulus is mandatory. Pure consolidation + expressive reach; axiom-clean; no core
   movement, but retires duplicated machinery and future-proofs for scale-dependent
   moduli. Do this as a hardening artifact, **not** as a substitute for item 1.

3. **[SITE 3 — build, organizational] Island / cost-collapse lemma + tail⊕core split.**
   Port `lem:island-free` (`no-step ⇒ unit-defect=0`) as a general theorem, instantiate
   at w=1 and the hierarchical lattice, and license the "free deep-UV island ⊕ finite
   Bałaban core" decomposition as a named move. Organizes existing proofs; concentrates
   the hard problem onto the finite decidable middle (feeds item 1).

4. **[SITES 4–5 — do NOT prioritize] Additive/monad restatements.** SITE 4 is already the
   content of `YMGap/Codynamic.lean`; SITE 5 is defect-free and a magnitude/composition
   category error. Any "whole-gap ⇐ singleStep" via these is a **forbidden loop**
   (`C++`). Skip.

**Bottom line for the caller:** point the new Lean codynamic tools at **SITE 1** (the
only core-moving target, guarded by the ledger clause-(b) test), use **SITE 2/3** as
axiom-clean consolidation that makes the fold and the island-split first-class, and
treat **SITES 4/5** as already-done / off-limits (loop risk).
