# Canonical one-page project status

Chart schema: **1**. Snapshot: **6**, 2026-09-24 UTC. Source checkpoint:
the conditional spectator-pairing and channel-tail milestone committed with this snapshot;
verification is recorded in `audits/AUDIT-CONDITIONAL-CHANNEL-TAIL-2026-09-24.md`.
This is the single source for user-facing ASCII progress charts.
The baseline preserves the last displayed chart's wording, layout and
symbols; subsequent updates are maintenance, not redesigns.

## Fixed interpretation

- `[x]`: the EXACT displayed claim is proved and Lean-kernel-checked within
  its recorded scope. "Checked" is evidence for "proved," not a separate
  completion status. A typechecked interface, numerical test, conditional
  theorem or proved sublemma does not close a broader obligation.
- `[ ]`: the displayed obligation is open. Proving a sublemma does not
  change this marker until the whole displayed claim is established.
- `[OPEN]`: the whole-goal header/footer spelling of `[ ]`.
- `<-- CURRENT FRONTIER`: primary active work, independently of proof status.
  Parallel activity is recorded by permanent node ID below.
- Arrows: required dependency flow, NOT a claim that open joins are proved.
  The AND-join requires all its inputs on the SAME resulting theory.
- The checked "Conditional survival theorem" is the implication ONLY;
  its missing input and unproved survival conclusion remain separate nodes.

## Chart

```text
WHOLE-PROJECT GOAL                                      [OPEN]
Constructive Lean Yang-Mills on R^4, EVERY compact simple group:
nontrivial SAME theory, full QFT axioms, isolated vacuum,
and a finite positive physical mass gap: 0 < Delta < infinity.

[x] Checked within stated scope     [ ] Still open

EXPANSION: work backward from the goal into necessary inputs.
CONTRACTION: work forward, joining only proved SAME-object facts.

              ORIGINAL SU(2) LATTICE THEORY [x]
                            |
             +--------------+---------------+
             |                              |
             v                              v
     NONTRIVIALITY BRANCH               GAP BRANCH
     ONE excitation                    EVERY centered state
             |                              |
 [x] Exact plaquette heat images   [x] SAME reflected completion
 [x] Signed energy: 4E+D=2J        [x] Transfer + vacuum sector
             |                              |
             v                              v
 [ ] Complete signed cost versus   [x] Strict completed T^2 bound
     SAME interacting variance        at FIXED coupling/width
     on a justified scaling family          |
             |  <-- CURRENT FRONTIER        v
             v                         [ ] Spatial and spacing
 [x] Conditional survival theorem           control of the rate
     (requires the missing input)           |
             |                              v
             v                         [ ] EVERY-state decay
 [ ] ONE nonzero excitation survives        survives scaling
             |                              |
             +--------------+---------------+
                            |
                            v
 +------------------ REQUIRED AND-JOIN ----------------------+
 | [ ] SAME thermodynamic + continuum limits, explicit moduli |
 | [ ] Full Hilbert/OS/QFT structure and YM fields/UV behavior |
 | [ ] Physical time, Hamiltonian, and mass calibration       |
 | [ ] Construction for EVERY compact simple gauge group     |
 |     All branches must describe the SAME resulting theory. |
 +--------------------------+--------------------------------+
                            |
                            v
                 WHOLE-PROJECT GOAL [OPEN]
```

## Permanent node registry and scope

IDs are never recycled. They identify the fixed labels above without widening
the diagram. This is presentation bookkeeping, not a new Lean frontier bundle.

| ID | Fixed label | Scope / evidence |
|---|---|---|
| G00 | WHOLE-PROJECT GOAL | Unchanged target in the opening of `work_plan.md`. OPEN. |
| F00 | ORIGINAL SU(2) LATTICE THEORY | Finite original action, heat factors and observables underlying the consumers below; NOT continuum Yang--Mills. |
| A01 | Exact plaquette heat images | `BF4ExactSlabFixedSpatialPlaquetteSquare.plaquette_fullRange` and `.plaquetteSquare_fullRange`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteSquare.lean:139`, `:165`; actual bare product heat, supported-Haar equivalence, explicit cutoff guards. |
| A02 | Signed energy: 4E+D=2J | `BF4ExactSlabFixedSpatialSourceYoungExplicit.padded_terminal_plaquette_young_channels`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceYoungExplicit.lean:115`; original complete projected source and correction. |
| A03 | Complete signed cost versus SAME interacting variance on a justified scaling family | OPEN original-source estimate for ONE family, or direct response alternative. |
| A04 | Conditional survival theorem (requires the missing input) | `BF4ExactSlabFixedSpatialJointEnergySurvival.response_floor_of_relative_energy`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointEnergySurvival.lean:112`; supplied relative energy and positive norm floor, SAME fixed-width carrier. |
| A05 | ONE nonzero excitation survives | OPEN compatible changing-scale observable and nonzero response. |
| B01 | SAME reflected completion | `BF4ExactSlabFixedSpatialJointPhysicalTime.JointCompletion`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointPhysicalTime.lean:111`; fixed-width carrier. Full Hilbert/QFT packaging remains J02. |
| B02 | Transfer + vacuum sector | Original `jointCompletedTime`, `jointCompletedUnit` and orthogonality used by `completed_twoStep_form_gap` below; discrete time, not a continuum Hamiltonian. |
| B03 | Strict completed T^2 bound at FIXED coupling/width | `BF4ExactSlabFixedSpatialJointCompletedGap.completed_twoStep_form_gap`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointCompletedGap.lean:150`; EVERY vacuum-orthogonal vector, nome/width-dependent rate. Complex extension: `BF4ExactSlabFixedSpatialJointComplexGap.complex_twoStep_form_gap`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointComplexGap.lean:117`. |
| B04 | Spatial and spacing control of the rate | OPEN; fixed-parameter strictness is not scaling control. |
| B05 | EVERY-state decay survives scaling | OPEN; one surviving excitation does not supply a universal bound. |
| J01 | SAME thermodynamic + continuum limits, explicit moduli | OPEN; cutoff/time-window limits are not the full physical limit. |
| J02 | Full Hilbert/OS/QFT structure and YM fields/UV behavior | OPEN; algebra, represented completeness and pairing inequalities are partial prerequisites. |
| J03 | Physical time, Hamiltonian, and mass calibration | OPEN; discrete transfer and scalar logarithmic rates do not identify a physical Hamiltonian or mass edge. |
| J04 | Construction for EVERY compact simple gauge group | OPEN; an SU(2) proof cannot close this node. |

Verification context: `audits/AUDIT-FOUR-LINK-SQUARE-YOUNG-2026-09-24.md`,
`audits/AUDIT-SURVIVAL-QUANTIFIERS-2026-09-24.md`, and the complex-time
checkpoint in `work_plan.md`. These record targeted checks, not a fresh
full-tree build or full axiom audit.

## Activity and changes since the preceding chart

- Primary active node: **A03**. The COMPLETE original projected endpoint source
  now has a proved conditional mixed-positive pairing retaining shared active
  variables. Its cone controls the SAME spectator quadratic, and its computed
  one-link harmonic tail is epsilon-small after summing the actual plaquette
  channels, uniformly in width/depth/sufficiently late cutoff at FIXED nome.
  Next: joint four-active-link retained heat and SAME centered-variance/scaling
  comparisons. A one-link tail does not supply either comparison. Partial
  productMap is not the conditional operator, and signed channel sources are
  not asserted positive. A03 remains `[ ]`; the positivity-only shortcut stays
  excluded by `fa0cd1f`.
- Parallel node: **J02**. Sharp complex pairing work supplies prerequisites;
  `JointComplexCauchySchwarz.inner_cauchySchwarz` now reaches the SAME completed
  carrier, and `JointComplexSharpContinuity.time_pairing_converges` supplies
  its actual constant-one matrix-coefficient consumer. The full node remains
  `[ ]`; no continuum, full-QFT or physical-mass closure is claimed.
- Goal-node status changes: **NONE**.
- Displayed wording/layout/symbol changes: **NONE**. The chart block is
  unchanged from snapshots 1--5; this snapshot records only new proof evidence.

## Maintenance contract

1. Read this file before every chart. Copy its chart block; do not regenerate
   the arrangement or paraphrase labels. Always show the whole-project goal.
2. Change a proof marker only with evidence covering the EXACT node's
   carrier, action, quantifiers, parameters and limits. Record the old marker,
   new marker, declaration, verification scope and reason here.
3. Record partial proofs and conditional compilers as evidence/activity;
   do not rename or silently shrink their parent goal node.
4. Keep activity separate from proof status. Record movements of the primary
   frontier by old/new ID; list parallel work separately.
5. Necessary wording, geometry or semantic corrections require a new schema
   version, explicit old-to-new ID/label mapping, and a user-facing explanation.
   Preserve superseded versions in Git; never recycle IDs or silently add glyphs.
6. Every delivered update states what mathematically changed since the last
   snapshot. Say "no status change" when appropriate. Formatting is not progress.
7. Refuted shortcuts go in the evidence/change record; they do not replace
   original goal nodes. This contract does not freeze an erroneous mathematics
   claim: correct it explicitly, with evidence and migration history.

## Snapshot history

| Schema / snapshot | Date (UTC) | Change |
|---|---|---|
| 1 / 1 | 2026-09-24 | Freeze last displayed chart; add permanent IDs, fixed meanings and evidence rules. No goal-node status change. |
| 1 / 2 | 2026-09-24 | Sharp complex Cauchy--Schwarz and explicit matrix-coefficient consumer on the SAME completion. Partial J02 evidence only; no chart-block or goal-node status change. |
| 1 / 3 | 2026-09-24 | Quantitative original-source geometric energy budget with signed correction retained. Partial A03 evidence only; SAME variance/scaling comparison open. No chart-block or goal-node status change. |
| 1 / 4 | 2026-09-24 | Spectator-retaining geometric budget, coefficient-one contraction, and SAME moments with exactly four active heat blocks. Partial A03 evidence only; channel-aggregated SAME variance/scaling comparison open. No chart-block or goal-node status change. |
| 1 / 5 | 2026-09-24 | Complete original-source local angular bound and explicit one-link harmonic-tail modulus at fixed nome. Partial A03 evidence only; conditional spectator quadratic and SAME variance/scaling comparison open. No chart-block or goal-node status change. |
| 1 / 6 | 2026-09-24 | Conditional original-kernel mixed positivity and computed harmonic tails in the SAME actual spectator-channel quadratic. Partial A03 evidence only; joint four-link heat and SAME variance/scaling comparisons open. No chart-block or goal-node status change. |
