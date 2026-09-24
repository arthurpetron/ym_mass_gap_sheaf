# Canonical one-page project status

Chart schema: **1**. Snapshot: **10**, 2026-09-24 UTC. Source checkpoint:
the literal all-nome Wilson completion/time milestone committed with this
snapshot; verification is recorded in
`audits/AUDIT-ALL-NOME-WILSON-COMPLETED-TIME-2026-09-24.md`.
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

- Primary active node: **A03**. Literal Wilson squares now have side L=2^s,
  assigned spacing 2^-s, unit geometric side and a computed spacing modulus.
  Their original increment bound has a SAME reflected-form consumer:
  2*(F(x,x)-F(x,advance L x))<=384*L^3*(1-w). The cubic cost remains. This is not useful
  relative control without the SAME centered-variance comparison and a
  justified scaling trajectory. The complete signed-source route remains
  available; the preceding coarse coefficient limitation is unchanged.
  A03 stays `[ ]`: no nonzero limiting norm or continuum premise is supplied.
- Parallel node: **J02**. `BF4WilsonAllNomeCompletedInner` now constructs
  the literal-width all-nome represented Cauchy completion and its actual
  pairing, including sharp Cauchy--Schwarz and a norm-one unit.
  `CompletedTime` descends actual advance to a positive contractive discrete
  semigroup, fixes that unit and preserves its orthogonal sector. Original
  loop moments and the dyadic absolute loss bound are SAME-operator matrix
  coefficients. This is NOT the face-span completion or the older small-nome
  Wilson completion. A strict gap on this carrier, full metric/Hilbert/QFT
  assembly and scaling/continuum joins remain open. The next strict-gap
  route must prove the centered lag envelope for arbitrary Wilson expressions;
  a face-span embedding alone would bound only its image. Previous sharp
  complex pairing results are retained. Full J02 and all goal markers stay open.
- Goal-node status changes: **NONE**.
- Displayed wording/layout/symbol changes: **NONE**. The chart block is
  unchanged from snapshots 1--9; this snapshot records only new proof evidence.

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
| 1 / 7 | 2026-09-24 | Computed positive floor comparing the SAME original channel norm with the ORIGINAL partition, and its direct original-energy consumer, independent of width/depth/late cutoff at fixed nome. Partial A03 evidence only; SAME centered-variance/scaling comparisons open. No chart-block or goal-node status change. |
| 1 / 8 | 2026-09-24 | The computed normalized coefficient is at least 32; this limits that certificate, not actual energy. ORIGINAL transfer positivity sharpens E<=norm and the existing centered approximation retains the same epsilon in energy. Partial A03 evidence only. No chart-block or goal-node status change. |
| 1 / 9 | 2026-09-24 | Literal dyadic Wilson squares, fixed-width all-nome reflected form, exact two-time moment pin and SAME-form cubic-cost loss bound. Partial A03/J02 evidence only; no completion substitution or scaling-survival conclusion. No chart-block or goal-node status change. |
| 1 / 10 | 2026-09-24 | Literal all-nome represented completion and pairing, actual positive contractive time semigroup, fixed unit, invariant orthogonal sector and SAME-operator loop moments/loss. Partial J02 evidence only; strict same-carrier gap, centered scaling survival and full Hilbert/QFT remain open. No chart-block or goal-node status change. |
