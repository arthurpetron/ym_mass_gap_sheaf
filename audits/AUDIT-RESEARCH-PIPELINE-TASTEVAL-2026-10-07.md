# Research-pipeline review and scoped adaptation (2026-10-07)

Whole-project goal unchanged and OPEN: construct nontrivial continuum
Yang--Mills on R^4 for every compact simple group, with SAME-theory QFT axioms
and a strictly positive physical Hamiltonian mass gap, constructively in Lean.
This document changes execution instructions, not a mathematical target,
canonical frontier field, or proof status.

## Source and what it establishes

Reviewed [TasteVal, arXiv:2610.06824v2](https://arxiv.org/html/2610.06824v2),
especially sections 2.1, 3.3--3.4 and appendices D--G. Its experimental setup
separates a Researcher choosing experiments from a Coder implementing them;
monitors inspect requests/reports, artifacts support offline audit, and planning
continues during serial experiments. Section 3.3 observes advance predictions
and cancellation criteria in the higher-inference scaffold. Section 3.4 does
NOT establish superiority of role separation: its split/end-to-end comparison
is statistically indistinguishable. These are empirical AI-R&D results, not
Yang--Mills mathematics or evidence that this adaptation will accelerate a proof.

## Local adaptation: a hypothesis-to-decision loop

This is our proposed use, not a conclusion of the paper. Existing goal rules
1--9 already require typed consumers, early obstruction tests, safe verification
and bidirectional parallelism. New rule 10 makes the next decision explicit:

1. Select one missing mathematical estimate/obstruction, stating its exact
   action, carrier, observable, normalization, time and downstream consumer.
2. Record a predicted result and a cheap decisive test before costly execution.
   Predictions are conjectures; numerical agreement never closes a theorem.
3. Give an implementer a bounded input/output contract. Preserve missing
   hypotheses as missing; implementation may not quietly redesign the problem.
4. Inspect source and independently review consequential joins, then run the
   narrow constructive kernel check with the existing resource limits.
5. Record result, scope and residue, then continue, revise or prune the branch.
   Use existing dated audits rather than creating a new orchestration system.

Not adopted: hidden proof source, validation-score optimization, forced spending
of compute budgets, token-generation quotas, extra monitor/liaison agents for
every task, or model-performance claims as evidence of proximity to Clay.
Mathematical review must see the implementation, and Lean's kernel/axiom gate
is the authority for formal correctness. A source-correct finite theorem can
still be inadequate for the physical target; that is separately reviewed.

## Recent-commit review and the present decision

The source/history review for October 5--7 through `8c6e113a` is
`AUDIT-RECENT-COMMITS-AND-CENTERED-SIGNED-PRODUCER-2026-10-07.md`.
Rechecked the live plan and subsequent `c71f9eb4`, `ba69eaf8`, `cbd93ff3`:
signed centering, retained mean-derivative correction, and original nonunit
innovation/covariance are finite checked inputs. They do not supply AF window
survival or a changing-action all-vector completed comparison. The old opposite
RG rate direction, heat-only substitution and full fringe coercivity must not
re-enter the route. No fresh whole-tree verification is claimed.

Current experiment: replace the reconstruction covariance's global source cap
by the actual multiplier-weighted source second moment, and test a residual
completion of the finite prediction against the constant observable. Predicted
identities/estimates were obtained before their focused checks. The generic
prediction file was already checked when the paper was reviewed; this is not
claimed as retrospective preregistration of that check.

The decisive tests are constants, zero source, k=0, t=0, and the exact norm in
the consumer. The original ratio fails exact constant preservation; its residual
completion passes. A conditional-noise comparison still needs its actual B^2
leakage payment; it cannot erase that term because the vacuum noise is zero.
The finite marginal square is not the completed OS norm. Independent read-only
review verified these boundaries. Verification evidence and exact declarations
are recorded in the companion finite-proof audit when checks pass.

Next decision: use these finite estimates only with a proved SAME OS/scaling
join or a useful centered surviving-form payment. If that join is unavailable,
do not proliferate conditional gap wrappers around them; return to estimating
the combined actual direct score and signed remainder. AF survival, useful
ordinary delta budget, physical calibration, continuum QFT and every group
remain OPEN. The broad canonical chart has not changed and is not reprinted.

## User follow-up: group-indexed carriers, not split-real substitution

Retained the useful scope distinction: the Clay quantifier is over compact
simple gauge groups, including their global forms, not over split-real surface
representation components. Prospective carrier construction/completion is
objectwise in that ACTUAL gauge datum. No continuity in a space of group labels
is required, and a common numerical gap across all groups is not introduced
as an unnecessary prerequisite. Any claimed comparison must be an actual
action/form/observable/time map, not just a principal embedding.

Not adopted: completion is possible only for split-real fibers; a surface
flat-connection moduli space replaces the full four-dimensional interacting
configuration space; a projective or geometric boundary is automatically a
Cauchy completion. Our existing normed compact-gauge proof carriers admit
constructive completion. The corrected completion discussion and actual
extension APIs are in `AUDIT-ORIGINAL-CAP-FREE-PREDICTION-2026-10-07.md`.
No Outer-Space/Hitchin framework or new scorecard is added.

Independent read-only source review found:

- `lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:318`,
  `CompactSimpleGlobalFormCode`, stores Cartan and central subgroup data,
  not compact/topological realization. `:381`, `su2GlobalFormCode`, and
  `:387`, `so3GlobalFormCode`, distinguish the global forms.
- `lean/YMGap/RepTheory/ConstructiveGroup.lean:200`,
  `CentralQuotientPresentation`, provides algebraic quotient/lift/kernel data.
  `lean/YMGap/RepTheory/RationalQuaternionSignQuotient.lean:128`,
  `UnitNorm.signLocatedQuotientPresentation`; `:134`, `signCoset_iff`;
  `:165`, `descendSignRepresentation`, are actual algebraic inputs, not
  compact SO(3) or continuum Yang--Mills.
- `lean/YMGap/Rubric/ClayResolutionRoot.lean:37`, `PinnedSimpleLieType`,
  and `:45`, `pinnedSimpleLieType`, pin classification/RepData only.
  `lean/YMGap/MassGap/AllSimpleTypes.lean:159`, `repDataOf`, and `:183`,
  `admissible_of_cartanType`, provide scalar-table data, not realized groups.
- `lean/YMGap/MassGap/SimpleGroup.lean:627`, `GroupBoundGap`, and `:635`,
  `GroupBoundGap.row_eq_su2`, expose a legacy bound restricted to the SU(2)
  row. This is not an every-group proof.
- `lean/YMGap/Continuum/CanonicalOSRoot.lean:84`,
  `ReferenceWeightStageFamily`; `:121`, `CanonicalSchwingerLimit`;
  `:268`, `PositiveTimeOSRoot`, retain genuine action/limit/reflected-root
  requirements. `lean/YMGap/Continuum/ContinuumSelectedExactMassDecayTarget.lean:32`,
  its unsupplied `corrected`/`scaling` fields, and
  `lean/YMGap/Continuum/ContinuumSelectedTheoryPins.lean:155`, its unsupplied
  `rotations`, `gauge`, `uv`, `nonGaussian` fields, remain open; their Cartan
  labels are not full global-form/Haar realization.

There is no final source bundle already constructing the continuum theory for
EVERY realized compact group/global form. That remains an explicit external
Clay requirement, not something closed by the available classification tables
or selected-theory interfaces. This planning/source review closes no proof node.

The further compact-character-variety/Sobolev/Tannakian note is incorporated
only as a scope guard. Classical compactness of flat moduli does not establish
the quantum measure, its reflected Hilbert space or its spectral gap. Compact
groups do not prevent metric completion of these state/observable carriers.
Completing classical connections in a Sobolev norm is not itself quantization
or construction of the physical Hamiltonian. The actual conditional
`lean/YMGap/Continuum/CanonicalOSRoot.lean:513`,
`PositiveTimeOSRoot.physicalHilbert`, is built from the SAME reflected form;
`:518`, `physicalVacuum`, lives in that Hilbert space, not in a flat-moduli
quotient. Their continuum Yang--Mills input is still unsupplied.
[Clay's problem overview](https://www.claymath.org/millennium/yang-mills-the-maths-gap/)
explicitly concerns quantum Yang--Mills existence and its mass gap. No
Sobolev gauge-action regularity claim, Tannaka reconstruction implementation,
or new functor across groups is inferred from the user's note. Preserve all
interacting curvature configurations, compact Haar/action data, SAME-theory
time/generator identification, nontriviality and physical scaling.

## Bounded finite Gauss/Ward input (2026-10-08 UTC, selected)

Main retention screen: the actual `localResponseFloor_le_window` gives
rho=a*(l/u)^2/[4*(1+5*a)], a=w^12, hence cannot improve the bare
reference even before endpoint losses. Character-product positivity does
not order the full centered commutator against the interacting source.
No useful original three-moment credit/overlap producer was found by the
bounded read-only review; stop that proposed positivity shortcut.

Independent backward QFT input selected: prove the ACTUAL all-link vertex
Gauss generator annihilates `fullHeatProduct` at every finite cutoff and
odd extent; then prove H[W*G(p)]=0 for every supported signed insertion p.
Inputs are `VertexGaussClosedCharacter.closedCharacter_gauss_zero`, its
raw Leibniz rules, `FixedSpatialWilsonPlaquette.character_plaquette`, and
arbitrary-block Haar angular integration by parts. Every original spatial
and temporal plaquette heat factor remains. No positivity, nome range,
normalizer inverse, gauge fixing or static restriction is needed.

Consumer: the finite gauge-invariance input for SAME-theory QFT structure,
currently with no implemented all-action Gauss/Ward declaration. This does
NOT produce the horizontal signed cost estimate, continuum gauge symmetry,
or fixed-slice transfer Gauss preservation. The latter still needs the
literal fixed-slice action law plus a derivative/placement join (or a direct
four-edge proof); padded placement pins cannot simply be differentiated.

Predicted outcome: exact finite action invariance and signed Ward identity,
not a norm estimate. Decisive tests: K=0, arbitrary rational nome, boundary
vertices, reversed temporal edges, arbitrary signed insertions. Differentiate
only raw coefficient equalities; pad only AFTER forming derivatives.
Root owns action proof/source review; Sol owns the bounded Ward consumer;
independent Sol final-source review. Budget: two new finite leaves and at
most three serialized focused checks, one 20-GiB worker and fresh dynamic
preflight each time. Stop/revise if an original factor or unproved gauge
premise is needed; do not expand to a general differential embedding library.
Canonical chart and all Clay claims remain unchanged.

Verification-budget revision: action check 1 failed missing namespace opens;
action check 2 PASS. Ward check 1 failed local notation quotation syntax and
one support namespace, not a mathematical premise. Repair those explicitly
and allow ONE final Ward check (four total attempts). No limits are raised;
failed elaboration output is not axiom/proof evidence.

Observed outcome: PROGRESS on the finite QFT gauge-law input. The actual
action generator vanishes at common-padded coefficient strength. Raw Haar
IBP plus raw Leibniz yields H[W*G(p)]=0 for arbitrary supported signed p.
Every finite cutoff, arbitrary rational nome and all original boundary,
spatial and temporal factors remain. No horizontal-energy estimate or
continuum gauge domain follows; the main useful retention margin stays OPEN.

Exact source pins:

- `lean/YMGap/Continuum/BF4ExactSlabVertexGaussHeatAction.lean:87`,
  `vertexGauss_congr`; `:132`, `vertexGauss_supported`; `:177`,
  `faceHeatPolynomial_gauss_zero`; `:203`, `fullHeatProduct_gauss_zero`.
- `lean/YMGap/Continuum/BF4ExactSlabVertexGaussWardIdentity.lean:123`,
  `vertexGauss_haar_zero`; `:129`, `original_action_ward_zero`.

Final source SHA-256 (root full review and independent complete final-source
review PASS at these hashes):

- Action: `45cfd7c0dffe38df8bb94e5859b920b12ae9dc925804105100fe2847d7520603`.
- Ward: `f798cbd67d2ee26e6bdeb849e2640d15ff44b33b028de50b7e502ceddd7c2d53`.

Accepted focused logs and SHA-256:

- `/private/tmp/ym-oct8-vertex-gauss-action2.log`:
  `198e78d8459956d2447539e164c0f7ab06036f99ac6a726f633e15bf59bedb03`.
- `/private/tmp/ym-oct8-vertex-gauss-ward2.log`:
  `55d1c6722406ffe53b592103e18603067c487f972b416111a2c413d84881e5b3`.

Six public gates exactly {propext,Quot.sound}; no accepted warnings or
sorryAx. Four attempts as revised above, all monitored/serialized with
one 20-GiB worker, 12-GiB reserve, fresh capacity checks and zero swap.
Root imports registered only; no whole-root/tree build/audit/guard/metric.

Next mathematical decision: return to actual joint signed cost versus
surviving variance (or useful raw credit/overlap) on a justified changing
family. Finite vertical cancellation cannot pay individual angular squares.
For an independent gauge-law continuation, prove the actual fixed-slice
four-edge action law before using product-heat angular commutation; do not
assume a differential embedding or continuum domain from the above result.
