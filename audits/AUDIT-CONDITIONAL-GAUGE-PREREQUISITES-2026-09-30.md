# Conditional gauge identities with the original weights retained

Date: 2026-09-30 UTC. Four focused checks passed. These are finite
change-of-variable prerequisites, not a strict covariance estimate.

## Proved identities

Write P_i for the existing in-place Haar integration of block i and T for
the existing polynomial quaternion translation. Carrier equality means
equality after every polynomial Haar insertion; it is not coefficientwise
or pointwise equality. The following declarations introduce no new
analytic hypothesis bundle.

| Declaration | Source | Exact conclusion |
| --- | --- | --- |
| `partialHaarHead_translated` | `lean/YMGap/Continuum/SU2QuaternionConditionalHaarTranslation.lean:91` | Integrating the translated head preserves its conditional moment, modulo the tail Haar carrier, at every polynomial degree and for either multiplication order. |
| `project_head_translated` | `lean/YMGap/Continuum/SU2QuaternionConditionalHaarTranslation.lean:129` | P_0(Tp) and P_0(p) are Haar-carrier equivalent; arbitrary head-dependent insertions are projected, not dropped. |
| `weighted_moment_translated`, `weighted_square_translated`, `determinant_translated` | `lean/YMGap/Continuum/SU2QuaternionConditionalHaarTranslation.lean:139`, `:149`, `:159` | The weight and test transform TOGETHER; the existing conditional moments and division-free variance determinant are preserved. |
| `project_translatedHeadPolynomial` | `lean/YMGap/Continuum/SU2QuaternionTranslationSpectatorProjection.lean:226` | P_k T = T P_k coefficientwise for k >= 2; the translated head uses blocks 0 and 1. |
| `project_selectedLeft`, `project_selectedRight` | `lean/YMGap/Continuum/SU2QuaternionSelectedConditionalTranslation.lean:101`, `:109` | Cancellation after integrating the ORIGINAL selected block for the existing selected left/right shears, with supported input and arbitrary Haar insertions. |
| `project_spectator_selectedLeft`, `project_spectator_selectedRight` | `lean/YMGap/Continuum/SU2QuaternionSelectedConditionalTranslation.lean:164`, `:175` | Coefficientwise commutation on an in-range original block distinct from both the selected block and its multiplier. |
| `fullWeight_gauge_pairing` | `lean/YMGap/Continuum/BF4ExactSlabGaugeWeightedPairing.lean:56` | The actual common vertex-gauge ledger transforms both tests while retaining the UNTRANSFORMED original full heat product in the augmented Haar pairing. |

The last identity uses the existing full-action invariance
`heatProduct_invariant` at
`lean/YMGap/Continuum/BF4ExactSlabVertexGaugeAction.lean:234` and
`slabGauge_haar` at
`lean/YMGap/Continuum/BF4ExactSlabAuxiliaryVertexGauge.lean:106`.
It retains all physical face factors and has three auxiliary quaternion
blocks on its left side. It constructs no endomorphism of the original
unaugmented Hilbert completion. No positivity or coupling guard is needed
for this algebraic pairing identity; that is not a coupling-uniform gap.

## Consumer and remaining work

The intended consumer is original block-projection equivariance, needed
before restricting the signed estimate and its auxiliary recurrence to
gauge-invariant states. `GNSChebyshevEnergy.state_mem` at
`lean/YMGap/Continuum/GNSChebyshevEnergy.lean:137` CONSUMES sector closure;
it does not establish it for these gauge transformations.

Remaining: fixedness of selected shears on already projected inputs,
inverse-orientation translations, carrier-compatible composition
of the actual finite vertex ledger and family integrations, the original
weighted conditional inverse, and passage to the same completed sector.
The selected cancellation above alone is not that complete join. The
spectator theorem deliberately excludes the multiplier block. Full-action
invariance alone does not fill any omitted conditional commutation step.

More importantly, gauge-sector preservation would still supply no useful
rho. The original-action signed variance-relative estimate on justified
scaling remains the analytic producer to construct. The existing consumer
is `residual_pair_lower_of_certificates` at
`lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceCertificate.lean:83`.
Collective signed estimates remain alternatives to its sufficient pairwise
route. These are ordinary full-action conditional projections, not the OS
transfer. Geometry, scaling, nontrivial survival, thermodynamic passage,
same-theory OS/QFT/physical Hamiltonian mass and every compact simple group
remain open. No canonical chart claim changes.

## Parallel certificate and literature review

Source review located the one-head positivity producer
`determinant_certificate` at
`lean/YMGap/Continuum/SU2QuaternionConditionalVarianceReplica.lean:180`.
The family result `mixed_identity` at
`lean/YMGap/Continuum/SU2QuaternionFamilyCovarianceReplica.lean:127`
is an identity; `familyProject_certificate` at
`lean/YMGap/Continuum/SU2QuaternionHaarFamilyCertificate.lean:33`
preserves a SUPPLIED certificate. None of these declarations supplies the
missing strict covariance-budget coefficient. A variance-positivity
baseline is not recorded as a new strict-estimate milestone.

A targeted primary-source review of Shen, Rongchan Zhu and Xiangchan Zhu,
[*A stochastic analysis approach to lattice Yang--Mills at strong
coupling*, arXiv:2204.12737v1](https://arxiv.org/pdf/2204.12737v1),
checked Assumption 1.1, Theorem 1.4, Corollary 1.6 and Section 4.1.
For SU(N) the stated regime is |beta| < 1/[16(d-1)]. The measure uses the
Wilson action and the dynamics is Langevin stochastic quantization, not
this project's heat-kernel conditional projection or OS transfer. Its
Poincare/log-Sobolev and correlation-decay results retain the strong-coupling
guard. They do not supply this route's weak-coupling scaling input. This
is a relevance check, not an independent verification or a Lean import of
the paper's proofs. No routine math-ph listing refresh was performed.

## Verification boundary

Four focused checks ran serially through `scripts/safe_lean_build.py`, each
with one worker and a 20 GiB ceiling. All 12 printed declaration gates
passed within `{propext, Quot.sound}`. Earlier elaboration errors were fixed
before counting gates; failed-run placeholder output is not evidence.
Luna independently reviewed the conditional and selected-coordinate scope;
Sol supplied and reviewed the spectator and full-action pairing arguments.
No new sorry, axiom, classical input or weakened frontier was introduced.

No root/tree build, full audit, guard, broad test suite or progress metric
was run. Root imports are added without claiming root integration has been
checked. No Rust computation or external positivity solver was used.
