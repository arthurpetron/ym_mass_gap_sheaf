# Original response-null direction and the remaining variance estimate

Date: 2026-09-17 UTC. Pre-change checkpoint: `eff659848751bb88b85cb8d58114d0359204c828`.
This is a checked limitation of a proposed estimate, not a new spatial
variance upper bound or a refutation of Yang--Mills mass gap.

## New mathematical result

Fix the original selected action A and inserted heat h. Let C_A denote
the original connected numerator and set u=C_A(chi_p,h), v=C_A(chi_q,h).
The explicit rational rule

    (a,b) = (1,0) if u == 0; otherwise (v,-u)

has a*a+b*b>0 and a*u+b*v=0, including both-zero input. Semantic equality
of the rational u is decidable. No inverse, square root or erased choice
is used in this coefficient construction: `pair`, `pair_dot_zero` and
`pair_square_positive`, `lean/YMGap/Continuum/RationalOrthogonalPair.lean:23`,
:42 and :56.

The original connected numerator is linear before taking any bound:
`connectedNumerator_linear_left`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedResponseLinear.lean:122`.
The computed polynomial F=a*chi_p+b*chi_q consequently obeys C_A(F,h)=0:
`coefficients`, `probe` and `probe_connected_zero`,
`lean/YMGap/Continuum/BF4ExactSlabResponseNullDirection.lean:50`, :57 and :72.

For distinct physical p,q, 0<w<1, K>=headCutoff(w), and a physical
duplicate-free selected action, H[A*F^2]>0. This uses the already checked
family coercivity and the SAME positive partition, not a surrogate law:
`twoFaceSpan_norm_positive`,
`lean/YMGap/Continuum/BF4ExactSlabTwoPlaquettePositiveNorm.lean:93`, and
`probe_norm_positive`,
`lean/YMGap/Continuum/BF4ExactSlabResponseNullDirection.lean:81`.

The polynomial is not a constant modulo coefficient equality:
`probe_not_constant`,
`lean/YMGap/Continuum/BF4ExactSlabResponseNullDirection.lean:95`.
The proof uses bare-Haar mean zero and positive square of the SAME polynomial,
`twoFaceSpan_haar_mean_zero`, `twoFaceSpan_haar_square_positive` and
`twoFaceSpan_not_constant`,
`lean/YMGap/Continuum/BF4ExactSlabTwoPlaquettePositiveNorm.lean:137`, :150,
:166. These are not claims of interacting centering or OS non-nullness.

The original response therefore becomes exactly

    response_A(h;F,F) = M_A(h)*third_A(F,F,h).

This is `probe_response_eq_third`,
`lean/YMGap/Continuum/BF4ExactSlabResponseNullDirection.lean:104`.
The negative square contributes ZERO on this nonconstant direction. For
every delta>0 it cannot dominate delta*(a*a+b*b):
`no_positive_square_fraction`, same module :115. Cite the physical norm
theorem alongside this algebraic statement when claiming nontriviality.

## Exact consequence for the plan

A per-insertion variance estimate cannot assume that its rank-one
subtraction controls every signed coefficient direction. It must handle
the third term on the computed directions above. A combined estimate
across several insertions remains possible; no such combination is
refuted here. Neither positivity nor a nonzero value of the remaining
third term has been proved. The probe depends on the finite action and
cutoff, so no fixed-observable limit follows from its construction.

The older `response_eq` and `response_ne_zero`,
`lean/YMGap/Continuum/BF4ExactSlabPairwiseResponseObstruction.lean:273` and
:278, concern a special empty-action, single-plaquette chi_2/chi_3 example.
The new result ranges over arbitrary positive original selected actions
and two distinct fundamental faces, but makes no claim that its own
third term is nonzero. These are different statements.

The target upper comparison remains, for f=sum(c_p*chi_p), g=g_n,
Z=oddMass=m(g*Tg), A_2=m(g*Tg*f^2), B_1=m(g*Tg*f),

    Z*A_2-B_1^2 <= C(w)*Z^2*sum(c_p^2),

with width/depth/cofinal-cutoff control on a justified coupling domain or
scaling trajectory. Its same-marginal consumer is
`clearedDefect_diagonal_nonnegative_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175`,
together with `family_energy_floor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy.lean:174`.
An absolute summable covariance-row estimate is sufficient but stronger
than the required signed quadratic estimate.

## Other routes checked, without a new upper-bound producer

- Local erasure retains the conditional normalizer multiplying the exterior
  density: `full_partition_pin`, `full_insertion_pin`,
  `lean/YMGap/Continuum/BF4ExactSlabStarNormalizer.lean:75` and :86.
  `normalizer_form_bounds` at :101 controls its floor/cap, not the required
  distant covariance. `normalizer_local`,
  `lean/YMGap/Continuum/BF4ExactSlabStarConditionalLocality.lean:87`, is a
  support statement. The paper-level normalized variance identity from
  `response_identity`,
  `lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:90`, gives
  Var_new(F)-Var_old(F)=Cov(h,(F-mean_old(F))^2)/mean(h)
  -Cov(h,F)^2/mean(h)^2. Local floor/cap estimates alone give a multiplicative
  comparison, not the needed additive, spatially controlled coefficient bound.
- Vertex-star sign symmetry fixes physical spatial characters:
  `character_starSign`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialVertexStar.lean:313`.
  Thus its odd-sector cancellation does not apply to their even signed span.
- The existing actual spatial covariance producer retains small-nome
  guards: `finite_covariance_distance_bound`,
  `lean/YMGap/Continuum/BF4ExactSlabSelectedTwoProbeCovariance.lean:86`.
  Reflected Cauchy--Schwarz alone has no distance factor:
  `chartScalar_cauchySchwarz`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz.lean:148`.

**NOT FOUND:** the required beyond-small-nome original odd-marginal upper
estimate in those modules, `BF4ExactSlabOneFaceVarianceComparison.lean`,
`BF4ExactSlabFixedSpatialConditionalMessage.lean`,
`BF4ExactSlabStarLocalInfluence.lean`, `TruncatedBlockSpinContraction.lean`,
`BlockingStepFrontier.lean`, and the covariance modules listed in
`audits/AUDIT-PLAQUETTE-FAMILY-TEMPORAL-ENERGY.md` (all Lean modules under
`lean/YMGap/Continuum/`).

## Targeted literature cache

Reviewed 2026-09-17 21:20 UTC; this was not a routine math-ph listing scan.
Faria da Veiga--O'Carroll, arXiv:2205.07376v2, Theorem 4, equations
(83)--(84), bounds a fixed-r generating function with single-source
arguments r*J_j. Section VI.5 uses Holder's inequality; its resulting
quadratic source budget retains r. Substituting J_j=t*c_j therefore does
not give the requested family-size-independent estimate (our inference).
Equation (82) uses a scaled imaginary trace, not our fundamental character;
the model uses the Wilson exponential action. Remark 16 discusses action
fields but supplies no stronger family-uniform estimate. Keep this paper as
reflection-method background, not a discharge of the present bound.
[Primary paper](https://arxiv.org/html/2205.07376).

## Verification and unchanged boundaries

Four focused serialized checks through `scripts/safe_lean_build.py`, each
with `--jobs 1 --check-worker-limit-gib 20` and an explicit `.olean` output,
passed. All 23 printed gates lie within {propext, Quot.sound}; the coefficient
pair function is axiom-free. Final logs contain no errors, warnings or sorryAx.
Independent source review checked zero-input nonvacuity, action/partition,
distinct-face guards and the exact scope of the excluded inequality.

Final logs and SHA-256:

- `/tmp/ym-rational-orthogonal-pair-20260917.log`:
  `1136fd9d79c08d9dd718b0c4ce40ac4f0cf6915be35d5584f6998450a758f23d`
- `/tmp/ym-connected-response-linear-20260917.log`:
  `5f8977619d29912a6152c0e81336af5e716f38546c19864d4b06c374a332e59b`
- `/tmp/ym-two-plaquette-positive-norm-20260917.log`:
  `16ec59207f195819601504fecf278d29f87f3defef76bcc0482952f69a8b0e60`
- `/tmp/ym-response-null-direction-20260917.log`:
  `394b93851620bfe0ddcf3b821547e3ed0c5ef8c1c8784e8ebb9479ccb2525da2`

No sorry introduced/discharged, analytic premise or canonical field changed.
Four root imports added. No resource/CI changes or full-root
build/audit/guard/progress run. The existing small-nome completed gap and
excitation remain proved. Spatial upper control beyond those guards,
physical scaling, same-theory continuum/QFT and all compact simple groups
remain open.
