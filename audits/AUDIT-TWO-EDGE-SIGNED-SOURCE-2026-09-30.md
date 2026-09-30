# Two-edge signed-source detection and mixed plaquette kinematics

Date: 2026-09-30 UTC. Whole-project Clay target OPEN.
Classification: PROGRESS on the proposed two-edge route, not a completed
signed variance estimate. Six focused checks passed 30 public axiom gates
within {propext, Quot.sound}. No canonical chart field changed.

## Change of mathematical viewpoint

The preceding checkpoint ruled out the local defect (I-T)v as a fixed
positive relative-survival witness on one explicit candidate schedule.
This increment investigates a signed family of original plaquette sources.
It does not add another survival interface for that rejected candidate.

Three formerly proposed ingredients are now proved, with their join still
explicitly open:

1. Two distinct physical boundary links isolate a plaquette coefficient
   in the original signed source, including after arbitrary centering.
2. The mixed angular square of the exposed fundamental plaquette is
   exactly 8+f^2, with arbitrary Haar insertions retained.
3. The original relative Ward argument bounds angular energy by signed
   prediction error with explicit coefficient M(C)=24+36*C^2, without
   the singleton kinematic hypothesis.

## Exact signed-source isolation

`BF4ExactSlabPlaquetteMixedDerivativeIsolation.linkDerivative`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteMixedDerivativeIsolation.lean:54`,
uses the existing physical-link-to-head transposition, differentiates,
and returns to the original coordinate frame. `mixedDerivative` at :138
composes two such derivatives. These are not a new measure or carrier.

For a duplicate-free face list qs, arbitrary rational signed coefficients
c, a selected p in qs, and distinct e1,e2 in the boundary of p, the result is

    D_e2 D_e1 (sum_q c_q f_q - m) = c_p D_e2 D_e1 f_p.

Equality is polynomial coefficient equivalence; m is any rational center.
The physical links must belong to the displayed original slab carrier.
All other faces vanish because two distinct boundary links determine a
plaquette, and differentiation preserves the original link-locality set.

Declarations: `mixedDerivative_other_face_zero` at :189,
`sourceSpan_mixedDerivative_isolates` at :249, and
`affineSource_mixedDerivative_isolates` at :297 in that same file.
No coefficient absolute values, unsigned replacement sum, or independence
of neighboring plaquettes is used.

## The short mixed-square proof

Write Gamma_0 for the six-direction head angular square and Delta_0 for
its Laplacian. For a head-linear polynomial h, the proved Casimir and
Leibniz identities give

    Delta_0(h^2) = 2 Gamma_0(h) - 6 h^2.

For the exposed four-link fundamental character f, put
g_ij=D_(block 1,ij)f. Differentiation outside the head preserves exact
head degree. Both Gamma_0(f)=4-f^2 and sum g_ij^2=4-f^2 are supplied;
the latter follows by cyclically re-expressing the same quaternion word,
not by commuting its factors. Applying Delta_0 to the latter equality gives

    2 sum Gamma_0(g_ij) - 6(4-f^2) = -8 + 8 f^2,
    sum Gamma_0(g_ij) = 8 + f^2.

This avoids a 36-square polynomial expansion. The identity holds on every
Haar carrier containing the four exposed blocks, in all orientations,
after multiplication by any polynomial insertion.

Source map:

- `QuaternionHaarMixedAngularDerivative.blockAngularDerivative_headDegree_of_ne`,
  `lean/YMGap/Continuum/QuaternionHaarMixedAngularDerivative.lean:71`.
- `QuaternionHaarMixedAngularSquare.linear_square_laplacian` and
  `mixed_square_of_linear_identities`,
  `lean/YMGap/Continuum/QuaternionHaarMixedAngularSquare.lean:37`, :62.
- `QuaternionHaarExposedMixedAngularSquare.exposed_block_one_square`,
  `exposed_mixed_angular_square`, and `exposed_mixed_weighted_floor`,
  `lean/YMGap/Continuum/QuaternionHaarExposedMixedAngularSquare.lean:59`,
  :91, :121.

The last theorem inserts any supplied nonnegative polynomial-weight
certificate W and proves H[W*S2(f)] >= 8*H[W]. There is no lower bound on W,
heat-minimum comparison, or division by an assumed partition.

## Original-weight energy versus prediction error

`QuaternionHaarRelativePredictionEnergy.angular_energy_le_prediction`,
`lean/YMGap/Continuum/QuaternionHaarRelativePredictionEnergy.lean:53`, proves

    H[W*Gamma(f)] <= (24+36*C^2) H[W*(f-q)^2]

for supported head-linear f, supported head-independent q, C>0, and the
existing six original-weight relative-derivative certificates. The
coefficient is defined by `energyPredictionFactor` in that file at :41.
No kinematic identity, global partition bound, or volume comparison is
assumed. The action dependence remains in the supplied relative score C;
this is not a beta-independent variance or transfer gap.

## Exact remaining join and next action

The physical isolation theorem uses the pulled-back `linkDerivative`;
the mixed-square theorem uses raw angular derivatives of the exposed
four-block word. Their two-edge transport to the SAME physical source is
not supplied by this increment. A one-edge transport theorem alone does
not close this join.

NEXT: prove that transport, preserve incident/nonincident signed pieces,
and apply the original-weight prediction estimate twice. The proposed
per-face inequality 8*Z*c_p^2 <= M^2*Z*Var_W(F) is still OPEN, not an
assumed Lean input. Even such a per-face result does not prove a
family-uniform bound: summing it costs the number of faces. A genuine
bounded-interference/dual-family estimate remains necessary.

No completed family is silently identified with the literal Wilson
completion. Controlled physical support, scaling survival, useful
every-state decay, physical calibration, the continuum/QFT construction,
and every compact simple group remain OPEN.

## Verification boundary

All six new modules were checked serially by `scripts/safe_lean_build.py`,
one worker, 20 GiB hard cap, 12 GiB OS reserve and live memory monitoring.
Final logs are `/tmp/ym-relative-prediction-energy-20260930.log`,
`/tmp/ym-mixed-angular-derivative-20260930.log`,
`/tmp/ym-angular-laplacian-linear-20260930.log`,
`/tmp/ym-mixed-angular-square-20260930.log`,
`/tmp/ym-exposed-mixed-angular-square-20260930.log`, and
`/tmp/ym-plaquette-mixed-isolation-20260930.log`.

No new sorry, custom axiom, classical input, analytic frontier assumption,
or weakened field. No old sorry discharged. No broad build/audit/guard,
CI change, Rust computation, or canonical ASCII-chart change. Luna and Sol
provided bounded proof tasks and scope review; the main agent alone ran
the checks and repaired compilation issues.
