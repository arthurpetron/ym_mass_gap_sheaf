# Exact original polynomial dual tests and parallel scalar acceleration algebra

## Forward: optimize the actual signed test, not a comparison model

Fix the original nome, retained cutoff and slab extent. For an original
supported polynomial seed p, the already constructed conditional-kernel
polynomial is `t_i(p)=J_i(D_i)*p-J_i(N_i(p))`. With the original full-action
form, let `A=B(f,t_i(p))` and `C=B(t_i(p),t_i(p)) >= 0`.

The new construction returns the rational coefficient `a=A/C` when
`C>0`, and zero otherwise, together with the original supported seed `a*p`.
The exact dual value is `A*A/C` in the positive branch and zero in the
null branch. In the latter branch the original form's Cauchy--Schwarz
theorem forces A to vanish. Rational order is decidable; no real zero
test, representative choice, new analytic input or erased witness is used.

Square completion proves that this value is maximal among ALL rational
scalar multiples of the supplied test. It is not a maximum over all
polynomial tests. The computed maximum is a lower bound on the ACTUAL
completed conditional residual energy of f.

| Declaration | Source | Checked content |
| --- | --- | --- |
| `polynomialResidual_smul` | `lean/YMGap/Continuum/BF4ExactSlabStarPolynomialResidualScaling.lean:91` | Scaling the seed scales the actual supported kernel polynomial coefficientwise. |
| `dualValue_smul` | `lean/YMGap/Continuum/BF4ExactSlabStarPolynomialResidualScaling.lean:120` | Exact dual quadratic `2*a*A-a*a*C`. |
| `RationalDualTestOptimization.value_identity` / `value_le_gain` | `lean/YMGap/Continuum/RationalDualTestOptimization.lean:40`, `:70` | Positive-cost value and maximality by square completion. |
| `pairValue_null` | `lean/YMGap/Continuum/BF4ExactSlabStarOptimizedPolynomialTest.lean:70` | Null original cost forces null signed pairing. |
| `optimizedCoefficient` / `optimizedSeed` | `lean/YMGap/Continuum/BF4ExactSlabStarOptimizedPolynomialTest.lean:76`, `:84` | Total computable rational and original polynomial witnesses. |
| `optimized_value_identity` / `optimizedGain_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabStarOptimizedPolynomialTest.lean:87`, `:101` | Exact branchwise value and nonnegative gain. |
| `scaled_value_le_optimizedGain` | `lean/YMGap/Continuum/BF4ExactSlabStarOptimizedPolynomialTest.lean:110` | Maximum over rational multiples of the one supplied test. |
| `optimizedGain_lower` | `lean/YMGap/Continuum/BF4ExactSlabStarOptimizedPolynomialTest.lean:134` | Gain bounded by the SAME original completed residual norm square. |

The regularized baseline `a=A/(1+C)` is also checked:
`RationalDualTestNormalization.value_identity`
(`lean/YMGap/Continuum/RationalDualTestNormalization.lean:38`) gives
`2*a*A-a*a*C=A*A/(1+C)+a*a`, and the physical
`guaranteedGain_lower`
(`lean/YMGap/Continuum/BF4ExactSlabStarNormalizedPolynomialTest.lean:89`)
consumes this on the same completion. Its additive 1 depends on the test
scale; it must not be silently used as a homogeneous coercivity estimate.
The exact optimizer supersedes that loss, and
`guaranteedGain_le_optimizedGain`
(`lean/YMGap/Continuum/BF4ExactSlabStarOptimizedPolynomialTest.lean:125`)
proves it dominates the regularized guaranteed gain.

No coarse normalizer floor or cap is substituted into A or C. The signed
pairing is formed in full before squaring. No group-uniform, volume-uniform,
cutoff-uniform or changing-spacing lower coercivity constant is constructed.
The next analytic work is to select and estimate actual test families whose
summed gains dominate the SAME globally centered original norm with useful
parameter dependence. The scalar maximization alone does not do this.

## Backward: scalar normalization and the reverse-sweep energy seam

`ChebyshevReciprocalPair.T_center`
(`lean/YMGap/Continuum/ChebyshevReciprocalPair.lean:74`) proves the exact
identity `T_n((r+s)/2)=(r^n+s^n)/2` for `r*s=1`.
`T_center_pos` (`:123`) proves positivity for positive r,s, and
`T_center_recip_le` (`:165`) proves the positive reciprocal bound
`1/T_n((r+s)/2) <= 2*s^n`. The statement does not assume `s<1`, so it is
not itself a strict decay theorem. The parameter calibration, rescaled
original-operator contraction and polynomial cone/covariance join are
still required. The existing constructive calibration data are recorded
separately in `NOTE-RATIONAL-ACCELERATION-CALIBRATION-2026-09-27.md`;
that note is a proof plan, not a checked calibration theorem.

`Family.sumOn_perm` / `sumOn_reverse` and `finalEnergy_perm` /
`finalEnergy_reverse` in
`lean/YMGap/Continuum/GNSProjectionSweepEnergyOrder.lean:30`, `:43`,
`:50`, `:55` prove permutation and reversal invariance of the residual
energy evaluated on ONE fixed completed state. They do NOT permit
reordering noncommuting sweep operators. Combined with the existing
arbitrary-schedule 625 upper estimate, this removes the ordering seam for
using one future centered lower-energy estimate with S and its adjoint.
That useful lower estimate is still unsupplied; S remains the conditional
update sweep, not an identified physical-time OS transfer.

## Verification and status boundary

All seven new Lean modules passed focused, serialized checks through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20`.
All 35 printed gates stayed within `{propext, Quot.sound}` (some smaller).
Initial elaboration errors were repaired before the final checks; none
of their failed gate output is counted as verification. The one live check
was manually revisited after about five minutes while independent source
work and Sol contributions continued; automatic safety telemetry stayed
active and reported 43.9 GiB available, 91% pressure-free.

Sol contributed the scalar optimization, scalar Chebyshev identity,
energy-order proof and initial scaling work, and independently reviewed the
actual optimizer's null branch, carrier and inequality direction. Main
completed/repaired the physical integration and performed every check.

No new hole, axiom, analytic hypothesis field, canonical frontier field,
chart marker or CI setting changed. The root import list was updated, but
no root/full-tree build or audit was run. The safe-build guidance kept all
checks focused, serialized and resource-capped. Useful uniform interacting
coercivity, physical scaling, nontrivial continuum survival, the SAME-theory
OS/Hamiltonian/QFT passage, every compact simple group and the Clay target
remain OPEN.
