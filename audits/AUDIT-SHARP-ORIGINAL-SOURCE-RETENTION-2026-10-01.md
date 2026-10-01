# Sharp norm retention from the original source energy

Date: 2026-10-01 UTC. PROGRESS after `c1e95a8`: a positive-square argument
improves the original energy-to-domain consumer from the fraction 1-2c to
(1-c)^2. It covers zero-norm sources without division and extends the positive
derivative-core ratio guard from c<1/2 to c<1. This does not prove the input
energy bound on a justified scaling family.

## Exact original pairing argument

All new declarations are in
`lean/YMGap/Continuum/BF4WilsonAllNomeSectorSharpEnergyTransfer.lean`.
Let B be the ORIGINAL ambient completed pairing, T its actual one-step time,
N=B(x,x), E=B(x,x-Tx), and r=1-c. `retention_square_identity` (:125) proves

    B(Tx-r*x,Tx-r*x) + 2*r*(c*N-E) = B(Tx,Tx)-r^2*N.

Both sides use the same original x and time operator. Bilinearity and real
symmetry expand the square; an opaque kernel-checked rational polynomial
identity supplies cancellation. For c<=1 and E<=c*N, each left term is
nonnegative. `relative_norm_retention` (:141) therefore proves

    retainedFraction(c)*N <= B(Tx,Tx), retainedFraction(c)=(1-c)^2.

The proof never inverts N, decides equality of a constructive real, or excludes
N=0. It needs no c>=0 guard for this implication. The rational fraction is
returned by `retainedFraction` (:54), and `retainedFraction_positive` (:56)
proves strict positivity for c<1 using the existing constructive rational
one-minus-square positivity theorem, not heat-kernel estimates for x.

## Actual derivative core and source floor

`energyRatio` (:59) constructs c/(1-c)^2 using ONLY the explicit positive
rational denominator; `energyRatio_nonnegative` (:62) requires c>=0.
`relative_derivative_bound` (:155) combines sharp retention with the EXISTING
`BF4WilsonAllNomeSectorSmoothingEnergy.derivative_core_upper` on the original
time-smoothed source. It proves, for 0<=c<1 and E<=c*N,

    B(Tx,derivativeAction(x)) <= energyRatio(c)*B(Tx,Tx).

`corePoint_relative_bound` (:166) applies this to the ACTUAL represented
`SectorDerivative.corePoint(X)`, not a supplied operator or arbitrary domain
point. `corePoint_norm_floor` (:175) transports an original source floor
F<=N to (1-c)^2*F<=B(Tx,Tx); `transferredFloor_positive` (:183) keeps a positive
rational floor positive when c<1. Its right side is the ambient norm of the
same core input. It is not substituted for a physical bond norm.

Existing source-replacement and vacuum-complement theorems in
`BF4WilsonAllNomeSectorSourceTransfer` remain unchanged; this module does not
re-prove them or assume a different transfer. Its new claim is the sharper
zero-safe retention and actual derivative-core ratio.

## Remaining producer and causal use

The missing input remains a useful original E<=c*N bound on a justified
coupling/spatial/spacing family, with original norm floors and physical-time
calibration. This module does not estimate completeCenteredError, assume its
sign, construct a scaling family or identify a logarithm of T. A small-looking
prefactor in the preceding energy identity is not a supplied c.

Independent review notes that the existing fixed-coupling signed-family
Rayleigh response supplies E<=(1-rho)*N, and its lag-two orbit already contains
the resulting rho^2 norm floor. No redundant family-floor theorem is claimed
as a new frontier closure. A derivative-ratio specialization additionally
needs c>=0, equivalently rho<=1; that scalar specialization is not exported
here. This generic sharp consumer can accept a future useful signed estimate
without the old c<1/2 threshold.

Primary complete signed scaling, spatial/spacing control, nontrivial continuum
survival, physical time and positive physical mass, full same-theory continuum
OS/QFT, Yang--Mills field/UV identification, every compact simple group and the
Clay target remain OPEN. No canonical frontier field or displayed chart claim
changes; no ASCII reprint.

## Focused verification and independent review

Session 73780 returned terminal exit zero and emitted the target olean. All TEN
gates passed: one empty, two {propext}, seven {propext,Quot.sound}. Independent
Sol mathematical/source review and Luna source/log/hash review passed. No new
sorry, axiom, Classical dependency, native_decide, noncomputable declaration,
analytic premise or weakened frontier was introduced.

The first draft's scalar expression mismatch was repaired by matching the
actual bilinear expansion, not changing the statement or raising limits. Its
failed log and recovery sorryAx are not accepted evidence. Main alone compiled
through the safe-build skill and monitored launcher with one 20 GiB worker,
unchanged 12 GiB reserve and dynamic telemetry. Preflight found no competing
compiler/test/runner, 84 percent pressure-free memory and zero swap. No broad
build/audit/guard, progress-metric script or CI change. Root imports are
registered only, not aggregate-checked. The documentation skill keeps this
conditional improvement distinct from supplying the missing scaling input.

Accepted log: `/tmp/ym-sharp-source-retention-second-20261001.log`.
SHA-256: `c56c509e027f166aea2a171b29b948542f6e78a493b5e5b65bec8a090cc25f4f`.
