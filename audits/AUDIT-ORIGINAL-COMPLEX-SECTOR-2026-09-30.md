# Original complex continuity sector and intrinsic derivative adjoint

Date: 2026-09-30 UTC. Classification: PROGRESS. Whole-project Clay target OPEN.

## Actual construction and consumer

The original real range sector and its densely defined real derivative were
already constructed. The independent reconstruction consumer needed their
compatibility with the EXISTING complex Wilson carrier, not another abstract
Hilbert space. Two original range witnesses now supply that compatibility.
The original action, nome, width, reflected pairing and time unit are unchanged.

The new sector is presented/setoid-valued: its records retain witnesses;
equality compares underlying original vectors. It is not an identification
with the physical continuum OS space. No choice of a representative or of a
Cauchy modulus from a quotient is made.

## Checked statements

| Declaration | Source | Exact content |
| --- | --- | --- |
| `State`, `val` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexTimeSector.lean:49` | Two witnessed real sector states map into the existing complex carrier. |
| `val_smul` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexTimeSector.lean:88` | Scalar action is the existing complex scalar action, with both supplied real moduli. |
| `inner_posdef` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexTimeSector.lean:105` | Zero norm means zero underlying vector, not equality of witness records. |
| `distance_norm_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexTimeSector.lean:122` | Squared convergence distance is exactly the original complex norm of the difference. |
| `limitCertificate`, `limit_unique` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexTimeSector.lean:208`, `:197` | Constructed limits preserve both witnesses; the combined rate takes the maximum of component rates at e/2. Uniqueness is at original values. |
| `action`, `action_sum` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexTimeSector.lean:215`, `:220` | Actual positive-time images carry both range witnesses and obey composition. |
| `action_time_congr`, `action_original` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexTimeSector.lean:226`, `:233` | Independence of represented time; positive integers recover the existing complex transfer. |
| `continuityCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexTimeSector.lean:290` | Explicit positive zero-time continuity radius, using the minimum of component radii at e/2. |
| `output_congr` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexSectorDerivative.lean:55` | Domain output is single-valued under original complex input equality. |
| `smul_input`, `smul_output` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexSectorDerivative.lean:96`, `:102` | Actual graph complex-scalar closure, with exact original input/output pins. |
| `equation_iff_adjoint`, `ofAdjoint` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexSectorDerivative.lean:169`, `:182` | Intrinsic complex adjoint equals the paired original graph; the converse constructs a domain point. |
| `coreDensityCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexSectorDerivative.lean:196` | Computed domain approximants and a maximum-of-component-moduli density rate. |
| `domain_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexSectorDerivative.lean:234` | Original coreMargin on the original complex vacuum complement; nome/width dependence retained. |
| `closedLimit` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexSectorDerivative.lean:251` | Witnessed graph limits with exact component input/output limits. |
| `remainder_pin`, `realTaylorCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeComplexSectorDerivative.lean:281`, `:305` | Original complex remainder x-S(t)x-t*Hx has squared norm at most e*t^2 below an explicitly returned positive radius. |

The adjoint proof tests `(q,0)` and `(0,q)` and takes the REAL component of
the complex equality. These give both actual real adjoint tests. The checked
real graph reconstruction supplies both domain coordinates; graph symmetry
gives the converse, including the imaginary component. No spectrum, inverse
of the original transfer, or bounded whole-carrier generator is assumed.

## Analytic review boundary, not a new upper estimate

`productHeat_upperHessian_eq_neg_square`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularHessian.lean:144`,
retains the complete common source and identifies the integrated angular
Hessian with a negative same-kernel square. Its sign theorem at line 177 is
NOT a bound on the original finite temporal displacement. The existing
`sourceEnergy_le_angular_add_quadratic`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularTaylor.lean:121`,
still contains the source-dependent quadratic Taylor budget.
`productMap_full_defect_le_angular`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatSharpAngularDefect.lean:164`,
is an unweighted Haar product-map bound, not the missing normalized original
terminal-source energy/variance comparison.

The parallel unsandwiched-bulk-observable review found another one-sided
boundary: `plaquette_fringe_independent`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFringeIndependent.lean:37`,
and `spatialFringeResidual_scaled_transfer_zero`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeProjection.lean:174`,
control the explicit finite fringe residual. `original_transfer_haar_active`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveTransfer.lean:87`,
is an actual tested Haar factorization. None of those statements asserts
an exact characterization of the entire completed time kernel or constructs
the dense active range with moduli. Unsandwiched bulk multiplier invariance
is therefore NOT claimed here.

These source reviews do not prove a new obstruction to Yang--Mills, nor do
they turn the signed estimate into an impossible task. They identify why the
reviewed declarations do not yet supply it. The primary analytic target stays
the source-specific ORIGINAL relative upper energy estimate on a justified
scaling family, with the consumer already supplied by the previous milestone.

## Verification and remaining scope

Two final focused checks passed via the monitored launcher, serialized with
one worker, hard 20 GiB ceiling and 12 GiB OS reserve. Preflight found no
competing Lean/Lake/test/runner process. The launcher retained its live
memory-pressure and swap checks. All 55 printed gates report EXACTLY
`[propext, Quot.sound]`; no sorry, new axiom or classical input was introduced.
Sol drafted the adjoint/density core; the main agent integrated and verified
it and added the original-time derivative and gap joins. Luna reviewed the
sector and derivative scope. Root imports were added, but no full root,
full-tree build, audit, guard or progress run was performed.

Final logs and SHA-256:

- `/tmp/ym-wilson-complex-time-sector-20260930.log`:
  `472b1040fe3098aa51c54643b40d71d3d0ef2645b1f69a59f87dec030bdee989`
- `/tmp/ym-wilson-complex-sector-derivative-20260930.log`:
  `ce74d37689482b66cfdbb7f71b6b4930211388c93feaa382b64b5f3377092984`

Still OPEN: physical reflected OS/observable identification, constructive
resolvent/spectral and physical-time calibration, the signed scaling-relative
source estimate, survival in the continuum, every-state scaling decay, full
QFT axioms, every compact simple group, and the Clay theorem. No canonical
frontier field or ASCII chart state changed; the chart is not reprinted.
