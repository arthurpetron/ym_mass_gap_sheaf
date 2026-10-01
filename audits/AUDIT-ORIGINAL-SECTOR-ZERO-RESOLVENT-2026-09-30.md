# Original vacuum complement zero shift inverse

Date: 2026-09-30. The existing fixed-nome, fixed-width derivative now has
an actual bounded inverse on its original witnessed vacuum complement.
The construction takes positive-shift resolvents to zero with an explicit
modulus; both inverse identities are checked. This is supporting spectral
progress, not physical OS identification, spacing control or a Clay closure.

## The original objects and quantitative input

Let H denote the existing presented sector derivative, whose domain point
(u,v) satisfies A u=T(1)v. This notation does not assert A=H, does not
identify A with the separately constructed regularized logarithm, and does
not extend H to every ambient vector. The sector and domain are
`State`, `lean/YMGap/Continuum/BF4WilsonAllNomeTimeSector.lean:43`, and
`DomainPoint`, `lean/YMGap/Continuum/BF4WilsonAllNomeSectorDerivative.lean:68`.
Both coordinates retain original time-range witnesses.

Write delta=coreMargin(w,width)=(1-twoStepRate(w,width))/2>0.
Its defining declaration is `coreMargin`,
`lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:52`.
For the existing R_lambda=(lambda I+H)^(-1), every rational lambda>0,
the new chain proves on the original vacuum complement:

    ||R_lambda x||^2 <= (lambda+delta)^(-2) ||x||^2,
    ||R_lambda x||^2 <= delta^(-2) ||x||^2,
    R_lambda x-R_mu x = (mu-lambda) R_lambda(R_mu x),
    ||R_lambda x-R_mu x||^2 <= (mu-lambda)^2 delta^(-4) ||x||^2.

The uniformity is in the positive shifts lambda and mu ONLY. Nome and
width remain explicit in delta; no lattice-spacing parameter is introduced.
The norm estimate uses square completion, not division by an unknown vector
norm. There is no finite-dimensional spectral decomposition or choice.

| Declaration | Source | Content |
| --- | --- | --- |
| `state_orthogonal` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorResolventGap.lean:73` | Resolvents preserve the original vacuum complement. |
| `norm_bound`, `uniform_norm_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorResolventGap.lean:200`, `:215` | Sharp positive-shift bound and shift-independent cap. |
| `resolvent_identity` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorResolventIdentity.lean:74` | Exact identity for the already constructed resolvents. |
| `parameter_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorResolventContinuity.lean:42` | Quantitative parameter continuity with delta dependence retained. |
| `input_injective` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorZeroInjective.lean:38` | Equal outputs determine centered domain inputs at shift zero. |

## Constructed limit and inverse

The explicit schedule is lambda_n=2^(-(n+1)), not a selected subsequence.
`normCap` uses the input's supplied original representative; `modulus`
uses its rational norm ceiling and delta^(-4). The existing represented
sector completion then returns `zeroShift`, its range witness, and
`zeroShiftRate`. The completion's e/16 diagonal loss is retained.

These are respectively `parameter`, `normCap`, `modulus`, `zeroShift`, and
`zeroShiftRate` in
`lean/YMGap/Continuum/BF4WilsonAllNomeSectorZeroResolventLimit.lean:54`,
`:95`, `:106`, `:196`, and `:199`. Its `zeroShift_bound`,
`zeroShift_orthogonal`, and `zeroShift_norm_bound`, lines 202, 211 and 221,
prove convergence, vacuum orthogonality, and the cap delta^(-2) in squared
norm for the actual limit.

The positive-shift equation is A(R_lambda x)=T(1)(x-lambda R_lambda x).
The uniform norm cap makes lambda_n R_lambda_n x tend to zero; continuity
of the existing bounded A and contraction of T(1) pass this equation to
A(zeroShift x)=T(1)x. `zeroShift_equation` and `domainPoint` in
`lean/YMGap/Continuum/BF4WilsonAllNomeSectorZeroResolventEquation.lean:179`
and `:201` supply the actual domain point with output EXACTLY x.

`inverse_right` and `inverse_left` in
`lean/YMGap/Continuum/BF4WilsonAllNomeSectorZeroResolvent.lean:49` and `:54`
give H(H^(-1)x)=x and H^(-1)(H u)=u, with the latter restricted to centered
original domain inputs. `inverse_congr`, `inverse_symmetric`, and
`inverse_nonnegative`, lines 63, 71 and 80, prove independence of witness
presentation, symmetry and nonnegativity. `inverseCertificate`, line 88,
returns the actual domain point and its uniqueness on this complement.

The ambient time kernel has not been removed. No negative-shift resolvent,
full spectral exclusion interval, physical OS equivalence or calibrated
continuum mass follows as a newly checked declaration here.

## Review of the primary analytic frontier

Parallel source reviews did not find a useful scaling-relative energy UPPER
bound. The following existing facts constrain the next search; they were
read, not newly proved or recompiled in this milestone.

- `padded_endpoint_energy_le_originalPartition`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointEnergyPartitionBound.lean:179`,
  gives 2*rho*E <= kappa*Z. `normalizedCoefficient_ge_thirtyTwo`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialEndpointEnergyCoefficientFence.lean:213`,
  proves kappa<=2*rho*c implies c>=32. This is a limitation of that
  certificate, NOT an energy lower bound or a Yang--Mills counterexample.
- `frame_energy_le_originalVariance`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRelativeWardBound.lean:74`,
  compares angular energy to the same interacting variance with factor
  `angularVarianceFactor`, line 57, equal to
  6*(1+(6*relativeCap(w,4096)+2*relativeCap(w,32))^2).
  It does not bound the complete temporal signed correction by a
  scaling-small multiple of that variance.
- The exact full-weight test already exists: `clearedDefect` and
  `clearedDefect_pairing`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:62`
  and `:96`. On the diagonal it is Z*E-c*Z^2*Var. The checked
  `terminal_existing_fraction_nonnegative`, line 187, has the LOWER
  coercivity direction at the existing width-dependent fraction. Survival
  needs a useful UPPER relative estimate; a new name for the same defect
  or a conditional wrapper would not provide it.

The checked signed-family Ward/Taylor identity remains the analytic entry
point, as recorded in
`audits/AUDIT-SIGNED-FAMILY-ENERGY-VARIANCE-2026-09-30.md`. Preserve the
combined signed correction, original partition, all terminal factors and
cross terms. A useful bound relative to the SAME variance and a justified
physical scaling trajectory are still missing. This remains the primary
analytic priority; the new inverse does not supply either input.

## Verification boundary

Seven final focused checks exited 0. All 22 printed gates report exactly
{propext, Quot.sound}. No new sorry, axiom, classical shortcut, native_decide,
frontier weakening or surrogate substitution. Main serialized every check
through the monitored launcher: one worker, 20 GiB cap, 12 GiB OS reserve,
live memory telemetry and 300-second status setting. Preflight found no
competing compiler/test/runner and zero swap. No safety limit changed.

Sol agents developed independent parts and reviewed source/scope without
running compilers. Final read-only review found no carrier, domain,
uniformity or kernel-deletion issue. No full-tree/root build, broad audit or
guard was run. Root imports were registered after targeted checks; the root
was not recompiled. Canonical chart and frontier fields are unchanged.

| Final log in `/tmp/` | SHA-256 |
| --- | --- |
| `ym-sector-resolvent-identity-20260930.log` | `7ea62e55c4d14af3790dbabd6d3c91097ebf1c3632d93df80e92e5404b0435f4` |
| `ym-sector-resolvent-gap-20260930.log` | `eab4719938a9009ad9d54b2d73d0ddff58b1bd8649616ac5b93d0f586817e15d` |
| `ym-sector-resolvent-continuity-20260930.log` | `54ec0fed3c2cfd675087d561adf4dfc8c6758821eb66a6afbcad11da52911c3d` |
| `ym-sector-zero-injective-20260930.log` | `403ce0cd3509aaec3b623ffea9f67cc870d58790a466b192fdba8ddc53dbee3e` |
| `ym-sector-zero-resolvent-limit-20260930.log` | `9624e230f4230ca2167df561af370e1e82575ef1107dec6c452d7d0a03bcb98d` |
| `ym-sector-zero-resolvent-equation-20260930.log` | `5248a759671f809fd9566130ba47bd5218f5fcae3f9c5615c629624e93eb3fab` |
| `ym-sector-zero-resolvent-20260930.log` | `f42c9982d831236c17ac364ad7c2589f0b70f8b6d70f01c332db10c0589c8273` |
