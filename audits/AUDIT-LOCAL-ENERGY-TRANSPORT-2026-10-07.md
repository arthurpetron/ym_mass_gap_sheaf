# Decision: transport a local energy estimate through the original transfer

## Proposition and consumer (before verification)

Keep the literal finite transfer `T = K V`, its V-weighted pairing, and
`a = g_(s+1)`, `c = a*psi`. The existing actual terminal comparison constructs
`l*a <= T a <= U*a`, with `l > 0` and `U-l <= eta_s*l` in the certified
polynomial cone. Proposed finite theorem: if the INITIAL original edge energy
obeys `E(a,psi) <= d*ell[a*(T a)*psi^2]`, `0 <= d <= 1`, then for EVERY t,
`A = T^t a`, `b = T^t c` satisfy

```
clearedRayleighCost(A,b) <= (d+eta_s)*ell[A*(T A)]*ell[b^2].
```

The existing `BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.
blockConditionalRatio_energy_error_relative_tolerance` compares this literal
cost with the original energy of the finite reconstructed ratio and its
boundary drift. This would reduce the selected-source filtered-cost producer
to an UNFILTERED local energy/variance estimate, rather than an estimate of
high-degree derivatives of `G*b`. It does not construct that initial small
coefficient, a scaling modulus, independent AF or scaling-uniform source
survival, or an all-vector RG map.

Direct intended consumer: the reconstructed ratio energy itself, with
`n=s+1`, obeys

```
Z0*E(A,phi_k) <= (d+eta_s+epsilon+eta_(s+t))*Z1*ell[b^2]
```

at the existing relative reconstruction onset. The signed boundary drift is
paid by its actual all-degree certificate. This is a sufficient bypass, not
an equivalence: a small FILTERED cost need not imply a small initial d.

## Available inputs and predicted argument

- Actual `TransferPositive.transferStep_quadratic_nonnegative` and
  `TransferSymmetry.transferStep_weighted_symmetric` supply positive symmetric
  operator algebra, not a free-heat substitution.
- Actual `TransferOrder.transferStep_certificate` propagates BOTH fixed
  terminal-envelope endpoints under the original transfer.
- `TerminalComparison.terminalComparison_lower_positive` and
  `terminalComparison_relative_width` construct the envelope and its error.
- The exact `DirichletForm.energy` split gives
  `ell[c*(T c)] >= (1-d)*l*ell[c^2]` from the initial energy hypothesis.
- Positive ordinary and T-weighted squares of `T c-rho*c` propagate this fixed
  source Rayleigh floor, `rho=(1-d)*l`, without any source-norm inverse.
- Combining the propagated floor with the propagated vacuum envelope gives
  the claimed relative cost, with BOTH original partitions retained.

Prediction: this is a valid finite transport theorem, with no accumulation
in t. The initial estimate and eta may still be useless on a changing family.

Independent read-only review found the short source-floor persistence
identity, for `y=T c-rho*c`:

```
ell[(T c)*T(T c)]-rho*ell[(T c)^2]
  = ell[y*T y] + rho*ell[y^2]
      + rho^2*(ell[c*T c]-rho*ell[c^2]).
```

All three terms are certified nonnegative under the actual initial floor.
This requires neither a spectral representation nor a conditional-noise
payment. Source-level review alone is not a kernel-check claim; the final
focused checks are recorded below.

## Decisive tests and stop condition

Constant sources have initial edge energy zero and exact cleared cost zero;
the theorem must not equate their finite reciprocal reconstruction to a
constant. Zero or subsequently Haar-null sources must require no inverse of
their squared norm. This theorem does not infer a small INITIAL coefficient
from smoothing; its initial coefficient remains an explicit premise. No
stationary terminal eigenvector or degree-one condition may be inserted silently.

Abandon or revise this route if positivity/symmetry alone cannot propagate the
fixed source floor, or if terminal order cannot preserve the same endpoints.
No theorem will assert that d or eta is spacing-/volume-uniform.

## Scaling screen and retained main producer

Independent source-level review recommends keeping the selected filtered/window
estimate as the main producer; the initial-energy route is optional and stronger.
`lean/YMGap/Continuum/BF4DyadicWilsonSquare.lean:37`, `side`, is `2^j`.
`lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean:201`, `afGap`, and
`:272`, `afNomeSchedule`, give

```
1-w_j = 1.942/[j+(51/121)*floor(log2(j+1))+4].
```

Thus the bare leading coefficient `12*(1-w_j)` has order `1/j`, not `2^(-j)`;
its product with side is unbounded. This is a mathematical scaling screen,
not a newly kernel-checked asymptotic theorem or a lower bound on actual energy.
The exact identity in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:67`,
`padded_family_energy_variance`, RETAINS the whole signed `varianceRemainder`.
Its sign and cancellation have not been supplied. Do not discard it and infer
that the actual initial bound is impossible.

Also distinguish the denominators. That identity concerns finite marginal
`normalizedEnergy` (the original positive odd partition in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:92`,
`normalizedEnergy`) and its OWN-centered `oddVariance`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:87`).
The new initial premise uses `ell[a*(T a)*psi^2]`. The completed selected-state
requirement is instead `side_j*(R_j(side_j)-R_j(side_j+1)) <= c0*R_j(side_j)`:
`lean/YMGap/Continuum/BF4WilsonAllNomeShiftedH1Anchor.lean:418`,
`pathShiftedEpsBound_iff_response`. These quantities may not be substituted
for one another without their SAME-source, center, partition and completion
joins. No completed filtered-state denominator identification or scaling-small
d is proved here.

The appropriate INITIAL finite joins already exist and should be reused, not
scaffolded again: for `psi=oddCentered` at depth `s+1`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilySourceVarianceBound.lean:150`,
`marginal_centered_square`, pins the actual original marginal square to
`oddMass*oddVariance`.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:57`,
`terminalMessage_next`, and polynomial reordering identify this marginal square
with `ell[a*(T a)*psi^2]`.
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyBandResponse.lean:130`,
`energy_shifted`, preserves original temporal energy under that center shift.
Together with the exact Taylor identity, these make the optional initial
producer a signed cancellation estimate against the SAME finite variance,
not an angular ceiling. They do not identify that variance with the completed
filtered-state norm or prove the missing estimate.

NEXT: estimate genuine original filtered/window energy in surviving-form units
on the justified family. Use the initial route only if a useful initial bound
with the actual denominator and adequate terminal-error moduli can be produced.
Independent AF survival, actual all-vector changing-action comparison, useful
delta budget, physical/volume control, limiting QFT and every group remain OPEN.

## Verification budget

Source review and independent mathematical review first. Then only the new
finite persistence and transport leaves, followed by their direct energy
consumer if justified: serialized monitored checks, one 20-GiB worker and
12-GiB OS reserve, fresh capacity preflight each launch, permitted printed
axioms only. No full-root build or audit is planned.

## Observed result

PROVED in the stated finite, conditional scope. The new source-floor leaf has
three permitted printed gates:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceRayleighPersistence.lean:151`,
  `sourceRayleigh_supported`.
- Same file `:179`, `sourceRayleigh_floor_step`.
- Same file `:266`, `sourceRayleigh_floor_persists`.

The actual terminal/cost/reconstructed-energy join also has three permitted
printed gates:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLocalEnergyTransport.lean:109`,
  `terminalFixedEnvelope`.
- Same file `:224`, `original_block_cost_le_initial_energy`.
- Same file `:313`, `original_block_ratio_energy_le_initial_energy`.

The latter uses the EXISTING actual reconstruction onset and signed drift:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.lean:264`,
`blockConditionalRatio_energy_error_relative_tolerance`, and
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalDrift.lean:126`,
`blockConditionalRatio_boundaryDrift_abs_le`. The two terminal errors remain
explicit; no future filtered-derivative ceiling is assumed.

Both final focused checks exited 0 and emitted oleans. Every gate is exactly
`[propext, Quot.sound]`. Logs and SHA-256 digests:

```
/private/tmp/ym-oct7-source-rayleigh-persistence.log
8d2cf71695599473d433b20483a582ce3753c6412c6518cafe861d88b4fb8fdd
/private/tmp/ym-oct7-local-energy-transport.log
81b8c8f5801987924360335c021d88baa6c9b017c64d6c93ac00e3e94098a5cc
```

Checks were serialized with one capped 20-GiB worker and 12-GiB OS reserve,
fresh process/memory preflights and zero swap. Failed elaboration attempts
were repaired and are NOT proof evidence. The dependent record cast was
isolated behind equality lemmas, avoiding a costly proof-field expansion;
no heartbeat increase was used. No new source sorry, axiom, classical input,
frontier-field weakening, full-root/tree build/audit or hashed baseline refresh.
The root import registry is updated, not claimed rebuilt.

Independent reviews verified the positivity identity, original normalization,
constant/null tests and initial-versus-filtered scaling distinction. This is
a source Rayleigh LOWER floor, not an every-vector UPPER contraction bound.
Useful initial smallness, independent AF survival, actual all-vector RG
comparison and delta budget, physical/volume control, limiting QFT, every
group and the whole-project Clay goal remain OPEN. Canonical broad chart
claims are unchanged; no chart is reprinted.
