# Original physical bulk excitation at fixed coupling

## Result and scope

The literal fundamental plaquette now yields an explicitly mean-centered
vector in the ORIGINAL physical bond completion with positive norm and
first-two-lag response floor F/2, where F=nome^36/16 and nome=1/1024.
One computed interior threshold works in EVERY larger ambient width.
This connects the existing spatial response floor to actual physical
vectors; it does not prove survival under changing lattice spacing.

Declarations below are in
`lean/YMGap/Continuum/BF4WilsonOriginalBulkPositiveResponse.lean` unless
another module is named. `probe` (line 66) is the unnormalized fundamental
plaquette at base one and radius zero. `floor` (line 70) is F/2, and
`floor_positive` (line 72) proves it positive. `responseModulus` (line 77)
uses the SAME smaller-source comparison budget at F/4; `excitationModulus`
(line 83) is the maximum for physical lags one and two. Neither threshold
contains larger ambient width. The actual carrier width is
`paddedWidth larger r`; carriers at different widths are not identified.

## Proof and own mean

`BF4WilsonSpatialUnionPositiveResponse.vector_correlator_pin`
(`lean/YMGap/Continuum/BF4WilsonSpatialUnionPositiveResponse.lean:125`)
identifies the literal spatial moments. `lagTwo_floor` (same file, line 149)
and `lagThree_floor` (line 143) give F at spatial times two and three.
`bulk_lag_one_floor` (line 118) and `bulk_lag_two_floor` (line 128) apply
`OriginalBulkComparison.bulkConnected_included_spatial_close`
(`lean/YMGap/Continuum/BF4WilsonOriginalBulkComparison.lean:628`) with
tolerance F/2. The remaining floor is F/2, with the central bond buffer
retained: physical lags one/two correspond to spatial times two/three.

`physicalRepresentative` (line 147) constructs the actual root-image
representative with its explicit Cauchy data. `physicalRepresentative_pin`
(line 150) identifies it with the ORIGINAL physical source value.
`centeredPhysical` (line 162) subtracts its OWN computed unit coefficient,
using `unitCoefficientCauchy` rather than selecting an RC representative.
Original physical subtraction and real scaling retain the sector range
witness, so the result belongs to BondCompletion, not merely the ambient
vacuum complement. `centeredPhysical_value` (line 169) pins it to the
existing actual vacuum projection; `centeredPhysical_orthogonal` (line 177)
proves orthogonality to the actual physical vacuum.

`centeredPhysical_time_pairing` (line 184) and `excitation_time_pairing`
(line 209) identify its OWN time responses with the original connected
scalars. `excitation_norm_floor` (line 217) uses original time-form
contraction, and `excitation_ne_zero` (line 226) excludes the physical zero
class. `positiveExcitation` (line 238) returns the threshold, SAME physical
vector, positive rational floor, orthogonality, OWN norm and both SAME-vector
original-time response bounds as data. No normalization is used.

## Difference from prior finite results

This is NOT the first original finite-width survival result.
`family_bond_geometric_floor` and `family_bond_response_ne_zero`
(`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondOrbit.lean:118`
and `lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondOrbit.lean:131`)
already prove fixed-nome lower responses for interior signed
families at every integer lag. The new contribution is this existing
spatial-floor fraction, a computed threshold uniform in larger ambient
width, and an explicit physical vector centered by its own mean. No
completed-width map or equality of finite-width and spatial means is asserted.

## Verification

The final focused check on 2026-10-02 UTC exited 0, warning-free:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4WilsonOriginalBulkPositiveResponse.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonOriginalBulkPositiveResponse.olean --log-file /tmp/ym-original-bulk-positive-20261002-final.log
```

All 24 printed gates lie within {propext,Quot.sound}; `floor` is axiom-free.
Independent Sol source/math review passed. No sorry, new axiom, classical
choice, analytic premise, native oracle, erased modulus or weakened frontier.

- Source SHA256: `3e7f97e9e882c082fceff50ef7ae00b479309081f1be07968ff73d38d84788b3`.
- Final log SHA256: `2e6bbcfffa1ad21684feffbadf26f3c2dc33a095f3b61eca116903ca6c48ba8c`.
- One monitored 20 GiB capped worker, 12 GiB OS reserve; memory pressure
  reported 86 percent free before and after. Swap remained zero; no competing
  compiler/runner was found. Limits were not raised.
- Root import added. Full root/tree build, full audit, guard and progress
  checks were NOT run. CI remains manual-dispatch only. Canonical chart unchanged.

## Remaining frontier

`padded_family_energy_variance`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:67`)
still gives E=12*(1-w)*OWNVar+varianceRemainder. Useful signed control of the
COMPLETE remainder against OWNVar on a justified changing family remains
missing. Neither this fixed-nome floor nor its spatial threshold supplies
physical time/spacing calibration, nontrivial continuum survival, full
SAME-theory QFT or every compact simple group. The Clay target remains OPEN.
