# Original-action signed-family coercivity

Date: 2026-09-17 UTC. Parent checkpoint: `6496adc`.

## Whole-project goal and result boundary

The goal remains a constructive nontrivial continuum Yang--Mills QFT on R^4
for every compact simple gauge group, with the required QFT axioms and a
positive physical Hamiltonian mass gap, all belonging to the same theory.
The full goal is OPEN. This checkpoint proves a finite signed-family estimate
for the original SU(2) selected action. It does not assert a new spectral gap.

The already proved small-nome fixed-spacing completed Wilson gap and normalized
excitation are preserved: `completed_twoStep_form_gap`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionCompletedGap.lean:153`, and
`normalizedCertificate`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionNormalizedExcitation.lean:165`.
The new work seeks estimates beyond those small-nome guards.

## Checked outcome

Let A be the literal product of selected original physical heat factors,
Z=H[A], and F=sum(c_p*chi_p) for a finite duplicate-free list of physical
fundamental plaquettes. Coefficients c_p are arbitrary signed rationals.
The new result is

```
L(w)*Z*sum(c_p^2) <= 600*U(w)*H[A*F^2].
```

It is `family_partition_coercivity`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDualFamily.lean:374`.
The constants are the existing explicit local window

```
L(w)=min(headFloor(w),1)^24,
U(w)=(1+prefixCap(w))^24,
rho(w)=1-L(w)/U(w),     0<=rho(w)<1.
```

Their sources are `lower`, `upper`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryWindow.lean:45`, `:46`,
and `rate`, `rate_nonnegative`, `rate_lt_one`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDual.lean:133`, `:136`, `:141`.
The theorem quantifies every extent, selected physical nodup action list,
physical nodup observable list and K>=headCutoff(w), with 0<w<1.
No final constant depends on volume, family size or K. It depends on nome;
there is no coupling/spacing-uniform physical mass claim.

## Causal proof, with original weights retained

1. **Actual bounded interference.** Two labels interfere if their boundaries
   meet or a selected action face touches both. `interferes`, `Interferes`,
   `lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryOverlap.lean:32`, `:36`,
   define this concrete relation. The reused Z4 enumeration gives 24 immediate
   and 24*24 mediated candidates: `candidates_length`, same file `:122`.
   `interferenceRow_length_le` (`:154`) bounds each nodup physical row by 600.
   No bounded-degree analytic hypothesis is supplied in place of this proof.
2. **Actual finite dual locality and Gram error.** The polynomial reciprocal
   remains in its selected star (`reciprocal_local`, `dualTest_local`,
   `lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDualGram.lean:58`, `:66`).
   For noninterfering labels, `rest_dual_pairing_zero` (`:85`) proves zero
   under the first erased background. `fullAction_gram_residual_zero` (`:117`)
   restores A and retains the finite residual. With D_p=H[R_p],
   `fullAction_gram_square_bound` (`:211`) gives
   L^2*H[A*d_p,k*d_q,l]^2<=rho^(2k)*D_p*D_q. This is not finite-degree
   orthogonality under A. The unconditional cap is `fullAction_gram_square_le`
   (`:253`); signed weighted Young gives `fullAction_gram_young` (`:309`).
3. **Summed finite tests.** `sparse_gram_bound`,
   `lean/YMGap/Continuum/RationalFiniteSparseGram.lean:172`, uses symmetric
   row counts and signed pair bounds. Its concrete application is
   `family_norm_bound`,
   `lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDualFamily.lean:198`.
   Let Psi_k=sum(c_p*d_p,k), B=sum(c_p^2*D_p), E=H[A*F^2], N=length(labels).
   Together with `family_pairing` (`:222`) and `family_error_bound` (`:273`),
   it proves

   ```
   L*H[A*Psi_k^2] <= (600+rho^k*N)*B,
   H[A*Psi_k*F]+error_k = B,
   2*L*error_k <= rho^k*(L*B+N*E).
   ```

   The error stays signed; its upper bound is exactly the side needed below.
   Duplicate labels are not silently independent: `coefficientAt_map`
   (`:106`) uses the nodup observable list. Repeated input labels must have
   their signed coefficients combined, as the earlier `coefficientAt`
   construction records.
4. **Remove the finite approximation error.** The positive weighted square
   H[A*(600*F-L*Psi_k)^2] gives the division-free bound

   ```
   600*L*B <= 600^2*E
     + rho^k*(600*L*B + 600*N*E + L*N*B).
   ```

   `coercivity_of_finite_tests`,
   `lean/YMGap/Continuum/GNSFiniteDualCoercivity.lean:76`, uses the existing
   explicit `geometricCutoff` and rational all-precision order to remove the
   displayed nonnegative error budget. Family size occurs only there. Only
   positive 600 is cancelled: no division by B or E and no limiting dual.
   The physical application `family_coercivity` (BoundaryDualFamily:310)
   therefore gives L*B<=600*E, including empty/zero families.
5. **Compare with the SAME partition.** `lower_rest_mass_le_full_mass` and
   `full_mass_le_upper_rest_mass`,
   `lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDual.lean:178`, `:193`,
   prove L*D_p<=Z<=U*D_p. `partition_coefficient_budget`
   (BoundaryDualFamily:349) sums the second comparison against c_p^2.
   Its combination with step 4 is the displayed final bound.

## Exact remaining joins and next work

`sourceEnergy`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteBoundaryDualFamily.lean:65`, is the
RAW square H[A*F^2]. Its name does not identify it with a temporal Dirichlet
energy, spatial variance, OS form or physical Hamiltonian.

The next original temporal specialization was NOT FOUND in the current
BoundaryDualFamily, FixedSpatialPlaquetteEnergyFloor, WindowProbeSpan,
DirichletWindow and FacePlacement modules. The source review identifies
finite work, not a new analytic assumption:

- Construct the signed schedule of lower-time c_p and upper-time -c_p
  fundamental faces. Generalize the private `difference_source` and
  `difference_placed`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteEnergyFloor.lean:104`,
  `:121`, to pin that schedule to the original jump of the spatial signed sum.
- Prove the translated lower/upper label lists are nodup and disjoint, with
  doubled coefficient-square sum. Reuse `shift_injective`,
  `lean/YMGap/Continuum/BF4ExactSlabTimeEmbeddingGeometry.lean:39`, and
  `spatialFaces_shift_physical`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFacePlacement.lean:208`.
- Rejoin the full signed square using `windowRatio_span_mul_originalFiniteValue`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowProbeSpan.lean:215`.
  Normalize by the same positive odd-chain partition and use
  `normalizedEnergy_window`,
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletWindow.lean:109`.
  The planned two-time bound has a factor two on each side; their cancellation
  is still part of this unimplemented specialization.

Separately OPEN: an original spatial variance/susceptibility UPPER bound in
these combined coefficients, with the parameter control needed beyond the
small-nome guards or on a justified scaling trajectory. Only both estimates
can supply the existing `clearedDefect_diagonal_nonnegative_iff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialClearedCovariance.lean:175`.
Products, physical transfer orbit and full dense-sector coverage remain
beyond fundamental signed sums. Physical calibration, same-theory continuum
QFT and all compact simple groups remain OPEN.

## Verification

Six changed/new modules passed focused serialized one-worker / 20 GiB checks.
All 62 printed gates lie within {propext, Quot.sound}; final logs are clean.
Independent mathematical reviews passed the same-action normalization, signed
coefficient handling, two nodup guards, factor 600, finite-error removal and
zero cases. No new sorry, axiom or analytic premise; no canonical field,
resource setting or CI change. Five semantic-root imports were added.
Full-root build, full axiom audit, guard and progress suite were NOT run.
The hashed full-audit baseline was not regenerated.

| Final log | SHA-256 |
|---|---|
| `/tmp/ym-plaquette-boundary-partition-20260917.log` | `425496de0fb81396af8f06744803b8d6a3a8f58ddedaca91fb6d4f8340c57d99` |
| `/tmp/ym-plaquette-boundary-overlap-20260917.log` | `ae6c5c679bb2aad0aa6f0b227f8ceade5cbebac1bbd1ce05a2a9e89b0d9c595a` |
| `/tmp/ym-rational-finite-sparse-gram-20260917.log` | `c05c4850ba70ae879bd20b7a18a1269f86447bb4e6fce854be5e7806df536b3d` |
| `/tmp/ym-plaquette-boundary-dual-gram-20260917.log` | `45e21be2b22b5e27c654f1475dc2273fd18f7d324a7f4fbcfaf004367cab97c0` |
| `/tmp/ym-finite-dual-coercivity-20260917.log` | `da07d572a0c550fb9c8a26f064d3d46e2f6df46910970ac1aad435b2058a7589` |
| `/tmp/ym-plaquette-boundary-dual-family-20260917.log` | `11b777d5fa821644003e4a9b04ee46c6a7000b2cdbe26f8a2c98afde516b62fd` |
