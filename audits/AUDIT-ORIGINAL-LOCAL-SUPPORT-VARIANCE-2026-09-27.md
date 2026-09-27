# Original local variance with no all-volume comparison cost

Historical checkpoint: `8f8ab78`; declaration line references and four-check
counts below refer to that checkpoint. The subsequent
[local conditional coercivity proof](AUDIT-ORIGINAL-LOCAL-SUPPORT-COERCIVITY-2026-09-27.md)
supplies the residual estimate on embedded literal-local inputs, but not on
arbitrary completed auxiliary states or a scaling family.

## Checked estimate

For 0<w<1, any finite extent, K>=headCutoff(w), and a supported polynomial
p literally local on a link list S with length at most s, the proof constructs

    delta(w,s) = headFloor(w)^(6s) / prefixCap(w)^(6s) > 0
    delta(w,s) Var_Haar(p) <= Var_original(p)
    delta(w,s) Var_original(p) <= Var_Haar(p).

The original full physical face action and its actual partition are retained.
The constant has no extent, cutoff, location, degree or coefficient argument.
It depends explicitly on nome w and support-size budget s. These are static
variance comparisons, not decay in separation or physical time.

## Causal argument and source map

1. Split the full face list into faces touching S and detached faces. The
   split is a proved permutation; the detached product B is literally
   disjoint from S. `collarCount_le` and `fullWeight_split`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalSupportComparison.lean:56` and `:79`,
   reuse the existing collar geometry and prove the count is at most 6s.
2. `background_factorization` (`:87`) proves
   H[p^2 B]=H[p^2]H[B] by exact block-Haar factorization. It does not replace
   the interacting action by independent plaquettes. `background_certificate`
   (`:74`) retains every detached original heat factor with its positivity
   certificate, including its original multiplicity.
3. `local_squared_norm_bounds` (`:125`) bounds only the touching factors.
   If c is their exact count, m=headFloor^c and M=prefixCap^c, it proves
   m H[p^2]H[B] <= H[p^2 fullWeight] <= M H[p^2]H[B].
   `partition_bounds` (`:145`) proves m H[B] <= Z <= M H[B] for the SAME Z.
4. `normalized_square_comparison`,
   `lean/YMGap/Continuum/BF4ExactSlabLocalSupportVariance.lean:188`, combines
   those inequalities before dividing by the original positive Z. The shared
   background mass disappears algebraically; no full-volume lower floor is
   inserted into the final comparison factor.
5. `normalized_variance_comparison` (`:207`) tests the square comparison at
   the explicit original mean for the lower bound, and the explicit Haar
   mean for the upper bound. It does not assume those means agree. The generic
   minimization lemmas are `normalized_variance_le_shifted` and `bare_mean_pin`,
   `lean/YMGap/Continuum/QuaternionHaarDensityVariance.lean:189` and `:235`.
6. `support_variance_comparison` (`LocalSupportVariance.lean:234`) replaces
   the exact collar count by 6s using the proved headFloor<=1 and prefixCap>=1.
   `supportRatio` (`:140`) returns the rational constant; its strict positivity
   is `supportRatio_positive` (`:144`). No analytic coercivity input is assumed.

## Actual covariance and limit consumer

`finite_covariance_eq_normalized_variance`,
`lean/YMGap/Continuum/BF4ExactSlabLocalSupportCovariance.lean:45`, pins the
variance to the diagonal of the EXISTING original full-action finiteCovariance
at cutoff headCutoff(w)+stage. Both moments have the same original reciprocal.
`finite_covariance_support_comparison` (`:61`) proves both inequalities there.

`covariance_support_comparison` (`:81`) passes both bounds to the EXISTING
fixed-extent cutoff-limit covariance using `finite_covariance_converges` and
closed constructive-real order. The existing explicit covariance Cauchy
modulus is retained; no new limit or assumed convergence is introduced.

This supplies two-sided normalization control for local observables in the
original covariance/excitation branch. A positive bare-variance floor gives
a corresponding original floor through the displayed inequality. The code
does not assert nontrivial continuum survival or construct a thermodynamic
limit merely because the comparison coefficient is independent of extent.

## Scope and next missing estimate

- Literally local polynomial support is stronger than the operational
  `EightLayerCone.Localized` condition on a completed vector. No conversion
  for arbitrary completed auxiliary states is proved here.
- The static variance bound does not replace the all-volume coefficient in
  `BF4ExactSlabFiniteVolumeReverseEnergy`. A support-local lower comparison
  for the ACTUAL conditional residuals is still needed for that route.
- Uniformity concerns the relative coefficient. An absolute bound along a
  changing polynomial family also requires control of that family's displayed
  bareVariance(blocks extent,p); no such family pin is inferred here.
- Even such a local residual comparison must account for growing cones and
  changing coupling. The factor above can deteriorate with support size and
  is not claimed uniform in w, beta, or lattice spacing.
- The measure is the original finite SU(2) action. Neither an OS quotient
  norm nor a physical Hamiltonian has been substituted for this ordinary
  variance. Same-theory thermodynamic/scaling/OS/QFT, physical mass,
  nontrivial continuum survival, every compact simple group, and Clay remain
  open. No canonical frontier or displayed chart marker changes.

## Verification boundary

Four final focused checks passed through `scripts/safe_lean_build.py`, each
with one worker and the mandatory 20 GiB ceiling: QuaternionHaarDensityVariance
(13 printed gates), LocalSupportComparison (15), LocalSupportVariance (7),
and LocalSupportCovariance (3). All 38 gates use only {propext, Quot.sound}.
Draft namespace/elaboration errors were corrected before these final checks.
No new sorry, axiom, classical input, erased witness or frontier field.

Sol supplied bounded source/proof work and independent mathematical review;
Luna performed the simple existing-API lookup. Verification was serialized.
All checks completed in their initial tool call; there was no running job to
poll. The five-minute manual-poll cadence and continuous automatic memory
telemetry remain unchanged. No full root build, audit, guard, progress-metric
script, routine literature scan or CI run was requested or performed.
