# Active Casimir norms in the original channel energy

## Result and scope

The original signed plaquette-family channel error is now bounded by raw
Sobolev moments differentiating only the observable's active footprint.
Both third-moment and Haar-square channel contractions have coefficient one.
There is no passive derivative or channel-count multiplier in the resulting
budget. This reduces the cost that must be controlled; it does not establish
its smallness relative to the interacting variance on a changing family.

Write A for `familyObservableBlocks width qs`, H for the SAME product Haar
functional, C_A for its active Casimir, h=1-w, t=h^2/2 and
rho=w^((K+1)*(K+3)). For the ORIGINAL projected terminal source q and
f=`spatialSpan width coeff qs`, define

    S3_A(p) = H[(C_A p)(C_A^2 p)].
    D_A = h^3/6 * [(S3_A(q)+S3_A(q*f^2))/2+S3_A(q*f)]
          + rho * [(H[q^2]+H[(q*f^2)^2])/2+H[(q*f)^2]].

At 0<w<1, headCutoff(w)<=K, base<width, and every listed plaquette in
spatialFaces(base), the actual original positive-depth energy satisfies

    E <= (h+t)*Cfoot*(Z*OWNVar)
         + t*(-SIGNED channelCurvature-48*channelObservableSquare) + D_A.

Here q uses terminal depth n+1; Z and OWNVar are `oddMass` and `oddVariance`
at that SAME depth and width. Cfoot is the existing explicit
`channelFirstOrderVarianceConstant hw0 hw1 qs.length`. Arbitrary signed
coefficients and repeated plaquettes are permitted. Signed face cross terms
remain inside the existing curvature and observable-square quantities.
No individual channel is assumed positive or recentered separately.

## The causal argument

First use the existing exact passive Gram-channel energy decomposition.
Only the projected channel source b_c is passive-independent; the original
q is not asserted to be. Thus Cfull(b_c)=channel_c(C_A q). Its third moment
is the first-Casimir quadratic form evaluated on Cfull(b_c). Applying the
existing coefficient-one angular channel contraction to C_A q gives

    sum_c weight_c*S3_full(b_c) <= S3_A(q).

Passive-independent multiplication pulls f and f^2 through the actual
channel projection. The same argument applies to q*f and q*f^2. The raw
square terms use the existing Haar Bessel contraction, again with coefficient
one. Apply the previously checked cubic Sobolev bound in EACH channel,
retain its Casimir-12 negative square, then sum and insert D_A. The existing
same-source first-order variance bound supplies Cfoot*(Z*OWNVar).

This does NOT replace a global cubic heat weight by an active weight. It
does NOT identify the earlier growing-Wilson-square global projection gain
with a sum of these channel squares. That global-gain route is unchanged.
No ordering of the new and old numerical error budgets is claimed.

## Source declarations

| Declaration | Source | Content |
| --- | --- | --- |
| `activeThirdMoment` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelCasimirCube.lean:53` | Literal S3_A on the displayed original source |
| `activeThirdMoment_nonnegative` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelCasimirCube.lean:120` | Angular-square positivity |
| `channelSource_mul_pullback` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelCasimirCube.lean:138` | Exact coefficient identity for passive-independent insertion |
| `channelSource_thirdMoment_le_activeThirdMoment` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelCasimirCube.lean:151` | Coefficient-one full channel third-moment contraction |
| `channelSource_mul_thirdMoment_le_activeThirdMoment` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelCasimirCube.lean:209` | Same contraction with inserted original q*r |
| `channelSource_mul_haarSquare_sum_le` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelSobolevError.lean:86` | Coefficient-one inserted Haar-square contraction |
| `activeSourceSobolevErrorBudget` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelSobolevError.lean:110` | Explicit D_A |
| `channelSource_sobolevError_sum_le_active` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelSobolevError.lean:122` | Aggregate actual channel error <=D_A |
| `sourceRemainder_le_sobolev_retainedSquare` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelSobolevError.lean:180` | Signed remainder with Casimir-12 negative square retained |
| `familyActiveSobolevErrorBudget` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSobolev.lean:116` | Original source and actual family partition instance |
| `familyChannelTaylorDebt_le_activeSobolev_retained` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSobolev.lean:124` | Original signed debt consumer |
| `padded_family_energy_le_activeSobolevChannelVariance` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelSobolev.lean:226` | Actual energy estimate displayed above |

## Remaining input

OPEN: useful control of D_A and the complete signed curvature/square balance
against OWN variance on a physically justified changing family. Raw norms
still depend on the original source, nome, cutoff, width and terminal depth.
Removing passive derivatives does not prove width-, coupling- or
spacing-uniform control. No physical mass calibration, continuum excitation
survival, full same-theory QFT, every-group realization or Clay closure is
supplied. No exact displayed chart claim changes.

## Verification boundary

Three focused checks passed, covering all 7+6+3 printed gates with only
{propext,Quot.sound}. Accepted logs are listed below. Draft checks rejected
missing namespace qualification, an underconstrained channel congruence and
implicit carrier-size transport; explicit types/equality transport fixed
these without raising limits. Failed logs are not proof evidence.

Independent Sol mathematical source review passed, including the inherited
original energy Taylor identity, same partition pin and OWN interacting
variance. The review found no missing assumption; it confirms that the
channel contraction gives no uniform normalized error or scaling smallness.

Independent Luna evidence review passed: source/log hashes, all declaration
anchors, sixteen gate outputs, absence of forbidden source markers, the single
root import, documentation scope, whitespace check and byte-identical chart
fences against HEAD. The separate requested-paper report records fifteen
unique papers and imports no external theorem as a premise.

Each check used `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20`, serialized with a 12-GiB OS reserve. Fresh
preflight found no competing compiler, runner or pytest; free capacity was
84--86%, with zero swap. No source sorry, new axiom, analytic assumption or
frontier weakening was introduced. One downstream root import includes all
three modules. The root, full build/audit/guard and progress script were NOT
run; the automatic baseline was not regenerated. CI remains manual-only;
canonical chart fenced blocks remain unchanged.

## Source and accepted log hashes

| Artifact | SHA256 |
| --- | --- |
| `SU2QuaternionPassiveChannelCasimirCube.lean` | `24f51fdbf582c46a811d75899191aa3fbe2c23c868eb657e317bce0c87aa1f3d` |
| `SU2QuaternionPassiveChannelSobolevError.lean` | `f85af1ed23ca9e921fb37c56968c404098581f2b01bab809f8a971ae4eda558f` |
| `BF4ExactSlabFixedSpatialFamilyChannelSobolev.lean` | `d007de7f905b617a540a698f51bf15526684493fd69a261e552fb2a81cfc73bb` |
| `/tmp/ym-active-casimir-cube-20261002-first.log` | `cba94131cef1ae767a6ab6ecb848adc45092f237c5250338506cd1f2fa51a109` |
| `/tmp/ym-active-sobolev-error-20261002-second.log` | `2b9cfd2f9c3a9d720363b10d8f8e5927f23d6bd07f087053d9e85fe012c3a07c` |
| `/tmp/ym-family-active-sobolev-20261002-third.log` | `8603935e006eb58015f4e766ac182c1b4da79cafd9499d20394077edc841c73c` |
