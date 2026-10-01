# Both signs of the centered source defect

Date: 2026-10-01 UTC. Two positive polynomial sources on the actual
one-link SU(2) heat give opposite signs for the centered source-norm defect.
This excludes a universal-sign shortcut from source positivity and the bare
heat eigenpin. Neither source is identified with an original 4D terminal
message, so this is not a Yang--Mills counterexample.

## Checked finite example

The module is
`lean/YMGap/Continuum/SU2QuaternionSourceDefectSignFence.lean`.
Use one quaternion block, the actual product heat at w=1/2 and K=3,
f=chi_1, and chi_2=f^2-1. The sources are

    q_plus  = 1+chi_2/4 = 3/4+f^2/4,
    q_minus = 1-chi_2/4 = 1/4+(4-f^2)/4.

`sourcePlusCertificate` and `sourceMinusCertificate`, lines 77 and 84,
return positive certificates under arbitrary supported insertions. The
second uses the unit-quaternion bound f^2<=4. `fundamental_eigenpin`,
line 91, proves Pf=(1/2)^3*f for this same actual operator;
`heatQuarterFloor`, line 108, supplies its positive kernel floor.

Each source is centered in its OWN density q*Pq. The checked common mass
is 4097/4096, both first moments and centers are zero, and the variances
are respectively 5126/4097 and 3070/4097. They are strictly positive.
The declarations are `plusMass_value`, `minusMass_value`,
`plusCenter_zero`, `minusCenter_zero`, `plusVariance_value`,
`minusVariance_value`, `plusVariance_positive`, and
`minusVariance_positive` in the same module.

`sourceNormDefect1` is the generic expression underlying the existing
source norm defect, evaluated with this source's actual center. Its two
exact values are

    delta(q_plus)  = -765/16384,
    delta(q_minus) =  255/16384.

`plusDefect_value` and `minusDefect_value`, lines 242 and 250, prove these
values. `universal_nonnegative_defect_false` and
`universal_nonpositive_defect_false`, lines 267 and 275, refute both
universal sign claims, even for certified sources with positive own-law
variance. The actual BF4 terminal source is not instantiated here.

## Source review of the new finite band

The following is an arithmetic deduction from checked definitions and
inequalities, not a new kernel-checked theorem in this checkpoint.
For a nonempty family of m faces, the recent SAME-variance band has

    rho = w^12*(headFloor(w)/prefixCap(w))^(56*m),
    E_original <= (1-rho)*Z*Var_odd.

The definitions `localLower` and `localUpper` are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformLocalBand.lean:44`
and `:47`. `headFloor_le_oneThirtySecond` in
`lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46`
and `prefixCap_ge_one` in
`lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:32` imply

    0 < rho <= 2^(-280),  hence 1-rho >= 1-2^(-280).

Thus this PARTICULAR certified ceiling cannot tend to zero or meet the
positive retained-fraction guard c<1/2 in
`BF4WilsonAllNomeSectorSourceTransfer.relative_derivative_bound`,
`lean/YMGap/Continuum/BF4WilsonAllNomeSectorSourceTransfer.lean:116`.
This is not a lower bound on the true energy/variance ratio. It does not
exclude a stronger estimate on the same physical theory.

## Next mathematical input

Retain the complete source-dependent defect and signed Ward/Taylor
remainder; neither may be assigned a universal sign from positivity.
The checked consumer `finite_family_increment_variance` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceTaylor.lean:101`
keeps the original headCutoff(w)+stage schedule, terminal messages,
partition and centered variance. A useful scaling estimate for its
complete signed correction remains open. Improving only the current
global floor/cap coefficient cannot fill that input.

Physical observable/scaling justification, nontrivial continuum survival,
uniform physical decay and mass calibration, full same-theory continuum
QFT, and every compact simple group remain open. No canonical field or
chart marker changes.

## Verification

The final repaired focused check passed all 24 printed axiom gates exactly
in {propext, Quot.sound}. No sorry, new axiom, Classical dependency,
native_decide or noncomputable declaration was introduced.

The first draft check hit the mandatory 20 GiB kernel ceiling. Algebraically
reducing the centered defect to the smaller raw correction before finite
evaluation repaired this without raising any safety limit. The final run
was serialized by the main agent through the monitored launcher with one
worker, 20 GiB ceiling and 12 GiB OS reserve. Root import registration is
not aggregate-root verification. No full build, tree audit or guard ran.

Final log: `/tmp/ym-source-defect-sign-fence-repaired-20261001.log`.
SHA-256: `fd78aece15583c78c174a12ce59939156b6ebfde818b43f63b5888c13022b01a`.
