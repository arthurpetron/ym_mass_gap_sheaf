# Degree-uniform derivative control of the original conditional ratio

Whole-project goal: constructive, Mathlib-free continuum Yang--Mills on R^4
for every compact simple group, with nontrivial SAME-theory QFT, isolated
vacuum and finite positive physical mass gap. The whole-project goal is OPEN.

## New mathematical estimate

Keep the original action V, transfer T, terminal A=g_(n+t), and
b=T^t(g_n*psi). Let C be the constructed interval radius of psi. For
sigma=1/u, R=sigma*A-1, x=-R, h=1+R and S_k=corrector R k, define

    J_0=0, J_(k+1)=S_k+x*J_k,
    slope_k=sigma^2*J_k, F_k=h^2*J_k=A^2*slope_k.

The exact finite identity

    1-F_(k+1)=residual(R,k)*(x+(k+1)*h)

constructs certificates for F_k and 1-F_k under only 0<=A<=u, u>0.
It includes k=0 and possible zeros of A. Their product yields
1-F_k^2>=0. The literal finite G_k=sigma*S_k also has a certificate
1-(A*G_k)^2>=0 under the SAME non-strict window. These are polynomial
multiplier statements, NOT existence of an inverse at a zero of A.

The differentiated ratio phi_k=G_k*b satisfies the coefficient identity

    A*Dphi_k=(A*G_k)*Db-(A*slope_k*b)*DA.

For a general multiplier j, actual relative source certificates C*A plus
and minus b give the exact positive decomposition

    C^2-(j*b)^2 = j^2*(C*A+b)*(C*A-b)
                     +C^2*(1-(A*j)^2).

Use j=A*slope_k. The SAME certified weight W then gives

    H[W*(A*Dphi_k)^2] <= 2*H[W*(Db)^2]+2*C^2*H[W*(DA)^2].

The right hand side is independent of reciprocal degree k. There is no
strict lower window, inverse lower-floor cost, k*rho^k penalty, derivative
exchange with a limit, or change of weight in this estimate.

For the actual full projected endpoint source, terminal fringe independence
proves qbar=P_F(V*A)=Vbar*A with Vbar=P_F(V). Taking W=Vbar^2 and summing
all original blocks and all six planes gives

    weightedAngularEnergy(qbar,phi_k)
      <= 2*weightedAngularEnergy(Vbar,b)
           +2*C^2*weightedAngularEnergy(Vbar,A).

The complete original action survives projection. Vbar^2 has NOT been
identified with V. The dimension guard 0<N(width) solely pins the existing
tail=N(width)-1 angular sum to the correct original Haar carrier.

For t>=1, the original product transfer averages every inactive output
coordinate. Its exact output independence, terminal independence and finite
corrector transport prove phi_k fringe independent without a locality
hypothesis on the initial signed psi. Thus the EXISTING mixed Taylor bound
actually applies to the constructed ratio. With h=1-w it gives

    energy(A,phi_k) <= h*(2*Gamma(Vbar,b)+2*C^2*Gamma(Vbar,A))
                      +h^2*pairBudget(qbar,qbar*phi_k^2),

where Gamma denotes the same full weightedAngularEnergy. The two ordinary
heat-cutoff guards are explicit: headCutoff for original positivity and
sufficientCutoff for the Taylor remainder theorem. No fringe-independence
or analytic-budget hypothesis is added. The mixed pairBudget still depends
on the literal phi_k; it is NOT asserted uniform in k or on a scaling family.

## Declaration evidence

| Declaration | Source | Role |
|---|---|---|
| `sensitivity_complement_succ` | `lean/YMGap/Continuum/QuaternionHaarReciprocalSensitivity.lean:87` | Exact residual complement. |
| `sensitivityCertificate` | `lean/YMGap/Continuum/QuaternionHaarReciprocalSensitivity.lean:201` | Constructed finite multiplier positivity. |
| `sensitivityComplementCertificate` | `lean/YMGap/Continuum/QuaternionHaarReciprocalSensitivity.lean:207` | Constructed finite complement positivity. |
| `reciprocalMultiplierSquareCertificate` | `lean/YMGap/Continuum/QuaternionHaarReciprocalSensitivity.lean:254` | Unit multiplier cap without a strict lower floor. |
| `reciprocal_angularDerivative` | `lean/YMGap/Continuum/QuaternionHaarReciprocalSensitivity.lean:286` | Derivative of the existing finite reciprocal. |
| `reciprocalSlope_multiplier_pin` | `lean/YMGap/Continuum/QuaternionHaarReciprocalSensitivity.lean:326` | Same-carrier dimensionless sensitivity pin. |
| `reciprocalSensitivitySquareCertificate` | `lean/YMGap/Continuum/QuaternionHaarReciprocalSensitivity.lean:349` | Unit sensitivity square cap. |
| `relative_multiplier_square_certificate` | `lean/YMGap/Continuum/QuaternionHaarReciprocalRatioGradientBound.lean:45` | Relative signed-source cap for any certified multiplier. |
| `reciprocal_ratio_cleared_derivative` | `lean/YMGap/Continuum/QuaternionHaarReciprocalRatioGradientBound.lean:104` | Exact coupled derivative, sign retained. |
| `reciprocal_ratio_cleared_gradient_square_le` | `lean/YMGap/Continuum/QuaternionHaarReciprocalRatioGradientBound.lean:133` | Degree-uniform SAME-weight gradient bound. |
| `projected_terminal_source_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalGradient.lean:71` | Actual complete projected endpoint action. |
| `blockConditionalRatio_plane_gradient_bound` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalGradient.lean:110` | Actual one-plane instance. |
| `blockConditionalRatio_weightedAngularEnergy_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalGradient.lean:199` | Actual all-block, six-plane consumer. |
| `blockConditionalRatio_fringe_independent` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalGradient.lean:283` | Actual averaged output, t>=1, with no initial locality premise. |
| `blockConditionalRatio_energy_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalGradient.lean:297` | Original energy consumes the constructed ratio and gradient bound. |

## Backward residue and direction

Degree uniformity is not family uniformity. A, b, Vbar, C and their costs
still depend on the original nome, heat cutoff, width, terminal depth,
block length and observable. No useful variance-relative rate is proved.

The remaining backward input from the original Rayleigh split is still a
useful bound on Z0*energy(A,phi_k)+boundaryDrift(A,phi_k) relative to
Z1*ell(b^2), with the previously constructed reconstruction error paid on
the justified changing family. The mixed Taylor remainder also remains.

The exact coupled expression above preserves the signed cross term needed
for vacuum-derivative cancellation; the triangle ceiling discards it.
It must not be substituted
for a proved changing-family estimate of that cancellation. The next
action-specific analysis should retain the coupled square and its actual
weight and partitions, rather than impose separate extensive vacuum-cost
ceilings as a new proof prerequisite.

The inspected source does not provide the missing comparison:

- `derivative_core_upper`, `lean/YMGap/Continuum/BF4WilsonAllNomeSectorSmoothingEnergy.lean:200`, concerns the completed time-generator form, not this coordinate gradient.
- `productMap_angular_bounds`, `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularMessage.lean:108`, uses an erased-factor message and certified positive input.
- `productMapRelativeBound`, `lean/YMGap/Continuum/SU2QuaternionProductHeatRelativeAngularMessage.lean:91`, has a positive-input certificate; signed b is not supplied one.
- `productHeat_normalized_coefficientSquare_variance_bound`, `lean/YMGap/Continuum/SU2QuaternionProductHeatScoreVariance.lean:66`, bounds the square of a normalized score expectation under its stated density, not this Vbar^2 square integral.
- `filteredSquare_le_endpointSquare`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalNoise.lean:177`, gives B<=endpointSquare, not the needed reverse surviving-norm comparison.
- `family_normalized_ward`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:144`, retains its own original odd-marginal Ward residual and is not the new weighted gradient law.

No canonical field, guard, axiom or `sorry` was changed. No continuum,
physical-gap, scaling or all-groups box closes; the canonical ASCII chart
therefore remains unchanged and is not reprinted.

## Verification boundary

Focused checks only, serialized one worker, hard 20 GiB worker ceiling,
12 GiB OS reserve, fresh process/memory/swap preflight before every launch:

- `/tmp/ym-reciprocal-sensitivity-20261003-c.log`: exit 0, twelve gates;
  two axiom-free, ten exactly `{propext, Quot.sound}`.
- `/tmp/ym-reciprocal-ratio-gradient-20261003-d.log`: exit 0, three gates
  exactly `{propext, Quot.sound}`.
- `/tmp/ym-original-block-conditional-gradient-20261003-c.log`: exit 0,
  five gates exactly `{propext, Quot.sound}`.

Twenty public gates total, two axiom-free and eighteen permitted. Source
SHA-256 at these accepted checks:

- `QuaternionHaarReciprocalSensitivity.lean`:
  `cb3ca5fe539e8591483b0a86ff4ea1cfdfda75c0cc955c7adc8b54f178bcd0ab`.
- `QuaternionHaarReciprocalRatioGradientBound.lean`:
  `1b9ebc248cb306bb7e062cd56f8456e66c01d5f8b8782d15114ed52372d699ba`.
- `BF4ExactSlabFixedSpatialBlockConditionalGradient.lean`:
  `b57abde91d31e4b0eb5b866471a38ca23845ea6faee333d8ada37ba035be517d`.

Independent Luna read-only review reread these final source hashes and
accepted logs. It confirmed the coefficient signs, non-strict-window API,
same projected weight, dimension guards, actual fringe transport, distinct
cutoff guards and unbounded mixed-remainder scope. No errors, warnings,
`sorryAx`, classical or custom axiom occurred in the accepted outputs.
Sol's separate backward source review identified the coupled-square
cancellation, rather than a new isolated terminal-gradient premise, as the
appropriate next action-specific frontier. These reviews add no proof claim.

No full root/tree build, aggregate audit or broad guard/test suite was run.
Root imports are registration only. CI remains off.
