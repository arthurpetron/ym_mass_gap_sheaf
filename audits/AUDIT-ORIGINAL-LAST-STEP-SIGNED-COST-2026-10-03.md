# Last-step paired score and complete original signed cost

Whole-project goal: constructive, Mathlib-free continuum Yang--Mills on R^4
for every compact simple group, with nontrivial SAME-theory QFT, isolated
vacuum and finite positive physical mass gap. The whole-project goal is OPEN.

## Mathematical increment

Retain the original interacting transfer T=P_w M_V and ell(p)=H[V*p].
For arbitrary supported signed psi, set

    a=g_(n+r), c=T^r(g_n*psi), A=T a, b=T c,
    W=the complete original one-step half-open action,
    X=lift(A)*c-lift(b)*a, M=I W=T1, J=I(W X^2).

I integrates the full input slice, leaving the SAME output slice. Actual
transfer identities, not new centering premises, prove

    I(WX)=0, I(DW*X)=A*Db-b*DA=Score,
    J=A^2*T(c^2)-2*A*b*T(a*c)+b^2*T(a^2),
    Score^2 <= L(w)^2*M*J, L(w)=relativeCap(w,32).

The two negative cross terms, full original action and M=T1 remain.
Neither positivity of signed c nor division by a or A is used. The signed
dual-square certificate is instantiated using the actual final-link
derivative producer at its existing late-cutoff guard. This alternative
budget uses the surviving incoming c; it does not introduce the fluctuations
already lost earlier as full-history Noise. No pointwise ordering between
this budget and the earlier full-history bound is proved.

For the EXISTING finite reciprocal G_k of A and phi_k=G_k*b, let

    e_k=b*(G_k-A*slope_k)*DA.

The exact cleared derivative and SAME-weight triangle estimate give

    H[Wout*(A*Dphi_k)^2]
      <= 2*L(w)^2*H[Wout*G_k^2*M*J]+2*H[Wout*e_k^2].

No M, G_k^2 or A^2 factor is canceled. Actual projection qbar=Vbar*A
sets Wout=Vbar^2. Every active original link and six angular planes is
included in originalBlockLastStepAngularBudget; inactive links are exactly
zero by the actual transferred ratio's fringe independence for r+1>=1.

The new correction identity is e_k=-b*D(reciprocalResidual_k), hence

    e_(k+1)=(k+1)*residual_k*b*DR,
    H[Wout*e_(k+1)^2]
      <= (k+1)^2*rho^(2k)*H[Wout*(b*DR)^2].

The radius and derivative cost are computed from the actual window.
correctionSquareModulus(rho,cost,epsilon) is polynomialCutoff with degree
two and supplies an all-later fixed-window tolerance, including zero
radius and zero cost. Its actual projected-weight instance keeps Vbar^2.
It is NOT a scaling-uniform correction modulus.

## Forward/backward join

Let Z0=ell(A^2), Z1=ell(A*T A), h=1-w and

    D=Z1*ell(b^2)-Z0*ell(b*T b).

The exact original Taylor identity has energy(A,phi_k)=h*Angular+Rmixed-
Rdiagonal. ONLY Angular is bounded by the new last-step angular budget.
The computed literal combined ceiling is

    S_k=Z0*(h*LastStepAngularBudget+Rmixed-Rdiagonal)+boundaryDrift.

The actual original signed-energy reconstruction supplies

    D <= S_k + mixRate(w,width)^k*blockEnergyErrorCoefficient,
    D <= S_k + epsilon   at its existing computed absolute-error cutoff.

The negative diagonal remainder and signed drift are NOT replaced by
separate absolute ceilings. There is no premise supplying a relative
variance bound, favorable drift, stationary message or replacement action.
The Taylor remainder and S_k still depend on reciprocal degree.

The unpaid analytic target remains the useful original comparison

    side*D <= usefulConstant*Z1*ell(b^2)

for the literal OWN-centered growing square on a justified changing family.
The existing finite-to-completed consumer is
originalOwnBlockCost_converges,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:157`,
with its SAME denominator pin originalOwnBlockVariance_converges at :136.
Those limits hold at FIXED nome, width, scale and lag; they do not prove
the changing-family comparison. The constructed ownPaddedSquareInterval,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:350`,
already provides support for instantiating psi with the literal OWN source.
No further source-support assumption is needed there.

The older full-history score/noise theorem remains valid and available.
Its full-history Noise/B comparison is not a mandatory obligation for this
alternative route. The local L has explicit nome dependence but no width,
cutoff or horizon multiplier; this does NOT make the summed budget, M,
projected weights, reciprocal, partitions, Taylor terms or drift uniform.
No canonical field is inhabited or weakened. Continuum survival, physical
calibration, full QFT structure and every compact simple group remain OPEN.
The exact canonical ASCII block is unchanged and is not reprinted.

## Declaration evidence

Names are in YMGap.Continuum and the namespace matching each module.

| Declaration | Source | Role |
|---|---|---|
| `reciprocalScoreCorrection_residual_derivative` | `lean/YMGap/Continuum/QuaternionHaarReciprocalScoreCorrection.lean:50` | Exact derivative cancellation. |
| `reciprocalScoreCorrection_succ` | `lean/YMGap/Continuum/QuaternionHaarReciprocalScoreCorrection.lean:76` | Actual degree k+1 polynomial identity. |
| `reciprocalScoreCorrection_square_le` | `lean/YMGap/Continuum/QuaternionHaarReciprocalScoreCorrection.lean:139` | SAME-weight geometric/polynomial estimate. |
| `correctionSquareModulus` | `lean/YMGap/Continuum/QuaternionHaarReciprocalScoreCorrection.lean:158` | Explicit degree-two cutoff. |
| `reciprocalScoreCorrection_square_tolerance` | `lean/YMGap/Continuum/QuaternionHaarReciprocalScoreCorrection.lean:190` | Uses constructed window floor/cap and literal cost. |
| `lastStepPairedResidual` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepScoreVariance.lean:65` | Original incoming/outgoing pair. |
| `lastStepScoreBudget` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepScoreVariance.lean:70` | Retains M=T1 and full square. |
| `lastStepPairedResidual_mean_zero` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepScoreVariance.lean:131` | Constructed exact centering. |
| `lastStepPairedResidual_square_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepScoreVariance.lean:169` | Both negative mixed terms retained. |
| `lastStep_score_certificate` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepScoreVariance.lean:221` | Original signed derivative certificate consumer. |
| `lastStep_score_weighted_multiplier_square_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepScoreVariance.lean:262` | Retains arbitrary certified output weight and multiplier square. |
| `lastStep_reciprocal_gradient_square_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepScoreVariance.lean:296` | Actual finite reciprocal correction retained. |
| `original_block_lastStep_gradient_square_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepConditionalEnergy.lean:78` | Actual successive original messages. |
| `original_block_projected_plane_lastStep_gradient_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepConditionalEnergy.lean:118` | Literal qbar^2 plane with Vbar^2/G_k^2. |
| `originalBlockLastStepAngularBudget` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepConditionalEnergy.lean:168` | Computed active-link/six-plane sum. |
| `original_block_lastStep_weightedAngularEnergy_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepConditionalEnergy.lean:199` | Complete angular consumer, exact inactive zeros. |
| `original_block_lastStep_correction_square_tolerance` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepConditionalEnergy.lean:232` | Computed actual projected correction onset. |
| `originalBlockLastStepSignedBudget` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSignedCost.lean:48` | Literal combined signed expression. |
| `original_block_lastStep_signedCost_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSignedCost.lean:90` | COMPLETE original cost, retained signs, explicit error. |
| `original_block_lastStep_signedCost_tolerance` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSignedCost.lean:108` | Existing computed absolute error cutoff consumed. |

## Verification and independent review

Four focused checks ran serially through scripts/safe_lean_build.py with
one worker, 20 GiB hard ceiling and 12 GiB reserve. Each launch had fresh
process/swap/memory-pressure preflight; swap was zero. Accepted logs:

| Target | Accepted log | Public gates |
|---|---|---|
| QuaternionHaarReciprocalScoreCorrection | `/tmp/ym-reciprocal-score-correction-20261003-a.log` | 5 |
| BF4ExactSlabFixedSpatialLastStepScoreVariance | `/tmp/ym-last-step-score-variance-20261003-d.log` | 7 |
| BF4ExactSlabFixedSpatialLastStepConditionalEnergy | `/tmp/ym-last-step-conditional-energy-20261003-b.log` | 5 |
| BF4ExactSlabFixedSpatialLastStepSignedCost | `/tmp/ym-last-step-signed-cost-20261003-b.log` | 3 |

Twenty gates are within {propext, Quot.sound}; correctionSquareModulus is
axiom-free. No accepted log has errors or warnings. Failed elaboration
attempts are not acceptance evidence. No sorry/admit, Classical,
native_decide, noncomputable, custom axiom or resource-budget raise added.
Root imports are registered but the full root/library build, full audit,
guards and progress runners were NOT run. CI remains unchanged/off.

Checked source SHA-256 values, in target order:

    e0bde70bd7465be5bbc66c61e8b842f8ca8992a64c5ec6c4e9388528e90db7d3
    9b45d2c04d85f4a0a343b9fc44d3a0f888784f957c33a1e3f9bb3342a25e3052
    11deaa7f8e61fdb167133161146cfd66ade72025771da55df96ef0978162d22e
    f0dc8fd3190db27a971b57f093474380918d44c4aafeca199d41ed0d4846f347

Sol supplied the correction lemma and actual angular consumer. Root proved
the paired last-step estimate, exact square expansion and signed-cost join,
and serialized verification. Independent bounded Luna source/log/hash
review found no algebra or scope defect and confirmed the remaining
family-relative estimate is unpaid. Source/planning review of a free-model
diagnostic is NOT claimed as a BF4 theorem or counterexample.
