# Coupled original score/noise bound and actual energy consumer

Whole-project goal: constructive, Mathlib-free continuum Yang--Mills on R^4
for every compact simple group, with nontrivial SAME-theory QFT, isolated
vacuum and finite positive physical mass gap. The whole-project goal is OPEN.

## Mathematical contraction

Write I for integration over the full input history, retaining the output
tail. For the original positive window W and its output derivative d=DW,
the two weights U=L*W+d and V=L*W-d have constructed certificates. For a
supported signed input X the exact two-history identity is

    det(U;1,X)+det(V;1,X)+I_x I_y[U_x V_y (X_x+X_y)^2]
      = (I U+I V)*(I(UX^2)+I(VX^2))-(I(UX)-I(VX))^2
      = 4*(L^2*I(W)*I(WX^2)-I(dX)^2).

Each term on the left has a positive-cone certificate. Copying duplicates
only integrated input heads, not output spectators. Set

    A=I W, b=I(W f), X=lift(A)*f-lift(b).

Exact centering and partial-Haar/lift identities produce

    L^2*A^2*(A*I(Wf^2)-b^2)-(A*I(df)-b*I(d))^2 >= 0.

There is no division, inverse message, scalar partition floor or erased
output variable in this proof. Generic positivity inputs are constructed
by the actual original-action producer, not left as analytic hypotheses.

The actual W is g_n times the full t-step half-open interacting action,
t=r+1>=1. Its last kinetic link supplies BOTH signed derivative
certificates with L=relativeCap(w,32). All earlier transition factors,
spatial weights and g_n are retained and output-derivative independent.
Exact original window/moment pins give

    A=g_(n+t), b=T^t(g_n*psi),
    Noise=A*T^t(g_n*psi^2)-b^2,
    Score=A*Db-b*DA,
    L(w)^2*A^2*Noise-Score^2 >= 0.

The literal padded-square instance retains its OWN chronological center
middleRatio(n+1,n,f). The producer also permits arbitrary supported f and
rational c in psi=shifted(f,c), without a sign or interval-cap premise.

For G_k the EXISTING finite reciprocal and slope_k its derivative sensitivity,
the exact positive decomposition is

    L^2*Noise-(G_k*Score)^2
      = G_k^2*(L^2*A^2*Noise-Score^2)
           +L^2*Noise*(1-(A*G_k)^2).

The existing multiplier certificate requires only 0<=A<=u and u>0, not a
strict lower floor. The exact gradient decomposition is

    A*D(G_k*b)=G_k*Score+e_k,
    e_k=b*(G_k-A*slope_k)*DA.

For EVERY reciprocal degree k and the SAME positive output weight M,

    H[M*(A*Dphi_k)^2]
      <= 2*L(w)^2*H[M*Noise]+2*H[M*e_k^2].

The leading noise coefficient is degree-independent. The correction is
explicit and has NOT been dropped or asserted uniformly negligible.

Actual projection pins qbar=P_F(V*A)=Vbar*A. Thus M=Vbar^2 meets the
ORIGINAL qbar^2 angular form. The computed originalBlockScoreAngularBudget
sums the displayed plane budget over precisely active original links and
all six planes. Every inactive output contribution is exactly zero by the
already-proved actual fringe independence, not by replacing the action.
The full consumer gives, with h=1-w,

    energy(A,phi_k)
      <= h*originalBlockScoreAngularBudget
           +h^2*pairBudget(qbar,qbar*phi_k^2).

The mixed Taylor term remains literal. This is an actual finite energy
upper bound, not a favorable boundary-drift sign or surviving-norm estimate.

## Declaration evidence

| Declaration | Source | Role |
|---|---|---|
| `copySupported` | `lean/YMGap/Continuum/SU2QuaternionMultiHeadVarianceReplica.lean:305` | Public wrapper for existing shared-tail copy support. |
| `copyCertificate` | `lean/YMGap/Continuum/SU2QuaternionMultiHeadVarianceReplica.lean:312` | Public wrapper for existing certified copy. |
| `mixedPlusGram` | `lean/YMGap/Continuum/SU2QuaternionMultiHeadSignedDualSquare.lean:44` | Literal positive mixed two-history square. |
| `mixedPlusGram_certificate` | `lean/YMGap/Continuum/SU2QuaternionMultiHeadSignedDualSquare.lean:90` | Constructs the mixed certificate. |
| `relativeDualSquare_certificate` | `lean/YMGap/Continuum/SU2QuaternionMultiHeadSignedDualSquare.lean:183` | Two-signed-weight square contraction. |
| `conditionalCovarianceSquare_certificate` | `lean/YMGap/Continuum/SU2QuaternionMultiHeadSignedDualSquare.lean:256` | Exact centered covariance/noise certificate. |
| `halfOpenAction_outputRelative` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockScoreVariance.lean:144` | Full-window final-link derivative, one local cap. |
| `blockWindowWeight_outputRelative` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockScoreVariance.lean:194` | Retains original terminal factor. |
| `original_block_scoreVariance_certificate` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockScoreVariance.lean:247` | Actual score/noise producer. |
| `paddedSquare_own_block_scoreVariance_certificate` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockScoreVariance.lean:337` | Literal chronological OWN instance. |
| `conditionalScore` | `lean/YMGap/Continuum/QuaternionHaarConditionalScoreGradient.lean:38` | Actual coupled derivative polynomial. |
| `reciprocalScoreCorrection` | `lean/YMGap/Continuum/QuaternionHaarConditionalScoreGradient.lean:43` | Literal finite reciprocal correction. |
| `scoreMultiplierCertificate` | `lean/YMGap/Continuum/QuaternionHaarConditionalScoreGradient.lean:59` | Algebraic A^2 cancellation, without division. |
| `reciprocal_score_cleared_derivative` | `lean/YMGap/Continuum/QuaternionHaarConditionalScoreGradient.lean:95` | Exact cancellation-preserving Leibniz identity. |
| `reciprocal_score_weighted_square_le` | `lean/YMGap/Continuum/QuaternionHaarConditionalScoreGradient.lean:116` | SAME-weight leading noise ceiling. |
| `reciprocal_score_gradient_square_le` | `lean/YMGap/Continuum/QuaternionHaarConditionalScoreGradient.lean:154` | Complete gradient, explicit correction. |
| `original_block_coupled_gradient_square_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalScoreGradient.lean:64` | Both inputs produced by full original window. |
| `original_block_projected_plane_score_gradient_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalScoreGradient.lean:105` | Actual qbar^2 energy plane. |
| `originalBlockScoreAngularBudget` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalScoreGradient.lean:154` | Computed active-link/six-plane budget. |
| `original_block_score_weightedAngularEnergy_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalScoreGradient.lean:183` | Every original angular contribution consumed. |
| `original_block_score_energy_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalScoreGradient.lean:216` | Direct original energy consumer. |

## Uniformity and remaining inputs

L(w)=relativeCost(w,32)+1 is explicit and nome-dependent:
`QuaternionHaarHeatRelativeAngularBound.relativeCap`,
`lean/YMGap/Continuum/QuaternionHaarHeatRelativeAngularBound.lean:41`.
The computed late-cutoff guard is relativeCutoff(w,32)<=K, with that
definition at the same file:46. One local derivative constant has no width,
K or t multiplier. This does NOT make the summed noise budget, correction,
mixed Taylor term, partitions or a physical mass floor uniform in those
parameters. The actual producer is for the existing SU(2) quaternion model.

The extra projected Vbar^2 is preserved. The existing original conditional
noise identity uses ell(Noise)=H[V*Noise]; it does not identify that with
H[Vbar^2*Noise]. Nor does an upper ceiling on conditional noise establish
a useful comparison with surviving B=ell[b^2].

Next causal frontier: jointly control projected-weighted Noise, mixed
Taylor cost and signed boundary drift relative to the SAME surviving B
on a justified changing family. Existing fixed-window reciprocal/angular
reconstruction remains available for the explicit correction; fixed-window
convergence is not family-uniform control. Nontrivial continuum survival,
physical calibration, full same-theory QFT axioms and every compact simple
group remain OPEN. No canonical bundle field or displayed chart box closes.
The canonical chart is unchanged and is not reprinted.

The existing exact Taylor identity retains Rmixed-Rdiagonal, not merely a
positive mixed ceiling: `sourceEnergy_taylor_angular`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatAngularTaylor.lean:107`.
The upper-bound consumer used here discards favorable Rdiagonal>=0:
`sourceEnergy_le_firstOrder_add_mixed_quadratic`,
`lean/YMGap/Continuum/SU2QuaternionCyclicDiagonalRemainder.lean:127`.
The original energy/drift endpoint cancellation is retained by
`clearedRayleighCost_split`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:214`.
The next signed estimate should use these exact identities together; the
present upper bound does not assert their remainder/drift signs or eliminate
the projected weight.

## Verification

All five checks ran separately through scripts/safe_lean_build.py with
one worker, 20 GiB hard ceiling and 12 GiB reserve, after fresh process,
swap and memory-pressure preflight. No swap was in use. Accepted logs:

| Target | Accepted log | Public gates |
|---|---|---|
| MultiHeadVarianceReplica | `/tmp/ym-multihead-variance-copy-20261003-a.log` | 8 (6 unchanged) |
| MultiHeadSignedDualSquare | `/tmp/ym-multihead-signed-dual-square-20261003-b.log` | 4 |
| BlockScoreVariance | `/tmp/ym-original-block-score-variance-20261003-c.log` | 4 |
| ConditionalScoreGradient | `/tmp/ym-conditional-score-gradient-20261003-b.log` | 6 |
| BlockConditionalScoreGradient | `/tmp/ym-original-conditional-score-gradient-20261003-b.log` | 5 |

27 public gates, 21 added. All dependencies lie within {propext, Quot.sound};
accepted logs have no errors or warnings. Initial failed elaboration logs
are not acceptance evidence. No sorry, admit, Classical, native_decide,
noncomputable, custom axiom or raised resource budget was added. These are
focused source checks, NOT a full-library build or axiom audit.

Checked-source SHA-256 values, in target order:

    29077129378f9a936b15a4248b3654fc56d970c2391b361e47098d05553743da
    883fab54ab88feed09527b5074997ce819b88546625b9c5f403844d54685d998
    c24f85d2a18d43246e6740ff24e67d18385fd0f6ece003ca50f9f997cc217b2f
    e69ed1e28ec4e6b00dd0e536266284be932499e4c47e321239f3b0e91e4b9a97
    15a832df9921f425f33039de2c9a526620257b055ad3aa4c0b4abef10e8f6022

Independent bounded Sol/Luna source review found no algebra/sign defect and
confirmed that the projected-weighted noise/surviving-norm obligation remains
unpaid. Verification builds were serialized by the root agent.
