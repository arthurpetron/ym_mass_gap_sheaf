# Original three-column Gram certificate and complete signed-cost join

Whole-project goal: constructive, Mathlib-free continuum Yang--Mills on R^4
for every compact simple group, with nontrivial SAME-theory QFT, isolated
vacuum and finite positive physical Hamiltonian mass gap. Clay remains OPEN.

## Mathematical result

Use the complete ORIGINAL step W=K*V and its head integral I, retaining
the common output variables. For arbitrary supported signed a,c, set

    M=I(W), A=I(Wa), b=I(Wc),
    U=I(Wa^2), H=I(Wc^2), C=I(Wac),
    Gram=U*H-C^2, J=A^2*H-2*A*b*C+U*b^2.

The three-column determinant is

    M*Gram-J = M*U*H+2*A*b*C-A^2*H-U*b^2-M*C^2.

Three independent head copies, with the SAME surviving tail, carry the
six-term antisymmetric wedge of columns (a,c,1). Integrating its square
against all three copies of W gives exactly SIX times that determinant.
The constructed certificate scales by the closed rational 1/6 only.
No conditional mass, source, U, Gram or surviving norm is inverted.
Only W requires positivity; a and c may be signed, and zero heads/tail
are included. This is finite Gram positivity, not a strict contraction.

The original transfer pins these moments to T=P_w M_V. With M=T1 and
the EXISTING scoreBudget=M*J, multiplication by the constructed M
certificate yields

    Certificate [M^2*Gram-scoreBudget].

Consequently every certified SAME output weight R and supported square
multiplier G gives

    Haar[R*G^2*scoreBudget] <= Haar[R*G^2*M^2*Gram].

IMPORTANT: the new ceiling is LARGER than the original paired budget.
Its excess is M times the nonnegative three-column determinant. It is an
alternative analysis input that absorbs the mean mismatch with the correct
factor, not an improved numerical estimate. The original paired budget
and the checked regression/mismatch diagnostic remain available.

## Declaration map

| Constructed step | Declaration and source |
|---|---|
| Original six-moment determinant expansion | `threeGramDifference_expansion`, `lean/YMGap/Continuum/SU2QuaternionMultiHeadThreeGram.lean:58` |
| Three shared-tail ordered head copies | `tripleTensor`, `lean/YMGap/Continuum/SU2QuaternionMultiHeadThreeGram.lean:89`; `triple_product_pin`, same file :108 |
| Literal six-permutation wedge and full W product | `threeGramWedge`, `lean/YMGap/Continuum/SU2QuaternionMultiHeadThreeGram.lean:165`; `threeGramReplica`, same file :168 |
| Exact integral equals six times determinant | `threeGramReplica_identity`, `lean/YMGap/Continuum/SU2QuaternionMultiHeadThreeGram.lean:322` |
| Positive replica and integrated determinant witnesses | `threeGramReplica_certificate`, `lean/YMGap/Continuum/SU2QuaternionMultiHeadThreeGram.lean:393`; `conditionalThreeGram_certificate`, same file :433 |
| Actual original M-squared Gram budget | `lastStepThreeGramBudget`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepThreeGramBound.lean:54` |
| Actual budget difference certificate | `lastStepThreeGramBudget_certificate`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepThreeGramBound.lean:73` |
| Every output weight/square insertion | `lastStep_threeGram_weighted_multiplier_le`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepThreeGramBound.lean:146` |
| Original score and finite reciprocal derivative consumers | `lastStep_score_threeGram_weighted_multiplier_square_le`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepThreeGramBound.lean:173`; `lastStep_reciprocal_threeGram_gradient_square_le`, same file :193 |
| Full active-link/six-plane alternative | `originalBlockThreeGramAngularBudget`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepThreeGramCost.lean:58` |
| Correct comparison direction, old budget <= alternative | `originalBlockLastStepAngularBudget_le_threeGram`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepThreeGramCost.lean:89` |
| Actual full angular-energy consumer | `original_block_threeGram_weightedAngularEnergy_le`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepThreeGramCost.lean:116` |
| Original signed bulk, with both Taylor remainders | `originalBlockThreeGramBulkBudget`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepThreeGramCost.lean:131` |
| Same bulk comparison and complete cost join | `originalBlockLastStepBulkBudget_le_threeGram`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepThreeGramCost.lean:145`; `original_block_threeGram_cost_relative_tolerance`, same file :161 |

The original-action transport uses `transferStep_kernelMap`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferBound.lean:76`,
and `lastStepPairedResidual_square_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepScoreVariance.lean:169`.
The positive M producer is `transferStep_certificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferOrder.lean:39`.
No private half-open action is replaced by an auxiliary probability law.

## Complete SAME-cost consumer

The actual input pair is a=g_(n+r), c=T^r(g_n*psi), outgoing A=T a,
b=T c. The full projected angular alternative retains Vbar^2*G_k^2*M^2
inside the original Haar insertion and retains the finite reciprocal
correction separately. Every active link and all six planes are summed;
the existing original-energy theorem supplies the exact inactive zeros.

Set Z0=ell(A^2), Z1=ell(A*T A), B=ell(b^2). The complete consumer is

    D <= ThreeGramBulk_k + delta*Z1*B + epsilon*Z1*B,
    ThreeGramBulk_k = Z0*((1-w)*ThreeGramAngularBudget
                              + Rmixed-Rdiagonal).

The distinct computed depth/degree onsets are EXACTLY the existing
`blockConditionalDriftDepthCutoff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalDrift.lean:152`,
and `blockEnergyRelativeErrorCutoff`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.lean:217`.
The consumer composes `original_block_lastStep_driftPaid_cost_relative_tolerance`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepDriftPaidCost.lean:124`.
Both signed Taylor remainders, both partitions, the original source and
center, the SAME original transfer and the separate error payments survive.

## Backward residue and parameter honesty

The useful signed bulk estimate against Z1*B on the literal OWN-centered
growing square and a justified changing family remains OPEN. No useful
M^2*Gram/B estimate is constructed or assumed here. Positivity alone does
not discharge that input; the available budget comparison goes upward.

The existing actual numerator and denominator limits are
`originalOwnBlockCost_converges`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:157`,
and `originalOwnBlockVariance_converges`, same file :136. These are
fixed-parameter SAME-source joins, not changing-family estimates.
`originalOwnBlock_budget_rate_constraint`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredRateConstraint.lean:131`,
is a NECESSARY constraint on a supplied finite budget, not its producer.

The new determinant identity's constants 6 and 1/6 are fixed algebraic
constants; no coupling-uniform positive gap follows. The original angular
consumer still uses the explicitly nome-dependent `relativeCap(w,32)` and
late `relativeCutoff(w,32)` in
`lean/YMGap/Continuum/QuaternionHaarHeatRelativeAngularBound.lean:41` / :46.
The two error onsets depend on fixed nome,width and tolerance, not the
source or heat cutoff. They are NOT spacing/nome/width-uniform moduli on a
scaling family. No physical time or mass calibration is supplied.
Full same-theory OS/QFT passage, nontrivial continuum survival, finite
positive physical mass and every compact simple group remain OPEN.
No canonical field or exact displayed chart claim changes state.

## Verification boundary

Three focused serialized checks passed, with one worker, a 20 GiB hard
per-worker ceiling and 12 GiB OS reserve. Dynamic process/memory preflight
ran before each launch, with no competing build, no swap and 76--77 percent
system-wide free memory. Accepted logs report SEVENTEEN public gates, all
within {propext, Quot.sound}, with no errors or warnings:

| Module | Accepted focused log | Gates |
|---|---|---|
| SU2QuaternionMultiHeadThreeGram | `/tmp/ym-three-column-gram-20261003-c.log` | 6 |
| BF4ExactSlabFixedSpatialLastStepThreeGramBound | `/tmp/ym-last-step-three-gram-bound-20261003-a.log` | 5 |
| BF4ExactSlabFixedSpatialLastStepThreeGramCost | `/tmp/ym-last-step-three-gram-cost-20261003-a.log` | 6 |

Source SHA-256, respectively:

- `b5a28b024f0a77b8d3fe890e240cc584d16bfce3e72c51c9c437294cecdd1f3f`
- `2d9d46d87c1df712b27dbe140051472a4941fe88ce8f2d03bf1e330bfbe8ce15`
- `4dd41bbaffccf5d782f301acf8f666d276aae98a3c7659ed90fb7bc2394e02f6`

Independent Sol mathematical review passed the six permutation signs,
factor six, shared-tail retention, actual transfer pins, larger-ceiling
direction and complete signed-cost join. Independent Luna source/log QA
passed all three current hashes and the 6+5+6 accepted gates, with no
forbidden dependencies or error/warning markers. Final Luna audit/docs
review also passed the live declaration/cutoff citations, scope wording
and unchanged canonical ASCII fence (byte-identical to HEAD).
The generic leaf's first two
failed checks are NOT accepted evidence. The final contraction keeps
literal empty-polynomial zero sentinels and locally opaque polynomial
operations; a scoped two-million-heartbeat budget is retained for the finite
36-term identity. No machine memory ceiling or worker count was raised.

No sorry/admit, new axiom, Classical, native_decide, noncomputable,
analytic hypothesis, frontier weakening, exception or ledger closure was
added. Root imports are registration only. Full-root/full-tree build,
audit, guard, progress sweep and literature fetch were NOT run. The
canonical ASCII block is unchanged and is not reprinted.
