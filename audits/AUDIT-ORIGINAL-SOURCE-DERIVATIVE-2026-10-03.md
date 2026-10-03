# Original source derivatives replace the heat-score cap

Whole-project goal: constructive, Mathlib-free continuum Yang--Mills on R^4
for every compact simple group, with nontrivial SAME-theory QFT, isolated
vacuum and finite positive physical Hamiltonian mass gap. Clay remains OPEN.

## Mathematical argument

Keep the original finite SU(2) spatial action V, kinetic kernel K(x,y),
transfer T and Haar carrier. Write I for input-head Haar integration, H for
output Haar integration, and ell(f)=H[V*f]. For each quaternion angular
direction D, simultaneous endpoint rotation gives

    (D_x+D_y)K = 0  in the original Haar carrier.

Input Haar integration by parts and source support therefore give

    D_y I[K*p] = I[K*D_x p]

under EVERY surviving Haar insertion. This is not equality in the free
coefficient polynomial ring; it is exactly the carrier equality needed to
transport square certificates. No positivity, cutoff guard, kernel floor,
derivative cap, or inverse enters this identity.

For actual supported signed inputs a,c, put A=T a and b=T c. Define

    S=A*Db-b*DA,
    X=lift(A)*c-lift(b)*a,
    Y=lift(A)*D(V*c)-lift(b)*D(V*a).

The source derivatives are complete and remain unsplit in the square.
Their exact coefficient expansion is

    Y=V*(lift(A)*Dc-lift(b)*Da)+(DV)*X.

The original angular commutation then identifies S with I[K*Y] in the
original output Haar carrier. The constructed conditional determinant
certificate for positive K supplies

    (I K)*I[K*Y^2] - S^2 >= 0.

No positivity or inverse of a,c,A,b is assumed here. Kinetic mass I K is
retained, not canceled. Every certified output weight W and supported
multiplier J consequently give

    H[W*(J*S)^2] <= H[(W*J^2)*(I K)*I[K*Y^2]].

This alternative has no relativeCap(w,32)^2 factor in its leading term.
It is NOT proved numerically smaller than the previous cap-based estimate.
Nome dependence remains in K,V,the messages and their derivatives.

## Forward estimate meets the backward SAME-cost consumer

Instantiate the actual incoming messages

    a=g_(n+r), c=T^r(g_n*psi), A=g_(n+r+1), b=T c,
    phi_k=G_k*b, Vbar=P_fringe V,
    Z0=ell(A^2), Z1=ell(A*T A), B=ell(b^2).

Let SourceAngular_k be the sum over all active links and six angular planes
of twice H[Vbar^2*G_k^2*(I K)*I[K*Y^2]]. Both Vbar^2 and G_k^2 remain
literal. Inactive terms vanish by the actual post-transfer fringe
independence, not by removing fringe states from the original completion.
The previously constructed same-norm correction payment gives

    weightedAngularEnergy(q,phi_(k+1)) <= SourceAngular_(k+1)+eta*B,
    q=P_fringe(V*A)=Vbar*A.

The exact ORIGINAL energy Taylor identity retains BOTH signed remainders:

    SourceBulk_k = Z0*((1-w)*SourceAngular_k+Rmixed_k-Rdiagonal_k).

The actual partition comparison and existing correction, boundary-drift
and complete-reconstruction moduli then prove

    clearedRayleighCost(A,b)
      <= SourceBulk_(k+1)+((zeta+delta)+epsilon)*Z1*B.

The correction onset is required at predecessor degree k; reconstruction
is required at k+1; drift has its independent terminal-depth onset. All
three computed onsets depend only on FIXED nome,width and tolerances, not
K,the signed source or incoming depths. Zero B is included without a norm
inverse. Their existing fixed-parameter caps/floors remain in the onsets;
the new identity does not make those moduli spacing- or nome-uniform.

The SAME cleared cost is the one normalized by `originalOwnBlockCost`
(`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:98`)
and joined to the existing completed response by
`originalOwnBlockCost_converges` (same file:157). Those are fixed-parameter
joins, not a changing-family limit interchange. No comparison with an
unrelated dynamics or replacement carrier is asserted. No new structure
assumes the missing relative bound.

## Declaration map

| Result | Declaration and source |
|---|---|
| Kernel derivative moved to complete source | `productMap_angular_carrier`, `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularCommutation.lean:59` |
| Unsplit source derivative | `lastStepSourceDerivative`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:65` |
| Actual conditional square budget | `lastStepSourceDerivativeBudget`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:73` |
| Exact action/source expansion | `lastStepSourceDerivative_expansion`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:80` |
| Every-insertion score identity | `lastStep_sourceDerivative_carrier`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:159` |
| Constructed determinant certificate | `lastStep_sourceDerivative_certificate`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:177` |
| Weighted square bound | `lastStep_sourceDerivative_weighted_multiplier_square_le`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:210` |
| Finite reciprocal-gradient consumer | `lastStep_sourceDerivative_reciprocal_gradient_square_le`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:239` |
| Complete active/six-plane budget | `sourceDerivativeAngularBudget`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivativeEnergy.lean:82` |
| Actual angular energy with paid correction | `original_block_sourceDerivative_angular_le`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivativeEnergy.lean:153` |
| Both signed Taylor remainders retained | `sourceDerivativeSignedBulk`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivativeEnergy.lean:227` |
| ORIGINAL energy with relative correction payment | `original_block_sourceDerivative_energy_le`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivativeEnergy.lean:241` |
| Complete SAME-cost join | `original_block_sourceDerivative_cost_relative_tolerance`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivativeEnergy.lean:316` |

Four existing scalar proofs are exposed unchanged for reuse, with axiom
prints: `six_error` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepCorrectionPaidBudget.lean:77`,
`sum_error` in that file:99 and `plane_payment` in that file:121; and
`correctionBulkTolerance_payment` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost.lean:137`. Their exposure
is not new mathematics; the source-derivative estimate above is.

## Repointed analytic residue

The useful combined SourceBulk/(Z1*B) bound on the literal OWN-centered
growing-square source and a justified changing family remains OPEN. The
leading derivatives may now be studied on the actual incoming source,
without a global kernel-score cap, but their action-specific comparison
with the surviving norm has NOT been supplied. Keep the DV*X term and
both signed Taylor remainders together; no favorable total sign follows
from positivity alone. The existing
`SU2QuaternionAngularOnlyEnergyFence.angular_only_energy_bound_false`
(`lean/YMGap/Continuum/SU2QuaternionAngularOnlyEnergyFence.lean:81`)
already rules out that generic shortcut; this increment does not recheck
or claim a new counterexample.

Physical scaling, nontrivial continuum survival, full QFT axioms, every
compact simple group and the Clay theorem remain OPEN. No canonical
frontier field or exact displayed chart claim changes; no ASCII reprint.

## Verification boundary

Five serialized focused source checks passed, with all 34 printed gates
within {propext, Quot.sound}, including unchanged prerequisite/helper gates:

| Checked module | Accepted log | Gates |
|---|---|---:|
| `SU2QuaternionProductHeatAngularCommutation` | `/tmp/ym-product-angular-commutation-20261003-4.log` | 1 |
| `BF4ExactSlabFixedSpatialLastStepCorrectionPaidBudget` | `/tmp/ym-correction-paid-budget-helpers-20261003-1.log` | 9 |
| `BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost` | `/tmp/ym-correction-paid-cost-helper-20261003-1.log` | 12 |
| `BF4ExactSlabFixedSpatialLastStepSourceDerivative` | `/tmp/ym-last-step-source-derivative-20261003-2.log` | 7 |
| `BF4ExactSlabFixedSpatialLastStepSourceDerivativeEnergy` | `/tmp/ym-last-step-source-derivative-energy-20261003-3.log` | 5 |

Every launch used the monitored session-locked procedure with one worker,
20 GiB worker ceiling and 12 GiB OS reserve. Dynamic preflight found no
competing Lean/runner/test process, zero swap and 75--76% free memory.
No resource ceilings or heartbeat limits were raised. Independent Sol
mathematical review passed; Luna source/log QA is recorded with this
increment. No `sorry` is added or discharged; no new axiom, classical
shortcut or canonical-field weakening. Root imports are registration-only;
no aggregate build, audit or broad guard is claimed. CI remains off.

New checked source SHA256:

- Commutation: `5ad1de2c33eba70c9483ebc5a44805c222e9edbed5feaf3004e7102dfa329be1`
- Source derivative: `9a7d78903bb8cc2eea60d537f42e8d3132c36e9184d87e39b531ec51f465d8b8`
- Energy/cost consumer: `058ad16474fe7690242e681569e300ad83e96de96ca653d62df0b0ce3cfcd8ea`
