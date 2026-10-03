# Original reciprocal correction paid by the SAME surviving norm

Whole-project goal: constructive, Mathlib-free continuum Yang--Mills on R^4
for every compact simple group, with nontrivial SAME-theory QFT, isolated
vacuum and finite positive physical Hamiltonian mass gap. Clay remains OPEN.

## New estimate, not an assumed bound

Keep the original SU(2) finite spatial action, transfer T, terminal messages
and Haar carrier. Write ell(f)=H[V*f],

    a=g_(n+r), c=T^r(g_n*psi), A=T a, b=T c,
    Vbar=P_fringe V, u=kineticCap*ell(a), R=A/u-1,
    L=relativeCap(w,32), rho=mixRate(w,width),
    Z0=ell(A^2), Z1=ell(A*T A), B=ell(b^2).

The existing constructed terminal relative cone supplies -L*A<=DA<=L*A.
The certified upper window A<=u gives the following two cone witnesses:

    L - (1/u)*DA = L*(-R) + (1/u)*(L*A-DA),
    L + (1/u)*DA = L*(-R) + (1/u)*(L*A+DA).

Both summands have actual original-carrier certificates. Thus |DR|<=L is
constructed, with no lower bound or inverse of the terminal polynomial A.
The exact ORIGINAL correction is

    e_(k+1)=(k+1)*(-R)^k*b*DR.

For every certified same-carrier weight W this gives

    H[W*e_(k+1)^2] <= (k+1)^2*rho^(2*k)*L^2*H[W*b^2].

For the actual W=Vbar^2, projection preserves the original spatial
positivity/cap certificates, so Vbar*(spatialCeiling-Vbar) is certified.
After at least one original transfer, b is fringe-independent. The exact
Haar projection pin then yields H[Vbar*b^2]=ell(b^2). Consequently

    H[Vbar^2*b^2] <= spatialCeiling(w,width)*B,
    H[Vbar^2*e_(k+1)^2]
       <= (k+1)^2*rho^(2*k)*lastStepRelativeCorrectionCap(w,width)*B.

This is a genuine comparison, NOT the false equality Vbar^2=V. The cap is
L^2*spatialCeiling, with nome and width explicit; K,n,r,psi and B do not
enter the computed polynomial-geometric onset. Signed sources and B=0
are included by nonnegative multiplication, without a norm inverse.

## Complete angular and signed-cost consumer

All six planes on every active link are paid, including both copies of the
correction from sumBound. Allocation epsilon/(1+12*N), N=baseLinks.length,
gives

    LastStepAngularBudget_(k+1)
      <= PairedAngularBudget_(k+1) + epsilon*B.

PairedAngularBudget retains the literal G_(k+1)^2, Vbar^2 and
lastStepScoreBudget=T1*I(W_original*X^2),
X=lift(A)*c-lift(b)*a. Only the reciprocal correction is removed from
the analytic leading budget. Exact inactive angular zeros remain supplied
by the existing full-energy consumer.

The already checked original partition estimate Z0*C_transfer<=kappa*Z1,
and C_transfer>=kineticCap*spatialFloor, construct

    Z0 <= P*Z1, P=kappa/(kineticCap*spatialFloor).

Only this explicitly positive FIXED-parameter scalar floor is inverted;
neither a terminal mass, source norm nor either partition is inverted in
this payment. Allocating zeta/[1+(1-w)*P] in the angular bound pays its
complete signed-cost contribution by zeta*Z1*B. Define the remaining bulk
without changing its signed terms:

    PairedBulk_k = Z0*((1-w)*PairedAngularBudget_k+Rmixed_k-Rdiagonal_k).

Compose with the existing drift/reconstruction payments to obtain

    D <= PairedBulk_(k+1) + ((zeta+delta)+epsilon)*Z1*B.

Correction onset is <=k, reconstruction onset is <=k+1, and drift uses
depth n+(r+1)-1. Each onset is computed from fixed nome,width and its
tolerance only. No cutoff, source amplitude, source degree or incoming
depth enters these moduli. No changing-family uniformity is asserted.

## Declaration map

| Step | Declaration and source |
|---|---|
| Constructed reciprocal derivative interval | `remainderAngularInterval`, `lean/YMGap/Continuum/QuaternionHaarRelativeReciprocalCorrection.lean:51` |
| Every SAME certified output weight | `reciprocalScoreCorrection_relative_square_le`, same file :90 |
| Genuine projected spatial square comparison | `spatialFringeMass_square_weight_le`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepRelativeCorrection.lean:63` |
| Source-free fixed-parameter coefficient | `lastStepRelativeCorrectionCap`, same file :105 |
| Actual original-action per-plane estimate | `original_block_lastStep_correction_relative_square_le`, same file :116 |
| Computed actual all-later onset | `lastStepRelativeCorrectionCutoff`, same file :178; `original_block_lastStep_correction_relative_tolerance`, same file :184 |
| Actual post-transfer fringe independence | `block_source_fringe_independent`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalGradient.lean:255` |
| Literal remaining paired angular budget | `originalBlockLastStepPairedAngularBudget`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepCorrectionPaidBudget.lean:52` |
| All-active/six-plane payment and actual energy | `original_block_lastStep_angularBudget_correction_paid`, same file :149; `original_block_lastStep_weightedAngularEnergy_correction_paid`, same file :216 |
| Actual Z0/Z1 fixed-parameter comparison | `original_block_partition_relative_le`, `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost.lean:81` |
| Literal remaining signed bulk | `originalBlockLastStepPairedBulkBudget`, same file :164 |
| Original complete correction payment | `original_block_lastStep_bulk_correction_paid`, same file :177 |
| Complete signed cost with three explicit payments | `original_block_lastStep_correctionPaid_cost_relative_tolerance`, same file :245 |

The terminal derivative producer is `terminalMessageRelativeBound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalJacobiAngularBound.lean:66`.
The original window and exact mass cancellation are `blockWindowCertificates`
and `blockWindow_radius_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:103`
and :250. The polynomial-geometric scalar estimate and weighted-multiplier
estimate were exposed from the existing proofs in
`QuaternionHaarReciprocalScoreCorrection.lean`; their proofs were not changed.

## Remaining causal frontier

The genuinely missing producer is a useful bound on the COMBINED signed
PairedBulk against Z1*B on the literal chronological OWN-centered growing
square and a justified changing family. Its scale-normalized O(1/side)
budget must retain the paired residual's negative cross term and both signed
Taylor remainders. Separate absolute caps do not supply that estimate.
No extra correction/norm hypothesis is needed after this increment.

The backward SAME completed response consumer already has the exact
original variance/cost limit pins `originalOwnBlockVariance_converges` and
`originalOwnBlockCost_converges`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:136`
and :157. The new estimate does NOT supply the family-relative leading bulk,
its macroscopic reserve/ratio, a justified RG family, scaling-surviving
nonzero excitation, positive finite physical mass, full QFT axioms, or an
every-compact-simple-group construction. There is no new continuum theorem.

Fixed-parameter approximation constants can deteriorate with width or w->1.
These are approximation payments, NOT a uniform spectral rate. No canonical
frontier field or exact displayed diagram claim changes. The canonical ASCII
fence is unchanged and is not reprinted.

## Focused verification and independent review

Six final source checks completed using `scripts/safe_lean_build.py`, one
serialized worker, 20-GiB hard limit, 12-GiB OS reserve and fresh live resource
checks before each launch. All checks finished in their initial tool calls;
no long-running job or broad root build/audit was launched.

| Checked target | Accepted log | Printed gates |
|---|---|---:|
| `QuaternionHaarReciprocalScoreCorrection.lean` | `/tmp/ym-relative-correction-base-20261003-1.log` | 7 |
| `BF4ExactSlabFixedSpatialBlockConditionalGradient.lean` | `/tmp/ym-block-fringe-independent-20261003-1.log` | 6 |
| `QuaternionHaarRelativeReciprocalCorrection.lean` | `/tmp/ym-relative-reciprocal-20261003-3.log` | 2 |
| `BF4ExactSlabFixedSpatialLastStepRelativeCorrection.lean` | `/tmp/ym-last-step-relative-correction-20261003-3.log` | 6 |
| `BF4ExactSlabFixedSpatialLastStepCorrectionPaidBudget.lean` | `/tmp/ym-last-step-correction-paid-budget-20261003-3.log` | 6 |
| `BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost.lean` | `/tmp/ym-last-step-correction-paid-cost-20261003-4.log` | 11 |

All 38 printed outputs are within {propext, Quot.sound}; two definitions
are axiom-free. No new sorry, admit, Classical, choice, custom axiom,
native_decide, unsafe or noncomputable declaration is introduced. No
heartbeat increase is introduced. Root import additions are source wiring,
not a claim that the enormous full root was rebuilt or audited.

Sol independently reviewed the actual original action, projected-weight
comparison, partition payment, signs, zero norms and successor-degree
bookkeeping. Luna independently reviewed the frozen source/log pairs and
proof-status scope. Their reviews do not replace the focused kernel checks.

Frozen SHA-256 source hashes:

| Module basename | SHA-256 |
|---|---|
| `QuaternionHaarReciprocalScoreCorrection` | `28db0220d41693f9c496b4c59c3a51d23c380b4dc726e5360922c070a7d32b53` |
| `BF4ExactSlabFixedSpatialBlockConditionalGradient` | `6f581cb514f0a75d6afbf2770be4ad898c6228c94e62df3fd6d0711bab248a19` |
| `QuaternionHaarRelativeReciprocalCorrection` | `ab8aced132c5b4db3d00ab1200a1039c937d249eca354a94aa9fca7aadf6ff4f` |
| `BF4ExactSlabFixedSpatialLastStepRelativeCorrection` | `d0f2ba9173c69bb2d282c650e4bf17be56c0f5cc855b5f17029726360c880964` |
| `BF4ExactSlabFixedSpatialLastStepCorrectionPaidBudget` | `3d7e571ec68f995ace3180c9a4bc4064210d08b720ba5f4626b03ac0fd4cc0ef` |
| `BF4ExactSlabFixedSpatialLastStepCorrectionPaidCost` | `72a8a7f33e7cc14e0b22d541459eb9417b66efaeb725c2d20b813822d22ebc94` |
