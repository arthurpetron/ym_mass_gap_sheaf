# Original quadratic commutator gain and its SAME completed carrier

The complete signed filtered source now has an exact quadratic route.
Its endpoint mismatch and actual lag-one comparison have explicit
decaying bounds. A constructed real gain is pinned to the existing
completed state, time operator and unit normalization. No useful gain
bound or positive changing-family reserve is proved.
The actual normalized finite gain reaches that SAME completed gain
with explicit independent cutoff/time/representative thresholds.

## Original finite identity

Keep the original terminal message g, transfer T and spatial functional
ell. Write A=Tg, psi=f-c, b=T(g*psi) and E=ell(A^2), where f is the
fundamental closed Wilson-word trace. The arbitrary rational reference
a is NOT an asserted eigenvalue of the centered source. Define

    J1 = ell(A*psi*b)
    G2 = ell[b*(b-a*A*psi)]
    Delta = ell[A*T(g*psi^2)]-ell[(A*psi)^2].

`centeredMessage_pin`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredCommutatorGain.lean:132`,
pins b to T(g*f)-c*Tg, not to a centered eigenmode.
`filtered_loop_commutator_identity` at line 200 proves for arbitrary c,a

    complete original filtered numerator S = Delta+2*(1-a)*J1-2*G2.

This is the literal radius-two filtered source, with all original
spatial, terminal and kinetic factors retained. E is its EVEN partition;
there is no replacement by finite oddMass or marginal variance.

## Controlled finite endpoints

For the actual original finite OWN odd mean c,
`ownCenteredBound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredCommutatorGain.lean:288`,
constructs a square-bound certificate with cap16.
`endpointSquareDifference_interval` at line 347 constructs cap16 for
psi_lower^2-psi_upper^2, not cap32: both squares are nonnegative and
bounded by16. Matched endpoint symmetry makes this insertion zero at
window(n,1,n). The original common-tail comparison to window(n,1,n+1)
and its actual partition give

    abs(Delta) <= 32*mixRate^n*E.

This is `endpointMismatch_bound` at line 443. Endpoint symmetry is not
a finite odd/even stationarity claim. Strict nome 0<w<1 and the actual
headCutoff guard are explicit. mixRate and the required depth depend on
nome and spatial width; this is not a uniform physical scaling bound.

`centeredProduct_interval` at line 332 constructs cap16 for the endpoint
PRODUCT. `centeredTransferCross_window_pin` at line 533 pins J1/E to
the actual mixed window. `centeredTransferCross_commonTail` at line 574
compares it in BOTH directions to the existing matched normalized
centered transfer quadratic, with error32*mixRate^n. The finite OWN mean
is transported by proved mean/marginal pins. This matched quadratic is
the lag-one centered pairing C1, NOT the ambient variance C0.

## Constructed completed gain

`gainLimit`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredGainLimit.lean:51`,
constructs the real (1-a)*transferLimit-half*filteredIncrement, using
the existing original limits. `gainLimitCauchy` at line 63 supplies its
computed approximation modulus from their original joint moduli and
constructive scalar arithmetic.

`gainLimit_centered_pin` at line 100 identifies this real with C2-a*C1.
`gainLimit_completed_pin` at line 131 pins its quotient to the EXISTING
centered vector paired with completedTime2 minus a times completedTime1.
`dyadicUnit_gain_pin` at line 144 uses the existing normalizer TWICE and
pins the result exactly to R2-a*R1 for that SAME unit excitation. No new
inverse, carrier or state is introduced. These completed pins are
algebraic; the actual finite-to-limit join is proved below.

## Actual finite gain approximation

`normalizedFiniteGain`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredFiniteGainApproximation.lean:56`,
divides the original G2 by its SAME evenPartition, at the original
headCutoff-plus-stage cutoff and moving finite OWN mean.
`normalizedFiniteGain_identity` at line 87 retains the COMPLETE literal
radius-two finite scalar F and proves for arbitrary a

    G2/E = (1-a)*(J1/E)-half*F+half*(Delta/E).

`normalizedFiniteMismatch_bounds` at line 123 controls both signs of
Delta/E by 32*mixRate^n. `normalizedFiniteGain_bracket` at line 162 gives,
for 0<=a<=1, both-order error48*mixRate^n against

    (1-a)*finiteScalar(loop at time0)-half*F.

finiteScalar is the EXISTING matched centered transfer quadratic. Its
comparison uses the exact same loop/source, OWN center and partitions;
there is no supplied limit or desired gain bound as a new hypothesis.
The coefficient48 is32 plus half*32, not an untracked relative constant.
This bound remains fixed-nome/width, with explicit parameter-dependent
mixRate. The following module supplies its completed-gain modulus.

## Explicit finite-to-completed join

`gainTolerance`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredFiniteGainLimit.lean:39`,
is epsilon/4. `gainCutoffThreshold` at line 53 takes the maximum of the
existing centered-transfer and COMPLETE filtered joint cutoff thresholds.
`gainTimeThreshold` at line 59 takes their time-threshold maximum and
the computed geometricCutoff(mixRate,48,epsilon/4).
`gainRepresentativeThreshold` at line 65 takes the maximum of the two
EXISTING limits' representative thresholds. All three are data.

`normalizedFiniteGain_approx` at line 111 proves, for epsilon>0 and
0<=a<=1, BOTH approximation orders between the actual G2/E at independent
late cutoff/time indices and gainLimit.approx at every late representative.
Each of the two original scalar limits pays at most epsilon/4 after its
coefficient in[0,1]; the boundary error pays epsilon/4. Thus the total
is at most 3*epsilon/4<=epsilon. No source convergence or gain estimate
is supplied as a premise.

The moving finite OWN mean remains inside the actual computed gain.
Its exact comparison to the FIXED original source limits is used before
limit passage; no changing observable is passed through a fixed-source
convergence theorem. Nome and width remain fixed. This is a genuine
same-object finite-to-completed join, NOT physical scaling control.

## Backward consumer and open analytic input

The existing theorem `dyadicUnitResponse_filtered_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:154`,
needs R1>=gamma0 and m*(R1-R2)<=C*R1, with Nat C>=1 and m>=4*C.
It gives Rm>=gamma0*(1/4)^(2*C). Its premises are still missing on
a justified changing family with fixed C and positive gamma0.

The checked gain identity expresses the budget, algebraically, as
m*(R2-a*R1)>=[m*(1-a)-C]*R1. This report records the needed bound,
not a new theorem supplying it. No favorable sign is assigned to G2.
The reference coefficient may be chosen from existing heat data without
claiming that the interacting centered source is a free eigenfunction.

The earlier signed cross and complete OWN Young ceilings remain valid
alternative estimates. Their length-dependent absolute costs do not
automatically supply this relative gain or reserve. Spatial/spacing
control, nontrivial continuum survival, physical mass calibration, full
same-theory QFT, every compact simple group and Clay remain OPEN.

## Verification boundary

### Analytical review: positivity is not the missing gain estimate

This is SOURCE/ANALYTICAL REVIEW ONLY, not a newly Lean-checked witness
and not a counterexample to the literal BF4 terminal source. In the
one-link original SU(2) model with spatial weight 1, take f=chi1 and
g=1+t*chi1, 0<t<1/2. At K>=max(2,headCutoff w), set
r=w^3, s=w^8, D=1+t^2*r. Then A=Tg=1+t*r*chi1, the SAME odd
mean is c=t*(1+r)/D and the even partition is 1+t^2*r^2>0.
Both g and A are positive; g even has nonnegative character coefficients.
Direct character arithmetic, at reference a=r, gives

    G2 = -t^2*r^2*(1-t^4)*(1-r^2)/D^2 + t^2*s*(s-r^2) < 0.

The two terms are negative since 0<s<r^2<1. Root and parallel reviewer
independently checked this scalar expansion. The exact existing
ingredients are `first_character_square`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatPlaquetteSquare.lean:32`;
`harmonic_cross_degree`,
`lean/YMGap/Continuum/SU2QuaternionGroupedHarmonicNorm.lean:92`;
`endpoint_character` (private) and `endpoint_norm`,
`lean/YMGap/Continuum/SU2HeatQuarticSignedHaarObstruction.lean:198`
and line 250; and `harmonic_transmission_same_carrier`,
`lean/YMGap/Continuum/SU2QuaternionHarmonicHeatInsertion.lean:113`.
The assembled witness and its inequality are NOT declarations in this
increment. Do not replace the quantitative ORIGINAL-terminal-dependent
lower bound by generic positive-G2 or positive-character-cone reasoning.
The actual relative budget may allow negative gain and remains OPEN.

Four final focused checks exited zero: 15 finite, five completed,
six finite-approximation and six finite-limit public gates (32 total).
Dependencies are empty or
{propext,Quot.sound}. No accepted log contains errors, warnings or
sorryAx. Independent
mathematical review passed all four files, including their centering,
partitions, operators and normalization. Rejected preliminary logs are
not proof evidence; their repairs were narrow elaboration/namespace
fixes, without statement weakening or increased limits.

| Artifact | SHA256 |
| --- | --- |
| `BF4ExactSlabFixedSpatialFilteredCommutatorGain.lean` | `562bade2946bf8f42ac34b34693cae19c17254fe38154324413b3ad3fb291b4d` |
| `/tmp/ym-filtered-commutator-20261002-third.log` | `b04d59d87f13bcd293c7b2547685a4ef44883222d88c58c5f255846c88f6d1b0` |
| `BF4WilsonAllNomeFilteredGainLimit.lean` | `2e9264c0d4f1410236d79541883d848d5dad3fac3b1ec81b39a0a69210fb90e4` |
| `/tmp/ym-filtered-gain-limit-20261002-third.log` | `906364a94668ecb2f59df02b913ec4eec953cd66b68e6c82f6b10d57947dd189` |
| `BF4WilsonAllNomeFilteredFiniteGainApproximation.lean` | `c42c65e9b5a3da8159fccbb73df1be094943d53e559456ce1a0237b978b42d49` |
| `/tmp/ym-filtered-finite-gain-20261002-third.log` | `b6f6b92d9bb0bc1c83c9e11524c4474c3359d2608fc6ecc8efc2492e7442a76a` |
| `BF4WilsonAllNomeFilteredFiniteGainLimit.lean` | `d839d16fea8604cbbbbaa02747695514e06bd334057ed94074f45c5dc8b1d5fe` |
| `/tmp/ym-filtered-finite-gain-limit-20261002-second.log` | `1f915891819def8b66fc3990e01c44026e01ddde1fec29f457609bb02babcaca` |

Every launch had a fresh dynamic process/memory preflight, one worker,
a 20-GiB ceiling and a 12-GiB OS reserve. Root imports are registered,
NOT aggregate-checked. Root/tree, broad audit/guard and progress metric
were NOT run. No sorry, axiom, classical shortcut, analytic premise,
frontier-field weakening, surrogate source or CI change was introduced.
The documentation skill kept exact gain identities separate from the
open physical gain/reserve estimates. The exact canonical chart is
unchanged; no paper-list or ASCII reprint.
