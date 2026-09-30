# The original transfer gap reaches the existing witnessed series graph

Date: 2026-09-30 UTC. Classification: PROGRESS. Clay target remains OPEN.

## Short argument, actual objects

T is the existing all-nome completed Wilson one-step time operator. Its
constructed series is F=sum_(k>=1)(I-T)^k*T/k. The existing witnessed graph
has core pairs (T x,F x); neither an inverse of T nor a different carrier is
introduced here.

Write q for the existing two-step form rate, equivalently the one-step
squared-norm rate. On the original vacuum complement, positivity of
||x-Tx||^2 and ||Tx||^2<=q||x||^2 gives

    <x,(I-T)x> >= (1-q)/2 * ||x||^2.

All terms in the actual series paired with T x are nonnegative. Its first
term therefore gives

    <T x,F x> >= <T x,(I-T)T x> >= (1-q)/2 * ||T x||^2

when T x is vacuum-orthogonal. The margin is positive at each strict nome
and fixed width, but still depends on both parameters.

## Checked declarations

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `logPartial_time_firstTerm_le` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogRangePositive.lean:123` | First-term lower bound for every nonempty finite partial sum. |
| `regularizedLog_time_firstTerm_le` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogRangePositive.lean:161` | Same lower bound for the actual represented series limit. |
| `coreMargin`, `coreMargin_positive` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:52`, `:55` | Explicit positive rational margin (1-q)/2. |
| `completed_defect_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:101` | Strict one-step defect form on the existing vacuum complement. |
| `core_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:122` | The displayed strict bound on the actual graph core. |
| `regularizedLog_zero_iff_time_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:130` | F x=0 iff T x=0 for vacuum-orthogonal x. |
| `graph_input_time_kernel_eq_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:151` | A witnessed graph input in ker(T) is zero. |
| `graph_zero_output_iff` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:172` | On the vacuum complement, zero graph output iff zero input. |
| `action_zero_iff_input_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:186` | Same statement on the existing quotient graph domain. |
| `plaquette_regularizedLog_ne_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:196` | An actual active plaquette supplies a nonzero series output. |

For graph-kernel control, use `graph_time_pin` to get T(output)=F(input).
Zero output and vacuum orthogonality imply T(input)=0 by the new core result.
The graph's supplied approximants T(source_n) are then orthogonal to input.
Their explicit convergence modulus forces the input norm to vanish. This
does not assume a norm bound for the preimages source_n.

The original boundary time kernel remains present in the unchanged carrier.
The graph-input conclusion follows from a theorem about its approximants,
not a quotient that removes those states.

## Relation to the analytic frontier

This is an independent reconstruction join with already constructed inputs.
It does not replace the missing same-source relative temporal-energy UPPER
estimate needed by the scaling-survival branch. Source review found only
two-loop mixed upper bounds, not a useful whole-family scaling estimate.

The checked family temporal-energy LOWER floor also prevents a free
gradient-only cancellation argument at fixed nome: constant coefficients
have zero interior coefficient gradient but positive coefficient-square
budget. Any proposed estimate must retain appropriate zeroth-order/boundary
terms or prove source-specific variance amplification. No new Lean
asymptotic obstruction is claimed by this planning observation.

## Follow-on: exact margin on the entire witnessed graph

The next step is now proved, not an assumed continuity premise. For every
existing `GraphLimit` witness (x,y), its input images a_n=T(source_n) and
output images F(source_n) approximate x and y with the supplied modulus.
Distance-one control bounds ||a_n||^2 by 2+2*c when ||x||^2<=c. Time
contraction then permits ordinary pairing continuity for both B(a_n,a_n)
and B(a_n,T a_n). Together with the existing graph-pairing modulus this passes

    B(a_n,(I-T)a_n) <= B(a_n,F(source_n))

to B(x,(I-T)x)<=B(x,y). Neither bounded preimages nor their chosen Cauchy
representatives are required. Applying the already checked defect gap to x
gives the SAME full margin (1-q)/2 on every vacuum-orthogonal graph input.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `graphInputPairingModulus` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogGraphGap.lean:89` | Explicit all-tail input-pairing cutoff from the original graph modulus and supplied norm cap. |
| `graph_input_pairings_close` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogGraphGap.lean:96` | Both order errors for the norm and one-step pairing along graph input images. |
| `graph_defect_form_le` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogGraphGap.lean:133` | Universal defect-form lower bound on every existing witnessed graph pair. |
| `graph_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogGraphGap.lean:174` | Full original margin for vacuum-orthogonal graph input. |
| `action_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeLogGraphGap.lean:182` | Same quantitative bound on the existing quotient domain and action. |

## Follow-on construction: step back to positive coefficients

The direct polynomial iteration is now constructed on the ORIGINAL carrier.
Set D=I-T and define p_0(d)=0, p_(n+1)(d)=(d+p_n(d)^2)/2. Its coefficients
are nonnegative and increase coefficientwise. The mass m_n=p_n(1) obeys
m_(n+1)=(1+m_n^2)/2, with residual r_n=1-m_n satisfying

    r_(n+1)=r_n-r_n^2/2,     0<=r_n<=2/(n+2).

For m<=n, the difference polynomial p_n-p_m has nonnegative coefficients
and mass at most r_m. On the existing Wilson completion, mixed-moment
positivity and monotonicity give 0<=B(D^i x,D^j x)<=B(x,x). Bilinear
expansion therefore proves

    ||P(D)x||^2 <= P(1)^2 ||x||^2       (nonnegative coefficients),
    ||p_n(D)x-p_m(D)x||^2 <= r_m^2 ||x||^2.

This is NOT a sup-norm calculus for arbitrary signed polynomials. Signed
subtraction is performed exactly before its positive coefficient certificate
is applied. No group-dependent mass or lower spectral endpoint is inferred.
The relative convergence rate is independent of nome and width because it
uses only the proved original positive-contraction moments, not a gap.

Each finite row has an explicit original Cauchy representative. For a supplied
representative X with norm ceiling c, the absolute squared-distance Cauchy
modulus is max((4*c).num.toNat, epsilon.den). The existing diagonal limit
uses this at epsilon/16. Exact equality of finite actions makes the limit
independent of the presentation; no quotient representatives are selected.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `residual_tail_le` | `lean/YMGap/Continuum/ComplementRootMass.lean:219` | Explicit rational residual bound 2/(n+2). |
| `ordered_difference_nonnegative` | `lean/YMGap/Continuum/ComplementRootPolynomial.lean:97` | Coefficientwise positivity of p_n-p_m for m<=n. |
| `action_norm_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeDefectPolynomial.lean:145` | Squared coefficient-mass cap on the original completed norm. |
| `action_distance_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeDefectPolynomial.lean:193` | Same cap for an exactly retained positive polynomial difference. |
| `ordered_distance_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeRootIteration.lean:75` | Relative Cauchy bound for the actual original-carrier approximants. |
| `iterationModulus`, `iterationRows` | `lean/YMGap/Continuum/BF4WilsonAllNomeRootIteration.lean:115`, `:149` | Absolute outer modulus and explicitly represented original rows. |
| `complementLimit`, `complementLimitCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeRootIteration.lean:170`, `:189` | Same-carrier limit with a witnessing convergence modulus. |

The square equation and positivity that were left open at this checkpoint
are now proved by the follow-on below. Dyadic compatibility, strong continuity
and the existing log-series derivative remain separate requirements. This
positive-coefficient construction replaces the proposed port of a legacy
carrier's full calculus; it does not replace the primary missing
scaling-survival estimate.

## Follow-on: constructed positive square root of the SAME transfer

Let P_n=p_n(D) on the original completion and H=complementLimit.
Finite polynomial-action multiplication and symmetry give the exact identity

    B(P_n x,P_n y) = 2 B(x,P_(n+1) y) - B(x,Dy).

The existing represented pairing limits pass this recurrence to H. For
R=I-H, symmetry and cancellation then give B(Rx,Ry)=B(x,Ty). Definiteness
of the ORIGINAL pairing proves R^2=T. Positivity follows by passing the
finite bound B(x,P_n x)<=B(x,x) to H. The pairing identity gives contraction;
symmetry gives additivity and scalar compatibility. No composition-limit
theorem, inverse transfer, positive lower spectral endpoint, or choice of
representatives is assumed.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `action_pmul` | `lean/YMGap/Continuum/BF4WilsonAllNomeDefectPolynomialAlgebra.lean:163` | Exact composition of finite polynomial actions. |
| `action_symmetric`, `action_commutes_time` | `lean/YMGap/Continuum/BF4WilsonAllNomeDefectPolynomialAlgebra.lean:195`, `:209` | Original pairing symmetry and discrete-time compatibility. |
| `complementLimit_symmetric`, `complementLimit_form_le` | `lean/YMGap/Continuum/BF4WilsonAllNomeSquareRoot.lean:58`, `:69` | Symmetry and original-norm form ceiling for H. |
| `approximant_pairing_recurrence` | `lean/YMGap/Continuum/BF4WilsonAllNomeSquareRoot.lean:126` | Exact finite recurrence, tested on arbitrary original inputs. |
| `complementLimit_pairing_recurrence` | `lean/YMGap/Continuum/BF4WilsonAllNomeSquareRoot.lean:232` | Same recurrence after explicitly controlled pairing limits. |
| `squareRoot`, `squareRoot_nonnegative` | `lean/YMGap/Continuum/BF4WilsonAllNomeSquareRoot.lean:242`, `:249` | Actual positive operator R=I-H, not a supplied witness. |
| `squareRoot_pairing`, `squareRoot_square` | `lean/YMGap/Continuum/BF4WilsonAllNomeSquareRoot.lean:265`, `:274` | B(Rx,Ry)=B(x,Ty) and the SAME-object equation R^2=T. |
| `squareRoot_norm_bound`, `squareRoot_distance_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeSquareRoot.lean:279`, `:314` | Norm and squared-distance contraction. |
| `squareRoot_add`, `squareRoot_smul`, `squareRoot_realSmul` | `lean/YMGap/Continuum/BF4WilsonAllNomeSquareRoot.lean:284`, `:292`, `:300` | Additivity, rational scaling and real scaling with supplied modulus. |

The previously constructed convergence modulus is retained through R=I-H.
This algebraic positive square root acts on the whole original completion,
including its boundary states. No kernel removal or physical-time
calibration is inferred. The construction is not yet an iteratable generic
positive-contraction API, so applying it again to R is not an available
formal step.

### Next candidate, not a checked dyadic construction

Read-only review found existing finite Horner composition:
`QPolyRatPolySubstitutionAlgebra.compose`,
`lean/YMGap/Continuum/QPolyRatPolySubstitutionAlgebra.lean:118`, and
`eval_compose` at line 122. The candidate keeps all approximants as
polynomials in the ORIGINAL D:

    Q_(0,n)(d)=d; Q_(k+1,n)(d)=p_n(Q_(k,n)(d)).

The planned error certificate is
E_n(t)=(1-p_n(t))^2-(1-t), with E_0=t and
E_(n+1)=E_n*p_n+E_n^2/4. Its intended nonnegative coefficients and mass
E_n(1)=r_n^2 would control each finite square-relation error. Coefficient
positivity/monotonicity under composition, this error identity, a fixed-depth
modulus and the compatible limiting tower remain UNPROVED. This is a
mathematical work plan, not another assumed analytic input or a claim that
dyadic time has been constructed.

## Remaining obligations

Scalar-log identification, density in the appropriate physical sector,
self-adjointness, continuous physical time, spatial/spacing calibration,
continuum nontriviality and all Clay fields remain OPEN. No formal frontier
type was weakened or newly inhabited.

The next same-object reconstruction requirement is a fractional-time calculus
for this original all-nome T, strongly continuous on the closure of its
positive-time range, plus the explicit core limit
(T x-T^s T x)/s -> F x and a graph-core identification. The existing
`BF4ExactSlabThermodynamicDyadicSemigroup.action_one`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicDyadicSemigroup.lean:132`,
is pinned to that OTHER carrier's two-step transfer, not this T. No bridge
is supplied by the present result. The nonzero original time kernel prevents
assuming strong continuity on the whole carrier merely from positive-time
power laws.

## Verification

Two serialized focused checks passed 13 printed gates (11 new and two
existing), all within {propext, Quot.sound}. The safe launcher used one
worker, the mandatory 20 GiB ceiling and 12 GiB OS reserve. No full root,
full-tree build, audit or guard was run. No new sorry, axiom or classical
dependency. The canonical chart is unchanged and is not reprinted.

- `/tmp/ym-log-first-term-20260930.log`, SHA-256:
  `6ef15a6d4ed2131771f697a0845ebf6e87b6dc13b041978c6f1be8c4cc6b48e2`
- `/tmp/ym-log-core-gap-20260930.log`, SHA-256:
  `869b358fb8d14e9cdc2ab3362f8cc8d21653c5de0624b5e206718ac4e27600a1`

Follow-on verification: one further focused capped check passed the five new
graph-gap gates within {propext, Quot.sound}; no full-tree check or canonical
chart change. Log `/tmp/ym-log-graph-gap-20260930.log`, SHA-256:
`0a9afb9c9e1faf8c5e99cf91be1c6a77137e09e4443c6a30c7a6e3dd801c78b3`.

Complement-iteration verification: four serialized focused checks passed
26 gates within {propext, Quot.sound}, with the same one-worker/20 GiB cap
and 12 GiB reserve. No full build/audit/guard, new sorry, axiom or canonical
closure. Final log SHA-256 values:

- `/tmp/ym-defect-polynomial-20260930.log`:
  `63c723750ad06d8e0602b530d3279b2f0e143e4290919eb935e1975a99b029d5`
- `/tmp/ym-complement-root-mass-20260930.log`:
  `ef1588e697fb3f5e2a9737e27bad638c5de886380e608e863ad2a8e06cf236a8`
- `/tmp/ym-complement-root-polynomial-20260930.log`:
  `7f677e62a034435045017dd618ac1eddaacc23ac1b2896f888f860d5950e6314`
- `/tmp/ym-wilson-root-iteration-20260930.log`:
  `9160842d47be2ee3a51b7c1455b8aa26e909e4f337de11e8f9ad8601a1f76f27`

Positive-square-root verification: two further serialized focused checks
passed eight polynomial-algebra and fifteen square-root gates, all with
exactly {propext, Quot.sound}. The same one-worker/20 GiB cap and 12 GiB
reserve applied. A scalar error lemma eliminated repeated unfolding of
the completion after two elaboration-heartbeat failures; the successful
check uses the default heartbeat limit. No full root/tree build, audit,
guard, new sorry/axiom or canonical frontier closure. Final log SHA-256:

- `/tmp/ym-defect-polynomial-algebra-20260930.log`:
  `c40b6f092f39e6d6629cb57eae8cc1cab68621c2c9de77429786d2c4df1e771e`
- `/tmp/ym-wilson-square-root-20260930.log`:
  `10afbb6a2bcf6c2946c11523ecb3277bb901d403b9c9e69bcf447967979b6e64`
