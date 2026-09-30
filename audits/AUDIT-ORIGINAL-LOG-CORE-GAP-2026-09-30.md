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
calibration is inferred. This first-root construction is not an iteratable
generic positive-contraction API. The nested construction below avoids
needing such an API by keeping every approximant a polynomial in I-T.

## Follow-on: all fixed-depth nested limits with explicit moduli

Existing finite Horner composition is reused:
`QPolyRatPolySubstitutionAlgebra.compose`,
`lean/YMGap/Continuum/QPolyRatPolySubstitutionAlgebra.lean:118`, and
`eval_compose` at line 122. The construction keeps all approximants as
polynomials in the ORIGINAL D:

    Q_(0,n)(d)=d; Q_(k+1,n)(d)=p_n(Q_(k,n)(d)).

The shorter, now checked error certificate is E_n=2*(p_(n+1)-p_n).
Its coefficients are nonnegative by the previous monotonicity proof; its
evaluation is exactly (1-p_n(t))^2-(1-t) and its mass is r_n^2.
This avoids the proposed separate nonlinear error recurrence entirely.

Write s_(k,n)=1-Q_(k,n)(1). Coefficient-positive Horner composition and
scalar monotonicity prove 0<=s_(k,n)<=1 and

    s_(k+1,n)^2 <= s_(k,n) + r_n^2.

The explicit rational-precision modulus is

    N_0(e)=0,
    N_(k+1)(e)=max(N_k(e^2/2),tailModulus(e^2/2)).

For n>=N_k(e), s_(k,n)<=e. The induction uses r_n^2<=r_n and decidable
rational square-order reflection, not selection of a real square root.
There is no uniform-in-depth or practical computational-efficiency claim.

For m<=n, the ORIGINAL-carrier polynomial bound gives

    ||Q_(k,n)(D)x-Q_(k,m)(D)x||^2 <= s_(k,m)^2 ||x||^2.

With supplied representative X and norm ceiling c, put
j=max(c.num.toNat,e.den). The outer Cauchy modulus is N_k(invSucc j).
The existing represented diagonal limit supplies its approximation modulus
and a limit independent of the representation, at EVERY natural depth k.
No operator on a newly induced carrier or choice of quotient representatives
is involved.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `error_coeffNonnegative`, `eval_error`, `error_mass` | `lean/YMGap/Continuum/ComplementRootError.lean:30`, `:62`, `:77` | Positive finite square error with exactly identified scalar mass. |
| `compose_coeffLe`, `nested_difference_nonnegative` | `lean/YMGap/Continuum/ComplementRootComposition.lean:62`, `:133` | Monotone composition and positive ordered nested differences. |
| `residual_square_le` | `lean/YMGap/Continuum/ComplementRootNestedMass.lean:90` | Quantitative depth-step bound, retaining the scalar square error. |
| `residualModulus`, `residual_small` | `lean/YMGap/Continuum/ComplementRootNestedMass.lean:100`, `:106` | Explicit modulus for every fixed natural depth and positive rational tolerance. |
| `ordered_distance_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootIteration.lean:50` | SAME original completed-norm relative Cauchy bound. |
| `iterationModulus`, `iterationRows` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootIteration.lean:88`, `:116` | Computed outer modulus and actual original representatives. |
| `nestedLimit`, `nestedLimitCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootIteration.lean:138`, `:157` | Actual limits with witnessing convergence data, not supplied root objects. |
| `nestedLimit_symmetric`, `nestedLimit_form_le` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootIteration.lean:165`, `:177` | Original pairing symmetry and norm-form ceiling pass to every fixed-depth limit. |

The finite operator join is also checked. Put R_(k,n)=I-Q_(k,n)(D) and
E_(k,n)=E_n(Q_(k,n)(D)). Then on the SAME original completion,

    B(R_(k+1,n)x,R_(k+1,n)y) = B(x,R_(k,n)y) + B(x,E_(k,n)y),
    ||E_(k,n)x||^2 <= r_n^4 ||x||^2.

The error polynomial has nonnegative coefficients and mass <=r_n^2,
independently of nesting depth. This is a convergence-error bound, not a
uniform spectral gap. The exact polynomial identity descends through the
existing constructive coefficient-reflection theorem and the proved finite
action algebra. No polynomial functional-calculus axiom is introduced.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `action_eq_of_polyEqv` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootSquareError.lean:134` | Pointwise rational polynomial identity implies equality of actual finite actions, by proved coefficient reflection. |
| `finite_square_action_identity`, `finite_square_pairing_identity` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootSquareError.lean:145`, `:156` | Exact finite square law with its retained error on the original completion. |
| `nestedError_mass_le`, `nestedError_action_norm_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootSquareError.lean:170`, `:180` | Explicit vanishing error mass and original squared-norm bound. |

## Follow-on: compatible positive roots on the SAME original carrier

Square compatibility now holds for the actual limits:

    R_0=T,     B(R_(k+1)x,R_(k+1)y)=B(x,R_k y),     R_(k+1)^2=R_k.

The proof consumes `BF4WilsonAllNomeCompletedPairingContinuity.pairing_small`,
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedPairingContinuity.lean:84`.
For supplied original representatives X,Y, `errorPairingModulus X Y epsilon`
computes a cutoff independent of k for BOTH signs of the error pairing.
Represented root rows have modulus `iterationModulus k X (epsilon/2)`;
their limits equal the constructed R_k, without choosing a representative
from a quotient. In the finite pairing identity, the two pairing-limit errors
and the finite square error each receive epsilon/3. Their maximum cutoff
gives both inequalities up to arbitrary positive rational error. Definiteness
then yields the operator square law. The root approximation modulus itself
remains depth dependent.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `root`, `root_nonnegative`, `root_form_le` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootBasics.lean:54`, `:88`, `:169` | Actual positive root candidates and original-norm form ceiling. |
| `root_symmetric`, `root_realSmul`, `root_zero_depth` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootBasics.lean:71`, `:193`, `:230` | Symmetry, supplied-modulus real linearity and exact R_0=T(1). |
| `errorPairingModulus`, `nestedError_pairing_small` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootErrorSmall.lean:63`, `:124` | Explicit depth-independent two-sided error-pairing modulus. |
| `rootRows`, `limit_rootRows` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootCompatibility.lean:65`, `:88` | Original representatives and their exact root-limit pin. |
| `root_pairing`, `root_square` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootCompatibility.lean:177`, `:186` | Vanishing-error pairing identity and compatible square law. |
| `root_norm_bound`, `root_distance_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootCompatibility.lean:191`, `:201` | Norm and squared-distance contraction at every depth. |
| `root_zero_iff_time_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootCompatibility.lean:214` | Every constructed root retains exactly the original T(1) kernel. |

## Follow-on: actual dyadic semigroup, pinned to ORIGINAL one-step time

The existing `NonnegativeDyadicTime.Time` and `add`,
`lean/YMGap/Constructive/NonnegativeDyadicTime.lean:45`, `:73`, supply the
time quotient. Iterating R_depth for the supplied step count now descends
through its cross-multiplication relation. Two fine steps equal one coarse
step by `root_square`; induction gives arbitrary refinement. Equal mesh
presentations act equally at the explicit common depth p.depth+q.depth.
Quotient descent selects no time representative. The action is on the SAME
original completed carrier, without importing the legacy thermodynamic
action or replacing the one-step operator by its square.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `meshAction`, `mesh_refinement` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSemigroup.lean:41`, `:83` | Finite iteration of the actual roots and exact refinement consistency. |
| `mesh_congr`, `action` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSemigroup.lean:104`, `:116` | Equivalent meshes act equally; representation-independent dyadic action. |
| `action_add`, `action_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSemigroup.lean:123`, `:134` | S(s+t)=S(s)S(t) and S(0)=I on every original completed state. |
| `action_whole`, `action_root` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSemigroup.lean:137`, `:140` | S(n)=T(n), including the original T(1), and S(2^(-k))=R_k. |
| `action_symmetric`, `action_nonnegative`, `action_norm_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSemigroup.lean:142`, `:148`, `:153` | Symmetric positive contractions at every nonnegative dyadic time. |
| `action_add_state`, `action_smul`, `action_realSmul` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSemigroup.lean:159`, `:170`, `:180` | Additivity, rational linearity and real linearity with supplied scalar modulus. |
| `action_distance_bound`, `action_doubled_pairing` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicSemigroup.lean:202`, `:209` | Original squared-distance contraction and doubled-time pairing identity. |

## Follow-on: energy telescope and explicit original continuity moduli

The original-carrier argument is now checked. A single energy telescope
suffices for ALL small dyadic
increments; there is no need first to demand a sharper inverse-square rate
along only R_k. For A=S(steps/2^depth), its finer square root and contraction
give ||Ax||^2<=B(Ax,x), hence

    ||Ax-x||^2 + ||Ax||^2 <= ||x||^2.

Adjacent squared increments of A^n x decrease by contraction. Telescoping
therefore gives n*||A^(n+1)x-A^n x||^2<=||x||^2. When steps*n<=2^depth,
the remaining nonnegative integer steps transport this bound to Tx, since
`action_whole` pins a whole mesh interval to the original T. Taking n=2^k
proves

    steps*2^k<=2^depth
      => ||S(steps/2^depth)Tx-Tx||^2 <= 2^(-k)||x||^2.

The proof pattern was adapted from
`BF4ExactSlabThermodynamicDyadicEnergy.time_dissipation`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicDyadicEnergy.lean:86`,
`weighted_energy` at line 126, and `range_smallTime_bound` at line 221.
Those declarations concern a DIFFERENT carrier and transfer: their proof
pattern is reused, but their operator is not a supplied join here.
The original action laws above supply the algebraic inputs. For a supplied
ORIGINAL representative X with norm ceiling c, the checked modulus is

    rangeModulus(X,epsilon) = denominator(epsilon/(c+1)).

This follows from half^k<=invSucc(k)<=epsilon/(c+1) at that threshold.
Only the scalar `linearTolerance` and its rational budget are reused from
`BF4ExactSlabThermodynamicPolynomialContinuity`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicPolynomialContinuity.lean:82`;
the norm ceiling is the original `CRealSeminormPairingCompletion.normCeiling`
and its original diagonal bound, not that other carrier's norm.
The relative energy coefficient is independent of nome and width; the
absolute modulus uses the supplied original state's norm ceiling. This
is continuity, not a uniform mass estimate.

For an existing represented Cauchy family R of time images with supplied
preimage representatives X_n, set delta=epsilon/10, n=limitRate(R,delta).
The closure threshold is rangeModulus(X_n,delta). Two squared-distance
triangle estimates and dyadic contraction give total error
6*delta+4*delta=epsilon. The selected X_n is supplied data: no representative
is chosen from a quotient, and no uniform norm cap or convergence of X_n is
required. This is exactly the represented closure asserted by the theorem,
not an unproved characterization of the whole Hilbert carrier.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `mesh_form_dominates_norm`, `mesh_dissipation` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicEnergy.lean:93`, `:102` | Finer-root contraction gives the original one-increment energy inequality. |
| `weighted_energy`, `time_error_le_blockError` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicEnergy.lean:143`, `:176` | Finite telescope, then contraction over the explicit remaining time. |
| `range_small_bound`, `anchored_small_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicEnergy.lean:225`, `:232` | All small dyadic increments on T(1)x or relative to any positive dyadic anchor. |
| `rangeModulus`, `rangeContinuityCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicContinuity.lean:54`, `:85` | Computed original-state threshold retained as data. |
| `anchored_smallTime` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicContinuity.lean:91` | Explicit relative-time threshold at arbitrary positive anchors; zero anchor permits only zero increments. |
| `closureModulus`, `closure_smallTime`, `closureContinuityCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicContinuity.lean:127`, `:131`, `:157` | Quantitative continuity at the existing represented limit, with supplied preimage streams and no uniform source-norm bound. |

The original boundary kernel still forbids full-carrier continuity at zero.

The output-data step is also checked. `rootRepresentative` and
`rootRepresentative_pin`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicRepresentatives.lean:32`, `:36`,
use the actual root-row diagonal and its proved limit pin. `meshRepresentative`
at line 43 iterates these original Cauchy streams. `suppliedMeshCertificate`
at line 61 returns the stream AND equality to the existing dyadic action.
This supplies rows for the next real-time limit without any countable choice
of representatives from a quotient-valued sequence.

## Follow-on: positive real-time operators on the SAME original carrier

For supplied positive real time t with rational floor f>0, let p_n be its
computed upper dyadic approximations. At a common refinement the original
energy inequality proves

    p,q >= f and |p-q| <= f*2^(-k)
      => ||S(p)x-S(q)x||^2 <= 2^(-k)||x||^2.

For original representative X, choose k=rangeModulus(X,epsilon) and feed
f*2^(-k) into the supplied time-approximation modulus. The dyadic output
representatives therefore form an actual original-carrier Cauchy family.
Its diagonal supplies S(t)x, an output representative, and an explicit
convergence modulus. The construction works for EVERY original state at
strictly positive time, not just the range of T.

Equal represented times give equal outputs by comparing two dyadic streams
at the minimum of their positive floors and using the original squared
distance. Prop-level real equivalence is eliminated only into that equality
proof, never into the construction of output data. For positive dyadic t,
the upper-approximation error and an explicit denominator cutoff show that
the limit is the previous dyadic action. In particular S(n)=T(n), with one
unit exactly the ORIGINAL one-step transfer.

Positivity, symmetry and contraction pass through the existing represented
pairing limits; symmetry yields linearity. For time addition, rows at
p_n+q_n have a computed modulus and approach the already constructed sum-time
action. The finite identity

    B(S(p_n+q_n)x,y) = B(S(q_n)x,S(p_n)y)

passes to their actual limits. Original pairing definiteness then proves
S(s+t)=S(s)S(t). No continuity of operator composition is assumed, and no
legacy completed carrier or operator is used. Only carrier-free numerical
time data and scalar arithmetic are reused.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `mesh_close_bound`, `timeModulus` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimeAction.lean:70`, `:110` | Positive floor converts dyadic time precision into original-state precision. |
| `timeRows`, `positiveAction`, `actionCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimeAction.lean:125`, `:149`, `:174` | Constructed original output and explicit convergence data for every strictly positive represented time. |
| `positiveAction_symmetric`, `positiveAction_nonnegative`, `positiveAction_norm_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimeLaws.lean:43`, `:59`, `:84` | Symmetric positive contraction in the original completed pairing. |
| `positiveAction_time_congr`, `positiveAction_dyadic`, `positiveAction_original` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimePins.lean:53`, `:110`, `:118` | Independence from time presentation and exact recovery of original dyadic/integer time. |
| `realTimeAction` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimePins.lean:123` | Original operator descends to the existing numerical positive-real-time quotient. |
| `sumRows_limit`, `positiveAction_sum`, `sumActionCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveTimeComposition.lean:141`, `:177`, `:185` | Constructed summed-mesh limit, actual composition law, and explicit output/convergence certificate. |
| `realTimeAction_addTime`, `realTimeAction_mixed_moments`, `realTimeAction_original` | `lean/YMGap/Continuum/BF4WilsonAllNomePositiveRealSemigroup.lean:44`, `:59`, `:99` | Addition and moments on the existing numerical time quotient; exact original integer-time recovery. |

The norm contraction constant is one at every positive time. It is not a
strict mass-gap bound or a physical time calibration. Width and nome still
parameterize the original carrier. Its nonzero boundary kernel is retained;
no full-carrier zero-time continuity or continuous physical QFT is asserted.

## Recursive step back: direct root-sequence derivative (PROVED)

The finite telescope now uses the actual original roots throughout. For
D_k=I-R_k, nonnegative mixed moments obey an exact split; retaining the
terminal moment makes the estimate iterable. At every finite order r,

    n^(2*r) * ||R_k^(r*n) D_k^r x||^2 <= ||x||^2.

For Q_k x=2^k*(I-R_k)*T x, actual root compatibility gives

    Q_(k+1)x-Q_k x = 2^k*(I-R_(k+1))^2*T x,
    ||Q_(k+1)x-Q_k x||^2 <= 4^(-k)*||x||^2.

The geometric tail is summable in norm. The checked tail bound is
4*4^(-start)*||x||^2; the pair bound for m,n>=start is
16*4^(-start)*||x||^2. Original representatives and a computed modulus
construct A x=lim_k Q_k x. No original log-series identity is needed.
This intermediate result proves the difference-quotient limit along times
2^(-k). The all-small-time extension is supplied by the follow-on below.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `moment_nonnegative`, `moment_split`, `weighted_order`, `smoothing_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDefectDecay.lean:181`, `:188`, `:236`, `:259` | Positive original mixed moments give smoothing at every finite order. |
| `quotient_step`, `quotient_step_bound`, `quotient_tail_bound`, `quotient_pair_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDerivative.lean:93`, `:117`, `:148`, `:175` | Exact original refinement and quantitative geometric Cauchy bounds. |
| `quotientModulus`, `quotientRows`, `derivativeAction`, `derivativeCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDerivative.lean:196`, `:241`, `:274`, `:281` | Actual original output, supplied representatives and explicit convergence data; no choice over representatives. |
| `quotient_form_step`, `derivative_form_ge_defect`, `derivative_core_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDerivativeGap.lean:72`, `:97`, `:115` | Positive refinement passes the original defect floor to A; B(Tx,A x)>=(1-q)/2*B(Tx,Tx) when T x is vacuum-orthogonal. |
| `preimageRepresentative`, `quotientRows_time_image` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDerivativeContinuity.lean:42`, `:66` | Every quotient row is T(1) of an explicit original Cauchy preimage. |
| `derivativeContinuityModulus`, `derivative_smallTime`, `derivativeContinuityCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDerivativeContinuity.lean:74`, `:78`, `:89` | Computed continuity threshold for every small dyadic increment acting on A x; no whole-carrier continuity assumption. |
| `derivativeAction_time_congr` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDerivativeContinuity.lean:100` | Equal T(1)-images give equal A-outputs, without asserting injectivity of T. |
| `quotient_norm_bound`, `derivativeAction_norm_bound`, `derivativeAction_symmetric`, `derivativeAction_add`, `derivativeAction_smul` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDerivativeLaws.lean:83`, `:108`, `:120`, `:135`, `:145` | B(A x,A x)<=B(x,x), symmetry and rational linearity in the original PREIMAGE x. |

The core pair is (T x,A x). The last bound does not assert that its
Hamiltonian is bounded in the input norm ||T x||. The quotient preimages
need neither converge nor have a uniform norm ceiling: the continuity
modulus uses one explicitly computed row. The form margin retains the
original nome/width dependence; it is not a physical mass gap.

## Every small dyadic and positive real increment (PROVED)

The finite average of the actual original root defects telescopes exactly:

    ((I-R_k^(n+1))*T x)/((n+1)*2^(-k))
      = average_(j=0,...,n) R_k^j Q_k x.

Normalized averages preserve a common squared-norm bound, with no factor
depending on their length. Thus quotient convergence controls the average
of Q_k x-A x. The already constructed continuity modulus of A x controls
the remaining average of R_k^j A x-A x. Refinement preserves the actual
time and remainder, removing the threshold on k. This proves, including
zero and coarse mesh presentations,

    ||T x-S(t)T x-t*A x||^2 <= epsilon*t^2.

For dyadic time the positive radius is
`value <derivativeContinuityModulus X (quarter epsilon),1>`.
It depends on the supplied original representative, tolerance, nome and
width. No whole-carrier continuity assumption or uniform coupling/volume
radius is asserted.

Original difference rows and scalar-approximation rows now retain their
inner/outer moduli and have limits equal to the existing completed
operations. The actual dyadic remainders therefore have a represented
limit equal to the SAME positive-real-time remainder. The radius for real
time is half the dyadic radius; this leaves room for the supplied upper
dyadic time approximations. Pairing convergence and eventual order pass
the bound to the limit, retaining epsilon*t^2, not replacing it by a
constant error. No inverse of time or transfer is constructed or selected.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `average_norm_bound`, `timeAverage_contraction`, `timeAverage_defect` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeAverages.lean:226`, `:259`, `:298` | Normalized finite-average bound, contraction and exact original defect telescope. |
| `meshQuotient_average`, `timeAverage_derivative_close`, `mesh_quotient_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeMeshDerivative.lean:62`, `:93`, `:107` | The multi-step quotient and its error are controlled on sufficiently fine meshes, using continuity only of A x. |
| `remainder_refine`, `mesh_taylor_bound`, `meshTaylorCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeMeshDerivative.lean:172`, `:181`, `:224` | Refinement removes the depth threshold; a computed positive radius controls every small dyadic presentation. |
| `differenceRows`, `rowLimit_difference`, `scalarRows`, `scalarRows_limit` | `lean/YMGap/Continuum/BF4WilsonAllNomeRowLinear.lean:65`, `:102`, `:151`, `:202` | Constructed original rows, explicit moduli and limit pins to the existing difference and real scalar action. |
| `pairing_converges`, `remainderRows_pin`, `remainderRows_limit` | `lean/YMGap/Continuum/BF4WilsonAllNomeRealDerivative.lean:71`, `:117`, `:125` | Actual dyadic remainders converge to the original real-time remainder. |
| `realRemainder_time_congr`, `real_taylor_bound`, `realTaylorCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeRealDerivative.lean:102`, `:141`, `:179` | Time-presentation independence and the Taylor bound for EVERY supplied small positive real time, with computed positive radius. |

The derivative has the positive-generator sign: the derivative of S(t)T x
at zero from the right is -A x. A is still parameterized by the preimage x;
the core pair remains (T x,A x). Original T(1) defines the time unit.
The earlier core form margin now concerns this actual range derivative,
but it has not become a physical mass calibration or a self-adjoint
Hamiltonian theorem.

## Follow-on: closed witnessed graph of the actual derivative

The core pairs are now (Tx,A x), not (Tx,Fx). A graph witness supplies a
source sequence and one explicit modulus controlling both coordinates.
Commutation and continuity give T y=A u for a graph limit (u,y). When
u=0, the original kernel law gives A y=0. Symmetry then makes y orthogonal
to every approximating A-output, so convergence forces y=0. Subtraction
gives single-valuedness. This proof does not bound the preimages, choose
an inverse, assume T injective, or delete its boundary kernel.

The explicit diagonal samples the nth inner witness at its own invSucc(n)
threshold. It constructs closure under SUPPLIED simultaneous graph limits,
not a countable-choice selection of witnesses. Identifying presentations
by their original input gives a domain embedded in the unchanged carrier.
The positive-root fixedspace argument supplies the actual zero-action
vacuum: if R squared fixes u, positivity applied to u-Ru forces Ru=u.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `derivativeAction_commutes_time`, `derivativeAction_kernel_zero`, `derivativeAction_dist_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeCore.lean:56`, `:86`, `:96` | Original-time commutation, actual kernel annihilation and distance contraction in the preimage norm. |
| `derivativeAction_unit_zero`, `core_nonnegative`, `core_symmetric` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeCore.lean:165`, `:182`, `:186` | Actual vacuum annihilation and positive symmetric form on (Tx,A x). |
| `GraphLimit`, `graph_time_pin`, `graph_zero_input`, `graph_single_valued` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraph.lean:78`, `:97`, `:114`, `:147` | Simultaneous moduli, time pin, closability and unique output. |
| `diagonal`, `input_injective`, `vacuum_input`, `vacuum_action` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraph.lean:173`, `:223`, `:239`, `:242` | Witnessed closedness, original-carrier domain embedding and exact vacuum pins. |
| `scale`, `add`, `action_add`, `action_smul` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphLinear.lean:94`, `:116`, `:160`, `:174` | Explicit rational domain operations and linearity of its action. |
| `graphPairingModulus`, `action_nonnegative`, `action_symmetric` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphForm.lean:81`, `:194`, `:201` | Pairing continuity from image/output caps, positivity and symmetry on the quotient domain. |
| `graph_defect_form_le`, `graph_form_gap`, `action_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphGap.lean:130`, `:171`, `:179` | The actual derivative graph retains the unconditional defect floor and original margin (1-q)/2 on its vacuum complement. |

Only `coreMargin` and `completed_defect_form_gap` are reused from
`lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:52` and `:101`.
Their statements concern the original transfer and its rate; the new
derivative term uses `derivative_form_ge_defect` from
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDerivativeGap.lean:97`.
No equality A=F is used. The margin retains its nome/width dependence.

## Follow-on: actual Taylor differentiation at represented graph limits

Refining a fixed mesh leaves its quotient unchanged. The refined finite
averages of A x approach that quotient because the single-step quotients
approach A x and averaging contracts distance. Each average has norm at
most ||A x||, so order passage gives the sharp original bound
||Tx-S(t)Tx||^2<=t^2||A x||^2 at EVERY dyadic time. Passing this through
the two graph coordinates gives ||u-S(t)u||^2<=t^2||v||^2 for every supplied
GraphLimit (u,v), without a preimage norm bound.

For the Taylor extension, subtract one core graph pair (Tx_n,A x_n).
The new increment bound controls the difference of Taylor remainders by
4*t^2||v-A x_n||^2. Choose n from the graph's output modulus at
delta=epsilon/11, then take that ONE source's existing core Taylor radius.
The squared triangle costs at most 10*delta, leaving the required epsilon.
Thus no common radius across the approximating sequence is assumed.
Positive-real remainder rows pass the mesh estimate to their already
constructed original limit, retaining the factor t^2.

The radius constructor explicitly consumes representatives of the source
sequence, with their pins to G.source. These are additional SUPPLIED
representation data, not selected by choice from quotient elements. The
real-time theorem also takes representatives of u and v. Its claim is
differentiation at every such represented graph limit, not a converse or
maximal-domain theorem for arbitrary differentiable states. A remains the
actual positive-generator-sign derivative: d/dt S(t)u at zero is -v.

| Declaration | Source | Exact claim |
| --- | --- | --- |
| `norm_limit_order` | `lean/YMGap/Continuum/BF4WilsonAllNomeNormLimitOrder.lean:96` | Stagewise norm order passes through explicit same-carrier distance moduli. |
| `meshQuotient_refine`, `refined_average_close`, `meshQuotient_image_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeIncrement.lean:72`, `:81`, `:97` | Exact fixed-time refinement and sharp derivative-image norm bound, using finite averages. |
| `mesh_increment_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeIncrement.lean:134` | Every core dyadic increment is bounded by t squared times the actual derivative-image norm. |
| `incrementModulus`, `graph_mesh_increment_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphTimeBound.lean:64`, `:80` | Input increment convergence and the whole witnessed graph's sharp dyadic bound. |
| `outputContinuityCertificate`, `inputContinuityCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphContinuity.lean:117`, `:162` | Both graph-coordinate dyadic-continuity moduli from supplied source representatives. |
| `remainder_graph_bound`, `radius`, `mesh_taylor_bound`, `meshTaylorCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphMesh.lean:88`, `:131`, `:143`, `:176` | Output-error control transfers one core radius to all small dyadic times at the represented graph point. |
| `remainderRows_pin`, `remainderRows_limit`, `realRemainder_time_congr` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphReal.lean:90`, `:99`, `:74` | Original remainder rows converge to u-S(t)u-t*v, independent of time presentation. |
| `real_taylor_bound`, `realTaylorCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphReal.lean:126`, `:180` | Every small supplied positive real time obeys the Taylor estimate at a represented graph limit, with computed positive radius. |

## Follow-on: explicit two-coordinate graph criterion (PROVED)

The previous candidate is now constructed. Write D=I-T and
I_n=sum_(j<n)D^j. Exact finite identities give
T I_n u=u-D^n u and A I_n u=v-D^n v under A u=T v. Thus the two graph
errors are controlled by the same elementary tail argument, separately
for each coordinate.

For a supplied range witness R of z, choose ONE preimage x at its
epsilon/4 index. Contraction bounds ||D^n(z-Tx)||^2 by epsilon/4.
The existing positive-time tail, with that representative's own norm
ceiling, computes n large enough for ||D^n Tx||^2<=epsilon/4.
The squared triangle then gives ||D^n z||^2<=epsilon. There is no
uniform preimage norm bound, inverse transfer or selected representative.

Conversely, supplied source representatives of a graph give the input
range witness directly. For its output, the nth source has an explicit
dyadic quotient preimage at its computed invSucc(n)-accuracy depth.
Synchronizing that error with the graph error gives an actual original
time-range witness for the output. This is a two-coordinate criterion,
not full-carrier density or maximal differentiability-domain identification.

| Declaration | Source | Exact result |
|---|---|---|
| `defectPower_distance_contraction` | `lean/YMGap/Continuum/BF4WilsonAllNomeDefectContraction.lean:47` | Every original defect power contracts the original squared distance. |
| `defectPower_time_kernel` | `lean/YMGap/Continuum/BF4WilsonAllNomeDefectContraction.lean:59` | Defect powers fix original time-kernel states, rather than deleting them. |
| `RangeLimit`, `defectModulus`, `defect_small`, `defectDecayCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeClosure.lean:66`, `:98`, `:101`, `:120` | Supplied original time preimages and convergence modulus compute an all-tail defect cutoff. |
| `kernel_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeClosure.lean:127` | The witnessed sector intersects the original time kernel only at zero; the ambient carrier is unchanged. |
| `time_inverseSum_sub`, `derivativeAction_inverseSum_of_equation` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeInverseSum.lean:91`, `:105` | Exact graph-coordinate errors are D^n u and D^n v under A u=T v. |
| `inverseSumRepresentative`, `inverseSumRepresentative_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeInverseSum.lean:113`, `:118` | Supplied input representatives give explicit finite-sum representatives and exact original pins. |
| `stateQuotient`, `time_stateQuotient`, `derivative_equation_of_quotient_limit` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeEquation.lean:46`, `:51`, `:61` | Convergence of actual normalized state quotients gives A u=T v by original T contraction and represented-limit uniqueness. |
| `inputRange`, `outputPreimage`, `outputRange` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphRange.lean:45`, `:58`, `:75` | Construct both range witnesses from a represented graph; the output uses computed finite quotient preimages. |
| `equationDataOfGraph` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphEquation.lean:69` | Returns both coordinate range witnesses and the equation from represented graph data. |
| `graphOfEquation`, `graphOfEquation_representative_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphEquation.lean:78`, `:92` | Constructs the actual graph and supplies source representatives when the input representative is supplied. |
| `graphOfQuotientLimit` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphEquation.lean:101` | An actual quotient limit gives the graph given BOTH coordinate range witnesses. |
| `equationRealTaylorCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphEquation.lean:110` | With original input/output streams, the equation criterion now supplies the actual all-small-positive-real-time Taylor radius. |

`RangeLimit` is local convergence data, not a new frontier enumeration.
All constructed objects remain on the original fixed-nome/width carrier.
The equation alone still permits extraneous kernel components: the two
range hypotheses have not been erased or claimed automatic.

## Follow-on: output-range premise removed; derivative criterion in both directions (PROVED)

Write Q_n u=2^n*(u-R_n u) for the actual unshifted state quotient. Its
squared-distance cap is C_n=4*(2^n)^2. Given an input-range witness R,
choose its source at the computed tolerance
eta_n=invSucc(n)/(C_n+1). The original quotient representative of this
source has T-image Q_n(T source), and its squared distance to Q_n u is
at most invSucc(n). Thus, when Q_n u converges to v with modulus m,
the derivative output has an explicit range witness with modulus
max(m(epsilon/4),(epsilon/4).den). There is NO output-range premise.
The cap is depth-dependent and is paid by the chosen input tolerance;
no uniform quotient bound or uniform preimage norm cap is assumed.

For the reverse implication, the original graph Taylor theorem at a
single dyadic mesh step has remainder E_n with
||E_n||^2<=2^(-2n)*epsilon. The exact original-vector identity
Q_n u-v=2^n E_n cancels the rational factors. The denominator of the
computed positive Taylor radius is an explicit all-tail depth cutoff.

With an original input representative supplied, these give constructive
directions between represented graph data and input-range plus actual
quotient-limit data. Source representatives and convergence moduli remain
returned data. The already checked real Taylor consumer then upgrades
this actual root-sequence derivative to EVERY sufficiently small supplied
positive real time. This is not an assertion that every ambient state
has a derivative, or that the original boundary kernel has vanished.

| Declaration | Source | Exact result |
|---|---|---|
| `quotientCap`, `stateQuotient_distance_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeStateQuotientDistance.lean:44`, `:85` | Explicit positive cap C_n for the actual unshifted state quotients. |
| `preimageRepresentative_stateQuotient` | `lean/YMGap/Continuum/BF4WilsonAllNomeStateQuotientDistance.lean:101` | The original Cauchy preimage represents exactly Q_n of the supplied state. |
| `sourceTolerance`, `outputPreimage_close`, `outputRange` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeOutputRange.lean:58`, `:68`, `:82` | Pay the quotient cap at each depth, then construct the derivative-output range witness by an explicit diagonal. |
| `graphOfDerivative`, `representedGraphOfDerivative` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeOutputRange.lean:106`, `:123` | Actual quotient convergence on the witnessed input sector constructs the graph, with source representatives when the input representative is supplied. |
| `stateQuotient_error_pin`, `stateQuotientModulus`, `stateQuotient_bound`, `stateQuotientCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphQuotient.lean:56`, `:95`, `:111`, `:136` | Exact rescaled Taylor remainder and computed quotient convergence on every represented graph. |
| `derivativeDataOfGraph` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeOutputRange.lean:136` | Returns the input-range witness and actual derivative-limit modulus from represented graph data. |
| `derivativeRealTaylorCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeOutputRange.lean:148` | Real Taylor radius from the actual quotient limit and INPUT range only. |

## Follow-on: both range premises constructed from actual differentiability (PROVED)

The proposed finite factorization is now checked:
p(D)x=p(1)x+T(preimage), where preimage=-sum_j p_j I_j x.
Finite original vector operations construct its Cauchy representative.
Its exact squared approximation error is p(1)^2*B(x,x). For a fixed-depth
root polynomial the scalar mass p(1) is the existing explicit residual,
which tends to zero. Combining its modulus with the actual root-row
convergence constructs a time-range witness for EVERY fixed-depth root
image R_k u. The cutoffs depend on k; no depth-uniform estimate is claimed.

Actual quotient convergence Q_k u -> v bounds the quotient norms eventually:
the squared triangle and a norm ceiling for the supplied v representative
suffice. The exact identity u-R_k u=2^(-k)Q_k u then gives an explicit
root-to-input modulus. At depth n choose the root's time preimage to
invSucc(n) accuracy. This diagonal constructs the INPUT range witness.
The preceding output-range construction applies, so NEITHER coordinate
range is an additional premise of the represented derivative-to-graph map.
Both original representatives and every convergence modulus remain data.

| Declaration | Source | Exact result |
|---|---|---|
| `polynomial_time_pin`, `preimageRepresentative_pin`, `polynomial_time_error` | `lean/YMGap/Continuum/BF4WilsonAllNomePolynomialTimeRange.lean:114`, `:143`, `:150` | Exact finite T-image decomposition, its original representative and squared scalar-mass error. |
| `rootPolynomial_mass`, `rootPreimage_error`, `rootRange` | `lean/YMGap/Continuum/BF4WilsonAllNomeRootTimeRange.lean:55`, `:63`, `:104` | Root mass equals the computed residual; each actual fixed-depth root image has an explicit range witness. |
| `rootModulus`, `root_close` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeRootContinuity.lean:63`, `:111` | Actual quotient convergence computes an all-tail root-to-input cutoff. |
| `inputPreimage`, `inputPreimage_close`, `inputRange` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeInputRange.lean:59`, `:62`, `:69` | The diagonal supplies the former input-range premise from actual quotient convergence. |
| `representedGraphOfQuotientLimit` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeInputRange.lean:94` | Actual represented derivative data return a graph and original source representatives, with neither range premise. |
| `input_time_kernel_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeInputRange.lean:105` | A differentiable input in the original time kernel is zero; ambient boundary states are not removed. |
| `quotient_form_gap`, `quotientRealTaylorCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeInputRange.lean:115`, `:126` | The original fixed-nome/width margin and all-small-positive-real-time Taylor certificate apply to these actual derivative pairs. |

## Follow-on: direct weak-adjoint graph characterization (PROVED within sector)

No resolvent is needed for this pairing criterion. Write A for the bounded
preimage derivative and T for the original one-step transfer. Their proved
symmetry identifies the core tests B(u,A x)=B(v,T x), for every x, with
A u=T v. Given both coordinate range witnesses, the existing equation
criterion constructs the graph. Conversely, graph symmetry supplies the
tests against every graph pair. Kernel components are invisible to the
weak tests, so the sector restriction cannot simply be removed here.

| Declaration | Source | Exact result |
|---|---|---|
| `CorePairings`, `GraphPairings` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeAdjointTests.lean:51`, `:54` | Tests against the actual core and the actual witnessed graph, respectively. |
| `corePairings_iff_equation` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeAdjointTests.lean:57` | Original symmetry and pairing separation give exactly A u=T v. |
| `graph_pairings`, `graphPairings_core` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeAdjointTests.lean:68`, `:72` | A graph supplies every weak test; graph tests include core tests. |
| `graphOfCorePairings`, `graphOfPairings`, `corePairings_iff_graphPairings` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeAdjointTests.lean:78`, `:83`, `:88` | Both witnessed sector coordinates plus the tests construct the graph and its modulus. |
| `representedGraphOfPairings` | `lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeAdjointTests.lean:96` | Supplied input/output representatives return explicit graph-source representatives. |

## Follow-on: range closedness and dyadic continuity-sector characterization (PROVED)

The sector closedness step is now a construction on the original carrier.
Given range witnesses R_n for x_n and an explicit modulus for x_n -> z,
choose preimage_n from R_n at its invSucc(n)-accuracy index. The squared
triangle yields convergence to z at
max(outerModulus(epsilon/4),(epsilon/4).den). This computes a range witness
for z with no preimage norm cap. Applying it to the existing represented
Cauchy-row limit proves represented completeness within the witnessed sector;
the same limit retains vacuum orthogonality when every row has it.

Conversely a range witness already gives represented rows of time images.
Their Cauchy modulus is R.modulus(epsilon/4); uniqueness identifies the
computed row limit with the original target x. The existing diagonal thus
constructs an original Cauchy representative OF x from R, without choosing
one from an arbitrary quotient. Transporting the previous closure-continuity
theorem along this identity supplies ALL sufficiently small dyadic increments.

For the converse continuity criterion, each R_k x has a range witness from
the already checked root construction. If R_k x -> x with a supplied modulus
and original input representative, the new closedness construction returns
range membership. This requires no derivative or candidate derivative output.
The same membership then upgrades root-sequence continuity to all small
dyadic increments with an explicit modulus. These are constructive witness
maps, not a Prop-level existence characterization or a physical identification.

| Declaration | Source | Exact result |
|---|---|---|
| `diagonalPreimage`, `diagonalPreimage_close`, `ofLimit` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeClosed.lean:48`, `:52`, `:60` | Explicit range witness for a supplied original norm limit, with computed diagonal and outer cutoff. |
| `representedLimit`, `centeredRepresentedLimit` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeClosed.lean:85`, `:93` | The SAME completed row limit remains in the witnessed range and, when appropriate, the original vacuum complement. |
| `rangeRows`, `rangeRows_point`, `rangeRows_limit` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeClosed.lean:103`, `:119`, `:122` | A range witness supplies represented time-image rows whose limit is exactly its target. |
| `representative`, `representative_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeClosed.lean:128`, `:132` | Computed original Cauchy representative, without quotient choice. |
| `continuityModulus`, `smallTime`, `root_small` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeContinuitySector.lean:51`, `:55`, `:64` | Witnessed range membership gives all-small-dyadic continuity and its root specialization. |
| `rangeOfRootLimit`, `rangeOfDyadicContinuity` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeContinuitySector.lean:75`, `:81` | Actual root/dyadic continuity constructs the range witness in the reverse direction. |
| `continuityOfRootLimit` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeContinuitySector.lean:94` | Root-sequence continuity upgrades to a computed modulus for ALL small dyadic increments on the SAME input. |

## Remaining obligations and next consumer

The independent source review confirms that another pairing wrapper would
not remove an input. The actual `Domain` at
`lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraph.lean:210` already
has the positive symmetric action laws `action_nonnegative` and
`action_symmetric` at
`lean/YMGap/Continuum/BF4WilsonAllNomeDerivativeGraphForm.lean:194` and `:201`.
Represented closedness/completeness and the dyadic-continuity criterion are
now supplied above. The further checked real-continuity characterization,
positive-time invariance, real-linear sector operations and represented
graph scaling are recorded in
`audits/AUDIT-ORIGINAL-REAL-CONTINUITY-SECTOR-2026-09-30.md`.
The follow-on intrinsic REAL presented-sector density, completeness and
graph-adjoint equality are now checked in
`audits/AUDIT-ORIGINAL-SECTOR-ADJOINT-2026-09-30.md`, preserving explicit
source data. Physical OS and full complex Hilbert identification remain open.
`RangeLimit` at
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeClosure.lean:66` explicitly
supplies core approximation within that sector, not whole-carrier density.

Existing `CompleteGNSHilbert` at
`lean/YMGap/Continuum/GNSComplete.lean:276` uses another GNSData interface.
`SelfAdjointHamiltonianResidual` at
`lean/YMGap/Continuum/GNSHamiltonian.lean:285` requires a whole-carrier
map and a symmetry law, with no operator domain or boundedness field;
it is not directly filled by this sector-restricted graph. `SelfAdjointOp` at
`lean/YMGap/Continuum/OSReconstruction.lean:125` is an abstract placeholder,
not a proved physical identification. None of these names is a same-object
bridge. A complete Hilbert-sector package, physical OS-sector identification,
spatial/spacing and physical-time calibration, continuum nontriviality and
all Clay fields remain OPEN. Equality A=regularizedLog and identification
with the existing series graph remain separate open obligations; no frontier
field is removed or weakened. Scaling survival remains the independent
primary analytic problem: the source-specific relative temporal-energy
UPPER bound on a justified scaling family is not supplied by this domain work.

The existing `BF4ExactSlabThermodynamicDyadicSemigroup.action_one`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicDyadicSemigroup.lean:132`,
is pinned to that OTHER carrier's two-step transfer, not this T. No bridge
is supplied by the present result. Only carrier-free scalar lemmas and
numerical time data are reused from legacy files. The nonzero original time kernel prevents
assuming strong continuity on the whole carrier merely from positive-time
power laws; no boundary state has been removed.

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

Nested-limit verification: four final serialized focused checks passed 26 gates
within {propext, Quot.sound}; the finite nested polynomial and modulus
definitions have empty axiom sets. The same one-worker/20 GiB ceiling and
12 GiB reserve applied. The composition proof needed two implicit induction
argument corrections; all final gates are clean. The mass file has one
unused-variable warning. No full root/tree build, audit/guard, new sorry/axiom,
frontier weakening or canonical chart change. Final log SHA-256:

- `/tmp/ym-complement-root-error-20260930.log`:
  `e15ad0f5d68fd214401a71309501ce13562472da4d5b57878af3b9a1e1addc3e`
- `/tmp/ym-complement-root-composition-20260930.log`:
  `24ad326909b37daaf36166506ebb334b974235b03c0bcad09e7899d4edc9cee2`
- `/tmp/ym-complement-root-nested-mass-20260930.log`:
  `acfd83c9103c1b7eecf022ac81979d491aaccccca2181ed0bb2a887887c18004`
- `/tmp/ym-wilson-nested-root-iteration-20260930.log`:
  `d2e716236a25ee88ee13fc3c234b7b208ede51373d7bacc52304b63e5911c422`

Finite-square-error verification: one further final focused target check
passed seven gates in {propext, Quot.sound}, after a namespace qualification
and a missing argument-parenthesis correction. The same resource bounds
and verification scope apply. Together the five final targets passed 33
gates; no claim of whole-tree verification. Log
`/tmp/ym-wilson-nested-root-square-error-20260930.log`, SHA-256:
`5ded56a3b0ed6b7419534131069041df2cde3591eccc001d252be0ec6d146b66`.

Compatible-root verification: three final serialized focused checks passed
24 printed gates (13 Basics, three ErrorSmall, eight Compatibility), each
with exactly {propext, Quot.sound}. The same one-worker/20 GiB ceiling and
12 GiB reserve applied. No full root/tree build, audit/guard, new sorry/axiom,
frontier weakening or canonical chart change. Final log SHA-256:

- `/tmp/ym-wilson-nested-root-basics-20260930.log`:
  `b868a069bffe6cd179e9592aa4b179c71f8b7be47c7e734e60ff0fb14193dc03`
- `/tmp/ym-wilson-nested-root-error-small-20260930.log`:
  `88102c98e08679c73d93322b145e0956d1fefb43732de4853d8f2e9dab03f79c`
- `/tmp/ym-wilson-nested-root-compatibility-20260930.log`:
  `143bb89151a8ee9f2276e18c5d5f70e01c41193ad7728d6827e1ab44f1da03be`

Dyadic-action verification: one further final focused check passed all 16
printed gates, each with exactly {propext, Quot.sound}. One initial attempt
needed mesh presentations unfolded on BOTH sides before induction; the final
check uses the unchanged default heartbeat limit. The same one-worker/20 GiB
ceiling and 12 GiB reserve applied. No full root/tree build, audit/guard,
new sorry/axiom, frontier weakening or canonical chart change. Log
`/tmp/ym-wilson-dyadic-semigroup-20260930.log`, SHA-256:
`3e9a7fbd95e20b8e905c05b65b607ecbf9509b21112535010bb3d1ed5c779333`.

Dyadic-continuity verification: two serialized focused checks passed all
20 gates (12 Energy, eight Continuity), each with exactly
{propext, Quot.sound}. Both passed on their first check. The same
one-worker/20 GiB ceiling and 12 GiB reserve applied. No full root/tree build,
audit/guard, new sorry/axiom, frontier weakening or canonical chart change.
Final log SHA-256:

- `/tmp/ym-wilson-dyadic-energy-20260930.log`:
  `438145ff81887eab9918e81e647a2fb22dab338eacabec9ce4c714a74f058afa`
- `/tmp/ym-wilson-dyadic-continuity-20260930.log`:
  `20908b64ab60727b0f472de2fa2b7a5c0f74047fa314645b1baaf7b79e5c5432`

The further focused Representatives check passed five gates on its first
check, each with exactly {propext, Quot.sound}, under the same safety and
scope limits. The three final targets therefore passed 25 gates. Log
`/tmp/ym-wilson-dyadic-representatives-20260930.log`, SHA-256:
`7f99b33e1a18d6bf4cb9b11a0474a46983c54c6186fc74ebff6e45b4537fb97c`.

Positive-real-time verification: five final serialized focused file checks
passed 51 printed gates (12 Action, eight Laws, eight Pins, 11 Composition,
12 RealSemigroup), each with exactly {propext, Quot.sound}. The monitored
launcher used one worker capped at 20 GiB, with 12 GiB OS reserve. No safety
stop or ceiling increase was needed. The Action check needed a direct
induction for half-power positivity; Composition needed a namespace open and
explicit intermediate points in the generic squared-distance theorem.
All final logs are clean. No full root/tree build, audit/guard, new sorry,
new axiom, frontier weakening or canonical chart change was made.

Sol implemented the original limit laws and summed-mesh composition; main
constructed the actual limits, time pins and quotient-level laws and checked
all targets. Luna independently reviewed the next derivative seam. That
source review is a plan, not verification of new derivative theorems.
The safe-build skill kept checks targeted and serialized. Final log SHA-256:

- `/tmp/ym-wilson-positive-time-action-20260930.log`:
  `f4a997be93fb059f984cf257ebe2abd1a777ebf76112f5ef52e643bf7e17f01f`
- `/tmp/ym-wilson-positive-time-laws-20260930.log`:
  `0e638b6bf01c1c16c485b03139279ea2760e358469376ba3c0f4f7e2efcc5446`
- `/tmp/ym-wilson-positive-time-pins-20260930.log`:
  `c4724942231e0904b64ca7bac23bb87ead88a9c373bd8ce119a5d7909b878426`
- `/tmp/ym-wilson-positive-time-composition-20260930.log`:
  `58643931ff25a76a8aed1964147f49d8676ac16464a2fffb37bf5cb1f9a12aca`
- `/tmp/ym-wilson-positive-real-semigroup-20260930.log`:
  `926b26e8bf2a119e0c95f4ca72bc6611ab628495da28252a835f1f4ef6df5303`

Direct root-sequence derivative verification: five serialized focused checks
passed all 64 printed gates (24 DefectDecay, 21 Derivative, five Gap,
eight Continuity, six Laws), each with exactly {propext, Quot.sound}.
All five passed on their first focused check, without warnings. The same
one-worker/20 GiB ceiling and 12 GiB OS reserve applied. No full root/tree
build, audit or guard was run; adding root imports is not root verification.
No new sorry, axiom, classical dependency, frontier weakening or canonical
chart change. The safe-build skill kept verification targeted and serialized.

Main constructed the original mixed-moment telescope and core-gap proof;
Sol constructed the represented quotient limit and its output-continuity
certificate; Luna supplied symmetry, rational linearity and the preimage
norm bound. Main inspected and checked every new module. The all-small-time
derivative was source-guided planning at this checkpoint; the subsequent
verification below closes that join.
Final log SHA-256:

- `/tmp/ym-wilson-dyadic-defect-decay-20260930.log`:
  `6afa25ab6421a081ae54ba9ac1e2ed47abd1dcad9b8ba5470cd0d6e0dbd075a2`
- `/tmp/ym-wilson-dyadic-derivative-20260930.log`:
  `a8c1c103876540ddb2435c82e6ed6ecfe926a83ea216810b608c40b2d9bc6466`
- `/tmp/ym-wilson-dyadic-derivative-gap-20260930.log`:
  `2ef0300bd9b5fce1f439f156738791cbf2f8fa69eb28dbc7cd3c6a12b1250f50`
- `/tmp/ym-wilson-dyadic-derivative-continuity-20260930.log`:
  `f37322f19eee3fe6b01236f303e9f0dfac19b468eedfe1ab0783ad41dd87db4c`
- `/tmp/ym-wilson-dyadic-derivative-laws-20260930.log`:
  `3378eca018c120ccd11464a6bb9fe70b009608394e61eae3b625dd9ef6ff80d2`

All-small-time derivative verification: four final serialized focused checks
passed 58 printed gates (21 TimeAverages, 15 MeshDerivative, ten RowLinear,
12 RealDerivative), all within {propext, Quot.sound}, without warnings.
The first three needed respectively a zero-step unfolding, a match-layout
correction and explicit representative arguments; RealDerivative passed
its first check. The same one-worker/20 GiB ceiling and 12 GiB OS reserve
applied. No full root/tree build, audit or guard; root imports are added but
not root-checked. No new sorry/axiom, classical dependency, frontier
weakening, kernel deletion or canonical chart change.

Luna drafted finite averages; Sol constructed represented difference/scalar
rows; main reviewed those, constructed the dyadic and real Taylor proofs,
and checked every target with the safe-build skill's narrow serialized
procedure. A separate Luna source review informed the next graph plan;
it does not verify that future graph. Final log SHA-256:

- `/tmp/ym-wilson-time-averages-20260930.log`:
  `af8efaee570f849b64ac083f87034c7c1185bfb964d90742fae3f0df06d3503d`
- `/tmp/ym-wilson-mesh-derivative-20260930.log`:
  `a24991165feccd08bc5859d7bfb3fb0e8aba1c8749fda96ffbf77dcd8f3022e4`
- `/tmp/ym-wilson-row-linear-20260930.log`:
  `78d439c7966eb6bf6fb603a32d0fd30f31a353ad7ce62271ac656376f7aa15db`
- `/tmp/ym-wilson-real-derivative-20260930.log`:
  `fd446d78d346fbbb6220af1b9a0ff0aea25c510d7df2cd0d1a5e7f398e73781d`

Actual derivative-graph verification: five final serialized focused checks
passed 51 gates (eight Core, 21 Graph, nine Linear, eight Form, five Gap),
all within {propext, Quot.sound}, with no final warnings. Core required
explicit limit unfolding, a width argument and zero-vector/presentation
rewrites; Form required avoiding a local-notation binder collision.
Graph, Linear and Gap passed their first focused checks. The safe-build
skill kept verification targeted and serialized, with one 20 GiB worker
and a 12 GiB OS reserve. No ceiling increase or safety stop was needed.
No full root/tree build, audit or guard; root imports are not root verification.
No new sorry/axiom, classical dependency, frontier weakening, kernel
deletion or canonical chart change. Sol drafted Core, Luna drafted Linear
and independently reviewed graph scope, and main reviewed/finalized every
module and performed every compiler check. Final log SHA-256:

- `/tmp/ym-wilson-derivative-core-20260930.log`:
  `1d7998275b8c5c5f7d92fcf7e5e21a4eebab34474f16f31171bd9ce5f9d3cf69`
- `/tmp/ym-wilson-derivative-graph-20260930.log`:
  `63f962a1240ed5677b53639305096caf894a59134750751c5d7167d7b8e0a150`
- `/tmp/ym-wilson-derivative-graph-linear-20260930.log`:
  `ca48887ee38ef42c074ca1847fbdc31320d8ef216b79c8233417567905c4aad1`
- `/tmp/ym-wilson-derivative-graph-form-20260930.log`:
  `0e86ecad0dbe06a086fe923a896f82b77fe0f3a4a406b91b5d6bf59c5c8e0015`
- `/tmp/ym-wilson-derivative-graph-gap-20260930.log`:
  `1caadba2e871e0c54c7868fbf8aaecfb125fa644db554894323a9135bcc0fc8e`

Represented-graph derivative verification: six final serialized focused
checks passed 36 gates (one NormLimitOrder, five Increment, six Continuity,
five TimeBound, ten Mesh, nine Real), each with exactly {propext, Quot.sound},
without final warnings. NormLimitOrder needed namespace, propositional-cap
and pairing-orientation fixes; Increment needed positive-product and cast
rewrites; Continuity needed explicit local-vector unfolding; Mesh needed
the fully expanded completion-setoid notation. TimeBound and Real passed
their first focused checks after static inspection. The safe-build skill
kept all checks narrow and serialized under one 20 GiB worker and a 12 GiB
OS reserve; no safety stop or ceiling increase. No full root/tree build,
audit or guard; added root imports are not root verification. No new sorry,
axiom, classical dependency, frontier weakening, kernel deletion or
canonical chart change. Sol drafted the increment proof; Luna drafted norm
order, continuity and real-time passage; main reviewed/finalized all six
modules, proved the graph-bound/Taylor joins and ran every check.
Final log SHA-256:

- `/tmp/ym-wilson-norm-limit-order-20260930.log`:
  `b3b971afe560af77444fabbfc91937fe363df9d42003b123b59d52a8e625b452`
- `/tmp/ym-wilson-derivative-increment-20260930.log`:
  `0e2810509ae673003d84cd180e11b9a84fbd788179c161222addb257d127c8e9`
- `/tmp/ym-wilson-derivative-graph-continuity-20260930.log`:
  `e0ba576bf7c5a80ba4249a41477f8a0217939b73cea04fddc078806649a8d230`
- `/tmp/ym-wilson-derivative-graph-time-bound-20260930.log`:
  `5bdbe7b1a8f9462dbd8bc308de592f466b40127c39f2904cab08b9cb7d26c5b1`
- `/tmp/ym-wilson-derivative-graph-mesh-20260930.log`:
  `698b01d80faa988fa91f6694b3abf1a1554dcfdb8732e7714810486c8e3d875c`
- `/tmp/ym-wilson-derivative-graph-real-20260930.log`:
  `e19b6c79fdd136aa0a85c2807e5ecab79671bfb450f595a01894d22dbe5f3d13`

Two-coordinate graph-criterion verification: six final serialized focused
checks passed 37 printed gates (four DefectContraction, nine InverseSum,
11 TimeRangeClosure, three Equation, four GraphRange, six GraphEquation),
all within {propext, Quot.sound}, with no final warnings. DefectContraction
needed an explicit import and removal of a redundant tactic; InverseSum
needed beta reduction before a rewrite; Equation needed its dependent
bound generalized before quotient induction. GraphRange's unused binder
was renamed. The other new proofs checked on their first focused run.

The safe-build skill kept checks targeted and serialized, with one worker
capped at 20 GiB and a 12 GiB OS reserve. No safety stop or ceiling increase.
No full root/tree build, audit or guard; added root imports are NOT root
verification. No new sorry/axiom, classical dependency, frontier weakening,
kernel deletion or canonical chart change. Sol drafted finite inverse
sums and represented coordinate ranges; Luna drafted defect contraction
and the necessary derivative equation. Main reviewed/finalized all files,
constructed the explicit tail modulus and graph-equation/Taylor joins,
and ran every compiler check. Final log SHA-256:

- `/tmp/ym-wilson-defect-contraction-20260930.log`:
  `085aa516e78977c4668aa0c12e7cfd5f61e5b551ebd1db421809c781cfa07951`
- `/tmp/ym-wilson-derivative-inverse-sum-20260930.log`:
  `ec7e1f870c687bfedf5466638edc992f354d88377099e8d8530206efb39fbba3`
- `/tmp/ym-wilson-time-range-closure-20260930.log`:
  `091cbc5cf92a41d926f9f4bb9c37dc50ce0c1c69da75beec5885ac26cc4fe0a4`
- `/tmp/ym-wilson-derivative-equation-20260930.log`:
  `fd1761c2fdaaa486c1f96d1f0c172f7e227f0548dc606804b15ed6d89b121cbe`
- `/tmp/ym-wilson-derivative-graph-range-20260930.log`:
  `bdc8d7e8e5d1800f4a61721ad3a32370af65186632aeea24e28c4991b9ef21d9`
- `/tmp/ym-wilson-derivative-graph-equation-20260930.log`:
  `f59d2adeb480195cb540ea0049c32eb592f03647d4d58375396ae37becfab587`

Derivative-output range and converse verification: three final serialized
focused checks passed 21 printed gates (six StateQuotientDistance, including
its private defect bound; five GraphQuotient; ten OutputRange), all within
{propext, Quot.sound}, with no final warnings. StateQuotientDistance needed
explicit RCle composition instead of a nonexistent LE RC instance;
OutputRange needed an explicit rational endpoint for an intermediate
inequality. GraphQuotient passed its first check after an explicit namespace
open. Each final source, including the additional witness-returning join,
was checked. Root imports are added but NOT root-checked.

The safe-build skill kept checks narrow and serialized under one 20 GiB
worker and a 12 GiB OS reserve. No ceiling increase, safety stop, full
root/tree build, audit or guard. No new sorry/axiom, classical dependency,
frontier weakening, kernel deletion or canonical chart change. Luna drafted
the quotient distance cap; Sol drafted the Taylor-to-quotient proof; main
constructed the output-range diagonal, reviewed/finalized every module and
ran every compiler check. A separate Luna source review informed the next
input-range plan only; it is not evidence of a proved input-range theorem.
Final log SHA-256:

- `/tmp/ym-wilson-state-quotient-distance-20260930.log`:
  `3f4eef9d05da5a1e120e03d7201e05893076bc8ebe4769c501335cf5b9c854de`
- `/tmp/ym-wilson-derivative-graph-quotient-20260930.log`:
  `dffb0909935efe2c6971eea77e892e84ec23e6b926b3e14717cafe7bff9210ba`
- `/tmp/ym-wilson-derivative-output-range-20260930.log`:
  `c46e60c492c241439732ecac9be3d984ccff2dcb51f2e37a77a0cdd8097bf5ef`

Derivative-input range and direct adjoint-test verification: five final
serialized focused checks passed 35 printed gates (ten PolynomialTimeRange,
six RootTimeRange, three RootContinuity including its private cap, seven
InputRange, nine AdjointTests), each with exactly {propext, Quot.sound}.
The finite identity needed beta reduction and scalar-sum order corrections;
root continuity needed the pairing-data norm ceiling, explicit RCle
composition and the actual half-power namespace. All final logs are clean.
The sources were checked after those fixes; the added root imports are
NOT a root check.

The safe-build skill kept verification targeted and serialized: one worker,
20 GiB ceiling and 12 GiB OS reserve. No safety stop, limit increase, full
root/tree build, audit or guard. No new sorry/axiom, classical dependency,
frontier weakening, kernel deletion or canonical chart change. Sol drafted
the polynomial identity, Luna drafted the quotient-to-root estimate, and
main finalized both, constructed the range diagonals and direct adjoint
proof, and ran all compiler checks. Sol independently reviewed the scoped
adjoint argument and the existing consumer interfaces. Final log SHA-256:

- `/tmp/ym-wilson-polynomial-time-range-20260930.log`:
  `e6bcd9ebcdbecfe0a22bd4be0878b86d34206db9496ba18dd43037b8eaf499c1`
- `/tmp/ym-wilson-root-time-range-20260930.log`:
  `6509bdf9f01c422107b582c3fa41afea7654029e2a9d70c910ef91190737d093`
- `/tmp/ym-wilson-derivative-root-continuity-20260930.log`:
  `e5ed8930ab5a45b16cc546d91123ab470384778917f2d3cf758a9f3a5e18c666`
- `/tmp/ym-wilson-derivative-input-range-20260930.log`:
  `a7a2cdc12941e6512dab43251f4333a6380accf496519491de488178e47c4bd9`
- `/tmp/ym-wilson-derivative-adjoint-tests-20260930.log`:
  `161dd37f6fee5477d446a7803f9a29f6459dd83c3e7ccc80bffbd4f4b6e82309`

Range-closedness and continuity-sector verification: two final serialized
focused checks passed 16 gates (ten TimeRangeClosed, six TimeContinuitySector),
each with exactly {propext, Quot.sound}, with no warnings or proof failures.
The first five closedness gates were checked before extending the same file
with representative extraction; the final full file was then rechecked.
Both final checks finished within their initial tool calls. The safe-build
skill kept the one-worker 20 GiB ceiling, 12 GiB OS reserve, process preflight
and automatic telemetry. No safety stop or raised limit; no full root/tree
build, audit or guard. Root imports are NOT root verification.

Main constructed and checked both modules; Luna independently reviewed the
witness flow and scope. Sol separately reviewed the primary signed analytic
frontier; that review is recorded in
`audits/AUDIT-SIGNED-FAMILY-TEMPORAL-JOIN-2026-09-30.md` and is not a new
signed estimate. No new sorry/axiom, classical dependency, frontier weakening,
kernel deletion, physical-sector identification or canonical chart change.
Final log SHA-256:

- `/tmp/ym-wilson-time-range-closed-20260930.log`:
  `a78607033d2a9b583204e427c1bcd105cb38fe404c90f3f9897329ef1a3de8f9`
- `/tmp/ym-wilson-time-continuity-sector-20260930.log`:
  `9cb0ec19c4ec3718e363bcc30455516590e48fcba21b28525885b70407fec624`
