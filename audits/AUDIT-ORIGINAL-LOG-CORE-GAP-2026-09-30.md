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

## Remaining obligations

Scalar-log identification, density in the appropriate physical sector,
self-adjointness, continuous physical time, spatial/spacing calibration,
continuum nontriviality and all Clay fields remain OPEN. No formal frontier
type was weakened or newly inhabited.

The dyadic action, restricted dyadic continuity and positive real-time action
are now supplied. Real-time continuity at zero on the witnessed positive-time
sector and a genuine derivative/domain construction remain required. The
specific core limit (T x-T^s T x)/s -> F x and the existing series-graph
identification remain OPEN, but the direct derivative route below need not
prove that identity first. The existing
`BF4ExactSlabThermodynamicDyadicSemigroup.action_one`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicDyadicSemigroup.lean:132`,
is pinned to that OTHER carrier's two-step transfer, not this T. No bridge
is supplied by the present result. The nonzero original time kernel prevents
assuming strong continuity on the whole carrier merely from positive-time
power laws.

### Recursive step back: construct the derivative directly (PLAN, not proof)

The constructive target needs the actual time generator, not a compulsory
detour through one chosen series presentation. Define the candidate
Q_k x=2^k*(I-R_k)*T x. The original checked `root_square`,
`lean/YMGap/Continuum/BF4WilsonAllNomeNestedRootCompatibility.lean:186`,
suggests the finite identity

    Q_(k+1)x-Q_k x = 2^k*(I-R_(k+1))^2*T x.

The required smoothing estimate is NOT yet a Wilson declaration. The
other-carrier proof pattern is `smoothing_bound`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicDyadicDefectDecay.lean:190`:
positivity and exact splitting of mixed time/defect moments give an iterated
weighted telescope. Reprove that estimate for each actual original R_k,
using the finer original root for moment positivity. At depth k+1 and
n=2^k, order two, the target bound becomes

    2^(4*k) * ||(I-R_(k+1))^2*T x||^2 <= ||x||^2.

It would give ||Q_(k+1)x-Q_k x||^2<=4^(-k)||x||^2. The existing OTHER-carrier
implementation is `quotient_step_bound` and `quotient_tail_bound`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicDyadicDerivative.lean:100`,
`:125`; neither is an original-carrier theorem by import alone.
Positive refinement forms would let the derivative inherit the original
`completed_defect_form_gap`,
`lean/YMGap/Continuum/BF4WilsonAllNomeLogCoreGap.lean:101`, on inputs T x.
This reduces the next search to an actual smoothing estimate, not a new
assumed generator bundle or a full polynomial calculus. The original
derivative, all-real-time derivative identification, appropriate domain,
self-adjointness and physical calibration are still unproved. Equality with
regularizedLog stays an explicit separate obligation for that series graph;
no frontier field is removed or weakened. Scaling survival remains the
independent primary analytic problem.

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
