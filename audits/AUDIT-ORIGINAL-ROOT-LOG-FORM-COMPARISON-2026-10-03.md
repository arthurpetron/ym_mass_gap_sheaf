# ORIGINAL quotient/logPartial: actual two-sided finite diagonal comparison

The whole-project goal remains nontrivial continuum Yang--Mills on R^4 for
every compact simple group, with SAME-theory QFT axioms and a positive
physical Hamiltonian mass gap. It is OPEN. This increment constructs the
two-sided ORIGINAL finite diagonal estimate, not the norm/limit join,
derivativeAction=regularizedLog, physical calibration or continuum scaling.

## Literal map pins and retained finite tail

All source paths in this section have prefix `lean/YMGap/Continuum/`.
`BF4WilsonAllNomeRootLogMapPins.lean:46`, `differenceQuotient_diagonal_pin`,
proves B(x,Q_depth x)=N*moment(depth,x,N,1), N=2^depth. :77,
`finiteLog_diagonal_pin`, identifies the ACTUAL original coarse-defect
polynomial sum with B(x,logPartial_M x). The exponent is k+1 and scalar
invSucc(k), exactly as in the EXISTING map. All depths and M=0 are included.

`BF4WilsonAllNomeRootMomentTelescope.lean:51`, `finiteMomentSum`, is a
literal finite sum of ORIGINAL moments. :56, `finiteMomentSum_retained`,
proves the exact telescope, retaining its final nonnegative endpoint:

    sum_(i<r) moment(k+1,l+i)+moment(k,l+r)=moment(k,l).

:92, `weightedMomentTail`, starts at defect degree two with coefficient
invSucc(i+1). :110, `weightedMomentTail_half_bound`, bounds every term
by half times its original unweighted moment. :125, `originalTail`,
multiplies that finite tail by ofNat(N). :130,
`originalTail_quadratic_bound`, proves Tail<=(N*half)*moment(N-1,2)
for 0<N, including empty tails. The checked original `8/N` budget is
`BF4WilsonAllNomeRootLogTail.lean:76`, `root_quadratic_tail_bound`.

## ORIGINAL F pays the complete signed S-form

`BF4WilsonAllNomeRootLogSignedBudget.lean:55`, `coarseMoment_norm_bound`,
retains the EXISTING coarse moments and proves C(0,j)<=Bxx. :66,
`original_f_form_pin`, identifies the ACTUAL original F form with
invSucc(M)*C(0,M+1)-Phi(N,S). :91, `original_s_form_upper`, combines
that pin and proved F positivity; :100, `original_s_signed_budget`, gives

    0<=Phi(N,S)<=invSucc(M)*Bxx.

These statements include M=0, depth zero and the boundary kernel. No
favorable sign, norm estimate or positive spectral floor is assumed.

## Actual error decomposition and both bounds

`BF4WilsonAllNomeRootLogFormComparison.lean:77`, `finiteLog_root_tail_pin`,
separates the first term from the ORIGINAL finite root series. :99,
`original_s_diagonal_pin`, identifies the complete S-form with
quotientDiagonal+Tail-logDiagonal. :123, `diagonalError`, uses the EXISTING
completed subtraction and pairing of the actual two finite maps. :128,
`diagonalError_pin`, proves, for M>0,

    E=B(x,(logPartial_M-Q_depth)x)=Tail-Phi(N,S).

At depth=d+2, N=2^(d+2), :138, `diagonalError_upper`, and :152,
`diagonalError_lower`, construct

    -invSucc(M)*Bxx <= E <= (2*half^d)*Bxx.

The upper coefficient 2*half^d is the computed 8/N. The tail is finite;
the retained endpoint is not discarded before its positivity is proved.
Only M>0 is required for the series decomposition; no M=0 error identity
is claimed. This suffices for subsequent limit cutoffs. No surrogate action,
operator inverse, functional-calculus input or boundary-kernel exclusion.

## Exact remaining frontier

The checked generic symmetric form-to-norm principle must still be applied
to this ACTUAL finite difference, then its explicit error coefficient joined
to the EXISTING quotient/log limit moduli. No equality of the limiting maps
is claimed here. These are the next backward proof targets, not hypotheses
on a new wrapper.

The independent forward frontier is unchanged: complete original signed
cost relative to SAME OWN variance, or a retained macro ratio, on a JUSTIFIED
changing family. No producer for it is supplied. Continuum survival,
physical calibration, full QFT, every-group construction and Clay remain OPEN.

## Focused verification boundary

Four NEW targets passed serialized focused checks, reporting 21 gates,
all within {propext, Quot.sound}. Root reviewed all four complete sources;
Sol supplied the retained telescope, literal map pins and S budget.
Reviews are not proofs. All four accepted a-logs exited zero and contain
no error, warning, sorryAx or PANIC.

Launches used `scripts/safe_lean_build.py`, one worker, 20-GiB cap and
12-GiB reserve, after fresh memory/process/swap checks: 83--84% free,
swap zero. No concurrent build, full root/tree build, broad audit/guard
or progress metric. Root imports are registration-only. No sorry, axiom,
frontier weakening, CI or exact canonical chart change.

| Source | SHA-256 |
| --- | --- |
| BF4WilsonAllNomeRootMomentTelescope | 6a051baf190dcac5128be4f3874062585b3ea330371d2b75bc4128c2fe045fcb |
| BF4WilsonAllNomeRootLogMapPins | af4c7f71b70209b9ec97d9bbd14065346901d4ecc38e908905da1a8a486fef0a |
| BF4WilsonAllNomeRootLogSignedBudget | 81b1e81e49c99c4460c8b2392efcad4bfac80564203d4f6c1afd6844004ddd27 |
| BF4WilsonAllNomeRootLogFormComparison | a3ba7143e54c45b62c75ced47bf8321be8b914a30bf564307ebddbdc7256dd1c |

| Accepted focused log | SHA-256 |
| --- | --- |
| /tmp/ym-original-root-moment-telescope-20261003-a.log | 5fb3e7d2342df613a03d10463b2ad51bbaa2666d849758c09a316c95b6a22cce |
| /tmp/ym-original-root-log-map-pins-20261003-a.log | 74cdeb6bb21569a3be4bde9fc1178caad38a231fed360cf83972f84998c46b96 |
| /tmp/ym-original-root-log-signed-budget-20261003-a.log | e3c679cfbbfa5fc5ff0041d739d9f3423d46840c2ce97e953442d728538d0e85 |
| /tmp/ym-original-root-log-form-comparison-20261003-a.log | 013beff29341c33e17eb43a43ecce37753ca690ebe4cbc36629a5c4062074a42 |

Canonical first-chart SHA-256 remains
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.
