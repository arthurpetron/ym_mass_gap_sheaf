# ORIGINAL S/F positivity reaches the actual root and coarse moments

The whole-project goal remains nontrivial continuum Yang--Mills on R^4 for
every compact simple group, with SAME-theory QFT axioms and a positive
physical Hamiltonian mass gap. It is OPEN. This increment proves an actual
coefficient-to-moment bridge and coarse pins, not the complete root/log
comparison, equality of the two limiting maps, or physical scaling.

## Actual constructed functional and meeting point

For the EXISTING all-nome completion, depth-dependent original root and
defect h=I-R_depth, define the finite signed diagonal functional

    Phi(k,p,l)=sum_i p_i*moment(depth,x,k,l+i).

`lean/YMGap/Continuum/RCPolynomialFunctional.lean:77`, `formFrom`, is the
finite coefficient-list recursion. :93, `formFrom_coeffEqv`, proves equality
for actual padded rational coefficient equivalence, including lists of
unequal length. :109, `formFrom_padd`; :126, `formFrom_pscale`; :136,
`formFrom_pneg`; and :140, `formFrom_psub`, prove the finite linear laws.
This generic module creates no vector carrier or time action.

`lean/YMGap/Continuum/BF4WilsonAllNomeRootPolynomialForm.lean:38`, `form`,
substitutes the ORIGINAL mixed moments. :41, `form_coeffEqv`, transports
coefficient equivalence through them. :105, `form_coordinate`, shifts the
defect index under multiplication by h. :111, `form_split`, extends the
ACTUAL moment split linearly to signed polynomials. :122, `form_complement`,
shifts ROOT time under multiplication by u=1-h. Thus :144, `form_monomial`,
proves the exact pin

    Phi(k,u^a*h^b,l)=moment(depth,x,k+a,l+b).

:162, `rowForm`, returns the literal finite weighted sum of these original
moments. :167, `form_row`, identifies it with the actual polynomial form;
:177, `rowForm_nonnegative`, uses every computed nonnegative weight and
`BF4WilsonAllNomeDyadicDefectDecay.lean:181`, `moment_nonnegative`.

The previous increment's ORIGINAL coefficient pins therefore meet the
actual carrier: :189, `original_s_nonnegative`, and :195,
`original_f_nonnegative`, prove ORIGINAL S/F form positivity at EVERY
shifted pair of indices, every depth, state, width, 0<w<1 and n,m:Nat.
No positive surrogate, scalar-only positivity substitution, functional
calculus, operator inverse, spectral floor or kernel exclusion is assumed.
Phi is linear; no multiplicativity claim is introduced.

## Literal coarse-defect and original-time pins

`lean/YMGap/Continuum/BF4WilsonAllNomeRootCoarseMoment.lean:62`,
`form_power_complement_mul`, shifts the root-time index by an arbitrary
complement power multiplying an arbitrary polynomial. :78, `full_stride`,
pins EVERY full root stride to the EXISTING completed original time.
:97, `form_coarseDefectPower`, proves, for N=2^depth,

    Phi(k*N,(1-u^N)^j,0)=mixedMoment(x,k,j).

:125, `form_coarse_one_time`, proves the additional literal time-one pin

    Phi(0,u^N*(1-u^N)^j,0)=mixedMoment(x,1,j).

The induction retains ALL coarse time indices and uses the original moment
split. It works at every depth, including zero, all defect exponents and
the boundary kernel; no multiplicativity or cancellation of an operator.

## Exact remaining frontier

The finite-tail telescope, literal diagonal comparison of the two EXISTING
maps `differenceQuotient` and `logPartial`, and derivativeAction=regularizedLog
remain OPEN at this checkpoint. The already checked root `8/N` tail and
symmetric form-to-norm principle remain downstream consumers, not proofs
of those missing bounds.

The independent forward frontier is unchanged: complete original signed
cost relative to SAME OWN variance, or a retained macro ratio, on a JUSTIFIED
changing family. No estimate for it is supplied here. Continuum survival,
physical calibration, full QFT, every-group construction and Clay remain OPEN.

## Focused verification boundary

Three NEW targets passed serialized focused checks, reporting 31 gates, all
within {propext, Quot.sound}. The root reviewed the complete three sources;
Sol supplied the generic functional and the coarse pins and independently
reviewed the same-root route. Reviews are not proofs. Accepted logs exited
zero and contain no error, warning, sorryAx or PANIC.

All launches used `scripts/safe_lean_build.py`, one worker, 20-GiB cap and
12-GiB reserve, after fresh memory/process/swap checks. Observed free-memory
percentage was 82--84%, swap zero. No concurrent build, full root/tree build,
broad audit/guard or progress metric ran. Root imports are registration-only.
No sorry, axiom, frontier weakening, CI or exact canonical chart change.

| Source | SHA-256 |
| --- | --- |
| RCPolynomialFunctional | b65be37c179680ee139f84e4233ea3cee9a90040a81243e7d06af6b93ed9fcf5 |
| BF4WilsonAllNomeRootPolynomialForm | 49867c6fb5d47567df402e2121af68cae529f19c85928f4fb116294b4d11cab4 |
| BF4WilsonAllNomeRootCoarseMoment | 61b773d2e922a2552bce82a1298f249f8fd39591e91886918b6d604e97ecb87f |

| Accepted focused log | SHA-256 |
| --- | --- |
| /tmp/ym-RC-polynomial-functional-20261003-b.log | e62b8862c71a56ce7d428052d6c2f33cfcb269846a0ac5b269cc9027853ac0f2 |
| /tmp/ym-original-root-polynomial-form-20261003-b.log | cb5885ab4ce5537b68c6981c0ba8fe0242784ec4a826c7492c713a870ab52895 |
| /tmp/ym-original-root-coarse-moment-20261003-a.log | c36b436e77729f0cf31c96ed98bc22b206bbca5fba55d15742d37e46813d247f |

The generic a-log exposed an unavailable binary congruence helper, replaced
by two unary congruences. The actual-root a-log needed unfolding RCnonneg
before a rewrite. Accepted b-logs verify unchanged mathematical statements;
no resource, axiom or mathematical premise was changed.
Canonical first-chart SHA-256 remains
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.
