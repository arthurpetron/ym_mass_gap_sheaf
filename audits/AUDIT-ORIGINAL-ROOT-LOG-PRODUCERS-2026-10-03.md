# Finite producers for the SAME original derivative/log comparison

The whole-project goal remains nontrivial continuum Yang--Mills on R^4,
for every compact simple group, with SAME-theory QFT axioms and a positive
physical Hamiltonian mass gap. It is OPEN. These results pay finite algebraic
parts of the proposed identification of two EXISTING original-carrier maps;
they do not prove that identification or physical scaling.

## Current increment: ORIGINAL finite S/F identities

Set N=n+1, u=1-h and D=1-u^N. The ACTUAL computed coefficient data are

    S=N*sum_(k<N*M) h^(k+1)/(k+1)-sum_(k<M) D^(k+1)/(k+1),
    F=D^(M+1)/(M+1)-u^N*S.

The following are now kernel-checked, for every n,m:Nat, including N=1,
M=0 and both scalar endpoints. No interval premise or division by u is used.

- `lean/YMGap/Constructive/QPolyFiniteGeometric.lean:23`,
  `geometricPolynomial`, constructs the original finite geometric row;
  :35, `geometric_telescope`, proves `(1-p)*sum_(k<n)p^k=1-p^n`
  coefficientwise; :51, `polynomialPower_eval`, pins its constructive power.
- `lean/YMGap/Constructive/QPolyFiniteLogDerivative.lean:23`, `finiteLog`,
  computes the original truncated series; :34, `finiteLog_derivative`, proves
  its FORMAL derivative equals p' times that geometric row; :56,
  `finiteLog_eval`, pins the actual finite rational sum.
- `lean/YMGap/Constructive/QPolyRootLogDifference.lean:31`,
  `rootLogDifference`, computes ORIGINAL S; :121, `rootDefect_derivative`,
  proves D'=N*u^(N-1); :134, `rootLogDifference_derivative`, computes S';
  :156, `rootLogDifference_cleared_derivative`, proves
  `u*S'=N*(D^M-h^(N*M))` at EVERY padded coefficient.
- `lean/YMGap/Constructive/QPolyRootLogInitial.lean:23`, `rootLogRemainder`,
  computes ORIGINAL F; :56, `rootPower_zero`, and :61, `rootDefect_zero`,
  prove its literal endpoint data; :69, `rootLogDifference_zero`, and :85,
  `rootLogRemainder_zero`, calculate S(0)=F(0)=0 from finite evaluation pins.
- `lean/YMGap/Constructive/QPolyRootLogRemainderDerivative.lean:96`,
  `rootLogRemainder_derivative`, proves `F'=N*u^(N-1)*(S+h^(N*M))` from
  ORIGINAL S's cleared derivative, not from an assumed sign or replacement.
- `lean/YMGap/Constructive/QPolyComplementCancellation.lean:45`,
  `complement_mul_injective`, recovers all coefficients after multiplication
  by the actual `[1,-1]`. Its adjacent-coefficient induction has no inverse,
  support-degree guard, interval premise or classical choice.

Cancellation is at the POLYNOMIAL level, BEFORE original-root substitution.
No injectivity of the actual operator is asserted; its boundary kernel is
retained. No positive S/F row, positive S/F form, log/derivative equality,
changing-family signed estimate or physical gap is claimed in this increment.

## Forward constructions

`lean/YMGap/Constructive/QPolyPositivePrimitive.lean:38`, `primitive`,
computes an ACTUAL finite rational coefficient list by the positive recursion

    I(0,b)=h^(b+1)/(b+1),
    I(a+1,b)=(1-h)^(a+1)*h^(b+1)/(b+1)
             +(a+1)*I(a,b+1)/(b+1).

Its coefficientwise formal derivative is exactly (1-h)^a*h^b, its initial
value is zero, and its evaluation is nonnegative on the CLOSED interval
[0,1]. No analytic integration, mean-value theorem or choice is used.
`derivative_initial_unique` proves that derivative plus initial value
determine the ACTUAL finite polynomial. Thus later S/F identifications must
pin to the original polynomial, not substitute an arbitrary positive one.

`lean/YMGap/Continuum/RootLogFiniteTail.lean:57`, `partial_retained_tail`,
uses the EXISTING scalar partial sums p_m and proves

    p_(m+1)(u)+(1-u)^(m+2)/2 <= u*(1-u)+(1-u)^2/2.

Both endpoints are included. Its quadratic tail follows by removing only
the nonnegative retained remainder. This finite statement does not import
an operator from the older thermodynamic carrier.

Its :86, `complementaryPowerSum`, also computes P_n=sum_(k<n)(u^k+h^k),
where h=1-u. Its :100, `complementary_power_defect`, proves

    1-u^(n+1)-h^(n+1)=u*h*P_n.

The empty sum and both endpoints are included; :89,
`complementaryPowerSum_nonnegative`, proves P_n>=0 on [0,1]. This finite
telescope removes the binomial middle-row expansion from the proposed
S-derivative numerator. By itself it proves neither the original S derivative
identity nor coefficient/root-action transport. The first is now independently
proved by the coefficient module above; the latter remains OPEN.

`lean/YMGap/Continuum/BF4WilsonAllNomeRootLogTail.lean:76`,
`root_quadratic_tail_bound`, uses the ACTUAL mixed moments on the original
all-nome completion. With N=2^(d+2), for every original state x,

    (N/2)*B(x,R^(N-1)*(I-R)^2*x) <= (8/N)*B(x,x).

The coefficient 8/N is the computed rational 2*half^d. The proof retains
the original root, state and pairing, uses `weighted_order` with order two
and n=2^d, and propagates time monotonicity to N-1. It requires no supplied
form estimate or positive norm floor. It replaces the unnecessary sharp
scalar binomial ceiling in the operator route; no physical mass follows.

## Backward algebra on the SAME completion

`lean/YMGap/Continuum/BF4WilsonAllNomeSymmetricFormNorm.lean:127`,
`symmetric_form_norm_bound`, proves a genuine algebraic implication:
for an add/sub-linear symmetric map E and a positive rational e, the actual
two-sided diagonal form estimates imply

    -e*B(z,z) <= B(z,E z) <= e*B(z,z) for ALL z
      ==> B(E x,E x) <= e^2*B(x,x) for ALL x.

Polarization and the test y=recipPos(e)*E x give the result. Only a positive
rational reciprocal is used; no inverse operator, scalar linearity premise
on E, arbitrary real division or spectral theorem is required. The diagonal
estimates are explicit premises, NOT constructed for the root/log difference
in this module. The intended E is the literal logPartial-differenceQuotient.

## Declaration anchors

- `lean/YMGap/Constructive/QPolyPositivePrimitive.lean:27`, `polynomialPower`;
  :63, `power_derivative_succ`; :158, `primitive_derivative`;
  :237, `primitive_nonnegative`; :283, `primitive_zero`;
  :320, `derivative_initial_unique`.
- `lean/YMGap/Continuum/RootLogFiniteTail.lean:75`, `partial_quadratic_tail`.
- `lean/YMGap/Continuum/BF4WilsonAllNomeRootLogTail.lean:38`,
  `moment_time_antitone`.
- `lean/YMGap/Continuum/BF4WilsonAllNomeSymmetricFormNorm.lean:96`,
  `symmetric_form_pair_bound`.
- Existing `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDefectDecay.lean:236`,
  `weighted_order`; `BF4WilsonAllNomeDyadicEnergy.lean:198`,
  `half_power_normalizes` (same directory).

## Exact remaining meeting point

The ORIGINAL S/F derivative identities and zero initial values are now proved.
Still OPEN: their explicit positive expansions and transport to the ACTUAL root
actions. Those supply the two-sided form comparison with error
8/N+invSucc(M). The norm principle and existing approximation moduli would
then identify derivativeAction and regularizedLog on the SAME carrier,
including its boundary kernel. This equality is NOT claimed here.
The next producer must turn CoeffEqv into a diagonal functional on the existing
depth-dependent mixed moments, with the monomial pin
Phi(u^a*h^b)=moment(d,x,a,b) and literal pins to the existing operators.
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDefectDecay.lean:188`,
`moment_split`, is the available recursive identity; :181,
`moment_nonnegative`, is the positive consumer. These functional/map pins
are still OPEN. The older `BF4WilsonAllNomeDefectPolynomial.lean:96`,
`action`, is hardwired to I-T(1), not the depth-dependent root defect;
it supplies proof patterns, not that missing producer (same directory).

The independent forward input remains the complete action-dependent signed
cost versus SAME OWN variance, or a retained macro ratio, on a JUSTIFIED
changing family. No new estimate for that input is supplied by these finite
algebraic results. Continuum survival, physical calibration, full QFT,
every-group construction and Clay closure remain OPEN.

## Previous four-source verification boundary

The four targets' latest accepted serialized focused logs report 18 printed
gates: five computed definitions are axiom-free; thirteen gates use only
{propext, Quot.sound}. All accepted checks exited zero. The initial four
checks supplied 15 gates in `a0d9897`; the follow-up telescope adds three.
Accepted logs contain no error, warning, sorryAx or
PANIC. Root reviewed all four full sources. Sol agents built the primitive
and polarization proof; independent Sol mathematics and Luna static review
confirmed the endpoint and original-carrier scope. Reviews are not proofs.

All checks used `scripts/safe_lean_build.py`, one worker, 20-GiB worker cap
and 12-GiB reserve, with fresh capacity/process checks before each launch.
Observed free-memory percentage was 83--84%, swap zero. No concurrent build,
full root/tree build, broad audit/guard or progress metric ran. Root imports
are registration-only. No sorry, axiom, canonical frontier weakening, CI
change or chart-claim closure was introduced.

| Source | SHA-256 |
| --- | --- |
| QPolyPositivePrimitive | 98010e2a92222575b222362f0c74c7e80f851cc750a8189cf6a26e129d3058e1 |
| RootLogFiniteTail | cbc4419dc9aedb44177af39a9efe7b83bfdabf4a61c35a647d204fe88ac5bb56 |
| BF4WilsonAllNomeRootLogTail | 172ce83c95c4410e6b728d598b7c4253e4450ee9b8910f7c48b37eb9d5cbb72f |
| BF4WilsonAllNomeSymmetricFormNorm | 462739e843a8eabebb1fbc200617eb8796508aea58a7371f836161a604fcba3b |

| Accepted focused log | SHA-256 |
| --- | --- |
| /tmp/ym-positive-poly-primitive-20261003-b.log | 1902f01d5eb0ea71cd201e5d3f86252b1ca590685093774962fdc25fc8f08c5f |
| /tmp/ym-root-log-complementary-telescope-20261003-a.log | bd22e2a39a23312a11670eadcd322a44c162c0eec570f395f9f4cc9e962d62d4 |
| /tmp/ym-original-root-log-tail-20261003-b.log | 692dc800c53f27869fd3229421fab6ad038847afbfcf67a84d79fcf33ce17e6a |
| /tmp/ym-original-symmetric-form-norm-20261003-a.log | 483b4308bbcc171d49ff399a427112f1267dbdf73067367ca2d425343660845b |

The primitive a-log had local multiline case-layout errors; the root-tail
a-log retained an induction-side inequality hypothesis. Both were corrected
without changing mathematical statements, axioms or resources, and only the
passing b-logs are evidence for those sources. The finite-tail a-log passed
before an unused import was removed; the b-log verifies the initial tail.
The complementary-telescope a-log verifies the final extended tail source
with all five gates, passing on its first check.
Canonical first-chart SHA-256 remains
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.

## Current six-source verification boundary

The six NEW sources passed six serialized focused checks. Their accepted
logs report 19 new printed gates: six computed definitions are axiom-free;
thirteen theorem gates use only {propext, Quot.sound}. With the preceding
four sources, current ten-source coverage is 37 gates: eleven axiom-free,
twenty-six within the permitted gate. All accepted checks exited zero and
contain no error, warning, sorryAx or PANIC. Root reviewed the complete six
sources; Sol supplied finite sums, endpoint pins and coefficient cancellation;
independent Luna source/log/hash review passed. Reviews are not proofs.

Each launch used the same monitored single worker, 20-GiB cap and 12-GiB
reserve, after fresh memory/process/swap checks. Observed free-memory
percentage was 83--84%, swap zero. No concurrent build, full root/tree build,
broad audit/guard or progress metric ran. Root imports are registration-only;
no sorry, axiom, frontier weakening, CI change or exact chart-claim closure.

| New source | SHA-256 |
| --- | --- |
| QPolyFiniteGeometric | bd607d264214d05256e7211c712e8ac493f1e52f224546c45658939e1eb26913 |
| QPolyFiniteLogDerivative | 9676596e7d1b0922755ea64d1cf05e7073db4a00ae4bebd35c772bcd066bdc4f |
| QPolyRootLogDifference | d65918b8d8af8110900184591a8b7dc9d71714199292fa4694ed80930996f2d5 |
| QPolyRootLogInitial | 4d89d095c04353c314fd95897b2b93f072687b5f40e6b885a242da6f65d4ccb5 |
| QPolyRootLogRemainderDerivative | b7a633d0e4126024b66b6d0b5f758839ce1dad92b4f201988dc9074c6ce98e5f |
| QPolyComplementCancellation | 62ca089f2b2ca4dbd3168a038d64cc5ef850d7e044fe40cbd48746ea0acfe651 |

| New accepted focused log | SHA-256 |
| --- | --- |
| /tmp/ym-finite-geometric-20261003-a.log | 889629e7fd69e29bad41f10d3d1c5a22d085c478b5ca95f5b46be90ca3da96de |
| /tmp/ym-finite-log-derivative-20261003-a.log | 58356880dad3b343d88f715c100d93705c40b94da7bcbb0d8fc9b6cc1aa05efc |
| /tmp/ym-original-S-coefficients-20261003-b.log | e29c7f6892de541169107cdb532b7e502312a033bbd7481e32f04ec922af5884 |
| /tmp/ym-original-root-log-initial-20261003-a.log | a693b009a2c323f0552022448ba7bb89222caf06a6a68267ed7726cb841fab9f |
| /tmp/ym-original-F-coefficients-20261003-b.log | a250aeda5d814d594577bdf9d43dd0105c9c322e9bf75dd9b092329c295f585e |
| /tmp/ym-complement-coefficient-cancellation-20261003-a.log | 573ad731bffa6d81115dede8a0aafde5ca84cfe13f059e1f63539e32763f8d1f |

The S a-log had an incorrectly parenthesized theorem composition; the F a-log
needed an explicit padded-zero annotation. Both were local elaboration fixes,
with no statement, axiom or resource change. Only the accepted b-logs provide
evidence for those sources. The other four sources passed their first checks.
The canonical first-chart hash remains the value above; no ASCII reprint.
