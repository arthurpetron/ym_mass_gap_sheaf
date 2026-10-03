# Finite producers for the SAME original derivative/log comparison

The whole-project goal remains nontrivial continuum Yang--Mills on R^4,
for every compact simple group, with SAME-theory QFT axioms and a positive
physical Hamiltonian mass gap. It is OPEN. These results pay finite algebraic
parts of the proposed identification of two EXISTING original-carrier maps;
they do not prove that identification or physical scaling.

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

`lean/YMGap/Continuum/RootLogFiniteTail.lean:55`, `partial_retained_tail`,
uses the EXISTING scalar partial sums p_m and proves

    p_(m+1)(u)+(1-u)^(m+2)/2 <= u*(1-u)+(1-u)^2/2.

Both endpoints are included. Its quadratic tail follows by removing only
the nonnegative retained remainder. This finite statement does not import
an operator from the older thermodynamic carrier.

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
- `lean/YMGap/Continuum/RootLogFiniteTail.lean:73`, `partial_quadratic_tail`.
- `lean/YMGap/Continuum/BF4WilsonAllNomeRootLogTail.lean:38`,
  `moment_time_antitone`.
- `lean/YMGap/Continuum/BF4WilsonAllNomeSymmetricFormNorm.lean:96`,
  `symmetric_form_pair_bound`.
- Existing `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDefectDecay.lean:236`,
  `weighted_order`; `BF4WilsonAllNomeDyadicEnergy.lean:198`,
  `half_power_normalizes` (same directory).

## Exact remaining meeting point

Still OPEN: the coefficient identities for the ORIGINAL S/F polynomials,
their explicit positive expansions and their transport to the ACTUAL root
actions. Those supply the two-sided form comparison with error
8/N+invSucc(M). The norm principle and existing approximation moduli would
then identify derivativeAction and regularizedLog on the SAME carrier,
including its boundary kernel. This equality is NOT claimed here.

The independent forward input remains the complete action-dependent signed
cost versus SAME OWN variance, or a retained macro ratio, on a JUSTIFIED
changing family. No new estimate for that input is supplied by these finite
algebraic results. Continuum survival, physical calibration, full QFT,
every-group construction and Clay closure remain OPEN.

## Verification boundary

Four accepted serialized focused checks exited zero, with 15 new printed
gates: four computed definitions are axiom-free; eleven gates use only
{propext, Quot.sound}. Accepted logs contain no error, warning, sorryAx or
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
| RootLogFiniteTail | 98594dcbd70accb7605573649f0d17d96d7e15fd212a2f09bb0705d4acdb90b7 |
| BF4WilsonAllNomeRootLogTail | 172ce83c95c4410e6b728d598b7c4253e4450ee9b8910f7c48b37eb9d5cbb72f |
| BF4WilsonAllNomeSymmetricFormNorm | 462739e843a8eabebb1fbc200617eb8796508aea58a7371f836161a604fcba3b |

| Accepted focused log | SHA-256 |
| --- | --- |
| /tmp/ym-positive-poly-primitive-20261003-b.log | 1902f01d5eb0ea71cd201e5d3f86252b1ca590685093774962fdc25fc8f08c5f |
| /tmp/ym-root-log-finite-tail-20261003-b.log | d67b7048e5b153759a7a5fdc79a52d30c38320fcb9414bf9386a65c65fc1a93f |
| /tmp/ym-original-root-log-tail-20261003-b.log | 692dc800c53f27869fd3229421fab6ad038847afbfcf67a84d79fcf33ce17e6a |
| /tmp/ym-original-symmetric-form-norm-20261003-a.log | 483b4308bbcc171d49ff399a427112f1267dbdf73067367ca2d425343660845b |

The primitive a-log had local multiline case-layout errors; the root-tail
a-log retained an induction-side inequality hypothesis. Both were corrected
without changing mathematical statements, axioms or resources, and only the
passing b-logs are evidence for those sources. The finite-tail a-log passed
before an unused import was removed; the b-log verifies the frozen source.
Canonical first-chart SHA-256 remains
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.
