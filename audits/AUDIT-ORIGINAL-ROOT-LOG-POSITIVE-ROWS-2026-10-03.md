# Computed positive rows identify the ORIGINAL finite S and F

FOLLOW-UP: coefficient invariance, the ACTUAL root monomial pin, ORIGINAL
S/F form positivity, and coarse-defect/time-one moment pins are now checked
in `audits/AUDIT-ORIGINAL-ROOT-POLYNOMIAL-FORM-2026-10-03.md`. The evidence
below records this producer checkpoint; its complete comparison and physical
scaling obligations remain OPEN.

The whole-project goal remains nontrivial continuum Yang--Mills on R^4 for
every compact simple group, with SAME-theory QFT axioms and a positive
physical Hamiltonian mass gap. It is OPEN. This increment completes the
finite positive-row producer for the original root/log comparison, NOT the
coefficient-to-operator lift, operator equality or physical scaling.

## Actual constructed data and proved meeting point

Use N=n+1, u=1-h and D=1-u^N. The ORIGINAL polynomials are unchanged:

    S=N*sum_(k<N*M) h^(k+1)/(k+1)-sum_(k<M) D^(k+1)/(k+1),
    F=D^(M+1)/(M+1)-u^N*S.

`lean/YMGap/Constructive/QPolyRootLogPositiveRows.lean:43`, `sRow`, and
:47, `fRow`, compute finite lists of rational weights and u/h exponents.
:122, `original_sRow`, and :139, `original_fRow`, prove their expanded
polynomials are coefficientwise equivalent to ORIGINAL S and F. :162,
`nonnegative_sRow`, and :165, `nonnegative_fRow`, prove every computed
weight is nonnegative. These results hold for every n,m:Nat, including
N=1 and M=0. No sign, spectral floor or analytic input is assumed.

POSITIVE means nonnegative weights multiplying u^a*h^b. It does NOT mean
that all coefficients after expansion in the single variable h are positive.
This distinction matters for the actual mixed-moment consumer.

The shorter derivative factor is constructed as literal row data:

    P=sum_(k<n)(u^k+h^k),
    K=sum_(i<M) D^(M-1-i)*h^(N*i),
    S'=N*h*P*K.

:39, `derivativeRow`, computes that row; :98, `original_derivative_row`,
proves the EXACT derivative pin by combining the original cleared identity,
both coefficient telescopes, and coefficient cancellation of u. Its
termwise positive primitive, with the proved zero initial value, determines
ORIGINAL S by `derivative_initial_unique`. The row for
`F'=N*u^(N-1)*(S+h^(N*M))` is then computed from THAT identified S row and
integrated in the same way. No arbitrary positive polynomial replaces S/F.

## Supporting declarations

- `lean/YMGap/Constructive/QPolyFinitePowerDifference.lean:20`,
  `powerDifferenceRow`; :36, `powerDifference_telescope`; :67,
  `polynomialPower_add`; :83, `polynomialPower_iterated`.
- `lean/YMGap/Constructive/QPolyComplementaryTelescope.lean:25`,
  `complementaryPowerPolynomial`; :77, `root_defect_positive_factor`;
  :86, `complementary_power_defect`. These are coefficient identities, not
  merely rational interval evaluation tests.
- `lean/YMGap/Constructive/QPolyCoefficientEvaluation.lean:37`,
  `coefficient_eval`, respects padded coefficients at every rational argument.
- `lean/YMGap/Constructive/QPolyUHRow.lean:34`, `polynomial`; :68,
  `monomial_multiply`; :83, `polynomial_append`; :91, `polynomial_scale`;
  :99, `polynomial_shift`; :110, `polynomial_multiply`; :123,
  `polynomial_power`. These prove the row operations really expand to the
  existing rational polynomial carrier.
- `lean/YMGap/Constructive/QPolyUHRowPrimitive.lean:24`, `primitiveRow`;
  :31, `polynomial_primitiveRow`; :60, `integralRow`; :66,
  `integralRow_derivative`; :87, `integralRow_zero`. The data are finite
  positive integration-by-parts recursions, not an integral oracle.
- `lean/YMGap/Constructive/QPolyUHRowFiniteSums.lean:25`, `geometricRow`;
  :30, `differenceRow`; :34, `polynomial_geometricRow`; :49,
  `polynomial_differenceRow`. Computed finite sums match their polynomial
  counterparts and propagate nonnegative weights.

The earlier derivative/initial identities are recorded in
`audits/AUDIT-ORIGINAL-ROOT-LOG-PRODUCERS-2026-10-03.md`. Its positive-row
obligation is now discharged; its actual-root transport obligation is not.

## Exact residue and downstream consumer

Still OPEN: coefficient invariance of the ORIGINAL diagonal functional,
its monomial identity Phi(u^a*h^b)=moment(d,x,a,b), and literal pins to the
EXISTING root difference quotient and log partial. The available actual
consumers are `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDefectDecay.lean:181`,
`moment_nonnegative`, and :188, `moment_split`. No operator injectivity may
be assumed: cancellation above takes place BEFORE operator substitution.

The old `lean/YMGap/Continuum/BF4WilsonAllNomeDefectPolynomial.lean:96`,
`action`, is hardwired to I-T(1), not the depth-dependent root defect. It is
not the missing depth-parametric producer. Scalar interval positivity alone
also supplies no original-operator lift. Once the exact lift is proved, the
existing root tail and polarization consume the form error `8/N+invSucc(M)`.
DerivativeAction=regularizedLog remains OPEN.

The independent forward frontier is unchanged: complete original signed
cost relative to SAME OWN variance, or a retained macro ratio, on a JUSTIFIED
changing family. No estimate for it is supplied here. Continuum survival,
physical calibration, full QFT, every-group construction and Clay remain OPEN.

## Focused verification boundary

Seven NEW targets passed serialized focused checks, reporting 50 gates:
sixteen are axiom-free; thirty-four use only {propext, Quot.sound}. Root
reviewed the complete seven sources. All accepted checks exited zero and
contain no error, warning, sorryAx or PANIC. Independent Sol tasks supplied
the two coefficient telescopes, finite row sums and primitive rows; Luna
supplied evaluation and performed independent static QA. Reviews are not proofs.

All launches used `scripts/safe_lean_build.py`, one worker, 20-GiB cap and
12-GiB reserve, after fresh memory/process/swap checks. Observed free-memory
percentage was 83--84%, swap zero. No concurrent build, full root/tree build,
broad audit/guard or progress metric ran. Root imports are registration-only.
No sorry, axiom, frontier weakening, CI or exact canonical chart change.

| Source | SHA-256 |
| --- | --- |
| QPolyFinitePowerDifference | 32af75cd250413041d6dd4115183f96bf5b3c2f1001249a07af27026e9eceae7 |
| QPolyComplementaryTelescope | d4ae60f12f4e0eb148b34bd7b3573e28ab2f55d059efff71854d9f31e3ac8524 |
| QPolyCoefficientEvaluation | b0d8cb4d534889291b9709a8324db1ff753746537df7c2b54da947df8a4f9546 |
| QPolyUHRow | 8b8895195bb586786403f65bde6d26f71fe676860286e4b46ba706e8106c265f |
| QPolyUHRowPrimitive | e7384ddb0a21e1e856d73298d68453a02ea10af76018452fb6ceec64db31e88c |
| QPolyUHRowFiniteSums | 505dd362c391ef77fc27c05520a18507f8ea20dc4c19854f174e734df7201d96 |
| QPolyRootLogPositiveRows | 512ecf7580272f3774b2b9f7c3623398d33c05280f61ef238ff5d8773bd4b1cb |

| Accepted focused log | SHA-256 |
| --- | --- |
| /tmp/ym-coefficient-power-difference-20261003-a.log | 2844dbced2ea666d625906af7a095c65a69d18883bb706181940ecf9550d1a25 |
| /tmp/ym-coefficient-complementary-telescope-20261003-a.log | be4c0b668cab76783118340958c9799e09cad199e0a64ce7d5c7827732b3ec35 |
| /tmp/ym-coefficient-evaluation-20261003-a.log | a38f32248c47d12f9cdc14e5e53a7f709cb67d68bee5d2f948b75fbf6cebcc54 |
| /tmp/ym-UH-row-algebra-20261003-b.log | 177d2bcfd2ec3d538a71c92066fd25799d550b1d7fbfa0a84b7691dd984623b0 |
| /tmp/ym-UH-row-primitives-20261003-a.log | c0af52901d222211639700aceaa4528b3abd0b547c15a4b54670879e835d9975 |
| /tmp/ym-UH-finite-sums-20261003-b.log | 627da4d23b67176b70c21d358130cd2aea455e954c10bc88c290516a2c4539b8 |
| /tmp/ym-original-SF-positive-rows-20261003-a.log | ba68fb4f85c2cfec846c9899b9d058d3ad601bc502cbafd5575d4f3e91cf4b43 |

The row-algebra a-log needed an explicitly closed constant positivity type;
the finite-row-sum a-log needed a multiline case-layout correction. Their
accepted b-logs verify the unchanged mathematical statements. Two evaluation
direction errors were corrected in static review before its first check.
No resource, axiom or mathematical premise was changed by these fixes.
Canonical first-chart SHA-256 remains
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.
