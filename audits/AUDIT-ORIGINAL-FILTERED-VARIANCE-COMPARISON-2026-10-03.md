# ORIGINAL finite filtered-variance comparison

## Mathematical route and scope

PROGRESS after `b0cc2fd`: five focused checks and independent mathematical
and evidence reviews passed. This increment proves a missing estimate needed to pay finite time-window
approximation errors relative to ONE original starting variance. It does not
assume that different finite chronological variances are equal.

At the SAME original cutoff K, nome w and width, set

```text
ell(p) = weightedMass(w,K,width,p),    S = T^d,
A_u = g_(n+u),                       A_t = g_(n+u+d) = S A_u,
b_u = T^u(g_n*psi),                  b_t = T^(u+d)(g_n*psi) = S b_u,
Z_u = ell(A_u^2),                    Z_t = ell(A_t^2),
B_u = ell(b_u^2),                    B_t = ell(b_t^2).
```

The existing terminal comparison at s=n+u-1, r=d, t=0 constructs
l*A_u <= S A_u <= U*A_u, with U-l <= eta*l and
eta=comparisonEta(w,width,n+u-1). Its actual positive certificates retain
the full spatial action. The checked result is

```text
Z_u*B_t <= (1+eta)^2*(Z_t*B_u).
```

This is an UPPER finite variance comparison, not a lower survival floor,
useful signed bulk estimate or changing-family/physical mass theorem.
Signed psi, B_u=0 and d=0 are included. No source-norm inverse or terminal
stationary eigenpin is used. The whole constructive continuum Yang--Mills
goal, including nontriviality, SAME-theory QFT axioms, physical Hamiltonian
mass and every compact simple group, remains OPEN.

## Proof ingredients

1. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSchurTest.lean:84`
   `original_block_terminal_schur_square_le`
   derives ell[(S(A*f))^2] <= U^2*ell[(A*f)^2] from the ORIGINAL two-copy
   conditional-square certificate, two upper-certificate insertions and
   actual weighted symmetry. f may be signed; no lower A floor is assumed.
2. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockWeightedContinuity.lean:98`
   `originalBlockTransfer_weighted_square_le`
   derives coarse weighted continuity from the actual T1 upper certificate.
   This coefficient retains K,w,width,d dependence and is used ONLY to
   pay reciprocal reconstruction error.
3. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalSchurClosure.lean:109`
   `original_block_terminal_schur_source_le`
   uses the constructed finite reciprocal tests and their geometric
   reconstruction to extend the sharp U^2 estimate to the ACTUAL b_u.
   Explicit coefficient transport identifies (A*phi)^2 with A^2*phi^2.
   Two constructive rational order-reflection arguments remove approximation
   error and the asymmetric-triangle slack. The coarse coefficient disappears.
4. `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredVarianceComparison.lean:163`
   `filtered_variance_cleared_le`
   combines the actual source Schur estimate with l^2*Z_u <= Z_t and
   U^2 <= (1+eta)^2*l^2. No l cancellation or norm division is needed.
5. `lean/YMGap/Continuum/BF4WilsonAllNomeOriginalVarianceComparison.lean:79`
   `originalOwnBlockVariance_comparison` proves the normalized bound for
   the ACTUAL existing own-centered padded-square observable. It divides
   ONLY by constructed positive chronological partitions, retaining one
   K=headCutoff(w)+stage and one stage OWN mean at both lags.

## Parameter and normalization boundary

`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalComparison.lean:94`
`comparisonEta` is explicitly
comparisonKappa(w,width)*mixRate(w,width)^(n+u-1). The final factor does not
name K, d or psi. It DOES depend on nome, width and starting terminal depth;
this is not a volume/spacing/coupling-uniform physical gap. Approximation
cutoffs inside the closure may depend on K,d and the original B_u, but no
such coefficient remains in the final inequality.

The positive original partitions give the equivalent normalized statement
B_t/Z_t <= (1+eta)^2*(B_u/Z_u). Only positive partitions are inverted;
B_u is not. The fifth theorem proves this normalization on the actual
`originalOwnBlockVariance`, rather than introducing a substitute quantity.

`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:93`
`originalOwnBlockVariance` uses the actual padded-square source shifted by
the stage's OWN odd mean c_n. Instantiation must keep that SAME c_n at both
lags. Replacing it with a future mean would change the source and would not
be licensed by the new comparison. Each lag retains its own Z0,Z1.

## Forward/backward frontier

The existing forward estimate is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreCost.lean:324`
`original_block_exact_score_cost_relative_tolerance`:

```text
D_t <= exactScoreSignedBulk_t + tau*(Z1_t*B_t),
tau = (zeta+delta)+epsilon.
```

The existing backward consumer is
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`
`original_window_budget_macro_ratio`, whose eventual finite-stage hypothesis
is 2*originalWindowCost(stage,u,u) <= (1-kappa)*originalOwnBlockVariance(stage,u).
Its normalized terms use DISTINCT chronological partitions and one SAME
stage OWN center. The new finite comparison controls the changing variances
in the approximation-error portion of this sum. It does not provide the
required useful signed estimate on the retained normalized exact-score bulk
TOGETHER WITH BOTH original Taylor remainders.

The bounded mathematical review found no unused cross-lag cancellation
in these declarations that supplies that analytic input. The actual
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:267`
`energy_identity` retains the original edge density and the dynamic
ratio source. It is not a bare kinetic increment or an incoming source-square
budget. This review is not a proof of impossibility; the needed estimate
remains a research frontier.

The next analytic producer remains OPEN, on a JUSTIFIED changing family.
Do not reintroduce Jensen debt as a prerequisite, replace signed cancellation
with unproved absolute caps, infer a survival lower bound from this upper
comparison or pass a growing source family through fixed-source convergence.
No exact canonical chart claim or frontier atom changes; no chart reprint.

## Verification and reviews

All five focused checks exited 0. Eight printed public gates have only
{propext, Quot.sound}; accepted logs contain no error, warning or sorryAx.
The sources contain no sorry/admit, new axiom, Classical, native_decide,
unsafe or noncomputable. Independent Sol semantic review and Luna evidence
QA both PASS. Reviews are separate from the kernel check.

| Module | Public declarations (source line) | Gates | Accepted log |
| --- | --- | ---: | --- |
| BF4ExactSlabFixedSpatialTerminalSchurTest | original_block_terminal_schur_square_le (84) | 1 | `/tmp/ym-terminal-schur-test-20261003-2.log` |
| BF4ExactSlabFixedSpatialBlockWeightedContinuity | transferStep_weighted_square_le (66), originalBlockTransfer_weighted_square_le (98) | 2 | `/tmp/ym-block-weighted-continuity-20261003-1.log` |
| BF4ExactSlabFixedSpatialTerminalSchurClosure | original_block_terminal_schur_source_le (109) | 1 | `/tmp/ym-terminal-schur-closure-20261003-5.log` |
| BF4ExactSlabFixedSpatialFilteredVarianceComparison | filteredTerminalBracket (82), filtered_terminal_partition_lower (121), filtered_variance_cleared_le (163) | 3 | `/tmp/ym-filtered-variance-comparison-20261003-1.log` |
| BF4WilsonAllNomeOriginalVarianceComparison | originalOwnBlockVariance_comparison (79) | 1 | `/tmp/ym-original-variance-comparison-20261003-3.log` |

Each module is in `lean/YMGap/Continuum/`. Checks used exactly:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --reserve-gib 12 \
  --check-worker-limit-gib 20 --status-seconds 300 \
  --log-file /tmp/<accepted-log> \
  --check lean/YMGap/Continuum/<module>.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/<module>.olean
```

Fresh process/swap/pressure observations preceded every launch: one compiler,
20 GiB worker ceiling, 12 GiB reserve, zero swap and 76--77% free memory.
No competing compiler/runner/test was found. No safety cutoff occurred.
Failed drafts were NOT accepted evidence: they exposed a negation direction,
parser/scoped-option placement, the omitted explicit square rearrangement,
expensive unfolding of the same-weight triangle, and a missing defining
namespace. Factoring the triangle with generic polynomial arguments removed
the elaboration timeout without changing its mathematical statement.
The closure theorem alone has a scoped two-million heartbeat limit;
worker count, memory limit and OS reserve were not raised.

Root imports are registered only. Full root/tree build, full axiom audit,
guard and metrics runs were NOT performed. No sorry, new axiom, frontier-field
weakening or CI change. The first canonical chart fence is byte-for-byte
unchanged, so no ASCII chart is reprinted.

### SHA-256 of final sources

```text
1d4c2c9968146b8d38473dc88f1f64637727d96094bbaa7884580d638894dde0  BF4ExactSlabFixedSpatialTerminalSchurTest.lean
d5b60a872cf2681a8a9241b308937761692edab2ffc476291dfdd4b7e7330f3e  BF4ExactSlabFixedSpatialBlockWeightedContinuity.lean
04355ab85581747319c707834b42ea18c8678f87594f67da38bd3776e1654869  BF4ExactSlabFixedSpatialTerminalSchurClosure.lean
10999f107cc9ff2f20b143be012a95e5b11f501aaf235bb7e012373063378464  BF4ExactSlabFixedSpatialFilteredVarianceComparison.lean
d76ba7e29498a46c6f331a424299968b900182e621ef677a27c9335f13ce1e07  BF4WilsonAllNomeOriginalVarianceComparison.lean
```

### SHA-256 of accepted logs

```text
4e73083bb5089c0f760d5eb0fe6adab500ac26e25bf92f3b0ee71457e525602c  ym-terminal-schur-test-20261003-2.log
fdaf293f903249d3ee1dbd1b126702d99b4d7e4ec1e2e1545bc85fd626ec154e  ym-block-weighted-continuity-20261003-1.log
fd2312c591b05b00f055ea4f4321109b1f8a41aa6fb1c09e19ec233e20562bb3  ym-terminal-schur-closure-20261003-5.log
98bc5de582c050b6d990865be7fbd18aa8cefbd73ce373ff35b66e8124e55c0d  ym-filtered-variance-comparison-20261003-1.log
f771c54701926442508c5bb7fbde8dc54eba44879147aecae91231f8628395cc  ym-original-variance-comparison-20261003-3.log
```
