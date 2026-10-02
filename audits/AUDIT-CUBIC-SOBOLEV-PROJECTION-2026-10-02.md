# Original cubic Casimir norm control with retained projection gain

## Result and proof consequence

Both cubic absolute-leaf costs can now be replaced by literal full third
Casimir moments in an ACTUAL original growing-loop energy ceiling. The
underlying negative cubic form is proved positive and bilinear rather than
supplied as an assumption. Sharp Cauchy--Schwarz and signed Young control
its mixed source term. This supplies a norm-based route to the remaining
estimate; it does not establish a useful variance-relative scaling rate.

Let h=1-w, rho=w^((K+1)*(K+3)), Cfull be the sum of Casimirs over ALL
link blocks, and S3(p)=H[(Cfull p)(Cfull^2 p)]. For the ORIGINAL source
q=P_fringe(V*g_n), psi=f-OWNmean, SAME original positive partition Z,
signed centering correction C, and EXISTING normalized projection gain G,
define

    D3 = h^3/6 * [ (S3(q)+S3(q*psi^2))/2 + S3(q*psi) ].
    b = h^2/8 + 9*rho.

For 0<w<1, headCutoff(w)<=K, sufficientCutoff(w)<=K and side(scale)<width,
the actual original fundamental growing-loop energy satisfies

    E <= [12*side*h + b]*OWNVar
         + [D3 + rho*H[q^2]/2 + h^3*angularPairBudget - b*C]/Z
         - h*OWNWard - (h^2/2)*G.

Neither C nor the COMPLETE original Ward insertion is assumed favorable.
Raw H[q^2] is not Z; the exact signed pin H[(q*psi)^2]=Z*OWNVar-C remains.
G may vanish. The new third-moment cap is not claimed numerically smaller
than the old absolute-leaf cap. The old ceiling remains available.

## Declarations and causal joins

| Declaration | Source | Checked content |
| --- | --- | --- |
| `cubicPair_diagonal_nonnegative` | `lean/YMGap/Continuum/SU2QuaternionCyclicCubicOperator.lean:63` | Actual Cw=-pairCubic is nonnegative on supported diagonals |
| `cubicPair_symm` | `lean/YMGap/Continuum/SU2QuaternionCyclicCubicOperator.lean:139` | Symmetry via SAME exact heat, omitted and Casimir forms at computed auxiliary cutoff |
| `cubicGNSData` | `lean/YMGap/Continuum/SU2QuaternionCyclicCubicOperator.lean:163` | Actual positive bilinear form, without assuming input-tree linearity |
| `cubicPair_cauchySchwarz` | `lean/YMGap/Continuum/SU2QuaternionCyclicCubicOperator.lean:175` | Sharp squared mixed estimate |
| `sourceCubic_le_diagonalNorms` | `lean/YMGap/Continuum/SU2QuaternionCyclicCubicOperator.lean:221` | Original sign -Cw(q,q*psi^2)+Cw(q*psi,q*psi) bounded by three diagonals |
| `cubicBudget_le_cube` | `lean/YMGap/Continuum/SU2QuaternionCyclicCasimirCube.lean:57` | Scalar cubicBudget(n)<=n^3/6, including n=0,1,2 |
| `thirdMoment` | `lean/YMGap/Continuum/SU2QuaternionCyclicCasimirCube.lean:113` | Computed literal FULL third Casimir moment |
| `full_cubeMoment_eq_literal` | `lean/YMGap/Continuum/SU2QuaternionCyclicCasimirCube.lean:118` | Actual path eigenaction identifies lambda^3 path moment with S3 |
| `neg_pairCubic_diagonal_le_thirdMoment` | `lean/YMGap/Continuum/SU2QuaternionCyclicCasimirCube.lean:163` | Actual negative cubic diagonal <=h^3*S3/6 |
| `sourceSobolevCubicBudget` | `lean/YMGap/Continuum/SU2QuaternionCyclicSobolevProjection.lean:44` | The displayed D3, with full signed differential moments |
| `sourceCubic_le_thirdMoments` | `lean/YMGap/Continuum/SU2QuaternionCyclicSobolevProjection.lean:50` | Actual source cubic term <=D3 |
| `sourceError_le_sobolev` | `lean/YMGap/Continuum/SU2QuaternionCyclicSobolevProjection.lean:89` | Actual cubic-minus-omitted numerator, preserving omitted mixed/diagonal signs |
| `completeRemainder_le_sobolev_completedSquare` | `lean/YMGap/Continuum/SU2QuaternionCyclicSobolevProjection.lean:137` | Complete cancelled remainder retains its negative completed square and angular debt |
| `completeRemainder_le_sobolev_projectionCeiling` | `lean/YMGap/Continuum/SU2QuaternionCyclicSobolevProjection.lean:185` | SAME square pays EXISTING projection gain |
| `sobolevCenteredDebt` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSobolevProjection.lean:95` | D3 replaces ONLY the old cubic cost; raw mass, angular cost and SIGNED C remain |
| `paddedSquare_sobolevCeiling_le_varianceDebt` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSobolevProjection.lean:123` | Existing fourth-moment cap16 gives unchanged b=h^2/8+9*rho |
| `paddedSquare_remainder_sobolev_projection_bound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSobolevProjection.lean:205` | SAME Z normalization and EXISTING normalized gain |
| `paddedSquare_energy_sobolev_projection_bound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSobolevProjection.lean:246` | ACTUAL original energy consumer displayed above |

The product-heat cutoff used to prove cubic symmetry is a computed proof
device, not an added cutoff argument of the cubic form. Actual positive
diagonal path masses supply all positivity. Full-path Casimir eigenaction
uses the literal original source and all link blocks.

## Remaining analytic input

OPEN: useful control of the FULL S3 moments and COMPLETE signed angular,
Ward and centering debt minus retained gain against OWN variance on a
physically justified changing family. No generic active-only replacement
of the original global cubic coefficient has been proved. The prior
additive raw-mass cutoff modulus does not pay D3 relative to variance.
No width/coupling-uniform useful rate, physical spacing or mass calibration,
nonzero continuum survival, full same-theory QFT or every-group realization
is supplied. The continuum/Clay target and all exact chart claims remain OPEN.

The parallel requested seven-paper review reused primary-record verification
at 2026-10-02 09:27 UTC and the saved theorem screen. Conditional joint
preservation, rational certificate validation and same-operator gap assembly
remain methods; no result supplies the above missing Wilson scaling input.
See `audits/RESEARCH-MATH-PH-2026-09-30.md`. No paper theorem became a premise.

## Verification boundary and safety

Four accepted focused checks returned exit zero without warnings or errors;
all 7+10+7+6 printed gates stay within {propext,Quot.sound}. The coefficient
sixth and its sign are axiom-free. Independent Sol mathematical source review
passed for all four modules. Draft failed checks are not accepted evidence;
the new generic module's first check rejected pattern-match indentation,
corrected before its accepted check. No new sorry, custom axiom, classical
input, analytic hypothesis or weakened frontier field was introduced.

Independent Luna evidence QA also passed: source and accepted-log hashes,
all declaration anchors, the single new root import, documentation scope,
`git diff --check` and byte-identical chart fenced blocks were checked.

Every accepted check used `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20`, serialized with a 12-GiB OS reserve. Dynamic
preflight found no competing Lean/Lake, runner or pytest process; pressure
free capacity was 85%, with zero swap. No limits were raised. One downstream
root import transitively includes the four modules. The root itself,
full-tree build/audit/guard and progress metric were NOT run. The automatic
axiom baseline was not regenerated; CI remains manual-only. Canonical
chart fenced blocks are unchanged and no ASCII chart is reprinted.

## Source and accepted log hashes

| Artifact | SHA256 |
| --- | --- |
| `SU2QuaternionCyclicCasimirCube.lean` | `c45493594a7aa790ad65774a3dbf9495b70e2f5cc0fabebdd9611f8b3c6d415a` |
| `SU2QuaternionCyclicCubicOperator.lean` | `176259b7efeab43e0763bd0905c90e343528cf701f4cb69fecc9e1e2403cfbd8` |
| `SU2QuaternionCyclicSobolevProjection.lean` | `37c75d95b1ad5a0121b8c8c643a678906965eec77d45b628ceec929d1eb8ac44` |
| `BF4DyadicWilsonSquareSobolevProjection.lean` | `2ffd279a71cdee54700c73f1a3b5fdb8c69fd882c760977999ad07fe2dfac842` |
| `/tmp/ym-casimir-cube-20261002-accepted.log` | `3381793e4e29ba38bb73e45817cbc50bf23f523bbdc2f0a1975c06518cfa1662` |
| `/tmp/ym-cubic-operator-20261002-accepted.log` | `b57d79c9780bb80177ca1193cd40a0172929e6b8b274b55aadc16ebf20615d21` |
| `/tmp/ym-cubic-sobolev-projection-20261002-accepted.log` | `6a8c12cddfbdac3a887d529d8a96113c94500f62b32e8d955a2f41b3b15b47a4` |
| `/tmp/ym-wilson-square-sobolev-projection-20261002-accepted.log` | `5fe5af9448cc18806abb2598c06b80165e453b6ee2f29597ad2b51e0338de770` |
