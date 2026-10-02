# Exact channel moments in the original Wilson energy

## Result and scope

The growing Wilson square's original energy now has a ceiling written in
two actual passive-channel moments and the active cubic/cutoff budget.
The full signed curvature and literal Casimir square are evaluated exactly,
and an avoidable angular Bessel enlargement is removed. The result retains
the original source, OWN mean and SAME partition. It does not establish a
useful estimate relative to OWN variance on a changing physical family.

Let f be the original fundamental character of `paddedSquare`, P=4*side,
q the original projected endpoint source at terminal depth n, psi=f-OWNmean,
and Z=oddMass at that SAME depth. For the actual passive Gram channels b_c
with their original weights define

    M = sum_c weight_c * H[b_c^2],
    F = sum_c weight_c * H[b_c^2*f^2],
    h=1-w,  t=h^2/2,
    D_A = activeChannelSobolevBudget(q,psi).

The existing M and F are reused, not replaced by a new density or assumed
factorization. At 0<w<1, headCutoff(w)<=K and side(scale)<width, for every n,
the original energy satisfies

    E_original(f)/Z <= [(h+t)*P*(4M-F)
                       +t*P^2*(5F-8M)+D_A]/Z.

OWN centering stays inside D_A's q, q*psi and q*psi^2 moments. No explicit
Ward or angular-defect term is needed in THIS raw-channel ceiling: this
proof never enlarges channel angular cost to raw q^2 angular cost or rebases
it to the interacting variance. Those signed terms are not dropped. The
separate, earlier variance-rebased ceiling is preserved, and its signed
quadratic contribution is also joined to the exact moments here.

## Exact contraction

The previously checked original Gamma and Casimir pins, the full Casimir
product rule, and arbitrary-insertion carrier transport prove

    C(f^2) = 8P*(f^2-1),
    C Gamma(f,f) = 8P^2*(1-f^2),
    C(f-c) = C f = 3P*f,
    Gamma(f-c,f-c) = Gamma(f,f).

These are Haar-carrier equalities under every insertion, not false raw
coefficient equalities for padded representatives. They give, in each actual
channel and then their unchanged weighted sum,

    R = 8P^2*(M-F),
    S = 9P^2*F,
    -R-S/3 = P^2*(5F-8M),
    exact channel angular sum = P*(4M-F).

In particular the Casimir of psi is 3P*f, NOT 3P*psi. The negative square
is not called a centered variance. The original energy is first pinned
through shift invariance, projected source realization and exact passive
channel decomposition. The per-channel Taylor ceiling retains its exact
angular sum and signed R,S. Only the cubic/omitted errors are contracted to
D_A. Substituting the displayed equalities and dividing by the SAME positive
Z proves the original-energy ceiling above. No new analytic input is used.

## Declaration evidence

| Declaration | Source | Content |
| --- | --- | --- |
| `perimeter` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCasimirCurvature.lean:51` | Explicit rational P=4*side |
| `paddedSquare_perimeter_casimir` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCasimirCurvature.lean:205` | Original Cf=3P*f |
| `paddedSquare_square_casimir` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCasimirCurvature.lean:213` | Actual C(f^2) |
| `paddedSquare_gamma_casimir` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCasimirCurvature.lean:228` | Actual signed C Gamma |
| `paddedSquare_shifted_casimir_eq` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCasimirCurvature.lean:240` | Constant shift leaves Cf unchanged |
| `paddedSquare_shifted_casimir` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCasimirCurvature.lean:245` | Shifted Cf=3P*f, not 3P*psi |
| `paddedSquare_shifted_gamma` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCasimirCurvature.lean:256` | Shifted Gamma pin |
| `paddedSquare_shifted_gamma_casimir` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareCasimirCurvature.lean:262` | Shifted full curvature pin |
| `sourceEnergy_le_exactChannelAngular_activeSobolev_retainedCasimir` | `lean/YMGap/Continuum/SU2QuaternionPassiveChannelRetainedCasimirSobolev.lean:198` | Original energy with exact angular sum; no angular Bessel loss |
| `paddedSquare_channelCurvature_moments` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelMomentBalance.lean:122` | R=8P^2*(M-F) |
| `paddedSquare_channelCasimirSquare_moments` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelMomentBalance.lean:158` | S=9P^2*F |
| `signedChannelMomentBalance` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelMomentBalance.lean:205` | Literal P^2*(5F-8M) |
| `paddedSquare_channel_secondOrder_balance` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelMomentBalance.lean:211` | Complete signed quadratic evaluation |
| `signedChannelMomentBalance_le_twelve_mass` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelMomentBalance.lean:245` | Existing cap four yields only <=12P^2*M |
| `paddedSquare_channelAngular_moments` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelMomentBalance.lean:266` | Exact P*(4M-F) |
| `activeChannelCenteredDebt_moments` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelMomentBalance.lean:316` | Earlier complete signed debt rebased to these moments |
| `paddedSquare_energy_channel_moment_bound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelMomentBalance.lean:331` | Earlier OWN-variance/Ward ceiling with exact quadratic moments |
| `paddedSquare_energy_exact_channel_moment_bound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelMomentBalance.lean:350` | Actual raw-channel energy ceiling above |

Existing moments are `squareChannelMass` and `squareChannelMoment` at
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelGeometry.lean:56` and
`:62`. Their source is `squareChannelSource` at
`lean/YMGap/Continuum/BF4DyadicWilsonSquarePassiveChannels.lean:63`.
The active budget is `activeChannelSobolevBudget` at
`lean/YMGap/Continuum/BF4DyadicWilsonSquareActiveChannelSobolev.lean:96`.

## Remaining estimate and excluded shortcuts

OPEN: control the COMPLETE original moment ceiling against OWN interacting
variance on a physically justified changing family, with useful spatial and
physical-time/spacing dependence. Raw M,F are not that variance. The existing
cap F<=4M yields only P^2*(5F-8M)<=12P^2*M, not a favorable sign. The
division-free condition 5F<=8M would make this quadratic term nonpositive;
it is neither proved nor imposed as a mandatory route. Joint cancellation
with the leading and cubic terms may instead be needed.

The original q is not independent of the active loop blocks. Accordingly
`channelSquare_factor` at
`lean/YMGap/Continuum/SU2QuaternionPassiveChannelMomentFactorization.lean:136`
does not provide a factorization here. Complement-density moment identities
do not identify that density with these channel squares. No global projection
gain equality, comparison against that route's full numerical ceiling,
width/coupling uniformity, continuum survival, physical mass calibration,
full same-theory QFT, every-group realization or Clay closure is asserted.
No canonical chart claim changes.

## Verification boundary

Three serialized focused checks passed with 8+5+9 printed gates. P is
axiom-free; the other twenty-one outputs use only {propext,Quot.sound}.
Accepted logs below have no error or warning. Draft checks rejected missing
namespace opens, underconstrained channel congruence and unary-minus let
layout; explicit namespaces/endpoints and a let separator fixed them without
changing the estimate or raising limits. Failed logs are not proof evidence.

Independent Sol mathematical review passed, including the exact moments,
original energy/OWN-mean/partition pins, and the absence of a Ward rebase in
the raw-channel route. Independent Luna evidence review checked hashes,
anchors and all twenty-two printed gate outputs. The modified generic module
only appends the exact-angular theorem and its gate; earlier proofs and their
declaration anchors are unchanged.

Final Luna documentation QA passed: the declaration anchors and exact consumer
match the report, diff whitespace is clean, chart fences match HEAD, and CI
files are unchanged. The report keeps the remaining scaling estimate OPEN.

All checks used `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20`, with fresh dynamic capacity checks, zero swap,
no competing compiler/runner/pytest and a 12-GiB OS reserve. One downstream
root import includes this increment. No source sorry, new axiom, analytic
premise, frontier weakening or external theorem was added. No root/full-tree
build, broad audit, guard or progress script was run; the automatic axiom
baseline was not regenerated. CI and exact chart fenced blocks are unchanged.
No literature rescan was performed.

## Source and accepted log hashes

| Artifact | SHA256 |
| --- | --- |
| `BF4DyadicWilsonSquareCasimirCurvature.lean` | `67659708702f5c1ce50859ad8769f61ff6b0432652b7d0b5a9f198772b3da9f8` |
| `SU2QuaternionPassiveChannelRetainedCasimirSobolev.lean` | `54a32dc87affa5cb164acde73800671aeb3513dd55ee77f2f49b578f10b7ed54` |
| `BF4DyadicWilsonSquareChannelMomentBalance.lean` | `c408f75727b8d89ff5fe6379aead69de488d3a5f89a359bad889a0946933c8e2` |
| `/tmp/ym-dyadic-casimir-curvature-20261002-third.log` | `e4f09a4812a8e8e626559918dcb842967419b97ab39f568aa20cf80c0761eaef` |
| `/tmp/ym-exact-angular-active-channel-20261002-first.log` | `7793eecbd894135fd77d6cf1f127d3aa31d589337000c7e24ecfee4052c2bf7e` |
| `/tmp/ym-dyadic-channel-moment-balance-20261002-second.log` | `8894cd2917a7fa69cd2d9695db952fb431fe874e1a870c7d0bf4133b3ba2bc00` |
