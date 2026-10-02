# Exact heat response and original variance loss

## Result and scope

The original growing Wilson square now has a nonperturbative energy ceiling
with a computed negative response-square term. A separate checked estimate
quantitatively compares its actual raw channels, centered at the original
interacting mean, to its SAME interacting variance. Neither result supplies
the useful changing-family estimate required for physical scaling.

Let f be the original fundamental character of `paddedSquare`, P=4*side,
g the original terminal message at depth n, Z=oddMass at that SAME depth,
and b_c the existing signed passive-channel sources with their original
nonnegative weights. Use the existing moments

    M = sum_c weight_c * H[b_c^2],
    F = sum_c weight_c * H[b_c^2*f^2],
    a = w^(3P), b = w^(8P),
    B = (1-b)*M + (1+b-2a)*F,
    I = sum_c weight_c * sourceIncrementCost(b_c,f),
    R = sum_c weight_c * eigenResponse(b_c,f,a)^2.

For 0<w<1, headCutoff(w)<=K, the SEPARATE guard 2<=K, and
side(scale)<width, at EVERY terminal depth:

    4*E_original(f) + I = 2*B,
    0 <= I, R <= I,
    E_original(f)/Z = B/(2Z) - I/(4Z)
                   <= B/(2Z) - R/(4Z).

Both actual heat images are used exactly. No Taylor, cubic, angular-error
or omitted-mode budget enters THIS ceiling; the earlier ceilings remain
available. There is no claim of numerical dominance over their entire
bounds. Energy and I are invariant under constant shifts. The computed
response is 2*(1-a)*H[b_c*f], not an OWN-centered variance, and may vanish.
The coefficient 1+b-2a is signed: no independent cap on F is substituted
under an assumed positive coefficient.

For psi=f-OWNmean, define the actual centered raw-channel square and loss

    A = sum_c weight_c * H[b_c^2*psi^2],
    L = M-Z.

Under 0<w<1, headCutoff(w)<=K and side(scale)<width, at EVERY depth,
WITHOUT an additional label-two guard, the new variance consumer proves

    L >= 0,
    (A-Z*OWNVar)^2 <= 16*L*A.

The constant sixteen is independent of the square perimeter. This does
not make L, A, or their ratios uniform in width, coupling or physical spacing.
All normalizations, terminal messages, channels and OWN centers are the
original ones. There is no source-sign or active-independence premise.

## Mathematical argument

For the original normalized product heat P, define

    D(u,v) = H[u*v] - H[u*P(v)].

Its jump representation is twice D. Weighted Cauchy--Schwarz on that
positive jump form cancels the common factor four and gives

    0 <= D(u,u) <= H[u^2],
    D(u,v)^2 <= D(u,u)*D(v,v).

Symmetry of the kinetic pair gives the correct sourceMoment orientation:
the raw moment minus H[(q*p)*P(q)] equals D(q,q*p). A finite weighted
positive form aggregates the ACTUAL channels with coefficient one, without
a channel-count enlargement. Its p=1 identity yields L=M-Z. Its p=psi^2
identity joins the interacting moment to Z*OWNVar, using the original
centered-source-square theorem. The existing centered cap applied separately
under each signed b_c square gives the fourth-moment bound 16*A, not 16*M.
These identities prove the displayed variance-loss estimate.

## Declaration evidence

| Declaration | Source | Checked content |
| --- | --- | --- |
| `heatLossPair` | `lean/YMGap/Continuum/SU2QuaternionProductHeatMomentDefect.lean:47` | Original heat loss D |
| `jump_heatLoss_pin` | `lean/YMGap/Continuum/SU2QuaternionProductHeatMomentDefect.lean:52` | Jump pairing equals 2D |
| `heatLossPair_nonnegative` | `lean/YMGap/Continuum/SU2QuaternionProductHeatMomentDefect.lean:63` | Positive loss diagonal |
| `heatLossPair_le_haar` | `lean/YMGap/Continuum/SU2QuaternionProductHeatMomentDefect.lean:77` | Diagonal upper bound |
| `heatLossPair_cauchySchwarz` | `lean/YMGap/Continuum/SU2QuaternionProductHeatMomentDefect.lean:88` | Sharp coefficient-one CS |
| `rawMoment_difference_pin` | `lean/YMGap/Continuum/SU2QuaternionProductHeatMomentDefect.lean:123` | Correct moment orientation |
| `rawMoment_difference_square_le` | `lean/YMGap/Continuum/SU2QuaternionProductHeatMomentDefect.lean:135` | Mismatch controlled by heat loss |
| `squareChannelIncrement` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:94` | Entire original channel increment I |
| `squareChannelResponseSquares` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:103` | Computed channel response R |
| `exactChannelHeatCost` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:115` | Exact signed cost B |
| `squareChannelIncrement_nonnegative` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:139` | I>=0 |
| `squareChannelResponseSquares_le_increment` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:156` | R<=I |
| `squareChannelIncrement_shifted` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:169` | Increment unchanged by constant centering |
| `paddedSquare_channel_exact_cost` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:181` | Exact unnormalized identity |
| `paddedSquare_energy_exactChannel_increment` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:217` | Normalized identity under SAME Z |
| `paddedSquare_energy_exactChannel_response_bound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:237` | Exact nonperturbative response ceiling |
| `centeredChannelSquare` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean:227` | A at OWN interacting center |
| `channelHeatLoss` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean:238` | Actual L=M-Z |
| `paddedSquare_channel_heatLoss_nonnegative` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean:282` | Original channel loss nonnegative |
| `paddedSquare_channel_variance_loss_bound` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceLoss.lean:303` | SAME original variance comparison |

The actual heat images and exact channel cost are existing results:
`paddedSquare_fundamental_fullRange` at
`lean/YMGap/Continuum/BF4DyadicWilsonSquareHeatImage.lean:101` and
`paddedSquare_terminal_channel_cost` at
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelCost.lean:135`.
Response domination uses `sourceIncrement_ge_eigenResponse_square` at
`lean/YMGap/Continuum/SU2QuaternionProductHeatEigenResponse.lean:67`.
The variance joins use `oddMoment_eq_square_channels` at
`lean/YMGap/Continuum/BF4DyadicWilsonSquarePassiveChannels.lean:87`,
`centered_source_square` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceGram.lean:89`,
and `paddedSquare_centered_fourth_le_sixteen_second` at
`lean/YMGap/Continuum/BF4DyadicWilsonSquareCenteredFourthMoment.lean:113`.

## Remaining frontier

OPEN: useful control of actual L/Z on a physically justified changing
family, relative to OWN variance where needed, AND control of the remaining
signed mass, mean, response and cost terms of the complete exact energy
ceiling. L control alone is not a proved closure of that ceiling. Raw F
is not A or interacting variance; channel centering corrections are not
silently identified with the earlier global correction or projection gain.

No new analytic hypothesis, source factorization, surrogate density, favorable
sign, scaling trajectory, physical calibration or continuum claim is supplied.
Nonzero continuum survival, full same-theory QFT, every actual compact simple
group and the Clay result remain OPEN. Canonical chart claims are unchanged.

The requested papers supply methods, not these missing producers. In
particular 2610.01121 retains squared loss before composition, but its
conditional sampler is not identified with the original OS transfer here.
See `RESEARCH-REQUESTED-FIFTEEN-PAPERS-2026-10-02.md`.

## Verification boundary

Three serialized focused one-worker checks passed, each explicitly capped
at 20 GiB with dynamic capacity checks. Their 6+10+4 printed gates stay
within {propext,Quot.sound}; `responseQuarter` is axiom-free. The first two
accepted logs contain no errors or warnings. The third has zero errors and
ten unused-variable warnings; these do not discharge or conceal obligations.
Draft elaboration failures are not proof evidence. Fixes supplied missing
namespaces, explicit arguments/endpoints and valid rational ring syntax,
without changing statements or raising limits.

Independent Sol mathematical review passed the exact energy normalization,
signed coefficient, cutoff guards, sharp loss form, original-channel
aggregation and OWN-variance/fourth-moment joins. Read-only evidence review
confirmed final source/log hashes and gate outputs. No new sorry, axiom,
classical use or weakened frontier is introduced. Two semantic-root imports
include the three modules transitively. Root/full-tree builds, full axiom
audits, broad guards and progress metric were NOT run; no broader verification
is claimed. CI stays off and chart fences are preserved.

Final independent Luna documentation QA passed: all hashes and declaration
anchors match, the twenty printed gates and ten third-log warnings are
accurately recorded, whitespace checks pass, chart fences match HEAD,
and CI files are unchanged. Markdown rendering was not independently tested.

### Final source SHA256

- `SU2QuaternionProductHeatMomentDefect.lean`:
  `6ca099cdd6b56e2abfbd3119d20506634b3956530ee115c96d4b256335ac13b0`
- `BF4DyadicWilsonSquareChannelExactResponse.lean`:
  `94b7da8bab7d30d85c9a64c395ae8d7683d2981aef01e7852b69568d09a71f5f`
- `BF4DyadicWilsonSquareChannelVarianceLoss.lean`:
  `209d1284159bc4d921abdada2d29cdf86f1a5c58cfdbef96e95677aa6ddc5d26`

### Accepted focused logs and SHA256

- `/tmp/ym-product-heat-moment-defect-20261002-second.log`:
  `79ab01540b16cc5fc7400cfe697ffe5b03350592639ab65e97d5777396cc099a`
- `/tmp/ym-exact-channel-response-20261002-third.log`:
  `03377fe06f97762611bfb77c8d7091647b73f2b00b7b93db320a2d9e0d4af607`
- `/tmp/ym-channel-variance-loss-20261002-third.log`:
  `5af5054a10e898a836bb633feb02a906067b1630f6b13829b19084b1376aaffb`
