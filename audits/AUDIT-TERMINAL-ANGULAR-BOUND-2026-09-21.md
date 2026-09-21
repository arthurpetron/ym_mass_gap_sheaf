# Original terminal-message relative angular bound

Date: 2026-09-21 UTC. Increment after `496d124`.

## Mathematical result

For the ORIGINAL finite SU(2) action, let `g = T^(n+1)1`, and let D be the
angular field with coordinate indices `4*s+i, 4*s+j`, where s is an active
kinetic link and `i,j < 4`. At every `0<w<1` and `K >= headCutoff w`, the
code constructs both positive polynomial certificates

    C(w) g - h(w) Dg >= 0,       C(w) g + h(w) Dg >= 0,

and proves, for every certified positive background R on the same carrier,

    h(w)^2 H[R (Dg)^2] <= C(w)^2 H[R g^2].

The conclusion is `terminalMessage_angular_weighted_square`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalAngularBound.lean:166`.
Here H is the original product quaternion Haar functional; the implementation
uses `weightedPair`, with R on the right of the square. No partition,
reference measure, endpoint message or action is substituted.

## Causal declaration path

All paths below are relative to the repository root.

| declaration | source | role |
|---|---|---|
| `angularDerivative_supported_at` | `lean/YMGap/Continuum/SU2QuaternionAngularSupport.lean:77` | Support at arbitrary ambient coordinates, not only the first block |
| `angularDerivative_character_at` | `lean/YMGap/Continuum/QuaternionHaarCharacterDerivative.lean:184` | Exact character chain rule at those coordinates |
| `heatPrefixAngularIntervalAt` | `lean/YMGap/Continuum/QuaternionHaarHeatAngularDerivative.lean:133` | All-cutoff heat derivative cap at explicit strict nome |
| `scalarAngularInterval` | `lean/YMGap/Continuum/SU2QuaternionRelativeHeatAngularBound.lean:93` | Actual two-block scalar derivative has conservative cap 32 |
| `heatAngularInterval` | `lean/YMGap/Continuum/SU2QuaternionRelativeHeatAngularBound.lean:107` | Instantiates that cap on the original relative kinetic factor |
| `angularDerivative_partialHaarHeads` | `lean/YMGap/Continuum/SU2QuaternionHaarTailDerivative.lean:171` | Output differentiation commutes with original input integration, shifting indices by exactly 4 per input block |
| `angularDerivative_blockIndependent_zero` | `lean/YMGap/Continuum/SU2QuaternionHaarTailDerivative.lean:235` | All unselected factors and the entire supported input have zero selected output derivative |
| `productMap_angular_pin` | `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularMessage.lean:52` | Derivative hits exactly one matching heat factor; complete input and all other factors remain |
| `productMap_angular_bounds` | `lean/YMGap/Continuum/SU2QuaternionProductHeatAngularMessage.lean:108` | Integrates its two-sided interval against the full positive background |
| `terminalMessage_angular_bounds` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalAngularBound.lean:89` | Instantiates input as actual `spatialWeight * terminalMessage n` and eliminates the erased normalizer |
| `terminalMessage_angular_square_certificate` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalAngularBound.lean:124` | Product of the two signs retains the negative derivative square |
| `terminalMessage_angular_weighted_square` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalAngularBound.lean:166` | Actual relative quadratic inequality with arbitrary certified positive R |

The elimination uses the pre-existing `conditionalMessage_lowerCertificate`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialConditionalMessage.lean:103`.
Writing r for that exact erased message, the algebra is

    C(g - h*r) + h(C*r +/- Dg) = C*g +/- h*Dg.

Every summand has a constructed positive certificate. There is no division
by g and no premise asserting the desired derivative bound.

## Parameters and scope

- `h(w) = headFloor w` is defined in
  `lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:50`.
  It is half the existing pointwise strict heat floor.
- `C(w) = heatDerivativeCap w 32` is defined via
  `lean/YMGap/Continuum/QuaternionHaarHeatAngularDerivative.lean:97`:
  `(2*32)*prefixBudget w`. `prefixBudget` is the explicit finite-head plus
  tail budget in `lean/YMGap/Continuum/SU2HeatQuarticPrefixBound.lean:49`.
- The admissibility modulus `headCutoff w` is in
  `lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:55`.
  The theorem explicitly requires `headCutoff w <= K`.
- Neither h nor C contains the width, terminal depth, selected link, angular
  components, background R or cutoff K. The derivative constant is deliberately
  conservative; its numerical sharpness is not asserted.
- Both h and C depend explicitly on the nome w. No beta/spacing trajectory,
  near-one-nome uniformity, or useful physical-scale ratio `C/h` is proved.
- The source theorem covers `T^(n+1)1` and active kinetic links. It does not
  assert the same derivative estimate for arbitrary signed states, inactive
  fringe links, or second derivatives.

## Exact remaining join

The result is finite-polynomial regularity of the actual positive terminal
source. It does not define an angular derivative on `JointCompletion` or
compare the original weighted temporal energy to a gradient form. The required
small SAME-variance one-step energy estimate along a justified spatial/nome/
spacing family is still missing. Its conditional consumer remains
`centered_relative_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointTemporalEnergy.lean:128`.

Changing-spacing nontrivial survival, physical mass calibration, full
same-theory QFT structure, continuum construction and the every-compact-simple-
group theorem remain open. The inverse-heat remainder obstruction from the
previous increment is not bypassed by an assumed all-signed-state bound.

## Verification and delegation

The dependency-complete target
`+YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalAngularBound:olean`
passed, as did serialized direct checks of the seven changed
proof modules. All 38 printed gates are within `{propext, Quot.sound}`;
final logs contain no warnings, errors, `sorryAx` or classical dependencies.
No new hole, analytic premise or canonical frontier field was introduced.
The root import list was updated; a full-root build/audit was NOT run.

Final evidence:

- `/tmp/ym-gap-terminal-angular-final-build.log`
- `/tmp/ym-gap-terminal-angular-final-check.log`
- `/tmp/ym-gap-angular-final-SU2QuaternionAngularSupport.log`
- `/tmp/ym-gap-angular-final-QuaternionHaarCharacterDerivative.log`
- `/tmp/ym-gap-angular-final-QuaternionHaarHeatAngularDerivative.log`
- `/tmp/ym-gap-angular-final-SU2QuaternionHaarTailDerivative.log`
- `/tmp/ym-gap-angular-final-SU2QuaternionRelativeHeatAngularBound.log`
- `/tmp/ym-gap-angular-final-SU2QuaternionProductHeatAngularMessage.log`

All runs used the safe launcher, one worker and an explicit 20 GiB ceiling;
CI and resource settings were unchanged. Sol supplied the bounded tail-Haar
derivative draft and independently reviewed the actual-source/parameter scope
(PASS). Main supplied the actual-source estimate and consumers,
final elaboration fixes, and serialized verification.
