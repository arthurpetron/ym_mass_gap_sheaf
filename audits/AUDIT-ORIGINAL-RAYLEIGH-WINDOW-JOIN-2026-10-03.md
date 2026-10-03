# Original Rayleigh chronology and paid moving-center joint approximation

The whole-project continuum Yang--Mills/Clay target remains OPEN. This
checkpoint supplies original finite SU(2) identities and a fixed-parameter
joint approximation, not a physical mass-gap theorem.

## Checked mathematical increment

Keep the original transfer T=P_w M_V, g_n=T^n 1 and ell(p)=H[V*p].
For any supported SAME signed test psi, set

    A=g_(n+t), b=T^t(g_n*psi),
    Z0=ell(A^2), Z1=ell(A*T A).

The original normalized block pairing is exactly the chronological endpoint
window at lag 2t+d. Its partition is ell(g_(n+t)*g_(n+t+d)), also equal
to the full chronological partition ell(g_(n+2t+d)*g_n). The d=0 and d=1
partitions remain DISTINCT. Both are constructed positive under the unchanged
0<w<1 and K>=headCutoff(w) guards.

Consequently the EXISTING cleared Rayleigh cost satisfies

    D = Z1*ell(b^2) - Z0*ell(b*T b)
      = Z0*Z1 * (Q_(2t) - Q_(2t+1)),

where Q_L is the original normalized endpoint product of the SAME psi
at both endpoints. Zero t and d are included; no finite stationary vacuum,
bare-heat eigenpin, new action or response normalization is introduced.

For supported f and ANY common rational center c, denote by P_L the
uncentered original endpoint product, by M_L either original endpoint
mean, and by Q_L the product centered at that supplied c. Then

    Q_L = P_L - (c+c)*M_L + c*c,
    Q_L-Q_J = P_L-P_J - (c+c)*(M_L-M_J).

The center's square cancels EXACTLY before taking any limit. Padded-unit
congruence is used only on supported window insertions; strict coefficient
equality of a lifted unit is not assumed.

For a finite certified Interval(N,f,C), the original zero-window RIGHT-tail
comparison proves both signed orders of

    |M_L-M_J| <= mixRate(w,width)^n*(C+C),

for ALL lags L,J, including zero, independently of guarded late K. The
actual odd-window OWN center c_n=middleRatio(n+1,n,f) lies in [-C,C],
without assuming it equals the mean at either longer horizon. Therefore

    |(Q_L-Q_J)-(P_L-P_J)|
      <= mixRate(w,width)^n*((C+C)*(C+C)).

The module states BOTH order bounds, not an assumed sign. Every supported
polynomial receives C=polynomialCap(f) and its constructed interval; no
analytic interval or mean estimate is an unpaid input to that gate.
The same estimate is joined to the EXISTING D in BOTH cleared orders.

Finally, for the literal fundamental Wilson source of a supplied SourceLoop,
each P_L equals the original finite scalar for
WindowExpression.mul(.loop 0 loop 1)(.loop L loop 1). The TWO existing
originalJointLimit objects give both-order approximation of Q_L-Q_J by
their representative difference with error

    mixRate(w,width)^n*(2C)^2 + epsilon + epsilon.

Cutoff-stage, exterior-time and CReal representative thresholds are the
explicit maxima of the TWO existing fixed-source thresholds. No convergence
of the moving centered polynomial is assumed or invoked, and no additional
limit object is substituted.

## Declaration-to-source map

Names are local names in each cited module's namespace under YMGap.Continuum.
Every row below has an accepted printed axiom gate.

| Declaration | Source | Exact role |
| --- | --- | --- |
| `observedMessage_endpoints` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockWindowPin.lean:54` | Both signed endpoint insertions under original K/V, no support premise. |
| `block_window_numerator` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockWindowPin.lean:85` | SAME supported test and literal block, lag 2t+d. |
| `block_window_partition` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockWindowPin.lean:127` | Each block's own chronological partition. |
| `normalized_block_window_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockWindowPin.lean:140` | Actual constructed positive mass, no recentering. |
| `lower_endpoint_mean` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowLagMeanControl.lean:95` | Exact middleRatio(n,n+L,f). |
| `upper_endpoint_mean` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowLagMeanControl.lean:105` | Same finite mean by actual symmetry, not stationarity. |
| `endpoint_means_eqv` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowLagMeanControl.lean:114` | Equal original endpoint means at arbitrary lag. |
| `endpoint_mean_lags_commonTail` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowLagMeanControl.lean:124` | Both mean orders, q^n*(C+C), including zero lag. |
| `middleRatio_interval_bounds` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowLagMeanControl.lean:146` | Actual finite mean in [-C,C]. |
| `centered_pair_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMovingCenterLagDifference.lean:131` | Arbitrary common center, P_L-2c*M_L+c^2. |
| `centered_lag_difference_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMovingCenterLagDifference.lean:182` | Exact c^2 cancellation. |
| `own_centered_lag_difference_bounds` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMovingCenterLagDifference.lean:230` | Actual OWN-center correction, both orders. |
| `polynomial_own_centered_lag_difference_bounds` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMovingCenterLagDifference.lean:272` | Computes the cap for every supported f. |
| `clearedRayleighCost_window_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighWindow.lean:89` | Literal existing D=Z0*Z1*(Q_2t-Q_(2t+1)). |
| `own_clearedRayleighCost_raw_bounds` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighWindow.lean:141` | Pays the actual OWN-mean correction in D, both orders. |
| `raw_original_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit.lean:49` | Literal original two-loop finite scalar. |
| `centered_lag_joint_approx` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit.lean:81` | TWO existing fixed-source joint limits after center correction. |

The imported cost is `clearedRayleighCost`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:131`.
The original tail input is `windowRatio_right_commonTail`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowBracket.lean:140`.
The existing joint-limit approximation is `originalJoint_approx`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.lean:131`.

## Remaining mathematical input and exact scope

The new center-error bound is uniform in the TWO lags and guarded late K
at FIXED nome w, spatial width and source cap C. The joint-limit thresholds
also depend on the supplied loop and fixed lags. The statements do not
include a physical lattice-spacing parameter or imply spacing uniformity.

The SAME scaling producer remains UNSUPPLIED:

    side*D <= usefulConstant*Z1*ell(b^2)

on the actual growing square and a justified changing family, with
t=side/2 for the relevant even dyadic sides. The raw signed two-point
difference is not yet bounded RELATIVE to that interacting response.
The new absolute center error alone is not a relative budget, especially
when the response becomes small. The earlier comparison of ell(A^2*psi^2)
with ell(b^2) is not supplied by this checkpoint either.

The explicit finite/joint approximation is not yet a theorem identifying
the old completed dyadic response, with its computed normalization, with
this particular joint-limit difference. No full spatial/spacing passage,
cross-scale relative costs, nontrivial continuum survival, physical mass
calibration, full same-theory QFT, every compact simple group or Clay closure
is asserted. No canonical displayed frontier claim changed; no ASCII chart
was reprinted.

## Verification boundary

Root ran five serialized narrow file checks through scripts/safe_lean_build.py:
one worker, 12 GiB OS reserve, 20 GiB hard worker cap, atomic session lock.
Every launch had fresh memory/process/swap checks: 85--86 percent system-wide
free memory, zero swap and no competing Lean/Lake/test/runner worker.
All five accepted checks exited zero. Direct log parsing verified 17 unique
public axiom records, all within {propext, Quot.sound}, zero errors/warnings.
Independent read-only semantic/algebra review passed, including zero lag/t,
distinct partitions and the right-tail route.

An earlier dependent rewrite in the normalized Rayleigh pin reached its
heartbeat limit. Explicit scalar numerator/partition transport replaced it;
no resource ceiling was raised. Preliminary parser/namespace/timeout logs
are NOT accepted proof evidence. No new sorry/axiom, classical shortcut,
field weakening or CI change. Root imports are registered only; no aggregate
check, full build, full audit or axiom-baseline regeneration ran.

Accepted logs and SHA-256:

| Log | SHA-256 |
| --- | --- |
| `/tmp/ym-block-window-pin-20261003-b.log` | `137c67143a521ad4ab6ae1c5272ba6bc5ee1664e4e2d011b381eee679ef605d0` |
| `/tmp/ym-window-lag-mean-20261003-a.log` | `926e889e0616d6af64c161d6cc328cd75247766a9b47d3b5ec8fe37c96ef4259` |
| `/tmp/ym-moving-center-lag-20261003-c.log` | `29f17e17a751b34d644962db8118528beda86eb5651fa09bb11d7ca0e96d15fe` |
| `/tmp/ym-block-rayleigh-window-20261003-b.log` | `b79e7025fbb4f966c08c871a03d55b5604e56c03a7438d767ba1a9d23ca3825d` |
| `/tmp/ym-wilson-moving-center-limit-20261003-a.log` | `6889c8e609d4fd94363135da9246cb543043e1389450333d1daca4a2b035e2db` |

Checked sources and SHA-256 (all under lean/YMGap/Continuum):

| File | SHA-256 |
| --- | --- |
| `BF4ExactSlabFixedSpatialBlockWindowPin.lean` | `455eed7e871760d422abf07fe6e38217a4b7baa1ad45fb367abe12fe07bc8725` |
| `BF4ExactSlabFixedSpatialWindowLagMeanControl.lean` | `c6c9b5ffc0d63207a868278a2ed41ac56371026c6d4513d3e549a4917bbf54c1` |
| `BF4ExactSlabFixedSpatialMovingCenterLagDifference.lean` | `fb0050031ba2429e1e5d0ba77dea42db66501ead7957d4ab7d4b6075aabb8179` |
| `BF4ExactSlabFixedSpatialBlockRayleighWindow.lean` | `d2a280a2390d43f2a25c3cda9821bdbd1888aa9a5707894c8a873fe8b2574ff6` |
| `BF4ExactSlabFixedSpatialWilsonMovingCenterLagLimit.lean` | `bc91e0f513198e56a001e51fd301449a8e05f278905c9930a7941528d7d3245f` |
