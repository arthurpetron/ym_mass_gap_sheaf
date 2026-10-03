# All-depth original bent-loop relative gain and SAME completed support

The continuum Yang--Mills/Clay target remains OPEN. This increment removes
the terminal-depth restriction from the fixed-small-nome bent-loop gain,
then proves nonzero positive-time support on the EXISTING completed carrier.
It does not construct a changing family or claim continuum survival.

## Exact scope and normalization

Fix w=1/16, spatial width two and the literal six-edge bent observable F.
Every finite cutoff obeying K>=1 and headCutoff(w)<=K, and every natural
terminal depth n, is covered. Let T be the EXISTING original transfer,
g_n its terminal message, H the original bare Haar functional and ell the
FULL original spatially weighted functional. The actual odd OWN mean is
c_n=ell[(g_(n+1)*F)*g_n]/ell[g_(n+1)*g_n], pinned to the existing mean.
Write A=Tg_n, b=T[g_n(F-c_n)], S=ell[b^2], Q=ell[(A(F-c_n))^2],
E=the EXISTING even partition, and a_n=H(g_n)>0.

The three quantities a_n, odd partition and E remain distinct. In particular,
E is pinned to ell[A^2], not identified with the odd mean denominator.
The reference lambda=w^18 is used only in the original commutator gain
G=ell[b*(b-lambda*A*(F-c_n))]; no interacting eigenmode is asserted.

## Forward construction

The previous checked radius is r=1/80000 and six-face action deviation
delta=1/128. For supported p,g with positive bare Haar amplitudes and
relative centered-square radius r, the new generic shared-variable estimates
give, for an actual interval |U|<=C,

    |H[Up]-Hp*HU| <= C*r*Hp,
    |H[Upg]-Hp*Hg*HU| <= C*(2r+r^2)*Hp*Hg.

Both linear fluctuations and their cross term are retained. Weighted
Cauchy--Schwarz and rational square reflection avoid a square root, choice
or independence assumption.

All-insertion original-terminal transport is applied BEFORE peeling the
full spatial action. Put e=2r+r^2, L=1-delta-(1+delta)e and
U=2delta+2(1+delta)e. The exact original odd numerator and partition obey

    oddPartition >= L*a_(n+1)*a_n > 0,
    |oddNumerator| <= U*a_(n+1)*a_n,
    U <= L/4, hence |c_n| <= 1/4.

The action/shape bounds also construct

    a_(n+1) <= (1+delta)*a_n,
    E <= (1+delta)^3*(1+r^2)*a_n^2 <= 2*a_n^2.

The exact original kinetic test preserves w^12 outside BOTH errors. For
the first-face trace P, alpha=coeffW(w,1)=2^-11 and tail cap 2^-17,

    H[P*b] >= w^12*[alpha/4-(9/2)*2^-17
                         -(1+delta)*(9/2)*r]*a_n
             >= w^12*(alpha/16)*a_n = 2^-63*a_n.

The retained scalar margin above alpha/16 is exactly 87/163840000>0.
The already-weakened depth-zero channel is not substituted here.

Full-action square transport, the cube half-floor and H[P^2]=1 then give

    S >= (1/2)*(H[P*b])^2 >= 2^-127*a_n^2,
    S >= 2^-128*E, hence S/E >= 2^-128.

Raw original b is NEVER presumed fringe-independent. It is transported
under every supported insertion to its local cube representative for
action peeling, then transported back under the cube action insertion.
The final S still contains the ORIGINAL b and original normalization.

The actual centered interval constructs Q<=16E with full V*A^2 weighting.
The complete original Young square gives S-lambda^2*Q<=2G. Since the
constructed S/E floor pays 32*lambda^2*E<=S, it follows that

    G >= S/4 > 0, and G/E >= 2^-130.

These are actual producers: no S/E floor or favorable-gain hypothesis is
passed into the final theorems.

## Contraction to the EXISTING completion

A concrete SourceLoop uses exactly bentEdges, including inverse orientations.
Its sourceCharacter equals bentObservable as a polynomial, not a surrogate.
The original t=1,d=0 chronological window identity identifies S/E with
the lag-two centered pair. The actual odd mean is transported by the existing
mean pin; it is not replaced by a bare-Haar or supplied stationary center.

Along the EXISTING diagonal K=headCutoff(w)+k,n=k, the existing
own_centeredPair_converges theorem passes the floor to the SAME completed
centered moment C2. For the EXISTING centeredVector v of this loop,

    C2 >= 2^-128,
    B(T(1)v,T(1)v) = C2 >= 2^-128, hence T(1)v != 0.

The vacuum-complement vector, completed pairing and time map are existing
objects. No new carrier, normalizer, representative choice or limit is
introduced. A completed G-sign inequality is NOT claimed by this consumer.

## Declaration anchors

All following paths begin `lean/YMGap/Continuum/`.

- `QuaternionHaarRelativeShapePair.lean:197`, `single_shape_insertion_bound`;
  :276, `pair_shape_insertion_bound`.
- `BF4ExactSlabFixedSpatialCubeTerminalOwnMean.lean:105`,
  `original_terminal_pair_weighted_pin`; :131, `original_terminal_weighted_pin`;
  :262, `originalOddPartition_floor`; :295, `originalOddPartition_positive`;
  :312, `originalOddNumerator_abs_le`; :361, `mean_odd_ratio_pin`;
  :373, `originalOddMean`; :412, `originalOddMean_abs_le`.
- `BF4ExactSlabFixedSpatialCubeTerminalEvenBudget.lean:69`,
  `cubeTerminal_mass_upper`; :97, `cubeTerminal_square_bound`;
  :129, `evenPartition_cube_pin`; :163, `evenPartition_le_terminal_mass_square`.
- `BF4ExactSlabFixedSpatialCubeTerminalOverlap.lean:73`, `terminalTestRate`;
  :118, `centeredInterval`; :173, `action_channel_sharp_lower`;
  :215, `terminal_tested_floor`; :256, `originalOwn_tested_floor`.
- `BF4ExactSlabFixedSpatialCubeTerminalGain.lean:155`,
  `original_centeredMessage_cube_pin`; :173, `originalSquare_cube_pin`;
  :239, `originalOwn_square_floor`; :265, `originalOwn_relative_square_floor`;
  :285, `originalOwn_normalized_square_floor`;
  :299, `originalYoungCost_le_sixteen_evenPartition`;
  :348, `original_gain_young_lower`; :377, `originalOwn_gain_relative_lower`;
  :416, `originalOwn_gain_positive`; :429, `originalOwn_normalized_gain_floor`.
- `BF4WilsonSmallNomeBentCompletedGain.lean:92`, `bentLoop`;
  :119, `bentLoop_source_pin`; :159, `originalOwn_square_chronological_pin`;
  :175, `bent_centered_lag_two_floor`; :197, `bent_completed_T1_norm_floor`;
  :202, `bent_completed_T1_norm_ne_zero`; :213, `bent_completed_T1_ne_zero`.

## Verification evidence

Six serialized final focused checks exited zero and cover 47 distinct printed gates
(2+16+4+5+13+7). Dependencies are confined to {propext, Quot.sound};
terminalTestRate and relativeSquareFloor have no axioms. No accepted log
contains errors, warnings, `sorryAx` or PANIC. Failed development logs are
excluded; Overlap b's omitted terminal-tool exit status is superseded by
the explicit final c check, without changing its checked source.

Every launch used a fresh dynamic capacity/competing-process/swap preflight,
`scripts/safe_lean_build.py`, one worker, 12GiB reserve and 20GiB worker cap.
Final preflights had 84--86% system-wide free memory, zero swap and no
competing proof job. No resource limit was raised. The exact source and
accepted log SHA-256 values follow. Source prefix: `lean/YMGap/Continuum/`;
log prefix: `/tmp/ym-`, suffix: `-20261003-<version>.log`.

| Source basename | Log stem/version | Gates | Source SHA-256 | Log SHA-256 |
| --- | --- | ---: | --- | --- |
| `QuaternionHaarRelativeShapePair.lean` | `relative-shape-pair` / `a` | 2 | `c8e79d182b81cd64d24c743ee4c8b870e4bd49aa164b2b5b6f68f2be6ce66b46` | `e1422945b0dd8a26e572400e304f9e675a36e5a1953590be66b9bea514aa30ea` |
| `BF4ExactSlabFixedSpatialCubeTerminalOwnMean.lean` | `cube-terminal-own-mean` / `a` | 16 | `7cf43e47b0757e47e49f07f2f84d651d6aa75916d1ee36693d2efa9411ff7f39` | `eb7d89fda61f00f6944db656598ef49870020c363066064ed98c65cb2e5efb9a` |
| `BF4ExactSlabFixedSpatialCubeTerminalEvenBudget.lean` | `cube-terminal-even-budget` / `b` | 4 | `64fb05cac6abca12b8cd2106bb52f63b611f96cb5269f1353a240c7d7aff47d7` | `678024dd727e16c556ad085a791f6e3c576e644542458645d8cf1e8a15e8a6d4` |
| `BF4ExactSlabFixedSpatialCubeTerminalOverlap.lean` | `cube-terminal-overlap` / `c` | 5 | `2094f100ecd9cf9b106a07f210e9f9c64da53086ff333b3c47e4ace46d8a18e2` | `7e6e25c1542810cc149a1b10e7de38d8999df3fb0b9165e7317292dff5cc8f32` |
| `BF4ExactSlabFixedSpatialCubeTerminalGain.lean` | `cube-terminal-gain` / `a` | 13 | `c09d73a8041b31fee8bfb6427c3cb767bf94672ef1b7f7cbc392b4371079e8b9` | `6c0150b6649d4392ee4f37bb412de67edafe841aedc1703c337e563a38224e76` |
| `BF4WilsonSmallNomeBentCompletedGain.lean` | `bent-completed-gain` / `b` | 7 | `7f4e64cf571954f559b434619009e4202bae8701d366afc4f4142a0648719ca6` | `6ade065e1c4f1dde836651f53d6a3758c2beb432c6c696de9cc4505900345699` |

Root imports are registration-only. The aggregate root, broad audit/guard
and progress metric were NOT run. No old proof module was edited and no
`sorry`, axiom, classical shortcut or resource option was introduced.
Automatic CI remains off. The first canonical fenced chart is unchanged,
SHA-256 `0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.
No exact displayed scaling claim closed, so no ASCII chart is reprinted.

Independent Sol source/mathematical reviews passed the shared-variable mean,
sharper overlap, original all-depth gain and SAME completed-state join.
An independent Luna evidence/documentation review passed all six source/log
hash pairs, 47 permitted gate outputs, declaration anchors, six import
registrations, unchanged canonical chart and fixed-parameter proof boundary.

## The remaining meet-in-the-middle target

FORWARD: the exact complete radius-two source in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredCommutatorGain.lean:200`,
`filtered_loop_commutator_identity`, retains a negative 2G contribution.
The new finite G>=S/4 pays that contribution at this fixed geometry. It is
not the arbitrary-block signed multiplication cost.

BACKWARD: for A=T^t g and b=T^t[g*(F-OWNc)], the exact original split in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:234`,
`original_block_rayleigh_split`, is

    D = Z0*energy(A,psi) + boundaryDrift + signedMultiplicationCost(A,b,psi).

The boundary drift is already bounded by `boundaryDrift_terminal_abs_le`,
same file :261. The unpaid analytic production is the COMBINED energy and
signed multiplication cost relative to Z1*ell(b^2), so that
s*D<=C*Z1*ell(b^2) holds along a JUSTIFIED changing family. The existing
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:157`,
`originalOwnBlockCost_converges`, already transports that finite cost to the
SAME completed response; another normalization wrapper is not needed.
The direct macroscopic-response-ratio route remains an alternative.

The bent result concerns lags one/two; the block producer concerns
lags 2t/2t+1 and growing geometry. Increasing n removes boundary error,
not the response lag. No declaration identifies those two signed costs.
Spatial/spacing control, justified trajectory, continuum survival, physical
mass calibration, full SAME-theory QFT and every compact simple group remain
OPEN. The whole-project Clay target is unchanged.
