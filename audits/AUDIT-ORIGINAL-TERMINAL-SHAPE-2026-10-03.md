# All-depth Haar shape on the ORIGINAL terminal source

The continuum Yang--Mills/Clay target remains OPEN. This increment constructs
an actual terminal estimate at all depths and guarded finite cutoffs, fixed
nome w=1/16 and spatial width two. It does not prove a later-depth favorable
gain, growing-loop estimate, changing-family survival or physical mass gap.

## Constructed forward estimate

Let g_n be the EXISTING original terminal message, H the same bare quaternion
Haar functional, and a_n=H(g_n). Both original guards remain explicit:
K>=1 and headCutoff(w)<=K. The checked conclusions are

    a_n > 0,
    H[(g_n-cap(a_n))^2] <= r^2 a_n^2,  r=1/80000,

at every natural depth n and every guarded finite K. Neither a_n nor its
square is identified with an interacting odd/even partition or OS norm.
The final theorem is stated on the original message, not only a surrogate.

The original terminal is pinned under EVERY supported Haar insertion to the
literal iterated cube transfer of 1. This pin transports products, including
the centered square, through supported-to-full carrier recoding. Locality is
proved for that cube representative, not assumed for the raw original g_n.
Positivity is transported from the actual original terminal certificate.

The actual heat remainder has cap eta=1/1000; its factor has a constructed
floor 1-eta. The shared six-face cube action V has deviation cap delta=1/128.
The certified-floor contraction retains all the other full kinetic factors,
both marginals and zero branches. Its centered squared-norm rate is eta^2,
independent of the number of selected factors; it is not a product of crude
factorwise suprema.

For the cube representative, write M for the actual kinetic map and
m=H(Vg_n)=H(g_(n+1)). The square-root-free induction is

    H(g_n^2) <= (1+r^2)a_n^2,
    m >= (1-delta)a_n > 0,
    Var_H(M(Vg_n)) <= eta^2 Var_H(Vg_n)
                   <= 2 eta^2[delta^2(1+r^2)+r^2]a_n^2
                   <= r^2(1-delta)^2 a_n^2 <= r^2 m^2.

Haar centering minimizes squared distance. The doubled-square estimate
retains BOTH (V-1)g_n and g_n-cap(a_n); no signed cross term is discarded
without the checked Young inequality. The fixed scalar inequality above
is kernel-checked rational arithmetic. No square root is used.

## Exact source test and backward cost leg

For the first-face trace P, original transfer T, arbitrary supported source f
and every K>=1, the checked exact identity is

    H[P T(f)] = w^12 ell[P f].

Here ell is the FULL original interacting weighted functional. In particular,
for b_n=T(g_n(F-c)) the full V_original*g_n source remains inside ell:

    H[P b_n] = w^12 ell[P g_n(F-c)].

There is no locality restriction on f or substituted bare-Haar center.
This identity alone supplies no favorable overlap sign.

Separately, at arbitrary valid nome, width, depth and original SourceLoop,
let c_n be the actual OWN interacting mean, A=Tg_n, psi=F-c_n,
S=ell[(T(g_n psi))^2], Q=ell[(A psi)^2] and E=the SAME even partition.
The actual cap16 certificate constructs

    Q <= 16 E,
    S-lambda^2 Q <= 2 G,
    S >= 32 lambda^2 E  ==>  G >= S/4.

The Q/E cost leg is paid; the useful S/E lower leg is still an explicit
unpaid input. The last implication is not recorded as a positive-gain
producer. No terminal amplitude is cancelled against an unrelated partition.

## Declaration anchors

All paths below begin `lean/YMGap/Continuum/`.

- `BF4ExactSlabFixedSpatialCubeSharpHeatFloor.lean:79`, `sharpHeatRemainder`;
  :92, `sharpCubeRemainder`; :139, `heatAtSharpFloor`.
- `SU2QuaternionProductHeatCertifiedFloorContraction.lean:106`,
  `productMap_conditional_pair_bound`; :171, `productMap_conditional_square_bound`;
  :210, `productMap_centered_square_bound`.
- `BF4ExactSlabFixedSpatialCubeTerminalTransfer.lean:57`, `cubeTerminal`;
  :61, `cubeTerminal_supported`; :72, `cubeTerminal_independent`;
  :123, `terminalMessage_cubeTerminal`.
- `BF4ExactSlabFixedSpatialCubeTerminalVariance.lean:70`, `terminalRadius`;
  :147, `cubeTerminal_certificate`; :154, `cubeTerminal_mean_pin`;
  :181, `cubeTerminal_mass_lower`; :204, `cubeTerminal_mass_positive`;
  :290, `cubeTerminal_variance_bound`.
- `BF4ExactSlabFixedSpatialOriginalTerminalShape.lean:47`, `original_haar_mass_pin`;
  :54, `original_haar_mass_positive`; :80, `original_terminal_variance_bound`.
- `BF4ExactSlabFixedSpatialCubeTerminalTest.lean:69`, `firstFace_transfer_test`;
  :93, `terminal_centered_test`.
- `BF4ExactSlabFixedSpatialOwnGainYoungBudget.lean:60`, `ownGainEndpoint`;
  :64, `ownGainSquare`; :69, `ownGainYoungCost`;
  :111, `ownGainYoungCost_le_sixteen_evenPartition`;
  :144, `own_gain_young_lower`; :189, `own_gain_relative_lower`.

## Accepted verification boundary

Seven final serialized focused checks exited zero with 27 distinct printed
gates (3+3+4+6+2+6+3). All dependencies lie in {propext, Quot.sound};
`terminalRadius` has none. No accepted log has errors, warnings or `sorryAx`.
Failed development logs are excluded. Each launch used a fresh dynamic
capacity check, one worker, reserve 12GiB and worker cap 20GiB through
`scripts/safe_lean_build.py`. Final checks had 85--86% system-wide free
memory, zero swap and no competing Lean jobs; no resource limit was raised.

The source prefix is `lean/YMGap/Continuum/`. The source basename prefix
is `BF4ExactSlabFixedSpatial`, except the explicit SU2 module in the table.
Logs use `/tmp/ym-<log stem>-20261003-<version>.log`. SHA-256 hashes identify
the exact checked source and accepted log.

| Source suffix | Log stem/version | Gates | Source SHA-256 | Log SHA-256 |
| --- | --- | ---: | --- | --- |
| `CubeSharpHeatFloor.lean` | `cube-sharp-floor` / `c` | 3 | `92e2947f8d48e5d25ce57cac974e08a3ee855edd7c6b342381b00f4b7438d42c` | `e81de137e44fee8e63d0d476912d81fe0e70eedc607bcb12bcda0622a6c36832` |
| `SU2QuaternionProductHeatCertifiedFloorContraction.lean` | `certified-floor-contraction` / `a` | 3 | `1175485fc48a6d4bb94a1c749304dbf5337a79288d79f5c05182b69cea490b6e` | `87141668799ce818d7e7de07f2211cfff6d3c23453fd9ac9695369811b318fce` |
| `CubeTerminalTransfer.lean` | `cube-terminal-transfer` / `b` | 4 | `fffccf75ab7d28cb7ef861a47ec7963c4f3cf984dce64250127edfce24f91e2f` | `dd7859df042913df4b2b202e6af4d5ec643e4f45cfde2aec8cc797c579b0485b` |
| `OwnGainYoungBudget.lean` | `own-gain-young-budget` / `b` | 6 | `cde8d415e59851ebbf55715c74724e54733e538caaa18d5eca996dc011df6655` | `fd430db345e91f056170b1193e91d4b084361ee9fd27cdde3cca8f00cb51b5e7` |
| `CubeTerminalTest.lean` | `cube-terminal-test` / `b` | 2 | `8360b453edc55db73ed0358d8d33c437f8225d19a2dd2bd2d74eff15ec8bdced` | `7fa6c993e69f7357e6f0c0e5a47df8e96967f4fa41d800cc428c4746843e0b4b` |
| `CubeTerminalVariance.lean` | `cube-terminal-variance` / `c` | 6 | `ecf45bcd06b75aa076cd64b6a7741c87ef8cc6558f1e7e26f310b36f0a256d64` | `4b69f4945a919085147ad2071f23f45d76ead6be2c66501767ce61fe10669de0` |
| `OriginalTerminalShape.lean` | `original-terminal-shape` / `a` | 3 | `c884bfadbe9496f5790432439e46c14c6bcdcbfe2d1cd94cf327c35a0404dc70` | `b1b2d428c62085d753e4e35f22024cc714552d8580feaf94990ea7c1db4f43e7` |

Root imports are registered only. Aggregate root, broad audit/guard and
progress metric were NOT run. No old Lean proof was edited; no `sorry`,
axiom or classical shortcut was added. CI stays off. The canonical first
fenced chart remains unchanged, SHA-256
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.
No exact displayed claim closed, so no chart is reprinted.

An independent Sol mathematical review passed the radius induction,
full-factor contraction, original square transport and normalization scope.
Sol also passed the final documentation's mathematical scope. An independent
Luna evidence review passed all seven hash pairs, 27 gate outputs, declaration
anchors, import registration and unchanged canonical chart. Neither reviewer
ran builds.

## Next causal frontier, from both ends

FORWARD: pay the actual OWN mean under V_original*g_n*g_(n+1), not under
bare Haar or V_original*g_n alone. Then use the exact tested source to prove
the favorable overlap relative to a_n, compare E to the appropriate Haar
amplitude, and obtain the useful original S/E floor. Preserve the sharper
action channel before subtracting terminal error; the already weakened
depth-zero floor need not retain sufficient slack. None of these later-depth
weighted comparisons is claimed by the present variance theorem.

BACKWARD: the existing completed survival consumer still requires the SAME
macroscopic response ratio, or a sufficient signed block-Rayleigh estimate,
on a JUSTIFIED changing family. The fixed small-nome/width terminal bound
is not that trajectory. Growing-loop/spatial control, spacing and physical
mass calibration, completed/continuum survival, full same-theory QFT structure
and every compact simple group remain open. The whole Clay target is unchanged.
