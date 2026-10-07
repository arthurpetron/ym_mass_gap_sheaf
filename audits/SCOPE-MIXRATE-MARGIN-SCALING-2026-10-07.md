# Scope: the w- and width-dependence of the proved mixRate margin (2026-10-07)

Lean: `YMGap.Continuum.MixRateMarginScaling`. PROVED; axioms ⊆ {propext, Quot.sound}.

## (a) Closed form

`mixFraction w width = kineticFloor/kineticCap = (headFloor w / prefixCap w)^{n(width)}`, from
`BF4ExactSlabFixedSpatialTransferSandwich` and `…TransferMixingRate`.

- **`n(width)`** = `(temporalFaces width).length`, the temporal plaquettes of the time-0 layer
  of the `width³` spatial box (`BF4ExactSlabFixedSpatialFacePlacement.temporalFaces`).
  - A compiled `#eval` gives 3, 24, 81, 192 for width 1..4, i.e. `n = 3·width³`.
  - Lean proof: `temporalFaces_one` (`n(1) = 3`) only, by kernel `decide`. Width 2 times out
    at 200k heartbeats, so `n = 3·width³` for width ≥ 2 is a measurement, NOT proved.
- **`headFloor w`** = `½·SU2PointwiseHeatStrictFloor.floor w`
  = `½·(E·E)·¼` with `E = ½·euler w (cutoff w)`, a truncated Euler product `Π_{k≤C}(1−w^k)`.
  - The existing `headFloor_le_oneThirtySecond` gives `headFloor ≤ 1/32` for all w.
- **`prefixCap w`** = `Σ_{s<L}(s+1)²w^{s(s+2)}` plus the closed tail.
  - The existing `prefixCap_ge_one` gives `prefixCap ≥ 1` (the constant mode).
- No exact rational evaluation at w ∈ {1/1024, 1/8, 1/2}. The truncation cutoffs
  (`lossCutoff`, `spacingLabelCutoff`) give huge denominators, so I did not attempt it.
  The uniform bound below already decides (c).

## (b) Lean statements

- `mixFraction_le_pow (hw0 hw1 width) : mixFraction hw0 hw1 width ≤ (1/32)^{(temporalFaces width).length}`,
  for every 0 < w < 1.
- `mixRate_ge : 1 − (1/32)^{n(width)} ≤ mixRate hw0 hw1 width`.
- `temporalFaces_one : (temporalFaces 1).length = 3`.
- `mixFraction_le_width1 : mixFraction hw0 hw1 1 ≤ 1/32768` (= 2^{-15}), for all w.

Evaluated points: width 1 is proved for every w, which covers w = 1/1024, 1/8 and 1/2.
Widths 2 and 4 follow from `mixFraction_le_pow` together with the measured n = 24 and 192:
2^{-120} and 2^{-960}.

## (c) Verdicts

- **Width-uniform?** NO.
  - Even at extreme strong coupling (w → 0) the margin is ≤ 2^{-5·n(width)} = 2^{-15·width³}
    (exponent proved at width 1, measured beyond).
  - The loss is structural: one factor ≤ 1/32 per temporal face. The floor/cap spread
    (`thirtyTwo_mul_headFloor_le_prefixCap`) is paid face by face, so the Doeblin margin is
    exponentially small in the VOLUME of the layer.
- **As w → 1?** Heuristic, not formalized.
  - `prefixCap ~ c(1−w)^{-3/2}` → ∞, and the Euler-product floor decays roughly like
    `exp(−π²/(3(1−w)))`.
  - So the per-face ratio q(w) → 0 essentially exponentially in 1/(1−w), and the margin is
    q(w)^{3·width³}.
  - The rigorous statement is only the uniform bound q ≤ 1/32.
- **Compatible with the needed shapes?** NO, for either one.
  - Under the RG step the width doubles, `width_j = 2^j W₀`, so `n_j = 3W₀³·8^j` and
    `m_j ≤ 2^{-15 W₀³ 8^j}`.
  - *2^n-weighted* (`2^n m_{j₀+n} ≥ const`): we get `2^n m_{j₀+n} ≤ 2^{n − 15W₀³8^{j₀+n}} → 0`
    doubly exponentially. That is a gap of a factor 2^{15W₀³8^{j₀+n} − n}.
  - *Fresh-per-scale halving* (`m_j ≥ 1/(2M₀)`): it fails as soon as
    `15W₀³8^j > log₂(2M₀)`, which happens already at j = 0 unless M₀ ≥ 2^{15W₀³−1}.
  - Even at frozen width it needs w frozen too. Neither is the RG regime.
- **Measured gap.** The proved margin is ≤ 2^{-15·width³}; the needed margin is ≥ const·2^{-j}
  (or ≥ const). The Doeblin/sandwich route (floor-to-cap per face) cannot supply a
  volume-uniform margin. A route that does not multiply per-face constants is required, for
  example a cluster or polymer expansion with a width-independent rate. That is OPEN.

## U(1) rule

The same per-face sandwich applies verbatim to the U(1) analogue, so this is an obstruction to
the METHOD, not evidence about any gauge group. No claim of absence of a gap is made.
