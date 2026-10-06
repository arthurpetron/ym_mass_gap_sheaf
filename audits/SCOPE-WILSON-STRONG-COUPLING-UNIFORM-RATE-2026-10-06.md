# Scope: first non-Doeblin width-uniform rate (strong-coupling interface test) (2026-10-06 PT)

This is an INTERFACE TEST. It makes NO progress on the Clay gap and does NOT give the AF
margin on `afPaddedZeroMomentumAFExpr`.

## Exact target

Find `w* ∈ (0,1)` and `r* < 1` such that for every `w ≤ w*` and every spatial width,
there is an all-vector vacuum-square contraction at rate `r*` (independent of width).

On the Spatial Union / Descent carrier this is ALREADY proved:
- Rate: `BF4WilsonDescentUniformConnectedDecay.twoStepRate = timeRate² ≈ 1/16`
  (`twoStepRate_eq`, `:51`).
- Contraction: `BF4WilsonDescentCompletedGap.oneStep_norm_gap` (`:145`):
  `B(Tx,Tx) ≤ (1/16)·B(x,x)` for every completed unit-orthogonal `x`.
- Guards (the strong-coupling window):
  - `heatRatio w ≤ 1/2` (`heatRatio w = 32·w³`, so `w ≤ 1/4`);
  - `heatRemainderBound w < 1` (`= 128·w³`);
  - `entropyRate 625 (adjustedCoreRate w hd) < 1`.
- Width independence: the rate is a constant; the carrier is the Spatial Union completion,
  which already ranges over all bases.

## What this does NOT give

1. **Not on the all-nome literal-width carrier.** `WilsonVacuumSqContraction` is typed on
   `BF4WilsonAllNomeCompletedInner.Completion`. Descent lives on
   `BF4WilsonSpatialUnionSeminorm.UnionCompletion`. Bridging them is OPEN (carrier identity /
   transfer identification); it is not done here.
2. **Not on the AF trajectory.** Every `NomeSchedule` has `w_j → 1` (`nome_limit`), so it
   eventually leaves `w ≤ w*`. In particular `afPaddedZeroMomentumAFExpr` leaves the window.
   A width-uniform strong-coupling rate therefore does NOT witness
   `WilsonAFPaddedGapInput` on any `NomeSchedule` trajectory.
3. **Incompatible with the B04 upper half on unbounded side.** A constant `r* < 1` gives
   `side_j(1−r*) → ∞`, so it cannot satisfy `side_j(1−r_j) ≤ ceiling` for all `j`. The
   step-ratio ⇒ upper-half compatibility of cf08f0df therefore cannot hold together with a
   constant rate on any trajectory with unbounded `side_j`. The lower margin alone is fine:
   `m·2^-j ≤ 1−r*` holds for all `j` with `m = 1−r*`.

## Lemma plan (this pass)

| Piece | Status |
|---|---|
| Package Descent `oneStep_norm_gap` as `StrongCouplingVacuumSqContraction` | DONE (plumbing) |
| Dyadic lower margin at constant `twoStepRate` | DONE |
| Concrete `w*` inhabitant of all three guards | PARTIAL: `smallNome = 1/16` has `heatRatio ≤ 1/2` and `heatRemainderBound < 1` by `decide`; the `entropyRate 625 (adjustedCoreRate …)` guard is kept as a hypothesis (existing Descent consumers do the same) |
| Obstruction: constant rate ⇏ B04 upper half for all `j` | DONE |
| Non-vacuity of contraction + lower margin under the Descent guards | DONE |
| All-nome `WilsonVacuumSqContraction` at a width-independent rate | OPEN (needs a carrier bridge or a new all-nome producer) |
| Witness of `WilsonAFPaddedGapInput` on AF | OPEN (needs a weak-coupling, volume-uniform producer with `1−r_j ≍ 2^-j`) |

## Candidate routes for the OPEN all-nome piece (unchanged from the producer note)

- Dobrushin influence / tensorized one-slice Poincaré on the two-slice Haar carrier.
- Bakry–Émery with `n`-uniform curvature (strong coupling only).
- The Descent rate, transported across a Spatial-Union ↔ all-nome bridge (finite algebra if
  the completions coincide; not known).

## Interface-test use of `wilsonGapBranch_afPadded_generic`

Do NOT feed the constant Descent rate into `wilsonGapBranch_afPadded_generic` on `trAF`:
both the window exit and the upper-half obstruction apply. The live consumer for this rate
is the lower-margin packaging on the Descent carrier. AF still needs a weak-coupling producer.
