/-
# Wilson gap branch on the AF-padded `Y_j` trajectory (INSTANTIATION; PLUMBING ONLY)

**VACUOUS — DEAD END (2026-10-06 PT).** The X2 hypothesis `WilsonLowerMargin
(exprMixRateFamily trAF) m` is UNSATISFIABLE for every `m`. This is proved as
`not_wilsonLowerMargin_mixRate_afPadded` (`BF4WilsonAllNomeWilsonMixRateDeadEnd`), from
`mixFraction ≤ (1/32)^width` uniformly in `w`, with `width_j = 4^j + 1`. So
`wilsonGapBranch_afPadded` is true but vacuous.
* The live gap-side frontier is `WilsonAFPaddedGapInput`: SOME rate family with an
  all-vector contraction and `m·2^-j ≤ 1 − r_j`.
* That frontier is consumed by `wilsonGapBranch_afPadded_generic`.
The statement below is unchanged.

Companion to `audits/SCOPE-WILSON-CARRIER-GAP-RETARGET-2026-10-06.md` (§X1 instance). ADDITIVE.

This instantiates `wilsonGapBranch_mixRate` (`BF4WilsonAllNomeWilsonDynamicFamily`) on the
AF-calibrated padded zero-momentum trajectory.
* The trajectory is `afPaddedZeroMomentumAFExpr.toExprAnchorTrajectory`, which is
  `afPaddedZeroMomentumExpr = toExprTrajectory afPaddedZeroMomentumTrajectory` by `rfl`.
* The rate family is `exprMixRateFamily` on that SAME trajectory.

H-var and H-ray are DISCHARGED, with concrete floors and no open hypothesis:
* H-var: `afPaddedZeroMomentumExpr_hvar`, i.e. `toExpr_hvar`, with
  `v_j = paddedVar = varianceFloor(w_j)·Σc²`.
* H-ray: `afPaddedZeroMomentumExpr_hray`, i.e. `toExpr_hray` with
  `afPaddedZeroMomentum_padded`, giving `ρ_j = paddedRho = familyResponseFraction(w_j, |faces_j|)`.

`wilsonGapBranch_afPadded` has EXACTLY two open analytic hypotheses:
1. the step ratio `ExprStepRatio trAF ρ' k`, with the bound `side_j(1−ρ'_j) ≤ c` for
   `j ≥ j0` and the ranges `0 ≤ ρ'_j` (`j ≥ 1`), `ρ'_j ≤ 1` (`j ≥ j0`);
2. X2, `WilsonLowerMargin (exprMixRateFamily trAF) m`.
The rest are arithmetic parameters: `ha hC hcC hj0 hj0' hdelta0 hdelta hcd hk`.

Conclusions:
* the AF calibration (two-loop SHAPE only);
* A03;
* the Wilson B04 band;
* squared autocorrelation decay at every scale and every vacuum-complement vector;
* `m ≤ 2^(2C+3)`.

NO PROGRESS on either open input.
* X2 at the `mixRate` Doeblin rate is not expected to hold; it needs a new producer.
* X3 is a TODO, J02-level: the Wilson `ObservablePin` and the OS/GNS re-pointing.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily
import YMGap.Continuum.BF4WilsonAllNomeExprAFCalibrated

namespace YMGap.Continuum.BF4WilsonAllNomeWilsonGapBranchAFPadded

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime VacuumComplement)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
  (afA afKappa afC afPaddedZeroMomentumTrajectory)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprShiftedAnchorPackage (ExprShiftedAnchorPackage)
open YMGap.Continuum.BF4WilsonAllNomeExprStepRatioWindowSurvival (ExprStepRatio)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorRegression
  (paddedVar paddedRho afPaddedZeroMomentumExpr_hvar afPaddedZeroMomentumExpr_hray)
open YMGap.Continuum.BF4WilsonAllNomeExprAFCalibrated
  (ExprAFCalibrated afPaddedZeroMomentumAFExpr)
open YMGap.Continuum.BF4WilsonAllNomeWilsonDynamicFamily

/-- The AF-padded `Y_j` trajectory, as an expression anchor trajectory. -/
local notation "trAF" => afPaddedZeroMomentumAFExpr.toExprAnchorTrajectory

/-- Squared autocorrelation decay on every scale/vector of a Wilson family (Prop). -/
def WilsonFamilyDecay (F : WilsonDynamicFamily) : Prop :=
  ∀ j n (y : VacuumComplement (F.nome_pos j) (F.nome_lt_one j) (width := F.width j)),
    RCle
      (RCmul (completedInner (F.nome_pos j) (F.nome_lt_one j) y.val
          (completedTime (F.nome_pos j) (F.nome_lt_one j) n y.val))
        (completedInner (F.nome_pos j) (F.nome_lt_one j) y.val
          (completedTime (F.nome_pos j) (F.nome_lt_one j) n y.val)))
      (RCmul (RCscale ((F.rate j * F.rate j)^n)
          (completedInner (F.nome_pos j) (F.nome_lt_one j) y.val y.val))
        (completedInner (F.nome_pos j) (F.nome_lt_one j) y.val y.val))

theorem wilsonFamilyDecay (F : WilsonDynamicFamily) : WilsonFamilyDecay F :=
  fun j n y => F.completedAutocorrelation_sq_decay j n y

/-- **Wilson gap branch on the AF-padded `Y_j` trajectory.** VACUOUS: `hX2` is unsatisfiable
(`not_wilsonLowerMargin_mixRate_afPadded`); see `wilsonGapBranch_afPadded_generic`.
Open analytic hypotheses: the step ratio (`H`, `hc`, `hrho'0`, `hrho'1`) and X2 (`hX2`).
H-var and H-ray are discharged, and the contraction is `mixRate` (unconditional). -/
theorem wilsonGapBranch_afPadded
    (c delta : Q') (C j0 a : Nat) (ha : 1 ≤ a) (hC : 1 ≤ C) (hcC : c ≤ Q'.ofNat C)
    (hj0 : 2*C ≤ side j0) (hj0' : j0 ≤ 2*C+4)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : Q'.ofNat (2^(2*C+3)) ≤ Q'.ofNat (side a) * delta)
    (rho' : Nat → Q') (k : Nat → Nat)
    (hrho'0 : ∀ j, 1 ≤ j → (0 : Q') ≤ rho' j) (hrho'1 : ∀ j, j0 ≤ j → rho' j ≤ 1)
    (hk : ∀ j, 1 ≤ j → k j ≤ side j / 2)
    (hc : ∀ j, j0 ≤ j → Q'.ofNat (side j) * ((1 : Q') - rho' j) ≤ c)
    (H : ExprStepRatio trAF rho' k) (m : Q')
    (hX2 : WilsonLowerMargin (exprMixRateFamily trAF) m) :
    ExprAFCalibrated trAF afA afKappa afC ∧
      ExprShiftedAnchorPackage trAF delta hdelta a
        (exprNondegFloor trAF (paddedVar afPaddedZeroMomentumTrajectory)
          (paddedRho afPaddedZeroMomentumTrajectory))
        (exprNondegFloor_pos trAF _ _ afPaddedZeroMomentumExpr_hvar
          afPaddedZeroMomentumExpr_hray) ∧
      WilsonPhysicalRateBand (exprMixRateFamily trAF) ∧
      WilsonFamilyDecay (exprMixRateFamily trAF) ∧
      m ≤ Q'.ofNat (2^(2*C+3)) :=
  have h := wilsonGapBranch_mixRate trAF c delta C j0 a ha hC hcC hj0 hj0' hdelta0 hdelta hcd
    (paddedVar afPaddedZeroMomentumTrajectory) (paddedRho afPaddedZeroMomentumTrajectory)
    afPaddedZeroMomentumExpr_hvar afPaddedZeroMomentumExpr_hray rho' k hrho'0 hrho'1 hk hc H m hX2
  ⟨afPaddedZeroMomentumAFExpr.exprAFCalibrated, h.1, h.2.1,
    wilsonFamilyDecay _, h.2.2.2⟩

#print axioms WilsonFamilyDecay
#print axioms wilsonFamilyDecay
#print axioms wilsonGapBranch_afPadded

end YMGap.Continuum.BF4WilsonAllNomeWilsonGapBranchAFPadded
