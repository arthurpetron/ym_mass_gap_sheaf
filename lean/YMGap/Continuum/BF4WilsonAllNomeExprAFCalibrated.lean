/-
# Tying an expression anchor trajectory to the AF-calibrated schedule (shape only)

Companion to `audits/AUDIT-EXPR-ANCHOR-TRAJECTORY-2026-10-06.md` §5. ADDITIVE.

`ExprAnchorTrajectory` alone leaves the schedule, width and radius arbitrary. Here
the schedule is tied to the two-loop AF shape:
* `ExprAFCalibrated tr A κ C := NomeScheduleAFCalibrated tr.schedule A κ C`;
* `AFCalibratedExprAnchorTrajectory`, an `ExprAnchorTrajectory` bundled with
  constants `A κ C` and a proof of `NomeScheduleAFCalibrated` for its schedule.

Instances, stated honestly:
* POSITIVE: the AF-scheduled padded `Y_j`, `afPaddedZeroMomentumExpr`, is calibrated
  with `afA = 1942/1000`, `afKappa = 51/121`, `afC = 4`
  (`afPaddedZeroMomentumExpr_AFCalibrated`, `afPaddedZeroMomentumAFExpr`).
* NEGATIVE (proved): the dyadic padded `Y_j`, `paddedZeroMomentumExpr`, is calibrated
  for NO constants (`paddedZeroMomentumExpr_not_AFCalibrated`, transferred from
  `dyadic_not_AFCalibrated`). So no AF-calibrated bundle has it as its trajectory
  (`no_AFCalibrated_bundle_over_padded`). No positive instance is claimed for it.

HONEST SCOPE. `NomeScheduleAFCalibrated` is the two-loop SHAPE predicate only, i.e.
`|A/(1-w_j) - j - κ⌊log₂(j+1)⌋| ≤ C`:
* there is no concrete lattice spacing `a(w)`;
* `NomeSchedulePhysicalBox` (fixed physical box) stays OPEN;
* the width and radius are NOT tied to anything physical;
* no theorem's analytic content uses the calibration.

`afPaddedZeroMomentumExpr_package` restates the A03 package on the calibrated AF
trajectory. It is conditional on window survival only (H-var/H-ray are discharged
by the plaquette floors), and window survival stays OPEN.

Constructive, no external library; axioms `propext`, `Quot.sound` only.
-/

import YMGap.Continuum.BF4WilsonAllNomeExprAnchorRegression

namespace YMGap.Continuum.BF4WilsonAllNomeExprAFCalibrated

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4DyadicWilsonSquare (side)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (DyadicSmoothedTrajectory)
open YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor (NomeScheduleAFCalibrated)
open YMGap.Continuum.BF4WilsonAllNomeShiftedWindowSurvival (PathShiftedWindowSurvival)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
  (afA afKappa afC afNomeSchedule afNomeSchedule_AFCalibrated dyadic_not_AFCalibrated
   afPaddedZeroMomentumTrajectory afPaddedZeroMomentum_padded)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorTrajectory
open YMGap.Continuum.BF4WilsonAllNomeExprShiftedAnchorPackage
  (ExprShiftedAnchorPackage expr_normalized_anchor_of_windowSurvival_hvar_hray)
open YMGap.Continuum.BF4WilsonAllNomeExprAnchorRegression

/-- The trajectory's nome schedule has the two-loop AF shape with constants
`A, κ, C` (shape only; no `a(w)`, physical box OPEN). -/
def ExprAFCalibrated (tr : ExprAnchorTrajectory) (A kappa C : Q') : Prop :=
  NomeScheduleAFCalibrated tr.schedule A kappa C

/-- An expression anchor trajectory bundled with an AF-shape calibration of its
schedule. Width and radius remain free (not tied to a physical box). -/
structure AFCalibratedExprAnchorTrajectory extends ExprAnchorTrajectory where
  afConstA : Q'
  afConstKappa : Q'
  afConstC : Q'
  calibrated : NomeScheduleAFCalibrated schedule afConstA afConstKappa afConstC

theorem AFCalibratedExprAnchorTrajectory.exprAFCalibrated
    (d : AFCalibratedExprAnchorTrajectory) :
    ExprAFCalibrated d.toExprAnchorTrajectory d.afConstA d.afConstKappa d.afConstC :=
  d.calibrated

/-- For plaquette trajectories, the expression calibration IS the schedule calibration. -/
theorem toExpr_AFCalibrated_iff (tr : DyadicSmoothedTrajectory) (A kappa C : Q') :
    ExprAFCalibrated (toExprTrajectory tr) A kappa C ↔
      NomeScheduleAFCalibrated tr.schedule A kappa C := Iff.rfl

/-! ## Positive instance: the AF-scheduled padded `Y_j` -/

theorem afPaddedZeroMomentumExpr_schedule : afPaddedZeroMomentumExpr.schedule = afNomeSchedule :=
  rfl

/-- **POSITIVE instance.** The AF padded expression trajectory is AF-calibrated with
`afA = 1942/1000`, `afKappa = 51/121`, `afC = 4` (two-loop shape only). -/
theorem afPaddedZeroMomentumExpr_AFCalibrated :
    ExprAFCalibrated afPaddedZeroMomentumExpr afA afKappa afC :=
  afNomeSchedule_AFCalibrated

/-- The bundled AF-calibrated expression trajectory over the AF padded `Y_j`. -/
def afPaddedZeroMomentumAFExpr : AFCalibratedExprAnchorTrajectory where
  toExprAnchorTrajectory := afPaddedZeroMomentumExpr
  afConstA := afA
  afConstKappa := afKappa
  afConstC := afC
  calibrated := afNomeSchedule_AFCalibrated

theorem afPaddedZeroMomentumAFExpr_traj :
    afPaddedZeroMomentumAFExpr.toExprAnchorTrajectory = afPaddedZeroMomentumExpr := rfl

/-- The A03 package on the calibrated AF trajectory, conditional ONLY on window
survival (OPEN). H-var/H-ray are discharged by the plaquette floors. -/
theorem afPaddedZeroMomentumExpr_package (c0 theta delta : Q') (a : Nat) (ha : 1 ≤ a)
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : (1 : Q') ≤ c0)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : c0 ≤ Q'.ofNat (side a) * delta)
    (Hw : ExprShiftedWindowSurvival afPaddedZeroMomentumExpr theta) :
    ExprShiftedAnchorPackage afPaddedZeroMomentumExpr delta hdelta a
      (exprNondegFloor afPaddedZeroMomentumExpr (paddedVar afPaddedZeroMomentumTrajectory)
        (paddedRho afPaddedZeroMomentumTrajectory))
      (exprNondegFloor_pos afPaddedZeroMomentumExpr _ _ afPaddedZeroMomentumExpr_hvar
        afPaddedZeroMomentumExpr_hray) :=
  expr_normalized_anchor_of_windowSurvival_hvar_hray afPaddedZeroMomentumExpr c0 theta delta a
    ha h0 h1 hc0 hc1 hdelta0 hdelta hcd _ _ afPaddedZeroMomentumExpr_hvar
    afPaddedZeroMomentumExpr_hray Hw

/-! ## Negative instance: the dyadic padded `Y_j` -/

/-- **NEGATIVE instance (proved).** The dyadic padded expression trajectory
(`1 - w_j = 2^-(j+1)`) is AF-calibrated for NO constants. -/
theorem paddedZeroMomentumExpr_not_AFCalibrated (A kappa C : Q') :
    ¬ ExprAFCalibrated paddedZeroMomentumExpr A kappa C :=
  dyadic_not_AFCalibrated A kappa C

/-- Hence no AF-calibrated bundle has the dyadic padded `Y_j` as its trajectory. -/
theorem no_AFCalibrated_bundle_over_padded :
    ¬ ∃ d : AFCalibratedExprAnchorTrajectory,
      d.toExprAnchorTrajectory = paddedZeroMomentumExpr := by
  intro ⟨d, hd⟩
  have h := d.exprAFCalibrated
  rw [hd] at h
  exact paddedZeroMomentumExpr_not_AFCalibrated _ _ _ h

#print axioms ExprAFCalibrated
#print axioms AFCalibratedExprAnchorTrajectory
#print axioms AFCalibratedExprAnchorTrajectory.exprAFCalibrated
#print axioms toExpr_AFCalibrated_iff
#print axioms afPaddedZeroMomentumExpr_schedule
#print axioms afPaddedZeroMomentumExpr_AFCalibrated
#print axioms afPaddedZeroMomentumAFExpr
#print axioms afPaddedZeroMomentumAFExpr_traj
#print axioms afPaddedZeroMomentumExpr_package
#print axioms paddedZeroMomentumExpr_not_AFCalibrated
#print axioms no_AFCalibrated_bundle_over_padded

end YMGap.Continuum.BF4WilsonAllNomeExprAFCalibrated
