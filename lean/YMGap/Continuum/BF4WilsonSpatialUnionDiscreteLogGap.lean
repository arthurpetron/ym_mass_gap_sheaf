/-
# Exact logarithmic gap of the current fixed-spacing transfer rate

The current completed Wilson sector has an explicit rational two-step decay
rate `twoStepRate nome hd` in `(0,1)`.  The constructive binary range-reduction
machinery therefore produces an exact positive CReal `-log(rate)`, together
with a genuine logarithm pin.  This is a dimensionless discrete transfer mass
certificate only: no lattice-spacing conversion, canonical OS/GNS
identification, or continuum mass assertion is made here.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionCurrentSector
import YMGap.Continuum.HamiltonianAllSep

namespace YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealLog
open YMGap.Continuum.HamiltonianAllSep
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
  (nome nome_pos nome_lt_one)
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison (existingNome_guards)
open YMGap.Continuum.BF4ExactSlabSummableCoreRate (existingNome_entropyRate)

local notation "hsmall" => And.left existingNome_guards
local notation "hd" => And.right existingNome_guards
local notation "hs" => And.right existingNome_entropyRate

/-- The rational separator already controlling current completed-carrier decay. -/
def currentRate : Q' := twoStepRate nome hd

theorem currentRate_pos : (0 : Q') < currentRate :=
  twoStepRate_positive nome_pos hd

theorem currentRate_lt_one : currentRate < (1 : Q') :=
  twoStepRate_lt_one nome_pos hd hs

theorem currentRate_num_pos : 0 < currentRate.num :=
  Q'.num_pos_of_pos currentRate_pos

theorem currentRate_num_lt_den : currentRate.num < (currentRate.den : Int) := by
  have h := currentRate_lt_one
  change currentRate.num * (1 : Int) < (1 : Int) * (currentRate.den : Int) at h
  simpa only [Int.mul_one, Int.one_mul] using h

/-- The constructive binary range reduction of the current rational rate. -/
def currentRateBinExp : BinExpData currentRate :=
  binExpOf currentRate currentRate_num_pos currentRate_num_lt_den

def currentRateMantissa : Q' :=
  mant currentRate currentRateBinExp.k

theorem currentRateMantissa_pos_plus_one :
    (0 : Q') < currentRateMantissa + 1 :=
  mant_pos currentRate currentRateBinExp.k currentRate_num_pos

theorem currentRateMantissa_lt_one : currentRateMantissa < (1 : Q') :=
  mant_lt_one currentRate currentRateBinExp.k currentRateBinExp.hlt

theorem currentRateMantissa_window :
    Q'.abs (yOf currentRateMantissa currentRateMantissa_pos_plus_one) ≤ recipOdd 1 :=
  mant_window currentRate currentRateBinExp currentRate_num_pos

/-- The exact positive dimensionless transfer mass `-log(currentRate)`. -/
def currentTransferMass : CReal :=
  hamiltonianGapRealAll currentRateMantissa currentRateBinExp.k
    currentRateMantissa_pos_plus_one
    currentRateMantissa_window

theorem currentTransferMass_pos : CReal.IsPositive currentTransferMass :=
  hamiltonianGapRealAll_pos currentRateMantissa currentRateBinExp.k
    currentRateMantissa_pos_plus_one
    currentRateMantissa_lt_one currentRateMantissa_window

/-- A genuine range-reduction witness for the logarithm of the current rate. -/
def currentTransferLogReduction :
    CRealLogRangeReduction (CReal.ofQ' currentRate) :=
  reductionOf currentRate currentRateBinExp currentRate_num_pos

/-- The transfer mass is exactly pinned to the constructive logarithm of the
current rate. -/
theorem currentTransferMass_log_pin :
    CReal.Equiv currentTransferMass
      (CReal.neg (CReal.log (CReal.ofQ' currentRate)
        currentTransferLogReduction)) := by
  unfold currentTransferMass currentTransferLogReduction CReal.log reductionOf
  refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
  exact add_neg_eqv_neg_neg_add
    ((kLog2 currentRateBinExp.k).approx n)
    ((logRat currentRateMantissa currentRateMantissa_pos_plus_one
      currentRateMantissa_window).approx n)

end YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap.currentRate
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap.currentRate_pos
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap.currentRate_lt_one
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap.currentRateBinExp
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap.currentRateMantissa
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap.currentTransferMass
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap.currentTransferMass_pos
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap.currentTransferLogReduction
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionDiscreteLogGap.currentTransferMass_log_pin
