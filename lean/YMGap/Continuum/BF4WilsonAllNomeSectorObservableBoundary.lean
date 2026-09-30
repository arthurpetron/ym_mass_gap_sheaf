/-
# A literal width-one observable does not preserve the witnessed time sector

The original time-zero plaquette multiplier sends the constant state outside
the represented closure of the original one-step time range. This is a
fixed-width obstruction to restricting that multiplier to this sector, not a
claim about positive-time-sandwiched insertions or physical reconstruction.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeSector
import YMGap.Continuum.BF4WilsonAllNomeFringeTimeKernel
import YMGap.Continuum.BF4WilsonAllNomeTimeZeroVacuum
import YMGap.Continuum.BF4WilsonAllNomeCenteringPin

namespace YMGap.Continuum.BF4WilsonAllNomeSectorObservableBoundary

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion embed unitState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime completedUnit_fixed)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedZero completedZero_embed)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteExcitation
  (plaquetteExcitation plaquetteExcitation_ne_zero originFace originFace_mem)
open YMGap.Continuum.BF4WilsonAllNomeFringeTimeKernel (originPlaquette_time_one_zero)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure (RangeLimit kernel_zero)
open YMGap.Continuum.BF4WilsonAllNomeUnitProjection
  (unitCauchy unitCoefficient unitCoefficientCauchy unitProjection unitProjection_mk
    centeredPart)
open YMGap.Continuum.BF4WilsonAllNomeCenteringPin (centeredPart_embed)
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator (completedMultiply)
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroVacuum (completedMultiply_unitState)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

local notation "D" => seminorm hw0 hw1 (width := 1)
local notation "V" => Completion hw0 hw1 1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := 1)))

def originLoop := plaquetteLoop originFace (originFace_mem 0)

def originRaw : V := embed hw0 hw1 (loopState originLoop)

def originCentered : V :=
  Subtype.val (plaquetteExcitation hw0 hw1 1 originFace (originFace_mem 0))

/-- The already exhibited nonzero time-kernel vector cannot lie in the
witnessed closure of the original one-step time range. -/
theorem origin_centered_not_range :
    RangeLimit hw0 hw1 (originCentered hw0 hw1) → False := by
  intro R
  have hz : originCentered hw0 hw1 = completedZero hw0 hw1 1 :=
    kernel_zero hw0 hw1 R (originPlaquette_time_one_zero hw0 hw1)
  have hz' : originCentered hw0 hw1 =
      embed hw0 hw1 (YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra.zero 1) := by
    simpa only [completedZero_embed] using hz
  exact (plaquetteExcitation_ne_zero hw0 hw1 1 originFace (originFace_mem 0)) hz'

/-- The constant state has an explicit original-time preimage. -/
def unitRange : RangeLimit hw0 hw1 (unitState hw0 hw1 1) := by
  let X : (D).Cauchy := unitCauchy hw0 hw1
  have hclass : Class X = unitState hw0 hw1 1 := rfl
  have htime : completedTime hw0 hw1 1 (Class X) = unitState hw0 hw1 1 := by
    rw [hclass]
    exact completedUnit_fixed hw0 hw1 1
  exact htime ▸ BF4WilsonAllNomeTimeRangeClosure.fromTime hw0 hw1 X

/-- The actual computed unit projection of the raw loop is still in the
same witnessed range sector, with its scalar approximation modulus retained. -/
def originProjectionRange :
    RangeLimit hw0 hw1 (unitProjection hw0 hw1 (originRaw hw0 hw1)) := by
  let X : (D).Cauchy := (D).constant (loopState originLoop)
  have hclass : Class X = originRaw hw0 hw1 := rfl
  have hp : unitProjection hw0 hw1 (originRaw hw0 hw1) =
      BF4WilsonAllNomeCompletedRealScalar.completedRealSmul hw0 hw1
        (unitCoefficient hw0 hw1 X) (unitCoefficientCauchy hw0 hw1 X)
        (unitState hw0 hw1 1) := by
    rw [← hclass]
    exact unitProjection_mk hw0 hw1 X
  exact hp.symm ▸ BF4WilsonAllNomeTimeRangeLinear.realSmul hw0 hw1
    (unitCoefficient hw0 hw1 X) (unitCoefficientCauchy hw0 hw1 X)
    (unitRange hw0 hw1)

/-- The original uncentered time-zero plaquette is also outside the sector:
its unit component is inside, while its centered component is not. -/
theorem origin_raw_not_range : RangeLimit hw0 hw1 (originRaw hw0 hw1) → False := by
  intro R
  have hc : RangeLimit hw0 hw1
      (centeredPart hw0 hw1 (originRaw hw0 hw1)) :=
    BF4WilsonAllNomeTimeRangeLinear.subtract hw0 hw1 R
      (originProjectionRange hw0 hw1)
  have hp : centeredPart hw0 hw1 (originRaw hw0 hw1) =
      originCentered hw0 hw1 := by
    change centeredPart hw0 hw1 (embed hw0 hw1 (loopState originLoop)) =
      BF4WilsonAllNomeCenteredVector.centeredVector hw0 hw1 (loopState originLoop)
    exact centeredPart_embed hw0 hw1 (loopState originLoop)
  exact origin_centered_not_range hw0 hw1 (hp ▸ hc)

/-- No endomap of this witnessed width-one sector can agree everywhere with
the literal original time-zero plaquette multiplier. The unit is the witness. -/
theorem no_original_multiplier_sector_map
    (F : BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := 1) →
      BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := 1))
    (hF : ∀ x, (F x).val =
      completedMultiply hw0 hw1 originLoop 1 x.val) : False := by
  let U : BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := 1) :=
    ⟨unitState hw0 hw1 1, unitRange hw0 hw1⟩
  have hraw : (F U).val = originRaw hw0 hw1 := by
    rw [hF U]
    exact completedMultiply_unitState hw0 hw1 originLoop
  exact origin_raw_not_range hw0 hw1 (hraw ▸ (F U).range)

#print axioms originLoop
#print axioms originRaw
#print axioms originCentered
#print axioms origin_centered_not_range
#print axioms unitRange
#print axioms originProjectionRange
#print axioms origin_raw_not_range
#print axioms no_original_multiplier_sector_map

end YMGap.Continuum.BF4WilsonAllNomeSectorObservableBoundary
