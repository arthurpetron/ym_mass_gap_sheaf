/-
# A positive completed norm for the moving-centered BF4 cube observable

The cutoff-one cube coordinate of the moving-centered observable has a fixed
positive rational distance floor at every dense stage.  This file transports
that same floor through the explicit outer pairing limit and into the actual
completed sector inner product.  Thus the preceding nonzero theorem is
strengthened to the constructive statement needed downstream: a named
rational lower bound on the norm square of the same completed vector.

At time zero the literal completed same-object autocorrelation is
definitionally this norm square, so the same floor also gives strict
positivity of the zero-time connected channel.  No rationality of the
completed norm or moment is asserted.

This remains fixed nome and half-extent zero.  It does not inhabit a dynamic
observable pin, prove a uniform physical rate band, construct a projective
continuum limit, or claim the Clay theorem.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
import YMGap.Continuum.FCNormBoundLimit
import YMGap.Continuum.RCStrictPositivity

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredPositiveNorm

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerKernel
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredNonzero
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing
open YMGap.Continuum.RCStrictPositivity

/-! ## 1. The same explicit representative and stage floor -/

/-- The global physical Cauchy representative of the moving-centered
cutoff-one cube observable. -/
def centralPhysicalCutoffOneCubeMovingCenteredGlobalCauchy
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    (centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 0).Cauchy :=
  centralPhysicalVacuumSectorCylinderCauchyToGlobal
    (centralPhysicalVacuumSectorMovingCenteredCauchy
      hw0 hw1 1 0
      (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))

/-- The fixed coordinate floor bounds every diagonal pairing in the actual
global Cauchy representative. -/
theorem centralPhysicalCutoffOneCubeMovingCentered_stage_floor_le_pairing
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (stage : Nat) :
    CReal.leEv
      (CReal.ofQ' (centralPhysicalVacuumSectorCoordinateFloor
        w (Q'.le_of_lt hw0) 1 0))
      (innerLimit hw0 hw1 0
        (centralPhysicalVacuumSectorMovingCenteredPresentation
          hw0 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)
          stage).toLinearObservable
        (centralPhysicalVacuumSectorMovingCenteredPresentation
          hw0 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)
          stage).toLinearObservable) := by
  have hfloor :=
    centralPhysicalCutoffOneCubeMovingCentered_stage_floor_le_zeroDistSq
      hw0 hw1 stage
  exact CReal.leEv_trans hfloor
    (CReal.leEv_of_equiv
      (CReal.Equiv.symm
        (innerLimit_self_equiv_distSq_zero hw0 hw1 0
          (centralPhysicalVacuumSectorMovingCenteredPresentation
            hw0 1 0
            (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)
            stage).toLinearObservable)))

/-! ## 2. Passage through the completed outer limit -/

/-- The same fixed rational floor survives the explicit outer pairing limit.
No nonzero-to-positive inference is used: positivity is transported from the
stagewise coordinate estimate by the constructive limit-order theorem. -/
theorem centralPhysicalCutoffOneCubeMovingCentered_floor_le_pairingLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CReal.leEv
      (CReal.ofQ' (centralPhysicalVacuumSectorCoordinateFloor
        w (Q'.le_of_lt hw0) 1 0))
      (physicalCauchyPairingLimit hw0 hw1 0
        (centralPhysicalCutoffOneCubeMovingCenteredGlobalCauchy hw0 hw1)
        (centralPhysicalCutoffOneCubeMovingCenteredGlobalCauchy hw0 hw1)) := by
  apply CReal.leEv_of_convergesTo_le
    (CReal.convergesTo_const
      (CReal.ofQ' (centralPhysicalVacuumSectorCoordinateFloor
        w (Q'.le_of_lt hw0) 1 0)))
    (physicalCauchyPairingSeq_converges hw0 hw1 0
      (centralPhysicalCutoffOneCubeMovingCenteredGlobalCauchy hw0 hw1)
      (centralPhysicalCutoffOneCubeMovingCenteredGlobalCauchy hw0 hw1))
  intro stage
  simpa only [physicalCauchyPairingSeq,
    centralPhysicalCutoffOneCubeMovingCenteredGlobalCauchy,
    centralPhysicalVacuumSectorCylinderCauchyToGlobal,
    centralPhysicalVacuumSectorMovingCenteredCauchy] using
      (centralPhysicalCutoffOneCubeMovingCentered_stage_floor_le_pairing
        hw0 hw1 stage)

/-- Representative computation for the completed norm of the moving cube
vector.  Naming this quotient bridge prevents downstream proofs from asking
the elaborator to normalize all three quotient lifts simultaneously. -/
theorem centralPhysicalCutoffOneCubeMovingCentered_completedInner_eq_pairingLimitR
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
        (centralPhysicalVacuumSectorMovingCenteredCompletion
          hw0 hw1 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
        (centralPhysicalVacuumSectorMovingCenteredCompletion
          hw0 hw1 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)) =
      physicalCauchyPairingLimitR hw0 hw1 0
        (centralPhysicalCutoffOneCubeMovingCenteredGlobalCauchy hw0 hw1)
        (centralPhysicalCutoffOneCubeMovingCenteredGlobalCauchy hw0 hw1) := rfl

/-- The concrete completed sector norm square retains the explicit positive
rational coordinate floor. -/
theorem centralPhysicalCutoffOneCubeMovingCentered_floor_le_completedInner
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (centralPhysicalVacuumSectorCoordinateFloor
          w (Q'.le_of_lt hw0) 1 0)))
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
        (centralPhysicalVacuumSectorMovingCenteredCompletion
          hw0 hw1 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
        (centralPhysicalVacuumSectorMovingCenteredCompletion
          hw0 hw1 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))) := by
  rw [centralPhysicalCutoffOneCubeMovingCentered_completedInner_eq_pairingLimitR]
  unfold physicalCauchyPairingLimitR
  rw [CReal.RCle_mk]
  exact centralPhysicalCutoffOneCubeMovingCentered_floor_le_pairingLimit
    hw0 hw1

/-- Strict positivity of the completed norm square, with its rational witness
given by the explicit coordinate floor above. -/
theorem centralPhysicalCutoffOneCubeMovingCentered_completedInner_isPositive
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    RCIsPositive
      (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
        (centralPhysicalVacuumSectorMovingCenteredCompletion
          hw0 hw1 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
        (centralPhysicalVacuumSectorMovingCenteredCompletion
          hw0 hw1 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))) := by
  refine ⟨centralPhysicalVacuumSectorCoordinateFloor
      w (Q'.le_of_lt hw0) 1 0, ?_, ?_⟩
  · exact centralPhysicalVacuumSectorCoordinateFloor_pos
      w (Q'.le_of_lt hw0) 1 0
  · exact centralPhysicalCutoffOneCubeMovingCentered_floor_le_completedInner
      hw0 hw1

/-! ## 3. The literal zero-time same-object moment -/

/-- At time zero the literal completed autocorrelation of this same vector is
definitionally its completed norm square. -/
theorem centralPhysicalCutoffOneCubeMovingCentered_autocorrelation_zero_eq_inner
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    centralPhysicalVacuumSectorCylinderCompletedAutocorrelation hw0 hw1 0 0
        (centralPhysicalVacuumSectorMovingCenteredCompletion
          hw0 hw1 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)) =
      centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 0
        (centralPhysicalVacuumSectorMovingCenteredCompletion
          hw0 hw1 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))
        (centralPhysicalVacuumSectorMovingCenteredCompletion
          hw0 hw1 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0)) := rfl

/-- The zero-time same-object completed autocorrelation is strictly positive
by the very same explicit rational coordinate floor. -/
theorem centralPhysicalCutoffOneCubeMovingCentered_autocorrelation_zero_isPositive
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    RCIsPositive
      (centralPhysicalVacuumSectorCylinderCompletedAutocorrelation
        hw0 hw1 0 0
        (centralPhysicalVacuumSectorMovingCenteredCompletion
          hw0 hw1 1 0
          (centralPhysicalCutoffOneCubeIndicatorCoefficient w hw0))) := by
  rw [centralPhysicalCutoffOneCubeMovingCentered_autocorrelation_zero_eq_inner]
  exact centralPhysicalCutoffOneCubeMovingCentered_completedInner_isPositive
    hw0 hw1

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredPositiveNorm

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredPositiveNorm.centralPhysicalCutoffOneCubeMovingCentered_stage_floor_le_pairing
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredPositiveNorm.centralPhysicalCutoffOneCubeMovingCentered_floor_le_completedInner
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredPositiveNorm.centralPhysicalCutoffOneCubeMovingCentered_autocorrelation_zero_isPositive
