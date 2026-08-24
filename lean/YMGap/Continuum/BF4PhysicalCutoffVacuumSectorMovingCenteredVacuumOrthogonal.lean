/-
# The moving centered completion lies in the actual vacuum complement

The preceding modules constructed one explicit-modulus completed vector from
the same finite cylinder with a moving rational root correction, and proved
that the dense representatives' actual vacuum pairings converge to zero.
Here those two paths are identified at the representative-level completed
pairing.  Limit uniqueness then places that exact completed vector in the
actual global vacuum complement.

This does not prove that the vector is nonzero, identify its completed
transfer moments, inhabit a dynamic observable pin, or make a continuum/Clay
claim.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumOrthogonal

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseVacuumPairing
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing
open YMGap.Continuum.CRealSeminormCompletion

/-! ## One representative pairing sequence, two already constructed limits -/

/-- The representative-level completed pairing of the moving Cauchy vector
with the constant vacuum converges to zero.  The termwise identification is
exactly the previously proved dense vacuum-pairing/pulled-mean theorem. -/
theorem centralPhysicalVacuumSectorMovingCentered_pairingLimit_equiv_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal
          (centralPhysicalVacuumSectorMovingCenteredCauchy
            hw0 hw1 base half coefficient))
        ((centralPhysicalCutoffLinearSquaredSeminorm
          hw0 hw1 half).constant centralPhysicalLinearVacuum))
      CReal.czero := by
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := physicalCauchyPairingSeq hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal
        (centralPhysicalVacuumSectorMovingCenteredCauchy
          hw0 hw1 base half coefficient))
      ((centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).constant centralPhysicalLinearVacuum))
    (bSeq := fun stage =>
      centralPhysicalFinitePulledVacuumSectorWeightedMeanCutoffLimit
        hw0 hw1 base half
        (centralPhysicalVacuumSectorMovingCenteredPresentation
          hw0 base half coefficient stage).coefficient)
  · intro stage
    simpa only [physicalCauchyPairingSeq,
      centralPhysicalVacuumSectorCylinderCauchyToGlobal,
      centralPhysicalVacuumSectorMovingCenteredCauchy,
      SquaredSeminorm.constant] using
      (centralPhysicalVacuumSectorCylinder_innerLimitVacuum_equiv_pulledMean
        hw0 hw1 half
        (centralPhysicalVacuumSectorMovingCenteredPresentation
          hw0 base half coefficient stage))
  · exact physicalCauchyPairingSeq_converges hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal
        (centralPhysicalVacuumSectorMovingCenteredCauchy
          hw0 hw1 base half coefficient))
      ((centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).constant centralPhysicalLinearVacuum)
  · exact centralPhysicalMovingCenteredMeanLimit_converges_zero
      hw0 hw1 base half coefficient

/-! ## Descent to the actual completed vector -/

/-- The exact global completed vector built from the moving rationally
centered observable is orthogonal to the normalized completed vacuum. -/
theorem centralPhysicalVacuumSectorMovingCenteredGlobalVector_vacuumOrthogonal
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat) (coefficient : Nat → Q') :
    CentralPhysicalCutoffCompletedVacuumOrthogonal hw0 hw1 half
      (centralPhysicalVacuumSectorMovingCenteredGlobalVector
        hw0 hw1 base half coefficient) := by
  unfold CentralPhysicalCutoffCompletedVacuumOrthogonal
    centralPhysicalVacuumSectorMovingCenteredGlobalVector
    centralPhysicalVacuumSectorMovingCenteredCompletion
    centralPhysicalCutoffCompletedVacuum
    embedCentralPhysicalLinearObservable
  change physicalCauchyPairingLimitR hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal
        (centralPhysicalVacuumSectorMovingCenteredCauchy
          hw0 hw1 base half coefficient))
      ((centralPhysicalCutoffLinearSquaredSeminorm
        hw0 hw1 half).constant centralPhysicalLinearVacuum) =
    CReal.RCzero
  unfold physicalCauchyPairingLimitR CReal.RCzero
  exact Quotient.sound
    (centralPhysicalVacuumSectorMovingCentered_pairingLimit_equiv_zero
      hw0 hw1 base half coefficient)

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumOrthogonal

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumOrthogonal.centralPhysicalVacuumSectorMovingCentered_pairingLimit_equiv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumOrthogonal.centralPhysicalVacuumSectorMovingCenteredGlobalVector_vacuumOrthogonal
