/-
# Persistent endpoint energy on arbitrary completed sector vectors

The dense persistent-path estimate extends to an arbitrary vector of the
actual canonical vacuum-sector completion.  The adaptive outer-matrix input
is used only as a cofinal representative; its proved closeness and quotient
class equality ensure that both endpoint coordinates and both completed forms
belong to the original vector.

No spectral rate, separation statement, fixed-vector theorem, or continuum
claim is introduced.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentCoordinate
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergyLimit
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawDiagonal
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawMatrix
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedEndpointEnergy

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawDiagonal
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOuterRawMatrix
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentCoordinate
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergyLimit
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling

private theorem creal_add_congr {a a' b b' : CReal}
    (ha : CReal.Equiv a a') (hb : CReal.Equiv b b') :
    CReal.Equiv (CReal.add a b) (CReal.add a' b') :=
  (CReal.add_congr_left ha).trans (CReal.add_congr_right hb)

private theorem creal_mul_congr {a a' b b' : CReal}
    (ha : CReal.Equiv a a') (hb : CReal.Equiv b b') :
    CReal.Equiv (CReal.mul a b) (CReal.mul a' b') :=
  (CReal.mul_congr_left ha).trans
    ((CRealAlg.cmul_comm a' b).trans
      ((CReal.mul_congr_left hb).trans (CRealAlg.cmul_comm b' a')))

/-- Twice the completed norm minus twice the completed transfer form, on the
literal completed sector vector. -/
def centralPhysicalVacuumSectorCompletedDirichlet
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (vector : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half) : CReal.RC :=
  let diagonal := centralPhysicalVacuumSectorCylinderCompletedInner
    hw0 hw1 half vector vector
  let matrix := centralPhysicalVacuumSectorCylinderCompletedInner
    hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCompletedTransfer
        hw0 hw1 half vector) vector
  CReal.RCadd (CReal.RCadd diagonal diagonal)
    (CReal.RCneg (CReal.RCadd matrix matrix))

/-- Every persistent finite-base endpoint difference of an arbitrary
completed sector vector is controlled by its actual same-vector completed
Dirichlet form. -/
theorem fixedBaseFloor_mul_completedEndpointSq_le_completedDirichlet
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (vector : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half) :
    let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
    let leftCoordinate := completedCoordinate
      hw0 hw1 base half left hleft vector
    let rightCoordinate := completedCoordinate
      hw0 hw1 base half right hright vector
    CReal.RCle
      (CReal.RCmul
        (Quotient.mk CReal.crealSetoid (CReal.ofQ' certificate.floor))
        (CReal.RCmul
          (CReal.RCadd leftCoordinate (CReal.RCneg rightCoordinate))
          (CReal.RCadd leftCoordinate (CReal.RCneg rightCoordinate))))
      (CReal.RCmul
        (Quotient.mk CReal.crealSetoid
          (CReal.ofQ' (centralPhysicalFiniteVacuumSectorPathCeiling
            w (Q'.le_of_lt hw0) base half)))
        (centralPhysicalVacuumSectorCompletedDirichlet
          hw0 hw1 half vector)) := by
  let D := centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half
  refine Quotient.inductionOn vector ?_
  intro X
  let Z := centralPhysicalVacuumSectorOuterMatrixInputCauchy
    hw0 hw1 half X
  let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
  let floor : CReal := CReal.ofQ' certificate.floor
  let ceiling : CReal := CReal.ofQ'
    (centralPhysicalFiniteVacuumSectorPathCeiling
      w (Q'.le_of_lt hw0) base half)
  let leftSeq : Nat → CReal := fun n => CReal.ofQ'
    (coordinate base half left (Z.seq n))
  let rightSeq : Nat → CReal := fun n => CReal.ofQ'
    (coordinate base half right (Z.seq n))
  let deltaSeq : Nat → CReal := fun n =>
    CReal.add (leftSeq n) (CReal.neg (rightSeq n))
  let endpointSeq : Nat → CReal := fun n =>
    CReal.mul floor (CReal.mul (deltaSeq n) (deltaSeq n))
  let diagonalSeq := centralPhysicalVacuumSectorCylinderOuterPulledDiagonalSeq Z
  let matrixSeq := centralPhysicalVacuumSectorCylinderOuterPulledMatrixSeq X
  let deficitSeq : Nat → CReal := fun n =>
    CReal.add (CReal.add (diagonalSeq n) (diagonalSeq n))
      (CReal.neg (CReal.add (matrixSeq n) (matrixSeq n)))
  let rightSeqForm : Nat → CReal := fun n =>
    CReal.mul ceiling (deficitSeq n)
  let leftLimitZ := coordinateLimit hw0 hw1 base half left hleft Z
  let rightLimitZ := coordinateLimit hw0 hw1 base half right hright Z
  let deltaLimitZ := CReal.add leftLimitZ (CReal.neg rightLimitZ)
  let endpointLimitZ := CReal.mul floor
    (CReal.mul deltaLimitZ deltaLimitZ)
  let diagonalLimit := physicalCauchyPairingLimit hw0 hw1 half
    (centralPhysicalVacuumSectorCylinderCauchyToGlobal Z)
    (centralPhysicalVacuumSectorCylinderCauchyToGlobal Z)
  let matrixLimit := centralPhysicalVacuumSectorOuterMatrixPairingLimit
    hw0 hw1 half X
  let deficitLimit := CReal.add (CReal.add diagonalLimit diagonalLimit)
    (CReal.neg (CReal.add matrixLimit matrixLimit))
  let rightLimit := CReal.mul ceiling deficitLimit
  have hleftConverges : CReal.ConvergesTo leftSeq leftLimitZ :=
    coordinate_converges hw0 hw1 base half left hleft Z
  have hrightConverges : CReal.ConvergesTo rightSeq rightLimitZ :=
    coordinate_converges hw0 hw1 base half right hright Z
  have hdeltaConverges : CReal.ConvergesTo deltaSeq deltaLimitZ :=
    convergesTo_add hleftConverges (convergesTo_neg hrightConverges)
  have hsquareConverges : CReal.ConvergesTo
      (fun n => CReal.mul (deltaSeq n) (deltaSeq n))
      (CReal.mul deltaLimitZ deltaLimitZ) :=
    CReal.convergesTo_mul_general hdeltaConverges hdeltaConverges
  have hendpointConverges : CReal.ConvergesTo endpointSeq endpointLimitZ :=
    CReal.convergesTo_mul_general (CReal.convergesTo_const floor)
      hsquareConverges
  have hdiagonalConverges : CReal.ConvergesTo diagonalSeq diagonalLimit :=
    centralPhysicalVacuumSectorCylinder_outerPulledDiagonal_converges
      hw0 hw1 half Z
  have hmatrixConverges : CReal.ConvergesTo matrixSeq matrixLimit :=
    centralPhysicalVacuumSectorCylinder_outerPulledMatrix_converges
      hw0 hw1 half X
  have hdeficitConverges : CReal.ConvergesTo deficitSeq deficitLimit :=
    convergesTo_add
      (convergesTo_add hdiagonalConverges hdiagonalConverges)
      (convergesTo_neg
        (convergesTo_add hmatrixConverges hmatrixConverges))
  have hrightConverges : CReal.ConvergesTo rightSeqForm rightLimit :=
    CReal.convergesTo_mul_general (CReal.convergesTo_const ceiling)
      hdeficitConverges
  have htermwise : ∀ n, CReal.leEv (endpointSeq n) (rightSeqForm n) := by
    intro n
    have h := fixedBaseFloor_mul_endpoint_sq_leEv_pulledDirichletLimit
      hw0 hw1 base half (Z.seq n) left right hleft hright
    change CReal.leEv _ (rightSeqForm n) at h
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv
        (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))) h
  have hlimit : CReal.leEv endpointLimitZ rightLimit :=
    CReal.leEv_of_convergesTo_le hendpointConverges hrightConverges htermwise
  have hclose := centralPhysicalVacuumSectorOuterMatrixInputClose
    hw0 hw1 half X
  have hleftCoordinate := coordinateLimit_equiv_of_close
    hw0 hw1 base half left hleft hclose
  have hrightCoordinate := coordinateLimit_equiv_of_close
    hw0 hw1 base half right hright hclose
  have hclass := centralPhysicalVacuumSectorOuterMatrixInput_class_eq
    hw0 hw1 half X
  have hdiagonalClass :
      centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          (Quotient.mk D.completionSetoid X)
          (Quotient.mk D.completionSetoid X) =
        Quotient.mk CReal.crealSetoid diagonalLimit := by
    rw [hclass]
    exact centralPhysicalVacuumSectorCylinder_completedInner_mk_eq_outerRawDiagonalLimit
      hw0 hw1 half Z
  have hmatrixClass :
      centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          (centralPhysicalVacuumSectorCylinderCompletedTransfer hw0 hw1 half
            (Quotient.mk D.completionSetoid X))
          (Quotient.mk D.completionSetoid X) =
        Quotient.mk CReal.crealSetoid matrixLimit :=
    centralPhysicalVacuumSectorCylinder_completedTransferForm_mk_eq_outerRawMatrixLimit
      hw0 hw1 half X
  unfold centralPhysicalVacuumSectorCompletedDirichlet
  rw [hdiagonalClass, hmatrixClass]
  change CReal.leEv
    (CReal.mul floor
      (CReal.mul
        (CReal.add (coordinateLimit hw0 hw1 base half left hleft X)
          (CReal.neg (coordinateLimit hw0 hw1 base half right hright X)))
        (CReal.add (coordinateLimit hw0 hw1 base half left hleft X)
          (CReal.neg (coordinateLimit hw0 hw1 base half right hright X)))))
    rightLimit
  exact CReal.leEv_trans
    (CReal.leEv_of_equiv (by
      exact creal_mul_congr (CReal.Equiv.refl floor)
        (creal_mul_congr
          (creal_add_congr hleftCoordinate (CReal.neg_congr hrightCoordinate))
          (creal_add_congr hleftCoordinate (CReal.neg_congr hrightCoordinate)))))
    hlimit

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedEndpointEnergy

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedEndpointEnergy.centralPhysicalVacuumSectorCompletedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedEndpointEnergy.fixedBaseFloor_mul_completedEndpointSq_le_completedDirichlet
