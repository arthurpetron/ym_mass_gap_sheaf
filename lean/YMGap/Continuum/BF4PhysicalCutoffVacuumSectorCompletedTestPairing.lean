/-
# Completed BF4 sector vectors paired with dense tests

The actual completed pairing against a fixed sector cylinder is the finite
sum of the completed retained coordinates, the cylinder coefficients, and
the pulled stationary-weight limits.  The proof passes the checked dense
identity through the existing representative-pairing convergence.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseTestPairingLimit
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPairingSeparation
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentCoordinate
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedTestPairing

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseTestPairingLimit
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPairingSeparation
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentCoordinate
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CRealSeminormPairingCompletion
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

attribute [local irreducible] centralPhysicalFiniteCarrierSize
  centralPhysicalFiniteIndexCarrier centralPhysicalFiniteVacuumSectorIndices
  centralPositiveHalfStates

/-- Representative-level finite sum of completed coordinates against a fixed
dense sector test. -/
def representativeDenseTestCoordinateSum
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (test : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) : CReal :=
  finiteCRealSum
    (fun index =>
      if hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw0) test.base half then
        CReal.mul
          (CReal.mul
            (coordinateLimit hw0 hw1 test.base half index hindex X)
            (CReal.ofQ' (test.coefficient index)))
          (centralPhysicalFinitePulledWeightCutoffLimit
            hw0 hw1 test.base half index
            (centralPhysicalFiniteVacuumSectorIndex_lt
              w (Q'.le_of_lt hw0) test.base half hindex))
      else CReal.czero)
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) test.base half)

private theorem finiteCRealSum_converges
    {A : Type} {sequence : A → Nat → CReal} {limit : A → CReal} :
    ∀ items : List A,
      (∀ item, item ∈ items →
        CReal.ConvergesTo (sequence item) (limit item)) →
      CReal.ConvergesTo
        (fun n => finiteCRealSum (fun item => sequence item n) items)
        (finiteCRealSum limit items)
  | [], _ => CReal.convergesTo_const CReal.czero
  | head :: tail, h =>
      CReal.convergesTo_add
        (h head List.mem_cons_self)
        (finiteCRealSum_converges tail
          (fun item hitem => h item (List.mem_cons_of_mem head hitem)))

theorem denseTestCoordinateSum_converges
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (test : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    CReal.ConvergesTo
      (fun n => centralPhysicalVacuumSectorDenseTestCoordinateSum
        hw0 hw1 half (X.seq n).toLinearObservable test)
      (representativeDenseTestCoordinateSum hw0 hw1 half X test) := by
  unfold centralPhysicalVacuumSectorDenseTestCoordinateSum
    representativeDenseTestCoordinateSum
  apply finiteCRealSum_converges
  intro index hindex
  have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w (Q'.le_of_lt hw0) test.base half hindex
  simp only [dif_pos hindex, dif_pos hindexLt]
  apply CReal.convergesTo_mul_general
  · apply CReal.convergesTo_mul_general
    · exact coordinate_converges
        hw0 hw1 test.base half index hindex X
    · exact CReal.convergesTo_const
        (CReal.ofQ' (test.coefficient index))
  · exact CReal.convergesTo_const
      (centralPhysicalFinitePulledWeightCutoffLimit
        hw0 hw1 test.base half index hindexLt)

/-- The existing representative pairing limit is the finite sum of the same
representative's completed retained coordinates against the fixed test. -/
theorem physicalCauchyPairingLimit_equiv_representativeDenseTestCoordinateSum
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (test : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    CReal.Equiv
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).constant test)))
      (representativeDenseTestCoordinateSum hw0 hw1 half X test) := by
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := physicalCauchyPairingSeq hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal
        ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).constant test)))
    (bSeq := fun n => centralPhysicalVacuumSectorDenseTestCoordinateSum
      hw0 hw1 half (X.seq n).toLinearObservable test)
  · intro n
    exact innerLimit_equiv_denseTestCoordinateSum
      hw0 hw1 half (X.seq n).toLinearObservable test
  · exact physicalCauchyPairingSeq_converges hw0 hw1 half _ _
  · exact denseTestCoordinateSum_converges hw0 hw1 half X test

/-- Finite addition in the quotient constructive-real carrier. -/
def finiteRCSum {A : Type} (value : A → CReal.RC) : List A → CReal.RC
  | [] => CReal.RCzero
  | head :: tail => CReal.RCadd (value head) (finiteRCSum value tail)

theorem finiteRCSum_mk {A : Type} (value : A → CReal) :
    ∀ items : List A,
      finiteRCSum
          (fun item => Quotient.mk CReal.crealSetoid (value item)) items =
        Quotient.mk CReal.crealSetoid (finiteCRealSum value items)
  | [] => rfl
  | head :: tail => by
      simp only [finiteRCSum, finiteCRealSum]
      rw [finiteRCSum_mk value tail, CReal.RCadd_mk]

/-- Finite sum in the quotient constructive-real carrier, stated directly in
terms of the quotient-descended completed coordinates. -/
def completedDenseTestCoordinateSum
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (x : CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half)
    (test : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) : CReal.RC :=
  finiteRCSum
    (fun index =>
      if hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
          w (Q'.le_of_lt hw0) test.base half then
        CReal.RCmul
          (CReal.RCmul
            (completedCoordinate
              hw0 hw1 test.base half index hindex x)
            (Quotient.mk CReal.crealSetoid
              (CReal.ofQ' (test.coefficient index))))
          (Quotient.mk CReal.crealSetoid
            (centralPhysicalFinitePulledWeightCutoffLimit
              hw0 hw1 test.base half index
              (centralPhysicalFiniteVacuumSectorIndex_lt
                w (Q'.le_of_lt hw0) test.base half hindex)))
      else CReal.RCzero)
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) test.base half)

theorem completedDenseTestCoordinateSum_mk
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy)
    (test : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    completedDenseTestCoordinateSum hw0 hw1 half
        (Quotient.mk (centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).completionSetoid X) test =
      Quotient.mk CReal.crealSetoid
        (representativeDenseTestCoordinateSum hw0 hw1 half X test) := by
  unfold completedDenseTestCoordinateSum representativeDenseTestCoordinateSum
  rw [← finiteRCSum_mk]
  apply congrArg (fun value => finiteRCSum value
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) test.base half))
  funext index
  by_cases hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) test.base half
  · simp only [dif_pos hindex]
    rfl
  · simp only [dif_neg hindex]
    rfl

/-- Actual completed sector pairing against a dense test, with no selected
representative in the statement. -/
theorem completedInner_embedRep_eq_completedDenseTestCoordinateSum
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (x : CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half)
    (test : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half x
        ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).embedRep test) =
      completedDenseTestCoordinateSum hw0 hw1 half x test := by
  rw [← sectorCompletedInner_eq_existing hw0 hw1 half]
  refine Quotient.inductionOn x ?_
  intro X
  rw [completedDenseTestCoordinateSum_mk]
  apply Quotient.sound
  change CReal.Equiv
    (representativeInner (sectorPairingData hw0 hw1 half) X
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).constant test))
    (representativeDenseTestCoordinateSum hw0 hw1 half X test)
  exact CReal.Equiv.trans
    (sectorRepresentativeInner_equiv_physicalCauchyPairingLimit
      hw0 hw1 half X
      ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).constant test))
    (physicalCauchyPairingLimit_equiv_representativeDenseTestCoordinateSum
      hw0 hw1 half X test)

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedTestPairing

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedTestPairing.representativeDenseTestCoordinateSum
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedTestPairing.denseTestCoordinateSum_converges
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedTestPairing.physicalCauchyPairingLimit_equiv_representativeDenseTestCoordinateSum
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedTestPairing.finiteRCSum
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedTestPairing.finiteRCSum_mk
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedTestPairing.completedDenseTestCoordinateSum
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedTestPairing.completedDenseTestCoordinateSum_mk
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCompletedTestPairing.completedInner_embedRep_eq_completedDenseTestCoordinateSum
