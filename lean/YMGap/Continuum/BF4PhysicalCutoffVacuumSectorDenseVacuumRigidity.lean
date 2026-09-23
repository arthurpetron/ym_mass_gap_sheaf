/-
# Conditional dense-vacuum rigidity on the completed BF4 sector

If a completed sector vector pairs on every dense sector cylinder as one
fixed real multiple of the global-vacuum functional, then global-vacuum
orthogonality forces the vector to be the genuine embedded sector zero.

This is a consumer of an explicit dense proportionality identity.  It does
not prove that identity for transfer-fixed vectors, and hence does not by
itself prove fixed-vector uniqueness.  The global vacuum is used only as a
test vector in the ambient completed pairing; it is not assumed to belong to
the sector completion.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPairingSeparation
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseVacuumRigidity

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffPairingCompletionAdapter
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPairingSeparation
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.CRealSeminormPairingCompletion

attribute [local irreducible]
  BF4PhysicalCutoffFiniteIndexBridge.centralPhysicalFiniteCarrierSize
  BF4PhysicalFiniteVacuumSector.centralPhysicalFiniteIndexCarrier
  BF4PhysicalFiniteVacuumSector.centralPhysicalFiniteVacuumSectorIndices
  BF4SU2FixedMagneticPhysicalMarkov.centralPositiveHalfStates

private theorem sub_zeroPresentation_equivalent_self
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half) :
    Equivalent
      (sub presentation.toLinearObservable
        (centralPhysicalVacuumSectorZeroPresentation
          (w := w) (hw := hw) (half := half)).toLinearObservable)
      presentation.toLinearObservable := by
  let zeroPresentation := centralPhysicalVacuumSectorZeroPresentation
    (w := w) (hw := hw) (half := half)
  have hzero := centralPhysicalVacuumSectorZeroPresentation_equivalent_zero
    (w := w) (hw := hw) (half := half)
  intro state
  refine Q'.eqv_trans _
    (presentation.toLinearObservable.value state +
      -zeroPresentation.toLinearObservable.value state) _
    (sub_value_equiv _ _ state) ?_
  refine Q'.eqv_trans _
    (presentation.toLinearObservable.value state + -(0 : Q')) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (hzero state))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

private theorem sector_eq_zero_of_generic_self_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (vector : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half)
    (hself : completedInner (sectorPairingData hw0 hw1 half)
      vector vector = RCzero) :
    vector =
      (centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).embedRep
        (centralPhysicalVacuumSectorZeroPresentation
          (w := w) (hw := Q'.le_of_lt hw0) (half := half)) := by
  let D := centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half
  let P := sectorPairingData hw0 hw1 half
  let zeroPresentation := centralPhysicalVacuumSectorZeroPresentation
    (w := w) (hw := Q'.le_of_lt hw0) (half := half)
  have hdist : ∀ presentation,
      Equiv (D.distSq presentation zeroPresentation)
        (P.pairing presentation presentation) := by
    intro presentation
    exact innerLimit_congr hw0 hw1 half
      (sub_zeroPresentation_equivalent_self presentation)
      (sub_zeroPresentation_equivalent_self presentation)
  have hz : Equiv (P.pairing zeroPresentation zeroPresentation) czero := by
    exact innerLimit_congr hw0 hw1 half
      centralPhysicalVacuumSectorZeroPresentation_equivalent_zero
      centralPhysicalVacuumSectorZeroPresentation_equivalent_zero
  exact (completedInner_posdef P zeroPresentation hdist hz vector).mp hself

/-- Conditional rigidity consumer.  The dense proportionality identity is
the explicit remaining producer obligation; under it, ambient vacuum
orthogonality forces the completed sector vector to be sector zero. -/
theorem sector_eq_zero_of_orthogonal_and_dense_vacuum_proportional
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (scalar : CReal.RC)
    (vector : CentralPhysicalCutoffVacuumSectorCylinderCompletion
      hw0 hw1 half)
    (horthogonal : CentralPhysicalCutoffCompletedVacuumOrthogonal
      hw0 hw1 half
      (centralPhysicalVacuumSectorCylinderCompletionToGlobal vector))
    (hdense : ∀ presentation :
      CentralPhysicalVacuumSectorCylinderPresentation
        w (Q'.le_of_lt hw0) half,
      centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          vector
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation) =
        CReal.RCmul scalar
          (centralPhysicalCutoffCompletedInner hw0 hw1 half
            (centralPhysicalCutoffCompletedVacuum hw0 hw1 half)
            (embedCentralPhysicalLinearObservable hw0 hw1 half
              presentation.toLinearObservable))) :
    vector =
      (centralPhysicalVacuumSectorCylinderSquaredSeminorm
        hw0 hw1 half).embedRep
        (centralPhysicalVacuumSectorZeroPresentation
          (w := w) (hw := Q'.le_of_lt hw0) (half := half)) := by
  let DS := centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half
  let PS := sectorPairingData hw0 hw1 half
  let DG := centralPhysicalCutoffLinearSquaredSeminorm hw0 hw1 half
  let PG := physicalPairingData hw0 hw1 half
  let vacuumCauchy := DG.constant centralPhysicalLinearVacuum
  apply sector_eq_zero_of_generic_self_zero hw0 hw1 half vector
  revert horthogonal hdense
  refine Quotient.inductionOn scalar ?_
  intro scalarRepresentative
  refine Quotient.inductionOn vector ?_
  intro X horthogonal hdense
  let GX := centralPhysicalVacuumSectorCylinderCauchyToGlobal X
  let sectorSelf := representativeInner PS X X
  let vacuumPair := representativeInner PG vacuumCauchy GX
  have hsectorConverges : ConvergesTo
      (fun n => representativeInner PS X (DS.constant (X.seq n)))
      sectorSelf :=
    representativeInner_right_stage_converges PS X X
  have hvacuumConverges : ConvergesTo
      (fun n => representativeInner PG vacuumCauchy
        (DG.constant (X.seq n).toLinearObservable))
      vacuumPair :=
    representativeInner_right_stage_converges PG vacuumCauchy GX
  have hscaledVacuumConverges : ConvergesTo
      (fun n => mul scalarRepresentative
        (representativeInner PG vacuumCauchy
          (DG.constant (X.seq n).toLinearObservable)))
      (mul scalarRepresentative vacuumPair) :=
    CReal.convergesTo_mul_general
      (convergesTo_const scalarRepresentative) hvacuumConverges
  have hterm : ∀ n, Equiv
      (representativeInner PS X (DS.constant (X.seq n)))
      (mul scalarRepresentative
        (representativeInner PG vacuumCauchy
          (DG.constant (X.seq n).toLinearObservable))) := by
    intro n
    apply Quotient.exact (s := CReal.crealSetoid)
    have hdenseN := hdense (X.seq n)
    rw [← sectorCompletedInner_eq_existing hw0 hw1 half] at hdenseN
    rw [← completedInner_eq_centralPhysicalCutoffCompletedInner
      hw0 hw1 half] at hdenseN
    exact hdenseN
  have hselfScaled : Equiv sectorSelf
      (mul scalarRepresentative vacuumPair) :=
    Equiv_of_limit_of_equal hterm hsectorConverges hscaledVacuumConverges
  have hvacuumZero : Equiv vacuumPair czero := by
    apply Quotient.exact (s := CReal.crealSetoid)
    change completedInner PG
      (Quotient.mk DG.completionSetoid vacuumCauchy)
      (Quotient.mk DG.completionSetoid GX) = RCzero
    rw [completedInner_eq_centralPhysicalCutoffCompletedInner]
    rw [centralPhysicalCutoffCompletedInner_symm]
    exact horthogonal
  apply Quotient.sound
  exact hselfScaled.trans
    ((CRealAlg.cmul_comm scalarRepresentative vacuumPair).trans
      ((CReal.mul_congr_left hvacuumZero).trans
        ((CRealAlg.cmul_comm czero scalarRepresentative).trans
          (Equiv_of_approx_eqv (fun _ => Q'.mul_zero_eqv _)))))

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseVacuumRigidity

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorDenseVacuumRigidity.sector_eq_zero_of_orthogonal_and_dense_vacuum_proportional
