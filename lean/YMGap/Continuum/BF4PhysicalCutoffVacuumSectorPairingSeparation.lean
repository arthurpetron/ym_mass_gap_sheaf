/-
# Dense-test separation on the completed BF4 vacuum-sector cylinder carrier

The physical pairing data pull back along cylinder realization to the sector
seminorm.  Its generic choice-free completion is the already defined sector
pairing, and generic positive-definiteness therefore separates sector vectors
using sector-cylinder tests alone.

The zero object is the genuine zero-coefficient sector presentation.  No
global-vacuum membership or coordinate formula is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffPairingCompletionAdapter
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPairingSeparation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffPairingCompletionAdapter
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.CRealSeminormPairingCompletion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] centralPhysicalFiniteCarrierSize
  centralPhysicalFiniteIndexCarrier centralPhysicalFiniteVacuumSectorIndices
  centralPositiveHalfStates

private theorem zeroCoefficient_equivalent_zero
    {w : Q'} {hw : (0 : Q') ≤ w} (base half : Nat) :
    Equivalent
      (centralPhysicalFiniteVacuumSectorLinearObservable
        w hw base half (fun _ => 0))
      zero := by
  intro state
  change
    (centralPhysicalFiniteVacuumSectorLinearObservable
      w hw base half (fun _ => 0)).value state ≈ 0
  refine Q'.eqv_trans _
    (listQSum (fun _index => (0 : Q'))
      (centralPhysicalFiniteVacuumSectorIndices w hw base half)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
        (fun index =>
          if labellingsAgreeOnB (centralLowerFaceIds half) state
              (centralPhysicalFiniteStateAt w hw base half index)
          then (0 : Q') else 0)
        (centralPhysicalFiniteVacuumSectorIndices w hw base half)) _ ?_ ?_
    · exact centralPhysicalStateCylinderLinearCombination_value
        half (centralPhysicalFiniteStateAt w hw base half)
        (fun _ => 0) state
        (centralPhysicalFiniteVacuumSectorIndices w hw base half)
    · apply listQSum_congr_on
      intro index _hindex
      by_cases hagree : labellingsAgreeOnB
          (centralLowerFaceIds half) state
          (centralPhysicalFiniteStateAt w hw base half index) = true
      · simp only [hagree, if_true]
        exact Q'.eqv_refl 0
      · have hfalse : labellingsAgreeOnB
            (centralLowerFaceIds half) state
            (centralPhysicalFiniteStateAt w hw base half index) = false := by
          cases hvalue : labellingsAgreeOnB
              (centralLowerFaceIds half) state
              (centralPhysicalFiniteStateAt w hw base half index)
          · rfl
          · exact False.elim (hagree hvalue)
        simp only [hfalse, Bool.false_eq_true, if_false]
        exact Q'.eqv_refl 0
  · exact listQSum_zero
      (centralPhysicalFiniteVacuumSectorIndices w hw base half)

/-- A zero-coefficient finite sector realization is the algebraic zero
observable. -/
theorem centralPhysicalVacuumSectorZeroPresentation_equivalent_zero
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} :
    Equivalent
      (centralPhysicalVacuumSectorZeroPresentation
        (w := w) (hw := hw) (half := half)).toLinearObservable
      zero :=
  zeroCoefficient_equivalent_zero 0 half

#print axioms centralPhysicalVacuumSectorZeroPresentation_equivalent_zero

/-- The checked physical pairing data restricted to sector presentations. -/
def sectorPairingData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) :
    PairingData
      (centralPhysicalVacuumSectorCylinderSquaredSeminorm hw0 hw1 half) where
  pairing left right :=
    innerLimit hw0 hw1 half
      left.toLinearObservable right.toLinearObservable
  pairingCauchy left right :=
    (physicalPairingData hw0 hw1 half).pairingCauchy
      left.toLinearObservable right.toLinearObservable
  diagonal_anchor_bound left anchor :=
    (physicalPairingData hw0 hw1 half).diagonal_anchor_bound
      left.toLinearObservable anchor.toLinearObservable
  pairing_close left left' right right' :=
    (physicalPairingData hw0 hw1 half).pairing_close
      left.toLinearObservable left'.toLinearObservable
      right.toLinearObservable right'.toLinearObservable

/-- The generic sector representative pairing is the existing physical
pairing limit of the termwise realized global representatives. -/
theorem sectorRepresentativeInner_equiv_physicalCauchyPairingLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (X Y : (centralPhysicalVacuumSectorCylinderSquaredSeminorm
      hw0 hw1 half).Cauchy) :
    Equiv
      (representativeInner (sectorPairingData hw0 hw1 half) X Y)
      (physicalCauchyPairingLimit hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
        (centralPhysicalVacuumSectorCylinderCauchyToGlobal Y)) := by
  apply representativeInner_unique (sectorPairingData hw0 hw1 half) X Y
  exact physicalCauchyPairingSeq_converges hw0 hw1 half
    (centralPhysicalVacuumSectorCylinderCauchyToGlobal X)
    (centralPhysicalVacuumSectorCylinderCauchyToGlobal Y)

/-- The generic completed pullback is exactly the existing sector completed
inner form defined through the canonical global embedding. -/
theorem sectorCompletedInner_eq_existing
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (left right :
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half) :
    completedInner (sectorPairingData hw0 hw1 half) left right =
      centralPhysicalVacuumSectorCylinderCompletedInner
        hw0 hw1 half left right := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  exact Quotient.sound
    (sectorRepresentativeInner_equiv_physicalCauchyPairingLimit
      hw0 hw1 half X Y)

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

/-- Sector-cylinder dense tests separate the completed sector carrier at its
genuine embedded zero presentation. -/
theorem sectorCompleted_eq_zero_of_dense_pairings_zero
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (vector :
      CentralPhysicalCutoffVacuumSectorCylinderCompletion hw0 hw1 half)
    (hdense : ∀ presentation :
      CentralPhysicalVacuumSectorCylinderPresentation
        w (Q'.le_of_lt hw0) half,
      centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
          vector
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation) = RCzero) :
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
  apply (completedInner_posdef P zeroPresentation hdist hz vector).mp
  revert hdense
  refine Quotient.inductionOn vector ?_
  intro X hdense
  apply Quotient.sound
  apply Equiv_of_limit_of_equal
    (aSeq := fun n => representativeInner P X (D.constant (X.seq n)))
    (bSeq := fun _ => czero)
  · intro n
    exact Quotient.exact
      ((sectorCompletedInner_eq_existing hw0 hw1 half
        (Quotient.mk D.completionSetoid X) (D.embedRep (X.seq n))).trans
          (hdense (X.seq n)))
  · exact representativeInner_right_stage_converges P X X
  · exact convergesTo_const czero

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPairingSeparation

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPairingSeparation.sectorPairingData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPairingSeparation.sectorCompletedInner_eq_existing
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPairingSeparation.sectorCompleted_eq_zero_of_dense_pairings_zero
