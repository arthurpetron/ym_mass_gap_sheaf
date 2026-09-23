/-
# Persistent endpoint energy at the cutoff-removed limit

The finite persistent-path estimate passes to the constructive-real limit for
every vacuum-sector cylinder presentation.  The positive floor is the
constructed fixed-base floor; no additional analytic datum is assumed.

The right side is the explicit twice diagonal-minus-transfer expression in
the presentation's pulled cutoff limits.  Existing dense identification
theorems identify those two limits with the completed inner and transfer
forms.  This file makes no uniform-gap or fixed-vector-uniqueness claim.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergy
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm
import YMGap.Continuum.RCCauchySchwarz
import YMGap.Constructive.TrigAddCReal

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergyLimit

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.TrigAddCReal
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderDenseTransferForm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_congr_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ (a' * b) _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem twiceDeficit_converges (diagonal matrix : CReal) :
    CReal.ConvergesTo
      (fun n => CReal.ofQ'
        ((diagonal.approx n + diagonal.approx n) +
          -(matrix.approx n + matrix.approx n)))
      (CReal.add (CReal.add diagonal diagonal)
        (CReal.neg (CReal.add matrix matrix))) := by
  apply convergesTo_congr_seq
    (s := fun n => CReal.add
      (CReal.add (CReal.ofQ' (diagonal.approx n))
        (CReal.ofQ' (diagonal.approx n)))
      (CReal.neg (CReal.add (CReal.ofQ' (matrix.approx n))
        (CReal.ofQ' (matrix.approx n)))))
  · intro n
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  · exact convergesTo_add
      (convergesTo_add (CReal.convergesTo_self diagonal)
        (CReal.convergesTo_self diagonal))
      (convergesTo_neg (convergesTo_add (CReal.convergesTo_self matrix)
        (CReal.convergesTo_self matrix)))

/-- The explicit constructive-real twice-deficit of a sector presentation. -/
def centralPhysicalVacuumSectorCylinderPulledDirichletLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) : CReal :=
  let diagonal :=
    centralPhysicalFinitePulledVacuumSectorDiagonalQuadraticCutoffLimit
      hw0 hw1 presentation.base half presentation.coefficient
  let matrix :=
    centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
      hw0 hw1 presentation.base half presentation.coefficient
  CReal.add (CReal.add diagonal diagonal)
    (CReal.neg (CReal.add matrix matrix))

private theorem vacuumSectorDiagonal_coefficient_congr
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {left right : Nat → Q'}
    (hagrees : ∀ index, index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      left index ≈ right index) :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half left ≈
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half right := by
  unfold centralPhysicalFiniteVacuumSectorDiagonalQuadratic
  apply listQSum_congr_on
  intro index hindex
  exact Q'.mul_eqv_congr_right _ _ _
    (mul_eqv_congr_both_local
      (hagrees index hindex) (hagrees index hindex))

private theorem vacuumSectorMatrix_coefficient_congr
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {left right : Nat → Q'}
    (hagrees : ∀ index, index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      left index ≈ right index) :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half left ≈
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half right := by
  unfold centralPhysicalFiniteVacuumSectorMatrixQuadratic
    finiteJointQuadratic
  apply listQSum_congr_on
  intro first hfirst
  apply listQSum_congr_on
  intro second hsecond
  exact Q'.mul_eqv_congr_right _ _ _
    (mul_eqv_congr_both_local
      (hagrees first hfirst) (hagrees second hsecond))

private theorem fullCylinderDirichlet_eqv_pulledDeficit
    {w : Q'} {hw : (0 : Q') ≤ w} {half later : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (hlater : presentation.base ≤ later) :
    finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw later half)
        (centralPhysicalFiniteCoefficient w hw later half
          presentation.toLinearObservable.value)
        (centralPhysicalFiniteKernel w hw later half) ≈
      let diagonal :=
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw presentation.base later half presentation.coefficient
      let matrix :=
        centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w hw presentation.base later half presentation.coefficient
      (diagonal + diagonal) + -(matrix + matrix) := by
  let actual := centralPhysicalFiniteCoefficient w hw later half
    presentation.toLinearObservable.value
  let extension := centralPhysicalFiniteVacuumSectorCoefficientExtension
    w hw presentation.base later half presentation.coefficient
  have hagrees : ∀ index,
      index ∈ centralPhysicalFiniteVacuumSectorIndices w hw later half →
      actual index ≈ extension index := by
    intro index hindex
    exact centralPhysicalFiniteCoefficient_linearObservable_eqv_extension
      hlater presentation.coefficient
      (centralPhysicalFiniteVacuumSectorIndex_lt
        w hw later half hindex)
  have hdiagonal := vacuumSectorDiagonal_coefficient_congr
    (w := w) (hw := hw) (cutoff := later) (half := half) hagrees
  have hmatrix := vacuumSectorMatrix_coefficient_congr
    (w := w) (hw := hw) (cutoff := later) (half := half) hagrees
  have henergy :=
    centralPhysicalFiniteVacuumSectorDirichlet_eqv_twice_deficit
      w hw later half actual
  have hextension :
      (centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half actual +
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half actual) +
        -(centralPhysicalFiniteVacuumSectorMatrixQuadratic
            w hw later half actual +
          centralPhysicalFiniteVacuumSectorMatrixQuadratic
            w hw later half actual) ≈
      (centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half extension +
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half extension) +
        -(centralPhysicalFiniteVacuumSectorMatrixQuadratic
            w hw later half extension +
          centralPhysicalFiniteVacuumSectorMatrixQuadratic
            w hw later half extension) :=
    Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hdiagonal hdiagonal)
      (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hmatrix hmatrix))
  exact Q'.eqv_trans _ _ _ henergy
    (Q'.eqv_trans _ _ _ hextension
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (centralPhysicalFiniteVacuumSectorCoefficientExtensionDiagonal_eqv_pulled
            hlater presentation.coefficient)
          (centralPhysicalFiniteVacuumSectorCoefficientExtensionDiagonal_eqv_pulled
            hlater presentation.coefficient))
        (Q'.neg_eqv_congr _ _
          (Q'.add_eqv_congr'
            (centralPhysicalFiniteVacuumSectorCoefficientExtensionMatrix_eqv_pulled
              hlater presentation.coefficient)
            (centralPhysicalFiniteVacuumSectorCoefficientExtensionMatrix_eqv_pulled
              hlater presentation.coefficient)))))

/-- The constructed persistent edge floor controls every fixed-base endpoint
difference by the explicit completed twice-deficit of an arbitrary cylinder. -/
theorem fixedBaseFloor_mul_endpoint_sq_leEv_pulledDirichletLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half)
    (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half) :
    let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
    CReal.leEv
      (CReal.ofQ' (certificate.floor *
        ((presentation.toLinearObservable.value
              (centralPhysicalFiniteStateAt
                w (Q'.le_of_lt hw0) base half left) +
            -presentation.toLinearObservable.value
              (centralPhysicalFiniteStateAt
                w (Q'.le_of_lt hw0) base half right)) *
          (presentation.toLinearObservable.value
              (centralPhysicalFiniteStateAt
                w (Q'.le_of_lt hw0) base half left) +
            -presentation.toLinearObservable.value
              (centralPhysicalFiniteStateAt
                w (Q'.le_of_lt hw0) base half right)))))
      (CReal.mul
        (CReal.ofQ' (centralPhysicalFiniteVacuumSectorPathCeiling
          w (Q'.le_of_lt hw0) base half))
        (centralPhysicalVacuumSectorCylinderPulledDirichletLimit
          hw0 hw1 half presentation)) := by
  let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
  let endpoint : Q' := certificate.floor *
    ((presentation.toLinearObservable.value
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw0) base half left) +
        -presentation.toLinearObservable.value
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw0) base half right)) *
      (presentation.toLinearObservable.value
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw0) base half left) +
        -presentation.toLinearObservable.value
          (centralPhysicalFiniteStateAt
            w (Q'.le_of_lt hw0) base half right)))
  let ceiling := centralPhysicalFiniteVacuumSectorPathCeiling
    w (Q'.le_of_lt hw0) base half
  let diagonal :=
    centralPhysicalFinitePulledVacuumSectorDiagonalQuadraticCutoffLimit
      hw0 hw1 presentation.base half presentation.coefficient
  let matrix :=
    centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
      hw0 hw1 presentation.base half presentation.coefficient
  let deficit : Nat → Q' := fun later =>
    (diagonal.approx later + diagonal.approx later) +
      -(matrix.approx later + matrix.approx later)
  apply CReal.leEv_of_ofQ'_limit_le
    (CReal.convergesTo_const (CReal.ofQ' endpoint))
  · apply convergesTo_congr_seq
      (s := fun later => CReal.mul (CReal.ofQ' ceiling)
        (CReal.ofQ' (deficit later)))
      (t := fun later => CReal.ofQ' (ceiling * deficit later))
    · intro later
      exact CReal.Equiv.symm
        (YMGap.Constructive.CRealAlg.ofQ'_mul ceiling (deficit later))
    · exact CReal.convergesTo_constMul ceiling
        (twiceDeficit_converges diagonal matrix)
  · intro epsilon hepsilon
    refine ⟨max certificate.start presentation.base, fun later hlater => ?_⟩
    have hstart : certificate.start ≤ later :=
      Nat.le_trans (Nat.le_max_left _ _) hlater
    have hpresentation : presentation.base ≤ later :=
      Nat.le_trans (Nat.le_max_right _ _) hlater
    have hfinite := floor_mul_endpoint_sq_le_fullCylinderDirichlet
      certificate later hstart presentation left right hleft hright
    have hidentification := fullCylinderDirichlet_eqv_pulledDeficit
      presentation hpresentation
    have hscaled := Q'.mul_eqv_congr_left ceiling _ _ hidentification
    exact Q'.le_trans' _ _ _ hfinite
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hscaled)
        (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt hepsilon)))

/-- The two limits occurring in the endpoint estimate are exactly the
existing completed dense inner and transfer forms. -/
theorem pulledDirichletLimit_completed_identifications
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    centralPhysicalCutoffCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation))
        (centralPhysicalVacuumSectorCylinderCompletionToGlobal
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation)) =
      Quotient.mk CReal.crealSetoid
        (centralPhysicalFinitePulledVacuumSectorDiagonalQuadraticCutoffLimit
          hw0 hw1 presentation.base half presentation.coefficient) ∧
    centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
        (centralPhysicalVacuumSectorCylinderCompletedTransfer hw0 hw1 half
          ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
            hw0 hw1 half).embedRep presentation))
        ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
          hw0 hw1 half).embedRep presentation) =
      Quotient.mk CReal.crealSetoid
        (centralPhysicalFinitePulledVacuumSectorMatrixQuadraticCutoffLimit
          hw0 hw1 presentation.base half presentation.coefficient) := by
  exact
    ⟨centralPhysicalVacuumSectorCylinder_completedInner_embedRep_eq_pulled
        hw0 hw1 half presentation,
      centralPhysicalVacuumSectorCylinder_completedTransferForm_embedRep_eq_pulled
        hw0 hw1 half presentation⟩

/-- The explicit pulled twice-deficit is the actual dense completed
diagonal-minus-transfer Dirichlet form in the real quotient. -/
theorem pulledDirichletLimit_eq_completedDirichlet
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half) :
    Quotient.mk CReal.crealSetoid
        (centralPhysicalVacuumSectorCylinderPulledDirichletLimit
          hw0 hw1 half presentation) =
      CReal.RCadd
        (CReal.RCadd
          (centralPhysicalCutoffCompletedInner hw0 hw1 half
            (centralPhysicalVacuumSectorCylinderCompletionToGlobal
              ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                hw0 hw1 half).embedRep presentation))
            (centralPhysicalVacuumSectorCylinderCompletionToGlobal
              ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                hw0 hw1 half).embedRep presentation)))
          (centralPhysicalCutoffCompletedInner hw0 hw1 half
            (centralPhysicalVacuumSectorCylinderCompletionToGlobal
              ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                hw0 hw1 half).embedRep presentation))
            (centralPhysicalVacuumSectorCylinderCompletionToGlobal
              ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                hw0 hw1 half).embedRep presentation))))
        (CReal.RCneg
          (CReal.RCadd
            (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
              (centralPhysicalVacuumSectorCylinderCompletedTransfer
                hw0 hw1 half
                ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                  hw0 hw1 half).embedRep presentation))
              ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                hw0 hw1 half).embedRep presentation))
            (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
              (centralPhysicalVacuumSectorCylinderCompletedTransfer
                hw0 hw1 half
                ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                  hw0 hw1 half).embedRep presentation))
              ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                hw0 hw1 half).embedRep presentation)))) := by
  rw [centralPhysicalVacuumSectorCylinder_completedInner_embedRep_eq_pulled
      hw0 hw1 half presentation]
  rw [centralPhysicalVacuumSectorCylinder_completedTransferForm_embedRep_eq_pulled
      hw0 hw1 half presentation]
  rfl

/-- Quotient-level form of the persistent endpoint estimate, with the right
side written entirely in terms of the actual dense completed inner and
transfer forms. -/
theorem fixedBaseFloor_mul_endpoint_sq_RCle_completedDirichlet
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (base half : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w (Q'.le_of_lt hw0) half)
    (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw0) base half) :
    let certificate := fixedBasePulledPositiveEdgeFloor hw0 hw1 base half
    CReal.RCle
      (Quotient.mk CReal.crealSetoid
        (CReal.ofQ' (certificate.floor *
          ((presentation.toLinearObservable.value
                (centralPhysicalFiniteStateAt
                  w (Q'.le_of_lt hw0) base half left) +
              -presentation.toLinearObservable.value
                (centralPhysicalFiniteStateAt
                  w (Q'.le_of_lt hw0) base half right)) *
            (presentation.toLinearObservable.value
                (centralPhysicalFiniteStateAt
                  w (Q'.le_of_lt hw0) base half left) +
              -presentation.toLinearObservable.value
                (centralPhysicalFiniteStateAt
                  w (Q'.le_of_lt hw0) base half right))))))
      (CReal.RCmul
        (Quotient.mk CReal.crealSetoid
          (CReal.ofQ' (centralPhysicalFiniteVacuumSectorPathCeiling
            w (Q'.le_of_lt hw0) base half)))
        (CReal.RCadd
          (CReal.RCadd
            (centralPhysicalCutoffCompletedInner hw0 hw1 half
              (centralPhysicalVacuumSectorCylinderCompletionToGlobal
                ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                  hw0 hw1 half).embedRep presentation))
              (centralPhysicalVacuumSectorCylinderCompletionToGlobal
                ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                  hw0 hw1 half).embedRep presentation)))
            (centralPhysicalCutoffCompletedInner hw0 hw1 half
              (centralPhysicalVacuumSectorCylinderCompletionToGlobal
                ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                  hw0 hw1 half).embedRep presentation))
              (centralPhysicalVacuumSectorCylinderCompletionToGlobal
                ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                  hw0 hw1 half).embedRep presentation))))
          (CReal.RCneg
            (CReal.RCadd
              (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
                (centralPhysicalVacuumSectorCylinderCompletedTransfer
                  hw0 hw1 half
                  ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                    hw0 hw1 half).embedRep presentation))
                ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                  hw0 hw1 half).embedRep presentation))
              (centralPhysicalVacuumSectorCylinderCompletedInner hw0 hw1 half
                (centralPhysicalVacuumSectorCylinderCompletedTransfer
                  hw0 hw1 half
                  ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                    hw0 hw1 half).embedRep presentation))
                ((centralPhysicalVacuumSectorCylinderSquaredSeminorm
                  hw0 hw1 half).embedRep presentation)))))) := by
  rw [← pulledDirichletLimit_eq_completedDirichlet
    hw0 hw1 half presentation]
  rw [CReal.RCmul_mk, CReal.RCle_mk]
  exact fixedBaseFloor_mul_endpoint_sq_leEv_pulledDirichletLimit
    hw0 hw1 base half presentation left right hleft hright

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergyLimit

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergyLimit.fixedBaseFloor_mul_endpoint_sq_leEv_pulledDirichletLimit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergyLimit.pulledDirichletLimit_completed_identifications
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergyLimit.pulledDirichletLimit_eq_completedDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergyLimit.fixedBaseFloor_mul_endpoint_sq_RCle_completedDirichlet
