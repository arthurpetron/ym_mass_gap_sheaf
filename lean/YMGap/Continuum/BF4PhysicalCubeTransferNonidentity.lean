/-
# The actual completed physical cube transfer is not the identity

The root and single-face twice-spin-two probe have zero reflected pairing.
After applying the SAME completed conditional transfer to the root, their
pairing has the positive two-edge floor already proved through both original
limits. Thus the root cylinder moves, and the completed transfer is not id.

This is not uniqueness of the stationary sector vacuum, a strict norm bound
on its complement, geometric Euclidean time, or a continuum mass gap.
-/

import YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing

namespace YMGap.Continuum.BF4PhysicalCubeTransferNonidentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeKernelSaturation
open YMGap.Continuum.BF4PhysicalCubeObservableRealization
open YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeCompletedTransfer
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeSeparatedChannel
open YMGap.Continuum.BF4PhysicalCubeThreeStatePath
open YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.RationalKernelSpan
open YMGap.Continuum.ScaledGNSCompletion
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "G" => centralPhysicalCutoffLinearSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "S" => centralPhysicalVacuumSectorCylinderSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "P" => centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "M" => centralPhysicalCutoffCompletedInner (w := anchorCoupling) (by decide) (by decide) 0
local notation "J" => cubeToCompleted (w := anchorCoupling) (by decide) (by decide)
local notation "j" => cubeReflectedEmbed
local notation "B" => cubeReflectedInner

def probeVector : CubeSpan := basis probeState

theorem probe_root_kernel_zero : kernel anchorCoupling probeState rootState ≈ 0 :=
  probe_root_raw_zero anchorCoupling (cubeKernelSaturationCutoff probeState.val rootState.val) (by decide)

theorem root_probe_pairing_zero : B (j rootVector) (j probeVector) = CReal.RCzero := by
  rw [cubeReflectedInner_symm]
  change scaledCompletedInner D anchorNormalization ((scaledSeminorm D anchorNormalization).embedRep probeVector)
    ((scaledSeminorm D anchorNormalization).embedRep rootVector) = CReal.RCzero
  rw [scaledCompletedInner_embed]
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  have hform : form (kernel anchorCoupling) probeVector rootVector ≈ 0 :=
    Q'.eqv_trans _ _ _ (form_basis _ _ _) probe_root_kernel_zero
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hform) (Q'.zero_mul_eqv _)

/-- The single basis term is the literal unit cylinder, not a new observable. -/
theorem global_basis (state : CubeSectorState) :
    J (basis state) = (G).embedRep (.atom (cylinder state.val)) := by
  apply (G).embedRep_eq_of_null
  apply physicalLinearDistSq_equiv_czero_of_equivalent
  intro target
  change 1 * (cylinder state.val).value target + 0 ≈ (cylinder state.val).value target
  exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _)) (Q'.one_mul_eqv _)

/-- One reflected transfer insertion is exactly the original marginal
pairing of the two completed conditional images. -/
theorem transferred_root_probe_pairing :
    B (cubeTransfer (j rootVector)) (j probeVector) =
      M (P ((G).embedRep (.atom (cylinder zeroEdgeLabelling))))
        (P ((G).embedRep (.atom (cylinder probeState.val)))) := by
  have h := cubeTransferPower_sector_moments 1
    ((S).embedRep (spanPresentation rootVector)) ((S).embedRep (spanPresentation probeVector))
  rw [spanPresentation_reflected, spanPresentation_reflected,
    spanPresentation_global, spanPresentation_global] at h
  change B (j rootVector) (cubeTransfer (j probeVector)) = M (J rootVector) (P (P (J probeVector))) at h
  change B (j rootVector) (cubeTransfer (j probeVector)) = M (J (basis rootState)) (P (P (J (basis probeState)))) at h
  rw [global_basis, global_basis] at h
  exact Eq.trans (cubeTransfer_selfAdjoint (j rootVector) (j probeVector))
    (Eq.trans h (concrete_selfAdjoint (w := anchorCoupling) (by decide) (by decide) 0 _ _).symm)

theorem transferred_root_probe_floor :
    CReal.RCle (Quotient.mk CReal.crealSetoid (CReal.ofQ' twoStepFloor))
      (B (cubeTransfer (j rootVector)) (j probeVector)) := by
  rw [transferred_root_probe_pairing]
  exact completed_images_pairing_floor

private theorem positive_constant_not_le_zero (q : Q') (hq : (0 : Q') < q) :
    ¬ CReal.leEv (CReal.ofQ' q) CReal.czero := by
  intro h
  obtain ⟨N, hN⟩ := h (HalfPow.half * q) (ExpNeg.half_mul_pos q hq)
  have hbad := hN N (Nat.le_refl N)
  change q ≤ 0 + HalfPow.half * q at hbad
  rw [Q'.zero_add'] at hbad
  have hprod : q * 1 ≤ q * HalfPow.half := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_one_eqv _))
    (Q'.le_trans' _ _ _ hbad (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  exact (by decide : ¬ (1 : Q') ≤ HalfPow.half) (Q'.le_of_mul_le_mul_left hprod hq)

/-- A concrete moved vector on the ENTIRE actual reflected completion. -/
theorem root_is_moved : cubeTransfer (j rootVector) ≠ j rootVector := by
  intro hfix
  have h := transferred_root_probe_floor
  rw [hfix, root_probe_pairing_zero] at h
  exact positive_constant_not_le_zero twoStepFloor twoStepFloor_pos h

theorem cubeTransfer_ne_identity : cubeTransfer ≠ id := by
  intro h
  exact root_is_moved (congrFun h (j rootVector))

end YMGap.Continuum.BF4PhysicalCubeTransferNonidentity

#print axioms YMGap.Continuum.BF4PhysicalCubeTransferNonidentity.probeVector
#print axioms YMGap.Continuum.BF4PhysicalCubeTransferNonidentity.probe_root_kernel_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeTransferNonidentity.root_probe_pairing_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeTransferNonidentity.global_basis
#print axioms YMGap.Continuum.BF4PhysicalCubeTransferNonidentity.transferred_root_probe_pairing
#print axioms YMGap.Continuum.BF4PhysicalCubeTransferNonidentity.transferred_root_probe_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeTransferNonidentity.root_is_moved
#print axioms YMGap.Continuum.BF4PhysicalCubeTransferNonidentity.cubeTransfer_ne_identity
