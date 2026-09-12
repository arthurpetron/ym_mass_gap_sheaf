/-
# The three-state path survives the actual completed conditional action

At the fixed fundamental-cube source, both cutoff conditional images have
positive lower bounds from the same normalized physical joint. Its marginal
also has a fixed positive floor. Retain that single term in the positive
marginal pairing, then pass through the existing two constructive limits.
This gives a positive pairing of the ACTUAL completed images of root and
probe, not a replacement operator or a postulated cofinal certificate.

Scope is w=1/400 and extent one. No uniform all-vector gap is asserted.
-/

import YMGap.Continuum.BF4PhysicalCubeThreeStatePath
import YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws

namespace YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeSeparatedChannel
open YMGap.Continuum.BF4PhysicalCubeThreeStatePath
open YMGap.Continuum.BF4PhysicalCubeDifferenceBoundaryKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSingleFaceLeakage
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalCutoffStationarySourceTail
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalDenseStageDiagonalComparison
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FinitePositiveMaximumEntry
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "G" => centralPhysicalCutoffLinearSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "P" => centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "M" => centralPhysicalCutoffCompletedInner (w := anchorCoupling) (by decide) (by decide) 0
local notation "pointwise" => centralPhysicalDenseMarkovCauchyData
  (w := anchorCoupling) (by decide) (by decide) 0

def cylinder (state : EdgeLabelling) : CentralPhysicalUnitObservable :=
  centralPhysicalStateCylinderUnitObservable 0 state

def cutoffImage (state : EdgeLabelling) (K : Nat) : CentralPhysicalUnitObservable :=
  centralPhysicalMarkovCutoffUnitObservable (w := anchorCoupling) (by decide) K 0 (cylinder state)

theorem middle_mem (K : Nat) (hK : 1 ≤ K) :
    centralLowerCubeState ∈ centralPositiveHalfStates anchorCoupling (by decide) K 0 :=
  centralLowerCubeState_mem_centralPositiveHalfStates (w := anchorCoupling) (by decide) hK

theorem probe_mem (K : Nat) (hK : 2 ≤ K) :
    probeState.val ∈ centralPositiveHalfStates anchorCoupling (by decide) K 0 :=
  cubeSupported_mem_positiveHalfStates (by decide) K (by omega) probeState.val
    (fun face _ => Nat.le_trans (cutoffTwoSingleFaceTwoState_le_two face) hK) probe_zero_off_cube

theorem middle_probe_joint_floor (K : Nat) (hK : 2 ≤ K) :
    probeJointFloor ≤ centralNormalizedPhysicalReflectedKernel anchorCoupling (by decide) K 0
      centralLowerCubeState probeState.val :=
  Q'.le_trans' _ _ _ (probe_middle_joint_floor K hK)
    (Q'.ge_of_eqv (centralNormalizedPhysicalReflectedKernel_symm
      (mem_centralPositiveHalfStates_iff.mp (middle_mem K (by omega))).1
      (mem_centralPositiveHalfStates_iff.mp (probe_mem K hK)).1))

theorem middle_row_floor (K : Nat) (hK : 1 ≤ K) :
    rootJointFloor ≤ centralPhysicalRowMarginal anchorCoupling (by decide) K 0 centralLowerCubeState := by
  exact Q'.le_trans' _ _ _ (middle_root_joint_floor K hK)
    (le_listQSum_of_mem_nonnegative _ (centralHalfStates K 0) zeroEdgeLabelling
      (zeroEdgeLabelling_mem_centralHalfStates K 0)
      (fun target _ => centralNormalizedPhysicalReflectedKernel_nonnegative (by decide) K 0 _ target))

/-- Conditioning divides by a marginal at most one, so it retains this
joint floor. Only the displayed retained source/target are used. -/
theorem cylinder_image_floor (K : Nat) (source target : EdgeLabelling) (r : Q')
    (hs : source ∈ centralPositiveHalfStates anchorCoupling (by decide) K 0)
    (ht : target ∈ centralPositiveHalfStates anchorCoupling (by decide) K 0)
    (hr : r ≤ centralNormalizedPhysicalReflectedKernel anchorCoupling (by decide) K 0 source target) :
    r ≤ (cutoffImage target K).value source := by
  have hcond : centralNormalizedPhysicalReflectedKernel anchorCoupling (by decide) K 0 source target ≤
      centralPhysicalConditionalKernel anchorCoupling (by decide) K 0 source target := by
    rw [centralPhysicalConditionalKernel_eq_divPos (mem_centralPositiveHalfStates_iff.mp hs).2]
    apply Q'.le_divPos_of_mul_le
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (centralPhysicalRowMarginal_le_one_on_carrier hs)
        (centralNormalizedPhysicalReflectedKernel_nonnegative (by decide) K 0 source target))
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hself : (cylinder target).value target = (1 : Q') := by
    change (if labellingsAgreeOnB (centralLowerFaceIds 0) target target then (1 : Q') else 0) = 1
    rw [labellingsAgreeOnB_self]
    rfl
  have hterm := le_listQSum_of_mem_nonnegative
    (fun state => centralPhysicalConditionalKernel anchorCoupling (by decide) K 0 source state *
      (cylinder target).value state) (centralPositiveHalfStates anchorCoupling (by decide) K 0) target ht
    (fun state _ => Q'.mul_nonneg _ _
      (centralPhysicalConditionalKernel_nonnegative (by decide) K 0 source state)
      ((cylinder target).nonnegative state))
  dsimp only at hterm
  rw [hself] at hterm
  exact Q'.le_trans' _ _ _ hr (Q'.le_trans' _ _ _ hcond (Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_one_eqv _)) (Q'.le_trans' _ _ _ hterm
      (Q'.ge_of_eqv (centralPhysicalMarkovCutoffUnitObservable_value_of_mem
        (by decide) K 0 (cylinder target) source hs)))))

def twoStepFloor : Q' := rootJointFloor * (rootJointFloor * probeJointFloor)

theorem twoStepFloor_pos : (0 : Q') < twoStepFloor :=
  Q'.mul_pos rootJointFloor_pos (Q'.mul_pos rootJointFloor_pos probeJointFloor_pos)

/-- The action cutoff and pairing cutoff are independent. This is what
allows both existing completion limits, not just a finite diagonal limit. -/
theorem cutoff_pairing_floor (K L : Nat) (hK : 2 ≤ K) (hL : 1 ≤ L) :
    twoStepFloor ≤ centralPhysicalWeightedInner anchorCoupling (by decide) L 0
      (cutoffImage zeroEdgeLabelling K).value (cutoffImage probeState.val K).value := by
  have hroot := cylinder_image_floor K centralLowerCubeState zeroEdgeLabelling rootJointFloor
    (middle_mem K (by omega)) (zeroEdgeLabelling_mem_centralPositiveHalfStates (by decide) K 0)
    (middle_root_joint_floor K (by omega))
  have hprobe := cylinder_image_floor K centralLowerCubeState probeState.val probeJointFloor
    (middle_mem K (by omega)) (probe_mem K hK) (middle_probe_joint_floor K hK)
  have hprod := Q'.mul_le_mul_of_nonneg
    hroot hprobe ((cutoffImage zeroEdgeLabelling K).nonnegative _) (Q'.le_of_lt probeJointFloor_pos)
  have hweight := Q'.mul_le_mul_of_nonneg (middle_row_floor L hL) hprod
    (centralPhysicalRowMarginal_nonnegative (by decide) L 0 _)
    (Q'.mul_nonneg _ _ (Q'.le_of_lt rootJointFloor_pos) (Q'.le_of_lt probeJointFloor_pos))
  exact Q'.le_trans' _ _ _ hweight
    (le_listQSum_of_mem_nonnegative _ (centralPositiveHalfStates anchorCoupling (by decide) L 0)
      centralLowerCubeState (middle_mem L hL) (fun state _ => Q'.mul_nonneg _ _
        (centralPhysicalRowMarginal_nonnegative (by decide) L 0 state)
        (Q'.mul_nonneg _ _ ((cutoffImage zeroEdgeLabelling K).nonnegative state)
          ((cutoffImage probeState.val K).nonnegative state))))

theorem innerLimit_floor (K : Nat) (hK : 2 ≤ K) :
    CReal.leEv (CReal.ofQ' twoStepFloor)
      (innerLimit (w := anchorCoupling) (by decide) (by decide) 0
        (.atom (cutoffImage zeroEdgeLabelling K)) (.atom (cutoffImage probeState.val K))) := by
  intro epsilon hepsilon
  refine ⟨1, fun L hL => ?_⟩
  have h := cutoff_pairing_floor K L hK hL
  have heq := innerLimit_approx_eqv_stage (w := anchorCoupling) (by decide) (by decide) 0 L
    (.atom (cutoffImage zeroEdgeLabelling K)) (.atom (cutoffImage probeState.val K))
  exact Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hepsilon)))

def actionCauchy (state : EdgeLabelling) : (G).Cauchy :=
  centralPhysicalLinearMarkovCutoffCauchy ((pointwise).modulus (.atom (cylinder state)))

theorem actionCauchy_realizes (state : EdgeLabelling) :
    P ((G).embedRep (.atom (cylinder state))) = Quotient.mk (G).completionSetoid (actionCauchy state) :=
  centralPhysicalConcreteAdaptiveCompletedMarkovTransfer_embed (by decide) (by decide) 0 _

/-- A positive mixed pairing of the SAME completed conditional images. -/
theorem completed_images_pairing_floor :
    CReal.RCle (Quotient.mk CReal.crealSetoid (CReal.ofQ' twoStepFloor))
      (M (P ((G).embedRep (.atom (cylinder zeroEdgeLabelling))))
        (P ((G).embedRep (.atom (cylinder probeState.val))))) := by
  rw [actionCauchy_realizes, actionCauchy_realizes]
  change CReal.leEv (CReal.ofQ' twoStepFloor) (physicalCauchyPairingLimit
    (by decide) (by decide) 0 (actionCauchy zeroEdgeLabelling) (actionCauchy probeState.val))
  apply CReal.leEv_of_convergesTo_le (CReal.convergesTo_const _)
    (convergesTo_cofinalReindex (physicalCauchyPairingSeq_converges (by decide) (by decide) 0
      (actionCauchy zeroEdgeLabelling) (actionCauchy probeState.val))
      (fun n => n + 2) (fun n => n) (fun _ n h => Nat.le_trans h (Nat.le_add_right n 2)))
  intro n
  exact innerLimit_floor (n + 2) (by omega)

end YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing

#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.cylinder
#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.cutoffImage
#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.middle_mem
#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.probe_mem
#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.middle_probe_joint_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.middle_row_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.cylinder_image_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.twoStepFloor
#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.twoStepFloor_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.cutoff_pairing_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.innerLimit_floor
#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.actionCauchy
#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.actionCauchy_realizes
#print axioms YMGap.Continuum.BF4PhysicalCubeTwoStepPositivePairing.completed_images_pairing_floor
