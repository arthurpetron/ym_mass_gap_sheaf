/-
# The actual sector vacuum pairing and moving-centered observable realization

On every completed marginal-sector input, pairing with the constructed
sector vacuum equals the original global stationary mean. The proof starts
with support of each literal finite cylinder and passes the identity through
the existing representative pairing limits. No representative is selected.

Consequently the existing moving rational head-centering construction gives
vectors in the NEW reflected vacuum complement, and their conditional-power
correlators are the SAME original physical mean-zero matrix coefficients.
This head correction is not orthogonal projection along the sector vacuum.
Its earlier positive MARGINAL norm does not establish a positive REFLECTED
norm; that nontriviality bridge remains open, as do strict gap and time pins.
-/

import YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumOrthogonal

namespace YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeSectorIndicator
open YMGap.Continuum.BF4PhysicalCubeSectorVacuum
open YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeContainment
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumOrthogonal
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "Presentation" => CentralPhysicalVacuumSectorCylinderPresentation anchorCoupling (by decide) 0
local notation "M" => centralPhysicalVacuumSectorCylinderSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "G" => centralPhysicalCutoffLinearSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "B" => centralPhysicalCutoffCompletedInner
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "I" => centralPhysicalVacuumSectorCylinderCompletionToGlobal
  (hw0 := (by decide : (0 : Q') < anchorCoupling))
  (hw1 := (by decide : anchorCoupling < (1 : Q'))) (half := 0)
local notation "V" => centralPhysicalCutoffCompletedVacuum
  (w := anchorCoupling) (by decide) (by decide) 0

/-- Every finite sector cylinder vanishes off the exact sector event on
physical lower-supported states, independently of the later cutoff. -/
theorem presentation_zero_off_sector (p : Presentation) (state : EdgeLabelling)
    (hsupport : ∀ face, face ∉ centralLowerFaceIds 0 → state face = 0)
    (hoff : cubeSectorB state = false) : p.toLinearObservable.value state ≈ 0 := by
  refine Q'.eqv_trans _ _ _ (centralPhysicalStateCylinderLinearCombination_value 0
    (centralPhysicalFiniteStateAt anchorCoupling (by decide) p.base 0) p.coefficient state
    (centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide) p.base 0)) ?_
  refine Q'.eqv_trans _ (listQSum (fun _ : Nat => (0 : Q'))
    (centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide) p.base 0)) _ ?_ (listQSum_zero _)
  apply listQSum_congr_on
  intro index hindex
  cases hmatch : labellingsAgreeOnB (centralLowerFaceIds 0) state
      (centralPhysicalFiniteStateAt anchorCoupling (by decide) p.base 0 index) with
  | false => exact Q'.eqv_refl 0
  | true =>
      have hsector := centralPhysicalFiniteVacuumSectorState_mem_of_index
        anchorCoupling (by decide) p.base 0 hindex rfl
      have hhalf := centralPhysicalFiniteVacuumSectorState_mem_halfStates
        anchorCoupling (by decide) p.base 0 hsector
      have heq : state = centralPhysicalFiniteStateAt anchorCoupling (by decide) p.base 0 index := by
        funext face
        by_cases hf : face ∈ centralLowerFaceIds 0
        · exact (labellingsAgreeOnB_true_iff _ _ _).mp hmatch face hf
        · exact (hsupport face hf).trans ((boundedEdgeLabellings_sound p.base _ _ hhalf).2 face hf).symm
      have hclass := vacuumSector_cubeSupportedCommonParity anchorCoupling (by decide) p.base hsector
      rw [← heq] at hclass
      have hon := (cubeSectorB_iff state hsupport).mpr hclass
      exact False.elim (Bool.noConfusion (hoff.symm.trans hon))

theorem presentation_sector_pairing_eq_mean (p : Presentation) :
    CReal.Equiv
      (innerLimit (w := anchorCoupling) (by decide) (by decide) 0 p.toLinearObservable sectorLinearObservable)
      (innerLimit (w := anchorCoupling) (by decide) (by decide) 0 p.toLinearObservable centralPhysicalLinearVacuum) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro K
  refine Q'.eqv_trans _ _ _
    (innerLimit_approx_eqv_stage (w := anchorCoupling) (by decide) (by decide) 0 K _ _) ?_
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.eqv_symm (innerLimit_approx_eqv_stage (w := anchorCoupling) (by decide) (by decide) 0 K _ _))
  change centralPhysicalWeightedInner anchorCoupling (by decide) K 0 p.toLinearObservable.value
      cubeSectorIndicator ≈
    centralPhysicalWeightedInner anchorCoupling (by decide) K 0 p.toLinearObservable.value (fun _ => 1)
  unfold centralPhysicalWeightedInner
  apply listQSum_congr_on
  intro state hs
  apply Q'.mul_eqv_congr_left
  cases hb : cubeSectorB state with
  | true => simp only [cubeSectorIndicator, hb, if_true]; exact Q'.eqv_refl _
  | false =>
      have hz := presentation_zero_off_sector p state
        (boundedEdgeLabellings_sound K _ state (mem_centralPositiveHalfStates_iff.mp hs).1).2 hb
      simp only [cubeSectorIndicator, hb, Bool.false_eq_true, if_false]
      exact Q'.eqv_trans _ _ _ (Q'.mul_zero_eqv _)
        (Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_one_eqv _) hz))

/-- This identity holds on the ENTIRE existing completed marginal sector. -/
theorem completedSector_pairing_eq_mean (x : (M).Completion) :
    B (I x) ((G).embedRep sectorLinearObservable) = B (I x) V := by
  refine Quotient.inductionOn x ?_
  intro X
  change physicalCauchyPairingLimitR (by decide) (by decide) 0
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X) ((G).constant sectorLinearObservable) =
    physicalCauchyPairingLimitR (by decide) (by decide) 0
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X) ((G).constant centralPhysicalLinearVacuum)
  apply Quotient.sound
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := physicalCauchyPairingSeq (by decide) (by decide) 0
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X) ((G).constant sectorLinearObservable))
    (bSeq := physicalCauchyPairingSeq (by decide) (by decide) 0
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X) ((G).constant centralPhysicalLinearVacuum))
  · intro stage
    exact presentation_sector_pairing_eq_mean (X.seq stage)
  · exact physicalCauchyPairingSeq_converges (by decide) (by decide) 0
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X) ((G).constant sectorLinearObservable)
  · exact physicalCauchyPairingSeq_converges (by decide) (by decide) 0
      (centralPhysicalVacuumSectorCylinderCauchyToGlobal X) ((G).constant centralPhysicalLinearVacuum)

/-- Orthogonality to the new reflected vacuum is the ORIGINAL mean-zero
condition for every source vector; no second measure is introduced. -/
theorem reflectedSectorVacuum_pairing_eq_mean (x : (M).Completion) :
    cubeReflectedInner reflectedSectorVacuum (sectorToReflected x) = B (I x) V := by
  rw [cubeReflectedInner_symm]
  unfold reflectedSectorVacuum
  rw [sectorToReflected_pairing, sectorVacuum_global]
  unfold completedReflectedForm
  rw [globalSectorVacuum_fixed]
  exact completedSector_pairing_eq_mean x

/-- Reuse the already constructed moving rational head correction and its
Cauchy modulus, rather than pretending its limiting coefficient is rational. -/
def centeredSectorSource (base : Nat) (coefficient : Nat → Q') : (M).Completion :=
  centralPhysicalVacuumSectorMovingCenteredCompletion
    (w := anchorCoupling) (by decide) (by decide) base 0 coefficient

theorem centeredSectorSource_mean_zero (base : Nat) (coefficient : Nat → Q') :
    B (I (centeredSectorSource base coefficient)) V = CReal.RCzero :=
  centralPhysicalVacuumSectorMovingCenteredGlobalVector_vacuumOrthogonal
    (w := anchorCoupling) (by decide) (by decide) base 0 coefficient

def centeredCubeVector (base : Nat) (coefficient : Nat → Q') : CubeSectorVacuumComplement :=
  ⟨sectorToReflected (centeredSectorSource base coefficient), by
    rw [reflectedSectorVacuum_pairing_eq_mean]
    exact centeredSectorSource_mean_zero base coefficient⟩

def centeredCubeCorrelator (base : Nat) (coefficient : Nat → Q') (n : Nat) : CReal.RC :=
  cubeReflectedInner (centeredCubeVector base coefficient).val
    (cubeTransferPower n (centeredCubeVector base coefficient).val)

/-- Exact same-object conditional moments, including the E form's extra
insertion. Zero mean is proved by centeredCubeVector, not supplied as input. -/
theorem centeredCubeCorrelator_physical (base : Nat) (coefficient : Nat → Q') (n : Nat) :
    centeredCubeCorrelator base coefficient n =
      B (I (centeredSectorSource base coefficient))
        (centralPhysicalConcreteAdaptiveCompletedMarkovPower
          (w := anchorCoupling) (by decide) (by decide) 0 (n + 1)
          (I (centeredSectorSource base coefficient))) := by
  exact cubeTransferPower_sector_moments n
    (centeredSectorSource base coefficient) (centeredSectorSource base coefficient)

/-- Covariance under the original normalized global physical law. This uses
its unit vacuum V, not a presumed unit normalization of the sector vector. -/
def globalConditionalCovariance (n : Nat) (x y : (G).Completion) : CReal.RC :=
  CReal.RCadd (B x (centralPhysicalConcreteAdaptiveCompletedMarkovPower
    (w := anchorCoupling) (by decide) (by decide) 0 n y))
    (CReal.RCneg (CReal.RCmul (B x V) (B y V)))

/-- Literal mean subtraction vanishes for the same constructed observable. -/
theorem centeredCubeCorrelator_connected (base : Nat) (coefficient : Nat → Q') (n : Nat) :
    globalConditionalCovariance (n + 1) (I (centeredSectorSource base coefficient))
      (I (centeredSectorSource base coefficient)) = centeredCubeCorrelator base coefficient n := by
  unfold globalConditionalCovariance
  rw [centeredSectorSource_mean_zero, ← centeredCubeCorrelator_physical]
  refine Quotient.inductionOn (centeredCubeCorrelator base coefficient n) ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun k => Q'.eqv_of_eq (Q'.add_zero' (A.approx k))))

end YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization

#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization.presentation_zero_off_sector
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization.presentation_sector_pairing_eq_mean
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization.completedSector_pairing_eq_mean
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization.reflectedSectorVacuum_pairing_eq_mean
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization.centeredSectorSource
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization.centeredSectorSource_mean_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization.centeredCubeVector
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization.centeredCubeCorrelator
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization.centeredCubeCorrelator_physical
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization.globalConditionalCovariance
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization.centeredCubeCorrelator_connected
