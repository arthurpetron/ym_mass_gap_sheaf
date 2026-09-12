/-
# Exact rank-one effect of the existing physical head centering

The moving rational correction changes only the root cylinder. Pass its
literal finite identity through the SAME reflected pairing limits: against
every completed test vector, centering subtracts the correction CReal times
the root pairing. This is not an orthogonal projection along the sector
vacuum. The formula identifies the residual needed for centered-image
density; it does not assert density, a strict gap, or geometric time.
-/

import YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization
import YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage

namespace YMGap.Continuum.BF4PhysicalCubeCenteringPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeNormalizedKernelLimit
open YMGap.Continuum.BF4PhysicalCubeObservableRealization
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization
open YMGap.Continuum.BF4PhysicalCubeSectorVacuum
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorMovingCenteredVacuumPairing
open YMGap.Continuum.RationalKernelSpan
open YMGap.Continuum.ScaledGNSCompletion
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "S" => cubeReflectedSeminorm
local notation "j" => cubeReflectedEmbed
local notation "B" => cubeReflectedInner

/-- Original correction sequence, with its existing constructive cutoff rate. -/
def correctionLimit (p : SectorPresentation) : CReal :=
  centralPhysicalFinitePulledVacuumSectorHeadCorrectionCutoffLimit
    (w := anchorCoupling) (by decide) (by decide) p.base 0 p.coefficient

def centeredCauchy (p : SectorPresentation) : (S).Cauchy :=
  sectorCauchyToReflected (centralPhysicalVacuumSectorMovingCenteredCauchy
    (w := anchorCoupling) (by decide) (by decide) p.base 0 p.coefficient)

def rootShiftSpan (terms : CubeSpan) (c : Q') : CubeSpan := terms ++ [(rootState, c)]

private theorem observable_append (left right : CubeSpan)
    (state : EdgeLabelling) :
    (cubeObservable (left ++ right)).value state ≈
      (cubeObservable left).value state + (cubeObservable right).value state := by
  induction left with
  | nil => exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
  | cons t ts ih =>
    exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ ih)
      (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

theorem rootShiftSpan_observable (terms : CubeSpan) (c : Q') (state : EdgeLabelling) :
    (cubeObservable (rootShiftSpan terms c)).value state ≈
      (cubeObservable terms).value state +
        c * (centralPhysicalStateCylinderUnitObservable 0 rootState.val).value state := by
  refine Q'.eqv_trans _ _ _ (observable_append terms [(rootState, c)] state) ?_
  exact Q'.add_eqv_congr_left _ _ _ (Q'.eqv_of_eq (Q'.add_zero' _))

theorem centered_stage_observable (p : SectorPresentation) (stage : Nat) :
    CentralPhysicalLinearObservable.Equivalent
      (cubeObservable ((centeredCauchy p).seq stage))
      (cubeObservable (rootShiftSpan (presentationToCube p) (-(correctionLimit p).approx stage))) := by
  intro state
  change (cubeObservable (presentationToCube (centralPhysicalVacuumSectorMovingCenteredPresentation
    (w := anchorCoupling) (by decide) p.base 0 p.coefficient stage))).value state ≈ _
  rw [presentationToCube_observable]
  have h := centralPhysicalVacuumSectorMovingCentered_value_equiv_expansion
    (w := anchorCoupling) (by decide) p.base 0 p.coefficient stage state
  dsimp only at h
  rw [centralPhysicalFiniteStateAt_zero_eq_vacuum] at h
  have hshift := rootShiftSpan_observable (presentationToCube p) (-(correctionLimit p).approx stage) state
  rw [presentationToCube_observable] at hshift
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_symm hshift)

theorem centered_stage_recode (p : SectorPresentation) (stage : Nat) :
    j ((centeredCauchy p).seq stage) =
      j (rootShiftSpan (presentationToCube p) (-(correctionLimit p).approx stage)) :=
  (S).embedRep_eq_of_null (cubeObservable_null_of_equivalent (centered_stage_observable p stage))

theorem rootShiftSpan_form (terms test : CubeSpan) (c : Q') :
    (D).B (rootShiftSpan terms c) test ≈ (D).B terms test + c * (D).B rootVector test := by
  refine Q'.eqv_trans _ _ _ (form_add_left (kernel anchorCoupling) terms [(rootState, c)] test) ?_
  apply Q'.add_eqv_congr_left
  refine Q'.eqv_trans _ _ _ (form_congr_left (kernel anchorCoupling) test ?_)
    (form_scale_left (kernel anchorCoupling) c rootVector test)
  intro state
  change c * kernel anchorCoupling rootState state + 0 ≈
    (c * 1) * kernel anchorCoupling rootState state + 0
  exact Q'.add_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv c)))

private theorem dense_pairing (left right : CubeSpan) :
    B (j left) (j right) = Quotient.mk CReal.crealSetoid
      (normalizedFormLimit (w := anchorCoupling) (by decide) (by decide) left right) :=
  scaledCompletedInner_embed D anchorNormalization left right

theorem rootShiftSpan_pairing (terms test : CubeSpan) (c : Q') :
    CReal.Equiv
      (normalizedFormLimit (w := anchorCoupling) (by decide) (by decide) (rootShiftSpan terms c) test)
      (CReal.add (normalizedFormLimit (w := anchorCoupling) (by decide) (by decide) terms test)
        (CReal.mul (CReal.ofQ' c)
          (normalizedFormLimit (w := anchorCoupling) (by decide) (by decide) rootVector test))) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (rootShiftSpan_form terms test c))
    (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_assoc_eqv _ _ _)))

theorem centered_pairingRep (p : SectorPresentation) (Y : (S).Cauchy) :
    CReal.Equiv (cubeReflectedPairingLimit (centeredCauchy p) Y)
      (CReal.add (cubeReflectedPairingLimit ((S).constant (presentationToCube p)) Y)
        (CReal.mul (CReal.neg (correctionLimit p))
          (cubeReflectedPairingLimit ((S).constant rootVector) Y))) := by
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := fun n => normalizedFormLimit (w := anchorCoupling) (by decide) (by decide)
      ((centeredCauchy p).seq n) (Y.seq n))
    (bSeq := fun n => CReal.add
      (normalizedFormLimit (w := anchorCoupling) (by decide) (by decide) (presentationToCube p) (Y.seq n))
      (CReal.mul (CReal.ofQ' (-(correctionLimit p).approx n))
        (normalizedFormLimit (w := anchorCoupling) (by decide) (by decide) rootVector (Y.seq n))))
  · intro n
    have h := congrArg (fun x => B x (j (Y.seq n))) (centered_stage_recode p n)
    dsimp only at h
    rw [dense_pairing, dense_pairing] at h
    exact CReal.Equiv.trans (Quotient.exact h)
      (rootShiftSpan_pairing (presentationToCube p) (Y.seq n) (-(correctionLimit p).approx n))
  · exact cubeReflectedPairingLimit_converges (centeredCauchy p) Y
  · exact CReal.convergesTo_add
      (cubeReflectedPairingLimit_converges ((S).constant (presentationToCube p)) Y)
      (YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general (by
        simpa only [CReal.ofQ'_neg] using
          CReal.convergesTo_neg (CReal.convergesTo_self (correctionLimit p)))
        (cubeReflectedPairingLimit_converges ((S).constant rootVector) Y))

/-- Exact effect of the SAME centering against every completed test vector. -/
theorem centered_pairing (p : SectorPresentation) (y : CubeReflectedCompletion) :
    B (centeredCubeVector p.base p.coefficient).val y =
      CReal.RCadd (B (j (presentationToCube p)) y)
        (CReal.RCmul (CReal.RCneg (Quotient.mk CReal.crealSetoid (correctionLimit p)))
          (B (j rootVector) y)) := by
  refine Quotient.inductionOn y ?_
  intro Y
  exact Quotient.sound (centered_pairingRep p Y)

theorem cubeReflectedInner_sub_left (x y z : CubeReflectedCompletion) :
    B (cubeReflectedSub x y) z = CReal.RCsub (B x z) (B y z) := by
  unfold cubeReflectedInner cubeReflectedSub scaledCompletedInner rawToReflected reflectedToRaw
  rw [raw_scaled_inverse, GNSQuotient.GNSData.cinnerCompl_cSub_left]
  exact RCBilinearDifference.mul_sub _ _ _

private theorem shift_sub (a b : CReal.RC) :
    CReal.RCsub (CReal.RCadd a b) a = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))
    (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _) (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv _)) (Q'.eqv_of_eq (Q'.add_zero' _))))

/-- The actual reflected difference, not a marginal-norm surrogate. -/
def centeringResidual (p : SectorPresentation) : CubeReflectedCompletion :=
  cubeReflectedSub (centeredCubeVector p.base p.coefficient).val (j (presentationToCube p))

theorem centeringResidual_pairing (p : SectorPresentation) (y : CubeReflectedCompletion) :
    B (centeringResidual p) y =
      CReal.RCmul (CReal.RCneg (Quotient.mk CReal.crealSetoid (correctionLimit p))) (B (j rootVector) y) := by
  unfold centeringResidual
  rw [cubeReflectedInner_sub_left, centered_pairing, shift_sub]

private theorem negative_product_square (c r : CReal.RC) :
    CReal.RCmul (CReal.RCneg c) (CReal.RCmul (CReal.RCneg c) r) =
      CReal.RCmul (CReal.RCmul c c) r := by
  refine Quotient.inductionOn₂ c r ?_
  intro C R
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv _ _)
      (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv _ _)) (Q'.neg_neg_eqv _))))

/-- Exact squared error: controlling the correction controls the original
centered vector in the full reflected norm. No density is assumed. -/
theorem centeringResidual_norm (p : SectorPresentation) :
    B (centeringResidual p) (centeringResidual p) =
      CReal.RCmul
        (CReal.RCmul (Quotient.mk CReal.crealSetoid (correctionLimit p))
          (Quotient.mk CReal.crealSetoid (correctionLimit p)))
        (B (j rootVector) (j rootVector)) := by
  rw [centeringResidual_pairing, cubeReflectedInner_symm (j rootVector) (centeringResidual p),
    centeringResidual_pairing, negative_product_square]

end YMGap.Continuum.BF4PhysicalCubeCenteringPairing

#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.correctionLimit
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.centeredCauchy
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.rootShiftSpan
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.rootShiftSpan_observable
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.centered_stage_observable
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.centered_stage_recode
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.rootShiftSpan_form
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.rootShiftSpan_pairing
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.centered_pairingRep
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.centered_pairing
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.cubeReflectedInner_sub_left
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.centeringResidual
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.centeringResidual_pairing
#print axioms YMGap.Continuum.BF4PhysicalCubeCenteringPairing.centeringResidual_norm
