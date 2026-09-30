/-
# Exact closed-loop moments in the shared-heat three-path law

Block zero is a common spectator path C; blocks one and two are A and B.
The weight is the full original finite relative heat packet of A and B.
The tests are scalar(C A^-1) and scalar(C B^-1), not open-link coordinates.
Integrating C gives one quarter of the relative scalar of A and B.

Every cutoff spin is retained. This is a three-path heat law, NOT the
original full-slab action with all its one-sided plaquette factors.
-/

import YMGap.Continuum.SU2QuaternionSharedHeatCorrelationObstruction
import YMGap.Continuum.SU2QuaternionHaarCertificateLift

namespace YMGap.Continuum.SU2QuaternionSharedHeatLoopMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabSymmetricPowerHaarTrace
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHaarHeadConditionalProduct
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadLinearHaar (liftHead_mul)
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionRelativeHeatTransmission
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatMarkovData
open YMGap.Continuum.SU2QuaternionRelativeHeatContraction
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv

def weight (w : Q') (K : Nat) : RatPoly := liftHead (relativeHeat w K)
def leftLoop : RatPoly := scalarAt 0 1
def rightLoop : RatPoly := scalarAt 0 2
abbrev quarter : Q' := SU2QuaternionSharedHeatCorrelationObstruction.quarter

/-- Integrate only the common path. The interacting A/B packet is unchanged. -/
theorem integrate_common (w : Q') (K : Nat) (p : RatPoly) :
    quaternionHaar 3 (polyMul p (weight w K)) ≈
      quaternionHaar 2 (polyMul (partialHaarHead p) (relativeHeat w K)) := by
  have h := quaternionHaar_polyMul_headIndependent 2 p (weight w K)
    (SU2QuaternionRelativeHeatInsertion.lifted_independent _)
  rw [weight, drop_liftHead] at h
  exact h

theorem left_partial : RatPolyCoeffEqv (partialHaarHead leftLoop) polyZero := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

theorem right_partial : RatPolyCoeffEqv (partialHaarHead rightLoop) polyZero := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

theorem left_square_partial : RatPolyCoeffEqv
    (partialHaarHead (polyMul leftLoop leftLoop))
    (polySmul quarter (polyQuaternionNorm (PolyQuaternion.coordinateVariable 0))) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

theorem right_square_partial : RatPolyCoeffEqv
    (partialHaarHead (polyMul rightLoop rightLoop))
    (polySmul quarter (polyQuaternionNorm (PolyQuaternion.coordinateVariable 1))) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

/-- The retained mixed loop is not zero: it is the relative scalar of A/B. -/
theorem mixed_partial : RatPolyCoeffEqv
    (partialHaarHead (polyMul leftLoop rightLoop)) (polySmul quarter relativeScalar) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private def coordinateProduct (i : Fin 4) : RatPoly :=
  polyMul (polyVar i.val) (liftHead (polyVar i.val))

private theorem scalar_four : RatPolyCoeffEqv relativeScalar
    (polyAdd (coordinateProduct 0) (polyAdd (coordinateProduct 1)
      (polyAdd (coordinateProduct 2) (coordinateProduct 3)))) := by
  apply RatPolyCoeffEqv.of_canon_termwise
  decide +kernel

private theorem weighted_add (W p q : RatPoly) :
    quaternionHaar 2 (polyMul (polyAdd p q) W) ≈
      quaternionHaar 2 (polyMul p W) + quaternionHaar 2 (polyMul q W) := by
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append 2 _ _

theorem relative_scalar_moment (w : Q') (K : Nat) (hK : 1 ≤ K) :
    quaternionHaar 2 (polyMul relativeScalar (relativeHeat w K)) ≈ qpow w 3 := by
  have hcoord (i : Fin 4) :
      quaternionHaar 2 (polyMul (coordinateProduct i) (relativeHeat w K)) ≈
        qpow w 3 * quarter := by
    have h := coordinate_transmission 1 (by decide) w K hK i (polyVar i.val)
    have hv : ∀ j : Fin 4, quaternionHaar 1 (polyMul (polyVar j.val) (polyVar j.val)) ≈ quarter := by
      decide +kernel
    exact Q'.eqv_trans _ _ _ (haar_of_coeff
      ((RatPolyCoeffEqv.mul_comm _ _).trans (RatPolyCoeffEqv.mul_assoc _ _ _).symm))
      (Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_left _ _ _ (hv i)))
  refine Q'.eqv_trans _ _ _ (haar_of_coeff (scalar_four.mul_right _)) ?_
  refine Q'.eqv_trans _ _ _ (weighted_add _ _ _) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (hcoord 0)
    (Q'.eqv_trans _ _ _ (weighted_add _ _ _)
      (Q'.add_eqv_congr' (hcoord 1) (Q'.eqv_trans _ _ _ (weighted_add _ _ _)
        (Q'.add_eqv_congr' (hcoord 2) (hcoord 3)))))) ?_
  have he := poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1))
      (.add (.mul (.var 0) (.var 1))
        (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))))
    (.mul (.var 0) (.add (.var 1) (.add (.var 1) (.add (.var 1) (.var 1)))))
    (by decide) (fun | 0 => qpow w 3 | _ => quarter)
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (by decide : quarter + (quarter + (quarter + quarter)) ≈ 1))
    (Q'.mul_one_eqv _))

theorem mass (w : Q') (K : Nat) : quaternionHaar 3 (weight w K) ≈ 1 :=
  Q'.eqv_trans _ _ _ (haar_liftBoundary 1 2 _) (SU2QuaternionSharedHeatCorrelationObstruction.heat_mass w K)

theorem left_mean (w : Q') (K : Nat) :
    quaternionHaar 3 (polyMul leftLoop (weight w K)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (integrate_common w K _)
    (haar_of_coeff (left_partial.mul_right _))

theorem right_mean (w : Q') (K : Nat) :
    quaternionHaar 3 (polyMul rightLoop (weight w K)) ≈ 0 :=
  Q'.eqv_trans _ _ _ (integrate_common w K _)
    (haar_of_coeff (right_partial.mul_right _))

private theorem square_moment (w : Q') (K : Nat) (p : RatPoly) (i : Fin 2)
    (hp : RatPolyCoeffEqv (partialHaarHead (polyMul p p))
      (polySmul quarter (polyQuaternionNorm (PolyQuaternion.coordinateVariable i.val)))) :
    weightedPair 3 (weight w K) p p ≈ quarter := by
  have hn := haarNorm_coordinate i.isLt
  have he := haar_of_carrier ((QuaternionHaarCarrierEqv.smul quarter hn).mul_right (relativeHeat w K))
  refine Q'.eqv_trans _ _ _ (integrate_common w K _) ?_
  refine Q'.eqv_trans _ _ _ (haar_of_coeff (hp.mul_right _)) (Q'.eqv_trans _ _ _ he ?_)
  refine Q'.eqv_trans _ _ _ (haar_of_coeff
    ((RatPolyCoeffEqv.polyMul_smul_left quarter polyOne _).trans
      ((RatPolyCoeffEqv.one_mul _).smul quarter))) ?_
  exact Q'.eqv_trans _ _ _ (quaternionHaar_polySmul 2 quarter _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
      (SU2QuaternionSharedHeatCorrelationObstruction.heat_mass w K)) (Q'.mul_one_eqv quarter))

theorem left_variance (w : Q') (K : Nat) :
    weightedPair 3 (weight w K) leftLoop leftLoop ≈ quarter :=
  square_moment w K leftLoop ⟨0, by decide⟩ left_square_partial

theorem right_variance (w : Q') (K : Nat) :
    weightedPair 3 (weight w K) rightLoop rightLoop ≈ quarter :=
  square_moment w K rightLoop ⟨1, by decide⟩ right_square_partial

theorem covariance (w : Q') (K : Nat) (hK : 1 ≤ K) :
    weightedPair 3 (weight w K) leftLoop rightLoop ≈ qpow w 3 * quarter :=
  Q'.eqv_trans _ _ _ (integrate_common w K _)
    (Q'.eqv_trans _ _ _ (haar_of_coeff ((mixed_partial.mul_right _).trans
      (RatPolyCoeffEqv.polyMul_smul_left quarter _ _)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul 2 quarter _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (relative_scalar_moment w K hK))
          (Q'.mul_comm_eqv _ _))))

/-- Positivity of the literal three-path weight at the original late cutoff. -/
def weightCertificate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : BF4ExactSlabRetainedHeatHeadComparison.headCutoff w ≤ K) :
    Certificate 3 (weight w K) := lift_certificate 1 (relativeHeat_certificate hw0 hw1 K hK)

#print axioms integrate_common
#print axioms left_partial
#print axioms right_partial
#print axioms left_square_partial
#print axioms right_square_partial
#print axioms mixed_partial
#print axioms relative_scalar_moment
#print axioms mass
#print axioms left_mean
#print axioms right_mean
#print axioms left_variance
#print axioms right_variance
#print axioms covariance
#print axioms weightCertificate

end YMGap.Continuum.SU2QuaternionSharedHeatLoopMoments
