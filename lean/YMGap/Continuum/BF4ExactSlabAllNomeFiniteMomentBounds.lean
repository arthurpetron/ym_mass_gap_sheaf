/-
# Actual normalized finite moments and three-moment covariance comparison

The existing two-sided polynomial interval is integrated against the actual
positive selected heat product. Its SAME partition cancels, leaving the
original interval cap, with no volume-dependent reciprocal penalty.

Three supplied finite moment errors then bound the connected covariance
error by 6*c*c*eta when the marginal errors are 2*c*eta and the joint error
is 2*c*c*eta. A cleared original numerator floor also survives this SAME
normalization. The geometric errors and positive numerator floor are not
assumed to hold automatically; their concrete proofs are separate inputs.
No cutoff/volume limit, physical scale, transfer or continuum claim follows.
-/

import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
import YMGap.Continuum.QuaternionHaarBiadditive
import YMGap.Continuum.RationalConnectedResponse
import YMGap.Continuum.BF4ExactSlabSpectatorResummation

namespace YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation (connectedNumerator)
open YMGap.Continuum.BF4ExactSlabSpectatorResummation (partitionSquare)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarBiadditive (abs_product_bound)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem ratio_abs_bound (a Z c : Q') (hZ : (0 : Q') < Z)
    (h : Q'.abs a ≤ c*Z) : Q'.abs (a*Q'.recipPos Z hZ) ≤ c := by
  have hr := Q'.le_of_lt (Q'.recipPos_pos Z hZ)
  have ha := ExpNeg.abs_mul_le a (Q'.recipPos Z hZ)
  rw [ExpNeg.abs_of_nonneg hr] at ha
  exact Q'.le_trans' _ _ _ ha
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ h hr)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left c _ _ (Q'.mul_recipPos_eqv Z hZ))
          (Q'.mul_one_eqv c)))))

/-- Actual all-nome finiteValue, at its original cutoff headCutoff(w)+stage. -/
theorem finiteValue_abs_bound (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p : RatPoly) (c : Q')
    (P : Interval (boundaryCompleteSlabLinks extent).length p c) (stage : Nat) :
    Q'.abs (finiteValue w hw0 hw1 extent ids hi p stage) ≤ c := by
  have H := headProduct_certificate hw0 hw1 (headCutoff w+stage) extent
    (Nat.le_add_right _ _) ids hi
  have h := P.weighted_haar_bound H
  have hp := @haar_of_coeff (boundaryCompleteSlabLinks extent).length _ _ (RatPolyCoeffEqv.mul_comm p
    (polynomialProduct (faceHeatPolynomial w (headCutoff w+stage) extent) ids))
  have hn : Q'.abs (numerator w (boundaryCompleteSlabLinks extent).length extent ids p
      (headCutoff w+stage)) ≤
      c*heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids (headCutoff w+stage) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hp)) h
  unfold finiteValue reciprocalTerm PositiveRationalCauchyReciprocal.term partitionSample
  exact ratio_abs_bound _ _ c _ hn

/-- Only two endpoint marginal caps are needed; all six moments may be signed. -/
theorem covariance_difference_bound (a b ab a' b' ab' c e0 e1 e2 : Q')
    (ha : Q'.abs a ≤ c) (hb' : Q'.abs b' ≤ c)
    (h0 : Q'.abs (ab + -ab') ≤ e0)
    (h1 : Q'.abs (a + -a') ≤ e1) (h2 : Q'.abs (b + -b') ≤ e2) :
    Q'.abs ((ab + -(a*b)) + -(ab' + -(a'*b'))) ≤ e0 + (c*e2+c*e1) := by
  have hprod : Q'.abs (a*b + -(a'*b')) ≤ c*e2+c*e1 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (mul_sub_decomp a b a' b')))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
        (Q'.add_le_add (abs_product_bound ha h2) (abs_product_bound hb' h1)))
  have hsplit : (ab + -(a*b)) + -(ab' + -(a'*b')) ≈
      (ab + -ab') + -(a*b + -(a'*b')) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
        (.neg (.add (.var 3) (.neg (.mul (.var 4) (.var 5))))))
      (.add (.add (.var 0) (.neg (.var 3)))
        (.neg (.add (.mul (.var 1) (.var 2)) (.neg (.mul (.var 4) (.var 5))))))
      (by decide) (fun | 0 => ab | 1 => a | 2 => b | 3 => ab' | 4 => a' | _ => b')
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit))
    (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
      (Q'.add_le_add h0 (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _)) hprod)))

/-- The factor six is the joint error plus the two capped marginal errors. -/
theorem covariance_six_bound (a b ab a' b' ab' c eta : Q')
    (ha : Q'.abs a ≤ c) (hb' : Q'.abs b' ≤ c)
    (h0 : Q'.abs (ab + -ab') ≤ (2*c*c)*eta)
    (h1 : Q'.abs (a + -a') ≤ (2*c)*eta)
    (h2 : Q'.abs (b + -b') ≤ (2*c)*eta) :
    Q'.abs ((ab + -(a*b)) + -(ab' + -(a'*b'))) ≤ (6*c*c)*eta :=
  Q'.le_trans' _ _ _ (covariance_difference_bound a b ab a' b' ab' c _ _ _ ha hb' h0 h1 h2)
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.mul (.mul (.const 2) (.var 0)) (.var 0)) (.var 1))
        (.add (.mul (.var 0) (.mul (.mul (.const 2) (.var 0)) (.var 1)))
          (.mul (.var 0) (.mul (.mul (.const 2) (.var 0)) (.var 1)))))
      (.mul (.mul (.mul (.const 6) (.var 0)) (.var 0)) (.var 1))
      (by decide) (fun | 0 => c | _ => eta)))

section ActualMoments

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (extent : Nat) (left : List Nat)
  (hl : ∀ id, id ∈ left → id ∈ slabPhysicalFaceEdges extent)
  (right : List Nat) (hr : ∀ id, id ∈ right → id ∈ slabPhysicalFaceEdges extent)

local notation "Fl" => finiteValue w hw0 hw1 extent left hl
local notation "Fr" => finiteValue w hw0 hw1 extent right hr

/-- The same two actual actions and cutoff occur in all three comparisons. -/
theorem finite_covariance_comparison (p q : RatPoly) (c eta : Q')
    (P : Interval (boundaryCompleteSlabLinks extent).length p c)
    (Q : Interval (boundaryCompleteSlabLinks extent).length q c) (stage : Nat)
    (h0 : Q'.abs (Fl (polyMul p q) stage + -(Fr (polyMul p q) stage)) ≤ (2*c*c)*eta)
    (h1 : Q'.abs (Fl p stage + -(Fr p stage)) ≤ (2*c)*eta)
    (h2 : Q'.abs (Fl q stage + -(Fr q stage)) ≤ (2*c)*eta) :
    Q'.abs ((Fl (polyMul p q) stage + -(Fl p stage*Fl q stage)) +
      -(Fr (polyMul p q) stage + -(Fr p stage*Fr q stage))) ≤ (6*c*c)*eta :=
  covariance_six_bound _ _ _ _ _ _ c eta
    (finiteValue_abs_bound w hw0 hw1 extent left hl p c P stage)
    (finiteValue_abs_bound w hw0 hw1 extent right hr q c Q stage) h0 h1 h2

end ActualMoments

/-- Cancel the actual positive partition square; no sign assumption on the moments. -/
theorem finite_covariance_floor (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p q : RatPoly) (rho : Q') (stage : Nat)
    (h : rho*partitionSquare w (headCutoff w+stage) extent ids ≤
      connectedNumerator w (headCutoff w+stage) extent ids p q) :
    rho ≤ finiteValue w hw0 hw1 extent ids hi (polyMul p q) stage +
      -(finiteValue w hw0 hw1 extent ids hi p stage*finiteValue w hw0 hw1 extent ids hi q stage) := by
  let Z := heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids (headCutoff w+stage)
  have hZ : (0 : Q') < Z := Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
    (partition_floor hw0 hw1 extent ids hi _ (Nat.le_add_right _ _))
  have hc := RationalConnectedResponse.covariance_clear Z
    (numerator w (boundaryCompleteSlabLinks extent).length extent ids p (headCutoff w+stage))
    (numerator w (boundaryCompleteSlabLinks extent).length extent ids q (headCutoff w+stage))
    (numerator w (boundaryCompleteSlabLinks extent).length extent ids (polyMul p q) (headCutoff w+stage))
    (Q'.recipPos Z hZ) (Q'.mul_recipPos_eqv Z hZ)
  unfold finiteValue reciprocalTerm PositiveRationalCauchyReciprocal.term partitionSample
  apply Q'.le_of_mul_le_mul_left (c := Z*Z) _ (Q'.mul_pos hZ hZ)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv (Z*Z) rho))
    (Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.eqv_symm hc) (Q'.mul_comm_eqv _ _))))

end YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds

#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds.finiteValue_abs_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds.covariance_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds.covariance_six_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds.finite_covariance_comparison
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds.finite_covariance_floor
