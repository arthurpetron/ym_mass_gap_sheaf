/-
# Original-action Haar limits with arbitrary polynomial insertions

The insertion shares the original link variables. Its literal coefficient
L1 norm rescales the existing action-tail and Jacobi-comparison moduli.
This constructs the original interacting numerator CReal for every signed
polynomial, without an independence or pointwise-to-Haar premise.
-/

import YMGap.Continuum.BF4ExactSlabJacobiProductComparison
import YMGap.Continuum.FCLimitContinuity
import YMGap.Constructive.TrigAddCReal

namespace YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.BF4ExactSlabJacobiProductComparison
open YMGap.Continuum.BF4ExactSlabJacobiWeightedHeatPin
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem rational_add_converges {r s : Nat → Q'} {A B : CReal}
    (hr : CReal.ConvergesTo (fun K => CReal.ofQ' (r K)) A)
    (hs : CReal.ConvergesTo (fun K => CReal.ofQ' (s K)) B) :
    CReal.ConvergesTo (fun K => CReal.ofQ' (r K + s K)) (CReal.add A B) := by
  apply TrigAddCReal.convergesTo_congr_seq
    (s := fun K => CReal.add (CReal.ofQ' (r K)) (CReal.ofQ' (s K)))
    (t := fun K => CReal.ofQ' (r K + s K)) _ (CReal.convergesTo_add hr hs)
  intro K
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl (r K + s K))

def insertionTolerance (p : RatPoly) (epsilon : Q') : Q' :=
  HKConv.divPos epsilon (polynomialCoefficientL1 p + 1)

theorem insertionTolerance_pos (p : RatPoly) {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < insertionTolerance p epsilon := HKConv.divPos_pos (CReal.num_pos_of_pos he)

theorem insertionTolerance_budget (p : RatPoly) {epsilon : Q'} (he : (0 : Q') < epsilon) :
    polynomialCoefficientL1 p * insertionTolerance p epsilon ≤ epsilon := by
  have hpos : (0 : Q') < polynomialCoefficientL1 p + 1 :=
    Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ (polynomialCoefficientL1_nonnegative p))
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
      (Q'.le_of_lt (insertionTolerance_pos p he)))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hpos))))

theorem insertedHaar_small (blocks : Nat) (p r : RatPoly) {epsilon : Q'} (he : (0 : Q') < epsilon)
    (hr : polynomialCoefficientL1 r ≤ insertionTolerance p epsilon) :
    Q'.abs (quaternionHaar blocks (polyMul p r)) ≤ epsilon :=
  Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _)
    (Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hr (polynomialCoefficientL1_nonnegative p))
        (insertionTolerance_budget p he)))

def numerator (w : Q') (blocks extent : Nat) (ids : List Nat) (p : RatPoly) (K : Nat) : Q' :=
  quaternionHaar blocks (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) ids))

def numeratorCutoff (w : Q') (extent : Nat) (ids : List Nat) (p : RatPoly) (epsilon : Q') : Nat :=
  heatProductCutoff w extent ids (insertionTolerance p epsilon)

theorem numerator_increment {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) (p : RatPoly) (epsilon : Q') (he : (0 : Q') < epsilon)
    (K L : Nat) (hK : numeratorCutoff w extent ids p epsilon ≤ K) :
    numerator w blocks extent ids p (K + L) ≤ numerator w blocks extent ids p K + epsilon ∧
    numerator w blocks extent ids p K ≤ numerator w blocks extent ids p (K + L) + epsilon :=
  close_of_add_remainder
    (Q'.eqv_trans _ _ _ (haar_of_coeff_eqv blocks
      (((heatProduct_cutoff_append w extent K L ids).mul_left p).trans (RatPolyCoeffEqv.mul_add_right _ _ _)))
      (quaternionHaar_append blocks _ _))
    (insertedHaar_small blocks p _ he
      (heatProductRemainder_small hw0 hw1 extent ids _ (insertionTolerance_pos p he) K L hK))

def numeratorCauchy (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) (p : RatPoly) : CReal.QCauchy (numerator w blocks extent ids p) where
  M := numeratorCutoff w extent ids p
  bound := by
    intro epsilon he i j hi hj
    rcases Nat.le_total i j with hij | hji
    · have h := numerator_increment hw0 hw1 blocks extent ids p epsilon he i (j - i) hi
      rw [Nat.add_sub_of_le hij] at h
      exact h.symm
    · have h := numerator_increment hw0 hw1 blocks extent ids p epsilon he j (i - j) hj
      rw [Nat.add_sub_of_le hji] at h
      exact h

def numeratorLimit (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) (p : RatPoly) : CReal :=
  CReal.ofQ'CauchySeq _ (numeratorCauchy w hw0 hw1 blocks extent ids p)

theorem numerator_converges (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) (p : RatPoly) :
    CReal.ConvergesTo (fun K => CReal.ofQ' (numerator w blocks extent ids p K))
      (numeratorLimit w hw0 hw1 blocks extent ids p) := CReal.convergesTo_ofQ'CauchySeq _ _

/-- Both cutoff and CReal representative-index thresholds are explicit. -/
theorem numerator_approx_close (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) (p : RatPoly) (epsilon : Q') (he : (0 : Q') < epsilon)
    (K n : Nat) (hK : numeratorCutoff w extent ids p epsilon ≤ K) (hn : numeratorCutoff w extent ids p epsilon ≤ n) :
    numerator w blocks extent ids p K ≤ (numeratorLimit w hw0 hw1 blocks extent ids p).approx n + epsilon ∧
    (numeratorLimit w hw0 hw1 blocks extent ids p).approx n ≤ numerator w blocks extent ids p K + epsilon :=
  (numeratorCauchy w hw0 hw1 blocks extent ids p).bound epsilon he K _ hK
    (Nat.le_trans hn (CReal.self_le_QMhat _ _ n))

def insertedComparisonCutoff (w : Q') (extent : Nat) (ids : List Nat) (p : RatPoly) (epsilon : Q') : Nat :=
  comparisonCutoff w extent ids (insertionTolerance p epsilon)

theorem numerator_weighted_close {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) (p : RatPoly) (epsilon : Q') (he : (0 : Q') < epsilon)
    (K : Nat) (hK : insertedComparisonCutoff w extent ids p epsilon ≤ K) :
    numerator w blocks extent ids p K ≤
      quaternionHaar blocks (polyMul p (polynomialProduct (weightedFace w (K+1) extent) ids)) + epsilon ∧
    quaternionHaar blocks (polyMul p (polynomialProduct (weightedFace w (K+1) extent) ids)) ≤
      numerator w blocks extent ids p K + epsilon :=
  close_of_add_remainder
    (Q'.eqv_trans _ _ _ (haar_of_coeff_eqv blocks
      (((original_eq_weighted_add_deficit w K extent ids).mul_left p).trans (RatPolyCoeffEqv.mul_add_right _ _ _)))
      (quaternionHaar_append blocks _ _))
    (insertedHaar_small blocks p _ he
      (productDeficit_small hw0 hw1 extent ids _ (insertionTolerance_pos p he) K hK))

theorem eqv_close {a b : Q'} (h : a ≈ b) (epsilon : Q') (he : (0 : Q') < epsilon) :
    a ≤ b + epsilon ∧ b ≤ a + epsilon :=
  ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv h) (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)),
   Q'.le_trans' _ _ _ (Q'.ge_of_eqv h) (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

theorem numeratorLimit_one (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) :
    CReal.Equiv (numeratorLimit w hw0 hw1 blocks extent ids polyOne)
      (heatProductHaarLimit w hw0 hw1 blocks extent ids) :=
  CReal.Equiv_of_ofQ'_limit_close (numerator_converges w hw0 hw1 blocks extent ids polyOne)
    (heatProductHaar_converges w hw0 hw1 blocks extent ids)
    (fun epsilon he => ⟨0, fun _ _ => eqv_close (haar_of_coeff_eqv blocks (RatPolyCoeffEqv.one_mul _)) epsilon he⟩)

theorem numeratorLimit_congr (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    CReal.Equiv (numeratorLimit w hw0 hw1 blocks extent ids p) (numeratorLimit w hw0 hw1 blocks extent ids q) :=
  CReal.Equiv_of_ofQ'_limit_close (numerator_converges w hw0 hw1 blocks extent ids p)
    (numerator_converges w hw0 hw1 blocks extent ids q)
    (fun epsilon he => ⟨0, fun _ _ => eqv_close (haar_of_coeff_eqv blocks (h.mul_right _)) epsilon he⟩)

/-- Respects the actual quaternion-Haar relations, including sphere identities. -/
theorem numeratorLimit_carrier_congr (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) {p q : RatPoly} (h : HaarCarrierEqv blocks p q) :
    CReal.Equiv (numeratorLimit w hw0 hw1 blocks extent ids p) (numeratorLimit w hw0 hw1 blocks extent ids q) :=
  CReal.Equiv_of_ofQ'_limit_close (numerator_converges w hw0 hw1 blocks extent ids p)
    (numerator_converges w hw0 hw1 blocks extent ids q)
    (fun epsilon he => ⟨0, fun _ _ => eqv_close
      (QuaternionHaarSquareCertificate.haar_of_carrier (HaarCarrierEqv.mul_right _ h)) epsilon he⟩)

theorem numeratorLimit_add (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) (p q : RatPoly) :
    CReal.Equiv (numeratorLimit w hw0 hw1 blocks extent ids (polyAdd p q))
      (CReal.add (numeratorLimit w hw0 hw1 blocks extent ids p) (numeratorLimit w hw0 hw1 blocks extent ids q)) := by
  apply CReal.Equiv_of_ofQ'_limit_close
    (r' := fun K => numerator w blocks extent ids p K + numerator w blocks extent ids q K)
    (numerator_converges w hw0 hw1 blocks extent ids (polyAdd p q))
    (rational_add_converges (numerator_converges w hw0 hw1 blocks extent ids p) (numerator_converges w hw0 hw1 blocks extent ids q))
  intro epsilon he
  refine ⟨0, fun K _ => eqv_close ?_ epsilon he⟩
  unfold numerator
  rw [polyMul_add_left_exact]
  exact quaternionHaar_append blocks _ _

theorem numeratorLimit_smul (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) (c : Q') (p : RatPoly) :
    CReal.Equiv (numeratorLimit w hw0 hw1 blocks extent ids (polySmul c p))
      (CReal.mul (CReal.ofQ' c) (numeratorLimit w hw0 hw1 blocks extent ids p)) := by
  apply CReal.Equiv_of_ofQ'_limit_close
    (r' := fun K => c * numerator w blocks extent ids p K)
    (numerator_converges w hw0 hw1 blocks extent ids (polySmul c p))
    (CReal.convergesTo_const_mul (CReal.ofQ' c) (numerator_converges w hw0 hw1 blocks extent ids p))
  intro epsilon he
  refine ⟨0, fun _ _ => eqv_close ?_ epsilon he⟩
  exact Q'.eqv_trans _ _ _ (haar_of_coeff_eqv blocks (RatPolyCoeffEqv.polyMul_smul_left _ _ _))
    (quaternionHaar_polySmul blocks c _)

/-- Explicit all-later index for positivity after removing the auxiliary weights. -/
theorem numeratorLimit_approx_nonnegative (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p : RatPoly) (P : Certificate (boundaryCompleteSlabLinks extent).length p)
    (epsilon : Q') (he : (0 : Q') < epsilon) (n : Nat)
    (hn : insertedComparisonCutoff w extent ids p epsilon ≤ n) :
    (0 : Q') ≤ (numeratorLimit w hw0 hw1 (boundaryCompleteSlabLinks extent).length extent ids p).approx n + epsilon :=
  Q'.le_trans' _ _ _
    (P.mul (weighted_product_certificate hw0 hw1 _ extent ids hids)).haar_nonnegative
    (numerator_weighted_close hw0 hw1 _ extent ids p epsilon he _
      (Nat.le_trans hn (CReal.self_le_QMhat _ _ n))).2

theorem numeratorLimit_certificate_nonnegative (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p : RatPoly) (P : Certificate (boundaryCompleteSlabLinks extent).length p) :
    CReal.leEv (CReal.ofQ' 0) (numeratorLimit w hw0 hw1 (boundaryCompleteSlabLinks extent).length extent ids p) :=
  fun epsilon he => ⟨insertedComparisonCutoff w extent ids p epsilon,
    numeratorLimit_approx_nonnegative w hw0 hw1 extent ids hids p P epsilon he⟩

theorem numeratorLimit_square_nonnegative (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p) :
    CReal.leEv (CReal.ofQ' 0)
      (numeratorLimit w hw0 hw1 (boundaryCompleteSlabLinks extent).length extent ids (polyMul p p)) :=
  numeratorLimit_certificate_nonnegative w hw0 hw1 extent ids hids _ (.square p hp)

end YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit

#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.insertionTolerance
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.insertionTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.insertionTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.insertedHaar_small
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numerator
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numeratorCutoff
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numerator_increment
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numeratorCauchy
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numeratorLimit
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numerator_converges
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numerator_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.insertedComparisonCutoff
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numerator_weighted_close
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.eqv_close
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numeratorLimit_one
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numeratorLimit_congr
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numeratorLimit_carrier_congr
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numeratorLimit_add
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numeratorLimit_smul
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numeratorLimit_approx_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numeratorLimit_certificate_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit.numeratorLimit_square_nonnegative
