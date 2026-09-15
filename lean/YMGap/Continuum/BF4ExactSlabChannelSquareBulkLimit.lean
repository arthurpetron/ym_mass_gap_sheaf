/-
# Actual finite channel-square sums through ORIGINAL bulk cutoff removal

Every leaf retains its original rational weight and polynomial. Its
amplitude limit is the original lower-action numerator with the observable
and channel on the same links. Recursion on the actual finite square tree
constructs the sum of weighted limiting squares, its numerical Cauchy
modulus, and an explicit bulk/representative convergence cutoff.

The original mixed Gram pin identifies this sum with each finite crossing
packet's bulk limit. No channel completeness, transfer range density,
volume-uniform estimate, physical scaling or continuum/Clay result.
-/

import YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit
import YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit

namespace YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabMixedInterfacePin
open YMGap.Continuum.BF4ExactSlabCrossingPacketBulkLimit
open YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') : a*b ≈ a'*b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem cap_succ_pos {C : Q'} (hC : (0 : Q') ≤ C) : (0 : Q') < C + 1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 C hC) (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

def coefficientLimit (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (p : RatPoly) : CReal :=
  numeratorLimit w hw0 hw1 (boundaryCompleteSlabLinks (centralExtent half)).length (centralExtent half)
    (centralLowerFaceIds half) p

def coefficientLimitCauchy (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (p : RatPoly) : CReal.QCauchy (coefficientLimit w hw0 hw1 half p).approx :=
  BoundedRationalCauchyProduct.representativeCauchy _ (numeratorCauchy w hw0 hw1 _ _ _ p)

/-- Direct evaluation of every leaf against the original bulk action. -/
def energySequence (w : Q') (B half : Nat) (p : RatPoly) : SquareTree → Q'
  | .zero => 0
  | .term v q => v * (lowerMoment w B half (polyMul p q) * lowerMoment w B half (polyMul p q))
  | .add s t => energySequence w B half p s + energySequence w B half p t

/-- The actual finite sum, using the existing CReal sum and product. -/
def energyLimit (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (p : RatPoly) : SquareTree → CReal
  | .zero => CReal.ofQ' 0
  | .term v q => CReal.mul (CReal.ofQ' v)
      (CReal.mul (coefficientLimit w hw0 hw1 half (polyMul p q))
        (coefficientLimit w hw0 hw1 half (polyMul p q)))
  | .add s t => CReal.add (energyLimit w hw0 hw1 half p s) (energyLimit w hw0 hw1 half p t)

def energyLimitCauchy (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (p : RatPoly) : (t : SquareTree) → CReal.QCauchy (energyLimit w hw0 hw1 half p t).approx
  | .zero => rationalCauchy 0
  | .term v q => scalarMulCauchy _ _ (rationalCauchy v)
      (scalarMulCauchy _ _ (coefficientLimitCauchy w hw0 hw1 half (polyMul p q))
        (coefficientLimitCauchy w hw0 hw1 half (polyMul p q)))
  | .add s t => scalarAddCauchy _ _ (energyLimitCauchy w hw0 hw1 half p s) (energyLimitCauchy w hw0 hw1 half p t)

/-- Rescale first for the original weight, then for the bounded square. -/
def leafTolerance (w : Q') (hw0 : (0 : Q') < w) (half : Nat) (p : RatPoly) (v epsilon : Q') : Q' :=
  BoundedRationalCauchyProduct.tolerance (lowerMomentBound w half p + 1)
    (cap_succ_pos (lowerMomentBound_nonnegative w (Q'.le_of_lt hw0) half p))
    (CReal.InnerRegularity.scaleTolerance v epsilon)

theorem leafTolerance_pos (w : Q') (hw0 : (0 : Q') < w) (half : Nat) (p : RatPoly) (v : Q')
    {epsilon : Q'} (he : (0 : Q') < epsilon) : (0 : Q') < leafTolerance w hw0 half p v epsilon :=
  BoundedRationalCauchyProduct.tolerance_pos _ _ (CReal.InnerRegularity.scaleTolerance_pos v epsilon he)

private theorem weighted_square_close (C : Q') (hC : (0 : Q') ≤ C) (v epsilon : Q')
    (hv : (0 : Q') ≤ v) (he : (0 : Q') < epsilon) (a b : Q')
    (ha : Q'.abs a ≤ C) (hb : Q'.abs b ≤ C)
    (h : a ≤ b + BoundedRationalCauchyProduct.tolerance (C+1) (cap_succ_pos hC)
          (CReal.InnerRegularity.scaleTolerance v epsilon) ∧
         b ≤ a + BoundedRationalCauchyProduct.tolerance (C+1) (cap_succ_pos hC)
          (CReal.InnerRegularity.scaleTolerance v epsilon)) :
    v*(a*a) ≤ v*(b*b)+epsilon := by
  let B := C+1
  let delta := CReal.InnerRegularity.scaleTolerance v epsilon
  let tau := BoundedRationalCauchyProduct.tolerance B (cap_succ_pos hC) delta
  have hd := CReal.InnerRegularity.scaleTolerance_pos v epsilon he
  have hsq : a*a ≤ b*b+delta :=
    Q'.le_trans' _ _ _
      (BoundedRationalCauchyProduct.product_close a b a b B tau (Q'.le_of_lt (cap_succ_pos hC))
        (Q'.le_of_lt (BoundedRationalCauchyProduct.tolerance_pos B (cap_succ_pos hC) hd))
        (Q'.le_trans' _ _ _ ha (Q'.add_le_self_of_nonneg C 1 Q'.zero_le_one))
        (Q'.le_trans' _ _ _ hb (Q'.add_le_self_of_nonneg C 1 Q'.zero_le_one)) h h)
      (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _
        (BoundedRationalCauchyProduct.tolerance_budget B (cap_succ_pos hC) delta)))
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hsq hv)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_add_eqv _ _ _))
      (Q'.add_le_add_left _ _ _ (CReal.InnerRegularity.mul_scaleTolerance_le v epsilon hv he)))

def energyApproxCutoff (w : Q') (hw0 : (0 : Q') < w) (half : Nat) (p : RatPoly) : SquareTree → Q' → Nat
  | .zero, _ => 0
  | .term v q, epsilon => numeratorCutoff w (centralExtent half) (centralLowerFaceIds half)
      (polyMul p q) (leafTolerance w hw0 half (polyMul p q) v epsilon)
  | .add s t, epsilon => max (energyApproxCutoff w hw0 half p s (HalfPow.half*epsilon))
      (energyApproxCutoff w hw0 half p t (HalfPow.half*epsilon))

private theorem sum_close (a b c d epsilon : Q')
    (h : a ≤ b + HalfPow.half*epsilon) (h' : c ≤ d + HalfPow.half*epsilon) : a+c ≤ (b+d)+epsilon :=
  Q'.le_trans' _ _ _ (Q'.add_le_add h h') (Q'.le_of_eqv
    (Q'.eqv_trans _ _ _ (Q'.regroup b d (HalfPow.half*epsilon))
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon))))

/-- One computed threshold controls both the original bulk cutoff B and
the approximation index n of the actual finite CReal square sum. -/
theorem energy_approx_close (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat) (p : RatPoly) :
    (t : SquareTree) → t.Nonnegative → (epsilon : Q') → (0 : Q') < epsilon → (B n : Nat) →
    energyApproxCutoff w hw0 half p t epsilon ≤ B → energyApproxCutoff w hw0 half p t epsilon ≤ n →
    energySequence w B half p t ≤ (energyLimit w hw0 hw1 half p t).approx n + epsilon ∧
    (energyLimit w hw0 hw1 half p t).approx n ≤ energySequence w B half p t + epsilon
  | .zero, _, epsilon, he, _, _, _, _ =>
      ⟨Q'.add_le_self_of_nonneg 0 epsilon (Q'.le_of_lt he), Q'.add_le_self_of_nonneg 0 epsilon (Q'.le_of_lt he)⟩
  | .term v q, hv, epsilon, he, B, n, hB, hn => by
      let P := polyMul p q
      have h := numerator_approx_close w hw0 hw1 (boundaryCompleteSlabLinks (centralExtent half)).length
        (centralExtent half) (centralLowerFaceIds half) P (leafTolerance w hw0 half P v epsilon)
        (leafTolerance_pos w hw0 half P v he) B n hB hn
      have ha := lowerMoment_bound w hw0 hw1 B half P
      have hb := lowerMoment_bound w hw0 hw1
        (CReal.QMhat (fun K => lowerMoment w K half P) (numeratorCauchy w hw0 hw1
          (boundaryCompleteSlabLinks (centralExtent half)).length (centralExtent half) (centralLowerFaceIds half) P) n) half P
      exact ⟨weighted_square_close _ (lowerMomentBound_nonnegative w (Q'.le_of_lt hw0) half P) v epsilon hv he _ _ ha hb h,
        weighted_square_close _ (lowerMomentBound_nonnegative w (Q'.le_of_lt hw0) half P) v epsilon hv he _ _ hb ha h.symm⟩
  | .add s t, ht, epsilon, he, B, n, hB, hn => by
      have hs := energy_approx_close w hw0 hw1 half p s ht.1 (HalfPow.half*epsilon)
        (ExpNeg.half_mul_pos epsilon he) B n (Nat.le_trans (Nat.le_max_left _ _) hB) (Nat.le_trans (Nat.le_max_left _ _) hn)
      have ht' := energy_approx_close w hw0 hw1 half p t ht.2 (HalfPow.half*epsilon)
        (ExpNeg.half_mul_pos epsilon he) B n (Nat.le_trans (Nat.le_max_right _ _) hB) (Nat.le_trans (Nat.le_max_right _ _) hn)
      exact ⟨sum_close _ _ _ _ epsilon hs.1 ht'.1, sum_close _ _ _ _ epsilon hs.2 ht'.2⟩

theorem energy_converges (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (p : RatPoly) (t : SquareTree) (ht : t.Nonnegative) :
    CReal.ConvergesTo (fun B => CReal.ofQ' (energySequence w B half p t)) (energyLimit w hw0 hw1 half p t) :=
  fun epsilon he => ⟨energyApproxCutoff w hw0 half p t epsilon, fun B hB =>
    ⟨energyApproxCutoff w hw0 half p t epsilon, fun n hn => energy_approx_close w hw0 hw1 half p t ht epsilon he B n hB hn⟩⟩

private theorem dressed_amplitude (w : Q') (B : Nat) {half : Nat} (e : PlaquetteExpression half) (q : RatPoly) :
    quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (polyMul (dressedLower w B e) q) ≈
      lowerMoment w B half (polyMul (lower e) q) :=
  haar_of_coeff_eqv _ ((RatPolyCoeffEqv.mul_assoc (lower e) _ q).trans
    (((RatPolyCoeffEqv.mul_comm _ q).mul_left (lower e)).trans
      ((RatPolyCoeffEqv.mul_assoc (lower e) q _).symm.trans ((lowerObservable_one w B half).mul_left _))))

theorem dressed_energy_pin (w : Q') (B : Nat) {half : Nat} (e : PlaquetteExpression half) : ∀ t : SquareTree,
    haarSquareSum (boundaryCompleteSlabLinks (centralExtent half)).length (t.multiplyTerm 1 (dressedLower w B e)) ≈
      energySequence w B half (lower e) t
  | .zero => Q'.eqv_refl _
  | .term v q => mul_congr (Q'.one_mul_eqv v)
      (mul_congr (dressed_amplitude w B e q) (dressed_amplitude w B e q))
  | .add s t => Q'.add_eqv_congr' (dressed_energy_pin w B e s) (dressed_energy_pin w B e t)

/-- Independent bulk and crossing cutoffs, retaining the ACTUAL interface tree. -/
theorem mixed_energy_pin (b v : Q') (hv : (0 : Q') ≤ v) (B N : Nat) {half : Nat} (e : PlaquetteExpression half) :
    mixedQuadratic b v B N e ≈ energySequence b B half (lower e) (interfaceExpansion hv N half).tree :=
  Q'.eqv_trans _ _ _ (mixed_interface_pin b v B N e hv)
    (Q'.eqv_trans _ _ _
      (reflectedInterfaceExpansion hv N half (dressedLower b B e)
        (dressedLower_supported b B e) (dressedLower_local b B e)).haar_eq_squareValue
      (dressed_energy_pin b B e _))

/-- The finite sum of limiting ORIGINAL channel squares equals the
pre-existing fixed-crossing-packet bulk limit. No exchange is assumed. -/
theorem packetLimit_eq_energyLimit (b v : Q') (hb0 : (0 : Q') < b) (hb1 : b < (1 : Q'))
    (hv : (0 : Q') ≤ v) (N : Nat) {half : Nat} (e : PlaquetteExpression half) :
    CReal.Equiv (packetLimit b v hb0 hb1 N e)
      (energyLimit b hb0 hb1 half (lower e) (interfaceExpansion hv N half).tree) :=
  CReal.Equiv_of_ofQ'_limit_close (mixed_converges b v hb0 hb1 N e)
    (energy_converges b hb0 hb1 half (lower e) _ (interfaceExpansion hv N half).weightsNonnegative)
    (fun epsilon he => ⟨0, fun B _ => eqv_close (mixed_energy_pin b v hv B N e) epsilon he⟩)

end YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit

#print axioms YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit.coefficientLimit
#print axioms YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit.coefficientLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit.energySequence
#print axioms YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit.energyLimit
#print axioms YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit.energyLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit.leafTolerance
#print axioms YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit.leafTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit.energyApproxCutoff
#print axioms YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit.energy_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit.energy_converges
#print axioms YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit.dressed_energy_pin
#print axioms YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit.mixed_energy_pin
#print axioms YMGap.Continuum.BF4ExactSlabChannelSquareBulkLimit.packetLimit_eq_energyLimit
