/-
# Fixed ORIGINAL square channels survive full bulk cutoff removal

Every retained all-spin channel has a cutoff-independent polynomial and
strictly positive original heat weight. Its amplitude is the ORIGINAL
lower-action numerator with that polynomial insertion, so the existing
coefficient-L1 modulus constructs its bulk limit. The weighted square
remains bounded by the ORIGINAL full reflected numerator after ALL action
cutoffs tend to infinity together.

No lower bound uniform over channels or volume is used. This proves a
family of actual limiting coefficient estimates, not completeness of the
channel family, a zero completed transfer kernel or continuum/Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels
import YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
import YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor
import YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra

namespace YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabOriginalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor
open YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabAllSpinRetainedChannels
open YMGap.Continuum.ReflectedSquareTreeRealizedLeaf
open YMGap.Continuum.ReflectedSquareTreeTwoChannelBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') : a*b ≈ a'*b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem reorder (p L r : RatPoly) :
    RatPolyCoeffEqv (polyMul (polyMul p L) r) (polyMul (polyMul p r) L) :=
  (RatPolyCoeffEqv.mul_assoc p L r).trans
    (((RatPolyCoeffEqv.mul_comm L r).mul_left p).trans (RatPolyCoeffEqv.mul_assoc p r L).symm)

private theorem weighted_square_converges (r : Nat → Q') (A : CReal)
    (B : Q') (hB : (0 : Q') ≤ B) (hr : ∀ n, Q'.abs (r n) ≤ B)
    (hA : ∀ n, Q'.abs (A.approx n) ≤ B)
    (h : CReal.ConvergesTo (fun K => CReal.ofQ' (r K)) A) (v : Q') :
    CReal.ConvergesTo (fun K => CReal.ofQ' (v * (r K * r K)))
      (CReal.mul (CReal.ofQ' v) (CReal.mul A A)) := by
  have hs : CReal.ConvergesTo (fun K => CReal.ofQ' (r K * r K))
      (CReal.mul A A) :=
    CReal.convergesTo_mul (u := fun K => CReal.ofQ' (r K)) (v := fun K => CReal.ofQ' (r K))
      (U := A) (V := A) hB (fun K _ => hr K) hA h h
  exact CReal.convergesTo_const_mul (CReal.ofQ' v) hs

def lowerMoment (w : Q') (K half : Nat) (p : RatPoly) : Q' :=
  numerator w (boundaryCompleteSlabLinks (centralExtent half)).length (centralExtent half)
    (centralLowerFaceIds half) p K

/-- Arbitrary fixed channel, with all ORIGINAL lower heat factors still varying. -/
theorem realized_amplitude (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) {p : RatPoly} {v : Q'}
    (l : RealizedLeaf (interfaceExpansion hw K half).tree p v) (e : PlaquetteExpression half) :
    channelAmplitude w hw K half l.leaf e ≈ lowerMoment w K half (polyMul (lower e) p) :=
  haar_of_coeff_eqv _ ((l.channel_pin.mul_left (dressedLower w K e)).trans
    ((reorder (lower e) _ p).trans ((lowerObservable_one w K half).mul_left _)))

theorem realized_bound (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) {p : RatPoly} {v : Q'}
    (l : RealizedLeaf (interfaceExpansion hw K half).tree p v) (e : PlaquetteExpression half) :
    v * (lowerMoment w K half (polyMul (lower e) p) * lowerMoment w K half (polyMul (lower e) p)) ≤
      originalQuadratic w K e := by
  have ha := realized_amplitude w hw K half l e
  have he := mul_congr l.weight_pin (mul_congr ha ha)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _ (leaf_amplitude_bound w hw K half l.leaf e)
      (Q'.ge_of_eqv (reflected_upper_numerator w K e e)))

def lowerMomentBound (w : Q') (half : Nat) (p : RatPoly) : Q' :=
  polynomialCoefficientL1 p * heatProductBound w (centralExtent half) (centralLowerFaceIds half)

theorem lowerMomentBound_nonnegative (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (p : RatPoly) :
    (0 : Q') ≤ lowerMomentBound w half p :=
  Q'.mul_nonneg _ _ (polynomialCoefficientL1_nonnegative p) (heatProductBound_nonnegative hw _ _)

theorem lowerMoment_bound (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K half : Nat) (p : RatPoly) : Q'.abs (lowerMoment w K half p) ≤ lowerMomentBound w half p :=
  Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _)
    (Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (heatProduct_coefficientL1_bound hw0 hw1 K _ _)
        (polynomialCoefficientL1_nonnegative p)))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}
    (c : (id : Nat) → SpinChannel half id) (e : PlaquetteExpression half)

local notation "P" => polyMul (lower e) (channelPolynomial c (centralFixedFaceIds half))
local notation "W" => channelWeight w c (centralFixedFaceIds half)
local notation "blocks" => List.length (boundaryCompleteSlabLinks (centralExtent half))

def amplitudeSequence (K : Nat) : Q' := lowerMoment w K half P

def amplitudeCauchy : CReal.QCauchy (amplitudeSequence w c e) :=
  numeratorCauchy w hw0 hw1 blocks (centralExtent half) (centralLowerFaceIds half) P

/-- The pre-existing original lower-action numerator limit, not a surrogate coefficient. -/
def amplitudeLimit : CReal :=
  numeratorLimit w hw0 hw1 blocks (centralExtent half) (centralLowerFaceIds half) P

def amplitudeLimitCauchy : CReal.QCauchy (amplitudeLimit w hw0 hw1 c e).approx :=
  BoundedRationalCauchyProduct.representativeCauchy _ (amplitudeCauchy w hw0 hw1 c e)

theorem amplitude_converges :
    CReal.ConvergesTo (fun K => CReal.ofQ' (amplitudeSequence w c e K)) (amplitudeLimit w hw0 hw1 c e) :=
  numerator_converges w hw0 hw1 blocks (centralExtent half) (centralLowerFaceIds half) P

theorem amplitude_approx_close (epsilon : Q') (he : (0 : Q') < epsilon) (K n : Nat)
    (hK : (amplitudeCauchy w hw0 hw1 c e).M epsilon ≤ K)
    (hn : (amplitudeCauchy w hw0 hw1 c e).M epsilon ≤ n) :
    amplitudeSequence w c e K ≤ (amplitudeLimit w hw0 hw1 c e).approx n + epsilon ∧
    (amplitudeLimit w hw0 hw1 c e).approx n ≤ amplitudeSequence w c e K + epsilon :=
  numerator_approx_close w hw0 hw1 blocks (centralExtent half) (centralLowerFaceIds half) P epsilon he K n hK hn

def channelEnergyLimit : CReal :=
  CReal.mul (CReal.ofQ' W) (CReal.mul (amplitudeLimit w hw0 hw1 c e) (amplitudeLimit w hw0 hw1 c e))

/-- Explicit modulus for the actual weighted-square representative as well. -/
def channelEnergyLimitCauchy : CReal.QCauchy (channelEnergyLimit w hw0 hw1 c e).approx :=
  scalarMulCauchy _ _ (rationalCauchy W)
    (scalarMulCauchy _ _ (amplitudeLimitCauchy w hw0 hw1 c e) (amplitudeLimitCauchy w hw0 hw1 c e))

theorem channelEnergy_converges :
    CReal.ConvergesTo (fun K => CReal.ofQ' (W * (amplitudeSequence w c e K * amplitudeSequence w c e K)))
      (channelEnergyLimit w hw0 hw1 c e) :=
  weighted_square_converges (amplitudeSequence w c e) (amplitudeLimit w hw0 hw1 c e)
    (lowerMomentBound w half P) (lowerMomentBound_nonnegative w (Q'.le_of_lt hw0) half P)
    (fun K => lowerMoment_bound w hw0 hw1 K half P)
    (fun n => lowerMoment_bound w hw0 hw1
      (CReal.QMhat (amplitudeSequence w c e) (amplitudeCauchy w hw0 hw1 c e) n) half P)
    (amplitude_converges w hw0 hw1 c e) W

/-- Both the bulk and crossing action cutoffs are the same K and tend to infinity. -/
theorem channelEnergyLimit_bound :
    CReal.leEv (channelEnergyLimit w hw0 hw1 c e)
      (numeratorLimit w hw0 hw1 blocks (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
        (reflectedInsertion e)) := by
  apply CReal.leEv_of_ofQ'_limit_le (channelEnergy_converges w hw0 hw1 c e)
    (numerator_converges w hw0 hw1 blocks (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
      (reflectedInsertion e))
  intro epsilon he
  exact ⟨channelCutoff c, fun K hK => Q'.le_trans' _ _ _
    (realized_bound w (Q'.le_of_lt hw0) K half (interfaceChannel (Q'.le_of_lt hw0) K c hK) e)
    (Q'.add_le_self_of_nonneg _ epsilon (Q'.le_of_lt he))⟩

theorem channelEnergyLimit_nonnegative :
    CReal.leEv (CReal.ofQ' 0) (channelEnergyLimit w hw0 hw1 c e) :=
  CReal.leEv_ofQ'_of_approx_ge (fun _ => Q'.mul_nonneg _ _
    (Q'.le_of_lt (channelWeight_positive w hw0 c _)) (SumOfSquares.q_mul_self_nonneg _))

/-- Nullity of the ORIGINAL full-action form forces every retained limiting energy to vanish. -/
theorem channelEnergyLimit_zero_of_original_null
    (hz : CReal.Equiv
      (numeratorLimit w hw0 hw1 blocks (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
        (reflectedInsertion e)) (CReal.ofQ' 0)) :
    CReal.Equiv (channelEnergyLimit w hw0 hw1 c e) (CReal.ofQ' 0) := by
  have hu := CReal.leEv_trans (channelEnergyLimit_bound w hw0 hw1 c e) (CReal.leEv_of_equiv hz)
  have hl := channelEnergyLimit_nonnegative w hw0 hw1 c e
  intro epsilon he
  obtain ⟨N, hN⟩ := hu epsilon he
  obtain ⟨M, hM⟩ := hl epsilon he
  exact ⟨max N M, fun n hn => ⟨hN n (Nat.le_trans (Nat.le_max_left _ _) hn),
    hM n (Nat.le_trans (Nat.le_max_right _ _) hn)⟩⟩

private theorem weighted_square_zero (A : CReal) (v : Q') (hv : (0 : Q') < v)
    (hz : CReal.Equiv (CReal.mul (CReal.ofQ' v) (CReal.mul A A)) (CReal.ofQ' 0)) :
    CReal.Equiv A (CReal.ofQ' 0) := by
  intro epsilon he
  obtain ⟨N, hN⟩ := hz (v * (epsilon * epsilon)) (Q'.mul_pos hv (Q'.mul_pos he he))
  refine ⟨N, fun n hn => ?_⟩
  have hsq : A.approx n * A.approx n ≤ epsilon * epsilon := by
    apply Q'.le_of_mul_le_mul_left (c := v) _ hv
    have h := (hN n hn).1
    change v * (A.approx n * A.approx n) ≤ 0 + v * (epsilon * epsilon) at h
    rwa [Q'.zero_add'] at h
  have ha := Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq he hsq)
  constructor
  · exact Q'.le_trans' _ _ _ ha.1 (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
  · apply Q'.le_add_of_sub_le
    change 0 + -A.approx n ≤ epsilon
    rw [Q'.zero_add']
    exact ha.2

/-- Every fixed original all-spin channel coefficient vanishes on original OS-null polynomials. -/
theorem amplitudeLimit_zero_of_original_null
    (hz : CReal.Equiv
      (numeratorLimit w hw0 hw1 blocks (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
        (reflectedInsertion e)) (CReal.ofQ' 0)) :
    CReal.Equiv (amplitudeLimit w hw0 hw1 c e) (CReal.ofQ' 0) :=
  weighted_square_zero _ W (channelWeight_positive w hw0 c _)
    (channelEnergyLimit_zero_of_original_null w hw0 hw1 c e hz)

end YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit

#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.lowerMoment
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.realized_amplitude
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.realized_bound
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.lowerMomentBound
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.lowerMomentBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.lowerMoment_bound
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.amplitudeSequence
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.amplitudeCauchy
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.amplitudeLimit
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.amplitudeLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.amplitude_converges
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.amplitude_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.channelEnergyLimit
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.channelEnergyLimitCauchy
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.channelEnergy_converges
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.channelEnergyLimit_bound
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.channelEnergyLimit_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.channelEnergyLimit_zero_of_original_null
#print axioms YMGap.Continuum.BF4ExactSlabRetainedChannelBulkLimit.amplitudeLimit_zero_of_original_null
