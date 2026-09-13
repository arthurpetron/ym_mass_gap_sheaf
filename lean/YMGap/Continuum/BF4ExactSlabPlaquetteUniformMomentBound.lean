/-
# Volume- and nome-independent bounds on ORIGINAL normalized observables

Positive-polynomial certificates are evaluated in the SAME original action.
Normalization cancels the partition exactly; no full-action coefficient or
reciprocal ceiling enters the resulting bounds. For each fixed expression,
the computed cap bounds its ordinary square moment, reflected OS squared
norm, and completed centered squared norm at every odd slab, rational
0<w<1, bulk padding and admissible lag. Means have a square-root-free cap.

These are a priori size bounds, NOT decay estimates. Their constants still
depend on the observable's spins and expression syntax. Existing cutoff
moduli retain their parameter dependence; no padding or continuum modulus,
nontriviality persistence, transfer operator or spectral gap is supplied.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound
import YMGap.Continuum.RateMatchFloor

namespace YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteConnectedCovariance
open YMGap.Continuum.BF4ExactSlabPlaquetteCenteredDensity
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedInner
open YMGap.Continuum.BF4ExactSlabPlaquetteBulkEmbedding
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.GNSQuotient

private theorem minusOne (x : Q') : Q'.eqv ((-1)*x) (-x) :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 x) (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv x))

private theorem neg_smul : ∀ p : RatPoly, RatPolyCoeffEqv (polyNeg p) (polySmul (-1) p)
  | [] => RatPolyCoeffEqv.refl _
  | t :: rest => by
      intro weight
      change Q'.eqv ((-t.2)*weight t.1 + ratWeightedSum weight (polyNeg rest))
        (((-1)*t.2)*weight t.1 + ratWeightedSum weight (polySmul (-1) rest))
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (minusOne t.2))) (neg_smul rest weight)

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat)

theorem expectation_neg (p : RatPoly) : Equiv (expectation w hw0 hw1 half (polyNeg p))
    (CReal.neg (expectation w hw0 hw1 half p)) :=
  (expectation_congr w hw0 hw1 half (neg_smul p)).trans
    ((expectation_smul w hw0 hw1 half (-1) p).trans (SumOfSquares.Equiv_of_approx_eqv (fun _ => minusOne _)))

theorem expectation_cap (c : Q') : Equiv (expectation w hw0 hw1 half (cap c)) (ofQ' c) :=
  (expectation_smul w hw0 hw1 half c polyOne).trans
    ((Pivot2.mul_congr_right (expectation_one w hw0 hw1 half)).trans (CRealAlg.cmul_cone _))

theorem expectation_difference (p q : RatPoly) :
    Equiv (expectation w hw0 hw1 half (polyAdd p (polyNeg q)))
      (CReal.sub (expectation w hw0 hw1 half p) (expectation w hw0 hw1 half q)) :=
  (expectation_add w hw0 hw1 half p (polyNeg q)).trans
    (Pivot2.add_congr (Equiv.refl _) (expectation_neg w hw0 hw1 half q))

/-- The original partition disappears by E(c*1)=c, not by estimating 1/Z. -/
theorem expectation_upper (p : RatPoly) (c : Q')
    (P : Certificate (boundaryCompleteSlabLinks (centralExtent half)).length (polyAdd (cap c) (polyNeg p))) :
    leEv (expectation w hw0 hw1 half p) (ofQ' c) :=
  RateMatchFloor.leEv_of_geRat_sub
    (leEv_trans (expectation_certificate_nonnegative w hw0 hw1 half _ P)
      (leEv_of_equiv ((expectation_difference w hw0 hw1 half (cap c) p).trans
        (CReal.sub_congr_left (expectation_cap w hw0 hw1 half c)))))

variable {half : Nat}

theorem square_moment_bound (e : PlaquetteExpression half) :
    leEv (expectation w hw0 hw1 half (polyMul (lower e) (lower e))) (ofQ' (bound e)) :=
  expectation_upper w hw0 hw1 half _ _ (lowerBound e).certificate

theorem mean_upper (e : PlaquetteExpression half) :
    leEv (mean w hw0 hw1 e) (ofQ' (bound e + 1)) :=
  expectation_upper w hw0 hw1 half _ _ (lowerBound e).linear

theorem neg_mean_upper (e : PlaquetteExpression half) :
    leEv (CReal.neg (mean w hw0 hw1 e)) (ofQ' (bound e + 1)) :=
  leEv_trans (leEv_of_equiv (expectation_neg w hw0 hw1 half (lower e)).symm)
    (expectation_upper w hw0 hw1 half _ _ (lowerBound e).neg.linear)

/-- Bound on the actual reflected OS form, uniform in w and slab geometry. -/
theorem form_bound (e : PlaquetteExpression half) :
    leEv (form w hw0 hw1 e e) (ofQ' (bound e)) :=
  expectation_upper w hw0 hw1 half _ _ (reflectedBound e)

private theorem sub_le_left (a b : CReal) (hb : leEv czero b) : leEv (CReal.sub a b) a := by
  intro epsilon he
  obtain ⟨N, hN⟩ := hb epsilon he
  exact ⟨N, fun n hn => Q'.add_le_add_left _ _ _ (Q'.neg_le_of_zero_le_add
    (Q'.le_trans' _ _ _ (hN n hn) (Q'.le_of_eqv (Q'.add_comm_eqv _ _))))⟩

theorem connected_norm_bound (e : PlaquetteExpression half) :
    leEv (connectedCovariance w hw0 hw1 e e) (ofQ' (bound e)) := by
  have hpin : Equiv (connectedCovariance w hw0 hw1 e e)
      (CReal.sub (form w hw0 hw1 e e) (CReal.mul (mean w hw0 hw1 e) (mean w hw0 hw1 e))) :=
    CReal.sub_congr_left (form_reflected w hw0 hw1 e e).symm
  exact leEv_trans (leEv_of_equiv hpin) (leEv_trans
    (sub_le_left _ _ (SumOfSquares.geRat_sq_nonneg _)) (form_bound w hw0 hw1 e))

theorem completed_centered_norm_bound (e : PlaquetteExpression half) :
    RCle (completedInner w hw0 hw1 (centeredExpression w hw0 hw1 e).val (centeredExpression w hw0 hw1 e).val)
      (Quotient.mk crealSetoid (ofQ' (bound e))) := by
  rw [connectedCovariance_pairing]
  exact connected_norm_bound w hw0 hw1 e

theorem bulk_mean_upper (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) :
    leEv (mean w hw0 hw1 (bulkAtTime padding s e)) (ofQ' (bound e + 1)) := by
  simpa only [bound_bulkAtTime] using mean_upper w hw0 hw1 (bulkAtTime padding s e)

theorem bulk_neg_mean_upper (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) :
    leEv (CReal.neg (mean w hw0 hw1 (bulkAtTime padding s e))) (ofQ' (bound e + 1)) := by
  simpa only [bound_bulkAtTime] using neg_mean_upper w hw0 hw1 (bulkAtTime padding s e)

theorem bulk_norm_bound (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) :
    leEv (bulkCorrelation w hw0 hw1 padding s s e e) (ofQ' (bound e)) := by
  simpa only [bound_bulkAtTime] using connected_norm_bound w hw0 hw1 (bulkAtTime padding s e)

theorem bulk_completed_norm_bound (padding : Nat) (s : Fin (padding+1)) (e : PlaquetteExpression half) :
    RCle (completedInner w hw0 hw1 (bulkPoint w hw0 hw1 padding s e).val (bulkPoint w hw0 hw1 padding s e).val)
      (Quotient.mk crealSetoid (ofQ' (bound e))) := by
  rw [bulkCorrelation_pairing]
  exact bulk_norm_bound w hw0 hw1 padding s e

/-- Uniform size bound at arbitrary two lags. There is NO decaying lag factor. -/
theorem bulk_correlation_square_bound (padding : Nat) (s t : Fin (padding+1)) (e f : PlaquetteExpression half) :
    leEv (CReal.mul (bulkCorrelation w hw0 hw1 padding s t e f) (bulkCorrelation w hw0 hw1 padding s t e f))
      (ofQ' (bound e * bound f)) := by
  refine leEv_trans (connectedCovariance_cauchySchwarz w hw0 hw1 (bulkAtTime padding s e) (bulkAtTime padding t f)) ?_
  refine leEv_trans (leEv_mul_nonneg_left (connectedCovariance_nonnegative w hw0 hw1 (bulkAtTime padding s e))
    (bulk_norm_bound w hw0 hw1 padding t f)) ?_
  refine leEv_trans (leEv_of_equiv (CRealAlg.cmul_comm _ _)) ?_
  refine leEv_trans (leEv_mul_nonneg_left (leEv_ofQ'_of_approx_ge (fun _ => bound_nonnegative f))
    (bulk_norm_bound w hw0 hw1 padding s e)) ?_
  exact leEv_of_equiv (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_comm_eqv _ _))

end YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.expectation_neg
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.expectation_cap
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.expectation_difference
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.expectation_upper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.square_moment_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.mean_upper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.neg_mean_upper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.form_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.connected_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.completed_centered_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.bulk_mean_upper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.bulk_neg_mean_upper
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.bulk_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.bulk_completed_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound.bulk_correlation_square_bound
