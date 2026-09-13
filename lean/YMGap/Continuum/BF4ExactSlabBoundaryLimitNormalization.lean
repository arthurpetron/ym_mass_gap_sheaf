/-
# Cancel the ORIGINAL partition factors after cutoff removal

A bound |D_K(p)| <= b * F_K(1) * I_K(1), valid at every common
representation cutoff, passes to the existing original moment limits.
The two proved original partition reciprocals cancel these SAME factors,
leaving |E_large(embed p)-E_small(p)| <= b for supported source p.

The proof uses the sound eventual order, not the one-slack CReal order.
All source streams already carry explicit QCauchy moduli. No volume-uniform
reciprocal ceiling, replacement normalization, or new analytic premise is
required. This transport lemma consumes a finite bound; it does not assert
that an arbitrary supplied b shrinks or construct a thermodynamic limit.
-/

import YMGap.Continuum.BF4ExactSlabBulkExpectationComparison
import YMGap.Continuum.FCNormBoundLimit

namespace YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
open YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin
open YMGap.Continuum.BF4ExactSlabBulkExpectationComparison
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def streamReal (r : Nat → Q') (c : QCauchy r) : CReal where
  approx := r
  cauchy := fun epsilon he => ⟨c.M epsilon, c.bound epsilon he⟩

private theorem streamReal_eq_limit (r : Nat → Q') (c : QCauchy r) :
    Equiv (streamReal r c) (ofQ'CauchySeq r c) := by
  intro epsilon he
  exact ⟨c.M epsilon, fun n hn => c.bound epsilon he n _ hn
    (Nat.le_trans hn (self_le_QMhat r c n))⟩

private theorem order_of_approx {a b : CReal} (h : ∀ n, a.approx n ≤ b.approx n) : leEv a b := by
  intro epsilon he
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _ (h n)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

private theorem mul_right_mono {a b r : CReal} (hr : leEv czero r) (h : leEv a b) :
    leEv (CReal.mul a r) (CReal.mul b r) :=
  (leEv_congr (CRealAlg.cmul_comm _ _) (CRealAlg.cmul_comm _ _)).mp
    (leEv_mul_nonneg_left hr h)

private theorem abs_mul_right {a r : CReal} (hr : ∀ n, (0 : Q') ≤ r.approx n) :
    leEv (CReal.abs (CReal.mul a r)) (CReal.mul (CReal.abs a) r) := by
  apply order_of_approx
  intro n
  have h := ExpNeg.abs_mul_le (a.approx n) (r.approx n)
  rw [ExpNeg.abs_of_nonneg (hr n)] at h
  exact h

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half padding : Nat)

local notation "Zl" => fullActionLimit w hw0 hw1 (half+padding)
local notation "Zs" => fullActionLimit w hw0 hw1 half
local notation "Ll" => actionReciprocal w hw0 hw1 (half+padding)
local notation "Ls" => actionReciprocal w hw0 hw1 half
local notation "D" => boundaryResponse w hw0 hw1 half padding

/-- The common-cutoff cleared estimate reaches the SAME original partition limits. -/
theorem boundaryResponse_bound (p : RatPoly) (b : Q')
    (h : ∀ K, Q'.abs (boundaryNumerator w half padding p K) ≤
      b * (fullMoment w K half padding polyOne * interiorSequence w half padding polyOne K)) :
    leEv (CReal.abs (D p)) (CReal.mul (ofQ' b) (CReal.mul Zl Zs)) := by
  let d := streamReal _ (boundaryNumeratorCauchy w hw0 hw1 half padding p)
  let f := streamReal _ (numeratorCauchy w hw0 hw1
    (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
    (centralExtent (half+padding)) (slabPhysicalFaceEdges (centralExtent (half+padding))) polyOne)
  let i := streamReal _ (numeratorCauchy w hw0 hw1
    (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
    (centralExtent (half+padding)) (interiorIds half padding) polyOne)
  have hd : Equiv d (D p) := streamReal_eq_limit _ _
  have hf : Equiv f Zl := (streamReal_eq_limit _ _).trans (numeratorLimit_one w hw0 hw1 _ _ _)
  have hi : Equiv i Zs := (streamReal_eq_limit _ _).trans (interiorPartition_small w hw0 hw1 half padding)
  have hraw : leEv (CReal.abs d) (CReal.mul (ofQ' b) (CReal.mul f i)) := order_of_approx h
  exact (leEv_congr (abs_equiv_congr hd)
    (Pivot2.mul_congr_right ((Pivot2.mul_congr_left hf).trans (Pivot2.mul_congr_right hi)))).mp hraw

/-- Both original reciprocals are retained, with their existing explicit moduli. -/
def normalizedBoundaryResponse (p : RatPoly) : CReal := CReal.mul (CReal.mul (D p) Ll) Ls

/-- Exact cancellation: no extent-dependent reciprocal bound enters the answer. -/
theorem normalizedPartition_cancel (b : Q') :
    Equiv (CReal.mul (CReal.mul (CReal.mul (ofQ' b) (CReal.mul Zl Zs)) Ll) Ls) (ofQ' b) := by
  have hshuffle : Equiv
      (CReal.mul (CReal.mul (CReal.mul (ofQ' b) (CReal.mul Zl Zs)) Ll) Ls)
      (CReal.mul (ofQ' b) (CReal.mul (CReal.mul Zl Ll) (CReal.mul Zs Ls))) := by
    apply SumOfSquares.Equiv_of_approx_eqv
    intro n
    exact RingNormaliser.poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (.var 4))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 4)))) (by decide)
      (fun k => if k = 0 then b else if k = 1 then (Zl).approx n else if k = 2 then (Zs).approx n
        else if k = 3 then (Ll).approx n else (Ls).approx n)
  exact hshuffle.trans ((Pivot2.mul_congr_right
    ((Pivot2.mul_congr_left (action_mul_reciprocal w hw0 hw1 (half+padding))).trans
      ((Pivot2.mul_congr_right (action_mul_reciprocal w hw0 hw1 half)).trans
        (CRealAlg.cmul_cone cone)))).trans (CRealAlg.cmul_cone _))

theorem normalizedBoundaryResponse_bound (p : RatPoly) (b : Q')
    (h : ∀ K, Q'.abs (boundaryNumerator w half padding p K) ≤
      b * (fullMoment w K half padding polyOne * interiorSequence w half padding polyOne K)) :
    leEv (CReal.abs (normalizedBoundaryResponse w hw0 hw1 half padding p)) (ofQ' b) := by
  have hl := reciprocal_nonnegative w hw0 hw1 (half+padding)
  have hs := reciprocal_nonnegative w hw0 hw1 half
  have habs := leEv_trans
    (abs_mul_right (a := CReal.mul (D p) Ll) (fun n => Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 half n)))
    (mul_right_mono hs (abs_mul_right (a := D p)
      (fun n => Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 (half+padding) n))))
  exact leEv_trans habs (leEv_trans
    (mul_right_mono hs (mul_right_mono hl (boundaryResponse_bound w hw0 hw1 half padding p b h)))
    (leEv_of_equiv (normalizedPartition_cancel w hw0 hw1 half padding b)))

/-- The bound is on the existing normalized inter-slab expectation difference. -/
theorem expectationDifference_bound (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p) (b : Q')
    (h : ∀ K, Q'.abs (boundaryNumerator w half padding ((slabEmbedding half padding).polynomial p) K) ≤
      b * (fullMoment w K half padding polyOne * interiorSequence w half padding polyOne K)) :
    leEv (CReal.abs (expectationDifference w hw0 hw1 half padding p)) (ofQ' b) :=
  leEv_trans (leEv_of_equiv (abs_equiv_congr (expectationDifference_formula w hw0 hw1 half padding p hp)))
    (normalizedBoundaryResponse_bound w hw0 hw1 half padding _ b h)

/-- Supported quaternion-prefix equality preserves the ORIGINAL finite determinant. -/
theorem boundaryNumerator_prefix (K : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length q)
    (he : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p q) :
    Q'.eqv (boundaryNumerator w half padding p K) (boundaryNumerator w half padding q K) := by
  have hf : Q'.eqv (fullMoment w K half padding p) (fullMoment w K half padding q) :=
    quaternionHaar_prefixPolynomialEqv _ (he.mul (.refl _ _))
      (supported_polyMul hp (fullHeatProduct_supported w K (half+padding)))
      (supported_polyMul hq (fullHeatProduct_supported w K (half+padding)))
  have hi : Q'.eqv (interiorSequence w half padding p K) (interiorSequence w half padding q K) :=
    Q'.eqv_trans _ _ _ (interiorMoment_numerator w K half padding p)
      (Q'.eqv_trans _ _ _ (interiorMoment_prefix he hp hq)
        (Q'.eqv_symm (interiorMoment_numerator w K half padding q)))
  exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ hf)
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ hi))

/-- The finite estimate may use the literal target holonomy, pinned to the
actual image of the source observable rather than assumed syntactically equal. -/
theorem expectationDifference_bound_of_prefix (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p)
    (q : RatPoly)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length q)
    (he : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
      ((slabEmbedding half padding).polynomial p) q) (b : Q')
    (h : ∀ K, Q'.abs (boundaryNumerator w half padding q K) ≤
      b * (fullMoment w K half padding polyOne * interiorSequence w half padding polyOne K)) :
    leEv (CReal.abs (expectationDifference w hw0 hw1 half padding p)) (ofQ' b) :=
  expectationDifference_bound w hw0 hw1 half padding p hp b (fun K =>
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
      (boundaryNumerator_prefix w half padding K ((slabEmbedding half padding).polynomial_supported p) hq he))) (h K))

end YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization

#print axioms YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization.boundaryResponse_bound
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization.normalizedBoundaryResponse
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization.normalizedPartition_cancel
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization.normalizedBoundaryResponse_bound
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization.expectationDifference_bound
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization.boundaryNumerator_prefix
#print axioms YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization.expectationDifference_bound_of_prefix
