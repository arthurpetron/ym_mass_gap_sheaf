/-
# Normalize the ORIGINAL off-center boundary comparison

Exact product-Haar transport identifies the interior integral with the
original smaller slab. The same-cutoff determinant limit therefore equals
the difference of the two original normalized expectations, multiplied by
their two original partitions. Their proved reciprocals cancel those exact
factors: no volume-uniform reciprocal ceiling is assumed or needed.

The final theorem consumes the proved off-center core estimate, retaining
the observable interval, locality and protected-root conditions explicitly.
Its coefficient is independent of the outer padding and time offset. It is
a boundary-sensitivity estimate at the stated coupling, not a spectral gap.
-/

import YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse
import YMGap.Continuum.BF4ExactSlabOffsetBoundaryDecay
import YMGap.Continuum.BF4ExactSlabBoundaryLimitNormalization

namespace YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding
open YMGap.Continuum.BF4ExactSlabOffsetAction
open YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin
open YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse
open YMGap.Continuum.BF4ExactSlabOffsetExteriorSeparation
open YMGap.Continuum.BF4ExactSlabOffsetBoundaryDecay
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabUniformCoreBudget (summedBoundaryBudget)
open YMGap.Continuum.FiniteSizeGeometricSum
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
  (leEv_congr (CRealAlg.cmul_comm _ _) (CRealAlg.cmul_comm _ _)).mp (leEv_mul_nonneg_left hr h)

private theorem abs_mul_right {a r : CReal} (hr : ∀ n, (0 : Q') ≤ r.approx n) :
    leEv (CReal.abs (CReal.mul a r)) (CReal.mul (CReal.abs a) r) := by
  apply order_of_approx
  intro n
  have h := ExpNeg.abs_mul_le (a.approx n) (r.approx n)
  rw [ExpNeg.abs_of_nonneg (hr n)] at h
  exact h

variable (P : Placement) (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

local notation "E" => P.embedding
local notation "Zl" => fullActionLimit w hw0 hw1 (P.half+P.padding)
local notation "Zs" => fullActionLimit w hw0 hw1 P.half
local notation "Ll" => actionReciprocal w hw0 hw1 (P.half+P.padding)
local notation "Ls" => actionReciprocal w hw0 hw1 P.half
local notation "D" => boundaryResponse P w hw0 hw1
local notation "Ns" => numeratorLimit w hw0 hw1 (List.length (boundaryCompleteSlabLinks P.source))
  P.source (slabPhysicalFaceEdges P.source)

theorem comparison_cross (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.source).length p) :
    Equiv (CReal.sub (CReal.mul (expectation w hw0 hw1 (P.half+P.padding) ((E).polynomial p)) Zs) (Ns p))
      (CReal.mul (D ((E).polynomial p)) Ll) := by
  have hpin := (CReal.sub_congr_left (Pivot2.mul_congr_right
    (A := expectation w hw0 hw1 (P.half+P.padding) ((E).polynomial p))
    (interiorPartition_small P w hw0 hw1))).trans
    (CReal.sub_congr_right (interiorLimit_small P w hw0 hw1 p hp))
  exact hpin.symm.trans (normalized_boundary_response P w hw0 hw1 ((E).polynomial p))

def expectationDifference (p : RatPoly) : CReal :=
  CReal.sub (expectation w hw0 hw1 (P.half+P.padding) ((E).polynomial p)) (expectation w hw0 hw1 P.half p)

def expectationDifferenceCauchy (p : RatPoly) : QCauchy (expectationDifference P w hw0 hw1 p).approx :=
  scalarAddCauchy _ _ (expectationCauchy w hw0 hw1 (P.half+P.padding) ((E).polynomial p))
    (scalarNegCauchy _ (expectationCauchy w hw0 hw1 P.half p))

def normalizedBoundaryResponse (p : RatPoly) : CReal := CReal.mul (CReal.mul (D p) Ll) Ls

theorem expectationDifference_formula (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.source).length p) :
    Equiv (expectationDifference P w hw0 hw1 p)
      (normalizedBoundaryResponse P w hw0 hw1 ((E).polynomial p)) := by
  apply Equiv.symm
  refine (Pivot2.mul_congr_left (comparison_cross P w hw0 hw1 p hp).symm).trans ?_
  have hd : Equiv
      (CReal.mul (CReal.sub (CReal.mul (expectation w hw0 hw1 (P.half+P.padding) ((E).polynomial p)) Zs) (Ns p)) Ls)
      (CReal.sub (CReal.mul (CReal.mul (expectation w hw0 hw1 (P.half+P.padding) ((E).polynomial p)) Zs) Ls)
        (CReal.mul (Ns p) Ls)) := SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.sub_mul_eqv _ _ _)
  refine hd.trans (CReal.sub_congr_left ?_)
  exact (CRealAlg.cmul_assoc _ _ _).trans
    ((Pivot2.mul_congr_right (action_mul_reciprocal w hw0 hw1 P.half)).trans (CRealAlg.cmul_cone _))

theorem boundaryResponse_bound (p : RatPoly) (b : Q')
    (h : ∀ K, Q'.abs (boundaryNumerator P w K p) ≤
      b * (fullMoment P w K polyOne * interiorMoment P w K polyOne)) :
    leEv (CReal.abs (D p)) (CReal.mul (ofQ' b) (CReal.mul Zl Zs)) := by
  let d := streamReal _ (boundaryNumeratorCauchy P w hw0 hw1 p)
  let f := streamReal _ (numeratorCauchy w hw0 hw1
    (boundaryCompleteSlabLinks P.target).length P.target (slabPhysicalFaceEdges P.target) polyOne)
  let i := streamReal _ (numeratorCauchy w hw0 hw1
    (boundaryCompleteSlabLinks P.target).length P.target (interiorIds P) polyOne)
  have hd : Equiv d (D p) := streamReal_eq_limit _ _
  have hf : Equiv f Zl := (streamReal_eq_limit _ _).trans (numeratorLimit_one w hw0 hw1 _ _ _)
  have hi : Equiv i Zs := (streamReal_eq_limit _ _).trans (interiorPartition_small P w hw0 hw1)
  have hraw : leEv (CReal.abs d) (CReal.mul (ofQ' b) (CReal.mul f i)) := order_of_approx h
  exact (leEv_congr (abs_equiv_congr hd)
    (Pivot2.mul_congr_right ((Pivot2.mul_congr_left hf).trans (Pivot2.mul_congr_right hi)))).mp hraw

theorem normalizedBoundaryResponse_bound (p : RatPoly) (b : Q')
    (h : ∀ K, Q'.abs (boundaryNumerator P w K p) ≤
      b * (fullMoment P w K polyOne * interiorMoment P w K polyOne)) :
    leEv (CReal.abs (normalizedBoundaryResponse P w hw0 hw1 p)) (ofQ' b) := by
  have hl := reciprocal_nonnegative w hw0 hw1 (P.half+P.padding)
  have hs := reciprocal_nonnegative w hw0 hw1 P.half
  have habs := leEv_trans
    (abs_mul_right (a := CReal.mul (D p) Ll) (fun n => Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 P.half n)))
    (mul_right_mono hs (abs_mul_right (a := D p)
      (fun n => Q'.le_of_lt (actionReciprocal_approx_pos w hw0 hw1 (P.half+P.padding) n))))
  exact leEv_trans habs (leEv_trans
    (mul_right_mono hs (mul_right_mono hl (boundaryResponse_bound P w hw0 hw1 p b h)))
    (leEv_of_equiv (BF4ExactSlabBoundaryLimitNormalization.normalizedPartition_cancel
      w hw0 hw1 P.half P.padding b)))

theorem expectationDifference_bound (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.source).length p) (b : Q')
    (h : ∀ K, Q'.abs (boundaryNumerator P w K ((E).polynomial p)) ≤
      b * (fullMoment P w K polyOne * interiorMoment P w K polyOne)) :
    leEv (CReal.abs (expectationDifference P w hw0 hw1 p)) (ofQ' b) :=
  leEv_trans (leEv_of_equiv (abs_equiv_congr (expectationDifference_formula P w hw0 hw1 p hp)))
    (normalizedBoundaryResponse_bound P w hw0 hw1 _ b h)

theorem boundaryNumerator_prefix (K : Nat) {p q : RatPoly}
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.target).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.target).length q)
    (he : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks P.target).length p q) :
    Q'.eqv (boundaryNumerator P w K p) (boundaryNumerator P w K q) := by
  have hf : Q'.eqv (fullMoment P w K p) (fullMoment P w K q) :=
    quaternionHaar_prefixPolynomialEqv _ (he.mul (.refl _ _))
      (supported_polyMul hp (fullHeatProduct_supported w K (P.half+P.padding)))
      (supported_polyMul hq (fullHeatProduct_supported w K (P.half+P.padding)))
  have hi := interiorMoment_prefix P w K he hp hq
  exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ hf)
    (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ hi))

/-- The estimate may be proved for a supported literal target holonomy. -/
theorem expectationDifference_bound_of_prefix (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.source).length p) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.target).length q)
    (he : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks P.target).length ((E).polynomial p) q)
    (b : Q') (h : ∀ K, Q'.abs (boundaryNumerator P w K q) ≤
      b * (fullMoment P w K polyOne * interiorMoment P w K polyOne)) :
    leEv (CReal.abs (expectationDifference P w hw0 hw1 p)) (ofQ' b) :=
  expectationDifference_bound P w hw0 hw1 p hp b (fun K =>
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr
      (boundaryNumerator_prefix P w K ((E).polynomial_supported p) hq he))) (h K))

/-- Actual core decay and actual partition cancellation, for every allowed placement. -/
theorem protected_expectationDifference_bound
    (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
    (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (margin : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.source).length p) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.target).length q)
    (he : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks P.target).length ((E).polynomial p) q)
    (c : Q') (hc : Interval (boundaryCompleteSlabLinks P.target).length q c)
    (links : List Z4Link) (probe : ProbeCarrier links) (hl : LinkLocal P.target links q)
    (hr : ProtectedRoot P margin probe.animal.root) :
    leEv (CReal.abs (expectationDifference P w hw0 hw1 p))
      (ofQ' ((c+c)*summedBoundaryBudget probe w hd hs (margin+1-probe.animal.support.length))) :=
  expectationDifference_bound_of_prefix P w hw0 hw1 p hp q hq he _ (fun K =>
    protected_boundary_bound (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall hd hs P K margin q c hc links probe hl hr)

end YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison

#print axioms YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison.comparison_cross
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison.expectationDifference
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison.expectationDifferenceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison.normalizedBoundaryResponse
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison.expectationDifference_formula
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison.boundaryResponse_bound
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison.normalizedBoundaryResponse_bound
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison.expectationDifference_bound
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison.boundaryNumerator_prefix
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison.expectationDifference_bound_of_prefix
#print axioms YMGap.Continuum.BF4ExactSlabOffsetExpectationComparison.protected_expectationDifference_bound
