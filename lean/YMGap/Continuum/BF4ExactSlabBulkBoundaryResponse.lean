/-
# The exact ORIGINAL bulk boundary-response numerator, with its cutoff limit

Write F(p) for the full target-action moment, I(p) for the embedded-interior
moment on the SAME target Haar carrier, and W for the exterior heat product.
At every representation cutoff the determinant

    D(p) = F(p) I(1) - I(p) F(1)
         = I(p W) I(1) - I(p) I(W)

is proved exactly. No independence, positivity of a character truncation,
or reciprocal of I(1) is used. The actual same-cutoff determinant stream
has a returned QCauchy modulus and a CReal limit. At that limit,

    E_full(p) I(1) - I(p) = D(p) / Z_full,

using the existing ORIGINAL partition reciprocal. This names the actual
boundary response rather than assuming it small. All statements retain the
nome, source extent, padding and insertion as arguments. No decay as padding
increases, comparison with smaller-carrier Haar, time transfer, uniform gap,
or thermodynamic/continuum limit is asserted.
-/

import YMGap.Continuum.BF4ExactSlabBulkActionDressing

namespace YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-- A non-reindexed representative used only to compose the supplied moduli.
The Type-level QCauchy input is retained throughout the construction. -/
private def streamReal (r : Nat → Q') (c : QCauchy r) : CReal where
  approx := r
  cauchy := fun epsilon he => ⟨c.M epsilon, c.bound epsilon he⟩

private theorem streamReal_eq_limit (r : Nat → Q') (c : QCauchy r) :
    Equiv (streamReal r c) (ofQ'CauchySeq r c) := by
  intro epsilon he
  exact ⟨c.M epsilon, fun n hn => c.bound epsilon he n _ hn
    (Nat.le_trans hn (self_le_QMhat r c n))⟩

private theorem rational_mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

def interiorSequence (w : Q') (half padding : Nat) (p : RatPoly) (K : Nat) : Q' :=
  numerator w (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
    (centralExtent (half+padding)) (interiorIds half padding) p K

def boundaryNumerator (w : Q') (half padding : Nat) (p : RatPoly) (K : Nat) : Q' :=
  fullMoment w K half padding p * interiorSequence w half padding polyOne K +
    -(interiorSequence w half padding p K * fullMoment w K half padding polyOne)

/-- Exact, unnormalized covariance of the exterior weight and p under the
interior-weighted Haar functional. Shared links have not been integrated away. -/
theorem boundaryNumerator_covariance (w : Q') (half padding : Nat) (p : RatPoly) (K : Nat) :
    boundaryNumerator w half padding p K ≈
      interiorMoment w K half padding (polyMul p (exteriorHeat w K half padding)) *
          interiorMoment w K half padding polyOne +
        -(interiorMoment w K half padding p * interiorMoment w K half padding (exteriorHeat w K half padding)) :=
  Q'.add_eqv_congr'
    (rational_mul_congr (fullMoment_insertExterior w K half padding p) (interiorMoment_numerator w K half padding polyOne))
    (Q'.neg_eqv_congr _ _ (rational_mul_congr (interiorMoment_numerator w K half padding p) (fullMoment_exterior w K half padding)))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half padding : Nat)

private def fullStreamCauchy (p : RatPoly) : QCauchy (fun K => fullMoment w K half padding p) :=
  numeratorCauchy w hw0 hw1 _ _ _ p

private def interiorStreamCauchy (p : RatPoly) : QCauchy (interiorSequence w half padding p) :=
  numeratorCauchy w hw0 hw1 _ _ _ p

private def rawFull (p : RatPoly) : CReal := streamReal _ (fullStreamCauchy w hw0 hw1 half padding p)
private def rawInterior (p : RatPoly) : CReal := streamReal _ (interiorStreamCauchy w hw0 hw1 half padding p)

def fullMomentLimit (p : RatPoly) : CReal :=
  numeratorLimit w hw0 hw1 (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
    (centralExtent (half+padding)) (slabPhysicalFaceEdges (centralExtent (half+padding))) p

def interiorMomentLimit (p : RatPoly) : CReal :=
  numeratorLimit w hw0 hw1 (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
    (centralExtent (half+padding)) (interiorIds half padding) p

local notation "F" => rawFull w hw0 hw1 half padding
local notation "I" => rawInterior w hw0 hw1 half padding
local notation "FL" => fullMomentLimit w hw0 hw1 half padding
local notation "IL" => interiorMomentLimit w hw0 hw1 half padding

/-- Modulus for the ACTUAL determinant with the same cutoff in all four
moments. Arithmetic uses explicit tail ceilings computed from input moduli. -/
def boundaryNumeratorCauchy (p : RatPoly) : QCauchy (boundaryNumerator w half padding p) :=
  scalarAddCauchy (CReal.mul (F p) (I polyOne)) (CReal.neg (CReal.mul (I p) (F polyOne)))
    (scalarMulCauchy _ _ (fullStreamCauchy w hw0 hw1 half padding p) (interiorStreamCauchy w hw0 hw1 half padding polyOne))
    (scalarNegCauchy _ (scalarMulCauchy _ _ (interiorStreamCauchy w hw0 hw1 half padding p) (fullStreamCauchy w hw0 hw1 half padding polyOne)))

def boundaryResponse (p : RatPoly) : CReal :=
  ofQ'CauchySeq _ (boundaryNumeratorCauchy w hw0 hw1 half padding p)

def boundaryResponseCauchy (p : RatPoly) : QCauchy (boundaryResponse w hw0 hw1 half padding p).approx :=
  BoundedRationalCauchyProduct.representativeCauchy _ (boundaryNumeratorCauchy w hw0 hw1 half padding p)

def boundaryCutoff (p : RatPoly) (epsilon : Q') : Nat :=
  (boundaryNumeratorCauchy w hw0 hw1 half padding p).M epsilon

/-- Both the original cutoff and representative index are explicitly bounded. -/
theorem boundaryResponse_approx_close (p : RatPoly) (epsilon : Q') (he : (0 : Q') < epsilon)
    (K n : Nat) (hK : boundaryCutoff w hw0 hw1 half padding p epsilon ≤ K)
    (hn : boundaryCutoff w hw0 hw1 half padding p epsilon ≤ n) :
    boundaryNumerator w half padding p K ≤ (boundaryResponse w hw0 hw1 half padding p).approx n + epsilon ∧
    (boundaryResponse w hw0 hw1 half padding p).approx n ≤ boundaryNumerator w half padding p K + epsilon :=
  (boundaryNumeratorCauchy w hw0 hw1 half padding p).bound epsilon he K _ hK
    (Nat.le_trans hn (self_le_QMhat _ _ n))

theorem boundaryResponse_converges (p : RatPoly) :
    ConvergesTo (fun K => ofQ' (boundaryNumerator w half padding p K)) (boundaryResponse w hw0 hw1 half padding p) :=
  convergesTo_ofQ'CauchySeq _ _

/-- The same-cutoff determinant limit is pinned to the four original moment
limits, not to four unrelated or substituted probability laws. -/
theorem boundaryResponse_formula (p : RatPoly) :
    Equiv (boundaryResponse w hw0 hw1 half padding p)
      (CReal.sub (CReal.mul (FL p) (IL polyOne)) (CReal.mul (IL p) (FL polyOne))) := by
  have hF (q : RatPoly) : Equiv (F q) (FL q) := streamReal_eq_limit _ _
  have hI (q : RatPoly) : Equiv (I q) (IL q) := streamReal_eq_limit _ _
  have hraw : Equiv (CReal.sub (CReal.mul (F p) (I polyOne)) (CReal.mul (I p) (F polyOne)))
      (boundaryResponse w hw0 hw1 half padding p) := streamReal_eq_limit _ _
  exact hraw.symm.trans
    ((CReal.sub_congr_left ((Pivot2.mul_congr_left (hF p)).trans (Pivot2.mul_congr_right (hI polyOne)))).trans
      (CReal.sub_congr_right ((Pivot2.mul_congr_left (hI p)).trans (Pivot2.mul_congr_right (hF polyOne)))))

private theorem mul_swap_right (a b c : CReal) :
    Equiv (CReal.mul (CReal.mul a b) c) (CReal.mul (CReal.mul a c) b) :=
  (CRealAlg.cmul_assoc _ _ _).trans
    ((Pivot2.mul_congr_right (CRealAlg.cmul_comm _ _)).trans (CRealAlg.cmul_assoc _ _ _).symm)

/-- Normalized full-action comparison, without dividing by the interior
partition. The sole reciprocal is the already proved ORIGINAL full one. -/
theorem normalized_boundary_response (p : RatPoly) :
    Equiv (CReal.sub (CReal.mul (expectation w hw0 hw1 (half+padding) p) (IL polyOne)) (IL p))
      (CReal.mul (boundaryResponse w hw0 hw1 half padding p) (actionReciprocal w hw0 hw1 (half+padding))) := by
  apply Equiv.symm
  refine (Pivot2.mul_congr_left (boundaryResponse_formula w hw0 hw1 half padding p)).trans ?_
  have hdistrib : Equiv
      (CReal.mul (CReal.sub (CReal.mul (FL p) (IL polyOne)) (CReal.mul (IL p) (FL polyOne)))
        (actionReciprocal w hw0 hw1 (half+padding)))
      (CReal.sub (CReal.mul (CReal.mul (FL p) (IL polyOne)) (actionReciprocal w hw0 hw1 (half+padding)))
        (CReal.mul (CReal.mul (IL p) (FL polyOne)) (actionReciprocal w hw0 hw1 (half+padding)))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.sub_mul_eqv _ _ _)
  refine hdistrib.trans ((CReal.sub_congr_left (mul_swap_right _ _ _)).trans (CReal.sub_congr_right ?_))
  exact (CRealAlg.cmul_assoc _ _ _).trans
    ((Pivot2.mul_congr_right (expectation_one w hw0 hw1 (half+padding))).trans (CRealAlg.cmul_cone _))

theorem boundaryResponse_one : Equiv (boundaryResponse w hw0 hw1 half padding polyOne) czero :=
  (boundaryResponse_formula w hw0 hw1 half padding polyOne).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv _ _))) (Q'.add_neg_self_eqv _)))

end YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse

#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.interiorSequence
#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.boundaryNumerator
#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.boundaryNumerator_covariance
#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.fullMomentLimit
#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.interiorMomentLimit
#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.boundaryNumeratorCauchy
#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.boundaryResponse
#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.boundaryResponseCauchy
#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.boundaryCutoff
#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.boundaryResponse_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.boundaryResponse_converges
#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.boundaryResponse_formula
#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.normalized_boundary_response
#print axioms YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse.boundaryResponse_one
