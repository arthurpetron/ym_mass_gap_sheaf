/-
# The original off-center boundary determinant has an explicit cutoff limit

All four moments use the same representation cutoff and actual target Haar
carrier. Their existing moduli construct the determinant modulus and limit.
The exact response formula retains the original interior action; its source
partition identification is consumed only when the insertion is supported.
No boundary-decay premise, time invariance or transfer operator is assumed.
-/

import YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin

namespace YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding
open YMGap.Continuum.BF4ExactSlabOffsetAction
open YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

private def streamReal (r : Nat → Q') (c : QCauchy r) : CReal where
  approx := r
  cauchy := fun epsilon he => ⟨c.M epsilon, c.bound epsilon he⟩

private theorem streamReal_eq_limit (r : Nat → Q') (c : QCauchy r) :
    Equiv (streamReal r c) (ofQ'CauchySeq r c) := by
  intro epsilon he
  exact ⟨c.M epsilon, fun n hn => c.bound epsilon he n _ hn
    (Nat.le_trans hn (self_le_QMhat r c n))⟩

variable (P : Placement) (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

private def fullStreamCauchy (p : RatPoly) : QCauchy (fun K => fullMoment P w K p) :=
  numeratorCauchy w hw0 hw1 _ _ _ p

private def interiorStreamCauchy (p : RatPoly) : QCauchy (fun K => interiorMoment P w K p) :=
  numeratorCauchy w hw0 hw1 _ _ _ p

private def rawFull (p : RatPoly) : CReal := streamReal _ (fullStreamCauchy P w hw0 hw1 p)
private def rawInterior (p : RatPoly) : CReal := streamReal _ (interiorStreamCauchy P w hw0 hw1 p)

def fullLimit (p : RatPoly) : CReal :=
  numeratorLimit w hw0 hw1 (boundaryCompleteSlabLinks P.target).length
    P.target (slabPhysicalFaceEdges P.target) p

local notation "F" => rawFull P w hw0 hw1
local notation "I" => rawInterior P w hw0 hw1
local notation "FL" => fullLimit P w hw0 hw1
local notation "IL" => interiorLimit P w hw0 hw1

/-- Computed modulus for the original same-cutoff determinant stream. -/
def boundaryNumeratorCauchy (p : RatPoly) : QCauchy (fun K => boundaryNumerator P w K p) :=
  scalarAddCauchy (CReal.mul (F p) (I polyOne)) (CReal.neg (CReal.mul (I p) (F polyOne)))
    (scalarMulCauchy _ _ (fullStreamCauchy P w hw0 hw1 p) (interiorStreamCauchy P w hw0 hw1 polyOne))
    (scalarNegCauchy _ (scalarMulCauchy _ _ (interiorStreamCauchy P w hw0 hw1 p) (fullStreamCauchy P w hw0 hw1 polyOne)))

def boundaryResponse (p : RatPoly) : CReal := ofQ'CauchySeq _ (boundaryNumeratorCauchy P w hw0 hw1 p)

def boundaryResponseCauchy (p : RatPoly) : QCauchy (boundaryResponse P w hw0 hw1 p).approx :=
  BoundedRationalCauchyProduct.representativeCauchy _ (boundaryNumeratorCauchy P w hw0 hw1 p)

def boundaryCutoff (p : RatPoly) (epsilon : Q') : Nat := (boundaryNumeratorCauchy P w hw0 hw1 p).M epsilon

theorem boundaryResponse_approx_close (p : RatPoly) (epsilon : Q') (he : (0 : Q') < epsilon)
    (K n : Nat) (hK : boundaryCutoff P w hw0 hw1 p epsilon ≤ K)
    (hn : boundaryCutoff P w hw0 hw1 p epsilon ≤ n) :
    boundaryNumerator P w K p ≤ (boundaryResponse P w hw0 hw1 p).approx n + epsilon ∧
    (boundaryResponse P w hw0 hw1 p).approx n ≤ boundaryNumerator P w K p + epsilon :=
  (boundaryNumeratorCauchy P w hw0 hw1 p).bound epsilon he K _ hK
    (Nat.le_trans hn (self_le_QMhat _ _ n))

theorem boundaryResponse_converges (p : RatPoly) :
    ConvergesTo (fun K => ofQ' (boundaryNumerator P w K p)) (boundaryResponse P w hw0 hw1 p) :=
  convergesTo_ofQ'CauchySeq _ _

theorem boundaryResponse_formula (p : RatPoly) :
    Equiv (boundaryResponse P w hw0 hw1 p)
      (CReal.sub (CReal.mul (FL p) (IL polyOne)) (CReal.mul (IL p) (FL polyOne))) := by
  have hF (q : RatPoly) : Equiv (F q) (FL q) := streamReal_eq_limit _ _
  have hI (q : RatPoly) : Equiv (I q) (IL q) := streamReal_eq_limit _ _
  have hraw : Equiv (CReal.sub (CReal.mul (F p) (I polyOne)) (CReal.mul (I p) (F polyOne)))
      (boundaryResponse P w hw0 hw1 p) := streamReal_eq_limit _ _
  exact hraw.symm.trans
    ((CReal.sub_congr_left ((Pivot2.mul_congr_left (hF p)).trans (Pivot2.mul_congr_right (hI polyOne)))).trans
      (CReal.sub_congr_right ((Pivot2.mul_congr_left (hI p)).trans (Pivot2.mul_congr_right (hF polyOne)))))

private theorem mul_swap_right (a b c : CReal) :
    Equiv (CReal.mul (CReal.mul a b) c) (CReal.mul (CReal.mul a c) b) :=
  (CRealAlg.cmul_assoc _ _ _).trans
    ((Pivot2.mul_congr_right (CRealAlg.cmul_comm _ _)).trans (CRealAlg.cmul_assoc _ _ _).symm)

/-- The sole denominator is the existing original full partition. -/
theorem normalized_boundary_response (p : RatPoly) :
    Equiv (CReal.sub (CReal.mul (expectation w hw0 hw1 (P.half+P.padding) p) (IL polyOne)) (IL p))
      (CReal.mul (boundaryResponse P w hw0 hw1 p) (actionReciprocal w hw0 hw1 (P.half+P.padding))) := by
  apply Equiv.symm
  refine (Pivot2.mul_congr_left (boundaryResponse_formula P w hw0 hw1 p)).trans ?_
  have hdistrib : Equiv
      (CReal.mul (CReal.sub (CReal.mul (FL p) (IL polyOne)) (CReal.mul (IL p) (FL polyOne)))
        (actionReciprocal w hw0 hw1 (P.half+P.padding)))
      (CReal.sub (CReal.mul (CReal.mul (FL p) (IL polyOne)) (actionReciprocal w hw0 hw1 (P.half+P.padding)))
        (CReal.mul (CReal.mul (IL p) (FL polyOne)) (actionReciprocal w hw0 hw1 (P.half+P.padding)))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.sub_mul_eqv _ _ _)
  refine hdistrib.trans ((CReal.sub_congr_left (mul_swap_right _ _ _)).trans (CReal.sub_congr_right ?_))
  exact (CRealAlg.cmul_assoc _ _ _).trans
    ((Pivot2.mul_congr_right (expectation_one w hw0 hw1 (P.half+P.padding))).trans (CRealAlg.cmul_cone _))

theorem boundaryResponse_one : Equiv (boundaryResponse P w hw0 hw1 polyOne) czero :=
  (boundaryResponse_formula P w hw0 hw1 polyOne).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv _ _))) (Q'.add_neg_self_eqv _)))

end YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse

#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse.fullLimit
#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse.boundaryNumeratorCauchy
#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse.boundaryResponse
#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse.boundaryResponseCauchy
#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse.boundaryCutoff
#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse.boundaryResponse_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse.boundaryResponse_converges
#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse.boundaryResponse_formula
#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse.normalized_boundary_response
#print axioms YMGap.Continuum.BF4ExactSlabOffsetBoundaryResponse.boundaryResponse_one
