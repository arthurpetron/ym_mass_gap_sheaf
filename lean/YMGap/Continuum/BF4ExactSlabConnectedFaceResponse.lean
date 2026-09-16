/-
# Centered response to an ORIGINAL plaquette insertion

Adding one full heat factor changes the connected covariance by a third
connected moment MINUS a product of two connected moments. The existing
head covariance remains on the left; neither it nor the subtraction on
the right is discarded. On the diagonal the correction is a negative
square. All raw identities hold at every cutoff, without positivity.

The normalized consumer uses the existing original face-set expectations
at every 0<w<1. Both partition squares are canceled exactly. The inserted
heat depends on K and stays inside the finite response; only p and q are
fixed through the cutoff limit. No spatial bound on this response is
constructed here, and no thermodynamic or physical gap follows.
-/

import YMGap.Continuum.BF4ExactSlabAllNomeFaceSetComparison
import YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
import YMGap.Continuum.BF4ExactSlabTwoProbeCovariance
import YMGap.Continuum.RationalConnectedResponse

namespace YMGap.Continuum.BF4ExactSlabConnectedFaceResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabFaceInsertionDeterminant
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteRealScalarAlgebra
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

local infix:50 " ≈ " => Q'.eqv
local notation:max "nblocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

private theorem sub_square_le (a x : Q') : a + -(x*x) ≤ a :=
  Q'.sub_le_of_le_add (Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg a (x*x) (SumOfSquares.q_mul_self_nonneg x))
    (Q'.le_of_eqv (Q'.add_comm_eqv a (x*x))))

/-- Third cumulant numerator, cleared by the OLD partition cubed. -/
def thirdNumerator (w : Q') (K extent : Nat) (ids : List Nat) (p q r : RatPoly) : Q' :=
  let M := fun f => numerator w (nblocks extent) extent ids f K
  let Z := heatProductHaar w (nblocks extent) extent ids K
  M (polyMul (polyMul p q) r) * (Z*Z) + -(M (polyMul p q)*M r*Z) +
    -(M (polyMul p r)*M q*Z) + -(M (polyMul q r)*M p*Z) + 2*M p*M q*M r

/-- The signed combination to estimate, using the ACTUAL cutoff-dependent
inserted heat and the SAME old-action moments throughout. -/
def response (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat) (p q : RatPoly) : Q' :=
  let r := faceHeatPolynomial w K extent id
  numerator w (nblocks extent) extent ids r K * thirdNumerator w K extent ids p q r +
    -(connectedNumerator w K extent ids p r * connectedNumerator w K extent ids q r)

def responseDenominator (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat) : Q' :=
  let Z := heatProductHaar w (nblocks extent) extent ids K
  let R := heatProductHaar w (nblocks extent) extent (ids++[id]) K
  (R*R)*(Z*Z)

theorem connected_append_face (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat) (p q : RatPoly) :
    let M := fun f => numerator w (nblocks extent) extent ids f K
    let r := faceHeatPolynomial w K extent id
    connectedNumerator w K extent (ids++[id]) p q ≈
      M (polyMul (polyMul p q) r)*M r + -(M (polyMul p r)*M (polyMul q r)) :=
  Q'.add_eqv_congr'
    (qmul (numerator_append_face w K extent ids id (polyMul p q)) (partition_append_face w K extent ids id))
    (Q'.neg_eqv_congr _ _ (qmul (numerator_append_face w K extent ids id p)
      (numerator_append_face w K extent ids id q)))

/-- Both DIFFERENT partition squares remain, and the old connected
numerator is subtracted rather than replaced by zero. -/
theorem response_identity (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat) (p q : RatPoly) :
    let Z := heatProductHaar w (nblocks extent) extent ids K
    let R := heatProductHaar w (nblocks extent) extent (ids++[id]) K
    connectedNumerator w K extent (ids++[id]) p q*(Z*Z) +
      -(connectedNumerator w K extent ids p q*(R*R)) ≈ response w K extent ids id p q := by
  have hR := partition_append_face w K extent ids id
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (qmul (connected_append_face w K extent ids id p q) (Q'.eqv_refl _))
      (Q'.neg_eqv_congr _ _ (qmul (Q'.eqv_refl _) (qmul hR hR))))
    (RationalConnectedResponse.connected_response_identity _ _ _ _ _ _ _ _)

/-- The diagonal correction has a known sign: it is MINUS a square.
This does not assert a sign or a spatial bound for the third moment. -/
theorem diagonal_response_le_third (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat) (p : RatPoly) :
    response w K extent ids id p p ≤
      numerator w (nblocks extent) extent ids (faceHeatPolynomial w K extent id) K *
        thirdNumerator w K extent ids p p (faceHeatPolynomial w K extent id) :=
  sub_square_le _ _

/-- A constant probe has zero ORIGINAL connected numerator at any cutoff. -/
theorem connected_unit_left (w : Q') (K extent : Nat) (ids : List Nat) (q : RatPoly) :
    connectedNumerator w K extent ids polyOne q ≈ 0 := by
  have hq := @haar_of_coeff (nblocks extent) _ _ ((RatPolyCoeffEqv.one_mul q).mul_right
    (polynomialProduct (faceHeatPolynomial w K extent) ids))
  have h1 := @haar_of_coeff (nblocks extent) _ _ (RatPolyCoeffEqv.one_mul (polynomialProduct (faceHeatPolynomial w K extent) ids))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
    (qmul hq (Q'.eqv_refl _)) (Q'.neg_eqv_congr _ _ (qmul h1 (Q'.eqv_refl _))))
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 1) (.var 0)))) (.const 0)
      (by decide) (fun
        | 0 => numerator w (nblocks extent) extent ids q K
        | _ => heatProductHaar w (nblocks extent) extent ids K))

/-- Centering sanity check on the actual action, not a replacement model. -/
theorem response_unit_left (w : Q') (K extent : Nat) (ids : List Nat) (id : Nat) (q : RatPoly) :
    response w K extent ids id polyOne q ≈ 0 :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (response_identity w K extent ids id polyOne q))
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (qmul (connected_unit_left w K extent (ids++[id]) q) (Q'.eqv_refl _))
      (Q'.neg_eqv_congr _ _ (qmul (connected_unit_left w K extent ids q) (Q'.eqv_refl _))))
      (poly_identity_of_normal_eq (.add (.mul (.const 0) (.var 0)) (.neg (.mul (.const 0) (.var 1))))
        (.const 0) (by decide) (fun
          | 0 => let Z := heatProductHaar w (nblocks extent) extent ids K; Z*Z
          | _ => let R := heatProductHaar w (nblocks extent) extent (ids++[id]) K; R*R)))

private theorem appendPhysical {extent : Nat} {ids : List Nat} {id : Nat}
    (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent) (hid : id ∈ slabPhysicalFaceEdges extent) :
    ∀ j, j ∈ ids++[id] → j ∈ slabPhysicalFaceEdges extent := by
  intro j hj
  rcases List.mem_append.mp hj with h | h
  · exact hi j h
  · have he := List.mem_singleton.mp h
    subst j
    exact hid

section Normalized

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent : Nat)
  (ids : List Nat) (hi : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)

/-- Uses the existing original normalized values with one shared cutoff. -/
def finiteCovariance (p q : RatPoly) (n : Nat) : Q' :=
  finiteValue w hw0 hw1 extent ids hi (polyMul p q) n +
    -(finiteValue w hw0 hw1 extent ids hi p n * finiteValue w hw0 hw1 extent ids hi q n)

/-- The same existing cutoff-removed face-set expectations. -/
def covariance (p q : RatPoly) : CReal :=
  CReal.sub (expectation w hw0 hw1 extent ids hi (polyMul p q))
    (CReal.mul (expectation w hw0 hw1 extent ids hi p) (expectation w hw0 hw1 extent ids hi q))

def covarianceCauchy (p q : RatPoly) : QCauchy (covariance w hw0 hw1 extent ids hi p q).approx :=
  scalarAddCauchy _ _ (expectationCauchy w hw0 hw1 extent ids hi (polyMul p q))
    (scalarNegCauchy _ (scalarMulCauchy _ _ (expectationCauchy w hw0 hw1 extent ids hi p)
      (expectationCauchy w hw0 hw1 extent ids hi q)))

theorem finite_covariance_converges (p q : RatPoly) :
    ConvergesTo (fun n => ofQ' (finiteCovariance w hw0 hw1 extent ids hi p q n))
      (covariance w hw0 hw1 extent ids hi p q) := by
  have hs := convergesTo_add (finite_converges w hw0 hw1 extent ids hi (polyMul p q))
    (TrigAddCReal.convergesTo_neg (convergesTo_mul_general
      (finite_converges w hw0 hw1 extent ids hi p) (finite_converges w hw0 hw1 extent ids hi q)))
  refine TrigAddCReal.convergesTo_congr_seq ?_ hs
  intro n
  exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)

theorem finite_covariance_cleared (p q : RatPoly) (n : Nat) :
    finiteCovariance w hw0 hw1 extent ids hi p q n *
      (partitionSample w extent ids n * partitionSample w extent ids n) ≈
    connectedNumerator w (headCutoff w+n) extent ids p q :=
  RationalConnectedResponse.covariance_clear _ _ _ _ _
    (Q'.mul_recipPos_eqv _ (Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
      (partitionSample_floor w hw0 hw1 extent ids hi n)))

variable (id : Nat) (hid : id ∈ slabPhysicalFaceEdges extent)

/-- Clear the actual normalized covariance difference by BOTH partition
squares; the right side remains a signed original-action response. -/
theorem finite_response_cleared (p q : RatPoly) (n : Nat) :
    (finiteCovariance w hw0 hw1 extent (ids++[id]) (appendPhysical hi hid) p q n +
      -(finiteCovariance w hw0 hw1 extent ids hi p q n)) *
      responseDenominator w (headCutoff w+n) extent ids id ≈
    response w (headCutoff w+n) extent ids id p q :=
  Q'.eqv_trans _ _ _ (RationalConnectedResponse.difference_clear _ _ _ _ _ _
    (finite_covariance_cleared w hw0 hw1 extent (ids++[id]) (appendPhysical hi hid) p q n)
    (finite_covariance_cleared w hw0 hw1 extent ids hi p q n))
    (response_identity w (headCutoff w+n) extent ids id p q)

include hw0 hw1 hi hid in
theorem responseDenominator_positive (K : Nat) (hK : headCutoff w ≤ K) :
    (0 : Q') < responseDenominator w K extent ids id := by
  have ho := Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
    (partition_floor hw0 hw1 extent ids hi K hK)
  have hn := Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 (ids++[id]))
    (partition_floor hw0 hw1 extent (ids++[id]) (appendPhysical hi hid) K hK)
  exact Q'.mul_pos (Q'.mul_pos hn hn) (Q'.mul_pos ho ho)

/-- An input bound on the SIGNED response passes with its exact coefficient.
This theorem does not provide the missing spatially decaying coefficient. -/
theorem finite_response_bound (p q : RatPoly) (b : Q') (n : Nat)
    (h : Q'.abs (response w (headCutoff w+n) extent ids id p q) ≤
      b * responseDenominator w (headCutoff w+n) extent ids id) :
    Q'.abs (finiteCovariance w hw0 hw1 extent (ids++[id]) (appendPhysical hi hid) p q n +
      -(finiteCovariance w hw0 hw1 extent ids hi p q n)) ≤ b := by
  have hd := responseDenominator_positive w hw0 hw1 extent ids hi id hid (headCutoff w+n) (Nat.le_add_right _ _)
  have he := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (TsumDeriv.abs_mul_nonneg_right _ (Q'.le_of_lt hd)))
    (Q'.abs_eqv_congr (finite_response_cleared w hw0 hw1 extent ids hi id hid p q n))
  apply Q'.le_of_mul_le_mul_left (c := responseDenominator w (headCutoff w+n) extent ids id) _ hd
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))))

/-- Only the original p and q are fixed through the cutoff limit. The
cutoff-dependent heat insertion stays inside the finite signed hypothesis. -/
theorem covariance_response_bound_eventually (p q : RatPoly) (b : Q') (K0 : Nat)
    (h : ∀ K, K0 ≤ K → Q'.abs (response w K extent ids id p q) ≤ b*responseDenominator w K extent ids id) :
    leEv (CReal.abs (CReal.sub
      (covariance w hw0 hw1 extent (ids++[id]) (appendPhysical hi hid) p q)
      (covariance w hw0 hw1 extent ids hi p q))) (ofQ' b) := by
  have hs := convergesTo_abs (convergesTo_add
    (finite_covariance_converges w hw0 hw1 extent (ids++[id]) (appendPhysical hi hid) p q)
    (TrigAddCReal.convergesTo_neg (finite_covariance_converges w hw0 hw1 extent ids hi p q)))
  have hc : ConvergesTo
      (fun n => ofQ' (Q'.abs (finiteCovariance w hw0 hw1 extent (ids++[id]) (appendPhysical hi hid) p q n +
        -(finiteCovariance w hw0 hw1 extent ids hi p q n))))
      (CReal.abs (CReal.sub
        (covariance w hw0 hw1 extent (ids++[id]) (appendPhysical hi hid) p q)
        (covariance w hw0 hw1 extent ids hi p q))) := by
    refine TrigAddCReal.convergesTo_congr_seq ?_ hs
    intro n
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  apply leEv_of_ofQ'_limit_le hc (convergesTo_const (ofQ' b))
  intro epsilon he
  refine ⟨K0, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _
    (finite_response_bound w hw0 hw1 extent ids hi id hid p q b n
      (h _ (Nat.le_trans hn (Nat.le_add_left _ _))))
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))

end Normalized

/-- On the full odd slab this is the EXISTING covariance consumed by the
original distance-decay route, not an unrelated family of moments. -/
theorem full_covariance_pin (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (p q : RatPoly) :
    Equiv (covariance w hw0 hw1 (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
      (fun _ h => h) p q) (BF4ExactSlabTwoProbeCovariance.covariance w hw0 hw1 half p q) :=
  (CReal.sub_congr_left (odd_expectation_pin w hw0 hw1 half (polyMul p q))).trans
    (CReal.sub_congr_right
      ((Pivot2.mul_congr_left (odd_expectation_pin w hw0 hw1 half p)).trans
        (Pivot2.mul_congr_right (odd_expectation_pin w hw0 hw1 half q))))

end YMGap.Continuum.BF4ExactSlabConnectedFaceResponse

#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.thirdNumerator
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.response
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.responseDenominator
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.connected_append_face
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.response_identity
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.diagonal_response_le_third
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.connected_unit_left
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.response_unit_left
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.finiteCovariance
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.covariance
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.covarianceCauchy
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.finite_covariance_converges
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.finite_covariance_cleared
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.finite_response_cleared
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.responseDenominator_positive
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.finite_response_bound
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.covariance_response_bound_eventually
#print axioms YMGap.Continuum.BF4ExactSlabConnectedFaceResponse.full_covariance_pin
