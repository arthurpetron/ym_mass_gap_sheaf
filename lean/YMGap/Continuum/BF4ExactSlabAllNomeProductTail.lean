/-
# Fixed-region original heat-product tails at arbitrary rational nome

The low-spin head is retained in prefixCap. A finite product-sensitivity
recursion gives an explicit common cutoff depending only on w, the number
of retained faces, and the requested tolerance. All shared link variables
remain in the old heatProductRemainder and its exact prefix identity.

The interval certificate also bounds the normalized ORIGINAL interacting
square expectation of the actual prefix difference by epsilon^2. The
action nome v and inserted-region nome w are independent, both explicit.
The same partition cancels through the old normalized expectation theorem.
This is local representation-cutoff control, not thermodynamic decay or
an OS operator bound. The cutoff is not uniform in w or region size.
Physical scaling, continuum QFT and the Clay target remain open.
-/

import YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
import YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
import YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound

namespace YMGap.Continuum.BF4ExactSlabAllNomeProductTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.HeatKernelRGStep (lt_of_lt_of_le)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail (heatProductRemainder heatProduct_cutoff_append)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.BF4ExactSlabPlaquetteUniformMomentBound (expectation_upper)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

def productPrefixInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    Interval (boundaryCompleteSlabLinks extent).length (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (prefixCap w ^ ids.length) :=
  Interval.productUniform _ _ ids (fun id hid => facePrefixInterval hw0 hw1 K extent id (hi id hid))

/-- Computed sensitivity for n retained factors; no surrounding slab size. -/
def sensitivity (w : Q') : Nat → Q'
  | 0 => 0
  | n+1 => prefixCap w * sensitivity w n + prefixCap w ^ n

theorem sensitivity_nonnegative {w : Q'} (hw0 : (0 : Q') < w) : ∀ n, (0 : Q') ≤ sensitivity w n
  | 0 => Q'.le_refl' _
  | n+1 => Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ (prefixCap_nonnegative hw0) (sensitivity_nonnegative hw0 n))
    (Q'.pow_nonneg _ (prefixCap_nonnegative hw0) n)

/-- Exact old product remainder: no factorization across shared variables. -/
def productTailInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (delta : Q') (hd : (0 : Q') < delta) (K L extent : Nat) (hK : tailCutoff w delta ≤ K) :
    (ids : List Nat) → (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
      Interval (boundaryCompleteSlabLinks extent).length (heatProductRemainder w extent K L ids)
        (delta * sensitivity w ids.length)
  | [], _ => (Interval.zero _).changeCap (Q'.eqv_symm (Q'.mul_zero_eqv delta))
  | id::ids, hi =>
      ((facePrefixInterval hw0 hw1 K extent id (hi id List.mem_cons_self)).mul
        (productTailInterval hw0 hw1 delta hd K L extent hK ids (fun j hj => hi j (List.mem_cons_of_mem id hj)))).add
        ((faceTailInterval hw0 hw1 extent id (hi id List.mem_cons_self) delta hd K L hK).mul
          (productPrefixInterval hw0 hw1 (K+L) extent ids (fun j hj => hi j (List.mem_cons_of_mem id hj))))
      |>.changeCap (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.var 3)))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 3))) (by decide)
        (fun | 0 => prefixCap w | 1 => delta | 2 => sensitivity w ids.length | _ => prefixCap w ^ ids.length))

def productTolerance (w : Q') (n : Nat) (epsilon : Q') : Q' :=
  HKConv.divPos epsilon (sensitivity w n + 1)

theorem productTolerance_positive (w : Q') (n : Nat) {epsilon : Q'} (he : (0 : Q') < epsilon) :
    (0 : Q') < productTolerance w n epsilon := HKConv.divPos_pos (CReal.num_pos_of_pos he)

theorem productTolerance_budget {w : Q'} (hw0 : (0 : Q') < w) (n : Nat)
    {epsilon : Q'} (he : (0 : Q') < epsilon) : productTolerance w n epsilon * sensitivity w n ≤ epsilon := by
  have hp : (0 : Q') < sensitivity w n + 1 :=
    lt_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ (sensitivity_nonnegative hw0 n))
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
      (Q'.le_of_lt (productTolerance_positive w n he)))
    (Q'.le_of_eqv (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hp)))

def productCutoff (w : Q') (n : Nat) (epsilon : Q') : Nat :=
  tailCutoff w (productTolerance w n epsilon)

def smallProductTailInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat) (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (epsilon : Q') (he : (0 : Q') < epsilon) (K L : Nat) (hK : productCutoff w ids.length epsilon ≤ K) :
    Interval (boundaryCompleteSlabLinks extent).length (heatProductRemainder w extent K L ids) epsilon :=
  (productTailInterval hw0 hw1 (productTolerance w ids.length epsilon)
    (productTolerance_positive w ids.length he) K L extent hK ids hi).weaken (productTolerance_budget hw0 ids.length he)

/-- One returned cutoff works for EVERY placement of n physical faces in
EVERY slab, and every later cutoff/tail length, at the supplied w/epsilon. -/
def productTailData {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (n : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' cutoff : Nat, ∀ (extent : Nat) (ids : List Nat), ids.length = n →
      (∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) →
      ∀ K L : Nat, cutoff ≤ K →
        Interval (boundaryCompleteSlabLinks extent).length (heatProductRemainder w extent K L ids) epsilon :=
  ⟨productCutoff w n epsilon, fun extent ids hn hi K L hK =>
    smallProductTailInterval hw0 hw1 extent ids hi epsilon he K L (by simpa only [hn] using hK)⟩

/-- Literal later prefix minus earlier prefix, not a replacement observable. -/
def productDifference (w : Q') (extent K L : Nat) (ids : List Nat) : RatPoly :=
  polyAdd (polynomialProduct (faceHeatPolynomial w (K+L) extent) ids)
    (polyNeg (polynomialProduct (faceHeatPolynomial w K extent) ids))

theorem productDifference_pin (w : Q') (extent K L : Nat) (ids : List Nat) :
    RatPolyCoeffEqv (productDifference w extent K L ids) (heatProductRemainder w extent K L ids) :=
  ((heatProduct_cutoff_append w extent K L ids).add (RatPolyCoeffEqv.refl _)).trans
    (coeffEvalExpr_eqv_of_normalize_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
      (by decide) (fun | 0 => polynomialProduct (faceHeatPolynomial w K extent) ids | _ => heatProductRemainder w extent K L ids))

/-- Normalized ORIGINAL interacting second moment; partition cancels exactly. -/
theorem remainder_square_expectation {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (v : Q') (hv0 : (0 : Q') < v) (hv1 : v < (1 : Q'))
    (half : Nat) (ids : List Nat) (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (centralExtent half))
    (epsilon : Q') (he : (0 : Q') < epsilon) (K L : Nat) (hK : productCutoff w ids.length epsilon ≤ K) :
    CReal.leEv (expectation v hv0 hv1 half
      (polyMul (heatProductRemainder w (centralExtent half) K L ids) (heatProductRemainder w (centralExtent half) K L ids)))
      (CReal.ofQ' (epsilon*epsilon)) :=
  let R := smallProductTailInterval hw0 hw1 (centralExtent half) ids hi epsilon he K L hK
  expectation_upper v hv0 hv1 half _ _ (R.mul R).upper

/-- The same bound for the actual prefix difference in the old original law. -/
theorem difference_square_expectation {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (v : Q') (hv0 : (0 : Q') < v) (hv1 : v < (1 : Q'))
    (half : Nat) (ids : List Nat) (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (centralExtent half))
    (epsilon : Q') (he : (0 : Q') < epsilon) (K L : Nat) (hK : productCutoff w ids.length epsilon ≤ K) :
    CReal.leEv (expectation v hv0 hv1 half
      (polyMul (productDifference w (centralExtent half) K L ids) (productDifference w (centralExtent half) K L ids)))
      (CReal.ofQ' (epsilon*epsilon)) :=
  CReal.leEv_trans (CReal.leEv_of_equiv (expectation_congr v hv0 hv1 half
    ((productDifference_pin w (centralExtent half) K L ids).mul (productDifference_pin w (centralExtent half) K L ids))))
    (remainder_square_expectation hw0 hw1 v hv0 hv1 half ids hi epsilon he K L hK)

end YMGap.Continuum.BF4ExactSlabAllNomeProductTail

#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.productPrefixInterval
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.sensitivity
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.sensitivity_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.productTailInterval
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.productTolerance
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.productTolerance_positive
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.productTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.productCutoff
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.smallProductTailInterval
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.productTailData
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.productDifference
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.productDifference_pin
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.remainder_square_expectation
#print axioms YMGap.Continuum.BF4ExactSlabAllNomeProductTail.difference_square_expectation
