/-
# Same-action normalized cutoff limits without a slab-parity restriction

The existing small-nome face certificates bound EVERY finite partition
below by (1-delta(w))^|ids|. Its exact rational reciprocal stream therefore
has a computed modulus, for any physical face list and any slab extent.
The normalized finite values converge to the original numerator limit
times the reciprocal of the SAME original partition limit. Both the raw
cutoff stream and the resulting CReal representative have explicit moduli.

On a full odd slab this construction is proved equal to the EXISTING
polynomial expectation by exact partition cancellation. It is not a new
normalization or a substitute state theory. The face-count-dependent floor
is not volume-uniform. The small-nome guards are explicit throughout.

This removes the odd-only cutoff-normalization restriction needed by the
site-positivity comparison. It does not compare different finite volumes,
construct an even-slab thermodynamic limit, or prove completed T1 positivity,
range density, physical mass normalization or continuum/Clay closure.
-/

import YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
import YMGap.Continuum.BF4ExactSlabPolynomialExpectation

namespace YMGap.Continuum.BF4ExactSlabFaceSetExpectation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabSmallNomeHaarComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.BoundedRationalCauchyProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

def partitionFloor (w : Q') (ids : List Nat) : Q' := (1 + -heatRemainderBound w)^ids.length

theorem partitionFloor_pos {w : Q'} (hd : heatRemainderBound w < 1) (ids : List Nat) :
    (0 : Q') < partitionFloor w ids := HKPos.pow_pos (HKPos.one_sub_pos hd) _

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (extent : Nat) (ids : List Nat) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)

local notation "blocks" => List.length (boundaryCompleteSlabLinks extent)
local notation "Z" => heatProductHaar w blocks extent ids
local notation "ZC" => heatProductHaarCauchy w hw0 hw1 blocks extent ids
local notation "Zlim" => heatProductHaarLimit w hw0 hw1 blocks extent ids
local notation "N" => numerator w blocks extent ids
local notation "Nlim" => numeratorLimit w hw0 hw1 blocks extent ids

include hw0 hw1 hsmall hd hids in
theorem partition_floor (K : Nat) : partitionFloor w ids ≤ Z K :=
  faceProduct_floor (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) hsmall (Q'.le_of_lt hd) K extent ids hids

local notation "floorProof" => partition_floor w hw0 hw1 hsmall hd extent ids hids
local notation "R" => PositiveRationalCauchyReciprocal.term (partitionFloor w ids) (partitionFloor_pos hd ids) floorProof
local notation "RC" => PositiveRationalCauchyReciprocal.reciprocalCauchy ZC
  (partitionFloor w ids) (partitionFloor_pos hd ids) floorProof

/-- The denominator is the same-cutoff original partition, not an auxiliary law. -/
def finiteValue (p : RatPoly) (K : Nat) : Q' := N p K * R K

def reciprocal : CReal := PositiveRationalCauchyReciprocal.value ZC
  (partitionFloor w ids) (partitionFloor_pos hd ids) floorProof

theorem reciprocal_positive (n : Nat) :
    (0 : Q') < (reciprocal w hw0 hw1 hsmall hd extent ids hids).approx n :=
  PositiveRationalCauchyReciprocal.value_approx_pos _ _ _ _ n

theorem partition_cancellation :
    Equiv (CReal.mul Zlim (reciprocal w hw0 hw1 hsmall hd extent ids hids)) cone :=
  PositiveRationalCauchyReciprocal.mul_value _ _ _ _

def expectation (p : RatPoly) : CReal :=
  CReal.mul (Nlim p) (reciprocal w hw0 hw1 hsmall hd extent ids hids)

/-- A finite-volume numerical budget; no claim of uniformity in ids or w. -/
def productBound (p : RatPoly) : Q' :=
  polynomialCoefficientL1 p * heatProductBound w extent ids +
    Q'.recipPos (partitionFloor w ids) (partitionFloor_pos hd ids) + 1

include hw0 hw1 in
private theorem numerator_bound (p : RatPoly) (K : Nat) :
    Q'.abs (N p K) ≤ polynomialCoefficientL1 p * heatProductBound w extent ids :=
  Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _)
    (Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (heatProduct_coefficientL1_bound hw0 hw1 _ _ _)
        (polynomialCoefficientL1_nonnegative p)))

include hw0 in
theorem productBound_pos (p : RatPoly) : (0 : Q') < productBound w hd extent ids p :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (polynomialCoefficientL1_nonnegative p)
          (heatProductBound_nonnegative (Q'.le_of_lt hw0) _ _))
        (Q'.le_of_lt (Q'.recipPos_pos _ _))))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

include hw0 hw1 in
private theorem numerator_productBound (p : RatPoly) (K : Nat) :
    Q'.abs (N p K) ≤ productBound w hd extent ids p :=
  Q'.le_trans' _ _ _ (numerator_bound w hw0 hw1 extent ids p K)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt (Q'.recipPos_pos _ _)))
      (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one))

include hw0 in
private theorem reciprocal_ceiling_bound (p : RatPoly) :
    Q'.recipPos (partitionFloor w ids) (partitionFloor_pos hd ids) ≤ productBound w hd extent ids p :=
  Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _
      (Q'.mul_nonneg _ _ (polynomialCoefficientL1_nonnegative p)
        (heatProductBound_nonnegative (Q'.le_of_lt hw0) _ _)))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
    (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)

private theorem reciprocal_term_bound (p : RatPoly) (K : Nat) : Q'.abs (R K) ≤ productBound w hd extent ids p := by
  rw [ExpNeg.abs_of_nonneg (Q'.le_of_lt (PositiveRationalCauchyReciprocal.term_pos _ _ _ K))]
  exact Q'.le_trans' _ _ _ (PositiveRationalCauchyReciprocal.term_le _ _ _ K)
    (reciprocal_ceiling_bound w hw0 hd extent ids p)

private theorem reciprocal_rep_bound (p : RatPoly) (n : Nat) :
    Q'.abs ((reciprocal w hw0 hw1 hsmall hd extent ids hids).approx n) ≤ productBound w hd extent ids p :=
  reciprocal_term_bound w hw0 hw1 hsmall hd extent ids hids p _

def finiteCauchy (p : RatPoly) : QCauchy (finiteValue w hw0 hw1 hsmall hd extent ids hids p) :=
  productCauchy (numeratorCauchy w hw0 hw1 blocks extent ids p) RC
    (productBound w hd extent ids p) (productBound_pos w hw0 hd extent ids p)
    (numerator_productBound w hw0 hw1 hd extent ids p)
    (reciprocal_term_bound w hw0 hw1 hsmall hd extent ids hids p)

def expectationCauchy (p : RatPoly) : QCauchy (expectation w hw0 hw1 hsmall hd extent ids hids p).approx :=
  productCauchy
    (representativeCauchy _ (numeratorCauchy w hw0 hw1 blocks extent ids p))
    (representativeCauchy _ RC)
    (productBound w hd extent ids p) (productBound_pos w hw0 hd extent ids p)
    (fun _ => numerator_productBound w hw0 hw1 hd extent ids p _)
    (reciprocal_rep_bound w hw0 hw1 hsmall hd extent ids hids p)

theorem finite_converges (p : RatPoly) :
    ConvergesTo (fun K => ofQ' (finiteValue w hw0 hw1 hsmall hd extent ids hids p K))
      (expectation w hw0 hw1 hsmall hd extent ids hids p) := by
  have hmul := convergesTo_mul
    (u := fun K => ofQ' (N p K)) (v := fun K => ofQ' (R K))
    (U := Nlim p) (V := reciprocal w hw0 hw1 hsmall hd extent ids hids)
    (Q'.le_of_lt (productBound_pos w hw0 hd extent ids p))
    (fun K _ => numerator_productBound w hw0 hw1 hd extent ids p K)
    (reciprocal_rep_bound w hw0 hw1 hsmall hd extent ids hids p)
    (numerator_converges w hw0 hw1 blocks extent ids p)
    (PositiveRationalCauchyReciprocal.converges _ _ _ _)
  exact TrigAddCReal.convergesTo_congr_seq
    (fun _ => SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)) hmul

/-- The raw normalized cutoff and the actual CReal representative are both
controlled by the same computed product-stream modulus. -/
theorem approx_close (p : RatPoly) (epsilon : Q') (he : (0 : Q') < epsilon)
    (K n : Nat)
    (hK : (finiteCauchy w hw0 hw1 hsmall hd extent ids hids p).M epsilon ≤ K)
    (hn : (finiteCauchy w hw0 hw1 hsmall hd extent ids hids p).M epsilon ≤ n) :
    finiteValue w hw0 hw1 hsmall hd extent ids hids p K ≤
      (expectation w hw0 hw1 hsmall hd extent ids hids p).approx n + epsilon ∧
    (expectation w hw0 hw1 hsmall hd extent ids hids p).approx n ≤
      finiteValue w hw0 hw1 hsmall hd extent ids hids p K + epsilon := by
  let B := productBound w hd extent ids p
  have hB := productBound_pos w hw0 hd extent ids p
  let delta := tolerance B hB epsilon
  have hdelt := tolerance_pos B hB he
  have hN := numerator_approx_close w hw0 hw1 blocks extent ids p delta hdelt K n
    (Nat.le_trans (Nat.le_max_left _ _) hK) (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hR := (RC).bound delta hdelt K (QMhat _ RC n)
    (Nat.le_trans (Nat.le_max_right _ _) hK)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) hn) (self_le_QMhat _ RC n))
  have step := product_close (N p K) ((Nlim p).approx n) (R K)
    ((reciprocal w hw0 hw1 hsmall hd extent ids hids).approx n) B delta
    (Q'.le_of_lt hB) (Q'.le_of_lt hdelt)
    (numerator_productBound w hw0 hw1 hd extent ids p K)
    (reciprocal_rep_bound w hw0 hw1 hsmall hd extent ids hids p n) hN hR
  have back := product_close ((Nlim p).approx n) (N p K)
    ((reciprocal w hw0 hw1 hsmall hd extent ids hids).approx n) (R K) B delta
    (Q'.le_of_lt hB) (Q'.le_of_lt hdelt)
    (numerator_productBound w hw0 hw1 hd extent ids p _)
    (reciprocal_term_bound w hw0 hw1 hsmall hd extent ids hids p K) hN.symm hR.symm
  exact ⟨Q'.le_trans' _ _ _ step (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ (tolerance_budget B hB epsilon))),
    Q'.le_trans' _ _ _ back (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ (tolerance_budget B hB epsilon)))⟩

theorem expectation_one : Equiv (expectation w hw0 hw1 hsmall hd extent ids hids polyOne) cone :=
  (Pivot2.mul_congr_left (numeratorLimit_one w hw0 hw1 blocks extent ids)).trans
    (partition_cancellation w hw0 hw1 hsmall hd extent ids hids)

theorem expectation_recover (p : RatPoly) :
    Equiv (CReal.mul (expectation w hw0 hw1 hsmall hd extent ids hids p) Zlim) (Nlim p) :=
  (CRealAlg.cmul_assoc _ _ _).trans
    ((Pivot2.mul_congr_right ((CRealAlg.cmul_comm _ _).trans
      (partition_cancellation w hw0 hw1 hsmall hd extent ids hids))).trans (CRealAlg.cmul_cone _))

/-- No surrogate normalization: the full odd specialization is the existing law. -/
theorem odd_expectation_pin (half : Nat) (p : RatPoly) :
    Equiv (expectation w hw0 hw1 hsmall hd (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
      (fun _ h => h) p) (BF4ExactSlabPolynomialExpectation.expectation w hw0 hw1 half p) := by
  let e := expectation w hw0 hw1 hsmall hd (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
    (fun _ h => h) p
  have hcancel := BF4ExactSlabOriginalActionReciprocal.action_mul_reciprocal w hw0 hw1 half
  exact (CRealAlg.cmul_cone e).symm.trans
    ((Pivot2.mul_congr_right hcancel.symm).trans
      ((CRealAlg.cmul_assoc _ _ _).symm.trans
        (Pivot2.mul_congr_left (expectation_recover w hw0 hw1 hsmall hd
          (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) (fun _ h => h) p))))

end YMGap.Continuum.BF4ExactSlabFaceSetExpectation

#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.partitionFloor
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.partitionFloor_pos
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.partition_floor
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.finiteValue
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.reciprocal
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.reciprocal_positive
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.partition_cancellation
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.expectation
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.productBound
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.productBound_pos
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.finiteCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.expectationCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.finite_converges
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.approx_close
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.expectation_one
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.expectation_recover
#print axioms YMGap.Continuum.BF4ExactSlabFaceSetExpectation.odd_expectation_pin
