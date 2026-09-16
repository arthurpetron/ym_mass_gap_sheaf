/-
# Explicit cutoff tails for the actual fixed-spatial K times V kernel

The finite telescope retains the original lower-times-conjugate-upper
relative words and the ordered spatial plaquette words on the SAME two-slice
source carrier. The complete low-spin head is bounded by prefixCap; it is
not replaced by one. All shared variables remain in the polynomial product.

The returned cutoff depends on nome, width-only face count and tolerance,
not on the two later cutoffs, ambient extent or time placement. It is not
uniform in width or nome. The difference is signed: no positive-certificate
claim about W_J-W_K, stationary normalization, OS identification, operator
limit or spectral gap is made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
import YMGap.Continuum.BF4ExactSlabAllNomeProductTail
import YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse
import YMGap.Continuum.PolynomialProductRemainder

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabAllNomeProductTail
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (temporalFaces spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (relative kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarPolynomialGeometricInverse (negInterval)
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarAllNomeHeatCertificate
open YMGap.Continuum.PolynomialProductRemainder
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor (pointwiseHeatMajorant)
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
open YMGap.Continuum.SU2PointwiseHeatSpacingTailBound

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Both actual factor families, counting the head spatial weight once. -/
def stepFaceCount (width : Nat) : Nat :=
  (temporalFaces width).length + (spatialFaces width).length

private def stepFaces (width : Nat) : List (Sum Z4Plaq Z4Plaq) :=
  (temporalFaces width).map Sum.inl ++ (spatialFaces width).map Sum.inr

private def stepWord (width : Nat) : Sum Z4Plaq Z4Plaq → PolyQuaternion
  | .inl face => relative width face
  | .inr face => plaquette width face

private theorem stepFaces_length (width : Nat) :
    (stepFaces width).length = stepFaceCount width := by
  simp only [stepFaces, stepFaceCount, List.length_append, List.length_map]

private def stepWordSquare (width : Nat) :
    (i : Sum Z4Plaq Z4Plaq) → SquareBound (N width+N width) (stepWord width i).scalar 1
  | .inl face => .scalar (relative_supported width face) (relative_unit width face)
  | .inr face => .scalar (plaquette_supported width (N width+N width) (by omega) face)
      (plaquette_unit width (N width+N width) (by omega) face)

private theorem product_map {A C : Type} (f : C → RatPoly) (g : A → C) (xs : List A) :
    polynomialProduct f (xs.map g) = polynomialProduct (fun a => f (g a)) xs := by
  simp only [polynomialProduct, List.foldr_map]

private theorem stepWeight_product (w : Q') (K width : Nat) :
    RatPolyCoeffEqv (stepWeight w K width)
      (polynomialProduct (fun i => heatPrefix w K (stepWord width i).scalar) (stepFaces width)) := by
  have hkin : kineticWeight w K width = polynomialProduct
      (fun face => heatPrefix w K (relative width face).scalar) (temporalFaces width) := by
    apply polynomialProduct_congr
    intro face _
    exact heatFace_eq_prefix w K width face
  have hp := polynomialProduct_append
    (fun i => heatPrefix w K (stepWord width i).scalar)
    ((temporalFaces width).map Sum.inl) ((spatialFaces width).map Sum.inr)
  simpa only [stepWeight, hkin, spatialWeight, stepFaces, product_map, stepWord] using hp.symm

private def prefixTail (w : Q') (x : RatPoly) (K L : Nat) : RatPoly :=
  finitePolySum (fun i => heatTerm w x (K+1+i)) (List.range L)

private theorem prefix_add_tail (w : Q') (x : RatPoly) (K L : Nat) :
    heatPrefix w (K+L) x = polyAdd (heatPrefix w K x) (prefixTail w x K L) := by
  change finitePolySum (heatTerm w x) (List.range (K+L+1)) =
    polyAdd (finitePolySum (heatTerm w x) (List.range (K+1))) _
  rw [show K+L+1 = (K+1)+L by omega]
  exact PolynomialWeightedSumBounds.sum_range_add (heatTerm w x) (K+1) L

private def prefixTailInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {blocks : Nat} {x : RatPoly} (P : SquareBound blocks x 1)
    (delta : Q') (hd : (0 : Q') < delta) (K L : Nat) (hK : tailCutoff w delta ≤ K) :
    Interval blocks (prefixTail w x K L) delta := by
  have hN : spacingLabelCutoff w ≤ K+1 := by unfold tailCutoff at hK; omega
  have hM : spacingTailCauchyCutoff w delta ≤ K+1-spacingLabelCutoff w := by
    unfold tailCutoff at hK
    omega
  have h := shiftedMajorant_block hw0 hw1 (K+1-spacingLabelCutoff w) L
  simp only [← Nat.add_assoc, Nat.add_sub_of_le hN] at h
  exact (Interval.finiteRange (fun i => heatTerm w x (K+1+i))
    (fun i => pointwiseHeatMajorant w (K+1+i))
    (fun i => termInterval (Q'.le_of_lt hw0) P (K+1+i)) L).weaken
      (Q'.le_trans' _ _ _ h (closedTail_small hw0 hw1 delta hd _ hM))

private def sourceProductTailInterval {A : Type} {blocks : Nat} {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (x : A → RatPoly)
    (P : ∀ i, SquareBound blocks (x i) 1)
    (delta : Q') (hd : (0 : Q') < delta) (K L : Nat) (hK : tailCutoff w delta ≤ K) :
    (ids : List A) → Interval blocks
      (productRemainder (fun i => heatPrefix w K (x i))
        (fun i => heatPrefix w (K+L) (x i)) (fun i => prefixTail w (x i) K L) ids)
      (delta * sensitivity w ids.length)
  | [] => (Interval.zero _).changeCap (Q'.eqv_symm (Q'.mul_zero_eqv delta))
  | i::ids =>
      ((prefixInterval hw0 hw1 (P i) K).mul
        (sourceProductTailInterval hw0 hw1 x P delta hd K L hK ids)).add
        ((prefixTailInterval hw0 hw1 (P i) delta hd K L hK).mul
          (Interval.productUniform _ _ ids (fun j _ => prefixInterval hw0 hw1 (P j) (K+L))))
      |>.changeCap (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2))) (.mul (.var 1) (.var 3)))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 2)) (.var 3))) (by decide)
        (fun
          | 0 => prefixCap w
          | 1 => delta
          | 2 => sensitivity w ids.length
          | _ => prefixCap w ^ ids.length))

private def stepRemainder (w : Q') (K L width : Nat) : RatPoly :=
  productRemainder (fun i => heatPrefix w K (stepWord width i).scalar)
    (fun i => heatPrefix w (K+L) (stepWord width i).scalar)
    (fun i => prefixTail w (stepWord width i).scalar K L) (stepFaces width)

private theorem stepDifference_remainder (w : Q') (K L width : Nat) :
    RatPolyCoeffEqv (polyAdd (stepWeight w (K+L) width) (polyNeg (stepWeight w K width)))
      (stepRemainder w K L width) := by
  have hp := polynomialProduct_remainder
    (fun i => heatPrefix w K (stepWord width i).scalar)
    (fun i => heatPrefix w (K+L) (stepWord width i).scalar)
    (fun i => prefixTail w (stepWord width i).scalar K L)
    (fun i => by
      dsimp only
      rw [prefix_add_tail w (stepWord width i).scalar K L]
      exact RatPolyCoeffEqv.refl _)
    (stepFaces width)
  exact ((stepWeight_product w (K+L) width).add (RatPolyCoeffEqv.neg (stepWeight_product w K width))).trans
    ((hp.add (RatPolyCoeffEqv.refl _)).trans
      (coeffEvalExpr_eqv_of_normalize_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
        (by decide) (fun
          | 0 => polynomialProduct
              (fun i => heatPrefix w K (stepWord width i).scalar) (stepFaces width)
          | _ => stepRemainder w K L width)))

/-- Computed modulus: the existing all-nome product cutoff at the actual face count. -/
def stepTailCutoff (w : Q') (width : Nat) (epsilon : Q') : Nat :=
  productCutoff w (stepFaceCount width) epsilon

/-- Every later tail length is controlled on the actual two-slice K times V carrier. -/
def stepWeightTailInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) (K L : Nat)
    (hK : stepTailCutoff w width epsilon ≤ K) :
    Interval (N width+N width)
      (polyAdd (stepWeight w (K+L) width) (polyNeg (stepWeight w K width))) epsilon := by
  let R := sourceProductTailInterval hw0 hw1 (fun i => (stepWord width i).scalar)
    (stepWordSquare width) (productTolerance w (stepFaceCount width) epsilon)
    (productTolerance_positive w (stepFaceCount width) he) K L hK (stepFaces width)
  have R' : Interval (N width+N width) (stepRemainder w K L width)
      (productTolerance w (stepFaceCount width) epsilon * sensitivity w (stepFaceCount width)) := by
    simpa only [stepFaces_length] using R
  exact Interval.ofCoeff
    (((stepWeightInterval hw0 hw1 (K+L) width).add
      (negInterval (stepWeightInterval hw0 hw1 K width))).support)
    (stepDifference_remainder w K L width)
    (R'.weaken (productTolerance_budget hw0 (stepFaceCount width) he))

/-- A two-sided interval for the SIGNED difference at any two late cutoffs.
No positivity cutoff or certificate of the difference is assumed. -/
def stepWeightDifferenceInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) (K J : Nat)
    (hK : stepTailCutoff w width epsilon ≤ K) (hJ : stepTailCutoff w width epsilon ≤ J) :
    Interval (N width+N width)
      (polyAdd (stepWeight w J width) (polyNeg (stepWeight w K width))) epsilon := by
  if h : K ≤ J then
    simpa only [Nat.add_sub_of_le h] using stepWeightTailInterval hw0 hw1 width epsilon he K (J-K) hK
  else
    have h' : J ≤ K := by omega
    have R := negInterval (stepWeightTailInterval hw0 hw1 width epsilon he J (K-J) hJ)
    rw [Nat.add_sub_of_le h'] at R
    exact Interval.ofCoeff
      (((stepWeightInterval hw0 hw1 J width).add
        (negInterval (stepWeightInterval hw0 hw1 K width))).support)
      (coeffEvalExpr_eqv_of_normalize_eq (.add (.var 0) (.neg (.var 1)))
        (.neg (.add (.var 1) (.neg (.var 0)))) (by decide)
        (fun | 0 => stepWeight w J width | _ => stepWeight w K width)) R

/-- The modulus is returned as data and works simultaneously for both cutoff indices. -/
def stepTailData {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' cutoff : Nat, ∀ K J : Nat, cutoff ≤ K → cutoff ≤ J →
      Interval (N width+N width)
        (polyAdd (stepWeight w J width) (polyNeg (stepWeight w K width))) epsilon :=
  ⟨stepTailCutoff w width epsilon, fun K J hK hJ =>
    stepWeightDifferenceInterval hw0 hw1 width epsilon he K J hK hJ⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferTail

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferTail.stepFaceCount
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferTail.stepTailCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferTail.stepWeightTailInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferTail.stepWeightDifferenceInterval
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferTail.stepTailData
