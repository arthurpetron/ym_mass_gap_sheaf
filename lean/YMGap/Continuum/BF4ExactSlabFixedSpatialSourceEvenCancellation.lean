/-
# Quadratic source information retained in the original plaquette energy

Test Delta(q)*Delta(f) against (q_x+q_y)*(f_x+f_y). Their product is
Delta(q^2)*Delta(f^2), so the actual label-two heat image determines the
test mean from the SAME raw source moments A=H[q^2], F=H[q^2*f^2].

The test norm is at most 64*A. Cauchy--Schwarz therefore retains the
square (1-w^32)^2*(F-A)^2 in a denominator-free original energy bound.
No positive response, source inverse, or stationary-source equation is
assumed. These raw moments are NOT the q*Pq interacting variance, and no
physical scaling or continuum survival estimate is asserted.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSumTest
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungCancellation
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSourceEvenCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_product)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat productMap)
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung (sourceIncrementCost)
open YMGap.Continuum.SU2QuaternionProductHeatJumpMean (jump_mean)
open YMGap.Continuum.SU2QuaternionProductHeatSumTest
  (sumCopy sumTest sumTest_supported sumTest_square_le_rawSourceMass)
open YMGap.Continuum.SU2QuaternionProductHeatPlaquetteSquare (first_character_square)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_one)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair weighted_cauchySchwarz)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare (plaquetteSquare_fullRange)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDefect (plaquetteSquareBound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit
  (plaquetteChannelCost padded_terminal_plaquette_young_channels)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry
  (rawSourceMass rawSourceSquare rawSourceMass_nonnegative)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks terminalMessage

/-- Half the mean of the quadratic source test; its sign is unrestricted. -/
def evenResponse (w : Q') (width : Nat) (face : Z4Plaq) (q : RatPoly) : Q' :=
  (1 + -(qpow w 32))*(rawSourceSquare width face q + -rawSourceMass width q)

/-- Exact one-slice raw square moment after the ORIGINAL full heat. -/
theorem square_heat_moment (w : Q') (K width : Nat) (hK : 2 ≤ K)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    let f := characterPolynomial (plaquette width face).scalar 1
    H width (polyMul (polyMul q q) (productMap (N width) w K (List.range (N width))
        (polyMul f f))) ≈
      rawSourceMass width q + qpow w 32*(rawSourceSquare width face q + -rawSourceMass width q) := by
  dsimp only
  let p := (plaquette width face).scalar
  let f := characterPolynomial p 1
  let chi2 := characterPolynomial p 2
  let q2 := polyMul q q
  have hcenter : RatPolyCoeffEqv chi2 (polyAdd (polyMul f f) (polySmul (-1) polyOne)) := by
    have h := coeffEvalExpr_eqv_of_normalize_eq
      (.var 0) (.add (.add (.var 1) (.var 0)) (.mul (.const (-1)) (.var 1)))
      (by decide) (fun | 0 => chi2 | _ => polyOne)
    exact h.trans (((RatPolyCoeffEqv.refl _).add (cap_mul_left (-1) polyOne)).trans
      ((first_character_square p).symm.add (RatPolyCoeffEqv.refl _)))
  have hchi : H width (polyMul q2 chi2) ≈ rawSourceSquare width face q + -rawSourceMass width q :=
    Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.refl q2).mul hcenter))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right (N width) q2 _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
          (quaternionHaar_polyMul_smul_right (N width) (-1) q2 polyOne)
          (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
            (by decide) (fun _ => rawSourceMass width q)))))
  exact Q'.eqv_trans _ _ _ (plaquetteSquare_fullRange width face hf w K hK q2
    (supported_polyMul hq hq))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right (N width) q2 _ _)
      (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_smul_right (N width) (qpow w 32) q2 chi2)
        (Q'.mul_eqv_congr_left _ _ _ hchi))))

/-- The test product is the product of the two square jumps, including all
cross terms. The proof neither factorizes the source nor takes absolute values. -/
theorem quadratic_jump_mean (w : Q') (K width : Nat) (hK : 2 ≤ K)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    let f := characterPolynomial (plaquette width face).scalar 1
    weightedPair (N width+N width) (productHeat (N width) w K (List.range (N width)))
        (polyMul (jump (N width) q) (jump (N width) f)) (sumTest (N width) q f) ≈
      2*evenResponse w width face q := by
  dsimp only
  let n := N width
  let f := characterPolynomial (plaquette width face).scalar 1
  let W := productHeat n w K (List.range n)
  have hs := character_supported
    (plaquette_supported width n (Nat.le_refl _) face).scalar 1
  have hid : RatPolyCoeffEqv
      (polyMul (polyMul (jump n q) (jump n f)) (sumTest n q f))
      (polyMul (polyMul (jump n (polyMul q q)) (jump n (polyMul f f))) polyOne) := by
    unfold jump sumTest sumCopy
    rw [lift_product, lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3))))
        (.mul (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3))))
      (.mul (.mul
        (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 1))))
        (.add (.mul (.var 2) (.var 2)) (.neg (.mul (.var 3) (.var 3))))) (.const 1))
      (by decide) (fun | 0 => q | 1 => liftBoundary n q | 2 => f | _ => liftBoundary n f)
  have hm := jump_mean n w K (List.range n) (CayleyParentInj.range_nodup _)
    (fun _ hi => List.mem_range.mp hi) (supported_polyMul hq hq) (supported_polyMul hs hs)
  have halg : 2*(rawSourceSquare width face q +
      -(rawSourceMass width q + qpow w 32*(rawSourceSquare width face q + -rawSourceMass width q))) ≈
      2*evenResponse w width face q := by
    let d : RingNormaliser.PolyExpr := .add (.var 0) (.neg (.var 1))
    exact poly_identity_of_normal_eq
      (.mul (.const 2) (.add (.var 0) (.neg (.add (.var 1) (.mul (.var 2) d)))))
      (.mul (.const 2) (.mul (.add (.const 1) (.neg (.var 2))) d))
      (by decide)
      (fun | 0 => rawSourceSquare width face q | 1 => rawSourceMass width q | _ => qpow w 32)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (hid.mul_right W))
    (Q'.eqv_trans _ _ _ hm (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 2 _ _ (Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (square_heat_moment w K width hK face hf q hq))))
      halg))

/-- Retained quadratic-source square with no division by A or F-A. -/
theorem sourceIncrement_even_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    evenResponse w width face q * evenResponse w width face q ≤
      16*rawSourceMass width q * sourceIncrementCost (N width) w K (List.range (N width)) q
        (characterPolynomial (plaquette width face).scalar 1) := by
  let n := N width
  let f := characterPolynomial (plaquette width face).scalar 1
  let r := polyMul (jump n q) (jump n f)
  let W := productHeat n w K (List.range n)
  let D := sourceIncrementCost n w K (List.range n) q f
  let J := evenResponse w width face q
  let A := rawSourceMass width q
  have hs := character_supported
    (plaquette_supported width n (Nat.le_refl _) face).scalar 1
  have hr := supported_polyMul (jump_supported hq) (jump_supported hs)
  let P := productHeatCertificate n hw0 hw1 K hK (List.range n)
    (fun _ hi => List.mem_range.mp hi)
  have hD : (0 : Q') ≤ D := P.square_insertion_nonnegative r hr
  have hcs := weighted_cauchySchwarz (n+n) W r (sumTest n q f) P hr (sumTest_supported hq hs)
  have hb := sumTest_square_le_rawSourceMass n hw0 hw1 K hK (List.range n)
    (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi) hq
    (plaquetteSquareBound width face)
  have ha : quaternionHaar n (polyMul q q) ≈ A :=
    Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one (polyMul q q)))
  have hcap := Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (Q'.mul_eqv_congr_left 64 _ _ ha))
  have hj := quadratic_jump_mean w K width hK2 face hf q hq
  have hj2 := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hj)
    (Q'.mul_eqv_congr_left _ _ _ hj)
  have h := Q'.le_trans' _ _ _ (Q'.ge_of_eqv hj2)
    (Q'.le_trans' _ _ _ hcs (Q'.mul_le_mul_of_nonneg_left _ _ D hcap hD))
  apply Q'.le_of_mul_le_mul_left (c := 4) _ (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.const 4) (.mul (.var 0) (.var 0)))
    (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 0)))
    (by decide) (fun _ => J)))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.const 64) (.var 1)))
      (.mul (.const 4) (.mul (.mul (.const 16) (.var 1)) (.var 0)))
      (by decide) (fun | 0 => D | _ => A))))

/-- The SAME original terminal energy with the even-source correction retained.
No unproved positive source-moment reciprocal enters this cleared statement. -/
theorem padded_terminal_even_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width)
    (depth : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let g := terminalMessage w K width depth
    let q := projectedEndpointSource w K width g
    let f := characterPolynomial (plaquette width face).scalar 1
    64*rawSourceMass width q * energy w K width g f +
        evenResponse w width face q * evenResponse w width face q ≤
      32*rawSourceMass width q * plaquetteChannelCost width face w q := by
  dsimp only
  let g := terminalMessage w K width depth
  let q := projectedEndpointSource w K width g
  let f := characterPolynomial (plaquette width face).scalar 1
  let A := rawSourceMass width q
  let E := energy w K width g f
  let D := sourceIncrementCost (N width) w K (List.range (N width)) q f
  let C := plaquetteChannelCost width face w q
  have hq : SupportedQuaternionBlocks (N width) q :=
    familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))
  have hd := sourceIncrement_even_square hw0 hw1 K width hK2 hK face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf) q hq
  have hy := padded_terminal_plaquette_young_channels w K hK2 hwidth depth face hf
  have he : 64*A*E+16*A*D ≈ 32*A*C :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.mul (.mul (.const 64) (.var 0)) (.var 1))
        (.mul (.mul (.const 16) (.var 0)) (.var 2)))
      (.mul (.mul (.const 16) (.var 0)) (.add (.mul (.const 4) (.var 1)) (.var 2)))
      (by decide) (fun | 0 => A | 1 => E | _ => D))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (16*A) _ _ hy)
        (poly_identity_of_normal_eq
          (.mul (.mul (.const 16) (.var 0)) (.mul (.const 2) (.var 1)))
          (.mul (.mul (.const 32) (.var 0)) (.var 1)) (by decide)
          (fun | 0 => A | _ => C)))
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_left (64*A*E) _ _ hd) (Q'.le_of_eqv he)

/-- Normalize all source moments by the SAME original odd partition. The
raw source mass ratio remains explicit; it is not identified with one. -/
theorem padded_terminal_normalized_even_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width)
    (depth : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let r := Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth)
    64*(rawSourceMass width q*r)*normalizedEnergy hw0 hw1 K width hK depth
        (characterPolynomial (plaquette width face).scalar 1) +
        (evenResponse w width face q*r)*(evenResponse w width face q*r) ≤
      32*(rawSourceMass width q*r)*(plaquetteChannelCost width face w q*r) := by
  dsimp only
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let r := Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth)
  let A := rawSourceMass width q
  let E := energy w K width (terminalMessage w K width depth)
    (characterPolynomial (plaquette width face).scalar 1)
  let J := evenResponse w width face q
  let C := plaquetteChannelCost width face w q
  have h := Q'.mul_le_mul_of_nonneg_right _ _ (r*r)
    (padded_terminal_even_square hw0 hw1 K hK2 hK hwidth depth face hf)
    (SumOfSquares.q_mul_self_nonneg r)
  have hl : 64*(A*r)*(E*r)+(J*r)*(J*r) ≈ (64*A*E+J*J)*(r*r) :=
    poly_identity_of_normal_eq
      (.add (.mul (.mul (.const 64) (.mul (.var 0) (.var 3))) (.mul (.var 1) (.var 3)))
        (.mul (.mul (.var 2) (.var 3)) (.mul (.var 2) (.var 3))))
      (.mul (.add (.mul (.mul (.const 64) (.var 0)) (.var 1)) (.mul (.var 2) (.var 2)))
        (.mul (.var 3) (.var 3))) (by decide)
      (fun | 0 => A | 1 => E | 2 => J | _ => r)
  have hr : (32*A*C)*(r*r) ≈ 32*(A*r)*(C*r) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.const 32) (.var 0)) (.var 1)) (.mul (.var 2) (.var 2)))
      (.mul (.mul (.const 32) (.mul (.var 0) (.var 2))) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => A | 1 => C | _ => r)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))

#print axioms square_heat_moment
#print axioms quadratic_jump_mean
#print axioms sourceIncrement_even_square
#print axioms padded_terminal_even_square
#print axioms padded_terminal_normalized_even_square

end YMGap.Continuum.BF4ExactSlabFixedSpatialSourceEvenCancellation
