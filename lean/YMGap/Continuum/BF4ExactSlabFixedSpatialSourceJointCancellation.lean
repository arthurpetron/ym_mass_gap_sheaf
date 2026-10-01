/-
# Both source tests retained in the original plaquette energy

The unit test and the symmetric quadratic test have a computed mixed Gram
entry. Centering the latter makes their simultaneous use valid. The exact
test norm and its supplied 64*A cap give two cleared energy inequalities.
Both retain the same complete projected terminal source. No source moment
is inverted and no favorable sign for a mixed response is assumed.

These raw heat-test moments are not the interacting centered variance.
Their useful relative scaling comparison and physical calibration stay open.
-/

import YMGap.Continuum.GNSUnitCenteredGram
import YMGap.Continuum.SU2QuaternionProductHeatSumGram
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceEvenCancellation

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSourceJointCancellation

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
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat productMap)
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.SU2QuaternionProductHeatSumTest
  (sumTest sumTest_supported sumTest_square_le_rawSourceMass)
open YMGap.Continuum.SU2QuaternionProductHeatJumpMean (productHeat_mass_one)
open YMGap.Continuum.SU2QuaternionProductHeatSumGram (sumTest_mean)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair weightedGNSData)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one haar_of_coeff)
open YMGap.Continuum.GNSUnitCenteredGram
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
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare (plaquette_fullRange)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDefect (plaquetteSquareBound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungCancellation
  (sourceResponse plaquette_jump_mean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceEvenCancellation
  (evenResponse quadratic_jump_mean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit
  (plaquetteChannelCost padded_terminal_plaquette_young_channels)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry (rawSourceMass)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks terminalMessage

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem qsub {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a-c ≈ b-d :=
  Q'.add_eqv_congr' h (Q'.neg_eqv_congr _ _ k)

/-- The mean of the symmetric test in normalized product heat. It uses a
linear raw source moment, not an original interacting mean. -/
def sumResponse (w : Q') (width : Nat) (face : Z4Plaq) (q : RatPoly) : Q' :=
  2*((1+qpow w 12)*H width
    (polyMul q (characterPolynomial (plaquette width face).scalar 1)))

/-- The actual uncentered norm of the second test, including shared variables. -/
def jointTestNorm (w : Q') (K width : Nat) (face : Z4Plaq) (q : RatPoly) : Q' :=
  let f := characterPolynomial (plaquette width face).scalar 1
  weightedPair (N width+N width) (productHeat (N width) w K (List.range (N width)))
    (sumTest (N width) q f) (sumTest (N width) q f)

/-- The centered cap for the supplied second test. It may be zero. -/
def jointVarianceCap (w : Q') (width : Nat) (face : Z4Plaq) (q : RatPoly) : Q' :=
  64*rawSourceMass width q-sumResponse w width face q*sumResponse w width face q

/-- Subtract the common unit component from the mixed response. -/
def jointResponse (w : Q') (width : Nat) (face : Z4Plaq) (q : RatPoly) : Q' :=
  2*evenResponse w width face q-sourceResponse w width face q*sumResponse w width face q

theorem plaquette_sum_mean (w : Q') (K width : Nat) (hK : 1 ≤ K)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    let f := characterPolynomial (plaquette width face).scalar 1
    weightedPair (N width+N width) (productHeat (N width) w K (List.range (N width)))
      (sumTest (N width) q f) polyOne ≈ sumResponse w width face q := by
  dsimp only
  let f := characterPolynomial (plaquette width face).scalar 1
  have hs := character_supported
    (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1
  have hp := Q'.eqv_trans _ _ _ (plaquette_fullRange width face hf w K hK q hq)
    (quaternionHaar_polyMul_smul_right (N width) (qpow w 12) q f)
  exact Q'.eqv_trans _ _ _
    (sumTest_mean (N width) w K (List.range (N width))
      (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi) hq hs)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 2 _ _ (Q'.add_eqv_congr_left _ _ _ hp))
      (poly_identity_of_normal_eq
        (.mul (.const 2) (.add (.var 0) (.mul (.var 1) (.var 0))))
        (.mul (.const 2) (.mul (.add (.const 1) (.var 1)) (.var 0)))
        (by decide) (fun | 0 => H width (polyMul q f) | _ => qpow w 12)))

private theorem norm_cap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (face : Z4Plaq)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    jointTestNorm w K width face q ≤ 64*rawSourceMass width q := by
  have h := sumTest_square_le_rawSourceMass (N width) hw0 hw1 K hK
    (List.range (N width)) (CayleyParentInj.range_nodup _)
    (fun _ hi => List.mem_range.mp hi) hq (plaquetteSquareBound width face)
  have hp : H width (polyMul q q) ≈ rawSourceMass width q :=
    Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.mul_one (polyMul q q)))
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left 64 _ _ hp))

theorem jointVarianceCap_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK1 : 1 ≤ K) (hK : headCutoff w ≤ K)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    (0 : Q') ≤ jointVarianceCap w width face q := by
  let n := N width
  let f := characterPolynomial (plaquette width face).scalar 1
  let W := productHeat n w K (List.range n)
  let G := weightedGNSData (n+n) W
    (productHeatCertificate n hw0 hw1 K hK (List.range n)
      (fun _ hi => List.mem_range.mp hi))
  have hs := character_supported
    (plaquette_supported width n (Nat.le_refl _) face).scalar 1
  let o : G.V := ⟨polyOne, supported_one _⟩
  let s : G.V := ⟨sumTest n q f, sumTest_supported hq hs⟩
  have ho : G.B o o ≈ 1 := productHeat_mass_one n w K (List.range n)
    (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi)
  have hm : G.B s o ≈ sumResponse w width face q :=
    plaquette_sum_mean w K width hK1 face hf q hq
  exact Q'.le_trans' _ _ _
    (centered_cap_nonnegative G o ho s (64*rawSourceMass width q)
      (norm_cap hw0 hw1 K width hK face q hq))
    (Q'.le_of_eqv (qsub (Q'.eqv_refl _) (qmul hm hm)))

private theorem terminal_budget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width)
    (depth : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base)
    (U : Q')
    (hU : jointTestNorm w K width face
      (projectedEndpointSource w K width (terminalMessage w K width depth)) ≤ U) :
    let g := terminalMessage w K width depth
    let q := projectedEndpointSource w K width g
    let J := sourceResponse w width face q
    let M := sumResponse w width face q
    let V := U-M*M
    4*V*energy w K width g (characterPolynomial (plaquette width face).scalar 1)+
        V*(J*J)+jointResponse w width face q*jointResponse w width face q ≤
      2*V*plaquetteChannelCost width face w q := by
  dsimp only
  let n := N width
  let g := terminalMessage w K width depth
  let q := projectedEndpointSource w K width g
  let f := characterPolynomial (plaquette width face).scalar 1
  let W := productHeat n w K (List.range n)
  let G := weightedGNSData (n+n) W
    (productHeatCertificate n hw0 hw1 K hK (List.range n)
      (fun _ hi => List.mem_range.mp hi))
  have hq : SupportedQuaternionBlocks n q :=
    familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))
  have hs := character_supported
    (plaquette_supported width n (Nat.le_refl _) face).scalar 1
  let o : G.V := ⟨polyOne, supported_one _⟩
  let r : G.V := ⟨polyMul (jump n q) (jump n f),
    supported_polyMul (jump_supported hq) (jump_supported hs)⟩
  let s : G.V := ⟨sumTest n q f, sumTest_supported hq hs⟩
  have ho : G.B o o ≈ 1 := productHeat_mass_one n w K (List.range n)
    (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi)
  have hf' := spatialFaces_mono (Nat.le_of_lt hwidth) hf
  have hj : G.B r o ≈ sourceResponse w width face q :=
    plaquette_jump_mean w K width (by omega) face hf' q hq
  have hm : G.B s o ≈ sumResponse w width face q :=
    plaquette_sum_mean w K width (by omega) face hf' q hq
  have hb : G.B r s ≈ 2*evenResponse w width face q :=
    quadratic_jump_mean w K width hK2 face hf' q hq
  have he : 4*energy w K width g f+G.B r r ≈
      2*plaquetteChannelCost width face w q :=
    padded_terminal_plaquette_young_channels w K hK2 hwidth depth face hf
  have h := joint_energy_budget G o ho r s U (energy w K width g f)
    (plaquetteChannelCost width face w q) hU he
  have hv := qsub (Q'.eqv_refl U) (qmul hm hm)
  have hx := qsub hb (qmul hj hm)
  have hl := Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (qmul (qmul (Q'.eqv_refl 4) hv) (Q'.eqv_refl (energy w K width g f)))
      (qmul hv (qmul hj hj)))
    (qmul hx hx)
  have hr := qmul (qmul (Q'.eqv_refl 2) hv)
    (Q'.eqv_refl (plaquetteChannelCost width face w q))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))

/-- The exact centered Gram denominator retains the original second-test norm. -/
theorem padded_terminal_exact_joint_budget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width)
    (depth : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let g := terminalMessage w K width depth
    let q := projectedEndpointSource w K width g
    let J := sourceResponse w width face q
    let M := sumResponse w width face q
    let V := jointTestNorm w K width face q-M*M
    4*V*energy w K width g (characterPolynomial (plaquette width face).scalar 1)+
        V*(J*J)+jointResponse w width face q*jointResponse w width face q ≤
      2*V*plaquetteChannelCost width face w q :=
  terminal_budget hw0 hw1 K hK2 hK hwidth depth face hf _ (Q'.le_refl' _)

/-- The supplied cap gives a simultaneous odd/even cancellation estimate,
with no inverse, source stationarity or nonzero-response premise. -/
theorem padded_terminal_joint_budget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width)
    (depth : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let g := terminalMessage w K width depth
    let q := projectedEndpointSource w K width g
    let J := sourceResponse w width face q
    let V := jointVarianceCap w width face q
    4*V*energy w K width g (characterPolynomial (plaquette width face).scalar 1)+
        V*(J*J)+jointResponse w width face q*jointResponse w width face q ≤
      2*V*plaquetteChannelCost width face w q := by
  have hq : SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width depth)) :=
    familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))
  exact terminal_budget hw0 hw1 K hK2 hK hwidth depth face hf _
    (norm_cap hw0 hw1 K width hK face _ hq)

/-- All factors are divided by the SAME original odd partition. The linear
raw response contributes J^2/Z, while the quadratic response contributes X/Z. -/
theorem padded_terminal_normalized_joint_budget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width)
    (depth : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let r := Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth)
    let J := sourceResponse w width face q
    let V := jointVarianceCap w width face q
    let X := jointResponse w width face q
    4*(V*r)*normalizedEnergy hw0 hw1 K width hK depth
        (characterPolynomial (plaquette width face).scalar 1)+
        (V*r)*((J*J)*r)+(X*r)*(X*r) ≤
      2*(V*r)*(plaquetteChannelCost width face w q*r) := by
  dsimp only
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let r := Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth)
  let V := jointVarianceCap w width face q
  let J := sourceResponse w width face q
  let X := jointResponse w width face q
  let E := energy w K width (terminalMessage w K width depth)
    (characterPolynomial (plaquette width face).scalar 1)
  let C := plaquetteChannelCost width face w q
  have h := Q'.mul_le_mul_of_nonneg_right _ _ (r*r)
    (padded_terminal_joint_budget hw0 hw1 K hK2 hK hwidth depth face hf)
    (SumOfSquares.q_mul_self_nonneg r)
  have hl : 4*(V*r)*(E*r)+(V*r)*((J*J)*r)+(X*r)*(X*r) ≈
      (4*V*E+V*(J*J)+X*X)*(r*r) :=
    poly_identity_of_normal_eq
      (.add (.add
        (.mul (.mul (.const 4) (.mul (.var 0) (.var 4))) (.mul (.var 1) (.var 4)))
        (.mul (.mul (.var 0) (.var 4)) (.mul (.mul (.var 2) (.var 2)) (.var 4))))
        (.mul (.mul (.var 3) (.var 4)) (.mul (.var 3) (.var 4))))
      (.mul (.add (.add (.mul (.mul (.const 4) (.var 0)) (.var 1))
        (.mul (.var 0) (.mul (.var 2) (.var 2)))) (.mul (.var 3) (.var 3)))
        (.mul (.var 4) (.var 4)))
      (by decide) (fun | 0 => V | 1 => E | 2 => J | 3 => X | _ => r)
  have hr : (2*V*C)*(r*r) ≈ 2*(V*r)*(C*r) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.mul (.var 2) (.var 2)))
      (.mul (.mul (.const 2) (.mul (.var 0) (.var 2))) (.mul (.var 1) (.var 2)))
      (by decide) (fun | 0 => V | 1 => C | _ => r)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr))

#print axioms sumResponse
#print axioms jointTestNorm
#print axioms jointVarianceCap
#print axioms jointResponse
#print axioms plaquette_sum_mean
#print axioms jointVarianceCap_nonnegative
#print axioms padded_terminal_exact_joint_budget
#print axioms padded_terminal_joint_budget
#print axioms padded_terminal_normalized_joint_budget

end YMGap.Continuum.BF4ExactSlabFixedSpatialSourceJointCancellation
