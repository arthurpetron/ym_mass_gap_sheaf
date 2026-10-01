/-
# A retained source-moment square in the ORIGINAL plaquette energy bound

Cauchy--Schwarz lower-bounds the favorable source-increment correction by
the square of its actual heat-pair mean. The plaquette's proved heat image
computes this mean as 2*(1-w^12)*H[q*f]. The complete projected terminal
source is retained; it is not replaced by an arbitrary stationary source.

The result improves the raw Young ceiling by an explicit nonnegative
source-dependent subtraction. Its normalized consumer uses the SAME odd
partition. H[q*f] is NOT the interacting mean/variance (whose density is
q*Pq); no relative scaling gain or continuum survival is asserted.
-/

import YMGap.Continuum.SU2QuaternionProductHeatJumpMean
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat productMap)
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung (sourceIncrementCost)
open YMGap.Continuum.SU2QuaternionProductHeatJumpMean (jump_mean productHeat_mass_one)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
  (weightedPair weighted_cauchySchwarz)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one)
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
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit
  (plaquetteChannelCost padded_terminal_plaquette_young_channels)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks terminalMessage

/-- The computed mean of the complete source/observable jump product. -/
def sourceResponse (w : Q') (width : Nat) (face : Z4Plaq) (q : RatPoly) : Q' :=
  2*((1 + -(qpow w 12))*
    H width (polyMul q (characterPolynomial (plaquette width face).scalar 1)))

theorem plaquette_jump_mean (w : Q') (K width : Nat) (hK : 1 ≤ K)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    let f := characterPolynomial (plaquette width face).scalar 1
    weightedPair (N width+N width) (productHeat (N width) w K (List.range (N width)))
        (polyMul (jump (N width) q) (jump (N width) f)) polyOne ≈
      sourceResponse w width face q := by
  dsimp only
  let f := characterPolynomial (plaquette width face).scalar 1
  have hs := character_supported
    (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1
  have hp := Q'.eqv_trans _ _ _ (plaquette_fullRange width face hf w K hK q hq)
    (quaternionHaar_polyMul_smul_right (N width) (qpow w 12) q f)
  exact Q'.eqv_trans _ _ _ (jump_mean (N width) w K (List.range (N width))
    (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi) hq hs)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left 2 _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ hp)))
      (poly_identity_of_normal_eq
        (.mul (.const 2) (.add (.var 0) (.neg (.mul (.var 1) (.var 0)))))
        (.mul (.const 2) (.mul (.add (.const 1) (.neg (.var 1))) (.var 0)))
        (by decide) (fun | 0 => H width (polyMul q f) | _ => qpow w 12)))

/-- A proved lower square for the favorable correction, rather than merely
discarding it by nonnegativity. No mean or Perron equation is assumed. -/
theorem sourceIncrement_ge_response_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK1 : 1 ≤ K) (hK : headCutoff w ≤ K)
    (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    sourceResponse w width face q * sourceResponse w width face q ≤
      sourceIncrementCost (N width) w K (List.range (N width)) q
        (characterPolynomial (plaquette width face).scalar 1) := by
  let f := characterPolynomial (plaquette width face).scalar 1
  let r := polyMul (jump (N width) q) (jump (N width) f)
  let W := productHeat (N width) w K (List.range (N width))
  have hr := supported_polyMul (jump_supported hq)
    (jump_supported (character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1))
  have hc := weighted_cauchySchwarz (N width+N width) W r polyOne
    (productHeatCertificate (N width) hw0 hw1 K hK (List.range (N width))
      (fun _ hi => List.mem_range.mp hi)) hr (supported_one _)
  have hm := productHeat_mass_one (N width) w K (List.range (N width))
    (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi)
  have hj := plaquette_jump_mean w K width hK1 face hf q hq
  have hleft := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hj)
    (Q'.mul_eqv_congr_left _ _ _ hj)
  have hright := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hm)
    (Q'.mul_one_eqv (weightedPair (N width+N width) W r r))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hc (Q'.le_of_eqv hright))

/-- The complete original terminal source supplies the response in this
signed Young ceiling. The literal energy is unchanged; improvement is
strict only if the computed response is nonzero. -/
theorem padded_terminal_energy_retained_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width)
    (depth : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let g := terminalMessage w K width depth
    let q := projectedEndpointSource w K width g
    let f := characterPolynomial (plaquette width face).scalar 1
    4*energy w K width g f + sourceResponse w width face q * sourceResponse w width face q ≤
      2*plaquetteChannelCost width face w q := by
  dsimp only
  have hq : SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width depth)) :=
    familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))
  have hlow := sourceIncrement_ge_response_square hw0 hw1 K width (by omega) hK
    face (spatialFaces_mono (Nat.le_of_lt hwidth) hf) _ hq
  exact Q'.le_trans' _ _ _ (Q'.add_le_add_left _ _ _ hlow)
    (Q'.le_of_eqv (padded_terminal_plaquette_young_channels w K hK2 hwidth depth face hf))

/-- Normalize by precisely the original odd partition. The retained square
is not relabeled as variance or an interacting mean. -/
theorem padded_terminal_normalized_retained_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width)
    (depth : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let q := projectedEndpointSource w K width (terminalMessage w K width depth)
    let r := Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth)
    4*normalizedEnergy hw0 hw1 K width hK depth
        (characterPolynomial (plaquette width face).scalar 1) +
        (sourceResponse w width face q * sourceResponse w width face q)*r ≤
      2*(plaquetteChannelCost width face w q*r) := by
  dsimp only
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let r := Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth)
  have h := Q'.mul_le_mul_of_nonneg_right _ _ r
    (padded_terminal_energy_retained_square hw0 hw1 K hK2 hK hwidth depth face hf)
    (Q'.le_of_lt (Q'.recipPos_pos _ (oddMass_positive hw0 hw1 K width hK depth)))
  have hl := poly_identity_of_normal_eq
    (.add (.mul (.const 4) (.mul (.var 0) (.var 2))) (.mul (.var 1) (.var 2)))
    (.mul (.add (.mul (.const 4) (.var 0)) (.var 1)) (.var 2)) (by decide)
    (fun | 0 => energy w K width (terminalMessage w K width depth)
                  (characterPolynomial (plaquette width face).scalar 1)
         | 1 => sourceResponse w width face q * sourceResponse w width face q | _ => r)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ h
      (Q'.le_of_eqv (Q'.mul_assoc_eqv 2 (plaquetteChannelCost width face w q) r)))

#print axioms plaquette_jump_mean
#print axioms sourceIncrement_ge_response_square
#print axioms padded_terminal_energy_retained_square
#print axioms padded_terminal_normalized_retained_square

end YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungCancellation
