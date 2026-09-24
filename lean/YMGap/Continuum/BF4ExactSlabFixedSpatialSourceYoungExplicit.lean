/-
# Explicit original-plaquette source-Young cost

The actual full-product images of the fundamental plaquette and its square
are tested against the COMPLETE projected source. The original energy and
its favorable source-increment correction are preserved. The raw squared
source moments below are not the interacting variance.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoung

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser (qpow)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (plaquette spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoung
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSquare
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (character_supported)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)
attribute [local irreducible] baseLinks

/-- Three explicit original Haar moments; no interacting normalization. -/
def plaquetteChannelCost (width : Nat) (face : Z4Plaq) (w : Q') (q : RatPoly) : Q' :=
  let f := characterPolynomial (plaquette width face).scalar 1
  let chi2 := characterPolynomial (plaquette width face).scalar 2
  H width (polyMul (polyMul q q) (polyMul f f)) +
    ((H width (polyMul (polyMul q q) polyOne) +
        qpow w 32 * H width (polyMul (polyMul q q) chi2)) +
      -((2 : Q') * (qpow w 12 * H width (polyMul (polyMul (polyMul q q) f) f))))

/-- Exact cost for the actual spatial face and arbitrary supported source. -/
theorem plaquette_singleEndedCost (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    singleEndedCost (N width) w K (List.range (N width)) q
        (characterPolynomial (plaquette width face).scalar 1) ≈
      plaquetteChannelCost width face w q := by
  let f := characterPolynomial (plaquette width face).scalar 1
  let chi2 := characterPolynomial (plaquette width face).scalar 2
  have hs : SupportedQuaternionBlocks (N width) f :=
    character_supported (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1
  have hq2 := supported_polyMul hq hq
  have hm := singleEndedCost_eq_moments (N width) w K (List.range (N width))
    (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi) hq hs
  have hsecond := Q'.eqv_trans _ _ _
    (plaquetteSquare_fullRange width face hf w K hK (polyMul q q) hq2)
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right (N width) (polyMul q q)
      polyOne (polySmul (qpow w 32) chi2))
      (Q'.add_eqv_congr_left _ _ _
        (quaternionHaar_polyMul_smul_right (N width) (qpow w 32) (polyMul q q) chi2)))
  have hthird := Q'.eqv_trans _ _ _
    (plaquette_fullRange width face hf w K (by omega)
      (polyMul (polyMul q q) f) (supported_polyMul hq2 hs))
    (quaternionHaar_polyMul_smul_right (N width) (qpow w 12)
      (polyMul (polyMul q q) f) f)
  exact Q'.eqv_trans _ _ _ hm
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr' hsecond
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _ hthird))))

/-- The original action and energy with their computed channel cost.
The source is the full fringe Haar projection of V*g, not a heat-evolved
replacement or a stationary-source hypothesis. -/
theorem projected_plaquette_young_channels (width : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (w : Q') (K : Nat) (hK : 2 ≤ K)
    (g : RatPoly) (hg : SupportedQuaternionBlocks (N width) g)
    (hind : ∀ i, i ∈ fringeBlocks width →
      QuaternionBlockIndependent i (characterPolynomial (plaquette width face).scalar 1)) :
    let f := characterPolynomial (plaquette width face).scalar 1
    let q := projectedEndpointSource w K width g
    (4 : Q') * energy w K width g f +
        sourceIncrementCost (N width) w K (List.range (N width)) q f ≈
      (2 : Q') * plaquetteChannelCost width face w q := by
  have hs := character_supported
    (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1
  have hq : SupportedQuaternionBlocks (N width) (projectedEndpointSource w K width g) :=
    familyProject_supported (fringeBlocks width)
      (supported_polyMul (spatialWeight_supported w K width) hg)
  exact Q'.eqv_trans _ _ _
    (projected_young_identity w K width g _ hg hs hind)
    (Q'.mul_eqv_congr_left 2 _ _
      (plaquette_singleEndedCost width face hf w K hK _ hq))

/-- Literal terminal-plaquette consumer. Strict spatial padding constructs
the independence witness; no source or observable-independence input remains. -/
theorem padded_terminal_plaquette_young_channels
    (w : Q') (K : Nat) (hK : 2 ≤ K) {base width : Nat} (hwidth : base < width)
    (n : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let g := terminalMessage w K width n
    let f := characterPolynomial (plaquette width face).scalar 1
    let q := projectedEndpointSource w K width g
    (4 : Q') * energy w K width g f +
        sourceIncrementCost (N width) w K (List.range (N width)) q f ≈
      (2 : Q') * plaquetteChannelCost width face w q :=
  projected_plaquette_young_channels width face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf) w K hK
    (terminalMessage w K width n) (terminalMessage_supported w K width n)
    (plaquette_fringe_independent width face
      (spatialFaces_mono (Nat.le_of_lt hwidth) hf)
      (plaquette_active_after_padding hwidth face hf))

end YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit.plaquette_singleEndedCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit.projected_plaquette_young_channels
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit.padded_terminal_plaquette_young_channels
