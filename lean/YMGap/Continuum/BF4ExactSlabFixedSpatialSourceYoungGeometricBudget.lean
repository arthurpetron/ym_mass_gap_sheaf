/-
# A derivative-free geometric budget for the ORIGINAL plaquette energy

The complete projected terminal source is retained. Its exact Young cost
has an order-(1-w) geometric weight H[q^2(4-f^2)] and an order-(1-w)^2
raw source-square remainder. The signed source-increment correction is
preserved in the strongest estimate; discarding it uses the existing
positive-heat cutoff guard.

Neither raw source moment is the interacting centered variance. No bound
on their changing-cutoff/width/depth values, no normalized scaling rate,
and no continuum survival or mass gap is supplied here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry
import YMGap.Continuum.SU2HeatPlaquetteGeometricBudget

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungGeometricBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoung
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungExplicit
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteSourceGeometry
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung (sourceIncrementCost)
open YMGap.Continuum.SU2HeatPlaquetteGeometricBudget

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage energy

/-- Explicit zeroth-order source budget. Both moments use q squared, not
the interacting q*P(q) weight. -/
def geometricBudget (w : Q') (width : Nat) (face : Z4Plaq) (q : RatPoly) : Q' :=
  (8 : Q') * ((1 : Q') - w) * geometricSourceCost width face q +
    (960 : Q') * (((1 : Q') - w) * ((1 : Q') - w)) * rawSourceMass width q

/-- The actual computed channel cost, with its signed coefficients combined
before applying the two nonnegative source-moment estimates. -/
theorem plaquetteChannelCost_le_geometricBudget {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (width : Nat) (face : Z4Plaq) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    plaquetteChannelCost width face w q ≤ geometricBudget w width face q :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (plaquetteChannelCost_collected w width face q))
    (plaquette_geometric_cost_le hw0 hw1
      (rawSourceMass_nonnegative width q hq)
      (geometricSourceCost_nonnegative width face q hq))

private theorem terminal_projected_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width n)) :=
  familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))

/-- Strongest signed estimate on the ORIGINAL terminal plaquette energy.
The correction is not discarded; no source positivity or stationary-source
premise is needed. Strict padding supplies observable independence. -/
theorem padded_terminal_plaquette_signed_geometric_budget {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K : Nat) (hK : 2 ≤ K) {base width : Nat} (hwidth : base < width)
    (n : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let g := terminalMessage w K width n
    let f := characterPolynomial (plaquette width face).scalar 1
    let q := projectedEndpointSource w K width g
    (4 : Q') * energy w K width g f +
        sourceIncrementCost (N width) w K (List.range (N width)) q f ≤
      (2 : Q') * geometricBudget w width face q := by
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (padded_terminal_plaquette_young_channels w K hK hwidth n face hf))
    (Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q')
      (plaquetteChannelCost_le_geometricBudget hw0 hw1 width face _
        (terminal_projected_supported w K width n)) (by decide))

/-- The positive-kernel version drops the favorable correction. The
remaining two source moments and both cutoff guards are explicit. -/
theorem padded_terminal_plaquette_energy_geometric_budget {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK2 : 2 ≤ K) (hK : headCutoff w ≤ K)
    {base width : Nat} (hwidth : base < width)
    (n : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces base) :
    let g := terminalMessage w K width n
    let f := characterPolynomial (plaquette width face).scalar 1
    let q := projectedEndpointSource w K width g
    (2 : Q') * energy w K width g f ≤ geometricBudget w width face q := by
  dsimp only
  have hq := terminal_projected_supported w K width n
  exact Q'.le_trans' _ _ _
    (padded_plaquette_energy_le_singleEndedCost hw0 hw1 K hwidth hK n face hf)
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (plaquette_singleEndedCost width face
        (spatialFaces_mono (Nat.le_of_lt hwidth) hf) w K hK2 _ hq))
      (plaquetteChannelCost_le_geometricBudget (Q'.le_of_lt hw0)
        (Q'.le_of_lt hw1) width face _ hq))

end YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungGeometricBudget

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungGeometricBudget.geometricBudget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungGeometricBudget.plaquetteChannelCost_le_geometricBudget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungGeometricBudget.padded_terminal_plaquette_signed_geometric_budget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoungGeometricBudget.padded_terminal_plaquette_energy_geometric_budget
