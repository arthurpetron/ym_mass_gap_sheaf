/-
# Error-free kinetic alignment in the original finite slab

At the computed sufficient cutoff, the original spatial weight, terminal
message, complete kinetic product and odd-window partition satisfy exact
one-link alignment and a linear-nome chordal displacement bound.  The endpoint
source and partition are unchanged; no cutoff error or source replacement is
introduced.
-/

import YMGap.Continuum.SU2QuaternionProductHeatExactAlignment
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticAlignment

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialExactKineticAlignment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticAlignment
  (alignmentNumerator alignmentMean)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (scalarAt)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (edgeWeight)
open YMGap.Continuum.SU2QuaternionProductHeatExactAlignment
open YMGap.Continuum.SU2HeatCutoffCasimirBound (sufficientCutoff)
open YMGap.Continuum.QuaternionHaarChordalDifference
open YMGap.Continuum.QuaternionHaarWordDifference (difference)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks spatialWeight terminalMessage oddMass

private theorem edgeWeight_pin (w : Q') (K width depth : Nat) :
    edgeWeight (N width) w (K+1) (activeBlocks width)
        (polyMul (spatialWeight w (K+1) width)
          (terminalMessage w (K+1) width depth)) =
      edgeDensity w (K+1) width (terminalMessage w (K+1) width depth) := by
  unfold edgeWeight edgeDensity productHeat
  rw [kineticWeight_eq_indexedProduct]

/-- Cleared alignment for the literal original slab density and partition,
with no finite-cutoff error term. -/
theorem exact_alignment_cleared {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : sufficientCutoff w ≤ K+1)
    (width depth i : Nat) (hi : i ∈ activeBlocks width) :
    coeffW w 1 * oddMass w (K+1) width depth ≤
      alignmentNumerator w (K+1) width depth i := by
  have h := product_alignment_no_error (N width) (Q'.le_of_lt hw0) hw1 K hK
    (activeBlocks width) (activeBlocks_lt width) i hi
    (supported_polyMul (spatialWeight_supported w (K+1) width)
      (terminalMessage_supported w (K+1) width depth))
  rw [edgeWeight_pin] at h
  have hz := edge_total_mass w (K+1) width depth
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ hz)) h

private theorem cancel (c z : Q') (hz : (0 : Q') < z) :
    (c*z)*Q'.recipPos z hz ≈ c :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv z hz))
      (Q'.mul_one_eqv c))

/-- Exact normalized alignment at a cutoff satisfying both already computed
finite thresholds. -/
theorem exact_alignment_normalized {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hS : sufficientCutoff w ≤ K+1)
    (hH : headCutoff w ≤ K+1) (width depth i : Nat)
    (hi : i ∈ activeBlocks width) :
    coeffW w 1 ≤ alignmentMean hw0 hw1 (K+1) width hH depth i := by
  have hz := oddMass_positive hw0 hw1 (K+1) width hH depth
  have h := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos _ hz)
    (exact_alignment_cleared hw0 hw1 K hS width depth i hi)
    (Q'.le_of_lt (Q'.recipPos_pos _ hz))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (cancel _ _ hz)) h

/-- One computable onset packages the heat-head and fusion-endpoint guards. -/
def exactCutoff (w : Q') : Nat := max (headCutoff w) (sufficientCutoff w)

theorem exact_alignment_normalized_of_cutoff {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : exactCutoff w ≤ K+1)
    (width depth i : Nat) (hi : i ∈ activeBlocks width) :
    coeffW w 1 ≤ alignmentMean hw0 hw1 (K+1) width
      (Nat.le_trans (Nat.le_max_left _ _) hK) depth i :=
  exact_alignment_normalized hw0 hw1 K
    (Nat.le_trans (Nat.le_max_right _ _) hK)
    (Nat.le_trans (Nat.le_max_left _ _) hK) width depth i hi

/-- The actual one-link four-coordinate chordal increment is controlled by
`6(1-w)` times the SAME original odd-window mass. -/
theorem exact_link_displacement_nome_bound {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : sufficientCutoff w ≤ K+1)
    (width depth i : Nat) (hi : i ∈ activeBlocks width) :
    quaternionHaar (N width+N width)
      (polyMul (edgeDensity w (K+1) width (terminalMessage w (K+1) width depth))
        (polyQuaternionNorm (difference (PolyQuaternion.coordinateVariable i)
          (PolyQuaternion.coordinateVariable (N width+i))))) ≤
      (6*(1-w)) * oddMass w (K+1) width depth := by
  have h := product_displacement_nome_bound (N width) (Q'.le_of_lt hw0) hw1 K hK
    (activeBlocks width) (activeBlocks_lt width) i hi
    (supported_polyMul (spatialWeight_supported w (K+1) width)
      (terminalMessage_supported w (K+1) width depth))
  rw [edgeWeight_pin] at h
  have hz := edge_total_mass w (K+1) width depth
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hz))

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialExactKineticAlignment.exact_alignment_cleared
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialExactKineticAlignment.exact_alignment_normalized
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialExactKineticAlignment.exactCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialExactKineticAlignment.exact_alignment_normalized_of_cutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialExactKineticAlignment.exact_link_displacement_nome_bound

end YMGap.Continuum.BF4ExactSlabFixedSpatialExactKineticAlignment
