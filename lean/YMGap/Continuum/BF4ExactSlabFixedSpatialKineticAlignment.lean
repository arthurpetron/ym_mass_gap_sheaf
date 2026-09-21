/-
# All-nome kinetic alignment in the ORIGINAL finite slab

The edge is K(x,y)V(x)V(y)g(x)g(y), with the actual g=T^n 1.
For every active temporal link, its fundamental relative-character mean
is at least coeffW(w,1) minus the explicit finite-cutoff endpoint error.
The SAME original odd-window partition normalizes the result. Neither width
nor terminal depth enters the coefficient or the computable cutoff threshold.

This controls one kinetic relative character, not arbitrary-observable
variance, a spatial spectral gap, continuum survival, or physical mass.
Nome dependence remains explicit; the cutoff is not uniform as w tends to 1.
-/

import YMGap.Continuum.SU2QuaternionHeatFusionQuadratic
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialKineticAlignment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
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
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry (scalarAt)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productHeat)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (edgeWeight)
open YMGap.Continuum.SU2QuaternionHeatFusionQuadratic
open YMGap.Continuum.SU2HeatFusionCutoffError

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks spatialWeight terminalMessage oddMass

/-- The actual central-edge insertion, with no replacement marginal. -/
def alignmentNumerator (w : Q') (K width depth i : Nat) : Q' :=
  quaternionHaar (N width+N width)
    (polyMul (edgeDensity w K width (terminalMessage w K width depth))
      (characterPolynomial (scalarAt (N width+i) i) 1))

/-- Cleared original-partition bound, valid at every width and terminal depth. -/
theorem alignment_cleared {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth i : Nat) (hi : i ∈ activeBlocks width) :
    coeffW w 1 * oddMass w K width depth ≤ alignmentNumerator w K width depth i +
      cutoffError w K * oddMass w K width depth := by
  have h := product_alignment (N width) hw0 hw1 K hK (activeBlocks width)
    (activeBlocks_lt width) i hi
    (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width depth))
    ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      (terminalMessage_certificate hw0 hw1 K width hK depth))
  have he : edgeWeight (N width) w K (activeBlocks width)
      (polyMul (spatialWeight w K width) (terminalMessage w K width depth)) =
      edgeDensity w K width (terminalMessage w K width depth) := by
    unfold edgeWeight edgeDensity productHeat
    rw [kineticWeight_eq_indexedProduct]
  rw [he] at h
  have hz := edge_total_mass w K width depth
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ hz))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz))))

/-- Normalize only by the existing positive odd-window partition. -/
def alignmentMean {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth i : Nat) : Q' :=
  alignmentNumerator w K width depth i *
    Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth)

private theorem cancel (c z : Q') (hz : (0 : Q') < z) :
    (c*z)*Q'.recipPos z hz ≈ c :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv z hz))
      (Q'.mul_one_eqv c))

/-- The finite normalized mean is bounded below by c_1 minus the literal
cutoff error. This is relative normalization, not an absolute partition bound. -/
theorem alignment_normalized {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth i : Nat) (hi : i ∈ activeBlocks width) :
    coeffW w 1 ≤ alignmentMean hw0 hw1 K width hK depth i + cutoffError w K := by
  have hz := oddMass_positive hw0 hw1 K width hK depth
  have h := Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos _ hz)
    (alignment_cleared hw0 hw1 K width hK depth i hi) (Q'.le_of_lt (Q'.recipPos_pos _ hz))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (cancel _ _ hz))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (cancel _ _ hz)))))

/-- A computed cutoff depending only on nome and tolerance, uniformly over
all spatial widths, terminal depths, and active selected temporal links. -/
theorem alignment_tolerance {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (epsilon : Q') (he : (0 : Q') < epsilon) (K width : Nat)
    (hK : headCutoff w ≤ K) (herror : cutoffErrorCutoff w epsilon ≤ K)
    (depth i : Nat) (hi : i ∈ activeBlocks width) :
    coeffW w 1 ≤ alignmentMean hw0 hw1 K width hK depth i + epsilon :=
  Q'.le_trans' _ _ _ (alignment_normalized hw0 hw1 K width hK depth i hi)
    (Q'.add_le_add_left _ _ _ (cutoffError_small hw0 hw1 epsilon he K herror))

end YMGap.Continuum.BF4ExactSlabFixedSpatialKineticAlignment

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticAlignment.alignmentNumerator
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticAlignment.alignment_cleared
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticAlignment.alignmentMean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticAlignment.alignment_normalized
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialKineticAlignment.alignment_tolerance
