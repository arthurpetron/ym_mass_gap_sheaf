/-
# Source Young bound on the original padded plaquette energy

The exact fringe projection keeps the COMPLETE original source V*g.  The
symmetric product-kernel identity then replaces endpoint derivatives by a
one-ended squared-source cost, retaining an explicit nonnegative correction.
Neither this raw Haar cost nor its source square is identified with the
original odd-marginal variance.  Useful changing-scale control remains open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
import YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoung

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic
  (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage

private theorem projected_supported (w : Q') (K width : Nat) {g : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g) :
    SupportedQuaternionBlocks (N width) (projectedEndpointSource w K width g) :=
  familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width) hg)

/-- Exact identity with the original action, terminal source and energy.
The favorable source-increment correction has not been discarded. -/
theorem projected_young_identity (w : Q') (K width : Nat) (g f : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    let q := projectedEndpointSource w K width g
    (4 : Q') * energy w K width g f +
        sourceIncrementCost (N width) w K (List.range (N width)) q f ≈
      (2 : Q') * singleEndedCost (N width) w K (List.range (N width)) q f := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left 4 _ _
        (energy_projected_source w K width g f hg hf hind))
      (Q'.eqv_refl _))
    (four_mul_sourceEnergy_add_increment_eq_two_singleEnded
      (N width) w K (List.range (N width)) (fun _ hi => List.mem_range.mp hi)
      (projected_supported w K width hg) hf)

/-- The signed identity expressed through the ACTUAL images of f and f^2.
No spectral image or comparison with interacting variance is assumed. -/
theorem projected_young_moment_identity (w : Q') (K width : Nat) (g f : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    let q := projectedEndpointSource w K width g
    let P := productMap (N width) w K (List.range (N width))
    (4 : Q') * energy w K width g f +
        sourceIncrementCost (N width) w K (List.range (N width)) q f ≈
      (2 : Q') * quaternionHaar (N width) (polyMul (polyMul q q)
        (polyAdd (polyMul f f)
          (polyAdd (P (polyMul f f))
            (polyNeg (polyMul (cap 2) (polyMul f (P f))))))) :=
  Q'.eqv_trans _ _ _ (projected_young_identity w K width g f hg hf hind)
    (Q'.mul_eqv_congr_left 2 _ _
      (singleEndedCost_eq_weightedPolynomial (N width) w K (List.range (N width))
        (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi)
        (projected_supported w K width hg) hf))

/-- The actual projected source occurs at zeroth order only.  The heat
positivity cutoff is explicit, and no variance comparison is asserted. -/
theorem projected_energy_le_singleEndedCost {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (g f : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    (2 : Q') * energy w K width g f ≤
      singleEndedCost (N width) w K (List.range (N width))
        (projectedEndpointSource w K width g) f :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left 2 _ _
      (energy_projected_source w K width g f hg hf hind)))
    (two_mul_sourceEnergy_le_singleEndedCost (N width) hw0 hw1 K hK
      (List.range (N width)) (fun _ hi => List.mem_range.mp hi)
      (projected_supported w K width hg) hf)

/-- Strict padding supplies every independence premise for the literal
plaquette.  The full original terminal message remains in the source. -/
theorem padded_plaquette_energy_le_singleEndedCost {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : headCutoff w ≤ K) (n : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces base) :
    let g := terminalMessage w K width n
    let f := characterPolynomial (plaquette width face).scalar 1
    (2 : Q') * energy w K width g f ≤
      singleEndedCost (N width) w K (List.range (N width))
        (projectedEndpointSource w K width g) f :=
  projected_energy_le_singleEndedCost hw0 hw1 K width hK
    (terminalMessage w K width n) (characterPolynomial (plaquette width face).scalar 1)
    (terminalMessage_supported w K width n)
    (SU2QuaternionRelativeHeatPairGeometry.character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1)
    (plaquette_fringe_independent width face
      (spatialFaces_mono (Nat.le_of_lt hwidth) hf)
      (plaquette_active_after_padding hwidth face hf))

end YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoung

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoung.projected_young_identity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoung.projected_young_moment_identity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoung.projected_energy_le_singleEndedCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceYoung.padded_plaquette_energy_le_singleEndedCost
