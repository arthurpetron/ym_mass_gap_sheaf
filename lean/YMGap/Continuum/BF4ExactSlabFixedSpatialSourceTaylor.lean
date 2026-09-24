/-
# Computed full-product Taylor bound for the ORIGINAL temporal energy

The source is exactly q=P_F(V*g), with the original spatial action and
terminal data retained. Exact inactive integration precedes the Taylor
expansion. The resulting first-order coefficient and both signed remainder
budgets are computed; no source eigenvector equation, angular identification,
SAME-variance bound or changing-scale survival is asserted.

For fixed polynomials the generic budget has no nome/cutoff argument, but
this actual q depends on w,K,width,g. Thus no parameter-uniform estimate
follows from the displayed quadratic factor alone.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor
import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSourceTaylor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (face_link_mem_base)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor
open YMGap.Continuum.SU2HeatCutoffCasimirBound

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage

private theorem projected_supported (w : Q') (K width : Nat) (g : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g) :
    SupportedQuaternionBlocks (N width) (projectedEndpointSource w K width g) :=
  familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width) hg)

/-- Actual original energy, not a bare heat defect or surrogate marginal. -/
theorem energy_taylor (w : Q') (K width : Nat) (g f : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (hb : 0 < N width)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    let q := projectedEndpointSource w K width g
    energy w K width g f ≈
      ((1 : Q')-w)*sourceFirstOrder (N width-1) q f +
        (pairRemainder (N width-1) w K q (polyMul q (polyMul f f)) +
          -(pairRemainder (N width-1) w K (polyMul q f) (polyMul q f))) := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel hb
  have h := sourceEnergy_taylor (N width-1) w K
    (projectedEndpointSource w K width g) f
    (by simpa only [hN] using projected_supported w K width g hg)
    (by simpa only [hN] using hf)
  simp only [hN] at h
  exact Q'.eqv_trans _ _ _ (energy_projected_source w K width g f hg hf hind) h

/-- All source dependence remains inside explicit computed coefficients. -/
theorem energy_le_firstOrder_add_quadratic {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : sufficientCutoff w ≤ K) (g f : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (hb : 0 < N width)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    let q := projectedEndpointSource w K width g
    energy w K width g f ≤
      ((1 : Q')-w)*sourceFirstOrder (N width-1) q f +
        (((1 : Q')-w)*((1 : Q')-w))*sourceTaylorBudget (N width-1) q f := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel hb
  have h := sourceEnergy_le_firstOrder_add_quadratic (N width-1) hw0 hw1 K hK
    (projectedEndpointSource w K width g) f
    (by simpa only [hN] using projected_supported w K width g hg)
    (by simpa only [hN] using hf)
  simp only [hN] at h
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (energy_projected_source w K width g f hg hf hind)) h

/-- Strict padding supplies independence of the literal plaquette. Neither
endpoint source is assumed independent of the inactive fringe. -/
theorem padded_plaquette_energy_le_firstOrder_add_quadratic {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : sufficientCutoff w ≤ K) (n : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces base) :
    let g := terminalMessage w K width n
    let f := characterPolynomial (plaquette width face).scalar 1
    let q := projectedEndpointSource w K width g
    energy w K width g f ≤
      ((1 : Q')-w)*sourceFirstOrder (N width-1) q f +
        (((1 : Q')-w)*((1 : Q')-w))*sourceTaylorBudget (N width-1) q f := by
  have hf' := spatialFaces_mono (Nat.le_of_lt hwidth) hf
  have hl : (face.1, (dirsOf face.2).1) ∈ baseLinks width :=
    face_link_mem_base hf' (by simp [edgesOf])
  have hb : 0 < N width := Nat.lt_of_le_of_lt (Nat.zero_le _)
    (List.idxOf_lt_length_of_mem hl)
  exact energy_le_firstOrder_add_quadratic hw0 hw1 K width hK
    (terminalMessage w K width n) (characterPolynomial (plaquette width face).scalar 1)
    (terminalMessage_supported w K width n)
    (SU2QuaternionRelativeHeatPairGeometry.character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1) hb
    (plaquette_fringe_independent_after_padding hwidth face hf)

end YMGap.Continuum.BF4ExactSlabFixedSpatialSourceTaylor

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceTaylor.energy_taylor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceTaylor.energy_le_firstOrder_add_quadratic
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSourceTaylor.padded_plaquette_energy_le_firstOrder_add_quadratic
