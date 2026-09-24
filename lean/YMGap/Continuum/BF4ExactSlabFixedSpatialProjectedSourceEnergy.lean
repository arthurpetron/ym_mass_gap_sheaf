/-
# Original temporal energy with the inactive source integrated exactly

For a fringe-independent observable, integrate the COMPLETE endpoint source
a=V*g before applying an angular estimate. The full temporal energy then has
no inactive residual. Moments in the original odd marginal are preserved by
the same reduction; the normalization and observable are not changed.

The projected source q=P_F(V*g) still carries all interactions. Its signed
correction H[q*f^2*(P_full q-q)] is retained. No source stationarity, useful
energy/variance ratio, spatial/scaling bound or continuum survival is proved.
-/

import YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (plaquette_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
  (transferStep_eq_productMap original_quadratic_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_lt fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure (labels)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily (labels_perm_range)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceSelection (face_link_mem_base)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry (FullyActive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFringeIndependent
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight activeBlocks terminalMessage

private theorem fringe_active_cover (width : Nat) :
    (fringeBlocks width ++ activeBlocks width).Perm (List.range (N width)) :=
  List.perm_append_comm.trans (by simpa only [labels] using labels_perm_range width)

private theorem fringe_not_active (width i : Nat) (hi : i ∈ fringeBlocks width) :
    i ∉ activeBlocks width := ((fringeBlocks_mem_iff width i).mp hi).2

def projectedEndpointSource (w : Q') (K width : Nat) (g : RatPoly) : RatPoly :=
  familyProject (fringeBlocks width) (endpointSource w K width g)

/-- Pin the generic weighted product form to the unchanged original transfer. -/
theorem energy_source_pin (w : Q') (K width : Nat) (g f : RatPoly) :
    energy w K width g f ≈
      sourceEnergy (N width) w K (activeBlocks width) (endpointSource w K width g) f := by
  let a := endpointSource w K width g
  have hfirst : weightedMass w K width
      (polyMul (polyMul g (transferStep w K width g)) (polyMul f f)) ≈
      sourceMoment (N width) w K (activeBlocks width) a (polyMul f f) := by
    unfold weightedMass sourceMoment
    rw [transferStep_eq_productMap]
    exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 2))))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2))) (.var 3))
      (by decide) (fun | 0 => spatialWeight w K width | 1 => g | 2 => f
                       | _ => productMap (N width) w K (activeBlocks width) a))
  have hs : RatPolyCoeffEqv (polyMul (spatialWeight w K width) (polyMul g f))
      (polyMul a f) := (RatPolyCoeffEqv.mul_assoc _ _ _).symm
  have hsecond := Q'.eqv_trans _ _ _ (original_quadratic_pin w K width (polyMul g f))
    (haar_of_coeff (hs.mul (productMap_congr (N width) w K (activeBlocks width) hs)))
  exact Q'.add_eqv_congr' hfirst (Q'.neg_eqv_congr _ _ hsecond)

/-- Exact original energy reduction. The source itself need NOT omit fringe. -/
theorem energy_projected_source (w : Q') (K width : Nat) (g f : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    energy w K width g f ≈
      sourceEnergy (N width) w K (List.range (N width))
        (projectedEndpointSource w K width g) f :=
  Q'.eqv_trans _ _ _ (energy_source_pin w K width g f)
    (sourceEnergy_project (N width) w K (activeBlocks width) (fringeBlocks width)
      (activeBlocks_lt width) (fringeBlocks_lt width) (fringe_not_active width)
      (fringe_active_cover width) (endpointSource w K width g) f
      (supported_polyMul (spatialWeight_supported w K width) hg) hf hind)

/-- Every independent insertion has the SAME original odd-marginal moment.
In particular this applies to 1, f and f*f, preserving mass and centering. -/
theorem oddMoment_projected_source (w : Q') (K width n : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (N width) p)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i p) :
    quaternionHaar (N width) (polyMul (marginalWeight w K width n) p) ≈
      sourceMoment (N width) w K (List.range (N width))
        (projectedEndpointSource w K width (terminalMessage w K width n)) p := by
  have ht : productMap (N width) w K (activeBlocks width)
      (endpointSource w K width (terminalMessage w K width n)) =
      terminalMessage w K width (n+1) :=
    (transferStep_eq_productMap w K width (terminalMessage w K width n)).symm.trans
      (terminalMessage_next w K width n)
  have hpin : quaternionHaar (N width) (polyMul (marginalWeight w K width n) p) ≈
      sourceMoment (N width) w K (activeBlocks width)
        (endpointSource w K width (terminalMessage w K width n)) p := by
    unfold sourceMoment
    rw [ht]
    exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => endpointSource w K width (terminalMessage w K width n)
           | 1 => terminalMessage w K width (n+1) | _ => p))
  exact Q'.eqv_trans _ _ _ hpin
    (sourceMoment_project (N width) w K (activeBlocks width) (fringeBlocks width)
      (activeBlocks_lt width) (fringeBlocks_lt width) (fringe_not_active width)
      (fringe_active_cover width) _ p
      (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n))
      hp hind)

/-- The original angular estimate after exact inactive-source integration:
NO separate fringe residual. The full projected source correction remains. -/
theorem energy_le_projectedSourceAngular_add_correction {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : sufficientCutoff w ≤ K) (g f : RatPoly)
    (hg : SupportedQuaternionBlocks (N width) g)
    (hf : SupportedQuaternionBlocks (N width) f) (hb : 0 < N width)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    energy w K width g f ≤
      (2*((1 : Q')-w)) * finSum (fun i => quaternionHaar (N width)
        (blockAngularSquare i (polyMul (projectedEndpointSource w K width g) f))) (N width) +
      sourceCorrection (N width) w K (List.range (N width))
        (projectedEndpointSource w K width g) f := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel hb
  have h := sourceEnergy_le_projectedAngular_add_correction (N width-1) hw0 hw1 K hK
    (activeBlocks width) (fringeBlocks width)
    (by simpa only [hN] using activeBlocks_lt width)
    (by simpa only [hN] using fringeBlocks_lt width) (fringe_not_active width)
    (by simpa only [hN] using fringe_active_cover width)
    (endpointSource w K width g) f
    (by simpa only [hN] using supported_polyMul (spatialWeight_supported w K width) hg)
    (by simpa only [hN] using hf) hind
  simp only [hN] at h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (energy_source_pin w K width g f)) h

/-- Literal active plaquette, with its independence proved from incidence.
Spatial padding supplies the activity guard in PlaquetteKinetic. -/
theorem plaquette_energy_le_projectedSourceAngular_add_correction {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : sufficientCutoff w ≤ K) (n : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces width) (hactive : FullyActive width face) :
    let g := terminalMessage w K width n
    let f := characterPolynomial (plaquette width face).scalar 1
    energy w K width g f ≤
      (2*((1 : Q')-w)) * finSum (fun i => quaternionHaar (N width)
        (blockAngularSquare i (polyMul (projectedEndpointSource w K width g) f))) (N width) +
      sourceCorrection (N width) w K (List.range (N width))
        (projectedEndpointSource w K width g) f := by
  have hl : (face.1, (dirsOf face.2).1) ∈ baseLinks width :=
    face_link_mem_base hf (by simp [edgesOf])
  have hb : 0 < N width := Nat.lt_of_le_of_lt (Nat.zero_le _)
    (List.idxOf_lt_length_of_mem hl)
  exact energy_le_projectedSourceAngular_add_correction hw0 hw1 K width hK
    (terminalMessage w K width n) (characterPolynomial (plaquette width face).scalar 1)
    (terminalMessage_supported w K width n)
    (SU2QuaternionRelativeHeatPairGeometry.character_supported
      (plaquette_supported width (N width) (Nat.le_refl _) face).scalar 1) hb
    (plaquette_fringe_independent width face hf hactive)

/-- Strict padding discharges the activity premise for a literal original
plaquette. No independence premise is imposed on either endpoint source. -/
theorem padded_plaquette_energy_le_projectedSourceAngular_add_correction {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat) {base width : Nat}
    (hwidth : base < width) (hK : sufficientCutoff w ≤ K) (n : Nat) (face : Z4Plaq)
    (hf : face ∈ spatialFaces base) :
    let g := terminalMessage w K width n
    let f := characterPolynomial (plaquette width face).scalar 1
    energy w K width g f ≤
      (2*((1 : Q')-w)) * finSum (fun i => quaternionHaar (N width)
        (blockAngularSquare i (polyMul (projectedEndpointSource w K width g) f))) (N width) +
      sourceCorrection (N width) w K (List.range (N width))
        (projectedEndpointSource w K width g) f :=
  plaquette_energy_le_projectedSourceAngular_add_correction hw0 hw1 K width hK n face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf)
    (plaquette_active_after_padding hwidth face hf)

end YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy.energy_source_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy.energy_projected_source
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy.oddMoment_projected_source
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy.energy_le_projectedSourceAngular_add_correction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy.plaquette_energy_le_projectedSourceAngular_add_correction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy.padded_plaquette_energy_le_projectedSourceAngular_add_correction
