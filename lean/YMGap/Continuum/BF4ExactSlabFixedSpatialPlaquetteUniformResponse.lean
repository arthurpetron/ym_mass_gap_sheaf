/-
# A cutoff- and terminal-depth-independent ORIGINAL plaquette response floor

The explicit dual test has bounded cost. The original detector and partition
share exactly the terminal mass M: ell*M<=D and Z<=U*M^2. Keeping M until
normalization yields ell^2/((w^(-12)+5)*U), independent of cutoff and depth.
Nome and spatial width remain explicit. This finite estimate is not yet a
completed-response pin, spatial/spacing-uniform floor or continuum survival.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost
import YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion (spatialFaces_mono)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteKinetic (plaquette_active_after_padding)
open YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteDualCost
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks weightedMass terminalMessage

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem cancel_two (d C Z : Q') (hC : (0 : Q') < C) (hZ : (0 : Q') < Z) :
    ((d*(C*Z))*Q'.recipPos C hC)*Q'.recipPos Z hZ ≈ d :=
  Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (.var 4))
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 4))))
      (by decide) (fun | 0 => d | 1 => C | 2 => Z | 3 => Q'.recipPos C hC | _ => Q'.recipPos Z hZ))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left d _ _ (qmul (Q'.mul_recipPos_eqv C hC) (Q'.mul_recipPos_eqv Z hZ)))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left d _ _ (Q'.mul_one_eqv 1)) (Q'.mul_one_eqv d)))

/-- The common mass is retained until the last scalar comparison. -/
private theorem normalized_common_mass (ell M D C Z A U : Q')
    (hell : (0 : Q') ≤ ell) (hM : (0 : Q') ≤ M)
    (hC : (0 : Q') < C) (hZ : (0 : Q') < Z)
    (hA : (0 : Q') < A) (hU : (0 : Q') < U)
    (hD : ell*M ≤ D) (hcost : C ≤ A) (hpart : Z ≤ U*(M*M)) :
    (ell*ell)*Q'.recipPos (A*U) (Q'.mul_pos hA hU) ≤
      (D*D*Q'.recipPos C hC)*Q'.recipPos Z hZ := by
  let r := Q'.recipPos (A*U) (Q'.mul_pos hA hU)
  let delta := (ell*ell)*r
  have hdelta : (0 : Q') ≤ delta := Q'.mul_nonneg _ _
    (SumOfSquares.q_mul_self_nonneg ell) (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hD0 : (0 : Q') ≤ D := Q'.le_trans' _ _ _ (Q'.mul_nonneg _ _ hell hM) hD
  have hsquare := Q'.mul_le_mul_of_nonneg hD hD hD0 (Q'.mul_nonneg _ _ hell hM)
  have hc := Q'.mul_le_mul_of_nonneg hcost hpart (Q'.le_of_lt hA) (Q'.le_of_lt hZ)
  have hpin : delta*(A*(U*(M*M))) ≈ (ell*M)*(ell*M) := by
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.mul (.var 0) (.var 0)) (.var 1))
          (.mul (.var 2) (.mul (.var 3) (.mul (.var 4) (.var 4)))))
        (.mul (.mul (.var 0) (.var 4))
          (.mul (.mul (.var 0) (.var 4)) (.mul (.mul (.var 2) (.var 3)) (.var 1))))
        (by decide) (fun | 0 => ell | 1 => r | 2 => A | 3 => U | _ => M))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (ell*M) _ _
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (ell*M) _ _ (Q'.mul_recipPos_eqv (A*U) (Q'.mul_pos hA hU)))
            (Q'.mul_one_eqv _))) (Q'.eqv_refl _))
  have hcross : delta*(C*Z) ≤ D*D :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ delta hc hdelta)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin) hsquare)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (cancel_two delta C Z hC hZ))
    (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos Z hZ)
      (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.recipPos C hC) hcross
        (Q'.le_of_lt (Q'.recipPos_pos _ _))) (Q'.le_of_lt (Q'.recipPos_pos _ _)))

/-- Positive rational data depending on nome and width, NOT cutoff or depth. -/
def uniformFloor {w : Q'} (hw0 : (0 : Q') < w) (width : Nat) : Q' :=
  (detectorScale w width * detectorScale w width) *
    Q'.recipPos (costCap hw0 * partitionScale w width)
      (Q'.mul_pos (costCap_positive hw0) (partitionScale_positive hw0 width))

theorem uniformFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : (0 : Q') < uniformFloor hw0 width :=
  Q'.mul_pos (Q'.mul_pos (detectorScale_positive hw0 hw1 width)
    (detectorScale_positive hw0 hw1 width)) (Q'.recipPos_pos _ _)

/-- The computed preceding responseFloor dominates one fixed positive
constant for all late cutoffs and every terminal depth at least one. -/
theorem uniformFloor_le_responseFloor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) (m : Q')
    (hm0 : -(2 : Q') ≤ m) (hm1 : m ≤ (2 : Q')) :
    uniformFloor hw0 width ≤ responseFloor hw0 hw1 K width hK (n+1)
      (source width face m) (dualTest hw0 width face m) (dualTest_supported hw0 width face m) := by
  exact normalized_common_mass (detectorScale w width)
    (weightedMass w K width (terminalMessage w K width n))
    (detector w K width (n+1) (source width face m) (dualTest hw0 width face m))
    (1+testCost w K width (dualTest hw0 width face m)) (oddMass w K width (n+1))
    (costCap hw0) (partitionScale w width)
    (Q'.le_of_lt (detectorScale_positive hw0 hw1 width))
    (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK n))
    (regularizedCost_positive w (Q'.le_of_lt hw0) K width (dualTest_supported hw0 width face m))
    (oddMass_positive hw0 hw1 K width hK (n+1))
    (costCap_positive hw0) (partitionScale_positive hw0 width)
    (detector_common_mass hw0 hw1 width face hf hactive K hK hK1 n m)
    (one_add_plaquette_dualTest_cost_le_cap hw0 width face hf hactive K hK1 m hm0 hm1)
    (partition_common_mass hw0 hw1 K width hK n)

/-- SAME original normalized response, not an auxiliary kinetic expectation. -/
theorem window_response_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) (m : Q')
    (hm0 : -(2 : Q') ≤ m) (hm1 : m ≤ (2 : Q')) :
    uniformFloor hw0 width ≤ windowRatio hw0 hw1 K width hK (n+1) 1 (n+1)
      (polyMul (source width face m) (liftBoundary (N width) (source width face m))) :=
  Q'.le_trans' _ _ _ (uniformFloor_le_responseFloor hw0 hw1 width face hf hactive K hK hK1 n m hm0 hm1)
    (responseFloor_le_window hw0 hw1 K width hK (n+1)
      (source_supported width face m) (dualTest_supported hw0 width face m))

/-- Choose the original finite common endpoint mean. Its boundedness is
proved from the actual positive marginal, not assumed. -/
theorem centered_window_response_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) :
    let m := middleRatio hw0 hw1 K width hK ((n+1)+1) (n+1)
      (characterPolynomial (plaquette width face).scalar 1)
    uniformFloor hw0 width ≤ windowRatio hw0 hw1 K width hK (n+1) 1 (n+1)
      (polyMul (source width face m) (liftBoundary (N width) (source width face m))) := by
  have hb := plaquette_middleRatio_bounds hw0 hw1 K width hK ((n+1)+1) (n+1) face
  exact window_response_floor hw0 hw1 width face hf hactive K hK hK1 n _ hb.1 hb.2

/-- One fixed positive rational floor for all late K and n+1 terminal
depths, at the displayed fixed nome and padded width. -/
theorem padded_centered_window_response_floor {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {base width : Nat} (hwidth : base < width)
    (face : Z4Plaq) (hf : face ∈ spatialFaces base)
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) :
    let m := middleRatio hw0 hw1 K width hK ((n+1)+1) (n+1)
      (characterPolynomial (plaquette width face).scalar 1)
    uniformFloor hw0 width ≤ windowRatio hw0 hw1 K width hK (n+1) 1 (n+1)
      (polyMul (source width face m) (liftBoundary (N width) (source width face m))) :=
  centered_window_response_floor hw0 hw1 width face
    (spatialFaces_mono (Nat.le_of_lt hwidth) hf)
    (plaquette_active_after_padding hwidth face hf) K hK hK1 n

end YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse.uniformFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse.uniformFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse.uniformFloor_le_responseFloor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse.window_response_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse.centered_window_response_floor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse.padded_centered_window_response_floor
