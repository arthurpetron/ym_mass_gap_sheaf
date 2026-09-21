/-
# The SAME terminal mass in the detector and original partition

At depth n+1, let M=H[V*T^n1]. The existing transfer sandwich gives
ell*M <= the plaquette detector and Z <= U*M^2, with ell>0 and U>0
depending only on nome and width. No endpoint weight is removed. These
unnormalized bounds are for cancellation against the SAME original Z;
they do not by themselves assert a positive normalized or limiting floor.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive
import YMGap.Continuum.QuaternionHaarSharpCharacterInterval

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder (spatialCertificate spatialInterval)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialResponseDual
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteResponsePositive
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalWindow (messageFloor)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headFloor headFloor_positive headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval (prefixCap prefixCap_nonnegative)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarSharpCharacterInterval

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage weightedMass

def spatialCap (w : Q') (width : Nat) : Q' :=
  (prefixCap w)^(spatialFaces width).length

def detectorScale (w : Q') (width : Nat) : Q' :=
  kineticFloor w width * (headFloor w)^(spatialFaces width).length

def partitionScale (w : Q') (width : Nat) : Q' :=
  1 + kineticCap w width * ((kineticCap w width * spatialCap w width) *
    (kineticCap w width * spatialCap w width))

theorem detectorScale_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) : (0 : Q') < detectorScale w width :=
  Q'.mul_pos (kineticFloor_positive hw0 hw1 width)
    (HKPos.pow_pos (headFloor_positive hw0 hw1) _)

theorem partitionScale_positive {w : Q'} (hw0 : (0 : Q') < w) (width : Nat) :
    (0 : Q') < partitionScale w width :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.add_le_self_of_nonneg 1 _ (Q'.mul_nonneg _ _
      (kineticCap_nonnegative hw0 width) (SumOfSquares.q_mul_self_nonneg _)))

private theorem weighted_interval_upper {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) {p r : RatPoly} {c : Q'}
    (P : Certificate (N width) p) (I : Interval (N width) r c) :
    weightedMass w K width (polyMul p r) ≤ c*weightedMass w K width p := by
  have hb : Q'.abs (quaternionHaar (N width)
      (polyMul (polyMul (spatialWeight w K width) p) r)) ≤ c*weightedMass w K width p := by
    unfold weightedMass
    exact I.weighted_haar_bound
      ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul P)
  have he : weightedMass w K width (polyMul p r) ≈
      quaternionHaar (N width) (polyMul (polyMul (spatialWeight w K width) p) r) := by
    unfold weightedMass
    exact haar_of_coeff (RatPolyCoeffEqv.mul_assoc _ _ _).symm
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _) hb)

theorem spatial_mass_cap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) : weightedMass w K width polyOne ≤ spatialCap w width := by
  unfold weightedMass
  have h := (spatialInterval hw0 hw1 K width (N width) (Nat.le_refl _)).haar_bound
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv
    (haar_of_coeff (RatPolyCoeffEqv.mul_one (spatialWeight w K width))))
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _) h)

private def messageInterval {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    Interval (N width) (terminalMessage w K width (n+1))
      (kineticCap w width * weightedMass w K width (terminalMessage w K width n)) where
  support := terminalMessage_supported w K width (n+1)
  nonnegative := Q'.mul_nonneg _ _ (kineticCap_nonnegative hw0 width)
    (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK n))
  upper := by
    rw [← terminalMessage_next]
    exact transferStepUpperCertificate hw0 hw1 K width hK
      (terminalMessage_supported w K width n) (terminalMessage_certificate hw0 hw1 K width hK n)
  lower := (Certificate.constant _ _ (Q'.mul_nonneg _ _ (kineticCap_nonnegative hw0 width)
    (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK n)))).add
      (terminalMessage_certificate hw0 hw1 K width hK (n+1))

/-- One-step mass growth uses the very same earlier weighted mass. -/
theorem terminal_mass_cap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    weightedMass w K width (terminalMessage w K width (n+1)) ≤
      (kineticCap w width * spatialCap w width) *
        weightedMass w K width (terminalMessage w K width n) := by
  let M := weightedMass w K width (terminalMessage w K width n)
  have h := weighted_interval_upper hw0 hw1 K width hK (Certificate.one _)
    (messageInterval hw0 hw1 K width hK n)
  have hc := Q'.mul_nonneg _ _ (kineticCap_nonnegative hw0 width)
    (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK n))
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (weightedMass_congr w K width (RatPolyCoeffEqv.one_mul _)))
    (Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (kineticCap w width*M) (spatial_mass_cap hw0 hw1 K width) hc)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
        (fun | 0 => kineticCap w width | 1 => M | _ => spatialCap w width)))))

/-- Upper bound for the SAME original odd partition, not a replaced denominator. -/
theorem oddMass_cap {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    oddMass w K width n ≤ kineticCap w width *
      (weightedMass w K width (terminalMessage w K width n) *
        weightedMass w K width (terminalMessage w K width n)) := by
  have h := weighted_interval_upper hw0 hw1 K width hK
    (terminalMessage_certificate hw0 hw1 K width hK n) (messageInterval hw0 hw1 K width hK n)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _)))
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)))

/-- Both this cap and detector_common_mass use exactly H[V*T^n1]. -/
theorem partition_common_mass {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) :
    oddMass w K width (n+1) ≤ partitionScale w width *
      (weightedMass w K width (terminalMessage w K width n) *
        weightedMass w K width (terminalMessage w K width n)) := by
  let M := weightedMass w K width (terminalMessage w K width n)
  let A := weightedMass w K width (terminalMessage w K width (n+1))
  let c := kineticCap w width * spatialCap w width
  have hA : (0 : Q') ≤ A := Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK (n+1))
  have hc : (0 : Q') ≤ c*M := Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _ (kineticCap_nonnegative hw0 width)
      (Q'.pow_nonneg _ (prefixCap_nonnegative hw0) _))
    (Q'.le_of_lt (terminalMessage_mass_positive hw0 hw1 K width hK n))
  have hsq := Q'.mul_le_mul_of_nonneg (terminal_mass_cap hw0 hw1 K width hK n)
    (terminal_mass_cap hw0 hw1 K width hK n) hc hA
  have he : kineticCap w width*((c*M)*(c*M)) ≈
      (kineticCap w width*(c*c))*(M*M) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.mul (.var 2) (.var 2)))
      (by decide) (fun | 0 => kineticCap w width | 1 => c | _ => M)
  have hslack : kineticCap w width*(c*c) ≤ partitionScale w width :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
  exact Q'.le_trans' _ _ _ (oddMass_cap hw0 hw1 K width hK (n+1))
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (kineticCap w width) hsq (kineticCap_nonnegative hw0 width))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
        (Q'.mul_le_mul_of_nonneg_right _ _ (M*M) hslack (SumOfSquares.q_mul_self_nonneg M))))

/-- The detector retains the same unsquared mass, for any rational center. -/
theorem detector_common_mass {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)
    (hactive : ∀ l, l ∈ edgesOf face → (baseLinks width).idxOf l ∈ activeBlocks width)
    (K : Nat) (hK : headCutoff w ≤ K) (hK1 : 1 ≤ K) (n : Nat) (m : Q') :
    detectorScale w width * weightedMass w K width (terminalMessage w K width n) ≤
      detector w K width (n+1) (source width face m) (dualTest hw0 width face m) := by
  have he : detectorScale w width * weightedMass w K width (terminalMessage w K width n) ≈
      messageFloor w K width (n+1)*(headFloor w)^(spatialFaces width).length :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => kineticFloor w width | 1 => (headFloor w)^(spatialFaces width).length
           | _ => weightedMass w K width (terminalMessage w K width n))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
    (detector_floor hw0 hw1 width face hf hactive K hK hK1 (n+1) m)

end YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds.detectorScale
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds.partitionScale
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds.detectorScale_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds.partitionScale_positive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds.spatial_mass_cap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds.terminal_mass_cap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds.oddMass_cap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds.partition_common_mass
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialResponseMassBounds.detector_common_mass
