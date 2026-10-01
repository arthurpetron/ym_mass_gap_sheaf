/-
# Centered angular reserve for the original finite transfer

The centered odd observable leaves the original energy unchanged. Its source
square splits exactly into that energy and the original spatially weighted
transfer quadratic. Full-output angular smoothing reserves part of the latter
quadratic without a fringe, family-size, or spatial-weight floor assumption.
This is finite additive control, not an angular fraction of the variance or a
scaling estimate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSmoothing
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferReserve

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment sourceEnergy)
open YMGap.Continuum.SU2QuaternionChannelAngularContraction (angularListSum)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted normalizedMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (original_quadratic_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy normalizedEnergy_nonnegative)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (energy_source_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (marginalMass_positive oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
  (centered_unprojected_square energy_shifted)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSmoothing
  (transferStep_angular_smoothing)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)

attribute [local irreducible] baseLinks spatialWeight terminalMessage

/-- Exact original odd-source partition after centering. The second term is
the actual spatially weighted transfer quadratic, with the complete `V*g`
source and original active heat. -/
theorem centered_transfer_quadratic_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let g := terminalMessage w K width depth
    let psi := oddCentered hw0 hw1 K width hK depth f
    energy w K width g f +
      weightedMass w K width
        (polyMul (polyMul g psi) (transferStep w K width (polyMul g psi))) ≈
      oddMass w K width depth * oddVariance hw0 hw1 K width hK depth f := by
  dsimp only
  let g := terminalMessage w K width depth
  let psi := oddCentered hw0 hw1 K width hK depth f
  let q := endpointSource w K width g
  let a := sourceMoment (N width) w K (activeBlocks width) q (polyMul psi psi)
  let b := H width (polyMul (polyMul q psi)
    (productMap (N width) w K (activeBlocks width) (polyMul q psi)))
  let t := polyMul g psi
  let quad := weightedMass w K width (polyMul t (transferStep w K width t))
  have hg := terminalMessage_supported w K width depth
  have hshift : energy w K width g f ≈ energy w K width g psi := by
    exact Q'.eqv_symm (show energy w K width g psi ≈ energy w K width g f from
      energy_shifted w K width hg hf
        (normalizedMoment (N width) (marginalWeight w K width depth) f
          (marginalMass_positive hw0 hw1 K width hK depth)))
  have henergy : energy w K width g psi ≈ a + -b := by
    exact energy_source_pin w K width g psi
  have hs : RatPolyCoeffEqv
      (polyMul (spatialWeight w K width) t) (polyMul q psi) :=
    (RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) g psi).symm
  have hquad : quad ≈ b :=
    Q'.eqv_trans _ _ _ (original_quadratic_pin w K width t)
      (haar_of_coeff (hs.mul
        (productMap_congr (N width) w K (activeBlocks width) hs)))
  have hmoment : a ≈
      oddMass w K width depth * oddVariance hw0 hw1 K width hK depth f :=
    centered_unprojected_square hw0 hw1 K width hK depth hf
  have hcancel : (a + -b) + b ≈ a :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => a | _ => b)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ hshift henergy) hquad)
    (Q'.eqv_trans _ _ _ hcancel hmoment)

/-- The centered transfer output has a genuine additive angular reserve.
Its cost is paid by the SAME original odd interacting variance and partition;
the theorem makes no lower-bound claim for the angular reserve itself. -/
theorem centered_transfer_angular_reserve {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let g := terminalMessage w K width depth
    let psi := oddCentered hw0 hw1 K width hK depth f
    energy w K width g f +
      ((1 : Q')-w) * angularListSum (N width) (List.range (N width))
        (transferStep w K width (polyMul g psi)) ≤
      oddMass w K width depth * oddVariance hw0 hw1 K width hK depth f := by
  dsimp only
  let g := terminalMessage w K width depth
  let psi := oddCentered hw0 hw1 K width hK depth f
  have ht : SupportedQuaternionBlocks (N width) (polyMul g psi) :=
    supported_polyMul (terminalMessage_supported w K width depth)
      (oddCentered_supported hw0 hw1 K width hK depth hf)
  have hs := transferStep_angular_smoothing (Q'.le_of_lt hw0)
    (Q'.le_of_lt hw1) K width (polyMul g psi) ht
  have hp := centered_transfer_quadratic_pin hw0 hw1 K width hK depth hf
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left (energy w K width g f) _ _ hs)
    (Q'.le_of_eqv hp)

/-- Normalize both terms by the SAME positive original partition. No source
or variance is inverted, and the complete centered output is retained. -/
theorem normalized_centered_transfer_angular_reserve {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let g := terminalMessage w K width depth
    let psi := oddCentered hw0 hw1 K width hK depth f
    normalizedEnergy hw0 hw1 K width hK depth f +
      (((1 : Q')-w) * angularListSum (N width) (List.range (N width))
        (transferStep w K width (polyMul g psi))) *
        Q'.recipPos (oddMass w K width depth)
          (oddMass_positive hw0 hw1 K width hK depth) ≤
      oddVariance hw0 hw1 K width hK depth f := by
  dsimp only
  let z := oddMass w K width depth
  let r := Q'.recipPos z (oddMass_positive hw0 hw1 K width hK depth)
  let v := oddVariance hw0 hw1 K width hK depth f
  have h := Q'.mul_le_mul_of_nonneg_right _ _ r
    (centered_transfer_angular_reserve hw0 hw1 K width hK depth hf)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hcancel : (z*v)*r ≈ v :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
        (fun | 0 => z | 1 => v | _ => r))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ v
          (Q'.mul_recipPos_eqv z (oddMass_positive hw0 hw1 K width hK depth)))
        (Q'.one_mul_eqv v))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_mul_eqv _ _ _).symm)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hcancel))

/-- SAME interacting variance pays the centered output's rescaled angular
energy. Dropping only the proved nonnegative original temporal energy does
not turn this into a lower fraction or a scaling-uniform physical gap. -/
theorem centered_output_angular_le_variance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let g := terminalMessage w K width depth
    let psi := oddCentered hw0 hw1 K width hK depth f
    (((1 : Q')-w) * angularListSum (N width) (List.range (N width))
      (transferStep w K width (polyMul g psi))) *
        Q'.recipPos (oddMass w K width depth)
          (oddMass_positive hw0 hw1 K width hK depth) ≤
      oddVariance hw0 hw1 K width hK depth f := by
  dsimp only
  have hn := normalizedEnergy_nonnegative hw0 hw1 K width hK depth hf
  exact Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hn)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_comm_eqv _ _))
      (normalized_centered_transfer_angular_reserve hw0 hw1 K width hK depth hf))

#print axioms centered_transfer_quadratic_pin
#print axioms centered_transfer_angular_reserve
#print axioms normalized_centered_transfer_angular_reserve
#print axioms centered_output_angular_le_variance

end YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferReserve
