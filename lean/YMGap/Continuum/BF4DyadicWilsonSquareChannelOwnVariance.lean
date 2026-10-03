/-
# Exact channel increment versus the ORIGINAL OWN variance

The constant-vector Gram floor for the actual active product heat retains
the square of the full spatially weighted source mean. Applied to the
literal OWN-centered square source, this gives a constant-one OWN variance
ceiling for the original temporal energy, with that favorable square kept.
The exact channel identity then exposes the same correction inside the
complete source increment. No raw channel norm is relabeled a variance.

This is finite original-source control, not an O(1/side) filtered relative
rate, a changing-family estimate, a scaling limit or a physical mass gap.
-/

import YMGap.Continuum.SU2QuaternionProductHeatChannelMeanGram
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferReserve
import YMGap.Continuum.BF4DyadicWilsonSquareChannelExactResponse

namespace YMGap.Continuum.BF4DyadicWilsonSquareChannelOwnVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
  (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionProductHeatChannelMeanGram
  (channelMeanSquares channelMeanSquares_pin channelMeanSquares_ge_haar_square)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
  (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_nodup activeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferPositive (original_quadratic_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredTransferReserve
  (centered_transfer_quadratic_pin)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelExactResponse
  (squareChannelIncrement exactChannelHeatCost paddedSquare_channel_exact_cost)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] baseLinks spatialWeight terminalMessage sourceCharacter

/-- The full ORIGINAL transfer quadratic dominates its SAME weighted source
mean square. No strict nome or head-cutoff hypothesis is required. -/
theorem transferStep_quadratic_ge_mean_square (w : Q') (hw : (0 : Q') ≤ w)
    (K width : Nat) (h : RatPoly) (hh : SupportedQuaternionBlocks (N width) h) :
    weightedMass w K width h * weightedMass w K width h ≤
      weightedMass w K width (polyMul h (transferStep w K width h)) := by
  let p := polyMul (spatialWeight w K width) h
  have hp : SupportedQuaternionBlocks (N width) p :=
    supported_polyMul (spatialWeight_supported w K width) hh
  have hgram : quaternionHaar (N width) p * quaternionHaar (N width) p ≤
      channelMeanSquares (N width) w K (activeBlocks width) p :=
    channelMeanSquares_ge_haar_square (N width) hw K (activeBlocks width)
      (activeBlocks_nodup width) (activeBlocks_lt width) p hp
  have hpin : weightedMass w K width (polyMul h (transferStep w K width h)) ≈
      channelMeanSquares (N width) w K (activeBlocks width) p :=
    Q'.eqv_trans _ _ _ (original_quadratic_pin w K width h)
      (channelMeanSquares_pin (N width) w K (activeBlocks width)
        (activeBlocks_lt width) p hp)
  exact Q'.le_trans' _ _ _ hgram (Q'.ge_of_eqv hpin)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (h2 : 2 ≤ K)
  (depth scale : Nat) (hwidth : side scale < width)

set_option quotPrecheck false in
local notation "f" => sourceCharacter width (paddedSquare scale width hwidth).edges 1
local notation "g" => terminalMessage w K width depth
local notation "psi" => oddCentered hw0 hw1 K width hK depth f
local notation "S" => oddMass w K width depth * oddVariance hw0 hw1 K width hK depth f
local notation "J" => weightedMass w K width
  (polyMul (polyMul g psi) (transferStep w K width (polyMul g psi)))
local notation "I" => squareChannelIncrement w K scale width hwidth depth
local notation "B" => exactChannelHeatCost w K scale width hwidth depth

attribute [local irreducible] weightedMass oddCentered oddVariance oddMass
  squareChannelIncrement exactChannelHeatCost

include h2 in
/-- Exact OWN-centered identity, retaining the original transfer response
and the complete channel increment. All original action factors remain. -/
theorem paddedSquare_channel_ownVariance_identity : I+4*S ≈ 2*B+4*J := by
  let e := energy w K width g f
  have hcenter : e+J ≈ S :=
    centered_transfer_quadratic_pin hw0 hw1 K width hK depth
      (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1)
  have hcost : 4*e+I ≈ 2*B :=
    paddedSquare_channel_exact_cost K width h2 depth scale hwidth
  have hreplace : I+4*S ≈ I+4*(e+J) :=
    Q'.add_eqv_congr' (Q'.eqv_refl I)
      (Q'.mul_eqv_congr_left 4 _ _ (Q'.eqv_symm hcenter))
  have hreorder : I+4*(e+J) ≈ (4*e+I)+4*J :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.mul (.const 4) (.add (.var 1) (.var 2))))
      (.add (.add (.mul (.const 4) (.var 1)) (.var 0)) (.mul (.const 4) (.var 2)))
      (by decide) (fun
        | 0 => I
        | 1 => e
        | _ => J)
  exact Q'.eqv_trans _ _ _ hreplace
    (Q'.eqv_trans _ _ _ hreorder
      (Q'.add_eqv_congr' hcost (Q'.eqv_refl (4*J))))

include h2 in
/-- Actual complete increment versus the SAME interacting variance, with
the favorable full-source mean square retained, not asserted to vanish. -/
theorem paddedSquare_channel_ownVariance_lower :
    2*B+4*(weightedMass w K width (polyMul g psi) *
      weightedMass w K width (polyMul g psi)) ≤ I+4*S := by
  have hh : SupportedQuaternionBlocks (N width) (polyMul g psi) :=
    supported_polyMul (terminalMessage_supported w K width depth)
      (oddCentered_supported hw0 hw1 K width hK depth
        (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1))
  have hmean := transferStep_quadratic_ge_mean_square w (Q'.le_of_lt hw0)
    K width (polyMul g psi) hh
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ (4 : Q') hmean (by decide)
  have hsum := Q'.add_le_add_left (2*B) _ _ hscaled
  exact Q'.le_trans' _ _ _ hsum
    (Q'.ge_of_eqv (paddedSquare_channel_ownVariance_identity
      hw0 hw1 K width hK h2 depth scale hwidth))

#print axioms transferStep_quadratic_ge_mean_square
#print axioms paddedSquare_channel_ownVariance_identity
#print axioms paddedSquare_channel_ownVariance_lower

end YMGap.Continuum.BF4DyadicWilsonSquareChannelOwnVariance
