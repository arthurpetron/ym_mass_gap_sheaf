/-
# Exact channel payment in the ORIGINAL chronological lag cost

The actual half-smoothed message keeps the stage OWN center. Normalize the
original Rayleigh split by BOTH chronological partitions before inserting
the exact long-square heat payment. The ENTIRE source increment remains;
only the boundary drift is paid by its computed terminal tolerance.
The endpoint raw reference square, endpoint OWN variance and filtered-start
variance are NOT identified. Their useful aggregate comparison on a justified
changing family is still open.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit
import YMGap.Continuum.BF4DyadicWilsonSquareExactVariancePayment
import YMGap.Continuum.BF4ExactSlabFixedSpatialSignedMultiplicationWindow
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
import YMGap.Constructive.CRealLogRatCongruence

namespace YMGap.Continuum.BF4WilsonAllNomeChronologicalExactChannelCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalPair_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio iterateStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive terminalMessage_next normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockRayleighSplit
  (clearedRayleighCost boundaryDrift signedMultiplicationCost original_block_rayleigh_split
    boundaryDrift_terminal_abs_le)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSignedMultiplicationWindow
  (originalPartitionProduct originalPartitionProduct_positive normalizedSignedMultiplicationCost)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse (energy_shifted)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison (comparisonEta)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry (squareChannelMass)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelExactResponse
  (responseQuarter squareChannelIncrement)
open YMGap.Continuum.BF4DyadicWilsonSquareExactVariancePayment
  (paddedSquare_energy_exact_variance_payment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyChannelSquareCredit
  (channelObservableSquareLinearVarianceCredit)
open YMGap.Continuum.SU2HeatExactSquareCreditWindow (exactSquareCredit)
open YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit (originalOwnBlockCost)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

private theorem cancel_product_left (x y r : Q') (hy : (0 : Q') < y)
    (hprod : (x*y)*r ≈ 1) : x*r ≈ Q'.recipPos y hy := by
  apply Q'.mul_left_cancel_of_pos hy
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (by decide) (fun | 0 => x | 1 => y | _ => r))
    (Q'.eqv_trans _ _ _ hprod (Q'.mul_recipPos_eqv y hy).symm)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width) (stage t : Nat)

local notation "K" => headCutoff w+stage
local notation "hK" => (Nat.le_add_right (headCutoff w) stage)
set_option quotPrecheck false in
local notation "f" => sourceCharacter width (paddedSquare scale width hwidth).edges 1
local notation "c" => middleRatio hw0 hw1 K width hK (stage+1) stage f
local notation "psi" => shifted f c
local notation "A" => terminalMessage w K width (stage+t)
local notation "b" => originalBlockTransfer w K width t
  (polyMul (terminalMessage w K width stage) psi)
local notation "Z0" => weightedMass w K width (polyMul A A)
local notation "Z1" => weightedMass w K width (polyMul A (transferStep w K width A))
local notation "r01" => Q'.recipPos (originalPartitionProduct w K width stage t)
  (originalPartitionProduct_positive hw0 hw1 K width hK stage t)
local notation "r" => Q'.recipPos (oddMass w K width (stage+t))
  (oddMass_positive hw0 hw1 K width hK (stage+t))
local notation "Cost" => originalOwnBlockCost hw0 hw1 scale width hwidth stage t
local notation "Signed" => normalizedSignedMultiplicationCost hw0 hw1 K width hK stage t f

attribute [local irreducible] baseLinks spatialWeight kineticWeight weightedMass
  terminalMessage middleRatio energy normalizedEnergy originalOwnBlockCost
  normalizedSignedMultiplicationCost oddMass oddVariance squareChannelMass
  squareChannelIncrement channelObservableSquareLinearVarianceCredit

include hw0 hw1 in
private theorem zeroMass_positive : (0 : Q') < Z0 :=
  terminalPair_positive hw0 hw1 K width hK (stage+t) (stage+t)

include hw0 hw1 in
private theorem oneMass_positive : (0 : Q') < Z1 := by
  rw [terminalMessage_next]
  exact terminalPair_positive hw0 hw1 K width hK (stage+t) (stage+t+1)

private theorem oddMass_oneMass_pin : oddMass w K width (stage+t) ≈ Z1 := by
  unfold oddMass
  rw [← terminalMessage_next]
  exact weightedMass_congr w K width (RatPolyCoeffEqv.mul_comm _ _)

private theorem cancel_zeroMass : Z0*r01 ≈ r :=
  Q'.eqv_trans _ _ _
    (cancel_product_left Z0 Z1 r01 (oneMass_positive hw0 hw1 width stage t)
      (Q'.mul_recipPos_eqv _ _))
    (Q'.recipPos_eqv_congr Z1 (oddMass w K width (stage+t))
      (oneMass_positive hw0 hw1 width stage t)
      (oddMass_positive hw0 hw1 K width hK (stage+t))
      (oddMass_oneMass_pin width stage t).symm)

private theorem cancel_oneMass : Z1*r01 ≈
    Q'.recipPos Z0 (zeroMass_positive hw0 hw1 width stage t) :=
  cancel_product_left Z1 Z0 r01 (zeroMass_positive hw0 hw1 width stage t)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ r01 (Q'.mul_comm_eqv Z1 Z0))
      (Q'.mul_recipPos_eqv _ _))

/-- Actual signed boundary drift divided by BOTH original chronological masses.
The observable still uses the stage mean, not the endpoint mean. -/
def originalBoundaryDrift : Q' := boundaryDrift w K width A psi*r01

/-- Raw endpoint square of the stage-centered observable. This is NOT the
filtered squared norm defining originalOwnBlockVariance. -/
def originalReferenceSquare : Q' :=
  weightedMass w K width (polyMul (polyMul A A) (polyMul psi psi))*
    Q'.recipPos Z0 (zeroMass_positive hw0 hw1 width stage t)

attribute [local irreducible] originalBoundaryDrift originalReferenceSquare

/-- Normalize the actual original split, preserving BOTH masses and the SAME
stage center in the drift and the complete signed multiplication correction. -/
theorem originalOwnBlockCost_energy_split :
    Cost ≈ normalizedEnergy hw0 hw1 K width hK (stage+t) f +
      originalBoundaryDrift hw0 hw1 scale width hwidth stage t + Signed := by
  have hf : SupportedQuaternionBlocks (N width) f :=
    sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hp := shifted_supported hf c
  have hg := terminalMessage_supported w K width stage
  have hA : originalBlockTransfer w K width t (terminalMessage w K width stage) = A := by
    unfold originalBlockTransfer terminalMessage
    exact (iterateStep_add (N width) (kineticWeight w K width)
      (spatialWeight w K width) stage t polyOne).symm
  have hsplit : clearedRayleighCost w K width A b ≈
      (Z0*energy w K width A f+boundaryDrift w K width A psi)+
        signedMultiplicationCost w K width A b psi :=
    Q'.eqv_trans _ _ _
      (by simpa only [hA] using original_block_rayleigh_split w K width t hg hp)
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left Z0 _ _
            (energy_shifted w K width (terminalMessage_supported w K width (stage+t)) hf c))
          (Q'.eqv_refl _)) (Q'.eqv_refl _))
  have hraw : Cost ≈
      ((Z0*energy w K width A f+boundaryDrift w K width A psi)+
        signedMultiplicationCost w K width A b psi)*r01 := by
    unfold originalOwnBlockCost
    exact Q'.mul_eqv_congr_right _ _ r01 hsplit
  have hdist :
      ((Z0*energy w K width A f+boundaryDrift w K width A psi)+
        signedMultiplicationCost w K width A b psi)*r01 ≈
      ((energy w K width A f*(Z0*r01))+boundaryDrift w K width A psi*r01)+
        signedMultiplicationCost w K width A b psi*r01 :=
    poly_identity_of_normal_eq
      (.mul (.add (.add (.mul (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4))
      (.add (.add (.mul (.var 1) (.mul (.var 0) (.var 4)))
        (.mul (.var 2) (.var 4))) (.mul (.var 3) (.var 4)))
      (by decide) (fun
        | 0 => Z0 | 1 => energy w K width A f
        | 2 => boundaryDrift w K width A psi
        | 3 => signedMultiplicationCost w K width A b psi | _ => r01)
  have he : energy w K width A f*(Z0*r01) ≈
      normalizedEnergy hw0 hw1 K width hK (stage+t) f := by
    unfold normalizedEnergy
    exact Q'.mul_eqv_congr_left _ _ _ (cancel_zeroMass hw0 hw1 width stage t)
  have hs : signedMultiplicationCost w K width A b psi*r01 ≈ Signed := by
    unfold normalizedSignedMultiplicationCost
    exact Q'.eqv_refl _
  have hd : boundaryDrift w K width A psi*r01 ≈
      originalBoundaryDrift hw0 hw1 scale width hwidth stage t := by
    unfold originalBoundaryDrift
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hraw
    (Q'.eqv_trans _ _ _ hdist (Q'.add_eqv_congr' (Q'.add_eqv_congr' he hd) hs))

/-- Only boundary drift is paid. The explicit raw endpoint square remains;
it is not substituted for the filtered-start norm. -/
theorem originalBoundaryDrift_upper (hdepth : 1 ≤ stage+t) :
    originalBoundaryDrift hw0 hw1 scale width hwidth stage t ≤
      comparisonEta hw0 hw1 width (stage+t-1)*
        originalReferenceSquare hw0 hw1 scale width hwidth stage t := by
  have hn : (stage+t-1)+1 = stage+t := Nat.sub_add_cancel hdepth
  have hp := shifted_supported
    (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1) c
  have habs := boundaryDrift_terminal_abs_le hw0 hw1 K width hK (stage+t-1) hp
  dsimp only at habs
  rw [hn] at habs
  have hb := Q'.le_trans' _ _ _ (Q'.le_abs_self _) habs
  have hnorm := Q'.mul_le_mul_of_nonneg_right _ _ r01 hb
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hshape :
      (comparisonEta hw0 hw1 width (stage+t-1)*Z1*
        weightedMass w K width (polyMul (polyMul A A) (polyMul psi psi)))*r01 ≈
      comparisonEta hw0 hw1 width (stage+t-1)*
        (weightedMass w K width (polyMul (polyMul A A) (polyMul psi psi))*(Z1*r01)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
      (.mul (.var 0) (.mul (.var 2) (.mul (.var 1) (.var 3))))
      (by decide) (fun
        | 0 => comparisonEta hw0 hw1 width (stage+t-1) | 1 => Z1
        | 2 => weightedMass w K width (polyMul (polyMul A A) (polyMul psi psi))
        | _ => r01)
  unfold originalBoundaryDrift originalReferenceSquare
  exact Q'.le_trans' _ _ _ hnorm (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hshape
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (cancel_oneMass hw0 hw1 width stage t)))))

/-- The exact variance payment reaches the ACTUAL chronological source cost.
Both signed corrections retain the stage center, while the endpoint OWN
variance is a separate retained credit. No macro survival budget is assumed. -/
theorem originalOwnBlockCost_exact_channel_payment
    (hdepth : 1 ≤ stage+t) (h2 : 2 ≤ K)
    (hcoefficient : (0 : Q') ≤ exactSquareCredit w (side scale)) :
    Cost + responseQuarter*(squareChannelIncrement w K scale width hwidth (stage+t)*r) +
        (HalfPow.half*exactSquareCredit w (side scale)*
          channelObservableSquareLinearVarianceCredit hw0 hw1 (side scale))*
          oddVariance hw0 hw1 K width hK (stage+t) f ≤
      HalfPow.half*(((1 : Q')-qpow w (32*side scale))*
        squareChannelMass w K scale width hwidth A*r) +
        originalBoundaryDrift hw0 hw1 scale width hwidth stage t + Signed := by
  have hn : (stage+t-1)+1 = stage+t := Nat.sub_add_cancel hdepth
  have hp := paddedSquare_energy_exact_variance_payment hw0 hw1 K width hK h2
    (stage+t-1) scale hwidth hcoefficient
  dsimp only at hp
  rw [hn] at hp
  let E := normalizedEnergy hw0 hw1 K width hK (stage+t) f
  let D := originalBoundaryDrift hw0 hw1 scale width hwidth stage t
  let S := Signed
  let I := responseQuarter*(squareChannelIncrement w K scale width hwidth (stage+t)*r)
  let V := (HalfPow.half*exactSquareCredit w (side scale)*
    channelObservableSquareLinearVarianceCredit hw0 hw1 (side scale))*
      oddVariance hw0 hw1 K width hK (stage+t) f
  let M := HalfPow.half*(((1 : Q')-qpow w (32*side scale))*
    squareChannelMass w K scale width hwidth A*r)
  have hcost : Cost ≈ E+D+S := originalOwnBlockCost_energy_split hw0 hw1 scale width hwidth stage t
  have hshape : Cost+I+V ≈ (E+I+V)+(D+S) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ V (Q'.add_eqv_congr_right _ _ I hcost))
      (poly_identity_of_normal_eq
        (.add (.add (.add (.add (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4))
        (.add (.add (.add (.var 0) (.var 3)) (.var 4)) (.add (.var 1) (.var 2)))
        (by decide) (fun | 0 => E | 1 => D | 2 => S | 3 => I | _ => V))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hshape)
    (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (D+S) hp)
      (Q'.le_of_eqv (Q'.add_assoc_eqv M D S).symm))

/-- Actual whole lag-cost ceiling with boundary drift PAID by its explicit
terminal tolerance. ENTIRE increment and complete signed multiplication
correction remain; no replacement of the raw reference norm by filtered norm. -/
theorem originalOwnBlockCost_exact_channel_boundary_paid
    (hdepth : 1 ≤ stage+t) (h2 : 2 ≤ K)
    (hcoefficient : (0 : Q') ≤ exactSquareCredit w (side scale)) :
    Cost + responseQuarter*(squareChannelIncrement w K scale width hwidth (stage+t)*r) +
        (HalfPow.half*exactSquareCredit w (side scale)*
          channelObservableSquareLinearVarianceCredit hw0 hw1 (side scale))*
          oddVariance hw0 hw1 K width hK (stage+t) f ≤
      HalfPow.half*(((1 : Q')-qpow w (32*side scale))*
        squareChannelMass w K scale width hwidth A*r) +
        comparisonEta hw0 hw1 width (stage+t-1)*
          originalReferenceSquare hw0 hw1 scale width hwidth stage t + Signed :=
  Q'.le_trans' _ _ _
    (originalOwnBlockCost_exact_channel_payment hw0 hw1 scale width hwidth stage t
      hdepth h2 hcoefficient)
    (Q'.add_le_add_right _ _ _ (Q'.add_le_add_left _ _ _
      (originalBoundaryDrift_upper hw0 hw1 scale width hwidth stage t hdepth)))

#print axioms originalBoundaryDrift
#print axioms originalReferenceSquare
#print axioms originalOwnBlockCost_energy_split
#print axioms originalBoundaryDrift_upper
#print axioms originalOwnBlockCost_exact_channel_payment
#print axioms originalOwnBlockCost_exact_channel_boundary_paid

end YMGap.Continuum.BF4WilsonAllNomeChronologicalExactChannelCost
