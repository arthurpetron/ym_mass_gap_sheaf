/-
# Signed omitted-mode payment for the OWN-centered original Wilson square

The positive complementary omitted operator retains the mixed-minus-diagonal
cancellation. Its square-cap bound is summed over the ACTUAL passive Gram
channels of the fringe-projected original terminal source. Coefficient-one
channel contraction gives 16*rho*rawSourceMass, without replacing the odd
interacting law by a bare square. The existing full-width cutoff modulus and
the OWN variance floor then pay this signed component at every positive depth.

The modulus depends explicitly on nome, full width and tolerance, not square
perimeter or positive depth. It does not bound the old absolute leaf budget,
pay cubic/curvature debt, or establish changing-spacing survival or a mass gap.
-/

import YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted
import YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError
import YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
import YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment
import YMGap.Continuum.BF4DyadicWilsonSquareOddVarianceFloor
import YMGap.Continuum.BF4ExactSlabFixedSpatialRawSourceMassBound

namespace YMGap.Continuum.BF4DyadicWilsonSquareSignedChannelOmittedPayment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionFamilyHeatGramBessel
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSum_smul channelSource_supported)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError (channelSum_le)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (sourceOmitted)
open YMGap.Continuum.SU2QuaternionCyclicOmittedNorm (omittedRate)
open YMGap.Continuum.SU2QuaternionCyclicComplementaryOmitted
  (neg_sourceOmitted_le_squareBound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
  (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram (oddCentered)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment
  (paddedSquare_centered_squareBound)
open YMGap.Continuum.BF4DyadicWilsonSquareOddVarianceFloor
  (paddedSquare_oddVariance_floor)
open YMGap.Continuum.BF4DyadicWilsonSquareProjectionGain (rawSourceMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialRawSourceMassBound
  (rawSourceMassCutoff omitted_rawSourceMass_bound)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks

attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource
  sourceCharacter oddMass oddVariance

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem source_supported (w : Q') (K width depth : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width depth)) := by
  unfold projectedEndpointSource
  exact familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))

/-- Literal signed omitted loss, not the absolute omitted leaf sums. Every
channel uses the unchanged projected endpoint and SAME original odd center. -/
def signedChannelOmitted {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) : Q' :=
  let ids := spectatorBlocks scale width hwidth
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let psi := oddCentered hw0 hw1 K width hK depth
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
  channelSum (productChannels (N width) w K ids) (fun z =>
    -(sourceOmitted (N width-1) w K (channelSource ids q z) psi))

/-- The complete signed channel loss has the perimeter-independent factor
sixteen. No positivity of individual channel sources is assumed. -/
theorem signedChannelOmitted_le_rawMass {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    signedChannelOmitted hw0 hw1 K width hK depth scale hwidth ≤
      (16*omittedRate w K)*rawSourceMass w K width depth := by
  let ids := spectatorBlocks scale width hwidth
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let psi := oddCentered hw0 hw1 K width hK depth
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
  let cs := productChannels (N width) w K ids
  let value := fun z => H (N width)
    (polyMul (channelSource ids q z) (channelSource ids q z))
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hq := source_supported w K width depth
  have P := paddedSquare_centered_squareBound hw0 hw1 K width hK depth scale hwidth
  have hs := channelSum_le
    (fun z => -(sourceOmitted (N width-1) w K (channelSource ids q z) psi))
    (fun z => (16*omittedRate w K)*value z) cs
    (productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K ids)
    (fun c hc => by
      have hb := channelSource_supported (N width) w K ids
        (spectatorBlocks_lt scale width hwidth) hq c hc
      have hp := neg_sourceOmitted_le_squareBound (N width-1)
        (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) K (channelSource ids q c.2) psi
        (by simpa only [hN] using hb) (by simpa only [hN] using P)
      simpa only [hN, value] using hp)
  have he := channelSum_smul value (16*omittedRate w K) cs
  have hn := productChannels_familyProject_square_le (N width)
    (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) K ids
    (spectatorBlocks_nodup scale width hwidth) (spectatorBlocks_lt scale width hwidth)
    q hq
  have hrho : (0 : Q') ≤ omittedRate w K :=
    RGTransport.qpow_nonneg w (Q'.le_of_lt hw0) _
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (16*omittedRate w K) hn
    (Q'.mul_nonneg _ _ (by decide : (0 : Q') ≤ 16) hrho)
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hm)

private def oneSixteenth : Q' := Q'.mkPos 1 16 (by decide)

/-- Computed tolerance for the existing full-width raw-source modulus. -/
def omittedPaymentTolerance (w delta : Q') : Q' :=
  oneSixteenth*(delta*starRatio w)

private theorem tolerance_positive {w delta : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (hdelta : (0 : Q') < delta) :
    (0 : Q') < omittedPaymentTolerance w delta :=
  Q'.mul_pos (by decide : (0 : Q') < oneSixteenth)
    (Q'.mul_pos hdelta (starRatio_positive hw0 hw1))

private theorem sixteen_tolerance (w delta : Q') :
    16*omittedPaymentTolerance w delta ≈ delta*starRatio w := by
  unfold omittedPaymentTolerance
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv 16 oneSixteenth _))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide : 16*oneSixteenth ≈ (1 : Q')))
      (Q'.one_mul_eqv _))

/-- Explicit signed-cutoff payment modulus: nome/full width/tolerance remain
visible, and every positive depth and permitted perimeter use this SAME Nat. -/
def omittedPaymentCutoff {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (delta : Q') : Nat :=
  rawSourceMassCutoff hw0 hw1 width (omittedPaymentTolerance w delta)

theorem headCutoff_le_omittedPaymentCutoff {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat) (delta : Q') :
    headCutoff w ≤ omittedPaymentCutoff hw0 hw1 width delta := Nat.le_max_left _ _

/-- Signed omitted modes are paid by delta times the SAME OWN odd variance,
uniformly in positive depth and literal square perimeter at this computed
cutoff. Cubic/curvature and changing-width/nome/scaling control are not claimed. -/
theorem signedChannelOmitted_le_variance {w delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hdelta : (0 : Q') < delta)
    (width K : Nat) (hK : omittedPaymentCutoff hw0 hw1 width delta ≤ K)
    (n scale : Nat) (hwidth : side scale < width) :
    let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width delta) hK
    signedChannelOmitted hw0 hw1 K width hhead (n+1) scale hwidth *
      Q'.recipPos (oddMass w K width (n+1))
        (oddMass_positive hw0 hw1 K width hhead (n+1)) ≤
      delta*oddVariance hw0 hw1 K width hhead (n+1)
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width delta) hK
  let a := Q'.recipPos (oddMass w K width (n+1))
    (oddMass_positive hw0 hw1 K width hhead (n+1))
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ a
    (signedChannelOmitted_le_rawMass hw0 hw1 K width hhead (n+1) scale hwidth)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hraw := omitted_rawSourceMass_bound hw0 hw1 width
    (tolerance_positive hw0 hw1 hdelta) K hK n
  have hshape : ((16*omittedRate w K)*rawSourceMass w K width (n+1))*a ≈
      16*((omittedRate w K*rawSourceMass w K width (n+1))*a) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.mul (.const 16) (.var 0)) (.var 1)) (.var 2))
      (.mul (.const 16) (.mul (.mul (.var 0) (.var 1)) (.var 2))) (by decide)
      (fun | 0 => omittedRate w K | 1 => rawSourceMass w K width (n+1) | _ => a)
  have hpay := Q'.mul_le_mul_of_nonneg_left _ _ (16 : Q') hraw (by decide)
  have hv := Q'.mul_le_mul_of_nonneg_left _ _ delta
    (paddedSquare_oddVariance_floor hw0 hw1 K width hhead (n+1) scale hwidth)
    (Q'.le_of_lt hdelta)
  exact Q'.le_trans' _ _ _ hs
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hshape)
      (Q'.le_trans' _ _ _ hpay
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv (sixteen_tolerance w delta)) hv)))

#print axioms signedChannelOmitted
#print axioms signedChannelOmitted_le_rawMass
#print axioms omittedPaymentTolerance
#print axioms omittedPaymentCutoff
#print axioms headCutoff_le_omittedPaymentCutoff
#print axioms signedChannelOmitted_le_variance

end YMGap.Continuum.BF4DyadicWilsonSquareSignedChannelOmittedPayment
