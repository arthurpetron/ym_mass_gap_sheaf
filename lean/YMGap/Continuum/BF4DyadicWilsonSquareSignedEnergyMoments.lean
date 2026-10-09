/-
# Exact raw Wilson moments of the original signed channel debt

Constant-shift cancellation keeps the actual signed cubic, while literal
Wilson geometry evaluates angular and retained quadratic terms on the SAME
channels. The complete unpaid debt becomes two raw channel moments plus
signed cubic, with no Bessel enlargement or centered-eigenfunction shortcut.
Only signed omitted loss is paid; the remaining relative estimate is open.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareSignedEnergyPayment
import YMGap.Continuum.BF4DyadicWilsonSquareChannelMomentBalance
import YMGap.Continuum.SU2QuaternionCyclicSourceShift

namespace YMGap.Continuum.BF4DyadicWilsonSquareSignedEnergyMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare (activeCasimirPolynomial)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct (activeGamma)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.SU2QuaternionPassiveChannelRetainedCasimirSobolev
  (channelCurvature channelCasimirSquare)
open YMGap.Continuum.SU2QuaternionGeneralRetainedCasimir (oneThird)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels (squareChannelSource)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelMomentBalance
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
  (squareChannelMass squareChannelMoment)
open YMGap.Continuum.BF4DyadicWilsonSquareCasimirCurvature (perimeter)
open YMGap.Continuum.BF4DyadicWilsonSquareSignedEnergyPayment
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered)
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (marginalMass_positive oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4DyadicWilsonSquareSignedChannelOmittedPayment
  (omittedPaymentCutoff headCutoff_le_omittedPaymentCutoff)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSum_congr channelSum_smul channelSource_supported)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError (channelSum_add)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder (sourceCubic)
open YMGap.Continuum.SU2QuaternionCyclicSourceShift (sourceCubic_shifted)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks

attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource sourceCharacter

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier.baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem source_supported (w : Q') (K width depth : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width depth)) := by
  unfold projectedEndpointSource
  exact familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width depth))

/- The centered signed cubic in the actual passive channels is exactly the
raw Wilson cubic.  This is only finite constant-shift cancellation. -/
theorem signedChannelCubic_center_eq_raw {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
        (fun z => sourceCubic (N width-1) w
          (channelSource (spectatorBlocks scale width hwidth)
            (projectedEndpointSource w K width (terminalMessage w K width depth)) z)
          (oddCentered hw0 hw1 K width hK depth
            (sourceCharacter width (paddedSquare scale width hwidth).edges 1))) ≈
      channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
        (fun z => sourceCubic (N width-1) w
          (squareChannelSource w K scale width hwidth
            (terminalMessage w K width depth) z)
          (sourceCharacter width (paddedSquare scale width hwidth).edges 1)) := by
  let ids := spectatorBlocks scale width hwidth
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let psi := oddCentered hw0 hw1 K width hK depth f
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hq : SupportedQuaternionBlocks (N width) q := source_supported w K width depth
  have hf : SupportedQuaternionBlocks (N width) f := sourceCharacter_supported width
    (paddedSquare scale width hwidth).edges 1
  apply channelSum_congr
  intro c hc
  have hb : SupportedQuaternionBlocks (N width) (channelSource ids q c.2) :=
    channelSource_supported (N width) w K ids
      (spectatorBlocks_lt scale width hwidth) hq c hc
  have hs := sourceCubic_shifted (N width-1) (w := w)
    (Q'.le_of_lt hw0) hw1 (channelSource ids q c.2) f
    (by simpa only [hN] using hb) (by simpa only [hN] using hf)
    (normalizedMoment (N width) (marginalWeight w K width depth)
      f (marginalMass_positive hw0 hw1 K width hK depth))
  simpa only [ids, q, f, psi, oddCentered, squareChannelSource] using hs

private theorem channelSum_neg (value : RatPoly → Q') (cs : List GramChannel) :
    channelSum cs (fun z => -(value z)) ≈ -(channelSum cs value) :=
  Q'.eqv_trans _ _ _ (channelSum_congr _ (fun z => (-1)*value z) cs (fun z _ =>
    poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
      (by decide) (fun _ => value z.2)))
    (Q'.eqv_trans _ _ _ (channelSum_smul value (-1) cs)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => channelSum cs value)))

private theorem channelSum_budget (cs : List GramChannel) (a t : Q')
    (A R S C : RatPoly → Q') :
    channelSum cs (fun z => a*A z+(t*(-R z-oneThird*S z)+C z)) ≈
      a*channelSum cs A+
        (t*(-channelSum cs R-oneThird*channelSum cs S)+channelSum cs C) := by
  have hinner : channelSum cs (fun z => -R z-oneThird*S z) ≈
      -channelSum cs R-oneThird*channelSum cs S :=
    Q'.eqv_trans _ _ _ (channelSum_add (fun z => -R z) (fun z => -(oneThird*S z)) cs)
      (Q'.add_eqv_congr' (channelSum_neg R cs)
        (Q'.eqv_trans _ _ _ (channelSum_neg (fun z => oneThird*S z) cs)
          (Q'.neg_eqv_congr _ _ (channelSum_smul S oneThird cs))))
  exact Q'.eqv_trans _ _ _ (channelSum_add _ _ cs)
    (Q'.add_eqv_congr' (channelSum_smul A a cs)
      (Q'.eqv_trans _ _ _ (channelSum_add _ C cs)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (channelSum_smul _ t cs)
            (Q'.mul_eqv_congr_left t _ _ hinner)) (Q'.eqv_refl _))))

/-- No center or norm bound appears: this is the literal signed cubic in
the actual passive channels, before any diagonal/absolute enlargement. -/
def rawChannelCubic (w : Q') (K width depth scale : Nat)
    (hwidth : side scale < width) : Q' :=
  channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
    (fun z => sourceCubic (N width-1) w
      (squareChannelSource w K scale width hwidth (terminalMessage w K width depth) z)
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1))

/-- EXACT unpaid numerator, not an assumed variance-relative estimate.
M/F are the actual raw channel mass/square moment, not the odd marginal. -/
def rawMomentDebt (w : Q') (K width depth scale : Nat)
    (hwidth : side scale < width) : Q' :=
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let g := terminalMessage w K width depth
  (h+t)*(perimeter scale*(4*squareChannelMass w K scale width hwidth g-
    squareChannelMoment w K scale width hwidth g)) +
    (t*signedChannelMomentBalance w K scale width hwidth g+
      rawChannelCubic w K width depth scale hwidth)

/-- The complete remaining debt has no differentiated insertions or mean
correction: raw Wilson geometry and exact signed cubic cancellation suffice.
All sources/channels/action factors are unchanged, including depth zero. -/
theorem signedEnergyDebt_eq_rawMoments {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    signedEnergyDebt hw0 hw1 K width hK depth scale hwidth ≈
      rawMomentDebt w K width depth scale hwidth := by
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let psi := oddCentered hw0 hw1 K width hK depth f
  let mean := normalizedMoment (N width) (marginalWeight w K width depth) f
    (marginalMass_positive hw0 hw1 K width hK depth)
  let ids := spectatorBlocks scale width hwidth
  let cs := productChannels (N width) w K ids
  let A := fun z => weightedAngularEnergy (N width-1) (channelSource ids q z) psi
  let R := fun z => H (N width) (polyMul (polyMul (channelSource ids q z)
    (channelSource ids q z)) (activeCasimirPolynomial (List.range (N width))
      (activeGamma (List.range (N width)) psi psi)))
  let S := fun z =>
    let v := polyMul (channelSource ids q z)
      (activeCasimirPolynomial (List.range (N width)) psi)
    H (N width) (polyMul v v)
  let C := fun z => sourceCubic (N width-1) w (channelSource ids q z) psi
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hagg : signedEnergyDebt hw0 hw1 K width hK depth scale hwidth ≈
      (h+t)*channelSum cs A +
        (t*(-channelCurvature (N width-1) w K ids q psi-
          oneThird*channelCasimirSquare (N width-1) w K ids q psi)+channelSum cs C) := by
    simpa only [signedEnergyDebt, channelCurvature, channelCasimirSquare, hN,
      h, t, q, f, psi, ids, cs, A, R, S, C] using channelSum_budget cs (h+t) t A R S C
  have hang := paddedSquare_channelAngular_moments w K scale width hwidth
    (terminalMessage w K width depth) mean
  have hquad := paddedSquare_channel_secondOrder_balance w K scale width hwidth
    (terminalMessage w K width depth) mean
  have hcubic := signedChannelCubic_center_eq_raw hw0 hw1 K width hK depth scale hwidth
  exact Q'.eqv_trans _ _ _ hagg (Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_left (h+t) _ _ hang)
    (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left t _ _ hquad) hcubic))

/-- Paid-cutoff ORIGINAL energy in its exact raw M/F plus signed cubic form.
Only omitted modes have a variance payment; the displayed raw debt is OPEN. -/
theorem normalizedEnergy_raw_moment_cutoff {w delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hdelta : (0 : Q') < delta)
    (width K : Nat) (hK : omittedPaymentCutoff hw0 hw1 width delta ≤ K)
    (n scale : Nat) (hwidth : side scale < width) :
    let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width delta) hK
    normalizedEnergy hw0 hw1 K width hhead (n+1)
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1) ≤
      rawMomentDebt w K width (n+1) scale hwidth *
        Q'.recipPos (oddMass w K width (n+1))
          (oddMass_positive hw0 hw1 K width hhead (n+1)) +
      delta*oddVariance hw0 hw1 K width hhead (n+1)
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width delta) hK
  have hpaid := normalizedEnergy_signed_cutoff_payment hw0 hw1 hdelta width K hK n scale hwidth
  exact Q'.le_trans' _ _ _ hpaid (Q'.le_of_eqv (Q'.add_eqv_congr'
    (Q'.mul_eqv_congr_right _ _ _
      (signedEnergyDebt_eq_rawMoments hw0 hw1 K width hhead (n+1) scale hwidth))
    (Q'.eqv_refl _)))

#print axioms rawChannelCubic
#print axioms rawMomentDebt
#print axioms signedChannelCubic_center_eq_raw
#print axioms signedEnergyDebt_eq_rawMoments
#print axioms normalizedEnergy_raw_moment_cutoff

end YMGap.Continuum.BF4DyadicWilsonSquareSignedEnergyMoments
