/-
# Signed original energy payment with the omitted channel separated

This leaf keeps the original signed cubic correction and the literal retained
Casimir curvature/square together.  Only the complementary omitted term is
paid by the existing same-OWN-variance consumer; the remaining signed debt is
not bounded here.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareActiveChannelSobolev
import YMGap.Continuum.BF4DyadicWilsonSquareSignedChannelOmittedPayment
import YMGap.Continuum.SU2QuaternionCyclicSecondOrder
import YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization

namespace YMGap.Continuum.BF4DyadicWilsonSquareSignedEnergyPayment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare (activeCasimirPolynomial)
open YMGap.Continuum.SU2QuaternionActiveCasimirProduct (activeGamma)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceEnergy)
open YMGap.Continuum.BF4DyadicWilsonSquareActiveChannelSobolev
open YMGap.Continuum.BF4DyadicWilsonSquareSignedChannelOmittedPayment
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource energy_projected_source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported oddCentered_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (marginalMass_positive oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse (energy_shifted)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage (paddedSquare_fringe_independent)
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSum_congr channelSum_smul channelSource_supported)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError (channelSum_add channelSum_le)
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
  (sourceCubic sourceOmitted sourceSecondMoment sourceEnergy_secondOrder)
open YMGap.Continuum.SU2QuaternionPassiveChannelRetainedCasimirSobolev
  (channelCurvature channelCasimirSquare)
open YMGap.Continuum.SU2QuaternionGeneralRetainedCasimir
  (sourceSecondMoment_le_retainedCasimir oneThird)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks

attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource
  sourceCharacter oddMass oddVariance

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

/-- The whole remaining signed debt on the ACTUAL channels. No upper bound
against OWN variance is assumed. The literal Casimir acts on the centered
observable; no centered eigenfunction identity is substituted. -/
def signedEnergyDebt {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) : Q' :=
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let q := projectedEndpointSource w K width (terminalMessage w K width depth)
  let f := oddCentered hw0 hw1 K width hK depth
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
  let ids := spectatorBlocks scale width hwidth
  channelSum (productChannels (N width) w K ids) (fun z =>
    let b := channelSource ids q z
    let R := H (N width) (polyMul (polyMul b b)
      (activeCasimirPolynomial (List.range (N width))
        (activeGamma (List.range (N width)) f f)))
    let v := polyMul b (activeCasimirPolynomial (List.range (N width)) f)
    (h+t)*weightedAngularEnergy (N width-1) b f +
      (t*(-R-oneThird*H (N width) (polyMul v v))+sourceCubic (N width-1) w b f))

private theorem channel_signed_second_order {w : Q'}
    (_hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K tail : Nat)
    (b f : RatPoly) (hb : SupportedQuaternionBlocks (tail+1) b)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    sourceEnergy (tail+1) w K (List.range (tail+1)) b f ≤
      ((1 : Q')-w + HalfPow.half*((1-w)*(1-w))) *
        weightedAngularEnergy tail b f +
      (HalfPow.half*((1-w)*(1-w))) *
        (-H (tail+1) (polyMul (polyMul b b)
          (activeCasimirPolynomial (List.range (tail+1))
            (activeGamma (List.range (tail+1)) f f))) -
          oneThird*H (tail+1) (polyMul
            (polyMul b (activeCasimirPolynomial (List.range (tail+1)) f))
            (polyMul b (activeCasimirPolynomial (List.range (tail+1)) f)))) +
      sourceCubic tail w b f - sourceOmitted tail w K b f := by
  let h := (1 : Q')-w
  let t := HalfPow.half*(h*h)
  let A := weightedAngularEnergy tail b f
  let R := H (tail+1) (polyMul (polyMul b b)
    (activeCasimirPolynomial (List.range (tail+1))
      (activeGamma (List.range (tail+1)) f f)) )
  let S := H (tail+1) (polyMul
    (polyMul b (activeCasimirPolynomial (List.range (tail+1)) f))
    (polyMul b (activeCasimirPolynomial (List.range (tail+1)) f)))
  have ht : (0 : Q') ≤ t := Q'.mul_nonneg _ _ HalfPow.half_nonneg
    (Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1))
      (Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)))
  have hquad := Q'.mul_le_mul_of_nonneg_left _ _ t
    (Q'.add_le_add_right _ _ A (sourceSecondMoment_le_retainedCasimir tail b f hb hf)) ht
  have hgroup : h*A + (t*(sourceSecondMoment tail b f+A) +
      sourceCubic tail w b f-sourceOmitted tail w K b f) ≈
      h*A + (t*(sourceSecondMoment tail b f+A) +
        (sourceCubic tail w b f-sourceOmitted tail w K b f)) :=
    Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.add_assoc_eqv _ _ _)
  have hright : h*A + (t*((-R-oneThird*S)+A) +
      (sourceCubic tail w b f-sourceOmitted tail w K b f)) ≈
      (h+t)*A + t*(-R-oneThird*S)+
        sourceCubic tail w b f-sourceOmitted tail w K b f := by
    exact poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2))
        (.add (.mul (.var 1) (.add
          (.add (.neg (.var 6)) (.neg (.mul (.var 7) (.var 8)))) (.var 2)))
          (.add (.var 4) (.neg (.var 5)))))
      (.add (.add (.add (.mul (.add (.var 0) (.var 1)) (.var 2))
        (.mul (.var 1) (.add (.neg (.var 6)) (.neg (.mul (.var 7) (.var 8))))))
        (.var 4)) (.neg (.var 5))) (by decide)
      (fun | 0 => h | 1 => t | 2 => A | 4 => sourceCubic tail w b f
           | 5 => sourceOmitted tail w K b f | 6 => R | 7 => oneThird | _ => S)
  have hmid := Q'.add_le_add_left (h*A) _ _
    (Q'.add_le_add_right _ _ (sourceCubic tail w b f-sourceOmitted tail w K b f) hquad)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (sourceEnergy_secondOrder tail w K b f hb hf) hgroup))
    (Q'.le_trans' _ _ _ hmid (Q'.le_of_eqv hright))

/-- The retained-Casimir inequality is composed on every signed source
before summing the actual passive channels. Omitted loss stays separate. -/
theorem sourceEnergy_signed_channel_payment {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
    (hwidth : side scale < width) :
    sourceEnergy (N width) w K (List.range (N width))
      (projectedEndpointSource w K width (terminalMessage w K width (n+1)))
      (oddCentered hw0 hw1 K width hK (n+1)
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1)) ≤
      signedEnergyDebt hw0 hw1 K width hK (n+1) scale hwidth +
        signedChannelOmitted hw0 hw1 K width hK (n+1) scale hwidth := by
  let hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  let q := projectedEndpointSource w K width (terminalMessage w K width (n+1))
  let f := oddCentered hw0 hw1 K width hK (n+1)
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
  let ids := spectatorBlocks scale width hwidth
  let active := observableBlocks scale width hwidth
  have hf0 := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hf := oddCentered_supported hw0 hw1 K width hK (n+1) hf0
  have hq : SupportedQuaternionBlocks (N width) q := by
    simpa only [q, hN] using source_supported w K width (n+1)
  have hind : ∀ i, i ∈ ids → QuaternionBlockIndependent i f := by
    intro i hi
    exact oddCentered_independent hw0 hw1 K width hK (n+1) i
      (sourceCharacter_spectator_independent scale width hwidth i hi)
  have hproj := sourceEnergy_projected_channels (N width) w K active ids
    (observableBlocks_lt scale width hwidth)
    (spectatorBlocks_lt scale width hwidth)
    (spectator_not_observable scale width hwidth)
    (spectator_observable_cover scale width hwidth)
    q f hq hf hind
  have hle := channelSum_le
    (fun c => sourceEnergy (N width) w K (List.range (N width))
      (channelSource ids q c) f)
    (fun c =>
      ((1 : Q')-w + HalfPow.half*((1-w)*(1-w))) *
        weightedAngularEnergy (N width-1) (channelSource ids q c) f +
      (HalfPow.half*((1-w)*(1-w))) *
        (-H (N width) (polyMul (polyMul (channelSource ids q c) (channelSource ids q c))
          (activeCasimirPolynomial (List.range (N width))
            (activeGamma (List.range (N width)) f f))) -
          oneThird*H (N width) (polyMul
            (polyMul (channelSource ids q c)
              (activeCasimirPolynomial (List.range (N width)) f))
            (polyMul (channelSource ids q c)
              (activeCasimirPolynomial (List.range (N width)) f)))) +
      sourceCubic (N width-1) w (channelSource ids q c) f -
      sourceOmitted (N width-1) w K (channelSource ids q c) f)
    (productChannels (N width) w K ids)
    (productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K ids)
    (fun c hc => by
      have hb : SupportedQuaternionBlocks (N width)
          (channelSource ids q c.2) := channelSource_supported (N width) w K ids
            (spectatorBlocks_lt scale width hwidth)
            hq c hc
      have hs := channel_signed_second_order (w := w) (tail := N width-1)
        (Q'.le_of_lt hw0) hw1 K (channelSource ids q c.2) f
        (by simpa only [hN] using hb) (by simpa only [hN] using hf)
      simpa only [hN] using hs)
  have hsum : sourceEnergy (N width) w K (List.range (N width)) q f ≤
      channelSum (productChannels (N width) w K ids) (fun c =>
        ((1 : Q')-w + HalfPow.half*((1-w)*(1-w))) *
          weightedAngularEnergy (N width-1) (channelSource ids q c) f +
        (HalfPow.half*((1-w)*(1-w))) *
          (-H (N width) (polyMul (polyMul (channelSource ids q c) (channelSource ids q c))
            (activeCasimirPolynomial (List.range (N width))
              (activeGamma (List.range (N width)) f f))) -
            oneThird*H (N width) (polyMul
              (polyMul (channelSource ids q c)
                (activeCasimirPolynomial (List.range (N width)) f))
              (polyMul (channelSource ids q c)
                (activeCasimirPolynomial (List.range (N width)) f)))) +
        sourceCubic (N width-1) w (channelSource ids q c) f -
        sourceOmitted (N width-1) w K (channelSource ids q c) f) := by
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hproj) hle
  let A := fun z => weightedAngularEnergy (N width-1) (channelSource ids q z) f
  let R := fun z => H (N width) (polyMul (polyMul (channelSource ids q z)
    (channelSource ids q z)) (activeCasimirPolynomial (List.range (N width))
      (activeGamma (List.range (N width)) f f)))
  let S := fun z =>
    let v := polyMul (channelSource ids q z)
      (activeCasimirPolynomial (List.range (N width)) f)
    H (N width) (polyMul v v)
  let C := fun z => sourceCubic (N width-1) w (channelSource ids q z) f
  let O := fun z => sourceOmitted (N width-1) w K (channelSource ids q z) f
  let debt := fun z => ((1-w)+HalfPow.half*((1-w)*(1-w)))*A z +
    (HalfPow.half*((1-w)*(1-w))*(-R z-oneThird*S z)+C z)
  have hsplit : channelSum (productChannels (N width) w K ids) (fun z =>
      ((1-w)+HalfPow.half*((1-w)*(1-w)))*A z +
        HalfPow.half*((1-w)*(1-w))*(-R z-oneThird*S z)+C z-O z) ≈
      signedEnergyDebt hw0 hw1 K width hK (n+1) scale hwidth +
        signedChannelOmitted hw0 hw1 K width hK (n+1) scale hwidth := Q'.eqv_trans _ _ _
    (channelSum_congr _ (fun z => debt z + -(O z))
      (productChannels (N width) w K ids) (fun c _ =>
        Q'.add_eqv_congr' (Q'.add_assoc_eqv _ _ _) (Q'.eqv_refl _)))
    (channelSum_add debt (fun z => -(O z)) (productChannels (N width) w K ids))
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hsplit)

/- The same signed remainder already bounds the actual original energy after
   the literal OWN centering and projected-source identity.  This is the
   useful non-normalized consumer; no estimate on the signed remainder is
   asserted here. -/
theorem energy_signed_channel_remainder {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n scale : Nat)
    (hwidth : side scale < width) :
    energy w K width (terminalMessage w K width (n+1))
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1) ≤
      signedEnergyDebt hw0 hw1 K width hK (n+1) scale hwidth +
        signedChannelOmitted hw0 hw1 K width hK (n+1) scale hwidth := by
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let psi := oddCentered hw0 hw1 K width hK (n+1) f
  let mean := normalizedMoment (N width) (marginalWeight w K width (n+1)) f
    (marginalMass_positive hw0 hw1 K width hK (n+1))
  have hf := sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1
  have hp := oddCentered_supported hw0 hw1 K width hK (n+1) hf
  have hfringe := fun i hi => oddCentered_independent hw0 hw1 K width hK (n+1) i
    (paddedSquare_fringe_independent scale width hwidth i hi)
  have hcenter := energy_shifted w K width
    (terminalMessage_supported w K width (n+1)) hf mean
  have hsource := energy_projected_source w K width
    (terminalMessage w K width (n+1)) psi
    (terminalMessage_supported w K width (n+1)) hp hfringe
  have hbound := sourceEnergy_signed_channel_payment hw0 hw1 K width hK
    n scale hwidth
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcenter.symm)
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsource) hbound)

/-- Original normalized energy with ONLY the signed omitted component paid.
The cutoff is computed from nome, width and tolerance, and serves every
positive depth/permitted perimeter. Remaining signed debt is explicit. -/
theorem normalizedEnergy_signed_cutoff_payment {w delta : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hdelta : (0 : Q') < delta)
    (width K : Nat) (hK : omittedPaymentCutoff hw0 hw1 width delta ≤ K)
    (n scale : Nat) (hwidth : side scale < width) :
    let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width delta) hK
    normalizedEnergy hw0 hw1 K width hhead (n+1)
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1) ≤
      signedEnergyDebt hw0 hw1 K width hhead (n+1) scale hwidth *
        Q'.recipPos (oddMass w K width (n+1))
          (oddMass_positive hw0 hw1 K width hhead (n+1)) +
      delta*oddVariance hw0 hw1 K width hhead (n+1)
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1) := by
  dsimp only
  let hhead := Nat.le_trans (headCutoff_le_omittedPaymentCutoff hw0 hw1 width delta) hK
  let a := Q'.recipPos (oddMass w K width (n+1))
    (oddMass_positive hw0 hw1 K width hhead (n+1))
  have hraw := Q'.mul_le_mul_of_nonneg_right _ _ a
    (energy_signed_channel_remainder hw0 hw1 K width hhead n scale hwidth)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hpay := signedChannelOmitted_le_variance hw0 hw1 hdelta width K hK n scale hwidth
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.add_mul_eqv _ _ _))
      (Q'.add_le_add_left _ _ _ hpay))

#print axioms signedEnergyDebt
#print axioms channel_signed_second_order
#print axioms sourceEnergy_signed_channel_payment
#print axioms energy_signed_channel_remainder
#print axioms normalizedEnergy_signed_cutoff_payment

end YMGap.Continuum.BF4DyadicWilsonSquareSignedEnergyPayment
