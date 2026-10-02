/-
# Complete original centered energy with explicit channel heat loss

First retain the exact SIGNED cross term minus moment defect, with the OWN
original interacting center. A separate sufficient upper estimate uses the
actual loss M-Z. It is not a necessary small-loss criterion: the retained
signed terms can cancel without small M-Z. No comparison with earlier
ceilings, useful changing-family scaling, or continuum closure is asserted.
-/

import YMGap.Continuum.SU2QuaternionProductHeatCenteredEnergyLoss
import YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceLoss
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse
import YMGap.Continuum.RationalSquareLossYoung

namespace YMGap.Continuum.BF4DyadicWilsonSquareCenteredEnergyLoss

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.SU2QuaternionProductHeatMomentDefect
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment sourceEnergy)
open YMGap.Continuum.SU2QuaternionProductHeatCenteredEnergyLoss
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization (channelSum_congr channelSum_smul)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError (channelSum_add channelSum_le)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource oddMoment_projected_source energy_projected_source)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (oddVariance marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
  (oddCentered oddCentered_supported oddCentered_independent centered_source_square)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyBandResponse (energy_shifted)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry (paddedSquareSquareBound)
open YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage
  (paddedSquare_fundamental_fullRange paddedSquare_fringe_independent)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceLoss
open YMGap.Continuum.RationalSquareLossYoung (le_add_of_square_le_four_mul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage sourceCharacter

private theorem qpow_rg (w : Q') : ∀ n, qpow w n = RGTransport.qpow w n
  | 0 => rfl
  | n+1 => congrArg (fun x : Q' => x*w) (qpow_rg w n)

private theorem sum_sub (cs : List GramChannel) (u v : RatPoly → Q') :
    channelSum cs (fun z => u z-v z) ≈ channelSum cs u-channelSum cs v := by
  have hn : channelSum cs (fun z => -v z) ≈ -(channelSum cs v) :=
    Q'.eqv_trans _ _ _ (channelSum_congr _ (fun z => (-1)*v z) cs (fun z _ =>
      poly_identity_of_normal_eq (.neg (.var 0)) (.mul (.const (-1)) (.var 0))
        (by decide) (fun _ => v z.2)))
      (Q'.eqv_trans _ _ _ (channelSum_smul v (-1) cs)
        (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
          (by decide) (fun _ => channelSum cs v)))
  exact Q'.eqv_trans _ _ _ (channelSum_add u (fun z => -v z) cs)
    (Q'.add_eqv_congr' (Q'.eqv_refl _) hn)

private theorem sum_polarization (cs : List GramChannel) (s mu : Q')
    (A J T S : RatPoly → Q') :
    channelSum cs (fun z => s*(A z+mu*J z)+T z-(A z-S z)) ≈
      s*(channelSum cs A+mu*channelSum cs J)+channelSum cs T-
        (channelSum cs A-channelSum cs S) :=
  Q'.eqv_trans _ _ _ (sum_sub cs _ _) (Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (channelSum_add _ T cs) (Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ (channelSum_smul _ s cs) (Q'.mul_eqv_congr_left s _ _
        (Q'.eqv_trans _ _ _ (channelSum_add A _ cs)
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (channelSum_smul J mu cs)))))
      (Q'.eqv_refl _)))
    (Q'.neg_eqv_congr _ _ (sum_sub cs A S)))

/-- The original mean of the COMPLETE interacting odd marginal. -/
def squareOwnMean {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) : Q' :=
  normalizedMoment (N width) (marginalWeight w K width depth)
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
    (marginalMass_positive hw0 hw1 K width hK depth)

/-- The exact Wilson heat gap; no continuum interpretation is attached. -/
def squareHeatGap (w : Q') (scale : Nat) : Q' := 1-qpow w (12*side scale)

theorem squareHeatGap_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (scale : Nat) : (0 : Q') < squareHeatGap w scale := by
  have hn : 0 < 12*side scale := by have h := side_positive scale; omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  unfold squareHeatGap
  rw [hm, qpow_rg]
  exact YMGap.Continuum.one_sub_pos_of_lt_one
    (HeatKernelGap.qpow_succ_lt_one (Q'.le_of_lt hw0) hw1 m)

/-- Signed cross term on the SAME original terminal channels and OWN center. -/
def squareCenteredHeatCross {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) : Q' :=
  let psi := oddCentered hw0 hw1 K width hK depth
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
  channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
    (fun z => sourceHeatCross (N width) w K (List.range (N width))
      (squareChannelSource w K scale width hwidth (terminalMessage w K width depth) z) psi)

/-- Entire raw / original centered moment difference, retaining its sign. -/
def squareCenteredMomentDefect {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) : Q' :=
  centeredChannelSquare hw0 hw1 K width hK depth scale hwidth-
    oddMass w K width depth*oddVariance hw0 hw1 K width hK depth
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1)

attribute [local irreducible] oddCentered normalizedMoment oddVariance oddMass
  marginalWeight squareOwnMean centeredChannelSquare centeredChannelFirstMoment
  squareCenteredHeatCross squareCenteredMomentDefect channelHeatLoss energy normalizedEnergy

/-- COMPLETE original energy, with both signed T-D terms retained separately.
The cutoff-head and algebraic label-two guards are distinct hypotheses. -/
theorem paddedSquare_energy_centered_loss_identity {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (h2 : 2 ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    energy w K width (terminalMessage w K width depth) f ≈
      squareHeatGap w scale*(centeredChannelSquare hw0 hw1 K width hK depth scale hwidth+
        squareOwnMean hw0 hw1 K width hK depth scale hwidth*
          centeredChannelFirstMoment hw0 hw1 K width hK depth scale hwidth)+
      squareCenteredHeatCross hw0 hw1 K width hK depth scale hwidth-
      squareCenteredMomentDefect hw0 hw1 K width hK depth scale hwidth := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let g := terminalMessage w K width depth
  let mu := squareOwnMean hw0 hw1 K width hK depth scale hwidth
  let psi := oddCentered hw0 hw1 K width hK depth f
  let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
  let b := squareChannelSource w K scale width hwidth g
  let A := centeredChannelSquare hw0 hw1 K width hK depth scale hwidth
  let J := centeredChannelFirstMoment hw0 hw1 K width hK depth scale hwidth
  let T := squareCenteredHeatCross hw0 hw1 K width hK depth scale hwidth
  let D := squareCenteredMomentDefect hw0 hw1 K width hK depth scale hwidth
  let V := oddMass w K width depth*oddVariance hw0 hw1 K width hK depth f
  let a := qpow w (12*side scale)
  let s := squareHeatGap w scale
  let aval := fun z => rawSourceMoment (N width) (b z) (polyMul psi psi)
  let jval := fun z => rawSourceMoment (N width) (b z) psi
  let tval := fun z => sourceHeatCross (N width) w K (List.range (N width)) (b z) psi
  let sval := fun z => sourceMoment (N width) w K (List.range (N width)) (b z) (polyMul psi psi)
  have hpsi : psi = QuaternionHaarDensityVariance.shifted f mu := by
    simp only [psi, oddCentered, mu, squareOwnMean, f]
  have hf : SupportedQuaternionBlocks (N width) f := (paddedSquareSquareBound scale width hwidth).support
  have hp : SupportedQuaternionBlocks (N width) psi := oddCentered_supported hw0 hw1 K width hK depth hf
  have hfr : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i psi :=
    fun i hi => oddCentered_independent hw0 hw1 K width hK depth i
      (paddedSquare_fringe_independent scale width hwidth i hi)
  have hsp : ∀ i, i ∈ spectatorBlocks scale width hwidth → QuaternionBlockIndependent i psi :=
    fun i hi => oddCentered_independent hw0 hw1 K width hK depth i
      (sourceCharacter_spectator_independent_allSpin scale width hwidth i hi 1)
  have hb (z : GramChannel) (hz : z ∈ cs) := squareChannelSource_supported w K scale width
    hwidth g (terminalMessage_supported w K width depth) z hz
  have haff : SupportedHaarEqv (N width) (productMap (N width) w K (List.range (N width)) psi)
      (polyAdd (polySmul a psi) (QuaternionHaarPolynomialSquareBound.cap (-(1-a)*mu))) := by
    rw [hpsi]
    exact productMap_shifted_affine (N width) w K (List.range (N width))
      (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi) f a mu
      (paddedSquare_fundamental_fullRange scale width hwidth w K (by omega))
  have hshift : energy w K width g psi ≈ energy w K width g f := by
    rw [hpsi]
    exact energy_shifted w K width (terminalMessage_supported w K width depth) hf mu
  have he : energy w K width g f ≈ channelSum cs (fun z =>
      sourceEnergy (N width) w K (List.range (N width)) (b z) psi) :=
    Q'.eqv_trans _ _ _ hshift.symm
      (Q'.eqv_trans _ _ _ (energy_projected_source w K width g psi
        (terminalMessage_supported w K width depth) hp hfr)
        (sourceEnergy_projected_channels (N width) w K
          (observableBlocks scale width hwidth) (spectatorBlocks scale width hwidth)
          (observableBlocks_lt scale width hwidth) (spectatorBlocks_lt scale width hwidth)
          (spectator_not_observable scale width hwidth) (spectator_observable_cover scale width hwidth)
          (projectedEndpointSource w K width g) psi
          (familyProject_supported (fringeBlocks width)
            (supported_polyMul (spatialWeight_supported w K width)
              (terminalMessage_supported w K width depth))) hp hsp))
  have hs : channelSum cs sval ≈ V :=
    Q'.eqv_trans _ _ _
      (oddMoment_eq_square_channels scale width hwidth w K depth (polyMul psi psi)
        (supported_polyMul hp hp)
        (fun i hi => quaternionBlockIndependent_polyMul (hfr i hi) (hfr i hi))
        (fun i hi => quaternionBlockIndependent_polyMul (hsp i hi) (hsp i hi))).symm
      (Q'.eqv_trans _ _ _ (oddMoment_projected_source w K width depth (polyMul psi psi)
        (supported_polyMul hp hp)
        (fun i hi => quaternionBlockIndependent_polyMul (hfr i hi) (hfr i hi)))
        (centered_source_square hw0 hw1 K width hK depth hf
          (paddedSquare_fringe_independent scale width hwidth)))
  have hA : channelSum cs aval ≈ A := by
    simp only [A, centeredChannelSquare, aval, cs, b, g, psi, f]
    exact Q'.eqv_refl _
  have hJ : channelSum cs jval ≈ J := by
    simp only [J, centeredChannelFirstMoment, jval, cs, b, g, psi, f]
    exact Q'.eqv_refl _
  have hT : channelSum cs tval ≈ T := by
    simp only [T, squareCenteredHeatCross, tval, cs, b, g, psi, f]
    exact Q'.eqv_refl _
  have hD : D ≈ A-V := by
    simp only [D, squareCenteredMomentDefect, A, V, f]
    exact Q'.eqv_refl _
  have hchannels : channelSum cs (fun z => sourceEnergy (N width) w K (List.range (N width)) (b z) psi) ≈
      channelSum cs (fun z => s*(aval z+mu*jval z)+tval z-(aval z-sval z)) :=
    channelSum_congr _ _ cs (fun z hz => sourceEnergy_centered_polarization (N width) w K
      (List.range (N width)) (fun _ hi => List.mem_range.mp hi) (b z.2) psi (hb z hz) hp a mu haff)
  have hcollected : channelSum cs (fun z => s*(aval z+mu*jval z)+tval z-(aval z-sval z)) ≈
      s*(A+mu*J)+T-(A-V) :=
    Q'.eqv_trans _ _ _ (sum_polarization cs s mu aval jval tval sval)
      (Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left s _ _
          (Q'.add_eqv_congr' hA (Q'.mul_eqv_congr_left mu _ _ hJ))) hT)
        (Q'.neg_eqv_congr _ _ (Q'.add_eqv_congr' hA (Q'.neg_eqv_congr _ _ hs))))
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ hchannels
    (Q'.eqv_trans _ _ _ hcollected (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ hD.symm))))

/-- Optional cap upper bound on signed T, not an assertion that T is positive. -/
theorem paddedSquare_centered_cross_le_loss {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (depth scale : Nat) (hwidth : side scale < width) :
    squareCenteredHeatCross hw0 hw1 K width hK depth scale hwidth ≤
      16*channelHeatLoss w K width depth scale hwidth := by
  unfold squareCenteredHeatCross
  let psi := oddCentered hw0 hw1 K width hK depth
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
  let b := squareChannelSource w K scale width hwidth (terminalMessage w K width depth)
  let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
  change channelSum cs (fun z => sourceHeatCross (N width) w K (List.range (N width)) (b z) psi) ≤ _
  have h := channelSum_le
    (fun z => sourceHeatCross (N width) w K (List.range (N width)) (b z) psi)
    (fun z => 16*heatLossPair (N width) w K (List.range (N width)) (b z) (b z)) cs
    (productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K _)
    (fun z hz => sourceHeatCross_le_cap_loss (N width) hw0 hw1 K hK
      (List.range (N width)) (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi)
      _ _ (squareChannelSource_supported w K scale width hwidth _
        (terminalMessage_supported w K width depth) z hz) 16
      (paddedSquare_centered_squareBound hw0 hw1 K width hK depth scale hwidth))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.eqv_trans _ _ _
    (channelSum_smul _ 16 _) (Q'.mul_eqv_congr_left 16 _ _
      (paddedSquare_channel_heatLoss_pin w K width depth scale hwidth).symm)))

private theorem half_gap_young (x A L c s : Q') (hA : (0 : Q') ≤ A)
    (hL : (0 : Q') ≤ L) (hc : (0 : Q') ≤ c) (hs : (0 : Q') < s)
    (hxx : x*x ≤ c*L*A) :
    x ≤ HalfPow.half*s*A+(HalfPow.half*c*Q'.recipPos s hs)*L := by
  let r := Q'.recipPos s hs
  have hr := Q'.le_of_lt (Q'.recipPos_pos s hs)
  have hfour : 4*((HalfPow.half*s*A)*((HalfPow.half*c*r)*L)) ≈ c*L*A :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.const 4) (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2))
        (.mul (.mul (.mul (.var 0) (.var 3)) (.var 4)) (.var 5))))
      (.mul (.mul (.mul (.const 4) (.mul (.var 0) (.var 0))) (.mul (.var 1) (.var 4)))
        (.mul (.mul (.var 3) (.var 5)) (.var 2))) (by decide)
      (fun | 0 => HalfPow.half | 1 => s | 2 => A | 3 => c | 4 => r | _ => L))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
          (by decide : 4*(HalfPow.half*HalfPow.half) ≈ 1))
          (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.mul_recipPos_eqv s hs))))
        (Q'.one_mul_eqv _))
  exact le_add_of_square_le_four_mul x (HalfPow.half*s*A) ((HalfPow.half*c*r)*L)
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt hs)) hA)
    (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hc) hr) hL)
    (Q'.le_trans' _ _ _ hxx (Q'.ge_of_eqv hfour))

private theorem complete_scalar_bound (E s A mu J T D L : Q')
    (hs : (0 : Q') < s) (hA : (0 : Q') ≤ A) (hL : (0 : Q') ≤ L)
    (he : E ≈ s*(A+mu*J)+T-D) (hT : T ≤ 16*L)
    (hJ : J*J ≤ L*A) (hD : D*D ≤ 16*L*A) (hmu : mu*mu ≤ (4 : Q')) :
    E ≤ 2*s*A+(16+2*s+8*Q'.recipPos s hs)*L := by
  let r := Q'.recipPos s hs
  have hneg : (-D)*(-D) ≤ 16*L*A := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (poly_identity_of_normal_eq (.mul (.neg (.var 0)) (.neg (.var 0)))
      (.mul (.var 0) (.var 0)) (by decide) (fun _ => D))) hD
  have hd0 := half_gap_young (-D) A L 16 s hA hL (by decide) hs hneg
  have hd : -D ≤ HalfPow.half*s*A+(8*r)*L := Q'.le_trans' _ _ _ hd0
    (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_right _ _ L (Q'.mul_eqv_congr_right _ _ r
        (by decide : HalfPow.half*16 ≈ 8)))))
  have hj0 : (s*mu*J)*(s*mu*J) ≤ (4*(s*s))*L*A := by
    have hpoly := poly_identity_of_normal_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => s | 1 => mu | _ => J)
    have hinner := Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (mu*mu) hJ (SumOfSquares.q_mul_self_nonneg mu))
      (Q'.mul_le_mul_of_nonneg_right _ _ (L*A) hmu (Q'.mul_nonneg _ _ hL hA))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpoly)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ (s*s) hinner (SumOfSquares.q_mul_self_nonneg s))
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 0)) (.mul (.const 4) (.mul (.var 1) (.var 2))))
          (.mul (.mul (.mul (.const 4) (.mul (.var 0) (.var 0))) (.var 1)) (.var 2))
          (by decide) (fun | 0 => s | 1 => L | _ => A))))
  have hj1 := half_gap_young (s*mu*J) A L (4*(s*s)) s hA hL
    (Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg s)) hs hj0
  have hcoef : HalfPow.half*(4*(s*s))*r ≈ 2*s :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.mul (.const 4) (.mul (.var 1) (.var 1)))) (.var 2))
      (.mul (.mul (.const 4) (.var 0)) (.mul (.var 1) (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => HalfPow.half | 1 => s | _ => r))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left s _ _ (Q'.mul_recipPos_eqv s hs)))
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
          (by decide : 4*HalfPow.half ≈ 2)) (Q'.mul_eqv_congr_left 2 _ _ (Q'.mul_one_eqv s))))
  have hj : s*mu*J ≤ HalfPow.half*s*A+(2*s)*L := Q'.le_trans' _ _ _ hj1
    (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_eqv_congr_right _ _ L hcoef)))
  have he' := Q'.eqv_trans _ _ _ he (poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.add (.var 1) (.mul (.var 2) (.var 3)))) (.var 4)) (.neg (.var 5)))
    (.add (.add (.add (.mul (.var 0) (.var 1)) (.mul (.mul (.var 0) (.var 2)) (.var 3))) (.var 4)) (.neg (.var 5)))
    (by decide) (fun | 0 => s | 1 => A | 2 => mu | 3 => J | 4 => T | _ => D))
  have hu := Q'.add_le_add (Q'.add_le_add
    (Q'.add_le_add (Q'.le_refl' (s*A)) hj) hT) hd
  have hcollect := poly_identity_of_normal_eq
    (.add (.add (.add (.mul (.var 0) (.var 1))
      (.add (.mul (.mul (.var 2) (.var 0)) (.var 1)) (.mul (.mul (.const 2) (.var 0)) (.var 3))))
      (.mul (.const 16) (.var 3)))
      (.add (.mul (.mul (.var 2) (.var 0)) (.var 1)) (.mul (.mul (.const 8) (.var 4)) (.var 3))))
    (.add (.mul (.mul (.add (.const 1) (.mul (.const 2) (.var 2))) (.var 0)) (.var 1))
      (.mul (.add (.add (.const 16) (.mul (.const 2) (.var 0))) (.mul (.const 8) (.var 4))) (.var 3)))
    (by decide) (fun | 0 => s | 1 => A | 2 => HalfPow.half | 3 => L | _ => r)
  have hhalf : 1+2*HalfPow.half ≈ (2 : Q') := by decide
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he') (Q'.le_trans' _ _ _ hu
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hcollect (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ A (Q'.mul_eqv_congr_right _ _ s hhalf)) (Q'.eqv_refl _)))))

/-- Sufficient L-only ceiling for the ORIGINAL normalized energy. The exact
signed identity above remains available when T-D cancellation is useful. -/
theorem paddedSquare_energy_centered_loss_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat)
    (hK : headCutoff w ≤ K) (h2 : 2 ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let s := squareHeatGap w scale
    let hs := squareHeatGap_positive hw0 hw1 scale
    let zinv := Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth)
    normalizedEnergy hw0 hw1 K width hK depth f ≤
      4*s*oddVariance hw0 hw1 K width hK depth f+
      (16+34*s+8*Q'.recipPos s hs)*(channelHeatLoss w K width depth scale hwidth*zinv) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let s := squareHeatGap w scale
  let hs := squareHeatGap_positive hw0 hw1 scale
  let A := centeredChannelSquare hw0 hw1 K width hK depth scale hwidth
  let J := centeredChannelFirstMoment hw0 hw1 K width hK depth scale hwidth
  let L := channelHeatLoss w K width depth scale hwidth
  let mu := squareOwnMean hw0 hw1 K width hK depth scale hwidth
  let T := squareCenteredHeatCross hw0 hw1 K width hK depth scale hwidth
  let D := squareCenteredMomentDefect hw0 hw1 K width hK depth scale hwidth
  let E := energy w K width (terminalMessage w K width depth) f
  let V := oddMass w K width depth*oddVariance hw0 hw1 K width hK depth f
  let r := Q'.recipPos s hs
  let zinv := Q'.recipPos (oddMass w K width depth) (oddMass_positive hw0 hw1 K width hK depth)
  have hA : (0 : Q') ≤ A := centeredChannelSquare_nonnegative hw0 hw1 K width hK depth scale hwidth
  have hL : (0 : Q') ≤ L := paddedSquare_channel_heatLoss_nonnegative hw0 hw1 K width hK depth scale hwidth
  have hE : E ≈ s*(A+mu*J)+T-D :=
    paddedSquare_energy_centered_loss_identity hw0 hw1 K width hK h2 depth scale hwidth
  have hT : T ≤ 16*L := paddedSquare_centered_cross_le_loss hw0 hw1 K width hK depth scale hwidth
  have hJ : J*J ≤ L*A := paddedSquare_channel_firstMoment_loss_bound hw0 hw1 K width hK depth scale hwidth
  have hD : D*D ≤ 16*L*A := by
    simpa only [D, squareCenteredMomentDefect, L, A, f] using
      (paddedSquare_channel_variance_loss_bound hw0 hw1 K width hK depth scale hwidth)
  have hmu : mu*mu ≤ (4 : Q') := by
    simpa only [mu, squareOwnMean] using
      (paddedSquare_mean_square_le_four hw0 hw1 K width hK depth scale hwidth)
  have h : E ≤ 2*s*A+(16+2*s+8*r)*L :=
    complete_scalar_bound E s A mu J T D L hs hA hL hE hT hJ hD hmu
  have hlin : A ≤ 2*V+16*L := paddedSquare_channel_square_linear_bound hw0 hw1 K width hK depth scale hwidth
  have hraw : energy w K width (terminalMessage w K width depth) f ≤
      4*s*V+(16+34*s+8*r)*L := Q'.le_trans' _ _ _ h (Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ (2*s) hlin
      (Q'.mul_nonneg _ _ (by decide) (Q'.le_of_lt hs))))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.mul (.mul (.const 2) (.var 0)) (.add (.mul (.const 2) (.var 1)) (.mul (.const 16) (.var 2))))
        (.mul (.add (.add (.const 16) (.mul (.const 2) (.var 0))) (.mul (.const 8) (.var 3))) (.var 2)))
      (.add (.mul (.mul (.const 4) (.var 0)) (.var 1))
        (.mul (.add (.add (.const 16) (.mul (.const 34) (.var 0))) (.mul (.const 8) (.var 3))) (.var 2)))
      (by decide) (fun | 0 => s | 1 => V | 2 => L | _ => r))))
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ zinv hraw
    (Q'.le_of_lt (Q'.recipPos_pos _ _))
  have hnorm : (4*s*V+(16+34*s+8*r)*L)*zinv ≈
      4*s*oddVariance hw0 hw1 K width hK depth f+(16+34*s+8*r)*(L*zinv) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.add (.mul (.mul (.const 4) (.var 0)) (.mul (.var 1) (.var 2)))
        (.mul (.var 3) (.var 4))) (.var 5))
      (.add (.mul (.mul (.mul (.const 4) (.var 0)) (.var 2)) (.mul (.var 1) (.var 5)))
        (.mul (.var 3) (.mul (.var 4) (.var 5)))) (by decide)
      (fun
        | 0 => s
        | 1 => oddMass w K width depth
        | 2 => oddVariance hw0 hw1 K width hK depth f
        | 3 => 16+34*s+8*r
        | 4 => L
        | _ => zinv))
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_recipPos_eqv (oddMass w K width depth)
            (oddMass_positive hw0 hw1 K width hK depth)))
          (Q'.mul_one_eqv _)) (Q'.eqv_refl _))
  have hout : E*zinv ≤ 4*s*oddVariance hw0 hw1 K width hK depth f+
      (16+34*s+8*r)*(L*zinv) := Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hnorm)
  simpa only [E, normalizedEnergy, f, zinv, s, r, hs, L] using hout

#print axioms squareOwnMean
#print axioms qpow_rg
#print axioms sum_polarization
#print axioms half_gap_young
#print axioms complete_scalar_bound
#print axioms squareHeatGap
#print axioms squareHeatGap_positive
#print axioms squareCenteredHeatCross
#print axioms squareCenteredMomentDefect
#print axioms paddedSquare_energy_centered_loss_identity
#print axioms paddedSquare_centered_cross_le_loss
#print axioms paddedSquare_energy_centered_loss_bound

end YMGap.Continuum.BF4DyadicWilsonSquareCenteredEnergyLoss
