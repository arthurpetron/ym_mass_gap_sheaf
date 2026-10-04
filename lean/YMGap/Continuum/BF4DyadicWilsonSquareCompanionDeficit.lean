/-
# Literal Wilson-square companion and cap deficit in the original channels

The two-copy plus square and its cap-sixteen defect retain the original
terminal source, spectator partition, whole increment and raw second moment.
Their exact heat-loss split exposes an alternative to a separately estimated
first-order source loss. Neither the cap defect nor the angular/raw deficit is
declared small, and no physical scaling conclusion is made.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareJointQuadraticDebt
import YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion

namespace YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels (channelSum)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionProductHeatMomentDefect (heatLossPair)
open YMGap.Continuum.SU2QuaternionProductHeatSourceCompanion
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung (sourceIncrementCost)
open YMGap.Continuum.SU2QuaternionPassiveChannelMomentFactorization
  (channelSum_congr channelSum_smul)
open YMGap.Continuum.SU2QuaternionPassiveChannelSobolevError (channelSum_add)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage (paddedSquare_fringe_independent)
open YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
open YMGap.Continuum.BF4DyadicWilsonSquareQuadraticHeat (paddedSquare_square_moment)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelExactResponse
  (squareChannelIncrement exactChannelHeatCost paddedSquare_channel_exact_cost)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelVarianceLoss
  (squareOriginalRawSecondMoment channelHeatLoss paddedSquare_channel_heatLoss_pin)
open YMGap.Continuum.SU2HeatExactSquareCreditWindow (exactSquareCredit)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks terminalMessage sourceCharacter

/-- Sum of the positive companion squares in the actual signed channels. -/
def squareChannelCompanion (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (depth : Nat) : Q' :=
  let g := terminalMessage w K width depth
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
    (fun c => sourceCompanionCost (N width) w K (List.range (N width))
      (squareChannelSource w K scale width hwidth g c) f)

/-- Sum of the cap-sixteen residuals paired with those same channel squares. -/
def squareChannelCapDeficit (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (depth : Nat) : Q' :=
  let g := terminalMessage w K width depth
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
    (fun c => sourceCapDeficitCost (N width) w K (List.range (N width))
      (squareChannelSource w K scale width hwidth g c) f)

/-- Original channels' source jump weighted by the observable's lower-copy
cap-four deficit. It is not the unobserved source mass loss. -/
def squareChannelObservedLoss (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (depth : Nat) : Q' :=
  let g := terminalMessage w K width depth
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
    (fun c => sourceObservedLoss (N width) w K (List.range (N width))
      (squareChannelSource w K scale width hwidth g c) f)

attribute [local irreducible] squareChannelCompanion squareChannelCapDeficit
  squareChannelObservedLoss squareChannelIncrement squareChannelMass
  squareChannelMoment squareOriginalRawSecondMoment channelHeatLoss oddMass
  energy qpow exactSquareCredit sourceCompanionCost sourceCapDeficitCost
  sourceObservedLoss sourceIncrementCost

private theorem sum_nonnegative (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
      (∀ c, c ∈ cs → (0 : Q') ≤ value c.2) →
      (0 : Q') ≤ channelSum cs value
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, hv => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (hw c List.mem_cons_self) (hv c List.mem_cons_self))
      (sum_nonnegative value cs (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => hv d (List.mem_cons_of_mem c hd)))

/-- Actual cap deficit is nonnegative with the literal character cap four. -/
theorem squareChannelCapDeficit_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    (0 : Q') ≤ squareChannelCapDeficit w K scale width hwidth depth := by
  let g := terminalMessage w K width depth
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
  let b := squareChannelSource w K scale width hwidth g
  have hf := paddedSquareSquareBound scale width hwidth
  unfold squareChannelCapDeficit
  apply sum_nonnegative
  · exact productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K _
  · intro c hc
    have hb := squareChannelSource_supported w K scale width hwidth g
      (terminalMessage_supported w K width depth) c hc
    exact sourceCapDeficitCost_nonnegative (N width) hw0 hw1 K hK
      (List.range (N width)) (fun j hj => List.mem_range.mp hj) hb hf

/-- The observed lower-copy cap deficit is positive in the same signed
channels, with no pointwise source sign. -/
theorem squareChannelObservedLoss_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    (0 : Q') ≤ squareChannelObservedLoss w K scale width hwidth depth := by
  let g := terminalMessage w K width depth
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
  let b := squareChannelSource w K scale width hwidth g
  have hf := paddedSquareSquareBound scale width hwidth
  unfold squareChannelObservedLoss
  apply sum_nonnegative
  · exact productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K _
  · intro c hc
    have hb := squareChannelSource_supported w K scale width hwidth g
      (terminalMessage_supported w K width depth) c hc
    exact sourceObservedLoss_nonnegative (N width) hw0 hw1 K hK
      (List.range (N width)) (fun j hj => List.mem_range.mp hj) hb hf

/-- The companion and cap deficit partition the computed ORIGINAL channel
heat loss; no small-loss hypothesis is supplied. -/
theorem squareChannelCompanion_add_capDeficit_heatLoss_pin (w : Q')
    (K width depth scale : Nat) (hwidth : side scale < width) :
    squareChannelCompanion w K scale width hwidth depth+
      squareChannelCapDeficit w K scale width hwidth depth ≈
      32*channelHeatLoss w K width depth scale hwidth := by
  let g := terminalMessage w K width depth
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
  let b := squareChannelSource w K scale width hwidth g
  let j := fun z => sourceCompanionCost (N width) w K (List.range (N width)) (b z) f
  let d := fun z => sourceCapDeficitCost (N width) w K (List.range (N width)) (b z) f
  let ell := fun z => heatLossPair (N width) w K (List.range (N width)) (b z) (b z)
  have hloc (c : GramChannel) (hc : c ∈ cs) :
      j c.2+d c.2 ≈ 32*ell c.2 := by
    have hb := squareChannelSource_supported w K scale width hwidth g
      (terminalMessage_supported w K width depth) c hc
    exact companion_add_capDeficit_heatLoss_pin (N width) w K
      (List.range (N width)) (CayleyParentInj.range_nodup _)
      (fun j hj => List.mem_range.mp hj) hb
      (paddedSquareSquareBound scale width hwidth).support
  have hsum : channelSum cs j+channelSum cs d ≈ 32*channelSum cs ell :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (channelSum_add j d cs))
      (Q'.eqv_trans _ _ _ (channelSum_congr _ _ cs hloc)
        (channelSum_smul ell 32 cs))
  have hshape : squareChannelCompanion w K scale width hwidth depth+
      squareChannelCapDeficit w K scale width hwidth depth ≈
      channelSum cs j+channelSum cs d := by
    unfold squareChannelCompanion squareChannelCapDeficit
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hshape
    (Q'.eqv_trans _ _ _ hsum
      (Q'.mul_eqv_congr_left 32 _ _
        (Q'.eqv_symm (paddedSquare_channel_heatLoss_pin
          w K width depth scale hwidth))))

/-- The cap deficit contains the WHOLE original channel increment. The
remaining term is four times the observed source loss, not an extra credit
on top of that increment. -/
theorem squareChannelCapDeficit_eq_increment_observedLoss_pin (w : Q')
    (K width depth scale : Nat) (hwidth : side scale < width) :
    squareChannelCapDeficit w K scale width hwidth depth ≈
      squareChannelIncrement w K scale width hwidth depth+
        4*squareChannelObservedLoss w K scale width hwidth depth := by
  let g := terminalMessage w K width depth
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let cs : List GramChannel := productChannels (N width) w K
    (spectatorBlocks scale width hwidth)
  let b : RatPoly → RatPoly := squareChannelSource w K scale width hwidth g
  let d : RatPoly → Q' := fun z =>
    sourceCapDeficitCost (N width) w K (List.range (N width)) (b z) f
  let i : RatPoly → Q' := fun z =>
    sourceIncrementCost (N width) w K (List.range (N width)) (b z) f
  let o : RatPoly → Q' := fun z =>
    sourceObservedLoss (N width) w K (List.range (N width)) (b z) f
  have hloc (c : GramChannel) (hc : c ∈ cs) :
      d c.2 ≈ i c.2+4*o c.2 := by
    have hb := squareChannelSource_supported w K scale width hwidth g
      (terminalMessage_supported w K width depth) c hc
    exact capDeficit_eq_increment_observedLoss_pin (N width) w K
      (List.range (N width)) (fun j hj => List.mem_range.mp hj)
      hb (paddedSquareSquareBound scale width hwidth).support
  have hs0 : channelSum cs d ≈
      channelSum cs (fun z : RatPoly => i z+4*o z) :=
    channelSum_congr d (fun z : RatPoly => i z+4*o z) cs hloc
  have hs1 : channelSum cs (fun z : RatPoly => i z+4*o z) ≈
      channelSum cs i+channelSum cs (fun z : RatPoly => 4*o z) :=
    channelSum_add i (fun z : RatPoly => 4*o z) cs
  have hs2 : channelSum cs (fun z : RatPoly => 4*o z) ≈
      4*channelSum cs o := channelSum_smul o 4 cs
  have hsum : channelSum cs d ≈ channelSum cs i+4*channelSum cs o :=
    Q'.eqv_trans _ _ _ hs0
      (Q'.eqv_trans _ _ _ hs1
        (Q'.add_eqv_congr_left (channelSum cs i) _ _ hs2))
  have hshape : squareChannelCapDeficit w K scale width hwidth depth ≈
      channelSum cs d := by
    unfold squareChannelCapDeficit
    exact Q'.eqv_refl _
  have hinc : channelSum cs i ≈
      squareChannelIncrement w K scale width hwidth depth := by
    unfold squareChannelIncrement
    exact Q'.eqv_refl _
  have hobs : channelSum cs o ≈
      squareChannelObservedLoss w K scale width hwidth depth := by
    unfold squareChannelObservedLoss
    exact Q'.eqv_refl _
  exact Q'.eqv_trans _ _ _ hshape
    (Q'.eqv_trans _ _ _ hsum
      (Q'.add_eqv_congr' hinc (Q'.mul_eqv_congr_left 4 _ _ hobs)))

/-- Exact raw original moment and whole increment plus the retained
companion square, after the literal label-two heat image in each channel. -/
theorem paddedSquare_rawSecond_increment_companion_pin {w : Q'}
    (K width : Nat) (h2 : 2 ≤ K)
    (depth scale : Nat) (hwidth : side scale < width) :
    8*squareOriginalRawSecondMoment w K width depth scale hwidth+
      squareChannelIncrement w K scale width hwidth depth+
      squareChannelCompanion w K scale width hwidth depth ≈
      4*((1+qpow w (32*side scale))*
        squareChannelMoment w K scale width hwidth (terminalMessage w K width depth)+
        (1-qpow w (32*side scale))*
          squareChannelMass w K scale width hwidth (terminalMessage w K width depth)) := by
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
  let b := squareChannelSource w K scale width hwidth (terminalMessage w K width depth)
  let u := fun z => sourceMoment (N width) w K (List.range (N width)) (b z) (polyMul f f)
  let i := fun z => sourceIncrementCost (N width) w K (List.range (N width)) (b z) f
  let j := fun z => sourceCompanionCost (N width) w K (List.range (N width)) (b z) f
  let v := fun z => H (N width) (polyMul (polyMul (b z) (b z)) (polyMul f f))
  let m := fun z => H (N width) (polyMul (b z) (b z))
  let U := squareOriginalRawSecondMoment w K width depth scale hwidth
  let I := squareChannelIncrement w K scale width hwidth depth
  let J := squareChannelCompanion w K scale width hwidth depth
  let Q := squareChannelMoment w K scale width hwidth (terminalMessage w K width depth)
  let M := squareChannelMass w K scale width hwidth (terminalMessage w K width depth)
  let beta := qpow w (32*side scale)
  have hf := (paddedSquareSquareBound scale width hwidth).support
  have hu : channelSum cs u ≈ U := by
    unfold U squareOriginalRawSecondMoment
    exact (oddMoment_eq_square_channels scale width hwidth w K depth (polyMul f f)
      (supported_polyMul hf hf)
      (fun t ht => quaternionBlockIndependent_polyMul
        (paddedSquare_fringe_independent scale width hwidth t ht)
        (paddedSquare_fringe_independent scale width hwidth t ht))
      (fun t ht => quaternionBlockIndependent_polyMul
        (sourceCharacter_spectator_independent_allSpin scale width hwidth t ht 1)
        (sourceCharacter_spectator_independent_allSpin scale width hwidth t ht 1))).symm
  have hi : channelSum cs i ≈ I := by
    unfold I squareChannelIncrement
    exact Q'.eqv_refl _
  have hj : channelSum cs j ≈ J := by
    unfold J squareChannelCompanion
    exact Q'.eqv_refl _
  have hv : channelSum cs v ≈ Q := by
    unfold Q squareChannelMoment
    exact Q'.eqv_refl _
  have hm : channelSum cs m ≈ M := by
    unfold M squareChannelMass
    exact Q'.eqv_refl _
  have hloc (c : GramChannel) (hc : c ∈ cs) :
      8*u c.2+i c.2+j c.2 ≈
        4*((1+beta)*v c.2+(1-beta)*m c.2) := by
    have hb := squareChannelSource_supported w K scale width hwidth _
      (terminalMessage_supported w K width depth) c hc
    have h := eight_sourceMoment_add_increment_companion_pin (N width) w K
      (List.range (N width)) (CayleyParentInj.range_nodup _)
      (fun t ht => List.mem_range.mp ht) hb hf
    have hr := paddedSquare_square_moment scale width hwidth w K h2 (b c.2) hb
    exact Q'.eqv_trans _ _ _ h
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left 4 _ _ (Q'.add_eqv_congr_left _ _ _ hr))
        (poly_identity_of_normal_eq
          (.mul (.const 4) (.add (.var 0)
            (.add (.mul (.var 2) (.var 0))
              (.mul (.add (.const 1) (.neg (.var 2))) (.var 1)))))
          (.mul (.const 4) (.add (.mul (.add (.const 1) (.var 2)) (.var 0))
            (.mul (.add (.const 1) (.neg (.var 2))) (.var 1))))
          (by decide) (fun | 0 => v c.2 | 1 => m c.2 | _ => beta)))
  have hsum : channelSum cs (fun z => 8*u z+i z+j z) ≈
      channelSum cs (fun z => 4*((1+beta)*v z+(1-beta)*m z)) :=
    channelSum_congr _ _ cs hloc
  have hl : channelSum cs (fun z => 8*u z+i z+j z) ≈ 8*U+I+J :=
    Q'.eqv_trans _ _ _ (channelSum_add (fun z => 8*u z+i z) j cs)
      (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _
        (channelSum_add (fun z => 8*u z) i cs)
        (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (channelSum_smul u 8 cs)
          (Q'.mul_eqv_congr_left 8 _ _ hu)) hi)) hj)
  have hr : channelSum cs (fun z => 4*((1+beta)*v z+(1-beta)*m z)) ≈
      4*((1+beta)*Q+(1-beta)*M) :=
    Q'.eqv_trans _ _ _ (channelSum_smul _ 4 cs) (Q'.mul_eqv_congr_left 4 _ _
      (Q'.eqv_trans _ _ _ (channelSum_add _ _ cs) (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (channelSum_smul v (1+beta) cs)
          (Q'.mul_eqv_congr_left (1+beta) _ _ hv))
        (Q'.eqv_trans _ _ _ (channelSum_smul m (1-beta) cs)
          (Q'.mul_eqv_congr_left (1-beta) _ _ hm)))))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hl)
    (Q'.eqv_trans _ _ _ hsum hr)

/-- Exact original energy identity retaining the ENTIRE increment, original
raw moment and the positive channel cap defect. No sign of `k` is used. -/
theorem paddedSquare_energy_companion_capDeficit_pin {w : Q'}
    (K width : Nat) (h2 : 2 ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let a := qpow w (12*side scale)
    let beta := qpow w (32*side scale)
    let k := exactSquareCredit w (side scale)
    let I := squareChannelIncrement w K scale width hwidth depth
    let U := squareOriginalRawSecondMoment w K width depth scale hwidth
    let M := squareChannelMass w K scale width hwidth (terminalMessage w K width depth)
    let Z := oddMass w K width depth
    let D := squareChannelCapDeficit w K scale width hwidth depth
    (1+beta)*(4*energy w K width (terminalMessage w K width depth) f+I)+
      (HalfPow.half*k)*I ≈
      4*(a*(1-beta)-4*k)*M+4*k*(4*Z-U)+(HalfPow.half*k)*D := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let a := qpow w (12*side scale)
  let beta := qpow w (32*side scale)
  let k := exactSquareCredit w (side scale)
  let heat := (1 : Q')+beta
  let d := (1 : Q')-beta
  let h := HalfPow.half
  let e := energy w K width (terminalMessage w K width depth) f
  let I := squareChannelIncrement w K scale width hwidth depth
  let J := squareChannelCompanion w K scale width hwidth depth
  let D := squareChannelCapDeficit w K scale width hwidth depth
  let U := squareOriginalRawSecondMoment w K width depth scale hwidth
  let Q := squareChannelMoment w K scale width hwidth (terminalMessage w K width depth)
  let M := squareChannelMass w K scale width hwidth (terminalMessage w K width depth)
  let Z := oddMass w K width depth
  let T := heat*Q+d*M
  let S := 8*U+I+J
  let A := 4*a*d*M
  have hcost : 4*e+I ≈ 2*(d*M-k*Q) :=
    Q'.eqv_trans _ _ _
      (paddedSquare_channel_exact_cost K width h2 depth scale hwidth)
      (Q'.mul_eqv_congr_left 2 _ _ (by
        unfold exactChannelHeatCost k exactSquareCredit
        dsimp only [d]
        exact poly_identity_of_normal_eq
          (.add (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))
            (.mul (.add (.add (.const 1) (.var 1))
              (.neg (.mul (.const 2) (.var 0)))) (.var 3)))
          (.add (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))
            (.neg (.mul
              (.add (.add (.mul (.const 2) (.var 0)) (.neg (.const 1)))
                (.neg (.var 1))) (.var 3))))
          (by decide) (fun | 0 => a | 1 => beta | 2 => M | _ => Q)))
  have hmoment : S ≈ 4*T :=
    paddedSquare_rawSecond_increment_companion_pin K width h2 depth scale hwidth
  have hloss : J+D ≈ 32*(M-Z) := by
    have hp := squareChannelCompanion_add_capDeficit_heatLoss_pin w K width depth scale hwidth
    unfold channelHeatLoss at hp
    exact hp
  have h4 : (h*k)*4 ≈ 2*k :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.const 4))
        (.mul (.mul (.const 4) (.var 0)) (.var 1))
        (by decide) (fun | 0 => h | _ => k))
      (Q'.mul_eqv_congr_right _ _ k (by decide : 4*HalfPow.half ≈ 2))
  have h8 : 8*(h*k) ≈ 4*k :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.const 8) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.const 8) (.var 0)) (.var 1))
        (by decide) (fun | 0 => h | _ => k))
      (Q'.mul_eqv_congr_right _ _ k (by decide : 8*HalfPow.half ≈ 4))
  have h32 : 32*(h*k) ≈ 16*k :=
    Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.const 32) (.mul (.var 0) (.var 1)))
        (.mul (.mul (.const 32) (.var 0)) (.var 1))
        (by decide) (fun | 0 => h | _ => k))
      (Q'.mul_eqv_congr_right _ _ k (by decide : 32*HalfPow.half ≈ 16))
  have hk : k = 2*a-1-beta := by
    unfold k exactSquareCredit
    rfl
  have hlinear : heat*(2*(d*M-k*Q))+(h*k)*I ≈
      A+(h*k)*I-(2*k)*T := by
    rw [hk]
    change ((1+beta)*(2*((1-beta)*M-(2*a-1-beta)*Q))+
        (h*(2*a-1-beta))*I) ≈
      4*a*(1-beta)*M+(h*(2*a-1-beta))*I-
        (2*(2*a-1-beta))*((1+beta)*Q+(1-beta)*M)
    let av : RingNormaliser.PolyExpr := .var 0
    let bv : RingNormaliser.PolyExpr := .var 1
    let mv : RingNormaliser.PolyExpr := .var 2
    let qv : RingNormaliser.PolyExpr := .var 3
    let iv : RingNormaliser.PolyExpr := .var 4
    let dv := RingNormaliser.PolyExpr.add (.const 1) (.neg bv)
    let hv := RingNormaliser.PolyExpr.add (.const 1) bv
    let kv := RingNormaliser.PolyExpr.add
      (.add (.mul (.const 2) av) (.neg (.const 1))) (.neg bv)
    let weightedIncrement := (h*(2*a-1-beta))*I
    let rho : Nat → Q' := fun j =>
      if j = 0 then a else if j = 1 then beta else if j = 2 then M else
      if j = 3 then Q else weightedIncrement
    exact poly_identity_of_normal_eq
      (.add (.mul hv (.mul (.const 2)
        (.add (.mul dv mv) (.neg (.mul kv qv))))) iv)
      (.add (.add (.mul (.mul (.mul (.const 4) av) dv) mv) iv)
        (.neg (.mul (.mul (.const 2) kv)
          (.add (.mul hv qv) (.mul dv mv)))))
      (by decide) rho
  have hscale : (h*k)*(4*T) ≈ (2*k)*T :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (h*k) 4 T))
      (Q'.mul_eqv_congr_right _ _ T h4)
  have hstep1 : heat*(4*e+I)+(h*k)*I ≈ A+(h*k)*I-(h*k)*(4*T) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ ((h*k)*I)
      (Q'.mul_eqv_congr_left heat _ _ hcost))
      (Q'.eqv_trans _ _ _ hlinear
        (Q'.add_eqv_congr_left (A+(h*k)*I) _ _
          (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hscale))))
  have hstep2 : A+(h*k)*I-(h*k)*(4*T) ≈
      A+(h*k)*I-(h*k)*S :=
    Q'.add_eqv_congr_left (A+(h*k)*I) _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left (h*k) _ _ (Q'.eqv_symm hmoment)))
  have hexpand : A+(h*k)*I-(h*k)*S ≈ A-(8*(h*k))*U-(h*k)*J :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.mul (.var 1) (.var 2)))
        (.neg (.mul (.var 1)
          (.add (.add (.mul (.const 8) (.var 3)) (.var 2)) (.var 4)))))
      (.add (.add (.var 0)
        (.neg (.mul (.mul (.const 8) (.var 1)) (.var 3))))
        (.neg (.mul (.var 1) (.var 4))))
      (by decide) (fun | 0 => A | 1 => h*k | 2 => I | 3 => U | _ => J)
  have hstep3 : A-(8*(h*k))*U-(h*k)*J ≈ A-4*k*U-(h*k)*J :=
    Q'.add_eqv_congr_right _ _ (-((h*k)*J))
      (Q'.add_eqv_congr_left A _ _
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ U h8)))
  have hJ : J ≈ 32*(M-Z)-D :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
        (by decide) (fun | 0 => J | _ => D)))
      (Q'.add_eqv_congr_right _ _ (-D) hloss)
  have hstep4 : A-4*k*U-(h*k)*J ≈
      A-4*k*U-(h*k)*(32*(M-Z)-D) :=
    Q'.add_eqv_congr_left (A-4*k*U) _ _
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left (h*k) _ _ hJ))
  have hdist : A-4*k*U-(h*k)*(32*(M-Z)-D) ≈
      A-4*k*U-(32*(h*k))*(M-Z)+(h*k)*D := by
    let av : RingNormaliser.PolyExpr := .var 0
    let kv : RingNormaliser.PolyExpr := .var 1
    let uv : RingNormaliser.PolyExpr := .var 2
    let hv : RingNormaliser.PolyExpr := .var 3
    let mv : RingNormaliser.PolyExpr := .var 4
    let zv : RingNormaliser.PolyExpr := .var 5
    let dv : RingNormaliser.PolyExpr := .var 6
    let mz := RingNormaliser.PolyExpr.add mv (.neg zv)
    let a4u := RingNormaliser.PolyExpr.add av
      (.neg (.mul (.mul (.const 4) kv) uv))
    let rho : Nat → Q' := fun j =>
      if j = 0 then A else if j = 1 then k else if j = 2 then U else
      if j = 3 then h*k else if j = 4 then M else if j = 5 then Z else D
    exact poly_identity_of_normal_eq
      (.add a4u (.neg (.mul hv
        (.add (.mul (.const 32) mz) (.neg dv)))))
      (.add (.add a4u (.neg (.mul (.mul (.const 32) hv) mz)))
        (.mul hv dv))
      (by decide) rho
  have hstep5 : A-4*k*U-(32*(h*k))*(M-Z)+(h*k)*D ≈
      A-4*k*U-(16*k)*(M-Z)+(h*k)*D :=
    Q'.add_eqv_congr_right _ _ ((h*k)*D)
      (Q'.add_eqv_congr_left (A-4*k*U) _ _
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ (M-Z) h32)))
  have hfinal : A-4*k*U-(16*k)*(M-Z)+(h*k)*D ≈
      4*(a*d-4*k)*M+4*k*(4*Z-U)+(h*k)*D := by
    let rho : Nat → Q' := fun j =>
      if j = 0 then a else if j = 1 then d else if j = 2 then M else
      if j = 3 then k else if j = 4 then U else if j = 5 then Z else (h*k)*D
    let av : RingNormaliser.PolyExpr := .var 0
    let dv : RingNormaliser.PolyExpr := .var 1
    let mv : RingNormaliser.PolyExpr := .var 2
    let kv : RingNormaliser.PolyExpr := .var 3
    let uv : RingNormaliser.PolyExpr := .var 4
    let zv : RingNormaliser.PolyExpr := .var 5
    let cv : RingNormaliser.PolyExpr := .var 6
    let oldMass := RingNormaliser.PolyExpr.mul (.mul (.mul (.const 4) av) dv) mv
    let rawCost := RingNormaliser.PolyExpr.mul (.mul (.const 4) kv) uv
    let lossCost := RingNormaliser.PolyExpr.mul (.mul (.const 16) kv) (.add mv (.neg zv))
    let newMass := RingNormaliser.PolyExpr.mul
      (.mul (.const 4) (.add (.mul av dv) (.neg (.mul (.const 4) kv)))) mv
    let rawDeficit := RingNormaliser.PolyExpr.mul (.mul (.const 4) kv)
      (.add (.mul (.const 4) zv) (.neg uv))
    exact poly_identity_of_normal_eq
      (.add (.add (.add oldMass (.neg rawCost)) (.neg lossCost)) cv)
      (.add (.add newMass rawDeficit) cv) (by decide) rho
  exact Q'.eqv_trans _ _ _ hstep1
    (Q'.eqv_trans _ _ _ hstep2
      (Q'.eqv_trans _ _ _ hexpand
        (Q'.eqv_trans _ _ _ hstep3
          (Q'.eqv_trans _ _ _ hstep4
            (Q'.eqv_trans _ _ _ hdist
              (Q'.eqv_trans _ _ _ hstep5 hfinal))))))

end YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit.squareChannelCompanion
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit.squareChannelCapDeficit
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit.squareChannelObservedLoss
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit.squareChannelCapDeficit_nonnegative
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit.squareChannelObservedLoss_nonnegative
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit.squareChannelCompanion_add_capDeficit_heatLoss_pin
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit.squareChannelCapDeficit_eq_increment_observedLoss_pin
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit.paddedSquare_rawSecond_increment_companion_pin
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareCompanionDeficit.paddedSquare_energy_companion_capDeficit_pin
