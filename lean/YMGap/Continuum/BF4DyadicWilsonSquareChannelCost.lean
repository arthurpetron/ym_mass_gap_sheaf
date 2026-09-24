/-
# Exact spectator-channel cost for a padded dyadic Wilson square

The complete original energy is decomposed over the literal square's passive
channels before the two exact Wilson heat images are collected.  The signed
source-increment correction is retained channel by channel.  No positivity,
normalization, variance, or scaling estimate is asserted here.
-/

import YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels
import YMGap.Continuum.BF4DyadicWilsonSquareQuadraticHeat
import YMGap.Continuum.SU2QuaternionFamilyChannelLoss

namespace YMGap.Continuum.BF4DyadicWilsonSquareChannelCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels
open YMGap.Continuum.BF4DyadicWilsonSquareSignedCost
  (paddedSquare_singleEndedCost)
open YMGap.Continuum.BF4DyadicWilsonSquareQuadraticHeat
  (paddedSquare_square_moment)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionFamilyChannelLoss
  (familyChannelQuadratic)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
  (sourceEnergy)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
  (sourceIncrementCost singleEndedCost
    four_mul_sourceEnergy_add_increment_eq_two_singleEnded)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" width:arg => quaternionHaar (N width)

private theorem channelSum_congr (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      (∀ c, c ∈ cs → left c.2 ≈ right c.2) →
      channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c :: cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left c.1 _ _ (h c List.mem_cons_self))
      (channelSum_congr left right cs
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem channelSum_add (left right : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => left c + right c) ≈
        channelSum cs left + channelSum cs right
  | [] => Q'.eqv_symm (QPoly.q_zero_add_eqv 0)
  | c :: cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_add_eqv c.1 (left c.2) (right c.2))
        (channelSum_add left right cs))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
        (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
        (by decide)
        (fun | 0 => c.1 * left c.2 | 1 => c.1 * right c.2
             | 2 => channelSum cs left | _ => channelSum cs right))

private theorem channelSum_scale (a : Q') (value : RatPoly → Q') :
    ∀ cs : List GramChannel,
      channelSum cs (fun c => a * value c) ≈ a * channelSum cs value
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | c :: cs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (channelSum_scale a value cs))
      (poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
          (.mul (.var 1) (.var 3)))
        (.mul (.var 1)
          (.add (.mul (.var 0) (.var 2)) (.var 3)))
        (by decide)
        (fun | 0 => c.1 | 1 => a | 2 => value c.2
             | _ => channelSum cs value))

private theorem source_quadratic_identity
    (scale width : Nat) (hwidth : side scale < width)
    (w : Q') (K : Nat) (hK : 2 ≤ K)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (N width) q) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let a := qpow w (12 * side scale)
    let b := qpow w (32 * side scale)
    (4 : Q') * sourceEnergy (N width) w K (List.range (N width)) q f +
        sourceIncrementCost (N width) w K (List.range (N width)) q f ≈
      (2 : Q') *
        ((1 + -((2 : Q') * a) + b) *
            H width (polyMul (polyMul q q) (polyMul f f)) +
          (1 + -b) * H width (polyMul q q)) := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  have hf := sourceCharacter_supported width
    (paddedSquare scale width hwidth).edges 1
  have hy := four_mul_sourceEnergy_add_increment_eq_two_singleEnded
    (N width) w K (List.range (N width))
    (fun _ hi => List.mem_range.mp hi) hq hf
  have hs := paddedSquare_singleEndedCost scale width hwidth w K (by omega) q hq
  have hsq := paddedSquare_square_moment scale width hwidth w K hK q hq
  exact Q'.eqv_trans _ _ _ hy (Q'.mul_eqv_congr_left 2 _ _
    (Q'.eqv_trans _ _ _ hs (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ hsq)
      (poly_identity_of_normal_eq
        (.add (.mul (.add (.const 1) (.neg (.mul (.const 2) (.var 0)))) (.var 2))
          (.add (.mul (.var 1) (.var 2))
            (.mul (.add (.const 1) (.neg (.var 1))) (.var 3))))
        (.add
          (.mul (.add (.add (.const 1) (.neg (.mul (.const 2) (.var 0))))
            (.var 1)) (.var 2))
          (.mul (.add (.const 1) (.neg (.var 1))) (.var 3)))
        (by decide)
        (fun | 0 => qpow w (12 * side scale)
             | 1 => qpow w (32 * side scale)
             | 2 => H width (polyMul (polyMul q q) (polyMul f f))
             | _ => H width (polyMul q q))))))

/-- Exact channel-aggregated signed cost of the actual terminal square.
The `Mchannel` term keeps the square insertion in every signed channel, while
the source mass is exactly the existing conditional family quadratic. -/
theorem paddedSquare_terminal_channel_cost
    (scale width : Nat) (hwidth : side scale < width)
    (w : Q') (K : Nat) (hK : 2 ≤ K) (depth : Nat) :
    let g := terminalMessage w K width depth
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let q := projectedEndpointSource w K width g
    let ids := spectatorBlocks scale width hwidth
    let cs := productChannels (N width) w K ids
    let bsrc := fun c => squareChannelSource w K scale width hwidth g c
    let Mchannel := channelSum cs (fun c =>
      H width (polyMul (polyMul (bsrc c) (bsrc c)) (polyMul f f)))
    (4 : Q') * energy w K width g f +
        channelSum cs (fun c => sourceIncrementCost (N width) w K
          (List.range (N width)) (bsrc c) f) ≈
      (2 : Q') *
        ((1 + -((2 : Q') * qpow w (12 * side scale)) +
            qpow w (32 * side scale)) * Mchannel +
          (1 + -(qpow w (32 * side scale))) *
            familyChannelQuadratic (N width) w K ids q) := by
  dsimp only
  let g := terminalMessage w K width depth
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let q := projectedEndpointSource w K width g
  let ids := spectatorBlocks scale width hwidth
  let cs := productChannels (N width) w K ids
  let bsrc := fun c => squareChannelSource w K scale width hwidth g c
  let E := fun c => sourceEnergy (N width) w K (List.range (N width)) (bsrc c) f
  let D := fun c => sourceIncrementCost (N width) w K (List.range (N width)) (bsrc c) f
  let M := fun c => H width (polyMul (polyMul (bsrc c) (bsrc c)) (polyMul f f))
  let A := fun c => H width (polyMul (bsrc c) (bsrc c))
  let alpha := (1 + -((2 : Q') * qpow w (12 * side scale)) +
    qpow w (32 * side scale))
  let beta := (1 + -(qpow w (32 * side scale)))
  have henergy := paddedSquare_energy_eq_channels scale width hwidth w K depth
  have hpoint : channelSum cs (fun c => (4 : Q') * E c + D c) ≈
      channelSum cs (fun c => (2 : Q') * (alpha * M c + beta * A c)) :=
    channelSum_congr _ _ cs (fun c hc =>
      source_quadratic_identity scale width hwidth w K hK (bsrc c.2)
        (squareChannelSource_supported w K scale width hwidth g
          (terminalMessage_supported w K width depth) c hc))
  have hmass : channelSum cs A ≈
      familyChannelQuadratic (N width) w K ids q := by
    dsimp [A, bsrc, cs, ids, q, familyChannelQuadratic,
      squareChannelSource, channelSource]
    exact Q'.eqv_refl _
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left 4 _ _ henergy) (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (channelSum_scale 4 E cs))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (channelSum_add (fun c => 4 * E c) D cs)) ?_
  refine Q'.eqv_trans _ _ _ hpoint ?_
  refine Q'.eqv_trans _ _ _ (channelSum_scale 2 (fun c => alpha * M c + beta * A c) cs) ?_
  refine Q'.mul_eqv_congr_left 2 _ _ ?_
  refine Q'.eqv_trans _ _ _ (channelSum_add (fun c => alpha * M c) (fun c => beta * A c) cs) ?_
  exact Q'.add_eqv_congr'
    (channelSum_scale alpha M cs)
    (Q'.eqv_trans _ _ _ (channelSum_scale beta A cs)
      (Q'.mul_eqv_congr_left beta _ _ hmass))

#print axioms paddedSquare_terminal_channel_cost

end YMGap.Continuum.BF4DyadicWilsonSquareChannelCost
