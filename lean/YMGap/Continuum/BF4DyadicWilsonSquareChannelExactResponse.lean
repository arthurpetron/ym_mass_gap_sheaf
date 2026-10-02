/-
# Exact original heat cost with retained channel response squares

The two literal Wilson heat images evaluate the entire one-ended cost,
without a Taylor remainder or omitted-mode estimate. The source-increment
correction is retained on the SAME original passive channels, and dominates
their computed eigenresponse squares. Every normalization uses the original
odd partition. Energy and source increments are invariant under constant
shifts, so no original mean is needed in these uncentered moment formulas.

The signed heat coefficient is not assigned a sign. Raw channel moments are
not identified with OWN variance, and no numerical dominance, useful
changing-family scaling or continuum result is asserted.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareChannelCost
import YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
import YMGap.Continuum.SU2QuaternionProductHeatEigenResponse
import YMGap.Continuum.SU2QuaternionProductHeatSourceCentering
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow

namespace YMGap.Continuum.BF4DyadicWilsonSquareChannelExactResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung (sourceIncrementCost)
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.SU2QuaternionProductHeatEigenResponse
  (eigenResponse sourceIncrement_ge_eigenResponse_square)
open YMGap.Continuum.SU2QuaternionProductHeatSourceCentering (sourceIncrementCost_shifted)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
  (oddMass oddMass_positive normalizedEnergy)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels
  (squareChannelSource squareChannelSource_supported)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
  (squareChannelMass squareChannelMoment)
open YMGap.Continuum.BF4DyadicWilsonSquareChannelCost (paddedSquare_terminal_channel_cost)
open YMGap.Continuum.BF4DyadicWilsonSquareHeatImage (paddedSquare_fundamental_fullRange)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage sourceCharacter

private theorem sum_le (left right : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
    (∀ c, c ∈ cs → left c.2 ≤ right c.2) → channelSum cs left ≤ channelSum cs right
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, h => Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (h c List.mem_cons_self) (hw c List.mem_cons_self))
      (sum_le left right cs (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem sum_nonnegative (value : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → (0 : Q') ≤ c.1) →
    (∀ c, c ∈ cs → (0 : Q') ≤ value c.2) → (0 : Q') ≤ channelSum cs value
  | [], _, _ => Q'.le_refl' _
  | c::cs, hw, h => Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (hw c List.mem_cons_self) (h c List.mem_cons_self))
      (sum_nonnegative value cs (fun d hd => hw d (List.mem_cons_of_mem c hd))
        (fun d hd => h d (List.mem_cons_of_mem c hd)))

private theorem sum_congr (left right : RatPoly → Q') : ∀ cs : List GramChannel,
    (∀ c, c ∈ cs → left c.2 ≈ right c.2) → channelSum cs left ≈ channelSum cs right
  | [], _ => Q'.eqv_refl _
  | c::cs, h => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h c List.mem_cons_self))
      (sum_congr left right cs (fun d hd => h d (List.mem_cons_of_mem c hd)))

/-- Exact rational coefficient for the retained increment and response gain. -/
def responseQuarter : Q' := Q'.mkPos 1 4 (by decide)

/-- Entire source-increment correction in the actual original channels. -/
def squareChannelIncrement (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (depth : Nat) : Q' :=
  let g := terminalMessage w K width depth
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
    (fun c => sourceIncrementCost (N width) w K (List.range (N width))
      (squareChannelSource w K scale width hwidth g c) f)

/-- Computed eigenresponse squares of those SAME signed channel sources. -/
def squareChannelResponseSquares (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (depth : Nat) : Q' :=
  let g := terminalMessage w K width depth
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  channelSum (productChannels (N width) w K (spectatorBlocks scale width hwidth))
    (fun c =>
      (eigenResponse (N width) (qpow w (12*side scale))
        (squareChannelSource w K scale width hwidth g c) f) *
      (eigenResponse (N width) (qpow w (12*side scale))
        (squareChannelSource w K scale width hwidth g c) f))

/-- The whole exact signed cost after BOTH actual Wilson heat images. -/
def exactChannelHeatCost (w : Q') (K scale width : Nat)
    (hwidth : side scale < width) (depth : Nat) : Q' :=
  let g := terminalMessage w K width depth
  let a := qpow w (12*side scale)
  let b := qpow w (32*side scale)
  (1-b)*squareChannelMass w K scale width hwidth g+
    (1+b-2*a)*squareChannelMoment w K scale width hwidth g

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (h2 : 2 ≤ K)
  (depth scale : Nat) (hwidth : side scale < width)

set_option quotPrecheck false in
local notation "f" => sourceCharacter width (paddedSquare scale width hwidth).edges 1
local notation "g" => terminalMessage w K width depth
local notation "cs" => productChannels (N width) w K (spectatorBlocks scale width hwidth)
local notation "I" => squareChannelIncrement w K scale width hwidth depth
local notation "R" => squareChannelResponseSquares w K scale width hwidth depth
local notation "B" => exactChannelHeatCost w K scale width hwidth depth
local notation "Z" => oddMass w K width depth

include hw0 hw1 hK in
/-- Positivity uses the existing original finite heat certificate and its
explicit headCutoff guard, independently of the algebraic label-two guard. -/
theorem squareChannelIncrement_nonnegative : (0 : Q') ≤ I := by
  unfold squareChannelIncrement
  apply sum_nonnegative
  · exact productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K _
  · intro c hc
    have hb := squareChannelSource_supported w K scale width hwidth g
      (terminalMessage_supported w K width depth) c hc
    let r := polyMul (jump (N width) (squareChannelSource w K scale width hwidth g c.2))
      (jump (N width) f)
    have hr := supported_polyMul (jump_supported hb)
      (jump_supported (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1))
    exact (productHeatCertificate (N width) hw0 hw1 K hK (List.range (N width))
      (fun _ hi => List.mem_range.mp hi)).square_insertion_nonnegative r hr

include hw0 hw1 hK h2 in
/-- Keep the complete computed negative response gain, with no OWN-mean
identification or independence premise on the original endpoint source. -/
theorem squareChannelResponseSquares_le_increment : R ≤ I := by
  unfold squareChannelResponseSquares squareChannelIncrement
  apply sum_le
  · exact productChannels_nonnegative (N width) (Q'.le_of_lt hw0) K _
  · intro c hc
    exact sourceIncrement_ge_eigenResponse_square (N width) hw0 hw1 K hK
      (List.range (N width)) (CayleyParentInj.range_nodup _) (fun _ hi => List.mem_range.mp hi)
      (squareChannelSource_supported w K scale width hwidth g
        (terminalMessage_supported w K width depth) c hc)
      (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1)
      (qpow w (12*side scale)) (paddedSquare_fundamental_fullRange scale width hwidth w K (by omega))

/-- The same channel increment survives arbitrary rational centering. -/
theorem squareChannelIncrement_shifted (c : Q') :
    channelSum cs (fun z => sourceIncrementCost (N width) w K (List.range (N width))
      (squareChannelSource w K scale width hwidth g z) (shifted f c)) ≈ I := by
  unfold squareChannelIncrement
  exact sum_congr _ _ cs (fun z hz => sourceIncrementCost_shifted (N width) w K
    (List.range (N width)) (fun _ hi => List.mem_range.mp hi)
    (squareChannelSource_supported w K scale width hwidth g
      (terminalMessage_supported w K width depth) z hz)
    (sourceCharacter_supported width (paddedSquare scale width hwidth).edges 1) c)

include h2 in
/-- Exact original energy plus its entire channel source increment. -/
theorem paddedSquare_channel_exact_cost : 4*energy w K width g f+I ≈ 2*B :=
  Q'.eqv_trans _ _ _ (paddedSquare_terminal_channel_cost scale width hwidth w K h2 depth)
    (Q'.mul_eqv_congr_left 2 _ _ (poly_identity_of_normal_eq
      (.add (.mul (.add (.add (.const 1) (.neg (.mul (.const 2) (.var 0)))) (.var 1)) (.var 3))
        (.mul (.add (.const 1) (.neg (.var 1))) (.var 2)))
      (.add (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))
        (.mul (.add (.add (.const 1) (.var 1)) (.neg (.mul (.const 2) (.var 0)))) (.var 3)))
      (by decide) (fun
        | 0 => qpow w (12*side scale)
        | 1 => qpow w (32*side scale)
        | 2 => squareChannelMass w K scale width hwidth g
        | _ => squareChannelMoment w K scale width hwidth g)))

private theorem quarter_solve (e i b : Q') (he : 4*e+i ≈ 2*b) :
    e ≈ HalfPow.half*b-responseQuarter*i := by
  have h4 : 4*e ≈ 2*b-i := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.const 4) (.var 0)) (.var 1)) (.neg (.var 1)))
      (.mul (.const 4) (.var 0)) (by decide) (fun | 0 => e | _ => i)).symm
    (Q'.add_eqv_congr' he (Q'.eqv_refl (-i)))
  have hq4 : responseQuarter*4 ≈ 1 := by decide
  have hq2 : responseQuarter*2 ≈ HalfPow.half := by decide
  have hl : responseQuarter*(4*e) ≈ e := Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv responseQuarter 4 e).symm
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ e hq4) (Q'.one_mul_eqv e))
  have hr : responseQuarter*(2*b-i) ≈ HalfPow.half*b-responseQuarter*i :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.var 0) (.add (.mul (.const 2) (.var 1)) (.neg (.var 2))))
      (.add (.mul (.mul (.var 0) (.const 2)) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => responseQuarter | 1 => b | _ => i))
      (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ b hq2) (Q'.eqv_refl _))
  exact Q'.eqv_trans _ _ _ hl.symm
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left responseQuarter _ _ h4) hr)

include h2 in
/-- The original normalized energy retains its COMPLETE negative increment. -/
theorem paddedSquare_energy_exactChannel_increment :
    let r := Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK depth)
    normalizedEnergy hw0 hw1 K width hK depth f ≈
      HalfPow.half*(B*r)-responseQuarter*(I*r) := by
  dsimp only
  let r := Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK depth)
  have hraw := quarter_solve (energy w K width g f) I B
    (paddedSquare_channel_exact_cost K width h2 depth scale hwidth)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ r hraw)
    (poly_identity_of_normal_eq
      (.mul (.add (.mul (.var 0) (.var 2))
        (.neg (.mul (.var 1) (.var 3)))) (.var 4))
      (.add (.mul (.var 0) (.mul (.var 2) (.var 4)))
        (.neg (.mul (.var 1) (.mul (.var 3) (.var 4)))))
      (by decide) (fun | 0 => HalfPow.half | 1 => responseQuarter | 2 => B | 3 => I | _ => r))

include h2 in
/-- ORIGINAL normalized nonperturbative ceiling, preserving the signed heat
coefficient and computed negative channel response squares. No Taylor debt
or omitted-mode estimate enters, and SAME-OWN-variance scaling remains open. -/
theorem paddedSquare_energy_exactChannel_response_bound :
    let a := qpow w (12*side scale)
    let b := qpow w (32*side scale)
    let M := squareChannelMass w K scale width hwidth g
    let F := squareChannelMoment w K scale width hwidth g
    let r := Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK depth)
    normalizedEnergy hw0 hw1 K width hK depth f ≤
      HalfPow.half*(((1-b)*M+(1+b-2*a)*F)*r)-responseQuarter*(R*r) := by
  dsimp only
  let r := Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK depth)
  have hR := squareChannelResponseSquares_le_increment hw0 hw1 K width hK h2 depth scale hwidth
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ responseQuarter
    (Q'.mul_le_mul_of_nonneg_right _ _ r hR (Q'.le_of_lt (Q'.recipPos_pos Z _)))
    (by decide : (0 : Q') ≤ responseQuarter)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (paddedSquare_energy_exactChannel_increment hw0 hw1 K width hK h2 depth scale hwidth))
    (Q'.add_le_add_left (HalfPow.half*(B*r)) _ _ (Q'.neg_le_neg hscaled))

#print axioms responseQuarter
#print axioms squareChannelIncrement
#print axioms squareChannelResponseSquares
#print axioms exactChannelHeatCost
#print axioms squareChannelIncrement_nonnegative
#print axioms squareChannelResponseSquares_le_increment
#print axioms squareChannelIncrement_shifted
#print axioms paddedSquare_channel_exact_cost
#print axioms paddedSquare_energy_exactChannel_increment
#print axioms paddedSquare_energy_exactChannel_response_bound

end YMGap.Continuum.BF4DyadicWilsonSquareChannelExactResponse
