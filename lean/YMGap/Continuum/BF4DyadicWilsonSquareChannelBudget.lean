/-
# Cancellation-preserving budget for the original growing-square energy

After retaining all spectator heat in the actual computed channels, the
complete signed cost has a geometric defect term linear in 1-w^L and a
quadratic remainder. The original terminal energy and channel correction
are unchanged. No comparison to the original partition or centered variance
is assumed or asserted; changing-scale survival is still open.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareChannelCost
import YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
import YMGap.Continuum.SU2HeatPlaquetteGeometricBudget

namespace YMGap.Continuum.BF4DyadicWilsonSquareChannelBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelPartition
open YMGap.Continuum.BF4DyadicWilsonSquarePassiveChannels
open YMGap.Continuum.BF4DyadicWilsonSquareChannelCost
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
open YMGap.Continuum.SU2QuaternionProductHeatGramChannels
open YMGap.Continuum.SU2QuaternionProductHeatPassiveChannels
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung (sourceIncrementCost)
open YMGap.Continuum.SU2HeatPlaquetteGeometricBudget

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

private theorem qpow_rg (w : Q') : ∀ n, qpow w n = RGTransport.qpow w n
  | 0 => rfl
  | n+1 => congrArg (fun x : Q' => x*w) (qpow_rg w n)

private theorem collected_reorder (a b A M : Q') :
    (1 + -((2 : Q')*a) + b)*M + (1 + -b)*A ≈
      (1-b)*A + (1+b-(2 : Q')*a)*M :=
  poly_identity_of_normal_eq
    (.add (.mul (.add (.add (.const 1) (.neg (.mul (.const 2) (.var 0))))
      (.var 1)) (.var 3)) (.mul (.add (.const 1) (.neg (.var 1))) (.var 2)))
    (.add (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))
      (.mul (.add (.add (.const 1) (.var 1))
        (.neg (.mul (.const 2) (.var 0)))) (.var 3)))
    (by decide) (fun | 0 => a | 1 => b | 2 => A | _ => M)

/-- The scalar bound keeps the geometric cancellation before estimating.
Both moment hypotheses will be supplied by actual channel certificates. -/
theorem collected_cost_le {w A M : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (L : Nat) (hA : (0 : Q') ≤ A)
    (hgeom : (0 : Q') ≤ (4 : Q')*A-M) :
    (1 + -((2 : Q')*qpow w (12*L)) + qpow w (32*L))*M +
        (1 + -(qpow w (32*L)))*A ≤
      (8 : Q')*(1-qpow w L)*((4 : Q')*A-M) +
        (960 : Q')*((1-qpow w L)*(1-qpow w L))*A := by
  let u := qpow w L
  have h12 : qpow w (12*L) ≈ RGTransport.qpow u 12 := by
    dsimp only [u]
    rw [qpow_rg, qpow_rg, Nat.mul_comm 12 L]
    exact Q'.eqv_symm (HeatKernelRGStep.qpow_qpow w L 12)
  have h32 : qpow w (32*L) ≈ RGTransport.qpow u 32 := by
    dsimp only [u]
    rw [qpow_rg, qpow_rg, Nat.mul_comm 32 L]
    exact Q'.eqv_symm (HeatKernelRGStep.qpow_qpow w L 32)
  have hu0 : (0 : Q') ≤ u := by
    dsimp only [u]
    rw [qpow_rg]
    exact RGTransport.qpow_nonneg w hw0 L
  have hu1 : u ≤ (1 : Q') := by
    dsimp only [u]
    rw [qpow_rg]
    exact HeatKernelGap.qpow_le_one hw0 hw1 L
  have hpin :
      (1-qpow w (32*L))*A + (1+qpow w (32*L)-(2 : Q')*qpow w (12*L))*M ≈
        (1-RGTransport.qpow u 32)*A +
          (1+RGTransport.qpow u 32-(2 : Q')*RGTransport.qpow u 12)*M :=
    Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ A
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ h32)))
      (Q'.mul_eqv_congr_right _ _ M (Q'.add_eqv_congr'
        (Q'.add_eqv_congr_left _ _ _ h32)
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _ h12))))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (collected_reorder (qpow w (12*L)) (qpow w (32*L)) A M) hpin))
    (plaquette_geometric_cost_le hu0 hu1 hA hgeom)

/-- Concrete signed budget on the ORIGINAL terminal energy, with every
channel moment and cap hypothesis constructed from its actual source. -/
theorem paddedSquare_terminal_signed_geometric_budget {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (scale width : Nat) (hwidth : side scale < width)
    (K : Nat) (hK : 2 ≤ K) (depth : Nat) :
    let g := terminalMessage w K width depth
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let cs := productChannels (N width) w K (spectatorBlocks scale width hwidth)
    let A := squareChannelMass w K scale width hwidth g
    let G := squareChannelGeometricCost w K scale width hwidth g
    let u := qpow w (side scale)
    (4 : Q')*energy w K width g f +
        channelSum cs (fun c => sourceIncrementCost (N width) w K
          (List.range (N width)) (squareChannelSource w K scale width hwidth g c) f) ≤
      (2 : Q')*((8 : Q')*(1-u)*G + (960 : Q')*((1-u)*(1-u))*A) := by
  dsimp only
  have hg := terminalMessage_supported w K width depth
  have hA := squareChannelMass_nonnegative hw0 K scale width hwidth _ hg
  have hG := squareChannelGeometricCost_nonnegative hw0 K scale width hwidth _ hg
  have hb := collected_cost_le hw0 hw1 (side scale) hA hG
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (paddedSquare_terminal_channel_cost scale width hwidth w K hK depth))
    (Q'.mul_le_mul_of_nonneg_left _ _ (2 : Q') hb (by decide))

#print axioms collected_cost_le
#print axioms paddedSquare_terminal_signed_geometric_budget

end YMGap.Continuum.BF4DyadicWilsonSquareChannelBudget
