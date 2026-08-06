/-
Track 11.7-fusion / R3f -- normalized mode-one cross compiler.

# Result

The crude endpoint-Lipschitz route is valid but provably too large.  The
physical mode-one tail is therefore rewritten in its cancellation-preserving
form.  Since

    lambda_k = A_k / D_k,

where `A_k` is the adjacent character correlation and `D_k` its squared
norm, the square step is exactly the division-free cross inequality

    A_k * D_(k+1)^2 <= D_k * A_(k+1)^2.

This module proves once and for all that those finite-sum cross products
compile to `BlockCompatibleP2ModeOneTailMonotonicity`.  Future certificates
can reason about the normalized cancellation without evaluating rational
quotients or carrying proof-dependent denominators.

# Constructivity

Finite `Q'` sums and positive-denominator cancellation only.  No `Classical`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleEndpointCriterion

namespace YMGap.Continuum.P2BlockCompatibleModeOneCross

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusionMarginMono
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleCells
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- Adjacent-correlation numerator of the physical fundamental quotient. -/
def blockModeOneNum (k : Nat) : Q' :=
  adjCorr (blockWeight k) (blockNcut k)

/-- Squared-norm denominator of the physical fundamental quotient. -/
def blockModeOneDen (k : Nat) : Q' :=
  coordNormSq (blockWeight k) (blockNcut k)

theorem blockModeOneDen_pos (k : Nat) :
    (0 : Q') < blockModeOneDen k := by
  unfold blockModeOneDen
  exact FusedRatioCorridor.pos_of_one_le
    (coordNormSq_ge_one (blockWeight_nonneg k) (blockNcut k))

/-- Strip the physical mode-one quotient to its two finite character sums. -/
theorem blockRawModeOne_eqv_crossRatio (k : Nat) :
    blockRawModeOne k ≈
      Q'.divPos (blockModeOneNum k) (blockModeOneDen k)
        (blockModeOneDen_pos k) := by
  unfold blockRawModeOne blockModeOneNum blockModeOneDen
  exact vacNorm_fundamental_eq_ratio
    (blockWeight_nonneg k) (blockWeight_le_one k) (blockNcut k)

/-- Cancellation-preserving all-scale residual.  It is division-free and
contains exactly three finite sums at each physical square step. -/
structure BlockCompatibleP2ModeOneCrossTail : Type where
  cross : forall k, 2 <= k ->
    blockModeOneNum k *
        (blockModeOneDen (k + 1) * blockModeOneDen (k + 1)) <=
      blockModeOneDen k *
        (blockModeOneNum (k + 1) * blockModeOneNum (k + 1))

private theorem qpow_two_eqv (x : Q') : qpow x 2 ≈ x * x := by
  show ((1 : Q') * x) * x ≈ x * x
  exact Q'.mul_eqv_congr_right _ _ x (Q'.one_mul_eqv x)

/-- Cross multiplication compiles the finite-sum residual to the exact raw
mode-one square comparison consumed by the physical bridge. -/
def BlockCompatibleP2ModeOneCrossTail.toModeOneTailMonotonicity
    (C : BlockCompatibleP2ModeOneCrossTail) :
    BlockCompatibleP2ModeOneTailMonotonicity where
  tail := fun k hk => by
    let A0 := blockModeOneNum k
    let D0 := blockModeOneDen k
    let A1 := blockModeOneNum (k + 1)
    let D1 := blockModeOneDen (k + 1)
    have hD0 : (0 : Q') < D0 := blockModeOneDen_pos k
    have hD1 : (0 : Q') < D1 := blockModeOneDen_pos (k + 1)
    have hD1sq : (0 : Q') < D1 * D1 := Q'.mul_pos hD1 hD1
    have hcross : A0 * (D1 * D1) <= (A1 * A1) * D0 :=
      Q'.le_trans' _ _ _ (C.cross k hk)
        (Q'.le_of_eqv (Q'.mul_comm_eqv D0 (A1 * A1)))
    have hratio :
        Q'.divPos A0 D0 hD0 <=
          Q'.divPos (A1 * A1) (D1 * D1) hD1sq :=
      divPos_le_divPos_of_cross A0 D0 (A1 * A1) (D1 * D1)
        hD0 hD1sq hcross
    have hcoarse := blockRawModeOne_eqv_crossRatio k
    have hfine := blockRawModeOne_eqv_crossRatio (k + 1)
    have hsquare :
        Q'.divPos (A1 * A1) (D1 * D1) hD1sq ≈
          blockRawModeOne (k + 1) * blockRawModeOne (k + 1) := by
      refine Q'.eqv_trans _ _ _
        (P2BlockCompatibleSchedule.divPos_square_eqv A1 D1 hD1) ?_
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hfine))
        (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hfine))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcoarse)
      (Q'.le_trans' _ _ _ hratio
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hsquare
          (Q'.eqv_symm (qpow_two_eqv (blockRawModeOne (k + 1)))))))

#print axioms blockModeOneDen_pos
#print axioms blockRawModeOne_eqv_crossRatio
#print axioms BlockCompatibleP2ModeOneCrossTail.toModeOneTailMonotonicity

end YMGap.Continuum.P2BlockCompatibleModeOneCross
