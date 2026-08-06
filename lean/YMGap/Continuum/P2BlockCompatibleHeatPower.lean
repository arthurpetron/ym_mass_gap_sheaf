/-
Track 11.7-fusion / R3a -- physical heat-power transport on the
block-compatible `pGamma = 2` schedule.

The schedule identity `4 * u_(k+1) = u_k`, together with constructive
Bernoulli, gives

    w_k <= w_(k+1)^4.

Monotonicity of finite powers then transports every SU(2) heat coefficient
from a coarse plaquette to the four fine plaquettes in a square block.  This
is the exact coefficient-level `fusionPower` input.  It does not assert the
still-open all-scale comparison of the normalized fused amplitudes.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleSchedule

namespace YMGap.Continuum.P2BlockCompatibleHeatPower

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.FusionRDFactor
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem four_mul_blockQuarter_eqv_one :
    Q'.ofNat 4 * blockQuarter ≈ (1 : Q') := by
  decide

/-- Exact quarter-margin arithmetic behind a square blocking step. -/
theorem four_mul_blockMargin_succ_eqv (k : Nat) :
    Q'.ofNat 4 * blockMargin (k + 1) ≈ blockMargin k := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ (blockMargin_succ_eqv k)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat 4) (blockMargin k) blockQuarter)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ blockQuarter
      (Q'.mul_comm_eqv (Q'.ofNat 4) (blockMargin k))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (blockMargin k) (Q'.ofNat 4) blockQuarter) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (blockMargin k) _ _
      four_mul_blockQuarter_eqv_one) ?_
  exact Q'.mul_one_eqv (blockMargin k)

/-- The coarse weight is value-equal to the linear Bernoulli lower bound at
the fine scale. -/
theorem one_sub_four_mul_blockMargin_succ_eqv (k : Nat) :
    (1 : Q') - Q'.ofNat 4 * blockMargin (k + 1) ≈ blockWeight k := by
  unfold blockWeight
  exact Q'.add_eqv_congr_left (1 : Q') _ _
    (Q'.neg_eqv_congr _ _ (four_mul_blockMargin_succ_eqv k))

/-- Physical square-block heat transport: one coarse heat weight is bounded
by the fourth power of the fine heat weight. -/
theorem blockWeight_le_fine_fourth (k : Nat) :
    blockWeight k <= qpow (blockWeight (k + 1)) 4 := by
  have hBernoulli := bernoulli_oneSub
    (blockMargin (k + 1))
    (blockMargin_nonneg (k + 1))
    (blockMargin_le_one (k + 1)) 4
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (one_sub_four_mul_blockMargin_succ_eqv k))
    hBernoulli

/-- Channelwise Casimir-power refinement of `blockWeight_le_fine_fourth`.
The exponent `4 * c4 s` is exactly the four-plaquette square-block power. -/
theorem blockHeatCoeff_le_fine_fourfold (k s : Nat) :
    qpow (blockWeight k) (c4 s) <=
      qpow (blockWeight (k + 1)) (4 * c4 s) := by
  have hpow := qpow_mono
    (blockWeight_nonneg k)
    (blockWeight_le_fine_fourth k)
    (c4 s)
  exact Q'.le_trans' _ _ _ hpow
    (Q'.le_of_eqv
      (HeatKernelRGStep.qpow_qpow (blockWeight (k + 1)) 4 (c4 s)))

#print axioms four_mul_blockMargin_succ_eqv
#print axioms blockWeight_le_fine_fourth
#print axioms blockHeatCoeff_le_fine_fourfold

end YMGap.Continuum.P2BlockCompatibleHeatPower
