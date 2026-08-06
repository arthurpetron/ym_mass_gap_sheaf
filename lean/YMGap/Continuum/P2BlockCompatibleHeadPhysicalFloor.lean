/-
Track 11.7-fusion / R3j -- scale-uniform physical tail floor for the
Dirichlet head compiler.

The physical endpoint occurs at a Casimir exponent of order the heat
denominator.  Instead of evaluating that growing power, split the exponent
into 34 identical Bernoulli blocks.  Each block has length `D/16`, hence
weight at least `15/16`; the fixed rational certificate

    (15/16)^34 >= 1/9

then gives a uniform endpoint floor at every scale.  This is a proof about
the computation, not a scale-by-scale computation.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleScheduleClosed
import YMGap.Continuum.AbelianFusionCLT
import YMGap.Continuum.BulkModeCrux
import YMGap.Continuum.FusedAmplitudeDerivation
import YMGap.Continuum.BondMovingStep

namespace YMGap.Continuum.P2BlockCompatibleHeadPhysicalFloor

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AbelianFusionCLT
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- One sixteenth of the physical heat denominator at scale `j+1`. -/
def physicalBernoulliChunk (j : Nat) : Nat := 3 * 4 ^ j

theorem physicalBernoulliChunk_pos (j : Nat) :
    0 < physicalBernoulliChunk j := by
  unfold physicalBernoulliChunk
  exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

theorem physicalWeightDen_eq_sixteen_chunks (j : Nat) :
    physicalWeightDen (j + 1) = 16 * physicalBernoulliChunk j := by
  unfold physicalWeightDen physicalBernoulliChunk
  rw [Nat.pow_succ]
  omega

private theorem ofNat_mul_scaled_unit_eqv (L c : Nat)
    (hL : 0 < L) (hc : 0 < c) :
    Q'.ofNat L * Q'.mkPos 1 (c * L) (Nat.mul_pos hc hL) ≈
      Q'.mkPos 1 c hc := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast, Q'.mkPos_num, Q'.mkPos_den]
  push_cast
  ac_rfl

private theorem mkPos_one_eqv_of_den_eq (left right : Nat)
    (hleft : 0 < left) (hright : 0 < right) (h : left = right) :
    Q'.mkPos 1 left hleft ≈ Q'.mkPos 1 right hright := by
  unfold Q'.eqv
  simp only [Q'.mkPos_num, Q'.mkPos_den, Int.one_mul]
  exact_mod_cast h.symm

/-- A chunk consumes exactly `1/16` of the physical heat margin. -/
theorem chunk_mul_margin_eqv_sixteenth (j : Nat) :
    Q'.ofNat (physicalBernoulliChunk j) *
        ((1 : Q') - blockWeight (j + 1)) ≈
      Q'.mkPos 1 16 (by decide) := by
  have hmargin := one_sub_blockWeight_eqv_margin (j + 1)
  have hclosed := blockMargin_eqv_closed (j + 1)
  have hden := physicalWeightDen_eq_sixteen_chunks j
  have hmarginClosed :
      ((1 : Q') - blockWeight (j + 1)) ≈
        Q'.mkPos 1
          (16 * physicalBernoulliChunk j)
          (Nat.mul_pos (by decide) (physicalBernoulliChunk_pos j)) := by
    refine Q'.eqv_trans _ _ _ hmargin ?_
    refine Q'.eqv_trans _ _ _ hclosed ?_
    exact mkPos_one_eqv_of_den_eq _ _ _ _ hden
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat (physicalBernoulliChunk j)) _ _
      hmarginClosed) ?_
  exact ofNat_mul_scaled_unit_eqv
    (physicalBernoulliChunk j) 16 (physicalBernoulliChunk_pos j) (by decide)

/-- The shifted physical cutoff square fits inside 34 Bernoulli chunks. -/
theorem endpointExponent_le_chunks (j : Nat) :
    c4 (blockNcut (j + 1) - 1) <= 34 * physicalBernoulliChunk j := by
  let N := blockNcut (j + 1)
  have hNpos : 0 < N := blockNcut_pos (j + 1)
  have hpred : N - 1 <= N := Nat.sub_le N 1
  have hcmono : c4 (N - 1) <= c4 N :=
    SpectralLocalizationCrux.c4_le_c4 hpred
  have hcas := c4_succ_eq_sq N
  have hclosed' : N + 1 = 10 * 2 ^ j := by
    dsimp only [N]
    rw [blockNcut_closed, Nat.pow_succ]
    omega
  have hsquare : (N + 1) * (N + 1) = 100 * 4 ^ j := by
    rw [hclosed', CasimirMoment.four_pow_eq]
    change (10 * 2 ^ j) * (10 * 2 ^ j) =
      100 * (2 ^ j * 2 ^ j)
    rw [show (100 : Nat) = 10 * 10 by decide]
    ac_rfl
  have hcBound : c4 N <= 100 * 4 ^ j := by
    omega
  unfold physicalBernoulliChunk
  have hscale : 100 * 4 ^ j <= 34 * (3 * 4 ^ j) := by
    have hp : 0 < 4 ^ j := Nat.pow_pos (by decide)
    omega
  exact Nat.le_trans hcmono (Nat.le_trans hcBound hscale)

private theorem fixed_block_floor :
    Q'.mkPos 1 9 (by decide) <=
      qpow (Q'.mkPos 15 16 (by decide)) 34 := by
  decide

/-- Uniform physical tail floor.  The proof cost is constant in `j`: one
Bernoulli block, base monotonicity, exponent monotonicity, and a fixed closed
rational comparison. -/
theorem physical_endpoint_qpow_floor (j : Nat) :
    Q'.mkPos 1 9 (by decide) <=
      qpow (blockWeight (j + 1))
        (c4 (blockNcut (j + 1) - 1)) := by
  let L := physicalBernoulliChunk j
  let w := blockWeight (j + 1)
  have hw0 : (0 : Q') <= w := blockWeight_nonneg (j + 1)
  have hw1 : w <= (1 : Q') := blockWeight_le_one (j + 1)
  have hbernRaw := qpow_ge_bernoulli hw0 hw1 L
  have hmargin := chunk_mul_margin_eqv_sixteenth j
  have hleft :
      ((1 : Q') - Q'.ofNat L * ((1 : Q') - w)) ≈
        Q'.mkPos 15 16 (by decide) := by
    unfold L w
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (1 : Q') _ _
        (Q'.neg_eqv_congr _ _ hmargin)) ?_
    decide
  have hblock : Q'.mkPos 15 16 (by decide) <= qpow w L :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hbernRaw
  have hblockPow :
      qpow (Q'.mkPos 15 16 (by decide)) 34 <=
        qpow (qpow w L) 34 :=
    qpow_mono_base (by decide) hblock 34
  have hiter : qpow (qpow w L) 34 ≈ qpow w (L * 34) :=
    qpow_qpow w L 34
  have hlarge : Q'.mkPos 1 9 (by decide) <= qpow w (L * 34) :=
    Q'.le_trans' _ _ _ fixed_block_floor
      (Q'.le_trans' _ _ _ hblockPow (Q'.le_of_eqv hiter))
  have hexp : c4 (blockNcut (j + 1) - 1) <= L * 34 := by
    unfold L
    have h := endpointExponent_le_chunks j
    simpa only [Nat.mul_comm] using h
  exact Q'.le_trans' _ _ _ hlarge
    (qpow_antitone hw0 hw1 _ _ hexp)

/-- The penultimate physical coefficient retains at least one ninth of its
unweighted dimension. -/
theorem physical_endpoint_coeff_floor (j : Nat) :
    Q'.ofNat (blockNcut (j + 1)) * Q'.mkPos 1 9 (by decide) <=
      coeffW (blockWeight (j + 1)) (blockNcut (j + 1) - 1) := by
  let N := blockNcut (j + 1)
  let w := blockWeight (j + 1)
  have hNpos : 0 < N := blockNcut_pos (j + 1)
  have hpow := physical_endpoint_qpow_floor j
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (dimQ (N - 1)) hpow
    (dimQ_nonneg (N - 1))
  have hdim : dimQ (N - 1) = Q'.ofNat N := by
    unfold dimQ
    rw [Nat.sub_add_cancel (by omega : 1 <= N)]
  dsimp only [N, w] at hmul ⊢
  rw [hdim] at hmul
  exact hmul

/-- Squared form consumed by the boundary reserve. -/
theorem physical_endpoint_coeff_sq_floor (j : Nat) :
    (Q'.ofNat (blockNcut (j + 1)) * Q'.mkPos 1 9 (by decide)) *
        (Q'.ofNat (blockNcut (j + 1)) * Q'.mkPos 1 9 (by decide)) <=
      coeffW (blockWeight (j + 1)) (blockNcut (j + 1) - 1) *
        coeffW (blockWeight (j + 1)) (blockNcut (j + 1) - 1) := by
  have h := physical_endpoint_coeff_floor j
  exact Q'.mul_le_mul_of_nonneg h h
    (coeffW_nonneg (blockWeight_nonneg (j + 1)) _)
    (Q'.mul_nonneg _ _ (zero_le_ofNat _) (by decide))

#print axioms physicalWeightDen_eq_sixteen_chunks
#print axioms endpointExponent_le_chunks
#print axioms physical_endpoint_qpow_floor
#print axioms physical_endpoint_coeff_floor
#print axioms physical_endpoint_coeff_sq_floor

end YMGap.Continuum.P2BlockCompatibleHeadPhysicalFloor
