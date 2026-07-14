/-
Square-root block tail bound for the lower-six harmonic Gaussian weight.

At the physical range `k >= 247`, advancing by one moving square-root
window center increases the quadratic exponent by at least seven harmonic
blocks.  The already proved one-block bound `w^(k+2) <= 1/2` therefore gives
an inter-block ratio `2^-7`.  Reindexing an arbitrary finite tail into these
blocks and summing geometrically yields the exact multiplier `128/127`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxSummedEnvelope
import YMGap.Continuum.RDThetaCentered

namespace YMGap.Continuum.HarmonicLowerSixSquareRootBlockTail

set_option maxHeartbeats 200000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicGrowingAnchorPF2
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem block_tail_neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "block_tail_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               block_tail_neg_num_cast, Q'.ofNat_num_cast,
               Q'.ofNat_den_cast,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl,
               show (0 : Q').num = 0 from rfl,
               show ((0 : Q').den : Int) = 1 from rfl,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.neg_zero, Int.zero_mul,
               Int.mul_zero, Int.one_mul, Int.mul_one];
             ac_rfl))

/-- Gaussian blocks of length the moving square-root center, beginning at
the first mode beyond the retained left prefix. -/
def lowerSixGaussianTailBlock (k i : Nat) : Q' :=
  let c := thetaWindowCenter k
  let K := thetaWindowLeft k + 1
  finSum (fun s => lowerSixModeWeight k (K + i * c + s)) c

/-- Uniform inter-block rate on the physical tail range. -/
def lowerSixBlockRate : Q' := qpow HalfPow.half 7

/-- Exact geometric closure multiplier `1/(1-2^-7)`. -/
def lowerSixBlockClosure : Q' := Q'.mkPos 128 127 (by decide)

private theorem harmonic_seven_blocks_le_rate (k : Nat) :
    qpow (harmW k) ((k + 2) * 7) ≤ lowerSixBlockRate := by
  let p := qpow (harmW k) (k + 2)
  have hp0 : (0 : Q') ≤ p := qpow_nonneg _ (harmW_nonneg k) _
  have hp : p ≤ HalfPow.half := by
    dsimp only [p]
    exact harmonic_block_power_le_half k
  have hmono := FusedAmplitudeDerivation.qpow_mono_base hp0 hp 7
  unfold lowerSixBlockRate
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm
      (HeatKernelRGStep.qpow_qpow (harmW k) (k + 2) 7))) hmono

private theorem seven_den_le_double_center_delta
    {k r : Nat} (hk : 247 ≤ k)
    (hr : thetaWindowLeft k + 1 ≤ r) :
    7 * (k + 2) ≤
      (2 * r * thetaWindowCenter k +
        thetaWindowCenter k * thetaWindowCenter k) +
      (2 * r * thetaWindowCenter k +
        thetaWindowCenter k * thetaWindowCenter k) := by
  let c := thetaWindowCenter k
  let D := k + 2
  have hc22 : 22 ≤ c := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hnext : 2 * D + 1 < (c + 1) * (c + 1) := by
    rcases Nat.lt_or_ge (2 * D + 1) ((c + 1) * (c + 1)) with h | h
    · exact h
    · have hbad : c + 1 ≤ c := by
        dsimp only [c, D, thetaWindowCenter, thetaWindowLength] at h ⊢
        exact ChebOrthoMidpointEst.isqrt_ge h
      omega
  have hsquare : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  rw [hsquare] at hnext
  have htwoD : 2 * D < c * c + 2 * c := by omega
  have hscaled : 7 * (2 * D) < 7 * (c * c + 2 * c) := by omega
  have hc14 : 14 * c ≤ c * c := by
    have h := Nat.mul_le_mul_right c (show 14 ≤ c by omega)
    simpa [Nat.mul_comm] using h
  have hupper : 7 * (c * c + 2 * c) ≤ 8 * (c * c) := by
    rw [Nat.mul_add]
    have hsevenTwo : 7 * (2 * c) = 14 * c := by omega
    rw [hsevenTwo]
    omega
  have hseven : 7 * D ≤ 4 * (c * c) := by omega
  have hcr : c ≤ 2 * r := by
    dsimp only [c]
    unfold thetaWindowLeft at hr
    omega
  have hmul : c * c ≤ (2 * r) * c := Nat.mul_le_mul_right c hcr
  dsimp only [c, D] at hseven hmul ⊢
  omega

/-- Advancing one square-root block suppresses every physical tail mode by
the derived rate `2^-7`. -/
theorem lowerSixModeWeight_center_step_le_rate
    {k r : Nat} (hk : 247 ≤ k)
    (hr : thetaWindowLeft k + 1 ≤ r) :
    lowerSixModeWeight k (r + thetaWindowCenter k) ≤
      lowerSixBlockRate * lowerSixModeWeight k r := by
  let c := thetaWindowCenter k
  let w := harmW k
  let sigma := w * w
  let delta := 2 * r * c + c * c
  change lowerSixModeWeight k (r + c) ≤
    lowerSixBlockRate * lowerSixModeWeight k r
  have hexp : (r + c) * (r + c) = r * r + delta := by
    dsimp only [delta]
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    rw [show c * r = r * c from Nat.mul_comm c r]
    have htwo : 2 * r * c = r * c + r * c := by
      rw [show 2 * r = r + r by omega, Nat.add_mul]
    rw [htwo]
    omega
  have hsplit : lowerSixModeWeight k (r + c) ≈
      lowerSixModeWeight k r * qpow sigma delta := by
    unfold lowerSixModeWeight
    dsimp only [sigma, w]
    rw [hexp]
    exact HeatKernelRGStep.qpow_add _ _ _
  have hdouble : qpow sigma delta ≈ qpow w (delta + delta) := by
    dsimp only [sigma]
    refine Q'.eqv_trans _ _ _
      (FusionQuotientCollapse.qpow_mul_self w delta) ?_
    exact Q'.eqv_symm (HeatKernelRGStep.qpow_add w delta delta)
  have hD : (k + 2) * 7 ≤ delta + delta := by
    have h := seven_den_le_double_center_delta hk hr
    dsimp only [c, delta] at h ⊢
    simpa [Nat.mul_comm] using h
  have hwGain : qpow w (delta + delta) ≤ qpow w ((k + 2) * 7) :=
    HeatKernelRGStep.qpow_antitone (harmW_nonneg k) (harmW_le_one k)
      ((k + 2) * 7) (delta + delta) hD
  have hgain : qpow sigma delta ≤ lowerSixBlockRate :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hdouble)
      (Q'.le_trans' _ _ _ hwGain (harmonic_seven_blocks_le_rate k))
  have hW0 : (0 : Q') ≤ lowerSixModeWeight k r := by
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hmul : lowerSixModeWeight k r * qpow sigma delta ≤
      lowerSixModeWeight k r * lowerSixBlockRate :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgain hW0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))

private theorem finSum_add_block (f : Nat → Q') (a : Nat) : ∀ t,
    finSum f (a + t) ≈ finSum f a + finSum (fun s => f (a + s)) t
  | 0 => Q'.eqv_symm (QPoly.q_add_zero_eqv _)
  | t + 1 => by
      rw [show a + (t + 1) = (a + t) + 1 by omega,
        finSum_succ, finSum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ (finSum_add_block f a t)) ?_
      exact Q'.add_assoc_eqv _ _ _

private theorem finSum_block (f : Nat → Q') (c : Nat) : ∀ P,
    finSum f (P * c) ≈
      finSum (fun i => finSum (fun s => f (i * c + s)) c) P
  | 0 => by rw [Nat.zero_mul]; exact Q'.eqv_refl 0
  | P + 1 => by
      rw [Nat.succ_mul, finSum_succ]
      refine Q'.eqv_trans _ _ _ (finSum_add_block f (P * c) c) ?_
      exact Q'.add_eqv_congr_right _ _ _ (finSum_block f c P)

theorem lowerSixGaussianTailBlock_nonnegative (k i : Nat) :
    (0 : Q') ≤ lowerSixGaussianTailBlock k i := by
  let c := thetaWindowCenter k
  let K := thetaWindowLeft k + 1
  let f := fun s => lowerSixModeWeight k (K + i * c + s)
  have hf : ∀ s, (0 : Q') ≤ f s := by
    intro s
    dsimp only [f]
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hsum := RationalTail.finSum_monotone_of_nonneg f hf
    0 c (Nat.zero_le c)
  unfold lowerSixGaussianTailBlock
  dsimp only [c, K, f] at hsum ⊢
  exact hsum

theorem lowerSixGaussianTailBlock_step_rate
    {k : Nat} (hk : 247 ≤ k) (i : Nat) :
    lowerSixGaussianTailBlock k (i + 1) ≤
      lowerSixBlockRate * lowerSixGaussianTailBlock k i := by
  let c := thetaWindowCenter k
  let K := thetaWindowLeft k + 1
  let f := fun s => lowerSixModeWeight k (K + (i + 1) * c + s)
  let g := fun s => lowerSixBlockRate *
    lowerSixModeWeight k (K + i * c + s)
  have hterm : ∀ s, s < c → f s ≤ g s := by
    intro s _
    let r := K + i * c + s
    have hr : thetaWindowLeft k + 1 ≤ r := by
      dsimp only [r, K]
      omega
    have hidx : K + (i + 1) * c + s = r + c := by
      dsimp only [r]
      rw [Nat.add_mul]
      omega
    dsimp only [f, g]
    rw [hidx]
    exact lowerSixModeWeight_center_step_le_rate hk hr
  have hsum := YMGap.Constructive.finSum_le_lt f g c hterm
  have hpull : lowerSixBlockRate * lowerSixGaussianTailBlock k i ≈
      finSum g c := by
    unfold lowerSixGaussianTailBlock
    dsimp only [c, K, g]
    exact RationalTail.const_mul_finSum
      (fun s => lowerSixModeWeight k
        (thetaWindowLeft k + 1 + i * thetaWindowCenter k + s))
      lowerSixBlockRate (thetaWindowCenter k)
  unfold lowerSixGaussianTailBlock
  dsimp only [c, K, f] at hsum ⊢
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hpull)

/-- Every finite block prefix is bounded by `128/127` times the first block. -/
theorem lowerSixGaussianTailBlocks_le_closure
    {k : Nat} (hk : 247 ≤ k) (P : Nat) :
    finSum (lowerSixGaussianTailBlock k) P ≤
      lowerSixBlockClosure * lowerSixGaussianTailBlock k 0 := by
  let F0 := lowerSixGaussianTailBlock k 0
  let H := lowerSixBlockClosure * F0
  have hF0 : (0 : Q') ≤ F0 := by
    dsimp only [F0]
    exact lowerSixGaussianTailBlock_nonnegative k 0
  have hrate : (0 : Q') ≤ lowerSixBlockRate := by
    unfold lowerSixBlockRate
    exact qpow_nonneg _ HalfPow.half_nonneg _
  have hclosure : (0 : Q') ≤ lowerSixBlockClosure := by
    unfold lowerSixBlockClosure
    decide
  have hH : (0 : Q') ≤ H := Q'.mul_nonneg _ _ hclosure hF0
  have hcoef : (1 : Q') + lowerSixBlockRate * lowerSixBlockClosure ≈
      lowerSixBlockClosure := by
    unfold lowerSixBlockRate lowerSixBlockClosure HalfPow.half qpow
    decide
  have hrec : F0 + lowerSixBlockRate * H ≤ H := by
    apply Q'.le_of_eqv
    refine Q'.eqv_trans _
      (((1 : Q') + lowerSixBlockRate * lowerSixBlockClosure) * F0) _ ?_ ?_
    · dsimp only [H]
      block_tail_ring
    · exact Q'.mul_eqv_congr_right _ _ F0 hcoef
  have hgeom := CharacterTail.geom_series_le
    (lowerSixGaussianTailBlock k) F0 lowerSixBlockRate H
    hrate hH (Q'.le_refl' F0)
    (lowerSixGaussianTailBlock_step_rate hk) hrec P
  dsimp only [H, F0] at hgeom ⊢
  exact hgeom

/-- The long lower-six Gaussian tail is bounded by one finite square-root
block times the exact geometric closure `128/127`. -/
theorem lowerSixWeightTail_le_squareRootBlock
    {k : Nat} (hk : 247 ≤ k) (M : Nat) :
    finSum
        (fun j => lowerSixModeWeight k (thetaWindowLeft k + j + 1)) M ≤
      lowerSixBlockClosure * lowerSixGaussianTailBlock k 0 := by
  let c := thetaWindowCenter k
  let K := thetaWindowLeft k + 1
  let f := fun j => lowerSixModeWeight k (K + j)
  have hcpos : 0 < c := by
    dsimp only [c]
    exact ChebOrthoMidpointEst.isqrt_pos (by
      unfold thetaWindowLength
      omega)
  have hM : M ≤ (M + 1) * c := by
    have hmul : M * 1 ≤ M * c :=
      Nat.mul_le_mul_left M (show 1 ≤ c by omega)
    have hsucc : M * c ≤ (M + 1) * c :=
      Nat.mul_le_mul_right c (Nat.le_succ M)
    exact Nat.le_trans (by simpa using hmul) hsucc
  have hf0 : ∀ j, (0 : Q') ≤ f j := by
    intro j
    dsimp only [f]
    unfold lowerSixModeWeight
    exact qpow_nonneg _
      (Q'.mul_nonneg _ _ (harmW_nonneg k) (harmW_nonneg k)) _
  have hpad := RationalTail.finSum_monotone_of_nonneg f hf0
    M ((M + 1) * c) hM
  have hblocks : finSum f ((M + 1) * c) ≈
      finSum (lowerSixGaussianTailBlock k) (M + 1) := by
    refine Q'.eqv_trans _ _ _ (finSum_block f c (M + 1)) ?_
    apply RationalTail.finSum_eqv_congr
    intro i
    unfold lowerSixGaussianTailBlock
    dsimp only [f, c, K]
    apply RationalTail.finSum_eqv_congr
    intro s
    have hidx : thetaWindowLeft k + 1 +
        (i * thetaWindowCenter k + s) =
        thetaWindowLeft k + 1 + i * thetaWindowCenter k + s := by omega
    rw [hidx]
    exact Q'.eqv_refl _
  have hgeom := lowerSixGaussianTailBlocks_le_closure hk (M + 1)
  have hstart : finSum
      (fun j => lowerSixModeWeight k (thetaWindowLeft k + j + 1)) M ≈
      finSum f M := by
    apply RationalTail.finSum_eqv_congr
    intro j
    dsimp only [f, K]
    rw [show thetaWindowLeft k + j + 1 =
      thetaWindowLeft k + 1 + j by omega]
    exact Q'.eqv_refl _
  dsimp only [f, K, c] at hpad hblocks hgeom ⊢
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hstart)
    (Q'.le_trans' _ _ _ hpad
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hblocks) hgeom))

#print axioms lowerSixModeWeight_center_step_le_rate
#print axioms lowerSixGaussianTailBlock_nonnegative
#print axioms lowerSixGaussianTailBlock_step_rate
#print axioms lowerSixGaussianTailBlocks_le_closure
#print axioms lowerSixWeightTail_le_squareRootBlock

end YMGap.Continuum.HarmonicLowerSixSquareRootBlockTail
