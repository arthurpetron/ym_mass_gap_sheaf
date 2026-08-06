/-
Track 11.7-fusion / R3a -- a block-compatible physical cutoff schedule.

The quadratic schedule is too slow for a square block step.  This replacement
couples the two physical scales:

    N_0 = 4,          N_(k+1) = 2*N_k + 1,
    u_0 = 1/12,       u_(k+1) = u_k/4,
    w_k = 1-u_k.

Thus the cutoff tracks the inverse heat length and the exact endpoint rate at
the fine cutoff has enough room to be squared.  This module contains only the
cheap all-scale schedule kernel.  The first physical cells are checked in the
companion `P2BlockCompatibleScheduleCells`, so changes to the structural proof
do not repeatedly invoke the larger integral certificates.  The all-scale
weighted comparison is kept as the next honest theorem rather than assumed.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2DyadicQuadraticCutoffFence

namespace YMGap.Continuum.P2BlockCompatibleSchedule

set_option maxRecDepth 30000
set_option exponentiation.threshold 10000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.EndpointCutoffTailClose
open YMGap.Continuum.FusionMarginMono
open YMGap.Continuum.FusionRDFactor
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.P2VacNormIntegralCertificate
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.VacNormEigShift
open YMGap.Continuum.BondMovingRetuneFix

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast, Int.mul_one];
             ac_rfl))

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-- The quarter heat-time ratio forced by a square block step. -/
def blockQuarter : Q' := Q'.mkPos 1 4 (by decide)

/-- Cutoff recurrence compatible with doubling the inverse heat length. -/
def blockNcut : Nat -> Nat
  | 0 => 4
  | k + 1 => 2 * blockNcut k + 1

/-- Geometric heat-time margin `u_k=(1/12)4^-k`. -/
def blockMargin (k : Nat) : Q' := q112 * qpow blockQuarter k

/-- Near-continuum heat weight. -/
def blockWeight (k : Nat) : Q' := (1 : Q') - blockMargin k

theorem blockQuarter_nonneg : (0 : Q') <= blockQuarter := by decide

theorem blockQuarter_le_one : blockQuarter <= (1 : Q') := by decide

theorem blockNcut_succ (k : Nat) :
    blockNcut (k + 1) = 2 * blockNcut k + 1 := rfl

/-- Closed form without truncated subtraction. -/
theorem blockNcut_closed (k : Nat) :
    blockNcut k + 1 = 5 * 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [blockNcut_succ, Nat.pow_succ]
      omega

theorem blockNcut_pos (k : Nat) : 0 < blockNcut k := by
  have h := blockNcut_closed k
  omega

theorem blockMargin_nonneg (k : Nat) : (0 : Q') <= blockMargin k :=
  Q'.mul_nonneg _ _ (by decide)
    (qpow_nonneg blockQuarter blockQuarter_nonneg k)

theorem blockMargin_le_q112 (k : Nat) : blockMargin k <= q112 := by
  have hp : qpow blockQuarter k <= (1 : Q') :=
    qpow_le_one blockQuarter_nonneg blockQuarter_le_one k
  have h := Q'.mul_le_mul_of_nonneg_left _ _ q112 hp
    (by decide : (0 : Q') <= q112)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_one_eqv q112))

theorem blockMargin_le_one (k : Nat) : blockMargin k <= (1 : Q') :=
  Q'.le_trans' _ _ _ (blockMargin_le_q112 k) (by decide)

theorem blockWeight_nonneg (k : Nat) : (0 : Q') <= blockWeight k :=
  Q'.sub_nonneg_of_le (blockMargin_le_one k)

theorem blockWeight_pos (k : Nat) : (0 : Q') < blockWeight k := by
  unfold blockWeight
  exact HKPos.one_sub_pos
    (Q'.lt_of_le_of_lt (blockMargin_le_q112 k)
      (by decide : q112 < (1 : Q')))

theorem blockWeight_le_one (k : Nat) : blockWeight k <= (1 : Q') :=
  BondMovingRetuneFix.oneSub_le_one (blockMargin_nonneg k)

theorem one_sub_blockWeight_eqv_margin (k : Nat) :
    ((1 : Q') - blockWeight k) ≈ blockMargin k := by
  unfold blockWeight
  exact AFRateCalibration.one_sub_one_sub_eqv (blockMargin k)

/-- The margin quarters at every physical square step. -/
theorem blockMargin_succ_eqv (k : Nat) :
    blockMargin (k + 1) ≈ blockMargin k * blockQuarter := by
  unfold blockMargin
  exact Q'.eqv_symm (Q'.mul_assoc_eqv q112 (qpow blockQuarter k) blockQuarter)

private def blockCoarseNum (x : Q') : Q' := Q'.ofNat 2 * x
private def blockCoarseDen (x : Q') : Q' := Q'.ofNat 2 * x + Q'.ofNat 3
private def blockFineNum (x : Q') : Q' :=
  Q'.ofNat 2 * (Q'.ofNat 2 * x + Q'.ofNat 1)
private def blockFineDen (x : Q') : Q' :=
  Q'.ofNat 2 * (Q'.ofNat 2 * x + Q'.ofNat 1) + Q'.ofNat 3

private def endpointBlockGapLHS : RingNormaliser.PolyExpr :=
  let x : RingNormaliser.PolyExpr := .var 0
  let d := .add (.mul (.const 2) x) (.const 3)
  let A := .mul (.const 2) (.add (.mul (.const 2) x) (.const 1))
  .mul (.mul A A) d

private def endpointBlockGapRHS : RingNormaliser.PolyExpr :=
  let x : RingNormaliser.PolyExpr := .var 0
  let a := .mul (.const 2) x
  let A := .mul (.const 2) (.add (.mul (.const 2) x) (.const 1))
  let D := .add A (.const 3)
  .add (.mul a (.mul D D)) (.mul (.const 6) (.add x (.const 2)))

private theorem endpointBlockGap_normal :
    RingNormaliser.normalize endpointBlockGapLHS =
      RingNormaliser.normalize endpointBlockGapRHS := by
  decide

/-- Reflectively certified polynomial identity behind the block-compatible
endpoint step.  The fine-square cross product exceeds the coarse one by the
explicit nonnegative slack `6*(x+2)`. -/
private theorem endpointBlockGap_eqv (x : Q') :
    (blockFineNum x * blockFineNum x) * blockCoarseDen x ≈
      blockCoarseNum x * (blockFineDen x * blockFineDen x) +
        Q'.ofNat 6 * (x + Q'.ofNat 2) := by
  have h := RingNormaliser.poly_identity_of_normal_eq
    endpointBlockGapLHS endpointBlockGapRHS endpointBlockGap_normal
    (fun _ => x)
  simpa [endpointBlockGapLHS, endpointBlockGapRHS, blockCoarseNum,
    blockCoarseDen, blockFineNum, blockFineDen, RingNormaliser.eval] using h

private theorem endpointBlock_cross_le (x : Q') (hx : (0 : Q') <= x) :
    blockCoarseNum x * (blockFineDen x * blockFineDen x) <=
      (blockFineNum x * blockFineNum x) * blockCoarseDen x := by
  have hx2 : (0 : Q') <= x + Q'.ofNat 2 :=
    Q'.zero_le_add _ _ hx (by decide)
  have hslack : (0 : Q') <= Q'.ofNat 6 * (x + Q'.ofNat 2) :=
    Q'.mul_nonneg _ _ (by decide) hx2
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _ hslack)
    (Q'.ge_of_eqv (endpointBlockGap_eqv x))

private theorem ofNat_two_mul_add_eqv (N c : Nat) :
    Q'.ofNat (2 * N + c) ≈ Q'.ofNat 2 * Q'.ofNat N + Q'.ofNat c :=
  Q'.eqv_trans _ _ _
    (Q'.ofNat_add_eqv (2 * N) c)
    (Q'.add_eqv_congr_right _ _ _
      (SU3CharFactor.ofNat_mul_eqv 2 N))

theorem divPos_square_eqv (p q : Q') (hq : (0 : Q') < q) :
    Q'.divPos (p * p) (q * q) (Q'.mul_pos hq hq) ≈
      Q'.divPos p q hq * Q'.divPos p q hq := by
  let r := Q'.divPos p q hq
  have hr : r * q ≈ p := Q'.divPos_mul_eqv p q hq
  have hregroup : (r * r) * (q * q) ≈ (r * q) * (r * q) := by
    ring_qeqv
  have hproduct : (r * q) * (r * q) ≈ p * p :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (r * q) hr)
      (Q'.mul_eqv_congr_left p _ _ hr)
  apply divPos_eqv_of_eqv_mul (Q'.mul_pos hq hq)
  exact Q'.eqv_symm (Q'.eqv_trans _ _ _ hregroup hproduct)

/-- **All-scale endpoint compatibility.**  A cutoff step `N -> 2N+1`
survives the physical square exactly. -/
theorem endpointRate_le_doubleSucc_square (N : Nat) :
    endpointRate N <=
      endpointRate (2 * N + 1) * endpointRate (2 * N + 1) := by
  let M := 2 * N + 1
  let a := Q'.ofNat (2 * N)
  let d := Q'.ofNat (2 * N + 3)
  let A := Q'.ofNat (2 * M)
  let D := Q'.ofNat (2 * M + 3)
  let x := Q'.ofNat N
  have hcross : a * (D * D) <= (A * A) * d := by
    have hM : Q'.ofNat M ≈ Q'.ofNat 2 * x + Q'.ofNat 1 := by
      unfold M x
      exact ofNat_two_mul_add_eqv N 1
    have ha : a ≈ blockCoarseNum x := by
      unfold a blockCoarseNum x
      exact SU3CharFactor.ofNat_mul_eqv 2 N
    have hd : d ≈ blockCoarseDen x := by
      unfold d blockCoarseDen x
      exact ofNat_two_mul_add_eqv N 3
    have hA : A ≈ blockFineNum x := by
      unfold A blockFineNum
      exact Q'.eqv_trans _ _ _
        (SU3CharFactor.ofNat_mul_eqv 2 M)
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hM)
    have hD : D ≈ blockFineDen x := by
      unfold D blockFineDen
      exact Q'.eqv_trans _ _ _
        (ofNat_two_mul_add_eqv M 3)
        (Q'.add_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hM))
    have hleft : a * (D * D) ≈
        blockCoarseNum x * (blockFineDen x * blockFineDen x) :=
      mul_eqv_both ha (mul_eqv_both hD hD)
    have hright : (A * A) * d ≈
        (blockFineNum x * blockFineNum x) * blockCoarseDen x :=
      mul_eqv_both (mul_eqv_both hA hA) hd
    have hcore := endpointBlock_cross_le x (SU3CharFactor.ofNat_nonneg N)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hcore (Q'.ge_of_eqv hright))
  have hquot := divPos_le_divPos_of_cross a d (A * A) (D * D)
    (endpointDen_pos N) (Q'.mul_pos (endpointDen_pos M) (endpointDen_pos M))
    hcross
  have hsquare := divPos_square_eqv A D (endpointDen_pos M)
  exact Q'.le_trans' _ _ _ hquot (Q'.le_of_eqv hsquare)

/-- Exact cross-multiplied reserve behind the endpoint square.  In ordinary
fraction notation this is

`(4N+2)^2(2N+3) = 2N(4N+5)^2 + 6(N+2)`.

The identity is reflected from the constant-size polynomial normal form; it
does not evaluate a growing cutoff expression. -/
theorem endpointBlockCrossGap_eqv (N : Nat) :
    let M := 2 * N + 1
    let a := Q'.ofNat (2 * N)
    let d := Q'.ofNat (2 * N + 3)
    let A := Q'.ofNat (2 * M)
    let D := Q'.ofNat (2 * M + 3)
    (A * A) * d ≈
      a * (D * D) + Q'.ofNat 6 * (Q'.ofNat N + Q'.ofNat 2) := by
  dsimp only
  let M := 2 * N + 1
  let x := Q'.ofNat N
  have hM : Q'.ofNat M ≈ Q'.ofNat 2 * x + Q'.ofNat 1 := by
    unfold M x
    exact ofNat_two_mul_add_eqv N 1
  have ha : Q'.ofNat (2 * N) ≈ blockCoarseNum x := by
    unfold blockCoarseNum x
    exact SU3CharFactor.ofNat_mul_eqv 2 N
  have hd : Q'.ofNat (2 * N + 3) ≈ blockCoarseDen x := by
    unfold blockCoarseDen x
    exact ofNat_two_mul_add_eqv N 3
  have hA : Q'.ofNat (2 * M) ≈ blockFineNum x := by
    unfold blockFineNum
    exact Q'.eqv_trans _ _ _
      (SU3CharFactor.ofNat_mul_eqv 2 M)
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hM)
  have hD : Q'.ofNat (2 * M + 3) ≈ blockFineDen x := by
    unfold blockFineDen
    exact Q'.eqv_trans _ _ _
      (ofNat_two_mul_add_eqv M 3)
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hM))
  have hleft :
      (Q'.ofNat (2 * M) * Q'.ofNat (2 * M)) *
          Q'.ofNat (2 * N + 3) ≈
        (blockFineNum x * blockFineNum x) * blockCoarseDen x :=
    mul_eqv_both (mul_eqv_both hA hA) hd
  have hright :
      Q'.ofNat (2 * N) *
            (Q'.ofNat (2 * M + 3) * Q'.ofNat (2 * M + 3)) +
          Q'.ofNat 6 * (Q'.ofNat N + Q'.ofNat 2) ≈
        blockCoarseNum x *
            (blockFineDen x * blockFineDen x) +
          Q'.ofNat 6 * (x + Q'.ofNat 2) :=
    Q'.add_eqv_congr'
      (mul_eqv_both ha (mul_eqv_both hD hD))
      (Q'.mul_eqv_congr_left (Q'.ofNat 6) _ _ (Q'.eqv_refl _))
  exact Q'.eqv_trans _ _ _ hleft
    (Q'.eqv_trans _ _ _ (endpointBlockGap_eqv x) (Q'.eqv_symm hright))

theorem endpointRate_block_step (k : Nat) :
    endpointRate (blockNcut k) <=
      endpointRate (blockNcut (k + 1)) * endpointRate (blockNcut (k + 1)) := by
  rw [blockNcut_succ]
  exact endpointRate_le_doubleSucc_square (blockNcut k)

end YMGap.Continuum.P2BlockCompatibleSchedule

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2BlockCompatibleSchedule.blockNcut_closed
#print axioms YMGap.Continuum.P2BlockCompatibleSchedule.blockWeight_pos
#print axioms YMGap.Continuum.P2BlockCompatibleSchedule.endpointRate_le_doubleSucc_square
#print axioms YMGap.Continuum.P2BlockCompatibleSchedule.endpointRate_block_step
#print axioms YMGap.Continuum.P2BlockCompatibleSchedule.endpointBlockCrossGap_eqv
