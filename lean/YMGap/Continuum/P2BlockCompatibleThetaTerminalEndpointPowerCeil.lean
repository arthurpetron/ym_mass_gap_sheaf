/-
Track 11.7-fusion / R3q -- uniform terminal endpoint-power ceiling.

# Result

At every open-tail scale `k >= 7`, put `H = 2^(k-7)`.  The fine heat
margin and terminal endpoint exponent satisfy the exact identities

    u_(k+1) * H^2 = 1 / 786432,
    8 * (640 H)^2 = (100 H^2) * 32768.

Reciprocal Bernoulli therefore bounds each `100 H^2` chunk by the fixed
rational `196608/196633`.  Iterating the chunk bound gives a uniform ceiling
for the physical terminal endpoint power.  The large exponent is never
evaluated by linear recursion: its proof is the `qpow_qpow` multiplication
law plus base monotonicity.

This discharges the scalar all-scale field of
`TerminalEndpointFixedCertificate`.  The fixed 640-entry table comparison
remains separate and is not asserted here.

# Constructivity

Primitive induction, exact rational equivalence, reciprocal Bernoulli, and
proved power laws only.  No `Classical`, `native_decide`, `sorry`, custom
axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointStep

namespace YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointPowerCeil

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointStep
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast, Int.mul_one];
             ac_rfl))

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

private theorem margin_eight_mul_dyadicSquare_eqv : forall d : Nat,
    blockMargin (8 + d) * Q'.ofNat ((2 ^ d) * (2 ^ d)) ≈
      Q'.mkPos 1 786432 (by decide)
  | 0 => by
      unfold blockMargin SpectralLocalizationCrux.q112 blockQuarter
      decide
  | d + 1 => by
      have hm := blockMargin_succ_eqv (8 + d)
      have hsquare :
          (2 ^ (d + 1)) * (2 ^ (d + 1)) =
            4 * ((2 ^ d) * (2 ^ d)) := by
        rw [Nat.pow_succ]
        rw [show 4 = 2 * 2 by decide]
        ac_rfl
      have hnat :
          Q'.ofNat ((2 ^ (d + 1)) * (2 ^ (d + 1))) ≈
            Q'.ofNat 4 * Q'.ofNat ((2 ^ d) * (2 ^ d)) := by
        rw [hsquare]
        exact Q'.eqv_symm
          (HeatKernelRGStep.ofNat_mul_eqv 4 ((2 ^ d) * (2 ^ d)))
      have hquarter : blockQuarter * Q'.ofNat 4 ≈ (1 : Q') := by
        unfold blockQuarter
        decide
      refine Q'.eqv_trans _
        ((blockMargin (8 + d) * Q'.ofNat ((2 ^ d) * (2 ^ d))) *
          (blockQuarter * Q'.ofNat 4)) _ ?_ ?_
      · refine Q'.eqv_trans _
          ((blockMargin (8 + d) * blockQuarter) *
            (Q'.ofNat 4 * Q'.ofNat ((2 ^ d) * (2 ^ d)))) _ ?_ ?_
        · exact mul_eqv_both hm hnat
        · ring_qeqv
      · refine Q'.eqv_trans _
          (Q'.mkPos 1 786432 (by decide) * (1 : Q')) _
          (mul_eqv_both (margin_eight_mul_dyadicSquare_eqv d) hquarter) ?_
        exact Q'.mul_one_eqv _

/-- Exact scale-free fine margin at the 640-block terminal scale. -/
theorem fineMargin_mul_dyadicSquare_eqv
    {k : Nat} (hk : 7 <= k) :
    blockMargin (k + 1) *
        Q'.ofNat ((2 ^ (k - 7)) * (2 ^ (k - 7))) ≈
      Q'.mkPos 1 786432 (by decide) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hidx : 7 + d + 1 = 8 + d := by omega
  rw [hidx]
  simpa only [Nat.add_sub_cancel_left] using
    margin_eight_mul_dyadicSquare_eqv d

/-- One reciprocal-Bernoulli chunk ceiling. -/
def endpointPowerChunkCeil : Q' :=
  Q'.mkPos 196608 196633 (by decide)

/-- The uniform all-scale terminal endpoint-power ceiling. -/
def terminalEndpointPowerCeil : Q' :=
  qpow endpointPowerChunkCeil 32768

theorem endpointPowerChunkCeil_nonneg :
    (0 : Q') <= endpointPowerChunkCeil := by
  unfold endpointPowerChunkCeil
  decide

theorem terminalEndpointPowerCeil_nonneg :
    (0 : Q') <= terminalEndpointPowerCeil := by
  unfold terminalEndpointPowerCeil
  exact qpow_nonneg _ endpointPowerChunkCeil_nonneg 32768

private theorem chunkExponent_margin_eqv
    {k : Nat} (hk : 7 <= k) :
    Q'.ofNat (100 *
        ((2 ^ (k - 7)) * (2 ^ (k - 7)))) * blockMargin (k + 1) ≈
      Q'.mkPos 25 196608 (by decide) := by
  let H2 := (2 ^ (k - 7)) * (2 ^ (k - 7))
  have hmargin := fineMargin_mul_dyadicSquare_eqv hk
  have hmargin' :
      blockMargin (k + 1) * Q'.ofNat H2 ≈
        Q'.mkPos 1 786432 (by decide) := by
    simpa only [H2] using hmargin
  have hnat : Q'.ofNat (100 * H2) ≈ Q'.ofNat 100 * Q'.ofNat H2 :=
    Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 100 H2)
  refine Q'.eqv_trans _
    (Q'.ofNat 100 *
      (blockMargin (k + 1) * Q'.ofNat H2)) _ ?_ ?_
  · refine Q'.eqv_trans _
      ((Q'.ofNat 100 * Q'.ofNat H2) * blockMargin (k + 1)) _
      (Q'.mul_eqv_congr_right _ _ _ hnat) ?_
    ring_qeqv
  · refine Q'.eqv_trans _
      (Q'.ofNat 100 * Q'.mkPos 1 786432 (by decide)) _
      (Q'.mul_eqv_congr_left _ _ _ hmargin') ?_
    decide

private theorem chunkBernDen_eqv
    {k : Nat} (hk : 7 <= k) :
    bernDen (blockMargin (k + 1))
        (100 * ((2 ^ (k - 7)) * (2 ^ (k - 7)))) ≈
      Q'.mkPos 196633 196608 (by decide) := by
  unfold bernDen
  refine Q'.eqv_trans _
    ((1 : Q') + Q'.mkPos 25 196608 (by decide)) _
    (Q'.add_eqv_congr_left 1 _ _ (chunkExponent_margin_eqv hk)) ?_
  decide

/-- One `100 H^2` block of the physical endpoint power is uniformly bounded
by `196608/196633`. -/
theorem physicalEndpointChunk_le
    {k : Nat} (hk : 7 <= k) :
    qpow (blockWeight (k + 1))
        (100 * ((2 ^ (k - 7)) * (2 ^ (k - 7)))) <=
      endpointPowerChunkCeil := by
  let u := blockMargin (k + 1)
  let n := 100 * ((2 ^ (k - 7)) * (2 ^ (k - 7)))
  let D := Q'.mkPos 196633 196608 (by decide)
  have hu0 : (0 : Q') <= u := blockMargin_nonneg (k + 1)
  have hu1 : u <= (1 : Q') := blockMargin_le_one (k + 1)
  have hbern := oneSub_pow_mul_bernDen_le hu0 hu1 n
  have hden : bernDen u n ≈ D := by
    simpa only [u, n, D] using chunkBernDen_eqv hk
  have hprod : qpow (blockWeight (k + 1)) n * D <= (1 : Q') := by
    have hleft : qpow (blockWeight (k + 1)) n * bernDen u n ≈
        qpow (blockWeight (k + 1)) n * D :=
      Q'.mul_eqv_congr_left _ _ _ hden
    have hweight : blockWeight (k + 1) = oneSub u := rfl
    rw [hweight]
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hbern
  have hDpos : (0 : Q') < D := by
    unfold D
    decide
  have hdivLe :
      Q'.divPos (1 : Q') D hDpos <= endpointPowerChunkCeil := by
    apply Q'.divPos_le_of_le_mul
    unfold D endpointPowerChunkCeil
    decide
  refine Q'.le_trans' _ _ _
    (Q'.le_divPos_of_mul_le (1 : Q') D hDpos hprod) ?_
  exact hdivLe

private theorem terminalExponent_split (H : Nat) :
    (100 * (H * H)) * 32768 = 8 * ((640 * H) * (640 * H)) := by
  calc
    (100 * (H * H)) * 32768 = (100 * 32768) * (H * H) := by ac_rfl
    _ = 3276800 * (H * H) := by
      rw [show 100 * 32768 = 3276800 by decide]
    _ = (8 * (640 * 640)) * (H * H) := by
      rw [show 8 * (640 * 640) = 3276800 by decide]
    _ = 8 * ((640 * H) * (640 * H)) := by ac_rfl

/-- The concrete ceiling dominates the terminal endpoint power at every
physical open-tail scale. -/
theorem physicalTerminalEndpointPower_le
    (k : Nat) (hk : 7 <= k) :
    physicalEndpointPower k 639 <= terminalEndpointPowerCeil := by
  let H := 2 ^ (k - 7)
  let n := 100 * (H * H)
  let w := blockWeight (k + 1)
  have hchunk : qpow w n <= endpointPowerChunkCeil := by
    simpa only [H, n, w] using physicalEndpointChunk_le hk
  have hchunk0 : (0 : Q') <= qpow w n :=
    qpow_nonneg _ (blockWeight_nonneg (k + 1)) n
  have hmono := FusedAmplitudeDerivation.qpow_mono_base
    hchunk0 hchunk 32768
  have hiter := HeatKernelRGStep.qpow_qpow w n 32768
  have hexp := terminalExponent_split H
  have hendpoint : physicalEndpointPower k 639 ≈
      qpow (qpow w n) 32768 := by
    unfold physicalEndpointPower
    dsimp only
    refine Q'.eqv_trans _ (qpow w (n * 32768)) _ ?_ ?_
    · rw [hexp]
      exact Q'.eqv_refl _
    · exact Q'.eqv_symm hiter
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hendpoint) hmono

/-! ## A small-integer upper certificate for the fixed table comparison -/

/-- Rounded-up squaring chain for `(196608/196633)^(2^i)`.  The common
decimal denominator is only a certificate-generation choice; every adjacent
square comparison is checked exactly below. -/
def endpointPowerSquareRound : Nat -> Q'
  | 0 => endpointPowerChunkCeil
  | 1 => Q'.mkPos 12496821691839 12500000000000 (by decide)
  | 2 => Q'.mkPos 499745767672377 500000000000000 (by decide)
  | 3 => Q'.mkPos 499491664612907 500000000000000 (by decide)
  | 4 => Q'.mkPos 249491923017773 250000000000000 (by decide)
  | 5 => Q'.mkPos 497969757208851 500000000000000 (by decide)
  | 6 => Q'.mkPos 991895516378569 1000000000000000 (by decide)
  | 7 => Q'.mkPos 983856715411909 1000000000000000 (by decide)
  | 8 => Q'.mkPos 967974036461111 1000000000000000 (by decide)
  | 9 => Q'.mkPos 936973735262817 1000000000000000 (by decide)
  | 10 => Q'.mkPos 219479945143089 250000000000000 (by decide)
  | 11 => Q'.mkPos 385371570560107 500000000000000 (by decide)
  | 12 => Q'.mkPos 118808997916771 200000000000000 (by decide)
  | 13 => Q'.mkPos 352889449649683 1000000000000000 (by decide)
  | 14 => Q'.mkPos 124530963674057 1000000000000000 (by decide)
  | _ => Q'.mkPos 1550796091359 100000000000000 (by decide)

/-- The compact rational used on the left side of the fixed-table check. -/
def terminalEndpointPowerRationalCeil : Q' :=
  Q'.mkPos 1550796091359 100000000000000 (by decide)

private theorem endpointPowerSquareRound_step (i : Nat) (hi : i < 15) :
    qpow (endpointPowerSquareRound i) 2 <=
      endpointPowerSquareRound (i + 1) := by
  have hcases :
      i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
      i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

private theorem powerTwo_le_squareRound : forall i : Nat, i <= 15 ->
    qpow endpointPowerChunkCeil (2 ^ i) <= endpointPowerSquareRound i
  | 0, _ => by
      change qpow endpointPowerChunkCeil 1 <= endpointPowerChunkCeil
      exact Q'.le_of_eqv (Q'.one_mul_eqv endpointPowerChunkCeil)
  | i + 1, hi => by
      have hprev := powerTwo_le_squareRound i (by omega)
      have hleft0 : (0 : Q') <=
          qpow endpointPowerChunkCeil (2 ^ i) :=
        qpow_nonneg _ endpointPowerChunkCeil_nonneg _
      have hmono := FusedAmplitudeDerivation.qpow_mono_base
        hleft0 hprev 2
      have hstep := endpointPowerSquareRound_step i (by omega)
      have hiter := HeatKernelRGStep.qpow_qpow
        endpointPowerChunkCeil (2 ^ i) 2
      have hpow : 2 ^ (i + 1) = (2 ^ i) * 2 := Nat.pow_succ 2 i
      rw [hpow]
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hiter))
        (Q'.le_trans' _ _ _ hmono hstep)

/-- The logarithmic Bernoulli ceiling itself is below a 15-digit rational.
This removes the remaining 32768th power from the fixed-table arithmetic. -/
theorem terminalEndpointPowerCeil_le_rational :
    terminalEndpointPowerCeil <= terminalEndpointPowerRationalCeil := by
  have h := powerTwo_le_squareRound 15 (by omega)
  have hpow : 2 ^ 15 = 32768 := by decide
  rw [hpow] at h
  simpa only [terminalEndpointPowerCeil,
    terminalEndpointPowerRationalCeil, endpointPowerSquareRound] using h

end YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointPowerCeil

#print axioms YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointPowerCeil.fineMargin_mul_dyadicSquare_eqv
#print axioms YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointPowerCeil.physicalEndpointChunk_le
#print axioms YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointPowerCeil.physicalTerminalEndpointPower_le
#print axioms YMGap.Continuum.P2BlockCompatibleThetaTerminalEndpointPowerCeil.terminalEndpointPowerCeil_le_rational
