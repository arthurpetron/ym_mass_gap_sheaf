/-
# Value-level outer tail at the prescribed AF terminal cutoff

The generic arbitrary-nome cutoff schedule pays its burn-in through stored
`Q'` denominators, so it misses every member of the AF terminal diagonal.
This module bypasses that representation artifact.  At AF stage `j >= 9`,
the literal terminal cutoff `4^j` pays the rational gap by at least `16383`.
Reciprocal Bernoulli therefore gives

  w_j^(4^j) <= 2^(-14).

The Casimir exponent then turns the first omitted degree-thirteen term into a
dyadic bound at precision `4^j + 16`, while the same block estimate supplies
the required successive-term ratio.  Consequently the complete one-face
outer shell above the exact terminal cutoff is bounded by
`2^(-(4^j + 15))`, uniformly in every later cutoff.

This is the one-coordinate input for the finite-Fubini tensor/slab lift.  It
does not yet bound the 96-face corrected-slab increment, compare different
AF nomes, control block remainders, or prove a continuum or mass-gap result.

Constructive contract: exact `Nat` and `Q'` inequalities only; no choice,
`Classical`, `native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalCarrier
import YMGap.Continuum.ReciprocalBernoulliUpper
import YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail
import YMGap.Continuum.PartitionUpperBound
import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy
import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
import YMGap.Continuum.RouteDHigherRepTail
import YMGap.Continuum.TotalMajorantClose

namespace
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalValueTail

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.ClusterCount
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalCarrier
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.PartitionUpperBound
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.RGTransport
open YMGap.Continuum.RouteDHigherRepTail
open YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

local infix:50 " ≈ " => Q'.eqv

private theorem shuffle_three (left middle right : Q') :
    left * (middle * right) ≈
      middle * (right * left) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

private theorem af_one_sub_one_sub_local (gap : Q') :
    (1 : Q') - ((1 : Q') - gap) ≈ gap := by
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.const 1)
      (.neg (.add (.const 1) (.neg (.var 0)))))
    (.var 0) (by decide) (fun _ => gap)

private theorem afE_linear_upper_local (stage : Nat) :
    afE stage ≤ 172 * stage + 484 := by
  have hlog : Nat.log2 (stage + 1) ≤ stage := by
    have h :=
      (Nat.log2_lt (n := stage + 1) (k := stage + 1) (by omega)).mpr
        Nat.lt_two_pow_self
    omega
  unfold afE
  omega

private theorem exponential_gap_budget_from_nine :
    ∀ offset : Nat,
      (16383 * 1000) * (172 * (9 + offset) + 484) ≤
        234982 * 4 ^ (9 + offset)
  | 0 => by decide
  | offset + 1 => by
      have ih := exponential_gap_budget_from_nine offset
      calc
        (16383 * 1000) * (172 * (9 + (offset + 1)) + 484) ≤
            2 * ((16383 * 1000) * (172 * (9 + offset) + 484)) := by
              omega
        _ ≤ 2 * (234982 * 4 ^ (9 + offset)) :=
          Nat.mul_le_mul_left 2 ih
        _ ≤ 4 * (234982 * 4 ^ (9 + offset)) := by omega
        _ = 234982 * 4 ^ (9 + (offset + 1)) := by
          rw [show 9 + (offset + 1) = (9 + offset) + 1 by omega,
            Nat.pow_succ]
          ac_rfl

private theorem af_gap_natural_budget
    {stage : Nat} (hstage : 9 ≤ stage) :
    16383 * (1000 * afE stage) ≤
      234982 * 4 ^ stage := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hstage
  calc
    16383 * (1000 * afE (9 + offset)) =
        (16383 * 1000) * afE (9 + offset) := by ac_rfl
    _ ≤ (16383 * 1000) * (172 * (9 + offset) + 484) :=
      Nat.mul_le_mul_left _ (afE_linear_upper_local (9 + offset))
    _ ≤ 234982 * 4 ^ (9 + offset) :=
      exponential_gap_budget_from_nine offset

/-- At every AF stage from nine onward, the prescribed terminal cutoff pays
at least `16383` units of the actual rational gap `1-w`. -/
theorem afTerminalGapPayment
    {stage : Nat} (hstage : 9 ≤ stage) :
    Q'.ofNat 16383 ≤
      Q'.ofNat (4 ^ stage) * afGap stage := by
  show (16383 : Int) *
      ((Q'.ofNat (4 ^ stage) * afGap stage).den : Int) ≤
    (Q'.ofNat (4 ^ stage) * afGap stage).num * 1
  rw [Q'.mul_den_cast, Q'.mul_num_cast,
    Q'.ofNat_den_cast, Q'.ofNat_num_cast, afGap_den]
  have hnum : (afGap stage).num = 234982 := rfl
  rw [hnum]
  simp only [Int.one_mul, Int.mul_one]
  have hnatural := af_gap_natural_budget hstage
  rw [Nat.mul_comm 234982 (4 ^ stage)] at hnatural
  exact Int.ofNat_le.mpr hnatural

/-- The represented AF nome, rather than its stored denominator, supplies a
uniform fourteen-bit block gain at the literal cutoff `4^stage`. -/
theorem afTerminalNomeBlock_le_dyadFourteen
    {stage : Nat} (hstage : 9 ≤ stage) :
    qpow (afNomeSchedule.nome stage) (4 ^ stage) ≤
      dyad 14 := by
  let gap := afGap stage
  let block := 4 ^ stage
  have hgap0 : (0 : Q') ≤ gap :=
    Q'.le_of_lt (afGap_pos stage)
  have hgap1 : gap ≤ (1 : Q') :=
    Q'.le_of_lt (afGap_lt_one stage)
  have hpayment : Q'.ofNat 16383 ≤
      Q'.ofNat block * gap := by
    dsimp only [block, gap]
    exact afTerminalGapPayment hstage
  have hdenominator : Q'.ofNat 16384 ≤ bernDen gap block := by
    unfold bernDen
    have hadd := Q'.add_le_add_left 1 _ _ hpayment
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (by decide :
        (1 : Q') + Q'.ofNat 16383 ≈ Q'.ofNat 16384))
      hadd
  have hbern := oneSub_pow_mul_bernDen_le hgap0 hgap1 block
  have hpower0 : (0 : Q') ≤ qpow (oneSub gap) block :=
    qpow_nonneg _ (Q'.sub_nonneg_of_le hgap1) block
  have hscaled :
      qpow (oneSub gap) block * Q'.ofNat 16384 ≤
        (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hdenominator hpower0)
      hbern
  have hnormalizes :
      dyad 14 * Q'.ofNat 16384 ≈ (1 : Q') := by
    simpa only [dyad] using
      (half_power_normalizes 14)
  have hmul :
      qpow (oneSub gap) block * Q'.ofNat 16384 ≤
        dyad 14 * Q'.ofNat 16384 :=
    Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hnormalizes)
  have hblock :
      qpow (oneSub gap) block ≤ dyad 14 :=
    BakryEmery.le_of_mul_le_mul_right_pos (by decide) hmul
  simpa only [gap, block, oneSub, afNomeSchedule] using hblock

private theorem degreeThirteen_dyadFourteen_eq_half :
    Q'.ofNat (2 ^ physicalFacePolynomialDegree) * dyad 14 ≈
      HalfPow.half := by
  unfold physicalFacePolynomialDegree dyad
  change Q'.ofNat (2 ^ 13) *
      (HalfPow.half * HalfPow.half ^ 13) ≈ HalfPow.half
  refine Q'.eqv_trans _ _ _
    (shuffle_three
      (Q'.ofNat (2 ^ 13)) HalfPow.half
      (HalfPow.half ^ 13)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left HalfPow.half _ _
      (half_power_normalizes 13)) ?_
  exact Q'.mul_one_eqv HalfPow.half

/-- From stage nine onward, the exact first omitted AF terminal spin satisfies
the degree-thirteen successive-term ratio condition. -/
theorem afTerminalRatioCondition
    {stage : Nat} (hstage : 9 ≤ stage) :
    Q'.ofNat (2 ^ physicalFacePolynomialDegree) *
        qpow (afNomeSchedule.nome stage)
          (2 * (4 ^ stage + 1) + 3) ≤
      HalfPow.half := by
  let w := afNomeSchedule.nome stage
  let block := 4 ^ stage
  have hw0 : (0 : Q') ≤ w :=
    Q'.le_of_lt (afNomeSchedule.nome_pos stage)
  have hw1 : w ≤ (1 : Q') :=
    Q'.le_of_lt (afNomeSchedule.nome_lt_one stage)
  have hpower :
      qpow w (2 * (block + 1) + 3) ≤ dyad 14 :=
    Q'.le_trans' _ _ _
      (qpow_antitone hw0 hw1 block
        (2 * (block + 1) + 3) (by omega))
      (by
        dsimp only [w, block]
        exact afTerminalNomeBlock_le_dyadFourteen hstage)
  have hscaled :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpower
      (zero_le_ofNat (2 ^ physicalFacePolynomialDegree))
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_of_eqv degreeThirteen_dyadFourteen_eq_half)

private theorem ofNat_twoPow_pays_halfPower
    (paid remaining : Nat) :
    Q'.ofNat (2 ^ paid) *
        HalfPow.half ^ (paid + remaining) ≈
      HalfPow.half ^ remaining := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (Q'.ofNat (2 ^ paid)) _ _
      (Q'.pow_add_eqv HalfPow.half
        paid remaining)) ?_
  refine Q'.eqv_trans _ _ _
    (shuffle_three
      (Q'.ofNat (2 ^ paid))
      (HalfPow.half ^ paid)
      (HalfPow.half ^ remaining)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (HalfPow.half ^ paid) _ _
      (Q'.mul_comm_eqv
        (HalfPow.half ^ remaining)
        (Q'.ofNat (2 ^ paid)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (HalfPow.half ^ paid)
        (Q'.ofNat (2 ^ paid))
        (HalfPow.half ^ remaining))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _
      (HalfPow.half ^ remaining)
      (half_power_normalizes paid)) ?_
  exact Q'.one_mul_eqv _

private theorem terminal_head_dyadic_identity (block : Nat) :
    Q'.ofNat ((2 ^ 13) ^ (block + 2)) *
        HalfPow.half ^ (14 * (block + 3)) ≈
      HalfPow.half ^ (block + 16) := by
  have hpower :
      (2 ^ 13) ^ (block + 2) =
        2 ^ (13 * (block + 2)) := by
    rw [Nat.pow_mul]
  have hexponent :
      14 * (block + 3) =
        13 * (block + 2) + (block + 16) := by omega
  rw [hpower, hexponent]
  exact ofNat_twoPow_pays_halfPower
    (13 * (block + 2)) (block + 16)

/-- The first omitted degree-thirteen term above the exact AF terminal cutoff
has a value-level dyadic bound independent of every stored denominator. -/
theorem afTerminalFirstOmittedHead_le
    {stage : Nat} (hstage : 9 ≤ stage) :
    tailTerm (afNomeSchedule.nome stage)
        physicalFacePolynomialDegree (4 ^ stage + 1) ≤
      dyad (4 ^ stage + 16) := by
  let w := afNomeSchedule.nome stage
  let block := 4 ^ stage
  have hw0 : (0 : Q') ≤ w :=
    Q'.le_of_lt (afNomeSchedule.nome_pos stage)
  have hw1 : w ≤ (1 : Q') :=
    Q'.le_of_lt (afNomeSchedule.nome_lt_one stage)
  have hblock : qpow w block ≤ dyad 14 := by
    dsimp only [w, block]
    exact afTerminalNomeBlock_le_dyadFourteen hstage
  have hexponent : block * (block + 3) ≤ c4 (block + 1) := by
    unfold c4
    change block * (block + 3) ≤ (block + 1) * (block + 3)
    exact Nat.mul_le_mul_right (block + 3) (Nat.le_succ block)
  have hcasimir :
      qpow w (c4 (block + 1)) ≤
        HalfPow.half ^ (14 * (block + 3)) := by
    have hreduce :
        qpow w (c4 (block + 1)) ≤
          qpow w (block * (block + 3)) :=
      qpow_antitone hw0 hw1
        (block * (block + 3)) (c4 (block + 1)) hexponent
    have hsplit :
        qpow w (block * (block + 3)) ≈
          (qpow w block) ^ (block + 3) := by
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm (qpow_qpow w block (block + 3)))
        (qpow_eqv_pow (qpow w block) (block + 3))
    have hpow :
        (qpow w block) ^ (block + 3) ≤
          (dyad 14) ^ (block + 3) :=
      TotalMajorantClose.pow_le_pow_base
        (qpow_nonneg w hw0 block) hblock (block + 3)
    have htarget :
        (dyad 14) ^ (block + 3) ≈
          HalfPow.half ^ (14 * (block + 3)) := by
      unfold dyad
      exact TotalMajorantClose.pow_mul
        HalfPow.half 14 (block + 3)
    exact Q'.le_trans' _ _ _ hreduce
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
        (Q'.le_trans' _ _ _ hpow (Q'.le_of_eqv htarget)))
  have hpolyNat :
      (block + 2) ^ 13 ≤
        (2 ^ 13) ^ (block + 2) :=
    nat_pow_le_two_pow_pow 13 (block + 2)
  have hpoly :
      Q'.ofNat ((block + 2) ^ 13) ≤
        Q'.ofNat ((2 ^ 13) ^ (block + 2)) :=
    ClusterCount.ofNat_le_ofNat hpolyNat
  have hcasimir0 :
      (0 : Q') ≤ qpow w (c4 (block + 1)) :=
    qpow_nonneg w hw0 _
  have htarget0 :
      (0 : Q') ≤ HalfPow.half ^ (14 * (block + 3)) :=
    Q'.pow_nonneg _ HalfPow.half_nonneg _
  have hfirst :
      Q'.ofNat ((block + 2) ^ 13) *
          qpow w (c4 (block + 1)) ≤
        Q'.ofNat ((2 ^ 13) ^ (block + 2)) *
          qpow w (c4 (block + 1)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpoly hcasimir0
  have hsecond :
      Q'.ofNat ((2 ^ 13) ^ (block + 2)) *
          qpow w (c4 (block + 1)) ≤
        Q'.ofNat ((2 ^ 13) ^ (block + 2)) *
          HalfPow.half ^ (14 * (block + 3)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hcasimir
      (zero_le_ofNat _)
  unfold tailTerm physicalFacePolynomialDegree dyad
  dsimp only [w, block] at hfirst hsecond ⊢
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _ _ _ hsecond
      (Q'.le_of_eqv
        (terminal_head_dyadic_identity (4 ^ stage))))

/-- Uniform one-face shell bound above the exact AF terminal cutoff.  The
later cutoff is arbitrary and need not be represented in the bound. -/
theorem afTerminalOneFaceOuterShellMass_le
    {depth : Nat} (hdepth : 8 ≤ depth) (later : Nat) :
    su2PhysicalOuterShellMass
        (afTerminalData depth).coupling
        (afTerminalData depth).cutoff later ≤
      dyad ((afTerminalData depth).cutoff + 15) := by
  let stage := depth + 1
  let block := 4 ^ stage
  have hstage : 9 ≤ stage := by
    dsimp only [stage]
    omega
  rw [afTerminalData_coupling, afTerminalData_cutoff]
  exact su2PhysicalOuterShellMass_le_dyad
    (afNomeSchedule.nome_pos stage)
    (afNomeSchedule.nome_lt_one stage)
    (block + 15)
    (M := block) (K := later)
    (afTerminalRatioCondition hstage)
    (by
      simpa only [Nat.add_assoc] using
        (afTerminalFirstOmittedHead_le hstage))

/-! ## Axiom audit -/

#print axioms afTerminalGapPayment
#print axioms afTerminalNomeBlock_le_dyadFourteen
#print axioms afTerminalRatioCondition
#print axioms afTerminalFirstOmittedHead_le
#print axioms afTerminalOneFaceOuterShellMass_le

end
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTerminalValueTail
