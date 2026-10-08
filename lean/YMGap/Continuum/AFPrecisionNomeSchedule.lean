/-
An improving-precision rational nome schedule from the ACTUAL Machin/artanh
coefficient. The running minimum folds precision indices, not trajectory
indices. This is a numerical two-loop seed, not a physical spacing function,
nonperturbative calibration, retention estimate or continuum construction.
The existing rounded AF schedule is unchanged.
-/

import YMGap.Continuum.AFLeadingCoefficient
import YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
import YMGap.Continuum.UniformSymbolEncoding

namespace YMGap.Continuum.AFPrecisionNomeSchedule

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFLeadingCoefficient (stream lower upper value)
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory (afE)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory (NomeSchedule)
open YMGap.Continuum.UniformSymbolEncoding (runningMin_le_at)

/-- Only logarithmically many precision stages are folded at scale j. -/
def precisionIndex (j : Nat) : Nat := 10 + Nat.log2 (j+1)

/-- Actual rational upper bounds folded over PRECISION indices 0,...,n_j. -/
def coefficientUpper (j : Nat) : Q' := Q'.runningMin upper (precisionIndex j)

private theorem lower_one_le_upper (k : Nat) : lower 1 ≤ upper k :=
  Q'.le_trans' _ _ _
    (AFLeadingCoefficient.stream_enclosure 1 (max 1 k) (Nat.le_max_left _ _)).1
    (AFLeadingCoefficient.stream_enclosure k (max 1 k) (Nat.le_max_right _ _)).2

theorem coefficientUpper_floor (j : Nat) : lower 1 ≤ coefficientUpper j :=
  Q'.le_runningMin_of_le lower_one_le_upper (precisionIndex j)

theorem coefficientUpper_positive (j : Nat) : (0 : Q') < coefficientUpper j :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.le_of_lt AFLeadingCoefficient.one_lt_lower_one)
      (coefficientUpper_floor j))

theorem coefficientUpper_lt_two (j : Nat) : coefficientUpper j < (2 : Q') :=
  Q'.lt_of_le_of_lt
    (runningMin_le_at upper (precisionIndex j) 1 (by unfold precisionIndex; omega))
    AFLeadingCoefficient.upper_one_lt_two

private theorem log2_succ_mono (j : Nat) : Nat.log2 (j+1) ≤ Nat.log2 (j+1+1) := by
  rw [Nat.le_log2 (by omega)]
  exact Nat.le_trans (Nat.log2_self_le (by omega)) (by omega)

theorem precisionIndex_mono (j : Nat) : precisionIndex j ≤ precisionIndex (j+1) := by
  unfold precisionIndex
  exact Nat.add_le_add_left (log2_succ_mono j) 10

private theorem runningMin_antitone (f : Nat → Q') {n m : Nat} (hnm : n ≤ m) :
    Q'.runningMin f m ≤ Q'.runningMin f n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  clear hnm
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih =>
    exact Q'.le_trans' _ _ _ (Q'.runningMin_succ_le f (n+d)) ih

theorem coefficientUpper_antitone (j : Nat) : coefficientUpper (j+1) ≤ coefficientUpper j :=
  runningMin_antitone upper (precisionIndex_mono j)

/-- Exactly the existing clock D_j=afE_j/121, with no rounded leading coefficient. -/
def denominator (j : Nat) : Q' := Q'.mkPos (afE j) 121 (by decide)

theorem denominator_ge_four (j : Nat) : (4 : Q') ≤ denominator j := by
  change (4 : Int)*121 ≤ (afE j : Int)*1
  simp only [Int.mul_one]
  unfold afE
  omega

theorem denominator_positive (j : Nat) : (0 : Q') < denominator j :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 4) (denominator_ge_four j)

theorem denominator_mono (j : Nat) : denominator j ≤ denominator (j+1) := by
  change (afE j : Int)*121 ≤ (afE (j+1) : Int)*121
  have hn : afE j ≤ afE (j+1) := by
    unfold afE
    have h := log2_succ_mono j
    omega
  exact Int.mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hn) (by decide)

/-- Actual varying rational coefficient divided by the unchanged logarithmic clock. -/
def gap (j : Nat) : Q' := Q'.divPos (coefficientUpper j) (denominator j) (denominator_positive j)

theorem gap_positive (j : Nat) : (0 : Q') < gap j :=
  Q'.divPos_pos _ _ (denominator_positive j) (coefficientUpper_positive j)

theorem gap_le_half (j : Nat) : gap j ≤ HalfPow.half := by
  apply Q'.divPos_le_of_le_mul _ _ (denominator_positive j)
  have h : (2 : Q') ≤ HalfPow.half * denominator j :=
    Q'.le_trans' _ _ _ (by decide : (2 : Q') ≤ HalfPow.half * 4)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (denominator_ge_four j) HalfPow.half_nonneg)
  exact Q'.le_trans' _ _ _ (Q'.le_of_lt (coefficientUpper_lt_two j)) h

theorem gap_lt_one (j : Nat) : gap j < (1 : Q') :=
  Q'.lt_of_le_of_lt (gap_le_half j) (by decide : HalfPow.half < (1 : Q'))

theorem gap_antitone (j : Nat) : gap (j+1) ≤ gap j := by
  have hrec := ArtanhMonotone.recipPos_antitone
    (denominator j) (denominator (j+1)) (denominator_positive j)
    (denominator_positive (j+1)) (denominator_mono j)
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ (coefficientUpper_antitone j)
      (Q'.le_of_lt (Q'.recipPos_pos _ (denominator_positive (j+1)))))
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hrec (Q'.le_of_lt (coefficientUpper_positive j)))

/-- Explicit limit modulus, separate from the coefficient's approximation modulus. -/
def limitModulus (epsilon : Q') : Nat := 2 * epsilon.den

theorem gap_le_of_modulus (epsilon : Q') (he : (0 : Q') < epsilon)
    (j : Nat) (hj : limitModulus epsilon ≤ j) : gap j ≤ epsilon := by
  apply Q'.divPos_le_of_le_mul _ _ (denominator_positive j)
  have heNum := Q'.num_pos_of_pos he
  have hclock : 242 * epsilon.den ≤ afE j := by
    unfold limitModulus at hj
    unfold afE
    omega
  have hclockInt : (242 : Int)*(epsilon.den : Int) ≤ (afE j : Int) := by
    have h := Int.ofNat_le.mpr hclock
    simpa only [Int.natCast_mul] using h
  have hnum : (afE j : Int) ≤ epsilon.num * (afE j : Int) := by
    have h := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ epsilon.num by omega)
      (Int.natCast_nonneg (afE j))
    simpa only [Int.one_mul] using h
  have hpay : (2 : Q') ≤ epsilon * denominator j := by
    change (2 : Int)*((epsilon.den*121 : Nat) : Int) ≤ (epsilon.num*(afE j : Int))*1
    rw [Int.natCast_mul, Int.mul_one]
    omega
  exact Q'.le_trans' _ _ _ (Q'.le_of_lt (coefficientUpper_lt_two j)) hpay

private theorem one_sub_lt_one (g : Q') (hg : (0 : Q') < g) :
    (1 : Q') - g < (1 : Q') := by
  have hn := Q'.num_pos_of_pos hg
  change (1 + -g).num * ((1 : Q').den : Int) < (1 : Q').num * ((1 + -g).den : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den]
  change (1 * (g.den : Int) + -g.num * 1)*1 < 1*(1*(g.den : Int))
  simp only [Int.one_mul, Int.mul_one]
  omega

/-- Actual increasing rational nome schedule with explicit limit data.
It neither asserts physical spacing nor changes the old rounded AF schedule. -/
def precisionNomeSchedule : NomeSchedule where
  nome := fun j => (1 : Q') - gap j
  nome_pos := fun j => HKPos.one_sub_pos (gap_lt_one j)
  nome_lt_one := fun j => one_sub_lt_one _ (gap_positive j)
  nome_mono := fun j => Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (gap_antitone j))
  limitModulus := limitModulus
  nome_limit := fun epsilon he j hj =>
    Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg (gap_le_of_modulus epsilon he j hj))

private theorem bounded_runningMin_floor (f : Nat → Q') (c : Q') :
    ∀ n, (∀ k, k ≤ n → c ≤ f k) → c ≤ Q'.runningMin f n
  | 0, h => h 0 (Nat.le_refl _)
  | n+1, h => (Q'.le_min'_iff _ _ _).mpr
      ⟨bounded_runningMin_floor f c n (fun k hk => h k (Nat.le_succ_of_le hk)),
        h (n+1) (Nat.le_refl _)⟩

/-- Every folded endpoint is an upper enclosure of the SAME constructed coefficient. -/
theorem value_leRat_coefficientUpper (j : Nat) : CReal.leRat value (coefficientUpper j) := by
  apply CReal.leRat_of_eventually
  refine ⟨precisionIndex j, fun m hm => ?_⟩
  rw [AFLeadingCoefficient.value_approx]
  apply bounded_runningMin_floor
  intro k hk
  exact (AFLeadingCoefficient.stream_enclosure k _
    (Nat.le_trans hk (Nat.le_trans hm (CReal.self_le_QMhat stream AFLeadingCoefficient.streamQCauchy m)))).2

/-- Computed precision bound; no differentiation or limit witness is supplied. -/
theorem coefficientUpper_precision_bound (j : Nat) :
    coefficientUpper j ≤ lower (precisionIndex j) + 110 * HalfPow.half ^ precisionIndex j :=
  Q'.le_trans' _ _ _ (Q'.runningMin_le upper (precisionIndex j))
    (AFLeadingCoefficient.upper_le_lower_add (precisionIndex j))

end YMGap.Continuum.AFPrecisionNomeSchedule

#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.precisionIndex
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.coefficientUpper
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.coefficientUpper_floor
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.coefficientUpper_positive
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.coefficientUpper_lt_two
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.precisionIndex_mono
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.coefficientUpper_antitone
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.denominator
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.denominator_ge_four
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.denominator_positive
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.denominator_mono
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.gap
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.gap_positive
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.gap_le_half
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.gap_lt_one
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.gap_antitone
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.limitModulus
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.gap_le_of_modulus
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.precisionNomeSchedule
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.value_leRat_coefficientUpper
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.coefficientUpper_precision_bound
