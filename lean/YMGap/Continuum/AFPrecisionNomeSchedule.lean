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

private theorem half_pow_num : ∀ n : Nat, (HalfPow.half^n).num = 1
  | 0 => rfl
  | n+1 => by
      show HalfPow.half.num * (HalfPow.half^n).num = 1
      rw [half_pow_num n]; rfl

private theorem half_pow_den : ∀ n : Nat, ((HalfPow.half^n).den : Int) = (2^n : Nat)
  | 0 => rfl
  | n+1 => by
      show ((HalfPow.half * HalfPow.half^n).den : Int) = (2^(n+1) : Nat)
      rw [Q'.mul_den_cast, half_pow_den n, Nat.pow_succ]
      have : (HalfPow.half.den : Int) = 2 := rfl
      rw [this]; omega

/-- The actual logarithmic precision pays an inverse-scale error, including j=0. -/
theorem geometric_precision_lt_invSucc (j : Nat) :
    110 * HalfPow.half ^ precisionIndex j <
      Q'.mkPos 55 256 (by decide) * Q'.invSucc j := by
  have hlog := Nat.lt_log2_self (n := j+1)
  rw [Nat.pow_succ] at hlog
  have hlogInt := Int.ofNat_lt.mpr hlog
  rw [Int.natCast_mul] at hlogInt
  show (110 * HalfPow.half ^ precisionIndex j).num *
      ((Q'.mkPos 55 256 (by decide) * Q'.invSucc j).den : Int) <
    (Q'.mkPos 55 256 (by decide) * Q'.invSucc j).num *
      ((110 * HalfPow.half ^ precisionIndex j).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, half_pow_num, half_pow_den,
    Q'.invSucc_num, Q'.invSucc_den]
  change 110 * (256 * ((j+1 : Nat) : Int)) < 55 * (1 * ((2 ^ precisionIndex j : Nat) : Int))
  unfold precisionIndex
  rw [Nat.pow_add, Int.natCast_mul]
  change 110 * (256 * ((j+1 : Nat) : Int)) <
    55 * (1 * (1024 * ((2 ^ Nat.log2 (j+1) : Nat) : Int)))
  omega

theorem interval_width_lt_invSucc (j : Nat) :
    upper (precisionIndex j) - lower (precisionIndex j) <
      Q'.mkPos 55 256 (by decide) * Q'.invSucc j :=
  Q'.lt_of_le_of_lt (AFLeadingCoefficient.enclosure_width_le (precisionIndex j))
    (geometric_precision_lt_invSucc j)

theorem coefficientUpper_width_lt_invSucc (j : Nat) :
    coefficientUpper j - lower (precisionIndex j) <
      Q'.mkPos 55 256 (by decide) * Q'.invSucc j :=
  Q'.lt_of_le_of_lt (Q'.sub_le_of_le_add (coefficientUpper_precision_bound j))
    (geometric_precision_lt_invSucc j)

/-- The SAME existing denominator grows at most four times the scale index. -/
theorem denominator_le_four_succ (j : Nat) :
    denominator j ≤ 4 * Q'.ofNat (j+1) := by
  have hlog : Nat.log2 (j+1) ≤ j := by
    have h := (Nat.log2_lt (n := j+1) (k := j+1) (by omega)).mpr Nat.lt_two_pow_self
    omega
  change (afE j : Int) * 1 ≤ (4 * ((j+1 : Nat) : Int)) * 121
  unfold afE
  simp only [Int.natCast_add, Int.natCast_mul]
  have hlogInt := Int.ofNat_le.mpr hlog
  omega

/-- The SAME clock also dominates the unrounded linear index. -/
theorem denominator_ge_index_add_four (j : Nat) :
    Q'.ofNat (j+4) ≤ denominator j := by
  change ((j+4 : Nat) : Int) * 121 ≤ (afE j : Int) * 1
  unfold afE
  simp only [Int.natCast_add, Int.natCast_mul, Int.mul_one]
  omega

/-- The numerical inverse-index payment does not vanish after index rescaling.
This is only a rational schedule bound, not an interacting response estimate. -/
theorem quarter_lt_gap_mul_succ (j : Nat) :
    Q'.mkPos 1 4 (by decide) < gap j * Q'.ofNat (j+1) := by
  have hU : (1 : Q') < coefficientUpper j :=
    ClusteringImpliesGap.lt_of_lt_of_le AFLeadingCoefficient.one_lt_lower_one
      (coefficientUpper_floor j)
  change (1 : Int) * (coefficientUpper j).den < (coefficientUpper j).num * 1 at hU
  simp only [Int.one_mul, Int.mul_one] at hU
  have hD := denominator_le_four_succ j
  change (afE j : Int) * 1 ≤ (4 * ((j+1 : Nat) : Int)) * 121 at hD
  simp only [Int.mul_one] at hD
  have hden : (0 : Int) ≤ (coefficientUpper j).den :=
    Int.ofNat_le.mpr (Nat.zero_le _)
  have hbound : (coefficientUpper j).den * (afE j : Int) <
      ((coefficientUpper j).num * 121) * ((j+1 : Nat) : Int) * 4 := by
    calc
      (coefficientUpper j).den * (afE j : Int) ≤
          (coefficientUpper j).den * ((4 * ((j+1 : Nat) : Int)) * 121) :=
        Int.mul_le_mul_of_nonneg_left hD hden
      _ < (coefficientUpper j).num * ((4 * ((j+1 : Nat) : Int)) * 121) :=
        Int.mul_lt_mul_of_pos_right hU (by omega)
      _ = ((coefficientUpper j).num * 121) * ((j+1 : Nat) : Int) * 4 := by ac_rfl
  change (1 : Int) * ((gap j * Q'.ofNat (j+1)).den : Int) <
    (gap j * Q'.ofNat (j+1)).num * 4
  simp only [gap, Q'.divPos, Q'.mul_den_cast, Q'.mul_num_cast,
    Q'.recipPos_den, Q'.recipPos_num]
  change (1 : Int) * ((coefficientUpper j).den * (afE j : Int) * 1) <
    ((coefficientUpper j).num * 121) * ((j+1 : Nat) : Int) * 4
  simpa only [Int.one_mul, Int.mul_one] using hbound

/-- The SAME rescaled numerical payment remains strictly bounded above. -/
theorem gap_mul_succ_lt_two (j : Nat) :
    gap j * Q'.ofNat (j+1) < (2 : Q') := by
  have hU := coefficientUpper_lt_two j
  change (coefficientUpper j).num * 1 < (2 : Int) * (coefficientUpper j).den at hU
  simp only [Int.mul_one] at hU
  have hD := denominator_ge_index_add_four j
  change ((j+4 : Nat) : Int) * 121 ≤ (afE j : Int) * 1 at hD
  simp only [Int.natCast_add, Int.mul_one] at hD
  have hclock : 121 * ((j+1 : Nat) : Int) ≤ (afE j : Int) := by
    simp only [Int.natCast_add]
    omega
  have hden : (0 : Int) ≤ 2 * (coefficientUpper j).den := by
    have h := Int.ofNat_le.mpr (Nat.zero_le (coefficientUpper j).den)
    omega
  have hbound : ((coefficientUpper j).num * 121) * ((j+1 : Nat) : Int) <
      2 * ((coefficientUpper j).den * (afE j : Int)) := by
    calc
      ((coefficientUpper j).num * 121) * ((j+1 : Nat) : Int) =
          (coefficientUpper j).num * (121 * ((j+1 : Nat) : Int)) := by ac_rfl
      _ < (2 * (coefficientUpper j).den) * (121 * ((j+1 : Nat) : Int)) :=
        Int.mul_lt_mul_of_pos_right hU (by omega)
      _ ≤ (2 * (coefficientUpper j).den) * (afE j : Int) :=
        Int.mul_le_mul_of_nonneg_left hclock hden
      _ = 2 * ((coefficientUpper j).den * (afE j : Int)) := by ac_rfl
  change (gap j * Q'.ofNat (j+1)).num * 1 <
    (2 : Int) * ((gap j * Q'.ofNat (j+1)).den : Int)
  simp only [gap, Q'.divPos, Q'.mul_den_cast, Q'.mul_num_cast,
    Q'.recipPos_den, Q'.recipPos_num]
  change (((coefficientUpper j).num * 121) * ((j+1 : Nat) : Int)) * 1 <
    (2 : Int) * ((coefficientUpper j).den * (afE j : Int) * 1)
  simpa only [Int.mul_one] using hbound

/-- Multiplying the actual enclosure width by its consumer clock keeps a fixed budget. -/
theorem denominator_precision_lt (j : Nat) :
    denominator j * (upper (precisionIndex j) - lower (precisionIndex j)) <
      Q'.mkPos 55 64 (by decide) := by
  have hD := denominator_le_four_succ j
  change (afE j : Int) * 1 ≤ (4 * ((j+1 : Nat) : Int)) * 121 at hD
  have hpay : denominator j * (Q'.mkPos 55 256 (by decide) * Q'.invSucc j) ≤
      Q'.mkPos 55 64 (by decide) := by
    change ((afE j : Int) * (55 * 1)) * 64 ≤ 55 * (121 * (256 * ((j+1 : Nat) : Int)))
    omega
  exact ClusteringImpliesGap.lt_of_lt_of_le
    (Q'.mul_lt_mul_of_pos_left (denominator_positive j) (interval_width_lt_invSucc j)) hpay

/-- Computed numerical compatibility index, using the actual Machin/artanh
lower endpoint and running upper endpoint.  This is only a rounding-error
guard; it supplies no physical spacing, scale-setting law or retention bound. -/
def precisionCompatibilityIndex (j : Nat) : Q' :=
  denominator j * Q'.divPos (lower (precisionIndex j)) (coefficientUpper j)
    (coefficientUpper_positive j) -
      Q'.mkPos 51 121 (by decide) * Q'.ofNat (Nat.log2 (j+1))

private theorem precision_lower_le_running_upper (j : Nat) :
    lower (precisionIndex j) ≤ coefficientUpper j := by
  apply bounded_runningMin_floor
  intro k hk
  exact Q'.le_trans' _ _ _
    (AFLeadingCoefficient.stream_enclosure _ _ (Nat.le_refl (precisionIndex j))).1
    (AFLeadingCoefficient.stream_enclosure k _ hk).2

set_option maxRecDepth 4096 in
private theorem compatibility_defect_pin (j : Nat) :
    (Q'.ofNat (j+4) - precisionCompatibilityIndex j).eqv
      (Q'.divPos (denominator j * (coefficientUpper j - lower (precisionIndex j)))
        (coefficientUpper j) (coefficientUpper_positive j)) := by
  let D := denominator j
  let U := coefficientUpper j
  let L := lower (precisionIndex j)
  let r := Q'.recipPos U (coefficientUpper_positive j)
  let k := Q'.mkPos 51 121 (by decide) * Q'.ofNat (Nat.log2 (j+1))
  have hclockAny (u v : Nat) :
      (Q'.mkPos ((121*u+51*v+484 : Nat) : Int) 121 (by decide)).eqv
        (Q'.ofNat (u+4) + Q'.mkPos 51 121 (by decide) * Q'.ofNat v) := by
    unfold Q'.eqv
    simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast, Q'.mul_den_cast]
    simp only [Q'.mkPos_num, Q'.mkPos_den]
    simp only [Q'.ofNat, Q'.den, Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
    omega
  have hclockAdd : D.eqv (Q'.ofNat (j+4)+k) :=
    hclockAny j (Nat.log2 (j+1))
  have hclock : (Q'.ofNat (j+4)).eqv (D-k) := by
    apply Q'.eqv_symm
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hclockAdd (Q'.eqv_refl (-k))) ?_
    exact RingNormaliser.poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.var 1))) (.var 0)
      (by decide) (fun | 0 => Q'.ofNat (j+4) | _ => k)
  have hD : D.eqv (D*(U*r)) := Q'.eqv_symm (Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left D _ _ (Q'.mul_recipPos_eqv U (coefficientUpper_positive j)))
    (Q'.mul_one_eqv D))
  have htop : (Q'.ofNat (j+4)).eqv (D*(U*r)-k) :=
    Q'.eqv_trans _ _ _ hclock (Q'.add_eqv_congr' hD (Q'.eqv_refl (-k)))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' htop (Q'.eqv_refl (-(precisionCompatibilityIndex j)))) ?_
  change ((D*(U*r)-k)-(D*(L*r)-k)).eqv ((D*(U-L))*r)
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.mul (.var 1) (.var 3))) (.neg (.var 4)))
      (.neg (.add (.mul (.var 0) (.mul (.var 2) (.var 3))) (.neg (.var 4)))))
    (.mul (.mul (.var 0) (.add (.var 1) (.neg (.var 2)))) (.var 3))
    (by decide) (fun | 0 => D | 1 => U | 2 => L | 3 => r | _ => k)

private theorem compatibility_defect_bounds (j : Nat) :
    (0 : Q') ≤ Q'.ofNat (j+4) - precisionCompatibilityIndex j ∧
      Q'.ofNat (j+4) - precisionCompatibilityIndex j < Q'.mkPos 55 64 (by decide) := by
  let e := denominator j * (coefficientUpper j - lower (precisionIndex j))
  have he0 : (0 : Q') ≤ e := Q'.mul_nonneg _ _
    (Q'.le_of_lt (denominator_positive j))
    (Q'.sub_nonneg_of_le (precision_lower_le_running_upper j))
  have he : e < Q'.mkPos 55 64 (by decide) := Q'.lt_of_le_of_lt
    (Q'.mul_le_mul_of_nonneg_left _ _ (denominator j)
      (Q'.add_le_add_right _ _ (-lower (precisionIndex j))
        (Q'.runningMin_le upper (precisionIndex j)))
      (Q'.le_of_lt (denominator_positive j))) (denominator_precision_lt j)
  have hU : (1 : Q') ≤ coefficientUpper j := Q'.le_trans' _ _ _
    (Q'.le_of_lt AFLeadingCoefficient.one_lt_lower_one) (coefficientUpper_floor j)
  have hr : Q'.recipPos (coefficientUpper j) (coefficientUpper_positive j) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (ArtanhMonotone.recipPos_antitone 1 _ (by decide) (coefficientUpper_positive j) hU)
      (by decide)
  have hpin := compatibility_defect_pin j
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.mul_nonneg _ _ he0 (Q'.le_of_lt (Q'.recipPos_pos _ (coefficientUpper_positive j))))
      (Q'.ge_of_eqv hpin)
  · exact Q'.lt_of_le_of_lt (Q'.le_of_eqv hpin)
      (Q'.lt_of_le_of_lt
        (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ e hr he0)
          (Q'.le_of_eqv (Q'.mul_one_eqv e))) he)

/-- The actual computed index never exceeds its unrounded linear target. -/
theorem precisionCompatibilityIndex_le (j : Nat) :
    precisionCompatibilityIndex j ≤ Q'.ofNat (j+4) :=
  Q'.le_of_sub_nonneg (compatibility_defect_bounds j).1

/-- A strict, uniform rounding-error budget, valid also at j=0. -/
theorem precisionCompatibilityIndex_gt (j : Nat) :
    Q'.ofNat (j+4) - Q'.mkPos 55 64 (by decide) < precisionCompatibilityIndex j := by
  have h := (compatibility_defect_bounds j).2
  have hp := ClusteringImpliesGap.sub_pos_of_lt h
  have he : (precisionCompatibilityIndex j -
      (Q'.ofNat (j+4) - Q'.mkPos 55 64 (by decide))).eqv
      (Q'.mkPos 55 64 (by decide) - (Q'.ofNat (j+4) - precisionCompatibilityIndex j)) :=
    RingNormaliser.poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.add (.var 1) (.neg (.var 2)))))
      (.add (.var 2) (.neg (.add (.var 1) (.neg (.var 0)))))
      (by decide) (fun
        | 0 => precisionCompatibilityIndex j
        | 1 => Q'.ofNat (j+4)
        | _ => Q'.mkPos 55 64 (by decide))
  have hn := Q'.num_pos_of_pos (Q'.pos_of_lt_of_le hp (Q'.ge_of_eqv he))
  change (Q'.ofNat (j+4) - Q'.mkPos 55 64 (by decide)).num *
      ((precisionCompatibilityIndex j).den : Int) <
    (precisionCompatibilityIndex j).num *
      ((Q'.ofNat (j+4) - Q'.mkPos 55 64 (by decide)).den : Int)
  change 0 < (precisionCompatibilityIndex j).num *
      ((Q'.ofNat (j+4) - Q'.mkPos 55 64 (by decide)).den : Int) +
    -(Q'.ofNat (j+4) - Q'.mkPos 55 64 (by decide)).num *
      ((precisionCompatibilityIndex j).den : Int) at hn
  rw [Int.neg_mul] at hn
  omega

/-- In particular, the computed numerical index is beyond j+3.  No physical
identification of this index is asserted. -/
theorem precisionCompatibilityIndex_gt_add_three (j : Nat) :
    Q'.ofNat (j+3) < precisionCompatibilityIndex j := by
  apply ClusteringImpliesGap.lt_of_lt_of_le (b := Q'.ofNat (j+4) - Q'.mkPos 55 64 (by decide))
  · change ((j+3 : Nat) : Int) * 64 < (((j+4 : Nat) : Int) * 64 + -55) * 1
    simp only [Int.natCast_add, Int.mul_one]
    omega
  · exact Q'.le_of_lt (precisionCompatibilityIndex_gt j)

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
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.geometric_precision_lt_invSucc
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.interval_width_lt_invSucc
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.coefficientUpper_width_lt_invSucc
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.denominator_le_four_succ
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.denominator_ge_index_add_four
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.quarter_lt_gap_mul_succ
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.gap_mul_succ_lt_two
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.denominator_precision_lt
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.precisionCompatibilityIndex
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.precisionCompatibilityIndex_le
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.precisionCompatibilityIndex_gt
#print axioms YMGap.Continuum.AFPrecisionNomeSchedule.precisionCompatibilityIndex_gt_add_three
