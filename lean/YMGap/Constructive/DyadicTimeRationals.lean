/-
# Rational values and computed upper dyadic approximations

Mesh values use the project's Q', never Lean's Rat. Natural division
computes an upper mesh point within one dyadic unit of any nonnegative
rational. All bounds and representation pins are exact. This is numerical
time data only; no operator or physical hypothesis is involved.
-/

import YMGap.Constructive.NonnegativeDyadicTime
import YMGap.Constructive.HalfPow

namespace YMGap.Constructive.DyadicTimeRationals

set_option autoImplicit false

open YMGap.Constructive.NonnegativeDyadicTime
open YMGap.Constructive.HalfPow (half)

def value (p : MeshPoint) : Q' := Q'.mkPos p.steps (2^p.depth) (Nat.pow_pos (by decide))

theorem value_num (p : MeshPoint) : (value p).num = p.steps := rfl

theorem value_den (p : MeshPoint) : (value p).den = 2^p.depth := Q'.mkPos_den _ _ _

theorem value_nonnegative (p : MeshPoint) : (0 : Q') ≤ value p :=
  (Q'.zero_le_iff_num_nonneg _).mpr (Int.natCast_nonneg _)

theorem value_le_iff (p q : MeshPoint) :
    value p ≤ value q ↔ p.steps * 2^q.depth ≤ q.steps * 2^p.depth := by
  change (value p).num * ((value q).den : Int) ≤ (value q).num * ((value p).den : Int) ↔ _
  rw [value_num, value_num, value_den, value_den]
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_le

theorem value_eqv_iff (p q : MeshPoint) : Q'.eqv (value p) (value q) ↔ Equivalent p q := by
  change (value p).num * ((value q).den : Int) = (value q).num * ((value p).den : Int) ↔ _
  rw [value_num, value_num, value_den, value_den]
  rw [← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_inj

theorem value_refine (p : MeshPoint) (extra : Nat) : Q'.eqv (value (refine p extra)) (value p) :=
  (value_eqv_iff _ _).mpr (refine_equivalent p extra)

theorem half_power_num (depth : Nat) : (half^depth).num = 1 := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change (1 : Int) * (half^depth).num = 1
      rw [ih, Int.one_mul]

theorem half_power_den (depth : Nat) : ((half^depth).den : Int) = (2^depth : Nat) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      change ((half * half^depth).den : Int) = (2^(depth+1) : Nat)
      rw [Q'.mul_den_cast, ih, Nat.pow_succ, Int.natCast_mul]
      change (2 : Int) * (2^depth : Nat) = (2^depth : Nat) * 2
      exact Int.mul_comm _ _

theorem unit_value (depth : Nat) : Q'.eqv (value ⟨depth,1⟩) (half^depth) := by
  change (value ⟨depth,1⟩).num * ((half^depth).den : Int) = (half^depth).num * ((value ⟨depth,1⟩).den : Int)
  rw [value_num, value_den, half_power_num, half_power_den]
  rfl

/-- Always a positive mesh point. For q>=0 the error is at most one mesh unit. -/
def upper (q : Q') (depth : Nat) : MeshPoint :=
  ⟨depth, (q.num.toNat * 2^depth) / q.den + 1⟩

theorem upper_depth (q : Q') (depth : Nat) : (upper q depth).depth = depth := rfl

theorem upper_steps_positive (q : Q') (depth : Nat) : 0 < (upper q depth).steps := Nat.succ_pos _

theorem rational_le_upper (q : Q') (hq : (0 : Q') ≤ q) (depth : Nat) : q ≤ value (upper q depth) := by
  have hnum : (q.num.toNat : Int) = q.num := Int.toNat_of_nonneg ((Q'.zero_le_iff_num_nonneg q).mp hq)
  have hnat := Nat.le_of_lt (Nat.lt_mul_div_succ (q.num.toNat * 2^depth) (Q'.den_pos q))
  rw [Nat.mul_comm q.den] at hnat
  change q.num * ((value (upper q depth)).den : Int) ≤ (value (upper q depth)).num * (q.den : Int)
  rw [value_den, value_num]
  change q.num * (2^depth : Nat) ≤ (((q.num.toNat * 2^depth) / q.den + 1 : Nat) : Int) * (q.den : Int)
  rw [← hnum]
  exact_mod_cast hnat

theorem upper_le_rational_add_unit (q : Q') (hq : (0 : Q') ≤ q) (depth : Nat) :
    value (upper q depth) ≤ q + value ⟨depth,1⟩ := by
  have hnum : (q.num.toNat : Int) = q.num := Int.toNat_of_nonneg ((Q'.zero_le_iff_num_nonneg q).mp hq)
  have hnat : ((q.num.toNat * 2^depth) / q.den + 1) * q.den ≤ q.num.toNat * 2^depth + q.den := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  have hi : (((q.num.toNat * 2^depth) / q.den + 1 : Nat) : Int) * (q.den : Int) ≤
      q.num * (2^depth : Nat) + (q.den : Int) := by
    rw [← hnum]
    exact_mod_cast hnat
  change (value (upper q depth)).num * ((q + value ⟨depth,1⟩).den : Int) ≤
    (q + value ⟨depth,1⟩).num * ((value (upper q depth)).den : Int)
  rw [Q'.add_den_cast, value_num, value_den, value_den]
  change (((q.num.toNat * 2^depth) / q.den + 1 : Nat) : Int) * ((q.den : Int) * (2^depth : Nat)) ≤
    (q.num * ((value ⟨depth,1⟩).den : Int) + (value ⟨depth,1⟩).num * (q.den : Int)) * (2^depth : Nat)
  rw [value_den, value_num]
  change (((q.num.toNat * 2^depth) / q.den + 1 : Nat) : Int) * ((q.den : Int) * (2^depth : Nat)) ≤
    (q.num * (2^depth : Nat) + 1 * (q.den : Int)) * (2^depth : Nat)
  rw [Int.one_mul, ← Int.mul_assoc]
  exact Int.mul_le_mul_of_nonneg_right hi (Int.natCast_nonneg _)

theorem upper_error (q : Q') (hq : (0 : Q') ≤ q) (depth : Nat) :
    q ≤ value (upper q depth) ∧ value (upper q depth) ≤ q + half^depth :=
  ⟨rational_le_upper q hq depth, Q'.le_trans' _ _ _ (upper_le_rational_add_unit q hq depth)
    (Q'.add_le_add_left _ _ _ (Q'.le_of_eqv (unit_value depth)))⟩

/-- Convert a rational relative error into an exact natural-number step budget. -/
theorem relative_scaled_bound (depth a b k : Nat)
    (h : value ⟨depth,b⟩ ≤ value ⟨depth,a⟩ + value ⟨depth,a⟩ * half^k) :
    b * 2^k ≤ a * 2^k + a := by
  change (value ⟨depth,b⟩).num * ((value ⟨depth,a⟩ + value ⟨depth,a⟩ * half^k).den : Int) ≤
    ((value ⟨depth,a⟩).num * ((value ⟨depth,a⟩ * half^k).den : Int) +
      ((value ⟨depth,a⟩).num * (half^k).num) * ((value ⟨depth,a⟩).den : Int)) *
      ((value ⟨depth,b⟩).den : Int) at h
  rw [Q'.add_den_cast, Q'.mul_den_cast, value_num, value_num, value_den,
    value_den, half_power_num, half_power_den, Int.mul_one] at h
  have hn : b * (2^depth * (2^depth * 2^k)) ≤
      (a * (2^depth * 2^k) + a * 2^depth) * 2^depth := by exact_mod_cast h
  have hc : (b * 2^k) * (2^depth * 2^depth) ≤ (a * 2^k + a) * (2^depth * 2^depth) := by
    simpa only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hn
  exact Nat.le_of_mul_le_mul_right hc (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)))

theorem relative_step_budget (depth a b k : Nat) (hab : a ≤ b)
    (h : value ⟨depth,b⟩ ≤ value ⟨depth,a⟩ + value ⟨depth,a⟩ * half^k) :
    (b-a) * 2^k ≤ a := by
  have hb := relative_scaled_bound depth a b k h
  have he : b * 2^k = (b-a)*2^k + a*2^k := by rw [← Nat.add_mul, Nat.sub_add_cancel hab]
  rw [he] at hb
  omega

end YMGap.Constructive.DyadicTimeRationals

#print axioms YMGap.Constructive.DyadicTimeRationals.value
#print axioms YMGap.Constructive.DyadicTimeRationals.value_num
#print axioms YMGap.Constructive.DyadicTimeRationals.value_den
#print axioms YMGap.Constructive.DyadicTimeRationals.value_nonnegative
#print axioms YMGap.Constructive.DyadicTimeRationals.value_le_iff
#print axioms YMGap.Constructive.DyadicTimeRationals.value_eqv_iff
#print axioms YMGap.Constructive.DyadicTimeRationals.value_refine
#print axioms YMGap.Constructive.DyadicTimeRationals.half_power_num
#print axioms YMGap.Constructive.DyadicTimeRationals.half_power_den
#print axioms YMGap.Constructive.DyadicTimeRationals.unit_value
#print axioms YMGap.Constructive.DyadicTimeRationals.upper
#print axioms YMGap.Constructive.DyadicTimeRationals.upper_depth
#print axioms YMGap.Constructive.DyadicTimeRationals.upper_steps_positive
#print axioms YMGap.Constructive.DyadicTimeRationals.rational_le_upper
#print axioms YMGap.Constructive.DyadicTimeRationals.upper_le_rational_add_unit
#print axioms YMGap.Constructive.DyadicTimeRationals.upper_error
#print axioms YMGap.Constructive.DyadicTimeRationals.relative_scaled_bound
#print axioms YMGap.Constructive.DyadicTimeRationals.relative_step_budget
