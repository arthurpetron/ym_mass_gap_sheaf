/-
# Computable normal form for the project's constructive rationals

The existing `Q'` operations deliberately leave fractions unreduced. This
module divides numerator and positive denominator by their natural gcd,
without changing `Rationals.lean` or replacing its setoid equality. The
result has a coprime numerator magnitude and denominator; reduced addition
and multiplication simply apply this operation after the existing exact
arithmetic. These are storage-size facts about one rational operation, not
uniform bounds on iterated coefficients, arithmetic runtime, or a physical
Yang--Mills estimate.
-/

import YMGap.Constructive.Rationals
import Init.Data.Nat.Coprime
import Init.Data.Int.DivMod.Lemmas

namespace YMGap.Constructive.Q'

set_option autoImplicit false

private def common (q : Q') : Nat := Nat.gcd q.num.natAbs q.den

private theorem common_pos (q : Q') : 0 < common q := by
  unfold common
  exact Nat.gcd_pos_of_pos_right _ (den_pos q)

private theorem common_le_den (q : Q') : common q ≤ q.den := by
  unfold common
  exact Nat.gcd_le_right _ (den_pos q)

private theorem common_dvd_den (q : Q') : common q ∣ q.den := by
  unfold common
  exact Nat.gcd_dvd_right _ _

private theorem common_dvd_num (q : Q') : (common q : Int) ∣ q.num := by
  apply Int.natAbs_dvd_natAbs.mp
  simpa only [Int.natAbs_natCast, common] using
    (Nat.gcd_dvd_left q.num.natAbs q.den)

private theorem reducedDen_pos (q : Q') : 0 < q.den / common q :=
  Nat.div_pos (common_le_den q) (common_pos q)

/-- Divide by the explicit natural gcd, retaining a positive denominator.
This is a data-valued computation with no quotient or choice. -/
def reduce (q : Q') : Q' :=
  ⟨q.num / (common q : Int), (q.den / common q).pred⟩

/-- The stored numerator after reduction. -/
theorem reduce_num (q : Q') :
    (reduce q).num = q.num / (common q : Int) := rfl

/-- The positive denominator after reduction. -/
theorem reduce_den (q : Q') :
    (reduce q).den = q.den / common q := by
  exact Nat.succ_pred_eq_of_pos (reducedDen_pos q)

/-- Reduction preserves the rational represented by `q`. -/
theorem reduce_eqv (q : Q') : eqv (reduce q) q := by
  have hd : ((q.den / common q : Nat) : Int) * (common q : Int) =
      (q.den : Int) := by
    have h := congrArg (fun n : Nat => (n : Int))
      (Nat.div_mul_cancel (common_dvd_den q))
    simpa only [Int.natCast_mul] using h
  have hn : q.num / (common q : Int) * (common q : Int) = q.num :=
    Int.ediv_mul_cancel (common_dvd_num q)
  show (reduce q).num * (q.den : Int) = q.num * ((reduce q).den : Int)
  rw [reduce_num, reduce_den]
  calc
    (q.num / (common q : Int)) * (q.den : Int) =
        (q.num / (common q : Int)) *
          (((q.den / common q : Nat) : Int) * (common q : Int)) := by rw [hd]
    _ = (q.num / (common q : Int) * (common q : Int)) *
          ((q.den / common q : Nat) : Int) := by ac_rfl
    _ = q.num * ((q.den / common q : Nat) : Int) := by rw [hn]

/-- Gcd reduction never enlarges the stored denominator. -/
theorem reduce_den_le (q : Q') : (reduce q).den ≤ q.den := by
  rw [reduce_den]
  exact Nat.div_le_self _ _

/-- Gcd reduction never enlarges the stored numerator magnitude. -/
theorem reduce_numAbs_le (q : Q') : (reduce q).num.natAbs ≤ q.num.natAbs := by
  rw [reduce_num]
  exact Int.natAbs_ediv_le_natAbs _ _

/-- A reduced numerator is zero exactly when the input numerator is zero. -/
theorem reduce_num_zero_iff (q : Q') : (reduce q).num = 0 ↔ q.num = 0 := by
  constructor
  · intro hz
    have hn : q.num / (common q : Int) * (common q : Int) = q.num :=
      Int.ediv_mul_cancel (common_dvd_num q)
    rw [← reduce_num q, hz, Int.zero_mul] at hn
    exact hn.symm
  · intro hz
    rw [reduce_num, hz]
    simp

private theorem divided_numAbs (q : Q') :
    (q.num / (common q : Int)).natAbs = q.num.natAbs / common q := by
  have hn : q.num / (common q : Int) * (common q : Int) = q.num :=
    Int.ediv_mul_cancel (common_dvd_num q)
  have hleft : (q.num / (common q : Int)).natAbs * common q =
      q.num.natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
      (congrArg Int.natAbs hn)
  have hright : (q.num.natAbs / common q) * common q = q.num.natAbs :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left q.num.natAbs q.den)
  exact Nat.eq_of_mul_eq_mul_right (common_pos q) (hleft.trans hright.symm)

/-- The output is a genuine gcd-normal form, even for zero or negative
numerators. -/
theorem reduce_coprime (q : Q') :
    Nat.Coprime (reduce q).num.natAbs (reduce q).den := by
  rw [reduce_num, reduce_den, divided_numAbs]
  simpa only [common] using
    (Nat.gcd_div_gcd_div_gcd_of_pos_right (den_pos q))

/-- Exact addition followed by computable gcd reduction. -/
def reducedAdd (p q : Q') : Q' := reduce (p + q)

/-- Exact multiplication followed by computable gcd reduction. -/
def reducedMul (p q : Q') : Q' := reduce (p * q)

theorem reducedAdd_eqv (p q : Q') : eqv (reducedAdd p q) (p + q) :=
  reduce_eqv _

theorem reducedMul_eqv (p q : Q') : eqv (reducedMul p q) (p * q) :=
  reduce_eqv _

/-- Structural computation, not just setoid equivalence: 2/4 becomes 1/2. -/
example : reduce (mkPos 2 4 (by decide)) = mkPos 1 2 (by decide) := by decide

/-- Reduced addition coalesces two halves to the structural integer one. -/
example : reducedAdd (mkPos 1 2 (by decide)) (mkPos 1 2 (by decide)) =
    (1 : Q') := by decide

#print axioms reduce
#print axioms reduce_num
#print axioms reduce_den
#print axioms reduce_eqv
#print axioms reduce_den_le
#print axioms reduce_numAbs_le
#print axioms reduce_num_zero_iff
#print axioms reduce_coprime
#print axioms reducedAdd
#print axioms reducedMul
#print axioms reducedAdd_eqv
#print axioms reducedMul_eqv

end YMGap.Constructive.Q'
