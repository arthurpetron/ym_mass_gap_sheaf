/-
`Q'`–to–`Nat` bridges: a nonnegative rational is dominated by (the `Q'`
embedding of) its numerator's `toNat`, and there is an explicit `Nat`
cutoff `M` with `x · 1/(M+1) ≤ 1/2` for every `x ≥ 0`.

Both facts are pure *data + bound* statements (an explicit `Nat`, plus a
cross-product `Int` inequality), exactly the Rule-8 modulus shape: the
cutoff `halfRatioCutoff x = 2 · x.num.toNat` is computable, and
`halfRatioCutoff_spec` certifies it.  Proofs reduce the `Q'.le` goal to
its underlying `Int` cross-product and discharge it with Lean-core `Int`
monotonicity lemmas only.

# Axiom-gate (AGENTS.md Rule 1)

Every theorem reports `[propext]` only.  No `Classical.*`, no
`Quot.sound`, no `sorryAx`, no `omega`.
-/

import YMGap.Constructive.Reals
import YMGap.Constructive.RationalsMul

namespace YMGap.Constructive.RatNat

open YMGap.Constructive

/-- A nonnegative `Q'` is bounded above by the `Q'` embedding of its
numerator's `toNat`.

The `≤` unfolds to the `Int` cross-product
`x.num · (ofNat x.num.toNat).den ≤ (ofNat x.num.toNat).num · x.den`.
Since `(ofNat n).den = 1` and `(ofNat n).num = (n : Int)`, this is
`x.num · 1 ≤ (x.num.toNat : Int) · x.den`.  From `hx` we get
`0 ≤ x.num`, hence `(x.num.toNat : Int) = x.num`; and `1 ≤ x.den`, so
`x.num · 1 ≤ x.num · x.den = (x.num.toNat : Int) · x.den`. -/
theorem le_ofNat_toNat (x : Q') (hx : (0 : Q') ≤ x) :
    x ≤ Q'.ofNat x.num.toNat := by
  show x.num * ((Q'.ofNat x.num.toNat).den : Int)
      ≤ (Q'.ofNat x.num.toNat).num * (x.den : Int)
  show x.num * (1 : Int) ≤ (Int.ofNat x.num.toNat) * (x.den : Int)
  have h_num_nn : (0 : Int) ≤ x.num := (Q'.zero_le_iff_num_nonneg x).mp hx
  have h_toNat : (Int.ofNat x.num.toNat) = x.num := Int.toNat_of_nonneg h_num_nn
  rw [h_toNat, Int.mul_one]
  have h_one_le_den : (1 : Int) ≤ (x.den : Int) := by
    have : (1 : Nat) ≤ x.den := x.den_pos
    exact_mod_cast this
  have h := Int.mul_le_mul_of_nonneg_left h_one_le_den h_num_nn
  rw [Int.mul_one] at h
  exact h

/-- An explicit `Nat` cutoff `M` (as DATA) such that `x / (M+1) ≤ 1/2`
for every `x ≥ 0`.  Concretely `M = 2 · x.num.toNat`. -/
def halfRatioCutoff (x : Q') : Nat := 2 * x.num.toNat

/-- The cutoff certificate: `x · 1/(M+1) ≤ 1/2` with `M = halfRatioCutoff x`.

The `≤` unfolds, using `(x * invSucc M).num = x.num · 1 = x.num`,
`(mkPos 1 2 _).num = 1`, `(mkPos 1 2 _).den = 2`, and
`((x * invSucc M).den : Int) = x.den · (M+1)` (via `mul_den_cast`,
`invSucc_den`), to the `Int` inequality `x.num · 2 ≤ 1 · (x.den · (M+1))`.

With `0 ≤ x.num` we have `(M+1 : Int) = 2·x.num + 1`, and `1 ≤ x.den`,
so `x.den · (M+1) ≥ 1 · (2·x.num + 1) = 2·x.num + 1 ≥ 2·x.num`. -/
theorem halfRatioCutoff_spec (x : Q') (hx : (0 : Q') ≤ x) :
    x * Q'.invSucc (halfRatioCutoff x) ≤ Q'.mkPos 1 2 (by decide) := by
  show (x * Q'.invSucc (halfRatioCutoff x)).num
        * ((Q'.mkPos 1 2 (by decide)).den : Int)
      ≤ (Q'.mkPos 1 2 (by decide)).num
        * ((x * Q'.invSucc (halfRatioCutoff x)).den : Int)
  have h_prod_num : (x * Q'.invSucc (halfRatioCutoff x)).num
      = x.num * (1 : Int) := rfl
  rw [h_prod_num, Int.mul_one]
  show x.num * (2 : Int)
      ≤ (1 : Int) * ((x * Q'.invSucc (halfRatioCutoff x)).den : Int)
  rw [Q'.mul_den_cast x (Q'.invSucc (halfRatioCutoff x))]
  have h_invden : ((Q'.invSucc (halfRatioCutoff x)).den : Int)
      = ((halfRatioCutoff x + 1 : Nat) : Int) := by
    rw [Q'.invSucc_den]
  rw [h_invden, Int.one_mul]
  have h_num_nn : (0 : Int) ≤ x.num := (Q'.zero_le_iff_num_nonneg x).mp hx
  have h_toNat : (Int.ofNat x.num.toNat) = x.num := Int.toNat_of_nonneg h_num_nn
  have h_Mplus1 : ((halfRatioCutoff x + 1 : Nat) : Int) = 2 * x.num + 1 := by
    show ((2 * x.num.toNat + 1 : Nat) : Int) = 2 * x.num + 1
    rw [Int.natCast_add, Int.natCast_mul]
    show (2 : Int) * (Int.ofNat x.num.toNat) + (1 : Int) = 2 * x.num + 1
    rw [h_toNat]
  rw [h_Mplus1]
  have h_one_le_den : (1 : Int) ≤ (x.den : Int) := by
    have : (1 : Nat) ≤ x.den := x.den_pos
    exact_mod_cast this
  have h_rhs_nn : (0 : Int) ≤ 2 * x.num + 1 := by
    have h2num : (0 : Int) ≤ 2 * x.num := Int.mul_nonneg (by decide) h_num_nn
    exact Int.add_nonneg h2num (by decide)
  have h_scale : (1 : Int) * (2 * x.num + 1) ≤ (x.den : Int) * (2 * x.num + 1) :=
    Int.mul_le_mul_of_nonneg_right h_one_le_den h_rhs_nn
  rw [Int.one_mul] at h_scale
  have h_step : x.num * (2 : Int) ≤ 2 * x.num + 1 := by
    rw [Int.mul_comm x.num (2 : Int)]
    exact Int.le_add_of_nonneg_right (by decide)
  exact Int.le_trans h_step h_scale

end YMGap.Constructive.RatNat

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.RatNat.le_ofNat_toNat
#print axioms YMGap.Constructive.RatNat.halfRatioCutoff_spec
