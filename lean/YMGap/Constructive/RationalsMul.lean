/-
`Q'` multiplicative laws at semantic equivalence — the keystone the
geometric-tail closed form, `expNeg`'s Cauchy modulus, and the `ExpUB`
seed all share.

`Rationals.lean` provides `mul_nonneg` and `mul_le_mul_of_nonneg_right`
but flags (in `Geometric.lean`'s "Open work") that the geometric series
needs commutativity, associativity, left-distributivity at `eqv`, and
left-monotonicity — none of which were built.  This module supplies
exactly those, via cross-product reduction to `Int` (no `ring`/`linarith`,
which are unavailable without Mathlib and would risk the axiom gate).

`Q'` equality is *structural*, so these laws hold only up to `eqv`
(`a*b ≃ b*a`, not `a*b = b*a`); the `eqv↔≤` bridges (`le_of_eqv`,
`ge_of_eqv`, `le_trans'` from `Rationals.lean`) chain them into the
`≤`-facts the closures consume.

# Axiom-gate (AGENTS.md Rule 1)

Every theorem reports `[propext]` or empty.  No `Classical.*`, no
`Quot.sound`, no `sorryAx`.
-/

import YMGap.Constructive.Rationals

namespace YMGap.Constructive

namespace Q'

/-! ## Denominator-cast helpers

`(a*b).den` and `(a+b).den` are both stored as `a.den*b.den - 1`; cast to
`Int` they are `a.den * b.den` (the product of positive Nats is ≥ 1, so
the truncated subtraction is exact).  These two lemmas package the
`Nat.sub_add_cancel` idiom used throughout `Rationals.lean`. -/

/-- `((a*b).den : Int) = a.den * b.den`. -/
theorem mul_den_cast (a b : Q') :
    ((a * b).den : Int) = (a.den : Int) * (b.den : Int) := by
  show (((a.den * b.den - 1) + 1 : Nat) : Int) = (a.den : Int) * (b.den : Int)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (den_pos a) (den_pos b))))]
  exact Int.natCast_mul a.den b.den

/-- `((a+b).den : Int) = a.den * b.den` (the `Q'.add` denominator has the
same `a.den*b.den - 1` shape as `Q'.mul`). -/
theorem add_den_cast (a b : Q') :
    ((a + b).den : Int) = (a.den : Int) * (b.den : Int) := by
  show (((a.den * b.den - 1) + 1 : Nat) : Int) = (a.den : Int) * (b.den : Int)
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.pos_iff_ne_zero.mp (Nat.mul_pos (den_pos a) (den_pos b))))]
  exact Int.natCast_mul a.den b.den

/-! ## Commutativity, associativity, left-distributivity (at `eqv`) -/

/-- `a * b ≃ b * a`. -/
theorem mul_comm_eqv (a b : Q') : (a * b).eqv (b * a) := by
  show (a * b).num * ((b * a).den : Int) = (b * a).num * ((a * b).den : Int)
  show (a.num * b.num) * ((b * a).den : Int)
      = (b.num * a.num) * ((a * b).den : Int)
  rw [mul_den_cast a b, mul_den_cast b a,
      Int.mul_comm a.num b.num, Int.mul_comm b.den a.den]

/-- `(a * b) * c ≃ a * (b * c)`. -/
theorem mul_assoc_eqv (a b c : Q') : ((a * b) * c).eqv (a * (b * c)) := by
  show ((a * b) * c).num * ((a * (b * c)).den : Int)
      = (a * (b * c)).num * (((a * b) * c).den : Int)
  show ((a.num * b.num) * c.num) * ((a * (b * c)).den : Int)
      = (a.num * (b.num * c.num)) * (((a * b) * c).den : Int)
  rw [mul_den_cast (a * b) c, mul_den_cast a (b * c),
      mul_den_cast a b, mul_den_cast b c,
      Int.mul_assoc a.num b.num c.num, Int.mul_assoc a.den b.den c.den]

/-- `a * (b + c) ≃ a * b + a * c` (left-distributivity). -/
theorem mul_add_eqv (a b c : Q') : (a * (b + c)).eqv (a * b + a * c) := by
  show (a * (b + c)).num * ((a * b + a * c).den : Int)
      = (a * b + a * c).num * ((a * (b + c)).den : Int)
  have hL_num : (a * (b + c)).num
      = a.num * (b.num * (c.den : Int) + c.num * (b.den : Int)) := rfl
  have hR_num : (a * b + a * c).num
      = (a.num * b.num) * ((a * c).den : Int)
        + (a.num * c.num) * ((a * b).den : Int) := rfl
  rw [hL_num, hR_num,
      mul_den_cast a c, mul_den_cast a b,
      add_den_cast (a * b) (a * c), mul_den_cast a b, mul_den_cast a c,
      mul_den_cast a (b + c), add_den_cast b c]
  simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

/-! ## `1 * a ≃ a`, additive commutativity/associativity (at `eqv`) -/

/-- `1 * a ≃ a`. -/
theorem one_mul_eqv (a : Q') : ((1 : Q') * a).eqv a := by
  show ((1 : Q') * a).num * (a.den : Int) = a.num * (((1 : Q') * a).den : Int)
  rw [mul_den_cast (1 : Q') a]
  show ((1 : Int) * a.num) * (a.den : Int)
      = a.num * ((1 : Int) * (a.den : Int))
  rw [Int.one_mul, Int.one_mul, Int.mul_comm a.num (a.den : Int)]

/-- `a + b ≃ b + a`. -/
theorem add_comm_eqv (a b : Q') : (a + b).eqv (b + a) := by
  show (a + b).num * ((b + a).den : Int) = (b + a).num * ((a + b).den : Int)
  have hL : (a + b).num = a.num * (b.den : Int) + b.num * (a.den : Int) := rfl
  have hR : (b + a).num = b.num * (a.den : Int) + a.num * (b.den : Int) := rfl
  rw [hL, hR, add_den_cast a b, add_den_cast b a]
  simp only [Int.add_mul, Int.mul_comm, Int.mul_assoc, Int.mul_left_comm,
    Int.add_comm]

/-- `(a + b) + c ≃ a + (b + c)`. -/
theorem add_assoc_eqv (a b c : Q') : ((a + b) + c).eqv (a + (b + c)) := by
  show ((a + b) + c).num * ((a + (b + c)).den : Int)
      = (a + (b + c)).num * (((a + b) + c).den : Int)
  have hL_num : ((a + b) + c).num
      = (a.num * (b.den : Int) + b.num * (a.den : Int)) * (c.den : Int)
        + c.num * ((a + b).den : Int) := rfl
  have hR_num : (a + (b + c)).num
      = a.num * ((b + c).den : Int)
        + (b.num * (c.den : Int) + c.num * (b.den : Int)) * (a.den : Int) := rfl
  rw [hL_num, hR_num,
      add_den_cast a b, add_den_cast b c,
      add_den_cast (a + b) c, add_den_cast a b,
      add_den_cast a (b + c), add_den_cast b c]
  simp only [Int.add_mul, Int.mul_add, Int.mul_assoc, Int.mul_comm,
    Int.mul_left_comm, Int.add_comm, Int.add_left_comm, Int.add_assoc]

/-! ## Congruence of `*` over `eqv` (right factor fixed) -/

/-- `x * y * (z * w) = x * z * (y * w)` — swap the two inner factors. -/
private theorem int_AABB (x y z w : Int) :
    (x * y) * (z * w) = (x * z) * (y * w) := by
  rw [Int.mul_assoc x y (z * w), ← Int.mul_assoc y z w, Int.mul_comm y z,
      Int.mul_assoc z y w, ← Int.mul_assoc x z (y * w)]

/-- `a ≃ b → a * c ≃ b * c`.  Congruence lets us rewrite a factor inside a
product up to `eqv` (needed to commute nested powers in the geometric
step). -/
theorem mul_eqv_congr_right (a b c : Q') (h : a.eqv b) : (a * c).eqv (b * c) := by
  show (a * c).num * ((b * c).den : Int) = (b * c).num * ((a * c).den : Int)
  show (a.num * c.num) * ((b * c).den : Int)
      = (b.num * c.num) * ((a * c).den : Int)
  rw [mul_den_cast b c, mul_den_cast a c,
      int_AABB a.num c.num (b.den : Int) (c.den : Int),
      int_AABB b.num c.num (a.den : Int) (c.den : Int),
      show a.num * (b.den : Int) = b.num * (a.den : Int) from h]

/-! ## Left-monotonicity of `*` -/

/-- `a ≤ b → 0 ≤ c → c * a ≤ c * b`.  Derived from the right-mono lemma
in `Rationals.lean` plus commutativity, via the `eqv↔≤` bridges. -/
theorem mul_le_mul_of_nonneg_left
    (a b c : Q') (h_ab : a ≤ b) (h_c : (0 : Q') ≤ c) :
    c * a ≤ c * b := by
  have h1 : a * c ≤ b * c := mul_le_mul_of_nonneg_right a b c h_ab h_c
  exact le_trans' (c * a) (a * c) (c * b)
    (le_of_eqv (mul_comm_eqv c a))
    (le_trans' (a * c) (b * c) (c * b) h1 (le_of_eqv (mul_comm_eqv b c)))

end Q'

end YMGap.Constructive

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.Q'.mul_den_cast
#print axioms YMGap.Constructive.Q'.add_den_cast
#print axioms YMGap.Constructive.Q'.mul_comm_eqv
#print axioms YMGap.Constructive.Q'.mul_assoc_eqv
#print axioms YMGap.Constructive.Q'.mul_add_eqv
#print axioms YMGap.Constructive.Q'.one_mul_eqv
#print axioms YMGap.Constructive.Q'.add_comm_eqv
#print axioms YMGap.Constructive.Q'.add_assoc_eqv
#print axioms YMGap.Constructive.Q'.mul_eqv_congr_right
#print axioms YMGap.Constructive.Q'.mul_le_mul_of_nonneg_left
