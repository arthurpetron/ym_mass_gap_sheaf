/-
# Torus RP (f2): rational polarization Cauchy–Schwarz (abstract)

`cs_q`: for `a b c : Q'`, if `0 ≤ s²a + 2st·b + t²c` for all integers `s, t` (as `Q'`), then `b·b ≤ a·c`.
This is the cross-multiplied shape of `SU2LogConvexGap.LogConvex`. It reduces to `cs_int` through
numerators and denominators. It is constructive: no reals, no Classical.

**OPEN: the bilinear expansion and symmetry of `rpB`, i.e. `TorusCS` itself.**
-/

import YMGap.Continuum.SU2TorusRPCSCore
import YMGap.Constructive.RegularCReal
import YMGap.Constructive.RationalsMul

namespace YMGap.Continuum.SU2TorusRPCSRat

set_option autoImplicit false

open YMGap.Constructive

/-- The polarization quadratic `s²a + 2st·b + t²c`. -/
def quad (a b c : Q') (s t : Int) : Q' :=
  (Q'.ofInt s * Q'.ofInt s) * a + ((Q'.ofInt s * Q'.ofInt t) * b + (Q'.ofInt s * Q'.ofInt t) * b) +
    (Q'.ofInt t * Q'.ofInt t) * c

theorem ofInt_den (s : Int) : ((Q'.ofInt s).den : Int) = 1 := rfl

theorem quad_num (a b c : Q') (s t : Int) :
    (quad a b c s t).num = (b.den : Int) * (s * s * (a.num * b.den * c.den) +
      (s * t * (b.num * a.den * c.den) + s * t * (b.num * a.den * c.den)) + t * t * (c.num * a.den * b.den)) := by
  have e : ∀ x : Int, (Q'.ofInt x).num = x := fun _ => rfl
  unfold quad
  simp only [Q'.add_num_cast, Q'.mul_num_cast, Q'.add_den_cast, Q'.mul_den_cast, ofInt_den, e]
  simp only [Int.mul_add, Int.add_mul, Int.mul_one, Int.one_mul]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem cs_q (a b c : Q') (h : ∀ s t : Int, (0 : Q') ≤ quad a b c s t) : b * b ≤ a * c := by
  have hα : (0 : Int) < a.den := Int.ofNat_lt.mpr (Q'.den_pos a)
  have hβ : (0 : Int) < b.den := Int.ofNat_lt.mpr (Q'.den_pos b)
  have hγ : (0 : Int) < c.den := Int.ofNat_lt.mpr (Q'.den_pos c)
  have hi := YMGap.Continuum.SU2TorusRPCSCore.cs_int (a.num * b.den * c.den) (b.num * a.den * c.den)
    (c.num * a.den * b.den) fun s t => by
      have := (Q'.zero_le_iff_num_nonneg _).1 (h s t)
      rw [quad_num] at this
      exact Int.nonneg_of_mul_nonneg_left (by rwa [Int.mul_comm] at this) hβ
  show (b * b).num * ((a * c).den : Int) ≤ (a * c).num * ((b * b).den : Int)
  rw [Q'.mul_num_cast, Q'.mul_num_cast, Q'.mul_den_cast, Q'.mul_den_cast]
  have hk : (0 : Int) < a.den * c.den := Int.mul_pos hα hγ
  refine Int.le_of_mul_le_mul_right ?_ hk
  have e1 : b.num * a.den * c.den * (b.num * a.den * c.den) = b.num * b.num * (a.den * c.den) * (a.den * c.den) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have e2 : a.num * b.den * c.den * (c.num * a.den * b.den) = a.num * c.num * (b.den * b.den) * (a.den * c.den) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [e1, e2] at hi
  exact hi

end YMGap.Continuum.SU2TorusRPCSRat

#print axioms YMGap.Continuum.SU2TorusRPCSRat.cs_q
