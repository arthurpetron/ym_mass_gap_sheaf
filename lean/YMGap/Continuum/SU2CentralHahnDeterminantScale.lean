/-
# The positive scale in the general central Hahn determinant

For a central `(m,n)` shell, the degree-`k` Hahn row has the prospective
leading factor `(n+m-k+1)_k`.  Consequently the Vandermonde determinant scale
is

  product_{k=1}^m k! * (n+m-k+1)_k.

This module defines that exact natural number, proves it strictly positive on
the physical range `m <= n`, and checks that its first two sizes are precisely
the already proved spin-half and spin-one determinant factors.  The remaining
general theorem must identify the actual determinant with this scale.
-/

import YMGap.Continuum.SU2SpinOneCentralHahnAdjugate
import YMGap.Continuum.SU2TransvectantFactorialRecurrence

namespace YMGap.Continuum.SU2CentralHahnDeterminantScale

open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence

/-- Product through the first `K` nonconstant central Hahn rows. -/
def centralHahnDetPartial (m n : Nat) : Nat -> Nat
  | 0 => 1
  | k + 1 =>
      centralHahnDetPartial m n k * tvFact (k + 1) *
        tvFallingNat (n + m - (k + 1) + 1) (k + 1)

/-- The full prospective determinant scale for a central `(m,n)` shell. -/
def centralHahnDetScale (m n : Nat) : Nat :=
  centralHahnDetPartial m n m

/-- A falling factorial is positive throughout its support. -/
theorem tvFallingNat_pos (n : Nat) : forall r, r <= n ->
    0 < tvFallingNat n r
  | 0, _ => by simp [tvFallingNat]
  | r + 1, hr => by
      simp only [tvFallingNat]
      exact Nat.mul_pos (tvFallingNat_pos n r (by omega)) (by omega)

/-- Every partial determinant scale is positive while its row index remains
inside the physical square matrix. -/
theorem centralHahnDetPartial_pos (m n K : Nat) (hmn : m <= n) (hK : K <= m) :
    0 < centralHahnDetPartial m n K := by
  induction K with
  | zero => simp [centralHahnDetPartial]
  | succ K ih =>
      simp only [centralHahnDetPartial]
      have htop : K + 1 <= n + m - (K + 1) + 1 := by omega
      exact Nat.mul_pos
        (Nat.mul_pos (ih (by omega)) (tvFact_pos (K + 1)))
        (tvFallingNat_pos _ _ htop)

/-- The general determinant scale is strictly positive for `m <= n`. -/
theorem centralHahnDetScale_pos (m n : Nat) (hmn : m <= n) :
    0 < centralHahnDetScale m n := by
  exact centralHahnDetPartial_pos m n m hmn (Nat.le_refl m)

/-- The size-two scale is the spin-half determinant `n+1`. -/
theorem centralHahnDetScale_one (n : Nat) :
    centralHahnDetScale 1 n = n + 1 := by
  simp [centralHahnDetScale, centralHahnDetPartial, tvFact, tvFallingNat]

/-- The size-three scale is exactly the proved spin-one determinant factor. -/
theorem centralHahnDetScale_two (n : Nat) :
    centralHahnDetScale 2 n = 2 * n * (n + 1) * (n + 2) := by
  simp [centralHahnDetScale, centralHahnDetPartial, tvFact, tvFallingNat]
  ac_rfl

end YMGap.Continuum.SU2CentralHahnDeterminantScale

#print axioms YMGap.Continuum.SU2CentralHahnDeterminantScale.tvFallingNat_pos
#print axioms YMGap.Continuum.SU2CentralHahnDeterminantScale.centralHahnDetPartial_pos
#print axioms YMGap.Continuum.SU2CentralHahnDeterminantScale.centralHahnDetScale_pos
#print axioms YMGap.Continuum.SU2CentralHahnDeterminantScale.centralHahnDetScale_one
#print axioms YMGap.Continuum.SU2CentralHahnDeterminantScale.centralHahnDetScale_two
