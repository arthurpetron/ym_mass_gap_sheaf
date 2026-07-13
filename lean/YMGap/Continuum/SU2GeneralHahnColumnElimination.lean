/-
# Constructive first column-elimination step for the general central Hahn matrix

On a central shell `m <= t <= n` (hence `m <= n`), the physical source
columns and channel rows are both enumerated by `0,...,m`.  Replacing every
column after the first by its difference with the preceding column turns the
zeroth Hahn row into `(1,0,...,0)`.  The remaining lower-right block is the
central Hahn matrix at `(m-1,n-1,t-1)`, with row `k` multiplied by the exact
pivot `(k+1)*(m+n-k)`.

The second half of the module proves that the product of these elimination
pivots times the reduced prospective determinant scale is exactly the scale
already defined for the larger matrix.  No division, choice, or classical
determinant interface is used here.
-/

import YMGap.Continuum.SU2GeneralHahnAdjacentDifferenceAllOrder
import YMGap.Continuum.SU2CentralHahnDeterminantScale

namespace YMGap.Continuum.SU2GeneralHahnColumnElimination

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnAdjacentDifferenceAllOrder
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2CentralHahnDeterminantScale

local infix:50 " ≈ " => Q'.eqv

/-- A square matrix with Hahn rows and the zero-based source-column index. -/
def centralHahnMatrix (m n t : Nat) : Nat → Nat → Q' :=
  fun k i => hahnEntry m n t k i

/-- The elementary determinant-preserving column operation: retain column
zero and replace column `i+1` by `column(i+1)-column(i)`. -/
def forwardColumnStep (A : Nat → Nat → Q') : Nat → Nat → Q'
  | r, 0 => A r 0
  | r, i + 1 => A r (i + 1) + -(A r i)

/-- In the central range the general physical enumeration has no hidden
offset: both its first source coordinate and its last source coordinate are
exactly `0` and `m`, and its zero-based width is `m`. -/
theorem central_shell_enumeration (m n t : Nat)
    (hmt : m ≤ t) (htn : t ≤ n) :
    shellLo n t = 0 ∧ shellHi m t = m ∧ shellWidth m n t = m := by
  have hlo : t - n = 0 := by omega
  have hhi : min m t = m := Nat.min_eq_left hmt
  constructor
  · exact hlo
  constructor
  · exact hhi
  · unfold shellWidth shellHi shellLo
    rw [hlo, hhi]
    simp

/-- The retained upper-left entry of the column-reduced central Hahn matrix is
one. -/
theorem forwardColumnStep_upperLeft (m n t : Nat) :
    (forwardColumnStep (centralHahnMatrix m n t) 0 0).eqv 1 := by
  exact hahnEntry_zero m n t 0

/-- Every later entry of the zeroth row vanishes after the forward column
operation. -/
theorem forwardColumnStep_topRow_zero (m n t i : Nat) :
    (forwardColumnStep (centralHahnMatrix m n t) 0 (i + 1)).eqv 0 := by
  unfold forwardColumnStep centralHahnMatrix
  have hleft := hahnEntry_zero m n t (i + 1)
  have hright := hahnEntry_zero m n t i
  have hdiff := Q'.add_eqv_congr' hleft (Q'.neg_eqv_congr _ _ hright)
  exact Q'.eqv_trans _ ((1 : Q') + -1) _ hdiff (Q'.add_neg_self_eqv 1)

/-- **Actual lower-right elimination block.**  Under the exact central-shell
guards, entry `(k+1,i+1)` after the forward column operation is row pivot
`(k+1)*(m+n-k)` times entry `(k,i)` of the reduced central Hahn matrix. -/
theorem forwardColumnStep_lowerRight (m n t k i : Nat)
    (hmt : m ≤ t) (htn : t ≤ n)
    (hk : k < m) (hi : i < m) :
    (forwardColumnStep (centralHahnMatrix m n t) (k + 1) (i + 1)) ≈
      (Q'.ofNat ((k + 1) * (m + n - k)) *
        centralHahnMatrix (m - 1) (n - 1) (t - 1) k i) := by
  have h := hahnEntry_adjacent_all_order m n t (k + 1) i
    (by omega) (by omega) hi (by omega) (by omega)
  have hinner : m + n - (k + 1) + 1 = m + n - k := by omega
  have hpivot : (k + 1) * (m + n - (k + 1) + 1) =
      (k + 1) * (m + n - k) := by rw [hinner]
  simpa only [forwardColumnStep, centralHahnMatrix, hpivot,
    show k + 1 - 1 = k by omega] using h

/-! ## Exact recurrence of the prospective determinant scale -/

/-- Product of the row pivots through row `K`. -/
def centralHahnPivotPartial (m n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 =>
      centralHahnPivotPartial m n k *
        ((k + 1) * (m + n - (k + 1) + 1))

/-- Full product of all nonconstant-row pivots. -/
def centralHahnPivotScale (m n : Nat) : Nat :=
  centralHahnPivotPartial m n m

/-- Leading-factor recursion for natural falling factorials:
`(x+1)_(r+1) = (x+1) * (x)_r` throughout its support. -/
theorem tvFallingNat_leading : ∀ r x : Nat, r ≤ x →
    tvFallingNat (x + 1) (r + 1) = (x + 1) * tvFallingNat x r
  | 0, x, _ => by simp [tvFallingNat]
  | r + 1, x, hr => by
      change
        tvFallingNat (x + 1) (r + 1) * (x + 1 - (r + 1)) =
          (x + 1) * (tvFallingNat x r * (x - r))
      rw [tvFallingNat_leading r x (by omega)]
      have hsub : x + 1 - (r + 1) = x - r := by omega
      rw [hsub]
      ac_rfl

private theorem elimination_local_factor (m n k : Nat)
    (hmn : m ≤ n) (hk : k + 1 ≤ m) :
    tvFact (k + 2) *
        tvFallingNat ((n + 1) + (m + 1) - (k + 2) + 1) (k + 2) =
      ((k + 2) * ((m + 1) + (n + 1) - (k + 2) + 1)) *
        (tvFact (k + 1) *
          tvFallingNat (n + m - (k + 1) + 1) (k + 1)) := by
  let x := n + m - (k + 1) + 1
  have hx : k + 1 ≤ x := by
    dsimp only [x]
    omega
  have hlarge : (n + 1) + (m + 1) - (k + 2) + 1 = x + 1 := by
    dsimp only [x]
    omega
  have hpivot : (m + 1) + (n + 1) - (k + 2) + 1 = x + 1 := by
    dsimp only [x]
    omega
  have hsmall : n + m - (k + 1) + 1 = x := by rfl
  rw [hlarge, hpivot, hsmall, tvFallingNat_leading (k + 1) x hx]
  simp only [tvFact]
  ac_rfl

/-- Partial scale recurrence generated by the actual row pivots.  The large
scale through row `K+1` is the pivot product through that row times the
reduced scale through row `K`. -/
theorem centralHahnDetPartial_elimination (m n K : Nat)
    (hmn : m ≤ n) (hK : K ≤ m) :
    centralHahnDetPartial (m + 1) (n + 1) (K + 1) =
      centralHahnPivotPartial (m + 1) (n + 1) (K + 1) *
        centralHahnDetPartial m n K := by
  induction K with
  | zero =>
      simp [centralHahnDetPartial, centralHahnPivotPartial,
        tvFact, tvFallingNat]
      omega
  | succ K ih =>
      change
        (centralHahnDetPartial (m + 1) (n + 1) (K + 1) *
            tvFact (K + 2) *
              tvFallingNat ((n + 1) + (m + 1) - (K + 2) + 1) (K + 2)) =
          (centralHahnPivotPartial (m + 1) (n + 1) (K + 1) *
              ((K + 2) * ((m + 1) + (n + 1) - (K + 2) + 1))) *
            (centralHahnDetPartial m n K * tvFact (K + 1) *
              tvFallingNat (n + m - (K + 1) + 1) (K + 1))
      rw [ih (by omega)]
      have hlocal := elimination_local_factor m n K hmn (by omega)
      calc
        centralHahnPivotPartial (m + 1) (n + 1) (K + 1) *
              centralHahnDetPartial m n K * tvFact (K + 2) *
              tvFallingNat ((n + 1) + (m + 1) - (K + 2) + 1) (K + 2) =
            centralHahnPivotPartial (m + 1) (n + 1) (K + 1) *
              centralHahnDetPartial m n K *
              (tvFact (K + 2) *
                tvFallingNat ((n + 1) + (m + 1) - (K + 2) + 1) (K + 2)) := by
                  ac_rfl
        _ = centralHahnPivotPartial (m + 1) (n + 1) (K + 1) *
              centralHahnDetPartial m n K *
              (((K + 2) * ((m + 1) + (n + 1) - (K + 2) + 1)) *
                (tvFact (K + 1) *
                  tvFallingNat (n + m - (K + 1) + 1) (K + 1))) := by
                    rw [hlocal]
        _ = (centralHahnPivotPartial (m + 1) (n + 1) (K + 1) *
              ((K + 2) * ((m + 1) + (n + 1) - (K + 2) + 1))) *
            (centralHahnDetPartial m n K * tvFact (K + 1) *
              tvFallingNat (n + m - (K + 1) + 1) (K + 1)) := by
                ac_rfl

/-- **Full determinant-scale recurrence.**  The product of the row pivots
created by the column operation times the determinant scale of the reduced
central Hahn matrix is exactly the determinant scale of the original matrix. -/
theorem centralHahnDetScale_elimination (m n : Nat) (hmn : m ≤ n) :
    centralHahnDetScale (m + 1) (n + 1) =
      centralHahnPivotScale (m + 1) (n + 1) * centralHahnDetScale m n := by
  simpa only [centralHahnDetScale, centralHahnPivotScale] using
    centralHahnDetPartial_elimination m n m hmn (Nat.le_refl m)

end YMGap.Continuum.SU2GeneralHahnColumnElimination

#print axioms YMGap.Continuum.SU2GeneralHahnColumnElimination.central_shell_enumeration
#print axioms YMGap.Continuum.SU2GeneralHahnColumnElimination.forwardColumnStep_upperLeft
#print axioms YMGap.Continuum.SU2GeneralHahnColumnElimination.forwardColumnStep_topRow_zero
#print axioms YMGap.Continuum.SU2GeneralHahnColumnElimination.forwardColumnStep_lowerRight
#print axioms YMGap.Continuum.SU2GeneralHahnColumnElimination.tvFallingNat_leading
#print axioms YMGap.Continuum.SU2GeneralHahnColumnElimination.centralHahnDetPartial_elimination
#print axioms YMGap.Continuum.SU2GeneralHahnColumnElimination.centralHahnDetScale_elimination
