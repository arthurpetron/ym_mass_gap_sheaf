/-
# Column elimination on every physical Hahn shell

Physical source columns are enumerated from `shellLo n t` through
`shellHi m t`, while active contraction orders run from zero through the same
`shellWidth`.  On every positive-width shell, decrementing `(m,n,t)` leaves
the source offset unchanged and lowers the width by one.  Consequently the
all-order adjacent-column identity gives the same lower-right elimination
block as in the central range, now for the exact general enumeration.
-/

import YMGap.Continuum.SU2GeneralHahnCentralCoordinateBases

namespace YMGap.Continuum.SU2GeneralHahnAllShellColumnElimination

open YMGap.Constructive
open YMGap.Continuum.SU2GeneralShellHahnMatrix
open YMGap.Continuum.SU2GeneralHahnAdjacentDifferenceAllOrder
open YMGap.Continuum.SU2GeneralHahnColumnElimination

local infix:50 " ≈ " => Q'.eqv

/-- Exact square Hahn matrix with the physical source-column offset. -/
def physicalHahnMatrix (m n t : Nat) : Nat → Nat → Q' :=
  fun k a => hahnEntry m n t k (shellLo n t + a)

/-- Positive shell width forces all three labels being decremented to be
strictly positive. -/
theorem positive_width_labels_pos (m n t : Nat) (ht : t ≤ m + n)
    (hw : 0 < shellWidth m n t) :
    0 < m ∧ 0 < n ∧ 0 < t := by
  have hlohi := shellLo_le_shellHi m n t ht
  have hstrict : shellLo n t < shellHi m t := by
    unfold shellWidth at hw
    omega
  have hm : 0 < m := by
    have hle := Nat.min_le_left m t
    unfold shellHi at hstrict
    omega
  have htpos : 0 < t := by
    have hle := Nat.min_le_right m t
    unfold shellHi at hstrict
    omega
  have hn : 0 < n := by
    cases n with
    | zero =>
        unfold shellLo shellHi at hstrict
        have hle := Nat.min_le_right m t
        omega
    | succ n => omega
  exact ⟨hm, hn, htpos⟩

/-- The lower shell has exactly the same physical source offset. -/
theorem shellLo_pred_eq (m n t : Nat) (ht : t ≤ m + n)
    (hw : 0 < shellWidth m n t) :
    shellLo (n - 1) (t - 1) = shellLo n t := by
  have hp := positive_width_labels_pos m n t ht hw
  unfold shellLo
  omega

private theorem shellHi_pred_eq (m t : Nat)
    (hm : 0 < m) (ht : 0 < t) :
    shellHi (m - 1) (t - 1) = shellHi m t - 1 := by
  unfold shellHi
  by_cases hmt : m ≤ t
  · have hpred : m - 1 ≤ t - 1 := by omega
    rw [Nat.min_eq_left hmt, Nat.min_eq_left hpred]
  · have htm : t ≤ m := by omega
    have hpred : t - 1 ≤ m - 1 := by omega
    rw [Nat.min_eq_right htm, Nat.min_eq_right hpred]

/-- The lower shell has width exactly one smaller. -/
theorem shellWidth_pred_eq (m n t : Nat) (ht : t ≤ m + n)
    (hw : 0 < shellWidth m n t) :
    shellWidth (m - 1) (n - 1) (t - 1) =
      shellWidth m n t - 1 := by
  have hp := positive_width_labels_pos m n t ht hw
  have hlo := shellLo_pred_eq m n t ht hw
  have hhi := shellHi_pred_eq m t hp.1 hp.2.2
  have hlohi := shellLo_le_shellHi m n t ht
  unfold shellWidth
  rw [hlo, hhi]
  omega

/-- The retained upper-left entry is one on every physical shell. -/
theorem physical_forward_upperLeft (m n t : Nat) :
    forwardColumnStep (physicalHahnMatrix m n t) 0 0 ≈ 1 := by
  exact hahnEntry_zero m n t (shellLo n t)

/-- Every later entry of the constant zeroth row vanishes. -/
theorem physical_forward_topRow_zero (m n t i : Nat) :
    forwardColumnStep (physicalHahnMatrix m n t) 0 (i + 1) ≈ 0 := by
  unfold forwardColumnStep physicalHahnMatrix
  have hleft := hahnEntry_zero m n t (shellLo n t + (i + 1))
  have hright := hahnEntry_zero m n t (shellLo n t + i)
  have hdiff := Q'.add_eqv_congr' hleft
    (Q'.neg_eqv_congr _ _ hright)
  exact Q'.eqv_trans _ ((1 : Q') + -1) _ hdiff
    (Q'.add_neg_self_eqv 1)

/-- **General lower-right elimination block.**  With the exact physical
column enumeration, deleting the constant row and first column gives a
positive row pivot times the complete matrix of the decremented shell. -/
theorem physical_forward_lowerRight (m n t k i : Nat)
    (ht : t ≤ m + n)
    (hk : k < shellWidth m n t)
    (hi : i < shellWidth m n t) :
    forwardColumnStep (physicalHahnMatrix m n t) (k + 1) (i + 1) ≈
      Q'.ofNat ((k + 1) * (m + n - k)) *
        physicalHahnMatrix (m - 1) (n - 1) (t - 1) k i := by
  have hw : 0 < shellWidth m n t := by omega
  have hlo := shellLo_pred_eq m n t ht hw
  have hchan := channelActive_of_index m n t (k + 1) ht (by omega)
  have hsrc := sourceActive_of_index m n t i ht (by omega)
  have hsrcNext := sourceActive_of_index m n t (i + 1) ht (by omega)
  let I := shellLo n t + i
  have hIm : I < m := by
    dsimp only [I]
    have h := hsrcNext.2.1
    omega
  have hIt : I < t := by
    dsimp only [I]
    have h := hsrcNext.1
    omega
  have hIn : t - I ≤ n := by
    dsimp only [I]
    exact hsrc.2.2
  have hadj := hahnEntry_adjacent_all_order m n t (k + 1) I
    hchan.1 hchan.2.1 hIm hIt hIn
  have hkm : k + 1 ≤ m := hchan.1
  have hpivot : (k + 1) * (m + n - (k + 1) + 1) =
      (k + 1) * (m + n - k) := by
    congr 1
    omega
  simpa only [forwardColumnStep, physicalHahnMatrix, I, hlo, hpivot,
    show k + 1 - 1 = k by omega,
    show shellLo n t + (i + 1) = shellLo n t + i + 1 by omega] using hadj

end YMGap.Continuum.SU2GeneralHahnAllShellColumnElimination

#print axioms YMGap.Continuum.SU2GeneralHahnAllShellColumnElimination.positive_width_labels_pos
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellColumnElimination.shellLo_pred_eq
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellColumnElimination.shellWidth_pred_eq
#print axioms YMGap.Continuum.SU2GeneralHahnAllShellColumnElimination.physical_forward_lowerRight
