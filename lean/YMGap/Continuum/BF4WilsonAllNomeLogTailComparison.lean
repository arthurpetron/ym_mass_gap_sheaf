/-
# A relative finite logarithm-tail bound on the ORIGINAL completion

The actual positive mixed moments compare the two finite sums coefficient
by coefficient, BEFORE taking a norm.  The tail starting at m is bounded
by (I-T)^m applied to the unshifted regularized partial sum.  No inverse of
T, spectral representation, or exclusion of the ambient kernel is used.
The consumer is convergence of the ordinary logarithm on the existing
derivative domain.  This finite statement supplies no physical scaling.
-/

import YMGap.Continuum.BF4WilsonAllNomeLogPartial
import YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra
import YMGap.Continuum.RCPolynomialFunctional

namespace YMGap.Continuum.BF4WilsonAllNomeLogTailComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail
open YMGap.Continuum.BF4WilsonAllNomeLogPartial
open YMGap.Continuum.BF4WilsonAllNomeDefectPolynomialAlgebra
  (defectPower_additive defectPower_smul defectPower_zero)
open YMGap.Continuum.RCPolynomialFunctional (rc_zero_add)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "DP" => defectPower hw0 hw1
local notation "v" => positiveTimeTail hw0 hw1

/-- Reciprocal start and defect offset remain separate computed indices. -/
def filteredTail (start offset : Nat) : Nat → V → V
  | 0, _ => Z
  | len+1, x => A (S (Q'.invSucc start) (v (offset+1) x))
      (filteredTail (start+1) (offset+1) len x)

theorem timeTail_pair_nonnegative (x : V) (i j : Nat) :
    RCnonneg (B (v i x) (v j x)) := by
  have hpin : B (v i x) (v j x) = mixedMoment hw0 hw1 x 2 (i+j) := by
    unfold positiveTimeTail
    rw [defectPower_symmetric, ← defectPower_add,
      ← time_defectPower, completedInner_time_sum]
    rfl
  rw [hpin]
  exact mixedMoment_nonnegative hw0 hw1 x 2 (i+j)

theorem filteredTail_timeTail_nonnegative (x : V) (start offset len j : Nat) :
    RCnonneg (B (filteredTail hw0 hw1 start offset len x) (v j x)) := by
  induction len generalizing start offset with
  | zero =>
      change RCnonneg (B Z (v j x))
      rw [completedInner_zero_left]
      exact RCle_refl _
  | succ len ih =>
      change RCnonneg (B (A (S (Q'.invSucc start) (v (offset+1) x))
        (filteredTail hw0 hw1 (start+1) (offset+1) len x)) (v j x))
      rw [completedInner_add_left, completedInner_smul_left]
      have hh := RCscale_mono (Q'.invSucc_nonneg start)
        (timeTail_pair_nonnegative hw0 hw1 x (offset+1) j)
      rw [RCscale_RCzero] at hh
      simpa only [rc_zero_add] using RCadd_le_add hh (ih (start+1) (offset+1))

/-- Increasing only the reciprocal denominator decreases every paired sum.
All actual mixed pairings are retained and proved nonnegative. -/
theorem filteredTail_timeTail_mono (x : V) (a b : Nat) (hab : a ≤ b)
    (offset len j : Nat) :
    RCle (B (filteredTail hw0 hw1 b offset len x) (v j x))
      (B (filteredTail hw0 hw1 a offset len x) (v j x)) := by
  induction len generalizing a b offset with
  | zero => exact RCle_refl _
  | succ len ih =>
      change RCle
        (B (A (S (Q'.invSucc b) (v (offset+1) x))
          (filteredTail hw0 hw1 (b+1) (offset+1) len x)) (v j x))
        (B (A (S (Q'.invSucc a) (v (offset+1) x))
          (filteredTail hw0 hw1 (a+1) (offset+1) len x)) (v j x))
      rw [completedInner_add_left, completedInner_add_left,
        completedInner_smul_left, completedInner_smul_left]
      exact RCadd_le_add
        (RCscale_scalar_mono (ExpNeg.invSucc_le_of_le hab)
          (timeTail_pair_nonnegative hw0 hw1 x (offset+1) j))
        (ih (a+1) (b+1) (by omega) (offset+1))

/-- The comparison survives BOTH finite sums, hence an actual squared norm. -/
theorem filteredTail_pair_mono (x : V) (a b : Nat) (hab : a ≤ b)
    (c d : Nat) (hcd : c ≤ d) (offset len offset' len' : Nat) :
    RCle (B (filteredTail hw0 hw1 b offset len x)
        (filteredTail hw0 hw1 d offset' len' x))
      (B (filteredTail hw0 hw1 a offset len x)
        (filteredTail hw0 hw1 c offset' len' x)) := by
  induction len' generalizing c d offset' with
  | zero =>
      change RCle (B _ Z) (B _ Z)
      rw [completedInner_zero_right, completedInner_zero_right]
      exact RCle_refl _
  | succ len' ih =>
      change RCle
        (B (filteredTail hw0 hw1 b offset len x)
          (A (S (Q'.invSucc d) (v (offset'+1) x))
            (filteredTail hw0 hw1 (d+1) (offset'+1) len' x)))
        (B (filteredTail hw0 hw1 a offset len x)
          (A (S (Q'.invSucc c) (v (offset'+1) x))
            (filteredTail hw0 hw1 (c+1) (offset'+1) len' x)))
      rw [completedInner_add_right, completedInner_add_right,
        completedInner_smul_right, completedInner_smul_right]
      have hh := RCle_trans
        (RCscale_mono (Q'.invSucc_nonneg d)
          (filteredTail_timeTail_mono hw0 hw1 x a b hab offset len (offset'+1)))
        (RCscale_scalar_mono (ExpNeg.invSucc_le_of_le hcd)
          (filteredTail_timeTail_nonnegative hw0 hw1 x a offset len (offset'+1)))
      exact RCadd_le_add hh (ih (c+1) (d+1) (by omega) (offset'+1))

theorem filteredTail_diagonal (x : V) (start len : Nat) :
    filteredTail hw0 hw1 start start len x = logTail hw0 hw1 start len x := by
  induction len generalizing start with
  | zero => rfl
  | succ len ih =>
      change A (logTerm hw0 hw1 start x)
        (filteredTail hw0 hw1 (start+1) (start+1) len x) = _
      rw [ih]
      rfl

theorem filteredTail_shift (x : V) (m start len : Nat) :
    filteredTail hw0 hw1 start (m+start) len x =
      DP m (logTail hw0 hw1 start len x) := by
  induction len generalizing start with
  | zero => exact (defectPower_zero hw0 hw1 m).symm
  | succ len ih =>
      change A (S (Q'.invSucc start) (v (m+start+1) x))
        (filteredTail hw0 hw1 (start+1) (m+start+1) len x) =
          DP m (A (S (Q'.invSucc start) (v (start+1) x))
            (logTail hw0 hw1 (start+1) len x))
      rw [defectPower_additive, defectPower_smul]
      have hv : DP m (v (start+1) x) = v (m+start+1) x := by
        unfold positiveTimeTail
        rw [← defectPower_add]
        congr 1
      rw [hv, show m+start+1 = m+(start+1) by omega, ih]

/-- The finite tail is controlled by the SAME defect filter of the unshifted
partial sum. Its limit consumer does not assume a preimage norm ceiling. -/
theorem logTail_norm_le_shifted_partial (x : V) (m n : Nat) :
    RCle (B (logTail hw0 hw1 m n x) (logTail hw0 hw1 m n x))
      (B (DP m (logPartial hw0 hw1 n x))
        (DP m (logPartial hw0 hw1 n x))) := by
  have h := filteredTail_pair_mono hw0 hw1 x 0 m (Nat.zero_le m)
    0 m (Nat.zero_le m) m n m n
  rw [filteredTail_diagonal] at h
  have hp : filteredTail hw0 hw1 0 m n x = DP m (logPartial hw0 hw1 n x) := by
    simpa only [Nat.add_zero, logPartial] using filteredTail_shift hw0 hw1 x m 0 n
  rwa [hp] at h

#print axioms filteredTail
#print axioms timeTail_pair_nonnegative
#print axioms filteredTail_timeTail_nonnegative
#print axioms filteredTail_timeTail_mono
#print axioms filteredTail_pair_mono
#print axioms filteredTail_diagonal
#print axioms filteredTail_shift
#print axioms logTail_norm_le_shifted_partial

end YMGap.Continuum.BF4WilsonAllNomeLogTailComparison
