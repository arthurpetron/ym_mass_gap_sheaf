/-
# Finite regularized-log partial sums on the actual all-nome Wilson carrier

For the original completed one-step transfer T and D=I-T, these are the
finite vectors sum_{k=1}^N D^k T x/k.  The proved mixed time-defect moments
bound every pair of terms and hence the squared norm of every finite tail
by invSucc(start)^2 times the original norm.  No scalar spectral model or
different completed carrier enters this finite statement.
-/

import YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail
import YMGap.Continuum.BF4WilsonAllNomeDistance
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeLogPartial

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail
open YMGap.Continuum.BF4WilsonAllNomeDistance

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "M" => mixedMoment hw0 hw1
local notation "v" => positiveTimeTail hw0 hw1

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_of_eq (Q'.zero_add' (A'.approx n))))

private theorem scale_add (a b : Q') (c : RC) :
    RCscale (a+b) c = RCadd (RCscale a c) (RCscale b c) := by
  refine Quotient.inductionOn c ?_
  intro C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.add_mul_eqv a b (C.approx n)))

private theorem recip_step (n : Nat) :
    Q'.eqv (Q'.invSucc n * Q'.invSucc (n+1) + Q'.invSucc (n+1))
      (Q'.invSucc n) := by
  let a := Q'.invSucc n
  let b := Q'.invSucc (n+1)
  have hfirst : Q'.eqv (a*b+b) (b*a+b*1) :=
    Q'.add_eqv_congr' (Q'.mul_comm_eqv a b)
      (Q'.eqv_symm (Q'.mul_one_eqv b))
  exact Q'.eqv_trans _ _ _ hfirst
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_add_eqv b a 1))
      (ExpNeg.invSucc_cancel n))

private theorem recip_step_mul (n : Nat) (c : Q') :
    Q'.eqv
      ((Q'.invSucc n * (Q'.invSucc (n+1)*c)) +
        Q'.invSucc (n+1)*c)
      (Q'.invSucc n*c) := by
  let a := Q'.invSucc n
  let b := Q'.invSucc (n+1)
  have h1 : Q'.eqv (a*(b*c)+b*c) ((a*b+b)*c) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_symm (Q'.mul_assoc_eqv a b c))
        (Q'.eqv_refl _))
      (Q'.eqv_symm (Q'.add_mul_eqv (a*b) b c))
  exact Q'.eqv_trans _ _ _ h1
    (Q'.mul_eqv_congr_right _ _ c (recip_step n))

private theorem zero_le_scaled_norm (c : Q') (hc : (0 : Q') ≤ c) (x : V) :
    RCnonneg (RCscale c (B x x)) := by
  have h := RCscale_mono hc (completedInner_nonnegative hw0 hw1 x)
  rw [RCscale_RCzero] at h
  exact h

/-- Every pair of actual polynomial-filtered positive-time vectors has a
product reciprocal bound, not just a separate diagonal bound. -/
theorem positiveTimeTail_pair_bound (x : V) (i j : Nat) :
    RCle (B (v i x) (v j x))
      (RCscale (Q'.invSucc i * Q'.invSucc j) (B x x)) := by
  have hpin : B (v i x) (v j x) = M x 2 (i+j) := by
    unfold positiveTimeTail
    rw [defectPower_symmetric, ← defectPower_add, ← time_defectPower,
      completedInner_time_sum]
    rfl
  have hi := mixedMoment_row_bound hw0 hw1 x 1 j i
  rw [Nat.add_comm j i] at hi
  have hj := mixedMoment_row_bound hw0 hw1 x 0 0 j
  simp only [Nat.zero_add, mixedMoment_zero] at hj
  have h := RCle_trans hi (RCscale_mono (Q'.invSucc_nonneg i) hj)
  rw [RCscale_RCscale] at h
  rwa [hpin]

/-- The kth summand of the finite regularized-log polynomial, with k=n+1. -/
def logTerm (n : Nat) (x : V) : V := S (Q'.invSucc n) (v (n+1) x)

/-- A head-recursive finite tail; all terms remain on the original completion. -/
def logTail (start : Nat) : Nat → V → V
  | 0, _ => Z
  | len+1, x => A (logTerm hw0 hw1 start x)
      (logTail (start+1) len x)

def logPartial (n : Nat) (x : V) : V := logTail hw0 hw1 0 n x

/-- A finite tail paired with one filtered time vector. -/
theorem logTail_timeTail_pair_bound (x : V) (start len j : Nat) :
    RCle (B (logTail hw0 hw1 start len x) (v j x))
      (RCscale (Q'.invSucc start * Q'.invSucc j) (B x x)) := by
  induction len generalizing start with
  | zero =>
      change RCle (B Z (v j x)) _
      rw [completedInner_zero_left]
      exact zero_le_scaled_norm hw0 hw1 _
        (Q'.mul_nonneg _ _ (Q'.invSucc_nonneg start) (Q'.invSucc_nonneg j)) x
  | succ len ih =>
      change RCle
        (B (A (logTerm hw0 hw1 start x)
          (logTail hw0 hw1 (start+1) len x)) (v j x)) _
      rw [completedInner_add_left, logTerm, completedInner_smul_left]
      have hhead := RCscale_mono (Q'.invSucc_nonneg start)
        (positiveTimeTail_pair_bound hw0 hw1 x (start+1) j)
      have htail := ih (start+1)
      have h := RCadd_le_add hhead htail
      rw [RCscale_RCscale, ← scale_add,
        RCSignedPairBudget.scale_congr (recip_step_mul start (Q'.invSucc j))] at h
      exact h

/-- Two finite tails obey the product of their starting reciprocal budgets. -/
theorem logTail_pair_bound (x : V) (a len b len' : Nat) :
    RCle (B (logTail hw0 hw1 a len x) (logTail hw0 hw1 b len' x))
      (RCscale (Q'.invSucc a * Q'.invSucc b) (B x x)) := by
  induction len' generalizing b with
  | zero =>
      change RCle (B (logTail hw0 hw1 a len x) Z) _
      rw [completedInner_zero_right]
      exact zero_le_scaled_norm hw0 hw1 _
        (Q'.mul_nonneg _ _ (Q'.invSucc_nonneg a) (Q'.invSucc_nonneg b)) x
  | succ len' ih =>
      change RCle
        (B (logTail hw0 hw1 a len x)
          (A (logTerm hw0 hw1 b x) (logTail hw0 hw1 (b+1) len' x))) _
      rw [completedInner_add_right, logTerm, completedInner_smul_right]
      have hhead := RCscale_mono (Q'.invSucc_nonneg b)
        (logTail_timeTail_pair_bound hw0 hw1 x a len (b+1))
      have htail := ih (b+1)
      have h := RCadd_le_add hhead htail
      rw [RCscale_RCscale, ← scale_add] at h
      have hcoeff : Q'.eqv
          (Q'.invSucc b * (Q'.invSucc a * Q'.invSucc (b+1)) +
            Q'.invSucc a * Q'.invSucc (b+1))
          (Q'.invSucc a * Q'.invSucc b) := by
        have hcomm : Q'.eqv
            (Q'.invSucc b * (Q'.invSucc a * Q'.invSucc (b+1)) +
              Q'.invSucc a * Q'.invSucc (b+1))
            (Q'.invSucc b * (Q'.invSucc (b+1) * Q'.invSucc a) +
              Q'.invSucc (b+1) * Q'.invSucc a) :=
          YMGap.Continuum.RingNormaliser.poly_identity_of_normal_eq
            (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
              (.mul (.var 1) (.var 2)))
            (.add (.mul (.var 0) (.mul (.var 2) (.var 1)))
              (.mul (.var 2) (.var 1))) (by decide)
            (fun | 0 => Q'.invSucc b | 1 => Q'.invSucc a | _ => Q'.invSucc (b+1))
        exact Q'.eqv_trans _ _ _ hcomm
          (Q'.eqv_trans _ _ _ (recip_step_mul b (Q'.invSucc a))
            (Q'.mul_comm_eqv _ _))
      rw [RCSignedPairBudget.scale_congr hcoeff] at h
      exact h

theorem logTail_norm_bound (x : V) (start len : Nat) :
    RCle (B (logTail hw0 hw1 start len x) (logTail hw0 hw1 start len x))
      (RCscale (Q'.invSucc start * Q'.invSucc start) (B x x)) :=
  logTail_pair_bound hw0 hw1 x start len start len

/-- Concatenating two finite tails uses only the existing vector addition. -/
theorem logTail_split (x : V) (start m n : Nat) :
    logTail hw0 hw1 start (m+n) x =
      A (logTail hw0 hw1 start m x)
        (logTail hw0 hw1 (start+m) n x) := by
  induction m generalizing start with
  | zero =>
      simp only [Nat.zero_add, Nat.add_zero, logTail]
      exact (completedZero_add hw0 hw1 _).symm
  | succ m ih =>
      rw [Nat.succ_add]
      change A (logTerm hw0 hw1 start x)
          (logTail hw0 hw1 (start+1) (m+n) x) =
        A (A (logTerm hw0 hw1 start x)
          (logTail hw0 hw1 (start+1) m x))
          (logTail hw0 hw1 (start+(m+1)) n x)
      have hidx : (start+1)+m = start+(m+1) := by omega
      rw [ih, completedAdd_assoc, hidx]

theorem logPartial_add_tail (x : V) (m n : Nat) :
    logPartial hw0 hw1 (m+n) x =
      A (logPartial hw0 hw1 m x) (logTail hw0 hw1 m n x) := by
  unfold logPartial
  simpa only [Nat.zero_add] using logTail_split hw0 hw1 x 0 m n

private theorem add_sub_cancel (x y : V) :
    completedSub hw0 hw1 (A x y) x = y := by
  unfold completedSub
  rw [completedAdd_comm hw0 hw1 x y, completedAdd_assoc,
    completedAdd_comm hw0 hw1 x, completedNeg_add, completedAdd_zero]

/-- Ordered finite partial sums are Cauchy in the actual completed distance,
with a bound depending only on the earlier cutoff and the original norm. -/
theorem logPartial_ordered_distance_bound (x : V) (m n : Nat) (hmn : m ≤ n) :
    RCle (completedDist hw0 hw1
      (logPartial hw0 hw1 m x) (logPartial hw0 hw1 n x))
      (RCscale (Q'.invSucc m * Q'.invSucc m) (B x x)) := by
  have hs := logPartial_add_tail hw0 hw1 x m (n-m)
  rw [Nat.add_sub_of_le hmn] at hs
  rw [completedDist_symm hw0 hw1 (logPartial hw0 hw1 m x)
    (logPartial hw0 hw1 n x), completedDist, hs, add_sub_cancel]
  exact logTail_norm_bound hw0 hw1 x m (n-m)

#print axioms positiveTimeTail_pair_bound
#print axioms logTerm
#print axioms logTail
#print axioms logPartial
#print axioms logTail_timeTail_pair_bound
#print axioms logTail_pair_bound
#print axioms logTail_norm_bound
#print axioms logTail_split
#print axioms logPartial_add_tail
#print axioms logPartial_ordered_distance_bound

end YMGap.Continuum.BF4WilsonAllNomeLogPartial
