/-
# Finite time averages on the ORIGINAL completion

Finite averages preserve a common squared-norm bound, with no factor
depending on the number of summands. Applied to the existing dyadic
semigroup they are contractions, preserve constants, and telescope its
one-step defect to the actual multi-step difference. These estimates
support differentiation at general positive increments; they do not
assert a generator, self-adjointness, physical scaling or the Clay target.
All operators and pairings remain the original fixed-nome SU(2) ones.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative

namespace YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
  (completedInner_sub_left completedInner_sub_right completedSub_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPairingContinuity (rc_telescope)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords (scale_nat_succ)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_zero scale_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (rc_add_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference (add_regroup smul_zero_state)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity (smul_norm)
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicLinear (sub_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (time_sub)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay (defect time_defect)

local notation "B" => completedInner

theorem pairing_common_bound (x y : Completion) (C : RC)
    (hx : RCle (B x x) C) (hy : RCle (B y y) C) : RCle (B x y) C := by
  have hp := RCadd_le_add (RCle_refl (RCscale 2 (B x y))) (completedDist_nonnegative x y)
  have hid : RCadd (RCscale 2 (B x y)) (completedDist x y)=RCadd (B x x) (B y y) := by
    unfold completedDist
    rw [completedInner_sub_left,completedInner_sub_right,completedInner_sub_right,completedInner_symm y x]
    refine Quotient.inductionOn₃ (B x x) (B x y) (B y y) ?_
    intro A D E
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun j =>
      poly_identity_of_normal_eq
        (.add (.mul (.const 2) (.var 1))
          (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 1) (.neg (.var 2))))))
        (.add (.var 0) (.var 2)) (by decide)
        (fun | 0 => A.approx j | 1 => D.approx j | _ => E.approx j)))
  rw [rc_add_zero,hid] at hp
  have h := RCscale_mono HalfPow.half_nonneg (RCle_trans hp (RCadd_le_add hx hy))
  have twice : RCadd C C=RCscale 2 C := by
    have hsum := scale_add 1 1 C
    simp only [RCscale_one] at hsum
    exact hsum.symm.trans (scale_congr (by decide : Q'.eqv ((1 : Q')+1) 2) C)
  simp only [twice,RCscale_RCscale,
    scale_congr (by decide : Q'.eqv (HalfPow.half*2) 1),RCscale_one] at h
  exact h

def vectorSum : Nat → (Nat → Completion) → Completion
  | 0,_ => completedZero
  | n+1,f => completedAdd (vectorSum n f) (f n)

theorem sum_add (n : Nat) (f g : Nat → Completion) :
    vectorSum n (fun j => completedAdd (f j) (g j))=completedAdd (vectorSum n f) (vectorSum n g) := by
  induction n with
  | zero => exact (completedZero_add completedZero).symm
  | succ n ih => simp only [vectorSum,ih]; exact add_regroup _ _ _ _

theorem sum_smul (n : Nat) (c : Q') (f : Nat → Completion) :
    vectorSum n (fun j => completedSmul c (f j))=completedSmul c (vectorSum n f) := by
  induction n with
  | zero => exact (smul_zero_state c).symm
  | succ n ih => rw [vectorSum,vectorSum,ih,completedSmul_add]

theorem sum_sub (n : Nat) (f g : Nat → Completion) :
    vectorSum n (fun j => completedSub (f j) (g j))=completedSub (vectorSum n f) (vectorSum n g) := by
  unfold completedSub completedNeg
  rw [sum_add,sum_smul]

theorem sum_const (n : Nat) (x : Completion) :
    vectorSum n (fun _ => x)=completedSmul (Q'.ofNat n) x := by
  induction n with
  | zero => exact (completedSmul_zero x).symm
  | succ n ih =>
      rw [vectorSum,ih]
      exact (congrArg (completedAdd (completedSmul (Q'.ofNat n) x)) (completedSmul_one x).symm).trans
        ((completedAdd_smul (Q'.ofNat n) 1 x).trans
          (completedSmul_congr (Q'.eqv_symm (Q'.ofNat_add_eqv n 1)) x))

theorem sum_pair_right_bound (n : Nat) (x : Completion) (f : Nat → Completion) (C : RC)
    (h : ∀ j,j<n → RCle (B x (f j)) C) :
    RCle (B x (vectorSum n f)) (RCscale (Q'.ofNat n) C) := by
  induction n with
  | zero =>
      rw [vectorSum,completedInner_zero_right,scale_congr (by decide : Q'.eqv (Q'.ofNat 0) 0),scale_zero]
      exact RCle_refl _
  | succ n ih =>
      rw [vectorSum,completedInner_add_right,scale_nat_succ]
      exact RCadd_le_add (ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n))))
        (h n (Nat.lt_succ_self n))

theorem sum_pair_bound (m n : Nat) (f g : Nat → Completion) (C : RC)
    (h : ∀ i,i<m → ∀ j,j<n → RCle (B (f i) (g j)) C) :
    RCle (B (vectorSum m f) (vectorSum n g)) (RCscale (Q'.ofNat m*Q'.ofNat n) C) := by
  have h' := sum_pair_right_bound m (vectorSum n g) f (RCscale (Q'.ofNat n) C) (by
    intro i hi
    rw [completedInner_symm]
    exact sum_pair_right_bound n (f i) g C (h i hi))
  rw [completedInner_symm,RCscale_RCscale] at h'
  exact h'

theorem sum_norm_bound (n : Nat) (f : Nat → Completion) (C : RC)
    (h : ∀ j,j<n → RCle (B (f j) (f j)) C) :
    RCle (B (vectorSum n f) (vectorSum n f)) (RCscale (Q'.ofNat n*Q'.ofNat n) C) :=
  sum_pair_bound n n f f C (fun i hi j hj => pairing_common_bound _ _ C (h i hi) (h j hj))

def average (n : Nat) (f : Nat → Completion) : Completion :=
  completedSmul (Q'.invSucc n) (vectorSum (n+1) f)

theorem inv_count (n : Nat) : Q'.eqv (Q'.invSucc n*Q'.ofNat (n+1)) 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.ofNat_succ_mul_invSucc n)

theorem average_const (n : Nat) (x : Completion) : average n (fun _ => x)=x := by
  unfold average
  rw [sum_const,completedSmul_mul,completedSmul_congr (inv_count n),completedSmul_one]

theorem smul_sub (c : Q') (x y : Completion) :
    completedSmul c (completedSub x y)=completedSub (completedSmul c x) (completedSmul c y) := by
  unfold completedSub completedNeg
  rw [completedSmul_add,completedSmul_mul,completedSmul_mul]
  exact congrArg (completedAdd (completedSmul c x)) (completedSmul_congr (Q'.mul_comm_eqv c (-1)) y)

theorem average_sub (n : Nat) (f g : Nat → Completion) :
    average n (fun j => completedSub (f j) (g j))=completedSub (average n f) (average n g) := by
  unfold average
  rw [sum_sub,smul_sub]

theorem average_smul (n : Nat) (c : Q') (f : Nat → Completion) :
    average n (fun j => completedSmul c (f j))=completedSmul c (average n f) := by
  unfold average
  rw [sum_smul,completedSmul_mul,completedSmul_mul]
  exact completedSmul_congr (Q'.mul_comm_eqv _ _) _

/-- No length factor survives normalization. -/
theorem average_norm_bound (n : Nat) (f : Nat → Completion) (C : RC)
    (h : ∀ j,j<n+1 → RCle (B (f j) (f j)) C) : RCle (B (average n f) (average n f)) C := by
  have hb := RCscale_mono (SumOfSquares.q_mul_self_nonneg (Q'.invSucc n)) (sum_norm_bound (n+1) f C h)
  have hcoeff : Q'.eqv ((Q'.invSucc n*Q'.invSucc n)*(Q'.ofNat (n+1)*Q'.ofNat (n+1))) 1 := by
    have hr : Q'.eqv ((Q'.invSucc n*Q'.invSucc n)*(Q'.ofNat (n+1)*Q'.ofNat (n+1)))
        ((Q'.invSucc n*Q'.ofNat (n+1))*(Q'.invSucc n*Q'.ofNat (n+1))) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (by decide)
        (fun | 0 => Q'.invSucc n | _ => Q'.ofNat (n+1))
    exact Q'.eqv_trans _ _ _ hr (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (inv_count n))
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (inv_count n)))
  rw [RCscale_RCscale,scale_congr hcoeff,RCscale_one] at hb
  unfold average
  rw [smul_norm]
  exact hb

theorem average_distance_bound (n : Nat) (f g : Nat → Completion) (C : RC)
    (h : ∀ j,j<n+1 → RCle (completedDist (f j) (g j)) C) :
    RCle (completedDist (average n f) (average n g)) C := by
  unfold completedDist
  rw [← average_sub]
  exact average_norm_bound n _ C h

def timeAverage (depth n : Nat) (x : Completion) : Completion := average n (fun j => time depth j x)

theorem timeAverage_contraction (depth n : Nat) (x y : Completion) :
    RCle (completedDist (timeAverage depth n x) (timeAverage depth n y)) (completedDist x y) :=
  average_distance_bound n _ _ _ (fun j _ =>
    BF4ExactSlabThermodynamicDyadicEnergy.time_distance_contraction depth j x y)

theorem timeAverage_close (depth n : Nat) (x : Completion) (C : RC)
    (h : ∀ j,j<n+1 → RCle (completedDist (time depth j x) x) C) :
    RCle (completedDist (timeAverage depth n x) x) C := by
  have hb := average_distance_bound n (fun j => time depth j x) (fun _ => x) C h
  rw [average_const] at hb
  exact hb

theorem sub_telescope (x y z : Completion) :
    completedAdd (completedSub x y) (completedSub y z)=completedSub x z := by
  apply completed_eq_of_pairings
  intro w
  rw [completedInner_add_left,completedInner_sub_left,completedInner_sub_left,completedInner_sub_left]
  exact rc_telescope _ _ _

theorem sum_defect (depth n : Nat) (x : Completion) :
    vectorSum n (fun j => time depth j (defect depth x))=completedSub x (time depth n x) := by
  induction n with
  | zero => exact (completedSub_self x).symm
  | succ n ih =>
      rw [vectorSum,ih,time_defect]
      exact sub_telescope x (time depth n x) (time depth (n+1) x)

/-- The average is exactly the normalized actual multi-step difference. -/
theorem timeAverage_defect (depth n : Nat) (x : Completion) :
    timeAverage depth n (defect depth x)=
      completedSmul (Q'.invSucc n) (completedSub x (time depth (n+1) x)) := by
  unfold timeAverage average
  rw [sum_defect]

end YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.pairing_common_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.vectorSum
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.sum_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.sum_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.sum_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.sum_const
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.sum_pair_right_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.sum_pair_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.sum_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.average
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.inv_count
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.average_const
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.smul_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.average_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.average_smul
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.average_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.average_distance_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.timeAverage
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.timeAverage_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.timeAverage_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.sub_telescope
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.sum_defect
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages.timeAverage_defect
