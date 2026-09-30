/-
# Finite time averages on the original all-nome Wilson completion

Finite averages of the actual dyadic mesh action are contractions in the
original completed distance. Their defect average is the normalized actual
multi-step difference. This is algebra on the fixed Wilson carrier only; it
does not assert a generator, physical-time calibration, or Clay closure.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
import YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
import YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar
import YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeTimeAverages

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right rc_telescope)
open YMGap.Continuum.BF4WilsonAllNomeCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics (root)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (mesh_distance_bound)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay (defect time_defect)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "M" => meshAction hw0 hw1

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A'.approx n)))

private theorem scale_zero (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A'.approx n)))

private theorem scale_one (a : RC) : RCscale 1 a = a := by
  refine Quotient.inductionOn a ?_
  intro A'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.one_mul_eqv (A'.approx n)))

private theorem scale_add (a b : Q') (c : RC) :
    RCscale (a+b) c = RCadd (RCscale a c) (RCscale b c) := by
  refine Quotient.inductionOn c ?_
  intro C
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_mul_eqv a b (C.approx n)))

private theorem scale_nat_succ (n : Nat) (a : RC) :
    RCscale (Q'.ofNat (n+1)) a = RCadd (RCscale (Q'.ofNat n) a) a := by
  refine Quotient.inductionOn a ?_
  intro A'
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun j =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv n 1))
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv (A'.approx j))))))

private theorem smul_zero (c : Q') : S c Z = Z := by
  calc
    S c Z = S c (S 0 Z) := congrArg (S c) (completedSmul_zero hw0 hw1 Z).symm
    _ = S (c*0) Z := completedSmul_mul hw0 hw1 c 0 Z
    _ = S 0 Z := completedSmul_congr hw0 hw1 (Q'.mul_zero_eqv c) Z
    _ = Z := completedSmul_zero hw0 hw1 Z

private theorem pairing_common_bound (x y : V) (C : RC)
    (hx : RCle (B x x) C) (hy : RCle (B y y) C) : RCle (B x y) C := by
  have hp := RCadd_le_add (RCle_refl (RCscale 2 (B x y)))
    (completedDist_nonnegative hw0 hw1 x y)
  have hid : RCadd (RCscale 2 (B x y)) (dist x y) = RCadd (B x x) (B y y) := by
    unfold completedDist
    rw [completedInner_sub_left, completedInner_sub_right, completedInner_sub_right,
      completedInner_symm hw0 hw1 y x]
    refine Quotient.inductionOn₃ (B x x) (B x y) (B y y) ?_
    intro Pxx Pxy Pyy
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun j =>
      poly_identity_of_normal_eq
        (.add (.mul (.const 2) (.var 1))
          (.add (.add (.var 0) (.neg (.var 1)))
            (.neg (.add (.var 1) (.neg (.var 2))))))
        (.add (.var 0) (.var 2)) (by decide)
        (fun | 0 => Pxx.approx j | 1 => Pxy.approx j | _ => Pyy.approx j)))
  rw [rc_add_zero, hid] at hp
  have h := RCscale_mono HalfPow.half_nonneg (RCle_trans hp (RCadd_le_add hx hy))
  have twice : RCadd C C = RCscale 2 C := by
    have hsum := scale_add 1 1 C
    simp only [scale_one] at hsum
    exact hsum.symm.trans (scale_congr (by decide : Q'.eqv ((1 : Q')+1) 2) C)
  simp only [twice, RCscale_RCscale,
    scale_congr (by decide : Q'.eqv (HalfPow.half*2) 1), scale_one] at h
  exact h

/-- The finite vector sum, with the same recursion order as the original
completed addition. -/
def vectorSum : Nat → (Nat → V) → V
  | 0, _ => Z
  | n+1, f => A (vectorSum n f) (f n)

theorem sum_add (n : Nat) (f g : Nat → V) :
    vectorSum hw0 hw1 n (fun j => A (f j) (g j)) =
      A (vectorSum hw0 hw1 n f) (vectorSum hw0 hw1 n g) := by
  induction n with
  | zero => exact (completedZero_add hw0 hw1 Z).symm
  | succ n ih =>
      simp only [vectorSum, ih]
      rw [completedAdd_assoc,
        ← completedAdd_assoc hw0 hw1 (vectorSum hw0 hw1 n g) (f n) (g n),
        completedAdd_comm hw0 hw1 (vectorSum hw0 hw1 n g) (f n),
        completedAdd_assoc, ← completedAdd_assoc]

theorem sum_smul (n : Nat) (c : Q') (f : Nat → V) :
    vectorSum hw0 hw1 n (fun j => S c (f j)) = S c (vectorSum hw0 hw1 n f) := by
  induction n with
  | zero => exact (smul_zero hw0 hw1 c).symm
  | succ n ih =>
      rw [vectorSum, vectorSum, ih, completedSmul_add]

theorem sum_sub (n : Nat) (f g : Nat → V) :
    vectorSum hw0 hw1 n (fun j => Sub (f j) (g j)) =
      Sub (vectorSum hw0 hw1 n f) (vectorSum hw0 hw1 n g) := by
  unfold completedSub completedNeg
  rw [sum_add, sum_smul]

theorem sum_const (n : Nat) (x : V) :
    vectorSum hw0 hw1 n (fun _ => x) = S (Q'.ofNat n) x := by
  induction n with
  | zero =>
      exact ((completedSmul_congr hw0 hw1 Q'.ofNat_zero_eqv x).trans
        (completedSmul_zero hw0 hw1 x)).symm
  | succ n ih =>
      rw [vectorSum, ih]
      exact (congrArg (A (S (Q'.ofNat n) x)) (completedSmul_one hw0 hw1 x).symm).trans
        ((completedAdd_smul hw0 hw1 (Q'.ofNat n) 1 x).trans
          (completedSmul_congr hw0 hw1 (Q'.eqv_symm (Q'.ofNat_add_eqv n 1)) x))

theorem sum_pair_right_bound (n : Nat) (x : V) (f : Nat → V) (C : RC)
    (h : ∀ j, j<n → RCle (B x (f j)) C) :
    RCle (B x (vectorSum hw0 hw1 n f)) (RCscale (Q'.ofNat n) C) := by
  induction n with
  | zero =>
      rw [vectorSum, completedInner_zero_right,
        scale_congr (by decide : Q'.eqv (Q'.ofNat 0) 0), scale_zero]
      exact RCle_refl _
  | succ n ih =>
      rw [vectorSum, completedInner_add_right, scale_nat_succ]
      exact RCadd_le_add (ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n)))
        ) (h n (Nat.lt_succ_self n))

theorem sum_pair_bound (m n : Nat) (f g : Nat → V) (C : RC)
    (h : ∀ i, i<m → ∀ j, j<n → RCle (B (f i) (g j)) C) :
    RCle (B (vectorSum hw0 hw1 m f) (vectorSum hw0 hw1 n g))
      (RCscale (Q'.ofNat m*Q'.ofNat n) C) := by
  have h' := sum_pair_right_bound hw0 hw1 m (vectorSum hw0 hw1 n g) f
    (RCscale (Q'.ofNat n) C) (by
      intro i hi
      rw [completedInner_symm hw0 hw1]
      exact sum_pair_right_bound hw0 hw1 n (f i) g C (h i hi))
  rw [completedInner_symm hw0 hw1, RCscale_RCscale] at h'
  exact h'

theorem sum_norm_bound (n : Nat) (f : Nat → V) (C : RC)
    (h : ∀ j, j<n → RCle (B (f j) (f j)) C) :
    RCle (B (vectorSum hw0 hw1 n f) (vectorSum hw0 hw1 n f))
      (RCscale (Q'.ofNat n*Q'.ofNat n) C) :=
  sum_pair_bound hw0 hw1 n n f f C
    (fun i hi j hj => pairing_common_bound hw0 hw1 _ _ C (h i hi) (h j hj))

/-- The mean of the first n+1 vectors. -/
def average (n : Nat) (f : Nat → V) : V :=
  S (Q'.invSucc n) (vectorSum hw0 hw1 (n+1) f)

theorem inv_count (n : Nat) : Q'.eqv (Q'.invSucc n*Q'.ofNat (n+1)) 1 :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.ofNat_succ_mul_invSucc n)

theorem average_const (n : Nat) (x : V) : average hw0 hw1 n (fun _ => x) = x := by
  unfold average
  rw [sum_const, completedSmul_mul, completedSmul_congr hw0 hw1 (inv_count n),
    completedSmul_one]

/-- Scalar multiplication distributes over the completed difference. -/
theorem smul_sub (c : Q') (x y : V) :
    S c (Sub x y) = Sub (S c x) (S c y) := by
  unfold completedSub completedNeg
  rw [completedSmul_add, completedSmul_mul, completedSmul_mul]
  exact congrArg (A (S c x))
    (completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv c (-1)) y)

theorem average_sub (n : Nat) (f g : Nat → V) :
    average hw0 hw1 n (fun j => Sub (f j) (g j)) =
      Sub (average hw0 hw1 n f) (average hw0 hw1 n g) := by
  unfold average
  rw [sum_sub, smul_sub]

theorem average_smul (n : Nat) (c : Q') (f : Nat → V) :
    average hw0 hw1 n (fun j => S c (f j)) =
      S c (average hw0 hw1 n f) := by
  unfold average
  rw [sum_smul, completedSmul_mul, completedSmul_mul]
  exact completedSmul_congr hw0 hw1 (Q'.mul_comm_eqv _ _) _

theorem average_norm_bound (n : Nat) (f : Nat → V) (C : RC)
    (h : ∀ j, j<n+1 → RCle (B (f j) (f j)) C) :
    RCle (B (average hw0 hw1 n f) (average hw0 hw1 n f)) C := by
  have hb := RCscale_mono (SumOfSquares.q_mul_self_nonneg (Q'.invSucc n))
    (sum_norm_bound hw0 hw1 (n+1) f C h)
  have hcoeff : Q'.eqv
      ((Q'.invSucc n*Q'.invSucc n)*(Q'.ofNat (n+1)*Q'.ofNat (n+1))) 1 := by
    have hr : Q'.eqv
        ((Q'.invSucc n*Q'.invSucc n)*(Q'.ofNat (n+1)*Q'.ofNat (n+1)))
        ((Q'.invSucc n*Q'.ofNat (n+1))*(Q'.invSucc n*Q'.ofNat (n+1))) :=
      poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (by decide)
        (fun | 0 => Q'.invSucc n | _ => Q'.ofNat (n+1))
    exact Q'.eqv_trans _ _ _ hr
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (inv_count n))
        (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (inv_count n)))
  rw [RCscale_RCscale, scale_congr hcoeff, RCscale_one] at hb
  unfold average
  rw [completedInner_smul_left, completedInner_smul_right, RCscale_RCscale]
  exact hb

theorem average_distance_bound (n : Nat) (f g : Nat → V) (C : RC)
    (h : ∀ j, j<n+1 → RCle (dist (f j) (g j)) C) :
    RCle (dist (average hw0 hw1 n f) (average hw0 hw1 n g)) C := by
  unfold completedDist
  rw [← average_sub]
  exact average_norm_bound hw0 hw1 n _ C h

/-- Average the first n+1 steps of the actual dyadic Wilson mesh action. -/
def timeAverage (depth n : Nat) (x : V) : V :=
  average hw0 hw1 n (fun j => meshAction hw0 hw1 depth j x)

theorem timeAverage_contraction (depth n : Nat) (x y : V) :
    RCle (dist (timeAverage hw0 hw1 depth n x) (timeAverage hw0 hw1 depth n y))
      (dist x y) :=
  average_distance_bound hw0 hw1 n _ _ _ (fun j _ =>
    mesh_distance_bound hw0 hw1 depth j x y)

theorem timeAverage_close (depth n : Nat) (x : V) (bound : RC)
    (h : ∀ j, j<n+1 → RCle (dist (meshAction hw0 hw1 depth j x) x) bound) :
    RCle (dist (timeAverage hw0 hw1 depth n x) x) bound := by
  have hb := average_distance_bound hw0 hw1 n
    (fun j => meshAction hw0 hw1 depth j x) (fun _ => x) bound h
  rw [average_const] at hb
  exact hb

private theorem mesh_defect_increment (depth j : Nat) (x : V) :
    defect hw0 hw1 depth (meshAction hw0 hw1 depth j x) =
      completedSub hw0 hw1 (meshAction hw0 hw1 depth j x)
        (meshAction hw0 hw1 depth (j+1) x) := rfl

private theorem sub_telescope (x y z : V) :
    A (Sub x y) (Sub y z) = Sub x z := by
  apply completed_eq_of_pairings hw0 hw1
  intro v
  rw [completedInner_add_left, completedInner_sub_left,
    completedInner_sub_left, completedInner_sub_left]
  exact rc_telescope _ _ _

theorem sum_defect (depth n : Nat) (x : V) :
    vectorSum hw0 hw1 n (fun j => meshAction hw0 hw1 depth j (defect hw0 hw1 depth x)) =
      Sub x (meshAction hw0 hw1 depth n x) := by
  induction n with
  | zero => exact (completedSub_self hw0 hw1 x).symm
  | succ n ih =>
      rw [vectorSum, ih, time_defect, mesh_defect_increment]
      exact sub_telescope hw0 hw1 x (meshAction hw0 hw1 depth n x)
        (meshAction hw0 hw1 depth (n+1) x)

/-- The averaged dyadic defect telescopes to the normalized actual time
difference on the same original carrier. -/
theorem timeAverage_defect (depth n : Nat) (x : V) :
    timeAverage hw0 hw1 depth n (defect hw0 hw1 depth x) =
      S (Q'.invSucc n) (Sub x (meshAction hw0 hw1 depth (n+1) x)) := by
  unfold timeAverage average
  rw [sum_defect]

#print axioms vectorSum
#print axioms sum_add
#print axioms sum_smul
#print axioms sum_sub
#print axioms sum_const
#print axioms sum_pair_right_bound
#print axioms sum_pair_bound
#print axioms sum_norm_bound
#print axioms average
#print axioms inv_count
#print axioms average_const
#print axioms smul_sub
#print axioms average_sub
#print axioms average_smul
#print axioms average_norm_bound
#print axioms average_distance_bound
#print axioms timeAverage
#print axioms timeAverage_contraction
#print axioms timeAverage_close
#print axioms sum_defect
#print axioms timeAverage_defect

end YMGap.Continuum.BF4WilsonAllNomeTimeAverages
