/-
# Higher dyadic smoothing on the SAME original Wilson completion

For the actual root R_depth and its defect D_depth=I-R_depth, a finer
positive root proves positivity of every mixed moment B(x,R^k D^l x).
Its exact split gives an iterated finite weighted telescope, hence
  n^(2*r) ||R^(r*n) D^r x||^2 <= ||x||^2.
This is the quantitative input to constructing actual dyadic derivatives.
No spectral representation, log-series identity, generator domain, physical
calibration, spatial/scaling estimate or Clay conclusion is assumed.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.SU3CharFactor (ofNat_nonneg)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity
  (completedInner_sub_left completedInner_sub_right)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootBasics
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "R" => root hw0 hw1
local notation "S" => meshAction hw0 hw1

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem add_assoc (a b c : RC) : RCadd (RCadd a b) c = RCadd a (RCadd b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B' C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_assoc_eqv (A.approx n) (B'.approx n) (C.approx n)))

private theorem add_comm (a b : RC) : RCadd a b = RCadd b a := by
  refine Quotient.inductionOn₂ a b ?_
  exact fun A B' => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_comm_eqv (A.approx n) (B'.approx n)))

private theorem scale_zero (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.zero_mul_eqv (A.approx n)))

private theorem sub_nonnegative {a b : RC} (h : RCle b a) : RCnonneg (RCsub a b) := by
  have h' := RCadd_le_add h (RCle_refl (RCneg b))
  have hz : RCsub b b = RCzero := by
    refine Quotient.inductionOn b ?_
    exact fun B' => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.add_neg_self_eqv (B'.approx n)))
  change RCle (RCsub b b) (RCsub a b) at h'
  rwa [hz] at h'

private theorem scale_nat_succ (n : Nat) (a : RC) :
    RCscale (Q'.ofNat (n+1)) a = RCadd (RCscale (Q'.ofNat n) a) a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun j =>
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv n 1))
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv (A.approx j))))))

private theorem sub_add_cancel (x y : V) :
    completedAdd hw0 hw1 (completedSub hw0 hw1 x y) y = x := by
  unfold completedSub
  rw [completedAdd_assoc,completedNeg_add,completedAdd_zero]

theorem mesh_add_state (depth steps : Nat) (x y : V) :
    S depth steps (completedAdd hw0 hw1 x y) =
      completedAdd hw0 hw1 (S depth steps x) (S depth steps y) :=
  action_add_state hw0 hw1 (NonnegativeDyadicTime.embed ⟨depth,steps⟩) x y

theorem mesh_sub (depth steps : Nat) (x y : V) :
    S depth steps (completedSub hw0 hw1 x y) =
      completedSub hw0 hw1 (S depth steps x) (S depth steps y) :=
  action_sub hw0 hw1 (NonnegativeDyadicTime.embed ⟨depth,steps⟩) x y

def defect (depth : Nat) (x : V) : V := completedSub hw0 hw1 x (R depth x)

theorem defect_symmetric (depth : Nat) (x y : V) :
    B (defect hw0 hw1 depth x) y = B x (defect hw0 hw1 depth y) := by
  unfold defect
  rw [completedInner_sub_left,completedInner_sub_right,root_symmetric]

theorem defect_positive (depth : Nat) (x : V) :
    RCnonneg (B x (defect hw0 hw1 depth x)) := by
  unfold defect
  rw [completedInner_sub_right]
  apply sub_nonnegative
  rw [← root_pairing]
  exact root_norm_bound hw0 hw1 (depth+1) x

theorem mesh_generator_commutes (mesh steps depth : Nat) (x : V) :
    S mesh steps (R depth x) = R depth (S mesh steps x) := by
  change action hw0 hw1 (NonnegativeDyadicTime.embed ⟨mesh,steps⟩)
      (action hw0 hw1 (NonnegativeDyadicTime.embed ⟨depth,1⟩) x) =
    action hw0 hw1 (NonnegativeDyadicTime.embed ⟨depth,1⟩)
      (action hw0 hw1 (NonnegativeDyadicTime.embed ⟨mesh,steps⟩) x)
  rw [← action_add,← action_add,NonnegativeDyadicTime.add_comm]

theorem time_defect (mesh steps depth : Nat) (x : V) :
    S mesh steps (defect hw0 hw1 depth x) = defect hw0 hw1 depth (S mesh steps x) := by
  unfold defect
  rw [mesh_sub,mesh_generator_commutes]

def defectPower (depth : Nat) : Nat → V → V
  | 0,x => x
  | n+1,x => defect hw0 hw1 depth (defectPower depth n x)

theorem defectPower_defect (depth n : Nat) (x : V) :
    defectPower hw0 hw1 depth n (defect hw0 hw1 depth x) =
      defect hw0 hw1 depth (defectPower hw0 hw1 depth n x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (defect hw0 hw1 depth) ih

theorem defectPower_add (depth m n : Nat) (x : V) :
    defectPower hw0 hw1 depth (m+n) x =
      defectPower hw0 hw1 depth m (defectPower hw0 hw1 depth n x) := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih => rw [Nat.succ_add,defectPower,defectPower,ih]

theorem defectPower_symmetric (depth n : Nat) (x y : V) :
    B (defectPower hw0 hw1 depth n x) y = B x (defectPower hw0 hw1 depth n y) := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
      change B (defect hw0 hw1 depth (defectPower hw0 hw1 depth n x)) y =
        B x (defect hw0 hw1 depth (defectPower hw0 hw1 depth n y))
      rw [defect_symmetric,ih,defectPower_defect]

theorem defectPower_positive (depth : Nat) : ∀ n, ∀ x : V,
    RCnonneg (B x (defectPower hw0 hw1 depth n x))
  | 0,x => completedInner_nonnegative hw0 hw1 x
  | 1,x => defect_positive hw0 hw1 depth x
  | n+2,x => by
      change RCnonneg (B x (defect hw0 hw1 depth
        (defect hw0 hw1 depth (defectPower hw0 hw1 depth n x))))
      rw [← defect_symmetric,← defectPower_defect]
      exact defectPower_positive depth n (defect hw0 hw1 depth x)

theorem time_defectPower (mesh steps depth n : Nat) (x : V) :
    S mesh steps (defectPower hw0 hw1 depth n x) =
      defectPower hw0 hw1 depth n (S mesh steps x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change S mesh steps (defect hw0 hw1 depth (defectPower hw0 hw1 depth n x)) =
        defect hw0 hw1 depth (defectPower hw0 hw1 depth n (S mesh steps x))
      rw [time_defect,ih]

def moment (depth : Nat) (x : V) (k l : Nat) : RC :=
  B x (S depth k (defectPower hw0 hw1 depth l x))

theorem moment_halfTime (depth : Nat) (x : V) (k l : Nat) :
    moment hw0 hw1 depth x k l =
      B (S (depth+1) k x) (defectPower hw0 hw1 depth l (S (depth+1) k x)) := by
  unfold moment
  rw [← mesh_double hw0 hw1 depth k,mesh_add,← mesh_symmetric,time_defectPower]

theorem moment_nonnegative (depth : Nat) (x : V) (k l : Nat) :
    RCnonneg (moment hw0 hw1 depth x k l) := by
  rw [moment_halfTime]
  exact defectPower_positive hw0 hw1 depth l (S (depth+1) k x)

theorem moment_zero (depth : Nat) (x : V) : moment hw0 hw1 depth x 0 0 = B x x := rfl

theorem moment_split (depth : Nat) (x : V) (k l : Nat) :
    moment hw0 hw1 depth x k l = RCadd (moment hw0 hw1 depth x (k+1) l)
      (moment hw0 hw1 depth x k (l+1)) := by
  have h := sub_add_cancel hw0 hw1 (defectPower hw0 hw1 depth l x)
    (R depth (defectPower hw0 hw1 depth l x))
  change completedAdd hw0 hw1 (defectPower hw0 hw1 depth (l+1) x)
    (R depth (defectPower hw0 hw1 depth l x)) = defectPower hw0 hw1 depth l x at h
  rw [completedAdd_comm] at h
  have ht := congrArg (fun y => B x (S depth k y)) h
  dsimp only at ht
  rw [mesh_add_state,completedInner_add_right,mesh_generator_commutes] at ht
  exact ht.symm

theorem moment_time_decreases (depth : Nat) (x : V) (k l : Nat) :
    RCle (moment hw0 hw1 depth x (k+1) l) (moment hw0 hw1 depth x k l) := by
  have h := RCadd_le_add (RCle_refl (moment hw0 hw1 depth x (k+1) l))
    (moment_nonnegative hw0 hw1 depth x k (l+1))
  rw [add_zero,← moment_split] at h
  exact h

/-- The retained terminal moment makes the finite estimate iterable. -/
theorem weighted_terminal (depth : Nat) (x : V) (k l n : Nat) :
    RCle (RCadd (RCscale (Q'.ofNat n) (moment hw0 hw1 depth x (k+n) (l+1)))
      (moment hw0 hw1 depth x (k+n) l)) (moment hw0 hw1 depth x k l) := by
  induction n with
  | zero =>
      rw [Nat.add_zero,scale_congr (by decide : Q'.eqv (Q'.ofNat 0) 0),scale_zero,zero_add]
      exact RCle_refl _
  | succ n ih =>
      have h := RCle_trans (RCadd_le_add
        (RCscale_mono (ofNat_nonneg n) (moment_time_decreases hw0 hw1 depth x (k+n) (l+1)))
        (RCle_refl (moment hw0 hw1 depth x (k+n) l))) ih
      rw [moment_split hw0 hw1 depth x (k+n) l,
        add_comm (moment hw0 hw1 depth x (k+n+1) l),← add_assoc] at h
      have h' := RCle_trans (RCadd_le_add (RCadd_le_add (RCle_refl _)
        (moment_time_decreases hw0 hw1 depth x (k+n) (l+1))) (RCle_refl _)) h
      rw [← scale_nat_succ] at h'
      simpa only [Nat.add_assoc] using h'

theorem weighted_step (depth : Nat) (x : V) (k l n : Nat) :
    RCle (RCscale (Q'.ofNat n) (moment hw0 hw1 depth x (k+n) (l+1)))
      (moment hw0 hw1 depth x k l) := by
  have h := RCadd_le_add
    (RCle_refl (RCscale (Q'.ofNat n) (moment hw0 hw1 depth x (k+n) (l+1))))
    (moment_nonnegative hw0 hw1 depth x (k+n) l)
  rw [add_zero] at h
  exact RCle_trans h (weighted_terminal hw0 hw1 depth x k l n)

theorem weighted_order (depth : Nat) (x : V) (k l n r : Nat) :
    RCle (RCscale ((Q'.ofNat n)^r) (moment hw0 hw1 depth x (k+r*n) (l+r)))
      (moment hw0 hw1 depth x k l) := by
  induction r with
  | zero =>
      change RCle (RCscale 1 (moment hw0 hw1 depth x (k+0*n) (l+0))) _
      rw [Nat.zero_mul,Nat.add_zero,RCscale_one]
      exact RCle_refl _
  | succ r ih =>
      have h := RCle_trans (RCscale_mono (Q'.pow_nonneg _ (ofNat_nonneg n) r)
        (weighted_step hw0 hw1 depth x (k+r*n) (l+r) n)) ih
      rw [RCscale_RCscale,scale_congr (Q'.mul_comm_eqv ((Q'.ofNat n)^r) (Q'.ofNat n))] at h
      simpa only [Nat.succ_mul,Nat.add_assoc] using h

theorem moment_square (depth : Nat) (x : V) (n r : Nat) :
    moment hw0 hw1 depth x (n+n) (r+r) =
      B (S depth n (defectPower hw0 hw1 depth r x))
        (S depth n (defectPower hw0 hw1 depth r x)) := by
  unfold moment
  rw [defectPower_add,time_defectPower,← defectPower_symmetric,
    mesh_add,← mesh_symmetric]

/-- Higher differences decay on actual mesh-time images, at every finite order. -/
theorem smoothing_bound (depth n r : Nat) (x : V) :
    RCle (RCscale ((Q'.ofNat n)^(r+r))
      (B (S depth (r*n) (defectPower hw0 hw1 depth r x))
        (S depth (r*n) (defectPower hw0 hw1 depth r x)))) (B x x) := by
  have h := weighted_order hw0 hw1 depth x 0 0 n (r+r)
  rw [Nat.zero_add,Nat.zero_add,Nat.add_mul,moment_square,moment_zero] at h
  exact h

#print axioms mesh_add_state
#print axioms mesh_sub
#print axioms defect
#print axioms defect_symmetric
#print axioms defect_positive
#print axioms mesh_generator_commutes
#print axioms time_defect
#print axioms defectPower
#print axioms defectPower_defect
#print axioms defectPower_add
#print axioms defectPower_symmetric
#print axioms defectPower_positive
#print axioms time_defectPower
#print axioms moment
#print axioms moment_halfTime
#print axioms moment_nonnegative
#print axioms moment_zero
#print axioms moment_split
#print axioms moment_time_decreases
#print axioms weighted_terminal
#print axioms weighted_step
#print axioms weighted_order
#print axioms moment_square
#print axioms smoothing_bound

end YMGap.Continuum.BF4WilsonAllNomeDyadicDefectDecay
