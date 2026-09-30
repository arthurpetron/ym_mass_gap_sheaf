/-
# Small dyadic increments on the ORIGINAL positive-time range

The finer square root gives the energy inequality
  ||Ax-x||^2 + ||Ax||^2 <= ||x||^2.
Decreasing adjacent increments and one finite telescope then control EVERY
small dyadic time on an original positive-time image. The leftover time is
natural subtraction, not an inverse transfer. One whole unit is original T(1).

These are same-carrier, preimage-norm bounds, not uniform physical mass or
scaling estimates. No density of the time range, deletion of its boundary
kernel, full-carrier zero-time continuity or generator identity is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
import YMGap.Continuum.RCSignedPairBudget

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCompletedPairingContinuity (completedInner_sub_left)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
open YMGap.Continuum.RCSignedPairBudget (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "d" => completedDist hw0 hw1
local notation "S" => meshAction hw0 hw1
local notation "T" => completedTime hw0 hw1

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem add_assoc (a b c : RC) : RCadd (RCadd a b) c = RCadd a (RCadd b c) := by
  refine Quotient.inductionOn₃ a b c ?_
  exact fun A B' C => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_assoc_eqv (A.approx n) (B'.approx n) (C.approx n)))

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

theorem mesh_distance_bound (depth steps : Nat) (x y : V) :
    RCle (d (S depth steps x) (S depth steps y)) (d x y) :=
  action_distance_bound hw0 hw1 (NonnegativeDyadicTime.embed ⟨depth,steps⟩) x y

theorem mesh_commutes (depth m n : Nat) (x : V) :
    S depth m (S depth n x) = S depth n (S depth m x) := by
  rw [← mesh_add,← mesh_add,Nat.add_comm m n]

theorem mesh_form_dominates_norm (depth steps : Nat) (x : V) :
    RCle (B (S depth steps x) (S depth steps x)) (B (S depth steps x) x) := by
  have h := mesh_norm_bound hw0 hw1 (depth+1) steps (S (depth+1) steps x)
  rw [← mesh_add,mesh_double] at h
  have hp : B (S depth steps x) x = B (S (depth+1) steps x) (S (depth+1) steps x) := by
    rw [← mesh_double hw0 hw1 depth steps x,mesh_add,mesh_symmetric]
  rwa [← hp] at h

/-- One increment is paid by the actual loss of original squared norm. -/
theorem mesh_dissipation (depth steps : Nat) (x : V) :
    RCle (RCadd (d (S depth steps x) x) (B (S depth steps x) (S depth steps x))) (B x x) := by
  let y := S depth steps x
  let z := completedSub hw0 hw1 x y
  have hc : RCnonneg (B z y) := by
    change RCnonneg (B (completedSub hw0 hw1 x y) y)
    rw [completedInner_sub_left,completedInner_symm hw0 hw1 x y]
    exact sub_nonnegative (mesh_form_dominates_norm hw0 hw1 depth steps x)
  have hc' : RCnonneg (B y z) := by rw [completedInner_symm]; exact hc
  have h := RCadd_le_add (RCadd_le_add (RCle_refl (B z z)) hc)
    (RCadd_le_add hc' (RCle_refl (B y y)))
  rw [add_zero,zero_add,← completedInner_add_right,
    ← completedInner_add_right,← completedInner_add_left] at h
  change RCle (RCadd (d x y) (B y y))
    (B (completedAdd hw0 hw1 (completedSub hw0 hw1 x y) y)
      (completedAdd hw0 hw1 (completedSub hw0 hw1 x y) y)) at h
  rw [sub_add_cancel,completedDist_symm hw0 hw1 x y] at h
  exact h

def block (depth steps n : Nat) (x : V) : V := S depth (steps*n) x

theorem block_zero (depth steps : Nat) (x : V) : block hw0 hw1 depth steps 0 x = x := by
  unfold block
  rw [Nat.mul_zero]
  rfl

theorem block_succ (depth steps n : Nat) (x : V) :
    block hw0 hw1 depth steps (n+1) x = S depth steps (block hw0 hw1 depth steps n x) := by
  unfold block
  rw [Nat.mul_succ,Nat.add_comm (steps*n) steps,mesh_add]

def blockError (depth steps n : Nat) (x : V) : RC :=
  d (block hw0 hw1 depth steps (n+1) x) (block hw0 hw1 depth steps n x)

theorem blockError_decreasing (depth steps n : Nat) (x : V) :
    RCle (blockError hw0 hw1 depth steps (n+1) x) (blockError hw0 hw1 depth steps n x) := by
  simpa only [blockError,block_succ] using
    mesh_distance_bound hw0 hw1 depth steps
      (block hw0 hw1 depth steps (n+1) x) (block hw0 hw1 depth steps n x)

/-- A finite telescope; the original terminal norm is retained. -/
theorem weighted_energy (depth steps n : Nat) (x : V) :
    RCle (RCadd (RCscale (Q'.ofNat n) (blockError hw0 hw1 depth steps n x))
      (B (block hw0 hw1 depth steps n x) (block hw0 hw1 depth steps n x))) (B x x) := by
  induction n with
  | zero =>
      rw [show Q'.ofNat 0 = (0 : Q') from rfl,scale_zero,zero_add,block_zero]
      exact RCle_refl _
  | succ n ih =>
      have hd := mesh_dissipation hw0 hw1 depth steps (block hw0 hw1 depth steps n x)
      rw [← block_succ] at hd
      have hb := RCle_trans (RCadd_le_add
        (RCle_refl (RCscale (Q'.ofNat n) (blockError hw0 hw1 depth steps n x))) hd) ih
      change RCle (RCadd (RCscale (Q'.ofNat n) (blockError hw0 hw1 depth steps n x))
        (RCadd (blockError hw0 hw1 depth steps n x)
          (B (block hw0 hw1 depth steps (n+1) x) (block hw0 hw1 depth steps (n+1) x)))) (B x x) at hb
      rw [← add_assoc,← scale_nat_succ] at hb
      exact RCle_trans (RCadd_le_add
        (RCscale_mono (Q'.ofNat_nonneg (n+1)) (blockError_decreasing hw0 hw1 depth steps n x))
        (RCle_refl _)) hb

theorem weighted_error (depth steps n : Nat) (x : V) :
    RCle (RCscale (Q'.ofNat n) (blockError hw0 hw1 depth steps n x)) (B x x) := by
  have h := RCadd_le_add (RCle_refl (RCscale (Q'.ofNat n) (blockError hw0 hw1 depth steps n x)))
    (completedInner_nonnegative hw0 hw1 (block hw0 hw1 depth steps n x))
  rw [add_zero] at h
  exact RCle_trans h (weighted_energy hw0 hw1 depth steps n x)

theorem full_mesh_time (depth : Nat) (x : V) : S depth (2^depth) x = T 1 x := by
  have h := mesh_refinement hw0 hw1 0 depth 1 x
  rw [Nat.zero_add,Nat.one_mul] at h
  exact h.trans (mesh_original hw0 hw1 1 x)

/-- The unused time interval is explicit, nonnegative, and contractive. -/
theorem time_error_le_blockError (depth steps n total : Nat)
    (hbudget : steps*n ≤ total) (x : V) :
    RCle (d (S depth steps (S depth total x)) (S depth total x))
      (blockError hw0 hw1 depth steps n x) := by
  let remainder := total-steps*n
  have ht : S depth remainder (block hw0 hw1 depth steps n x) = S depth total x := by
    unfold block
    rw [← mesh_add,Nat.sub_add_cancel hbudget]
  have hs : S depth remainder (block hw0 hw1 depth steps (n+1) x) = S depth steps (S depth total x) := by
    rw [block_succ,mesh_commutes,ht]
  have h := mesh_distance_bound hw0 hw1 depth remainder
    (block hw0 hw1 depth steps (n+1) x) (block hw0 hw1 depth steps n x)
  rw [hs,ht] at h
  exact h

theorem time_weighted_error (depth steps n total : Nat)
    (hbudget : steps*n ≤ total) (x : V) :
    RCle (RCscale (Q'.ofNat n) (d (S depth steps (S depth total x)) (S depth total x))) (B x x) :=
  RCle_trans (RCscale_mono (Q'.ofNat_nonneg n)
    (time_error_le_blockError hw0 hw1 depth steps n total hbudget x))
    (weighted_error hw0 hw1 depth steps n x)

theorem half_power_normalizes (k : Nat) : Q'.eqv (half^k * Q'.ofNat (2^k)) 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [Nat.pow_succ]
      change Q'.eqv ((half * half^k) * Q'.ofNat (2^k * 2)) 1
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (SU3CharFactor.ofNat_mul_eqv (2^k) 2)) ?_
      have hr : Q'.eqv ((half * half^k) * (Q'.ofNat (2^k) * 2))
          ((half * 2) * (half^k * Q'.ofNat (2^k))) :=
        RingNormaliser.poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.const 2)))
          (.mul (.mul (.var 0) (.const 2)) (.mul (.var 1) (.var 2))) (by decide)
          (fun | 0 => half | 1 => half^k | _ => Q'.ofNat (2^k))
      exact Q'.eqv_trans _ _ _ hr (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (half*2) 1))
        (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ih))

theorem time_small_bound (depth steps total k : Nat)
    (hsmall : steps*2^k ≤ total) (x : V) :
    RCle (d (S depth steps (S depth total x)) (S depth total x)) (RCscale (half^k) (B x x)) := by
  have h := RCscale_mono (Q'.pow_nonneg half half_nonneg k)
    (time_weighted_error hw0 hw1 depth steps (2^k) total hsmall x)
  rw [RCscale_RCscale,scale_congr (half_power_normalizes k),RCscale_one] at h
  exact h

/-- ALL dyadic increments at most 2^(-k), on the SAME original T(1) image. -/
theorem range_small_bound (depth steps k : Nat)
    (hsmall : steps*2^k ≤ 2^depth) (x : V) :
    RCle (d (S depth steps (T 1 x)) (T 1 x)) (RCscale (half^k) (B x x)) := by
  have h := time_small_bound hw0 hw1 depth steps (2^depth) k hsmall x
  rwa [full_mesh_time] at h

/-- Increment and positive anchor may have independent supplied mesh presentations. -/
theorem anchored_small_bound (anchorDepth anchorSteps depth steps k : Nat)
    (hsmall : (steps*2^anchorDepth)*2^k ≤ anchorSteps*2^depth) (x : V) :
    RCle (d (S depth steps (S anchorDepth anchorSteps x)) (S anchorDepth anchorSteps x))
      (RCscale (half^k) (B x x)) := by
  have h := time_small_bound hw0 hw1 (anchorDepth+depth) (steps*2^anchorDepth)
    (anchorSteps*2^depth) k hsmall x
  rw [mesh_refinement] at h
  have hr (y : V) : S (anchorDepth+depth) (steps*2^anchorDepth) y = S depth steps y := by
    rw [Nat.add_comm anchorDepth depth]
    exact mesh_refinement hw0 hw1 depth anchorDepth steps y
  rwa [hr] at h

#print axioms mesh_form_dominates_norm
#print axioms mesh_dissipation
#print axioms blockError_decreasing
#print axioms weighted_energy
#print axioms weighted_error
#print axioms full_mesh_time
#print axioms time_error_le_blockError
#print axioms time_weighted_error
#print axioms half_power_normalizes
#print axioms time_small_bound
#print axioms range_small_bound
#print axioms anchored_small_bound

end YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy
