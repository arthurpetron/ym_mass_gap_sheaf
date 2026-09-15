/-
# Quantitative positive dyadic time continuity on the ORIGINAL carrier

The next finer mesh supplies a positive square root of any mesh-time
operator. Its contraction gives the firm energy inequality
  ||Az-z||^2 + ||Az||^2 <= ||z||^2.
Successive increment errors decrease, so finite telescoping gives
  N ||A^(N+1)x-A^N x||^2 <= ||x||^2.
If N steps fit inside one T2 unit, the remaining time is constructed by
natural subtraction and contraction transports this estimate to T2 x.
Taking N=2^k gives squared error <= 2^(-k)||x||^2 at EVERY dyadic time
steps/2^depth <= 2^(-k), with an explicit tolerance-to-depth modulus.
The same estimate holds after ANY dyadic anchor time s when the increment
t satisfies t*2^k <= s. Common refinement compares different anchor and
increment meshes. Thus positive-time right continuity is quantitative on
every original state; the threshold is the supplied anchor divided by 2^k.

All states, norms and time operators remain the original fixed-nome,
fixed-spacing SU(2) objects. This proves zero-time continuity on the T2
RANGE and positive-time right continuity. It does not prove that the
range is dense, the transfer kernel is zero, or time is continuous at
zero on the entire completion. Real-time extension,
geometric T1 identification, Hamiltonian/physical-scale/continuum/Clay
obligations remain open. No spectral representation or inverse is assumed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Constructive.SU3CharFactor (ofNat_nonneg ofNat_mul_eqv)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (completedInner_sub_left)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime (twoStepTransfer)
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments (sub_nonnegative)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords (scale_nat_succ add_assoc)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (rc_add_zero rc_zero_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation (normCap normCap_nonnegative norm_le_cap)
open YMGap.Continuum.RegularLinearGeometricModulus (halfCutoff halfCutoff_spec)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup (time_refinement_power action action_embed)

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem time_sub (depth steps : Nat) (x y : Completion) :
    time depth steps (completedSub x y) = completedSub (time depth steps x) (time depth steps y) := by
  unfold completedSub completedNeg
  rw [time_add_state, time_smul]

theorem time_distance_contraction (depth steps : Nat) (x y : Completion) :
    RCle (completedDist (time depth steps x) (time depth steps y)) (completedDist x y) := by
  unfold completedDist
  rw [← time_sub]
  exact time_contraction depth steps (completedSub x y)

theorem time_commutes (depth s t : Nat) (x : Completion) :
    time depth s (time depth t x) = time depth t (time depth s x) := by
  rw [← time_add, ← time_add, Nat.add_comm s t]

/-- The finer square root supplies this inequality without a spectral theorem. -/
theorem time_form_dominates_norm (depth steps : Nat) (x : Completion) :
    RCle (B (time depth steps x) (time depth steps x)) (B (time depth steps x) x) := by
  have h := time_contraction (depth+1) steps (time (depth+1) steps x)
  rw [← time_add, time_double] at h
  have hp := time_moments (depth+1) steps x x
  rw [time_double] at hp
  rw [← hp] at h
  exact h

/-- One step's squared increment is paid by the actual loss of squared norm. -/
theorem time_dissipation (depth steps : Nat) (x : Completion) :
    RCle (RCadd (completedDist (time depth steps x) x)
      (B (time depth steps x) (time depth steps x))) (B x x) := by
  let y := time depth steps x
  let d := completedSub x y
  have hc : RCnonneg (B d y) := by
    change RCnonneg (B (completedSub x y) y)
    rw [completedInner_sub_left, completedInner_symm x y]
    exact sub_nonnegative _ _ (time_form_dominates_norm depth steps x)
  have hc' : RCnonneg (B y d) := by rw [completedInner_symm]; exact hc
  have h := RCadd_le_add (RCadd_le_add (RCle_refl (B d d)) hc)
    (RCadd_le_add hc' (RCle_refl (B y y)))
  rw [rc_add_zero, rc_zero_add, ← completedInner_add_right,
    ← completedInner_add_right, ← completedInner_add_left] at h
  change RCle (RCadd (completedDist x y) (B y y))
    (B (completedAdd (completedSub x y) y) (completedAdd (completedSub x y) y)) at h
  rw [completedSub_add_cancel, completedDist_symm x y] at h
  exact h

def block (depth steps n : Nat) (x : Completion) : Completion := time depth (steps*n) x

theorem block_zero (depth steps : Nat) (x : Completion) : block depth steps 0 x = x := by
  unfold block
  rw [Nat.mul_zero]
  rfl

theorem block_succ (depth steps n : Nat) (x : Completion) :
    block depth steps (n+1) x = time depth steps (block depth steps n x) := by
  unfold block
  rw [Nat.mul_succ, Nat.add_comm (steps*n) steps, time_add]

def blockError (depth steps n : Nat) (x : Completion) : RC :=
  completedDist (block depth steps (n+1) x) (block depth steps n x)

theorem blockError_succ (depth steps n : Nat) (x : Completion) :
    RCle (blockError depth steps (n+1) x) (blockError depth steps n x) := by
  simpa only [blockError, block_succ] using
    time_distance_contraction depth steps (block depth steps (n+1) x) (block depth steps n x)

/-- Finite telescoping with a decreasing increment, retaining the terminal energy. -/
theorem weighted_energy (depth steps n : Nat) (x : Completion) :
    RCle (RCadd (RCscale (Q'.ofNat n) (blockError depth steps n x))
      (B (block depth steps n x) (block depth steps n x))) (B x x) := by
  induction n with
  | zero =>
      rw [scale_congr (by decide : Q'.eqv (Q'.ofNat 0) 0), scale_zero, rc_zero_add, block_zero]
      exact RCle_refl _
  | succ n ih =>
      have hd := time_dissipation depth steps (block depth steps n x)
      rw [← block_succ] at hd
      have hb := RCle_trans (RCadd_le_add
        (RCle_refl (RCscale (Q'.ofNat n) (blockError depth steps n x))) hd) ih
      change RCle (RCadd (RCscale (Q'.ofNat n) (blockError depth steps n x))
        (RCadd (blockError depth steps n x)
          (B (block depth steps (n+1) x) (block depth steps (n+1) x)))) (B x x) at hb
      rw [← add_assoc, ← scale_nat_succ] at hb
      exact RCle_trans (RCadd_le_add
        (RCscale_mono (ofNat_nonneg (n+1)) (blockError_succ depth steps n x)) (RCle_refl _)) hb

theorem weighted_error (depth steps n : Nat) (x : Completion) :
    RCle (RCscale (Q'.ofNat n) (blockError depth steps n x)) (B x x) := by
  have h := RCadd_le_add (RCle_refl (RCscale (Q'.ofNat n) (blockError depth steps n x)))
    (completedInner_nonnegative (block depth steps n x))
  rw [rc_add_zero] at h
  exact RCle_trans h (weighted_energy depth steps n x)

theorem full_mesh_time (depth : Nat) (x : Completion) : time depth (2^depth) x = twoStepTransfer x := by
  have h := time_refinement_power 0 depth 1 x
  rw [Nat.zero_add, Nat.one_mul] at h
  exact h.trans (generator_zero x)

/-- The unspent interval is explicit natural subtraction, not an inverse time operator. -/
theorem time_error_le_blockError (depth steps n total : Nat)
    (hbudget : steps*n ≤ total) (x : Completion) :
    RCle (completedDist (time depth steps (time depth total x)) (time depth total x))
      (blockError depth steps n x) := by
  let remainder := total - steps*n
  have ht : time depth remainder (block depth steps n x) = time depth total x := by
    unfold block
    rw [← time_add, Nat.sub_add_cancel hbudget]
  have hs : time depth remainder (block depth steps (n+1) x) = time depth steps (time depth total x) := by
    rw [block_succ, time_commutes, ht]
  have h := time_distance_contraction depth remainder (block depth steps (n+1) x) (block depth steps n x)
  rw [hs, ht] at h
  exact h

theorem time_weighted_error (depth steps n total : Nat)
    (hbudget : steps*n ≤ total) (x : Completion) :
    RCle (RCscale (Q'.ofNat n)
      (completedDist (time depth steps (time depth total x)) (time depth total x))) (B x x) :=
  RCle_trans (RCscale_mono (ofNat_nonneg n) (time_error_le_blockError depth steps n total hbudget x))
    (weighted_error depth steps n x)

theorem range_error_le_blockError (depth steps n : Nat)
    (hbudget : steps*n ≤ 2^depth) (x : Completion) :
    RCle (completedDist (time depth steps (twoStepTransfer x)) (twoStepTransfer x))
      (blockError depth steps n x) := by
  have h := time_error_le_blockError depth steps n (2^depth) hbudget x
  rw [full_mesh_time] at h
  exact h

theorem range_weighted_error (depth steps n : Nat)
    (hbudget : steps*n ≤ 2^depth) (x : Completion) :
    RCle (RCscale (Q'.ofNat n)
      (completedDist (time depth steps (twoStepTransfer x)) (twoStepTransfer x))) (B x x) :=
  RCle_trans (RCscale_mono (ofNat_nonneg n) (range_error_le_blockError depth steps n hbudget x))
    (weighted_error depth steps n x)

theorem half_power_normalizes (k : Nat) : Q'.eqv (half^k * Q'.ofNat (2^k)) 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [Nat.pow_succ]
      change Q'.eqv ((half * half^k) * Q'.ofNat (2^k * 2)) 1
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (ofNat_mul_eqv (2^k) 2)) ?_
      have hreorder : Q'.eqv ((half * half^k) * (Q'.ofNat (2^k) * 2))
          ((half * 2) * (half^k * Q'.ofNat (2^k))) :=
        RingNormaliser.poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.const 2)))
          (.mul (.mul (.var 0) (.const 2)) (.mul (.var 1) (.var 2))) (by decide)
          (fun | 0 => half | 1 => half^k | _ => Q'.ofNat (2^k))
      refine Q'.eqv_trans _ _ _ hreorder ?_
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (by decide : Q'.eqv (half*2) 1))
        (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) ih)

theorem time_smallTime_bound (depth steps total k : Nat)
    (hsmall : steps * 2^k ≤ total) (x : Completion) :
    RCle (completedDist (time depth steps (time depth total x)) (time depth total x))
      (RCscale (half^k) (B x x)) := by
  have h := RCscale_mono (Q'.pow_nonneg half half_nonneg k)
    (time_weighted_error depth steps (2^k) total hsmall x)
  rw [RCscale_RCscale, scale_congr (half_power_normalizes k), RCscale_one] at h
  exact h

/-- Every dyadic time at most 2^(-k), not merely the single-step refinement sequence. -/
theorem range_smallTime_bound (depth steps k : Nat)
    (hsmall : steps * 2^k ≤ 2^depth) (x : Completion) :
    RCle (completedDist (time depth steps (twoStepTransfer x)) (twoStepTransfer x))
      (RCscale (half^k) (B x x)) := by
  have h := RCscale_mono (Q'.pow_nonneg half half_nonneg k)
    (range_weighted_error depth steps (2^k) hsmall x)
  rw [RCscale_RCscale, scale_congr (half_power_normalizes k), RCscale_one] at h
  exact h

theorem range_generator_bound (depth : Nat) (x : Completion) :
    RCle (completedDist (generator depth (twoStepTransfer x)) (twoStepTransfer x))
      (RCscale (half^depth) (B x x)) :=
  range_smallTime_bound depth 1 depth (by simpa only [Nat.one_mul] using Nat.le_refl (2^depth)) x

/-- The increment and anchor can be supplied on completely different meshes. -/
theorem anchored_smallTime_bound (anchorDepth anchorSteps depth steps k : Nat)
    (hsmall : (steps * 2^anchorDepth) * 2^k ≤ anchorSteps * 2^depth) (x : Completion) :
    RCle (completedDist (time depth steps (time anchorDepth anchorSteps x))
      (time anchorDepth anchorSteps x)) (RCscale (half^k) (B x x)) := by
  have h := time_smallTime_bound (anchorDepth+depth) (steps*2^anchorDepth)
    (anchorSteps*2^depth) k hsmall x
  rw [time_refinement_power] at h
  have hrefine (y : Completion) : time (anchorDepth+depth) (steps*2^anchorDepth) y = time depth steps y := by
    rw [Nat.add_comm anchorDepth depth]
    exact time_refinement_power depth anchorDepth steps y
  rw [hrefine] at h
  exact h

/-- Computed depth threshold; its unit is dyadic T2-time, with squared-distance tolerance. -/
def rangeModulus (X : seminorm.Cauchy) (epsilon : Q') : Nat :=
  halfCutoff (linearTolerance (normCap X) (normCap_nonnegative X) epsilon)

theorem scaled_norm_small (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (k : Nat) (hk : rangeModulus X epsilon ≤ k) :
    RCle (RCscale (half^k) (B (point X) (point X))) (rat epsilon) := by
  have hp := Q'.le_trans' _ _ _ (half_pow_antitone (rangeModulus X epsilon) k hk)
    (halfCutoff_spec _ (linearTolerance_pos _ _ he))
  have hb := Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hp (normCap_nonnegative X))
    (linearTolerance_budget _ _ he)
  refine RCle_trans (RCscale_mono (Q'.pow_nonneg half half_nonneg k) (norm_le_cap X)) ?_
  exact leEv_ofQ'_of_approx_ge (fun _ => Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)) hb)

theorem range_smallTime (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (depth steps : Nat) (hsmall : steps * 2^(rangeModulus X epsilon) ≤ 2^depth) :
    RCle (completedDist
      (action (NonnegativeDyadicTime.embed ⟨depth,steps⟩) (twoStepTransfer (point X)))
      (twoStepTransfer (point X))) (rat epsilon) :=
  RCle_trans (range_smallTime_bound depth steps (rangeModulus X epsilon) hsmall (point X))
    (scaled_norm_small X epsilon he _ (Nat.le_refl _))

theorem range_generator_small (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (depth : Nat) (hdepth : rangeModulus X epsilon ≤ depth) :
    RCle (completedDist (generator depth (twoStepTransfer (point X))) (twoStepTransfer (point X)))
      (rat epsilon) :=
  RCle_trans (range_generator_bound depth (point X)) (scaled_norm_small X epsilon he depth hdepth)

/-- A modulus for ALL small dyadic times on the actual T2 image of the supplied state. -/
def rangeContinuityCertificate (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    {k : Nat // ∀ depth steps, steps * 2^k ≤ 2^depth →
      RCle (completedDist
        (action (NonnegativeDyadicTime.embed ⟨depth,steps⟩) (twoStepTransfer (point X)))
        (twoStepTransfer (point X))) (rat epsilon)} :=
  ⟨rangeModulus X epsilon, range_smallTime X epsilon he⟩

/-- Positive anchor s gives the explicit increment threshold s/2^k.
At a zero anchor the budget allows only zero increments: no full-space
continuity-at-zero claim is hidden in this statement. -/
theorem anchored_smallTime (anchor increment : NonnegativeDyadicTime.MeshPoint)
    (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (hsmall : increment.steps * 2^(anchor.depth + rangeModulus X epsilon) ≤
      anchor.steps * 2^increment.depth) :
    RCle (completedDist
      (action (NonnegativeDyadicTime.embed increment)
        (action (NonnegativeDyadicTime.embed anchor) (point X)))
      (action (NonnegativeDyadicTime.embed anchor) (point X))) (rat epsilon) := by
  rw [Nat.pow_add, ← Nat.mul_assoc] at hsmall
  exact RCle_trans
    (anchored_smallTime_bound anchor.depth anchor.steps increment.depth increment.steps
      (rangeModulus X epsilon) hsmall (point X))
    (scaled_norm_small X epsilon he _ (Nat.le_refl _))

def anchoredContinuityCertificate (anchor : NonnegativeDyadicTime.MeshPoint)
    (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    {k : Nat // ∀ increment : NonnegativeDyadicTime.MeshPoint,
      increment.steps * 2^(anchor.depth+k) ≤ anchor.steps * 2^increment.depth →
      RCle (completedDist
        (action (NonnegativeDyadicTime.embed increment)
          (action (NonnegativeDyadicTime.embed anchor) (point X)))
        (action (NonnegativeDyadicTime.embed anchor) (point X))) (rat epsilon)} :=
  ⟨rangeModulus X epsilon, fun increment => anchored_smallTime anchor increment X epsilon he⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.time_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.time_distance_contraction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.time_commutes
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.time_form_dominates_norm
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.time_dissipation
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.block
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.block_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.block_succ
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.blockError
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.blockError_succ
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.weighted_energy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.weighted_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.full_mesh_time
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.time_error_le_blockError
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.time_weighted_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.range_error_le_blockError
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.range_weighted_error
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.half_power_normalizes
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.time_smallTime_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.range_smallTime_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.range_generator_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.anchored_smallTime_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.rangeModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.scaled_norm_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.range_smallTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.range_generator_small
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.rangeContinuityCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.anchored_smallTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy.anchoredContinuityCertificate
