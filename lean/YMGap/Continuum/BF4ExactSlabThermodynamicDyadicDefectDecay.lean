/-
# Higher defect decay for the ORIGINAL dyadic semigroup

At each actual dyadic mesh let S be its one-step operator and D=I-S.
The finer mesh supplies the positive square root needed to prove that
every mixed moment <x,S^k D^l x> is nonnegative. The exact splitting
m(k,l)=m(k+1,l)+m(k,l+1) telescopes to
  n^r m(k+r*n,l+r) <= m(k,l).
Consequently n^(2*r) ||S^(r*n) D^r x||^2 <= ||x||^2.
This is a quantitative smoothing estimate for the existing operators,
not an assumed spectral representation or a replacement state space.
It supplies the fourth-moment bound for actual dyadic difference
quotients. Their limit, derivative identification, self-adjointness,
physical-scale control, continuum QFT and Clay remain separate obligations.
The SU(2) nome and lattice spacing remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.SU3CharFactor (ofNat_nonneg)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
  (completedInner_sub_left completedInner_sub_right)
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeDefectMoments (sub_nonnegative)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinWords (scale_nat_succ add_assoc add_comm)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (rc_add_zero rc_zero_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup (action_commutes)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (time_sub)

local notation "B" => completedInner

def defect (depth : Nat) (x : Completion) : Completion := completedSub x (generator depth x)

theorem defect_symmetric (depth : Nat) (x y : Completion) :
    B (defect depth x) y=B x (defect depth y) := by
  unfold defect
  rw [completedInner_sub_left,completedInner_sub_right,generator_symmetric]

theorem defect_positive (depth : Nat) (x : Completion) : RCnonneg (B x (defect depth x)) := by
  unfold defect
  rw [completedInner_sub_right]
  apply sub_nonnegative
  rw [completedInner_symm x,← generator_pairing]
  exact generator_contraction (depth+1) x

theorem mesh_generator_commutes (mesh steps depth : Nat) (x : Completion) :
    time mesh steps (generator depth x)=generator depth (time mesh steps x) :=
  action_commutes (NonnegativeDyadicTime.embed ⟨mesh,steps⟩)
    (NonnegativeDyadicTime.embed ⟨depth,1⟩) x

theorem time_defect (mesh steps depth : Nat) (x : Completion) :
    time mesh steps (defect depth x)=defect depth (time mesh steps x) := by
  unfold defect
  rw [time_sub,mesh_generator_commutes]

def defectPower (depth : Nat) : Nat → Completion → Completion
  | 0,x => x
  | n+1,x => defect depth (defectPower depth n x)

theorem defectPower_defect (depth n : Nat) (x : Completion) :
    defectPower depth n (defect depth x)=defect depth (defectPower depth n x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (defect depth) ih

theorem defectPower_add (depth m n : Nat) (x : Completion) :
    defectPower depth (m+n) x=defectPower depth m (defectPower depth n x) := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih => rw [Nat.succ_add,defectPower,defectPower,ih]

theorem defectPower_symmetric (depth n : Nat) (x y : Completion) :
    B (defectPower depth n x) y=B x (defectPower depth n y) := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
      change B (defect depth (defectPower depth n x)) y=B x (defect depth (defectPower depth n y))
      rw [defect_symmetric,ih,defectPower_defect]

theorem defectPower_positive (depth : Nat) : ∀ n,∀ x : Completion,
    RCnonneg (B x (defectPower depth n x))
  | 0,x => completedInner_nonnegative x
  | 1,x => defect_positive depth x
  | n+2,x => by
      change RCnonneg (B x (defect depth (defect depth (defectPower depth n x))))
      rw [← defect_symmetric,← defectPower_defect]
      exact defectPower_positive depth n (defect depth x)

theorem time_defectPower (mesh steps depth n : Nat) (x : Completion) :
    time mesh steps (defectPower depth n x)=defectPower depth n (time mesh steps x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change time mesh steps (defect depth (defectPower depth n x))=
        defect depth (defectPower depth n (time mesh steps x))
      rw [time_defect,ih]

def moment (depth : Nat) (x : Completion) (k l : Nat) : RC :=
  B x (time depth k (defectPower depth l x))

theorem moment_halfTime (depth : Nat) (x : Completion) (k l : Nat) :
    moment depth x k l=B (time (depth+1) k x) (defectPower depth l (time (depth+1) k x)) := by
  rw [← time_defectPower,← time_moments,time_double,time_symmetric]
  rfl

theorem moment_nonnegative (depth : Nat) (x : Completion) (k l : Nat) :
    RCnonneg (moment depth x k l) := by
  rw [moment_halfTime]
  exact defectPower_positive depth l (time (depth+1) k x)

theorem moment_zero (depth : Nat) (x : Completion) : moment depth x 0 0=B x x := rfl

theorem moment_split (depth : Nat) (x : Completion) (k l : Nat) :
    moment depth x k l=RCadd (moment depth x (k+1) l) (moment depth x k (l+1)) := by
  have h := completedSub_add_cancel (defectPower depth l x) (generator depth (defectPower depth l x))
  change completedAdd (defectPower depth (l+1) x) (generator depth (defectPower depth l x))=
    defectPower depth l x at h
  rw [completedAdd_comm] at h
  have ht := congrArg (fun y => B x (time depth k y)) h
  dsimp only at ht
  rw [time_add_state,completedInner_add_right,time_commutes_generator] at ht
  exact ht.symm

theorem moment_time_decreases (depth : Nat) (x : Completion) (k l : Nat) :
    RCle (moment depth x (k+1) l) (moment depth x k l) := by
  have h := RCadd_le_add (RCle_refl (moment depth x (k+1) l)) (moment_nonnegative depth x k (l+1))
  rw [rc_add_zero,← moment_split] at h
  exact h

/-- Retaining the terminal moment makes finite telescoping exact enough to iterate. -/
theorem weighted_terminal (depth : Nat) (x : Completion) (k l n : Nat) :
    RCle (RCadd (RCscale (Q'.ofNat n) (moment depth x (k+n) (l+1)))
      (moment depth x (k+n) l)) (moment depth x k l) := by
  induction n with
  | zero =>
      rw [Nat.add_zero,scale_congr (by decide : Q'.eqv (Q'.ofNat 0) 0),scale_zero,rc_zero_add]
      exact RCle_refl _
  | succ n ih =>
      have h := RCle_trans (RCadd_le_add
        (RCscale_mono (ofNat_nonneg n) (moment_time_decreases depth x (k+n) (l+1)))
        (RCle_refl (moment depth x (k+n) l))) ih
      rw [moment_split depth x (k+n) l,add_comm (moment depth x (k+n+1) l),
        ← add_assoc] at h
      have h' := RCle_trans (RCadd_le_add (RCadd_le_add (RCle_refl _)
        (moment_time_decreases depth x (k+n) (l+1))) (RCle_refl _)) h
      rw [← scale_nat_succ] at h'
      simpa only [Nat.add_assoc] using h'

theorem weighted_step (depth : Nat) (x : Completion) (k l n : Nat) :
    RCle (RCscale (Q'.ofNat n) (moment depth x (k+n) (l+1))) (moment depth x k l) := by
  have h := RCadd_le_add (RCle_refl (RCscale (Q'.ofNat n) (moment depth x (k+n) (l+1))))
    (moment_nonnegative depth x (k+n) l)
  rw [rc_add_zero] at h
  exact RCle_trans h (weighted_terminal depth x k l n)

/-- An explicit estimate of every finite order, for the actual original moments. -/
theorem weighted_order (depth : Nat) (x : Completion) (k l n r : Nat) :
    RCle (RCscale ((Q'.ofNat n)^r) (moment depth x (k+r*n) (l+r))) (moment depth x k l) := by
  induction r with
  | zero =>
      change RCle (RCscale 1 (moment depth x (k+0*n) (l+0))) _
      rw [Nat.zero_mul,Nat.add_zero,RCscale_one]
      exact RCle_refl _
  | succ r ih =>
      have h := RCle_trans (RCscale_mono (Q'.pow_nonneg _ (ofNat_nonneg n) r)
        (weighted_step depth x (k+r*n) (l+r) n)) ih
      rw [RCscale_RCscale,scale_congr (Q'.mul_comm_eqv ((Q'.ofNat n)^r) (Q'.ofNat n))] at h
      simpa only [Nat.succ_mul,Nat.add_assoc] using h

theorem moment_square (depth : Nat) (x : Completion) (n r : Nat) :
    moment depth x (n+n) (r+r)=
      B (time depth n (defectPower depth r x)) (time depth n (defectPower depth r x)) := by
  unfold moment
  rw [defectPower_add,time_defectPower,← defectPower_symmetric,← time_symmetric,time_moments]

/-- Higher differences have polynomial decay; no spectral lower bound is needed. -/
theorem smoothing_bound (depth n r : Nat) (x : Completion) :
    RCle (RCscale ((Q'.ofNat n)^(r+r))
      (B (time depth (r*n) (defectPower depth r x))
        (time depth (r*n) (defectPower depth r x)))) (B x x) := by
  have h := weighted_order depth x 0 0 n (r+r)
  rw [Nat.zero_add,Nat.zero_add,Nat.add_mul,moment_square,moment_zero] at h
  exact h

end YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.defect
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.defect_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.defect_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.mesh_generator_commutes
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.time_defect
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.defectPower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.defectPower_defect
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.defectPower_add
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.defectPower_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.defectPower_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.time_defectPower
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.moment
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.moment_halfTime
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.moment_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.moment_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.moment_split
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.moment_time_decreases
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.weighted_terminal
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.weighted_step
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.weighted_order
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.moment_square
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay.smoothing_bound
