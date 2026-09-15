/-
# Actual dyadic difference quotients on the ORIGINAL T2 range

Q_k y = 2^k (T2 y - S_k T2 y), where S_k is the existing dyadic
time 2^(-k) operator. The exact refinement identity expresses
Q_(k+1)-Q_k as 2^k (I-S_(k+1))^2 T2. The original mixed-moment
estimate bounds its squared norm by 4^(-k)||y||^2.

The time unit is T2, not an unidentified physical time. These estimates
do not identify a derivative at every positive real increment, the
regularized logarithm, a self-adjoint Hamiltonian or a physical mass.
Continuum, scaling and the all-group Clay target remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay

namespace YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Constructive.SU3CharFactor (ofNat_nonneg ofNat_mul_eqv)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime (twoStepTransfer timeCauchy)
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (completedInner_sub_left)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr four_copies four_quarter_scale)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity (smul_norm)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinFactorialMoments (scale_add)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialAction (actionRepresentative)
open YMGap.Continuum.BF4ExactSlabThermodynamicUniformPolynomialLinear (sequenceAction_sub)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy
  (full_mesh_time half_power_normalizes rangeModulus scaled_norm_small)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDefectDecay

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def differenceQuotient (depth : Nat) (x : Completion) : Completion :=
  completedSmul (Q'.ofNat (2^depth)) (defect depth (twoStepTransfer x))

/-- A direct finite identity using the actual finer-mesh square law. -/
theorem refinement_difference (depth : Nat) (c : Q') (x : Completion) :
    completedSub (completedSmul (c*2) (defect (depth+1) x))
      (completedSmul c (defect depth x))=
      completedSmul c (defectPower (depth+1) 2 x) := by
  apply completed_eq_of_pairings
  intro y
  change B (completedSub (completedSmul (c*2) (defect (depth+1) x))
    (completedSmul c (defect depth x))) y=
      B (completedSmul c (defect (depth+1) (defect (depth+1) x))) y
  unfold defect
  rw [show generator (depth+1) (completedSub x (generator (depth+1) x))=
      completedSub (generator (depth+1) x) (generator (depth+1) (generator (depth+1) x)) from
        sequenceAction_sub _ _ _,generator_square]
  simp only [completedInner_sub_left,completedInner_smul_left]
  refine Quotient.inductionOn₃ (B x y) (B (generator (depth+1) x) y) (B (generator depth x) y) ?_
  intro A C D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun j =>
    poly_identity_of_normal_eq
      (.add (.mul (.mul (.var 0) (.const 2)) (.add (.var 1) (.neg (.var 2))))
        (.neg (.mul (.var 0) (.add (.var 1) (.neg (.var 3))))))
      (.mul (.var 0) (.add (.add (.var 1) (.neg (.var 2)))
        (.neg (.add (.var 2) (.neg (.var 3)))))) (by decide)
      (fun | 0 => c | 1 => A.approx j | 2 => C.approx j | _ => D.approx j)))

theorem quotient_step (depth : Nat) (x : Completion) :
    completedSub (differenceQuotient (depth+1) x) (differenceQuotient depth x)=
      completedSmul (Q'.ofNat (2^depth)) (defectPower (depth+1) 2 (twoStepTransfer x)) := by
  unfold differenceQuotient
  rw [Nat.pow_succ,completedSmul_congr (ofNat_mul_eqv (2^depth) 2)]
  exact refinement_difference depth (Q'.ofNat (2^depth)) (twoStepTransfer x)

theorem fourth_normalization (c h : Q') (hc : Q'.eqv (h*c) 1) :
    Q'.eqv ((h*h)*(c^(2+2))) (c*c) := by
  have ha : Q'.eqv ((h*h)*(c^(2+2))) (((h*c)*(h*c))*(c*c)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 0))
        (.mul (.var 1) (.mul (.var 1) (.mul (.var 1) (.mul (.var 1) (.const 1))))))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => h | _ => c)
  have hb : Q'.eqv ((h*c)*(h*c)) 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hc)
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) hc)
  exact Q'.eqv_trans _ _ _ ha (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hb)
    (Q'.one_mul_eqv _))

/-- Squared norm of the ACTUAL quotient increment, uniformly in mesh depth. -/
theorem quotient_step_bound (depth : Nat) (x : Completion) :
    RCle (completedDist (differenceQuotient (depth+1) x) (differenceQuotient depth x))
      (RCscale (half^depth*half^depth) (B x x)) := by
  have h := RCscale_mono (Q'.mul_nonneg _ _ (Q'.pow_nonneg half half_nonneg depth)
    (Q'.pow_nonneg half half_nonneg depth)) (smoothing_bound (depth+1) (2^depth) 2 x)
  rw [RCscale_RCscale,scale_congr (fourth_normalization _ _ (half_power_normalizes depth)),
    time_defectPower,show 2*2^depth=2^(depth+1) by rw [Nat.pow_succ,Nat.mul_comm 2],full_mesh_time] at h
  unfold completedDist
  rw [quotient_step,smul_norm]
  exact h

theorem tail_budget (a : Q') :
    Q'.eqv ((a*a+a*a)+(4*((half*a)*(half*a))+4*((half*a)*(half*a)))) (4*(a*a)) := by
  have h : Q'.eqv ((a*a+a*a)+(4*((half*a)*(half*a))+4*((half*a)*(half*a))))
      ((2+8*half*half)*(a*a)) :=
    poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))
        (.add (.mul (.const 4) (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))))
          (.mul (.const 4) (.mul (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 0))))))
      (.mul (.add (.const 2) (.mul (.mul (.const 8) (.var 1)) (.var 1))) (.mul (.var 0) (.var 0)))
      (by decide) (fun | 0 => a | _ => half)
  exact Q'.eqv_trans _ _ _ h (Q'.mul_eqv_congr_right _ _ _
    (by decide : Q'.eqv (2+8*half*half) 4))

/-- A geometric tail bound in the ORIGINAL squared distance. -/
theorem quotient_tail_bound (start length : Nat) (x : Completion) :
    RCle (completedDist (differenceQuotient start x) (differenceQuotient (start+length) x))
      (RCscale (4*(half^start*half^start)) (B x x)) := by
  induction length generalizing start with
  | zero =>
      rw [Nat.add_zero,(completedDist_zero_iff _ _).mpr rfl]
      have h := RCscale_mono (Q'.mul_nonneg _ _ (by decide : (0 : Q')≤4)
        (SumOfSquares.q_mul_self_nonneg (half^start))) (completedInner_nonnegative x)
      rw [RCscale_RCzero] at h
      exact h
  | succ length ih =>
      have hs := quotient_step_bound start x
      rw [completedDist_symm] at hs
      have ht := ih (start+1)
      have h := RCle_trans (completedDist_triangle (differenceQuotient start x)
        (differenceQuotient (start+1) x) (differenceQuotient ((start+1)+length) x))
        (RCadd_le_add (RCadd_le_add hs hs) (RCadd_le_add ht ht))
      rw [← scale_add,← scale_add,← scale_add] at h
      have budget : Q'.eqv ((half^start*half^start+half^start*half^start)+
          (4*(half^(start+1)*half^(start+1))+4*(half^(start+1)*half^(start+1))))
          (4*(half^start*half^start)) := tail_budget (half^start)
      rw [scale_congr budget] at h
      simpa only [Nat.add_assoc,Nat.add_comm 1 length] using h

theorem quotient_pair_bound (start m n : Nat) (hm : start≤m) (hn : start≤n) (x : Completion) :
    RCle (completedDist (differenceQuotient m x) (differenceQuotient n x))
      (RCscale (16*(half^start*half^start)) (B x x)) := by
  have hm' := quotient_tail_bound start (m-start) x
  have hn' := quotient_tail_bound start (n-start) x
  rw [Nat.add_sub_of_le hm,completedDist_symm] at hm'
  rw [Nat.add_sub_of_le hn] at hn'
  have h := RCle_trans (completedDist_triangle (differenceQuotient m x)
    (differenceQuotient start x) (differenceQuotient n x))
    (RCadd_le_add (RCadd_le_add hm' hm') (RCadd_le_add hn' hn'))
  have budget : Q'.eqv (4*(4*(half^start*half^start))) (16*(half^start*half^start)) :=
    poly_identity_of_normal_eq
    (.mul (.const 4) (.mul (.const 4) (.var 0))) (.mul (.const 16) (.var 0))
    (by decide) (fun _ => half^start*half^start)
  rw [four_copies,RCscale_RCscale,scale_congr budget] at h
  exact h

def quotientModulus (X : seminorm.Cauchy) (epsilon : Q') : Nat :=
  rangeModulus X (quarter (quarter epsilon))

theorem quotient_cauchy (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon)
    (m n : Nat) (hm : quotientModulus X epsilon≤m) (hn : quotientModulus X epsilon≤n) :
    RCle (completedDist (differenceQuotient m (point X)) (differenceQuotient n (point X))) (rat epsilon) := by
  let k := quotientModulus X epsilon
  have hk : (0 : Q')≤half^k := Q'.pow_nonneg half half_nonneg k
  have hk1 : half^k≤1 := HKPos.pow_le_one half_nonneg (by decide) k
  have hsq : half^k*half^k≤half^k := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hk1 hk) (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have h := RCle_trans (quotient_pair_bound k m n hm hn (point X))
    (RCscale_scalar_mono (Q'.mul_le_mul_of_nonneg_left _ _ _ hsq (by decide : (0 : Q')≤16))
      (completedInner_nonnegative (point X)))
  have hs := RCscale_mono (by decide : (0 : Q')≤16)
    (scaled_norm_small X (quarter (quarter epsilon)) (quarter_pos (quarter_pos he)) k (Nat.le_refl k))
  rw [RCscale_RCscale] at hs
  have budget : RCscale 16 (rat (quarter (quarter epsilon)))=rat epsilon := by
    rw [scale_congr (by decide : Q'.eqv (16 : Q') (4*4)),← RCscale_RCscale,
      four_quarter_scale,four_quarter_scale]
  rw [budget] at hs
  exact RCle_trans h hs

def quotientRepresentative (depth : Nat) (X : seminorm.Cauchy) : seminorm.Cauchy :=
  (scalarContinuous (Q'.ofNat (2^depth))).mapCauchy
    (differenceCauchy (timeCauchy 2 X)
      (actionRepresentative (generatorSequence depth).sequence (timeCauchy 2 X)))

theorem quotientRepresentative_pin (depth : Nat) (X : seminorm.Cauchy) :
    (point (quotientRepresentative depth X))=differenceQuotient depth (point X) := rfl

def quotientRows (X : seminorm.Cauchy) : CauchyRows where
  row := fun depth => quotientRepresentative depth X
  modulus := quotientModulus X
  isCauchy := quotient_cauchy X

/-- Constructed negative dyadic derivative at zero of t |-> A_t(T2 x), in T2-time units. -/
def representedLimit (X : seminorm.Cauchy) : Completion := rowLimit (quotientRows X)

def derivativeRate (X : seminorm.Cauchy) : Q' → Nat := rowLimitRate (quotientRows X)

theorem derivative_bound (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon)
    (n : Nat) (hn : derivativeRate X epsilon≤n) :
    RCle (completedDist (differenceQuotient n (point X)) (representedLimit X)) (rat epsilon) :=
  rowLimit_bound (quotientRows X) epsilon he n hn

theorem representedLimit_congr (X Y : seminorm.Cauchy) (h : (point X)=(point Y)) :
    representedLimit X=representedLimit Y := by
  apply rowLimit_independent
  intro n
  change differenceQuotient n (point X)=differenceQuotient n (point Y)
  rw [h]

def derivativeAction : Completion → Completion :=
  Quotient.lift representedLimit (fun X Y h => representedLimit_congr X Y (Quotient.sound h))

/-- Original output Cauchy data, exact state pin and usable dyadic convergence rate. -/
def derivativeCertificate (X : seminorm.Cauchy) :
    Σ' Y : seminorm.Cauchy, {rate : Q' → Nat //
      (point Y)=derivativeAction (point X) ∧ ∀ epsilon : Q',(0 : Q')<epsilon →
        ∀ n,rate epsilon≤n → RCle (completedDist (differenceQuotient n (point X)) (point Y)) (rat epsilon)} :=
  ⟨diagonalCauchy (quotientRows X),⟨derivativeRate X,⟨rfl,derivative_bound X⟩⟩⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.differenceQuotient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.refinement_difference
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.quotient_step
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.fourth_normalization
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.quotient_step_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.tail_budget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.quotient_tail_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.quotient_pair_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.quotientModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.quotient_cauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.quotientRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.quotientRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.quotientRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.representedLimit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.derivativeRate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.derivative_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.representedLimit_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.derivativeAction
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative.derivativeCertificate
