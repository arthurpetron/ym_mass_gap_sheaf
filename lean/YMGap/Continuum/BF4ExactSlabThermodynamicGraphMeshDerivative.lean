/-
# Actual dyadic Taylor derivative on the WHOLE original graph

For supplied original representatives U,V satisfying J u=T2 v, one
computed positive radius controls ||u-A_t u-t*v||^2 <= epsilon*t^2
on EVERY nonnegative dyadic mesh below that radius.

The core approximant is chosen in the image norm at tolerance epsilon/11.
The whole-graph increment bound controls the remainder difference by
4*t^2 times the squared image error. The original core Taylor estimate
and the squared triangle law cost at most 10 times that tolerance.
No preimage convergence or division by a small time is used.

This is still the original real completion at fixed SU(2), nome 1/1024,
fixed spacing and T2-time units. The real-time limit is the next consumer;
physical calibration, continuum QFT and all-group Clay stay open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeBound

namespace YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar (completed_eq_of_pairings)
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (completedInner_sub_left)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime (twoStepTransfer)
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation (completedTime_sub)
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit (dist_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (four_copies)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (smul_norm linearTolerance linearTolerance_pos linearTolerance_budget)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes (time)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (time_sub)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages (smul_sub)
open YMGap.Continuum.BF4ExactSlabThermodynamicDifferentiatedCore (image)
open YMGap.Continuum.BF4ExactSlabThermodynamicDerivativeGraphApproximation
open YMGap.Continuum.BF4ExactSlabThermodynamicGraphTimeBound (graph_mesh_increment_bound)

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem sub_sub_exchange (a b c d : Completion) :
    completedSub (completedSub a b) (completedSub c d)=
      completedSub (completedSub a c) (completedSub b d) := by
  apply completed_eq_of_pairings
  intro z
  simp only [completedInner_sub_left]
  refine Quotient.inductionOn₂ (B a z) (B b z) ?_
  intro A B'
  refine Quotient.inductionOn₂ (B c z) (B d z) ?_
  intro C D
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.neg (.add (.var 2) (.neg (.var 3)))))
      (.add (.add (.var 0) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 3)))))
      (by decide) (fun | 0 => A.approx n | 1 => B'.approx n | 2 => C.approx n | _ => D.approx n)))

theorem norm_sub_bound (x y : Completion) :
    RCle (B (completedSub x y) (completedSub x y))
      (RCadd (RCadd (B x x) (B x x)) (RCadd (B y y) (B y y))) := by
  have h := completedDist_triangle x completedZero y
  rw [dist_zero,completedDist_symm completedZero y,dist_zero] at h
  exact h

theorem graph_equation_sub (u v u' v' : Completion)
    (h : derivativeAction u=twoStepTransfer v) (h' : derivativeAction u'=twoStepTransfer v') :
    derivativeAction (completedSub u u')=twoStepTransfer (completedSub v v') := by
  rw [derivative_sub,h,h']
  exact (completedTime_sub 2 v v').symm

def remainder (depth steps : Nat) (u v : Completion) : Completion :=
  completedSub (completedSub u (time depth steps u)) (completedSmul (value ⟨depth,steps⟩) v)

theorem remainder_sub (depth steps : Nat) (u v u' v' : Completion) :
    remainder depth steps (completedSub u u') (completedSub v v')=
      completedSub (remainder depth steps u v) (remainder depth steps u' v') := by
  unfold remainder
  rw [time_sub,smul_sub,
    sub_sub_exchange u u' (time depth steps u) (time depth steps u'),
    sub_sub_exchange (completedSub u (time depth steps u)) (completedSub u' (time depth steps u'))
      (completedSmul (value ⟨depth,steps⟩) v) (completedSmul (value ⟨depth,steps⟩) v')]

/-- This bound is uniform as time tends to zero and only uses the IMAGE norm. -/
theorem remainder_graph_bound (depth steps : Nat) (u v : Completion)
    (h : derivativeAction u=twoStepTransfer v) :
    RCle (B (remainder depth steps u v) (remainder depth steps u v))
      (RCscale 4 (RCscale (value ⟨depth,steps⟩*value ⟨depth,steps⟩) (B v v))) := by
  have hb := norm_sub_bound (completedSub u (time depth steps u)) (completedSmul (value ⟨depth,steps⟩) v)
  rw [smul_norm] at hb
  have hi := graph_mesh_increment_bound depth steps u v h
  have hc := RCle_trans hb (RCadd_le_add (RCadd_le_add hi hi)
    (RCadd_le_add (RCle_refl _) (RCle_refl _)))
  rw [four_copies] at hc
  exact hc

def tolerance (epsilon : Q') : Q' := linearTolerance 10 (by decide) epsilon

theorem tolerance_positive {epsilon : Q'} (he : (0 : Q')<epsilon) : (0 : Q')<tolerance epsilon :=
  linearTolerance_pos 10 (by decide) he

theorem ten_copies (r : RC) :
    RCadd (RCadd (RCscale 4 r) (RCscale 4 r)) (RCadd r r)=RCscale 10 r := by
  refine Quotient.inductionOn r ?_
  intro R
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.mul (.const 4) (.var 0)) (.mul (.const 4) (.var 0))) (.add (.var 0) (.var 0)))
      (.mul (.const 10) (.var 0)) (by decide) (fun _ => R.approx n)))

theorem tolerance_budget (t epsilon : Q') (he : (0 : Q')<epsilon) :
    RCle (RCscale 10 (RCscale (t*t) (rat (tolerance epsilon)))) (rat ((t*t)*epsilon)) := by
  apply leEv_le_ofQ'_of_approx_le
  intro _
  have h : Q'.eqv (10*((t*t)*tolerance epsilon)) ((t*t)*(10*tolerance epsilon)) :=
    poly_identity_of_normal_eq
      (.mul (.const 10) (.mul (.var 0) (.var 1)))
      (.mul (.var 0) (.mul (.const 10) (.var 1))) (by decide)
      (fun | 0 => t*t | _ => tolerance epsilon)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (linearTolerance_budget 10 (by decide) he)
      (SumOfSquares.q_mul_self_nonneg t))

/-- Actual old core radius of the computed graph approximant; no preimage limit. -/
def radius (U V : seminorm.Cauchy) (epsilon : Q') : Q' :=
  BF4ExactSlabThermodynamicMeshDerivative.meshRadius (preimage U V (tolerance epsilon)) (tolerance epsilon)

theorem radius_positive (U V : seminorm.Cauchy) (epsilon : Q') : (0 : Q')<radius U V epsilon :=
  BF4ExactSlabThermodynamicMeshDerivative.meshRadius_positive _ _

/-- One computed radius for the entire graph point and EVERY nonnegative mesh. -/
theorem mesh_taylor_bound (U V : seminorm.Cauchy)
    (h : derivativeAction (point U)=twoStepTransfer (point V))
    (epsilon : Q') (he : (0 : Q')<epsilon) (depth steps : Nat)
    (ht : value ⟨depth,steps⟩≤radius U V epsilon) :
    RCle (B (remainder depth steps (point U) (point V)) (remainder depth steps (point U) (point V)))
      (rat ((value ⟨depth,steps⟩*value ⟨depth,steps⟩)*epsilon)) := by
  let delta := tolerance epsilon
  let q := approximant U V delta
  let c := RCscale (value ⟨depth,steps⟩*value ⟨depth,steps⟩) (rat delta)
  have hi : RCle (completedDist (point V) (image q)) (rat delta) := by
    rw [completedDist_symm]
    exact image_error U V h delta (tolerance_positive he)
  have hd := remainder_graph_bound depth steps (completedSub (point U) q.state)
    (completedSub (point V) (image q))
    (graph_equation_sub _ _ _ _ h (fromCore q).equation)
  rw [remainder_sub] at hd
  have hd' : RCle (completedDist (remainder depth steps (point U) (point V))
      (remainder depth steps q.state (image q))) (RCscale 4 c) :=
    RCle_trans hd (RCscale_mono (by decide : (0 : Q')≤4)
      (RCscale_mono (SumOfSquares.q_mul_self_nonneg _) hi))
  have hc : RCle (B (remainder depth steps q.state (image q)) (remainder depth steps q.state (image q))) c :=
    BF4ExactSlabThermodynamicMeshDerivative.mesh_taylor_bound (preimage U V delta)
      delta (tolerance_positive he) depth steps ht
  have hb := completedDist_triangle (remainder depth steps (point U) (point V))
    (remainder depth steps q.state (image q)) completedZero
  rw [dist_zero,dist_zero] at hb
  have hb' := RCle_trans hb (RCadd_le_add (RCadd_le_add hd' hd') (RCadd_le_add hc hc))
  rw [ten_copies] at hb'
  exact RCle_trans hb' (tolerance_budget (value ⟨depth,steps⟩) epsilon he)

def meshTaylorCertificate (U V : seminorm.Cauchy)
    (h : derivativeAction (point U)=twoStepTransfer (point V))
    (epsilon : Q') (he : (0 : Q')<epsilon) :
    Σ' r : Q', ((0 : Q')<r) ×'
      (∀ depth steps,value ⟨depth,steps⟩≤r →
        RCle (B (remainder depth steps (point U) (point V)) (remainder depth steps (point U) (point V)))
          (rat ((value ⟨depth,steps⟩*value ⟨depth,steps⟩)*epsilon))) :=
  ⟨radius U V epsilon,radius_positive U V epsilon,mesh_taylor_bound U V h epsilon he⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.sub_sub_exchange
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.norm_sub_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.graph_equation_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.remainder
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.remainder_sub
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.remainder_graph_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.tolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.tolerance_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.ten_copies
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.tolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.radius
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.radius_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.mesh_taylor_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicGraphMeshDerivative.meshTaylorCertificate
