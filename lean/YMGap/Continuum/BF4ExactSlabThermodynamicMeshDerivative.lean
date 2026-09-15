/-
# Uniform differentiation over ORIGINAL positive dyadic increments

The multi-step quotient is an actual finite time average of the proved
one-step quotients. Average contraction and full-space time-zero continuity
of their constructed limit yield an explicit radius, independent of mesh
depth and step count after refinement. The Taylor remainder is bounded by
epsilon*t^2 on EVERY nonnegative dyadic mesh with t below that radius.
The derivative vector is the previously constructed original limit.

This is dyadic-time differentiation in T2 units, not yet an all-real-time
derivative or a self-adjoint physical Hamiltonian. The original fixed SU(2)
nome/spacing, continuum and all-group Clay boundaries are unchanged.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages
import YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity

namespace YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint refine)
open YMGap.Constructive.DyadicTimeRationals
  (value value_num value_den value_nonnegative value_le_iff value_refine half_power_num half_power_den)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedBilinear (completedInner_zero_left)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion (completedSub_zero)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime (twoStepTransfer)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows (diagonalCauchy)
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation (completedDist_two_segment)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity (smul_norm)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicTimeMeshes
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicSemigroup (time_refinement_power action_embed)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicEnergy (half_power_normalizes)
open YMGap.Continuum.BF4ExactSlabThermodynamicDyadicDerivative
open YMGap.Continuum.BF4ExactSlabThermodynamicTimeAverages
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins
open YMGap.Continuum.BF4ExactSlabThermodynamicFullSpaceZeroContinuity (zeroRadius zeroRadius_positive full_space_zero_bound)

local notation "B" => completedInner
local notation "point" X => Quotient.mk seminorm.completionSetoid X
local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def meshQuotient (depth n : Nat) (x : Completion) : Completion :=
  completedSmul (Q'.ofNat (2^depth)*Q'.invSucc n)
    (completedSub (twoStepTransfer x) (time depth (n+1) (twoStepTransfer x)))

theorem meshQuotient_average (depth n : Nat) (x : Completion) :
    meshQuotient depth n x=timeAverage depth n (differenceQuotient depth x) := by
  unfold differenceQuotient
  have h : timeAverage depth n (completedSmul (Q'.ofNat (2^depth))
      (BF4ExactSlabThermodynamicDyadicDefectDecay.defect depth (twoStepTransfer x)))=
      completedSmul (Q'.ofNat (2^depth))
        (timeAverage depth n (BF4ExactSlabThermodynamicDyadicDefectDecay.defect depth (twoStepTransfer x))) := by
    unfold timeAverage
    simp only [time_smul,average_smul]
  rw [h,timeAverage_defect,completedSmul_mul]
  rfl

def derivativeRepresentative (X : seminorm.Cauchy) : seminorm.Cauchy := diagonalCauchy (quotientRows X)

theorem derivativeRepresentative_pin (X : seminorm.Cauchy) :
    (point (derivativeRepresentative X))=derivativeAction (point X) := rfl

def meshDepth (X : seminorm.Cauchy) (epsilon : Q') : Nat := derivativeRate X (quarter epsilon)

def meshRadius (X : seminorm.Cauchy) (epsilon : Q') : Q' :=
  zeroRadius (derivativeRepresentative X) (quarter epsilon)

theorem meshRadius_positive (X : seminorm.Cauchy) (epsilon : Q') : (0 : Q')<meshRadius X epsilon :=
  zeroRadius_positive _ _

theorem timeAverage_derivative_close (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon)
    (depth n : Nat) (ht : value ⟨depth,n+1⟩≤meshRadius X epsilon) :
    RCle (completedDist (timeAverage depth n (derivativeAction (point X))) (derivativeAction (point X)))
      (rat (quarter epsilon)) := by
  apply timeAverage_close
  intro j hj
  cases j with
  | zero =>
      change RCle (completedDist (derivativeAction (point X)) (derivativeAction (point X))) _
      rw [(completedDist_zero_iff _ _).mpr rfl]
      exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt (quarter_pos he))
  | succ j =>
      have hv : value ⟨depth,j+1⟩≤meshRadius X epsilon := Q'.le_trans' _ _ _
        ((value_le_iff _ _).mpr (Nat.mul_le_mul_right (2^depth) (Nat.le_of_lt hj))) ht
      have hb := full_space_zero_bound (derivativeRepresentative X) (quarter epsilon) (quarter_pos he)
        (timeValue (dyadicTime ⟨depth,j+1⟩ (Nat.succ_pos j)))
        (leEv_le_ofQ'_of_approx_le (fun _ => hv))
      rw [realTimeAction_dyadic,action_embed,derivativeRepresentative_pin] at hb
      exact hb

/-- The depth threshold and radius are computed from ORIGINAL input/output data. -/
theorem mesh_quotient_bound (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon)
    (depth n : Nat) (hd : meshDepth X epsilon≤depth) (ht : value ⟨depth,n+1⟩≤meshRadius X epsilon) :
    RCle (completedDist (meshQuotient depth n (point X)) (derivativeAction (point X))) (rat epsilon) := by
  rw [meshQuotient_average]
  exact completedDist_two_segment _ (timeAverage depth n (derivativeAction (point X))) _ epsilon
    (RCle_trans (timeAverage_contraction depth n _ _) (derivative_bound X (quarter epsilon) (quarter_pos he) depth hd))
    (timeAverage_derivative_close X epsilon he depth n ht)

theorem mesh_value (depth steps : Nat) :
    Q'.eqv (value ⟨depth,steps⟩) (Q'.ofNat steps*HalfPow.half^depth) := by
  change (value ⟨depth,steps⟩).num*((Q'.ofNat steps*HalfPow.half^depth).den : Int)=
    (Q'.ofNat steps*HalfPow.half^depth).num*((value ⟨depth,steps⟩).den : Int)
  rw [value_num,value_den,Q'.mul_den_cast]
  change (steps : Int)*(1*((HalfPow.half^depth).den : Int))=
    ((steps : Int)*(HalfPow.half^depth).num)*(2^depth : Nat)
  rw [half_power_den,half_power_num,Int.one_mul,Int.mul_one]

theorem mesh_normalization (depth n : Nat) :
    Q'.eqv (value ⟨depth,n+1⟩*(Q'.ofNat (2^depth)*Q'.invSucc n)) 1 := by
  have h := Q'.mul_eqv_congr_right _ _ (Q'.ofNat (2^depth)*Q'.invSucc n) (mesh_value depth (n+1))
  have hr : Q'.eqv ((Q'.ofNat (n+1)*HalfPow.half^depth)*(Q'.ofNat (2^depth)*Q'.invSucc n))
      ((HalfPow.half^depth*Q'.ofNat (2^depth))*(Q'.ofNat (n+1)*Q'.invSucc n)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3))) (by decide)
      (fun | 0 => Q'.ofNat (n+1) | 1 => HalfPow.half^depth | 2 => Q'.ofNat (2^depth) | _ => Q'.invSucc n)
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _ hr
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (half_power_normalizes depth))
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.ofNat_succ_mul_invSucc n))))

def meshRemainder (depth steps : Nat) (x : Completion) : Completion :=
  completedSub (completedSub (twoStepTransfer x) (time depth steps (twoStepTransfer x)))
    (completedSmul (value ⟨depth,steps⟩) (derivativeAction x))

theorem remainder_quotient (depth n : Nat) (x : Completion) :
    meshRemainder depth (n+1) x=
      completedSmul (value ⟨depth,n+1⟩) (completedSub (meshQuotient depth n x) (derivativeAction x)) := by
  rw [smul_sub]
  unfold meshQuotient meshRemainder
  rw [completedSmul_mul,completedSmul_congr (mesh_normalization depth n),completedSmul_one]

theorem fine_taylor_bound (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon)
    (depth n : Nat) (hd : meshDepth X epsilon≤depth) (ht : value ⟨depth,n+1⟩≤meshRadius X epsilon) :
    RCle (B (meshRemainder depth (n+1) (point X)) (meshRemainder depth (n+1) (point X)))
      (rat ((value ⟨depth,n+1⟩*value ⟨depth,n+1⟩)*epsilon)) := by
  rw [remainder_quotient,smul_norm]
  exact RCscale_mono (SumOfSquares.q_mul_self_nonneg _) (mesh_quotient_bound X epsilon he depth n hd ht)

theorem remainder_refine (depth steps extra : Nat) (x : Completion) :
    meshRemainder (depth+extra) (steps*2^extra) x=meshRemainder depth steps x := by
  have hv : Q'.eqv (value ⟨depth+extra,steps*2^extra⟩) (value ⟨depth,steps⟩) :=
    value_refine ⟨depth,steps⟩ extra
  unfold meshRemainder
  rw [time_refinement_power,completedSmul_congr hv]

/-- EVERY dyadic mesh, including zero and coarse presentations, with one computed radius. -/
theorem mesh_taylor_bound (X : seminorm.Cauchy) (epsilon : Q') (he : (0 : Q')<epsilon)
    (depth steps : Nat) (ht : value ⟨depth,steps⟩≤meshRadius X epsilon) :
    RCle (B (meshRemainder depth steps (point X)) (meshRemainder depth steps (point X)))
      (rat ((value ⟨depth,steps⟩*value ⟨depth,steps⟩)*epsilon)) := by
  let k := meshDepth X epsilon
  have href : Q'.eqv (value ⟨depth+k,steps*2^k⟩) (value ⟨depth,steps⟩) := value_refine ⟨depth,steps⟩ k
  have ht' : value ⟨depth+k,steps*2^k⟩≤meshRadius X epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv href) ht
  have hd : meshDepth X epsilon≤depth+k := Nat.le_add_left k depth
  cases hsteps : steps*2^k with
  | zero =>
      have hz : steps=0 := (Nat.mul_eq_zero.mp hsteps).resolve_right (Nat.ne_of_gt (Nat.pow_pos (by decide)))
      subst steps
      have hv : Q'.eqv (value ⟨depth,0⟩) 0 := by
        change (0 : Int)*1=0*((value ⟨depth,0⟩).den : Int)
        simp only [Int.zero_mul]
      unfold meshRemainder
      change RCle (B (completedSub (completedSub (twoStepTransfer (point X)) (twoStepTransfer (point X)))
        (completedSmul (value ⟨depth,0⟩) (derivativeAction (point X)))) _) _
      simp only [completedSub_self,completedSmul_congr hv,completedSmul_zero,completedSub_zero,completedInner_zero_left]
      exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.mul_nonneg _ _
        (SumOfSquares.q_mul_self_nonneg _) (Q'.le_of_lt he))
  | succ n =>
      have hb := fine_taylor_bound X epsilon he (depth+k) n hd (by simpa only [hsteps] using ht')
      have hstate : meshRemainder (depth+k) (n+1) (point X)=meshRemainder depth steps (point X) := by
        rw [← hsteps]
        exact remainder_refine depth steps k (point X)
      rw [hstate] at hb
      have hv : Q'.eqv (value ⟨depth+k,n+1⟩) (value ⟨depth,steps⟩) := by simpa only [hsteps] using href
      have hsquare : Q'.eqv ((value ⟨depth+k,n+1⟩*value ⟨depth+k,n+1⟩)*epsilon)
          ((value ⟨depth,steps⟩*value ⟨depth,steps⟩)*epsilon) :=
        Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hv)
          (Q'.mul_eqv_congr_left _ _ _ hv))
      exact RCle_trans hb (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv hsquare))

end YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.meshQuotient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.meshQuotient_average
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.derivativeRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.derivativeRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.meshDepth
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.meshRadius
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.meshRadius_positive
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.timeAverage_derivative_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.mesh_quotient_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.mesh_value
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.mesh_normalization
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.meshRemainder
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.remainder_quotient
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.fine_taylor_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.remainder_refine
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicMeshDerivative.mesh_taylor_bound
