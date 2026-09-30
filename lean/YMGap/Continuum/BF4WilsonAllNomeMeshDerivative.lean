/-
# Every-small-dyadic-increment derivative on the original Wilson range

A multi-step difference quotient is the finite time average of the actual
single-step quotients. Only continuity of their constructed limit is used;
the original carrier's boundary kernel forbids assuming full-space C0.
Mesh refinement removes the depth threshold from the Taylor remainder.
The resulting radius is computed from supplied original representatives.

One time unit remains the original T(1). This does not assert a real-time
derivative, a self-adjoint generator, physical calibration or Clay closure.
-/

import YMGap.Constructive.DyadicTimeRationals
import YMGap.Continuum.BF4WilsonAllNomeTimeAverages
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeContinuity
import YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit

namespace YMGap.Continuum.BF4WilsonAllNomeMeshDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint embed)
open YMGap.Constructive.DyadicTimeRationals
  (value value_num value_den value_le_iff value_refine half_power_num half_power_den)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit (completedSub_zero)
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (half_power_normalizes)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeContinuity
open YMGap.Continuum.BF4WilsonAllNomeTimeAverages
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "PD" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "S" => meshAction hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

def meshQuotient (depth n : Nat) (x : V) : V :=
  completedSmul hw0 hw1 (Q'.ofNat (2^depth)*Q'.invSucc n)
    (completedSub hw0 hw1 (T 1 x) (S depth (n+1) (T 1 x)))

theorem meshQuotient_average (depth n : Nat) (x : V) :
    meshQuotient hw0 hw1 depth n x =
      timeAverage hw0 hw1 depth n (differenceQuotient hw0 hw1 depth x) := by
  unfold differenceQuotient
  have h : timeAverage hw0 hw1 depth n
      (completedSmul hw0 hw1 (Q'.ofNat (2^depth))
        (BF4WilsonAllNomeDyadicDefectDecay.defect hw0 hw1 depth (T 1 x))) =
      completedSmul hw0 hw1 (Q'.ofNat (2^depth))
        (timeAverage hw0 hw1 depth n
          (BF4WilsonAllNomeDyadicDefectDecay.defect hw0 hw1 depth (T 1 x))) := by
    unfold timeAverage
    have hs (j : Nat) (c : Q') (z : V) :
        S depth j (completedSmul hw0 hw1 c z) =
          completedSmul hw0 hw1 c (S depth j z) :=
      action_smul hw0 hw1 (embed ⟨depth,j⟩) c z
    simp only [hs, average_smul]
  rw [h,timeAverage_defect,completedSmul_mul]
  rfl

def meshDepth (X : (PD).Cauchy) (epsilon : Q') : Nat :=
  derivativeRate hw0 hw1 X (quarter epsilon)

def meshRadius (X : (PD).Cauchy) (epsilon : Q') : Q' :=
  value ⟨derivativeContinuityModulus hw0 hw1 X (quarter epsilon),1⟩

theorem meshRadius_positive (X : (PD).Cauchy) (epsilon : Q') :
    (0 : Q') < meshRadius hw0 hw1 X epsilon := by
  change (0 : Int) * ((meshRadius hw0 hw1 X epsilon).den : Int) < 1*1
  simp only [Int.zero_mul,Int.one_mul]
  decide

theorem timeAverage_derivative_close (X : (PD).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (depth n : Nat)
    (ht : value ⟨depth,n+1⟩ ≤ meshRadius hw0 hw1 X epsilon) :
    RCle (dist (timeAverage hw0 hw1 depth n (A (Class X))) (A (Class X)))
      (rat (quarter epsilon)) := by
  apply timeAverage_close hw0 hw1
  intro j hj
  apply derivative_smallTime hw0 hw1 X (quarter epsilon) (quarter_pos he) depth j
  have hsteps := (value_le_iff ⟨depth,n+1⟩
    ⟨derivativeContinuityModulus hw0 hw1 X (quarter epsilon),1⟩).mp ht
  simp only [Nat.one_mul] at hsteps
  exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_of_lt hj)) hsteps

/-- The mesh threshold and radius use only supplied original input/output data. -/
theorem mesh_quotient_bound (X : (PD).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) (depth n : Nat)
    (hd : meshDepth hw0 hw1 X epsilon ≤ depth)
    (ht : value ⟨depth,n+1⟩ ≤ meshRadius hw0 hw1 X epsilon) :
    RCle (dist (meshQuotient hw0 hw1 depth n (Class X)) (A (Class X)))
      (rat epsilon) := by
  rw [meshQuotient_average]
  exact CRealSeminormCompletedApproximation.completedDist_two_segment
    (distanceData hw0 hw1 (width := width)) _
    (timeAverage hw0 hw1 depth n (A (Class X))) _ epsilon
    (RCle_trans (timeAverage_contraction hw0 hw1 depth n _ _)
      (derivative_bound hw0 hw1 X (quarter epsilon) (quarter_pos he) depth hd))
    (timeAverage_derivative_close hw0 hw1 X epsilon he depth n ht)

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
  have h := Q'.mul_eqv_congr_right _ _ (Q'.ofNat (2^depth)*Q'.invSucc n)
    (mesh_value depth (n+1))
  have hr : Q'.eqv ((Q'.ofNat (n+1)*HalfPow.half^depth)*(Q'.ofNat (2^depth)*Q'.invSucc n))
      ((HalfPow.half^depth*Q'.ofNat (2^depth))*(Q'.ofNat (n+1)*Q'.invSucc n)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3))) (by decide)
      (fun | 0 => Q'.ofNat (n+1) | 1 => HalfPow.half^depth | 2 => Q'.ofNat (2^depth) | _ => Q'.invSucc n)
  exact Q'.eqv_trans _ _ _ h (Q'.eqv_trans _ _ _ hr
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (half_power_normalizes depth))
      (Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.ofNat_succ_mul_invSucc n))))

def meshRemainder (depth steps : Nat) (x : V) : V :=
  completedSub hw0 hw1 (completedSub hw0 hw1 (T 1 x) (S depth steps (T 1 x)))
    (completedSmul hw0 hw1 (value ⟨depth,steps⟩) (A x))

theorem remainder_quotient (depth n : Nat) (x : V) :
    meshRemainder hw0 hw1 depth (n+1) x =
      completedSmul hw0 hw1 (value ⟨depth,n+1⟩)
        (completedSub hw0 hw1 (meshQuotient hw0 hw1 depth n x) (A x)) := by
  rw [smul_sub]
  unfold meshQuotient meshRemainder
  rw [completedSmul_mul,completedSmul_congr hw0 hw1 (mesh_normalization depth n),
    completedSmul_one]

theorem fine_taylor_bound (X : (PD).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (depth n : Nat) (hd : meshDepth hw0 hw1 X epsilon ≤ depth)
    (ht : value ⟨depth,n+1⟩ ≤ meshRadius hw0 hw1 X epsilon) :
    RCle (B (meshRemainder hw0 hw1 depth (n+1) (Class X))
      (meshRemainder hw0 hw1 depth (n+1) (Class X)))
      (rat ((value ⟨depth,n+1⟩*value ⟨depth,n+1⟩)*epsilon)) := by
  rw [remainder_quotient,completedInner_smul_left,completedInner_smul_right,RCscale_RCscale]
  have h := RCscale_mono (SumOfSquares.q_mul_self_nonneg (value ⟨depth,n+1⟩))
    (mesh_quotient_bound hw0 hw1 X epsilon he depth n hd ht)
  have hs : RCscale (value ⟨depth,n+1⟩*value ⟨depth,n+1⟩) (rat epsilon) =
      rat ((value ⟨depth,n+1⟩*value ⟨depth,n+1⟩)*epsilon) :=
    Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
  rw [hs] at h
  exact h

theorem remainder_refine (depth steps extra : Nat) (x : V) :
    meshRemainder hw0 hw1 (depth+extra) (steps*2^extra) x =
      meshRemainder hw0 hw1 depth steps x := by
  have hv : Q'.eqv (value ⟨depth+extra,steps*2^extra⟩) (value ⟨depth,steps⟩) :=
    value_refine ⟨depth,steps⟩ extra
  unfold meshRemainder
  rw [mesh_refinement,completedSmul_congr hw0 hw1 hv]

/-- One computed radius controls EVERY mesh, including zero and coarse presentations. -/
theorem mesh_taylor_bound (X : (PD).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon)
    (depth steps : Nat) (ht : value ⟨depth,steps⟩ ≤ meshRadius hw0 hw1 X epsilon) :
    RCle (B (meshRemainder hw0 hw1 depth steps (Class X))
      (meshRemainder hw0 hw1 depth steps (Class X)))
      (rat ((value ⟨depth,steps⟩*value ⟨depth,steps⟩)*epsilon)) := by
  let k := meshDepth hw0 hw1 X epsilon
  have href : Q'.eqv (value ⟨depth+k,steps*2^k⟩) (value ⟨depth,steps⟩) :=
    value_refine ⟨depth,steps⟩ k
  have ht' : value ⟨depth+k,steps*2^k⟩ ≤ meshRadius hw0 hw1 X epsilon :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv href) ht
  have hd : meshDepth hw0 hw1 X epsilon ≤ depth+k := Nat.le_add_left k depth
  cases hsteps : steps*2^k with
  | zero =>
      have hz : steps=0 := (Nat.mul_eq_zero.mp hsteps).resolve_right
        (Nat.ne_of_gt (Nat.pow_pos (by decide)))
      subst steps
      have hv : Q'.eqv (value ⟨depth,0⟩) 0 := by
        change (0 : Int)*1=0*((value ⟨depth,0⟩).den : Int)
        simp only [Int.zero_mul]
      unfold meshRemainder
      change RCle (B (completedSub hw0 hw1
        (completedSub hw0 hw1 (T 1 (Class X)) (T 1 (Class X)))
        (completedSmul hw0 hw1 (value ⟨depth,0⟩) (A (Class X)))) _) _
      simp only [completedSub_self,completedSmul_congr hw0 hw1 hv,
        completedSmul_zero,completedSub_zero,completedInner_zero_left]
      exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.mul_nonneg _ _
        (SumOfSquares.q_mul_self_nonneg _) (Q'.le_of_lt he))
  | succ n =>
      have hb := fine_taylor_bound hw0 hw1 X epsilon he (depth+k) n hd
        (by simpa only [hsteps] using ht')
      have hstate : meshRemainder hw0 hw1 (depth+k) (n+1) (Class X) =
          meshRemainder hw0 hw1 depth steps (Class X) := by
        rw [← hsteps]
        exact remainder_refine hw0 hw1 depth steps k (Class X)
      rw [hstate] at hb
      have hv : Q'.eqv (value ⟨depth+k,n+1⟩) (value ⟨depth,steps⟩) := by
        simpa only [hsteps] using href
      have hsquare : Q'.eqv ((value ⟨depth+k,n+1⟩*value ⟨depth+k,n+1⟩)*epsilon)
          ((value ⟨depth,steps⟩*value ⟨depth,steps⟩)*epsilon) :=
        Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hv) (Q'.mul_eqv_congr_left _ _ _ hv))
      exact RCle_trans hb (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_eqv hsquare))

def meshTaylorCertificate (X : (PD).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    {radius : Q' // (0 : Q') < radius ∧ ∀ depth steps,
      value ⟨depth,steps⟩ ≤ radius →
      RCle (B (meshRemainder hw0 hw1 depth steps (Class X))
        (meshRemainder hw0 hw1 depth steps (Class X)))
        (rat ((value ⟨depth,steps⟩*value ⟨depth,steps⟩)*epsilon))} :=
  ⟨meshRadius hw0 hw1 X epsilon,meshRadius_positive hw0 hw1 X epsilon,
    mesh_taylor_bound hw0 hw1 X epsilon he⟩

#print axioms meshQuotient
#print axioms meshQuotient_average
#print axioms meshDepth
#print axioms meshRadius
#print axioms meshRadius_positive
#print axioms timeAverage_derivative_close
#print axioms mesh_quotient_bound
#print axioms mesh_value
#print axioms mesh_normalization
#print axioms meshRemainder
#print axioms remainder_quotient
#print axioms fine_taylor_bound
#print axioms remainder_refine
#print axioms mesh_taylor_bound
#print axioms meshTaylorCertificate

end YMGap.Continuum.BF4WilsonAllNomeMeshDerivative
