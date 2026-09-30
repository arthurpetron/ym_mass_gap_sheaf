/-
# Original Wilson core increments controlled by the derivative image

The fixed dyadic increment of `T(1)x` is bounded by its actual derivative
image. Refinement is only a way to pass a norm estimate through the already
constructed quotient limit; no bound on an inverse or preimage is used.
-/

import YMGap.Continuum.BF4WilsonAllNomeMeshDerivative
import YMGap.Continuum.BF4WilsonAllNomeNormLimitOrder
import YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws

namespace YMGap.Continuum.BF4WilsonAllNomeDerivativeIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.DyadicTimeRationals (value)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws
open YMGap.Continuum.BF4WilsonAllNomeTimeAverages
open YMGap.Continuum.BF4WilsonAllNomeMeshDerivative
open YMGap.Continuum.BF4WilsonAllNomeNormLimitOrder (norm_limit_order)
open YMGap.Continuum.BF4ExactSlabThermodynamicResolventPartial (scale_congr)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "PD" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "S" => meshAction hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "d" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem refined_steps (n extra : Nat) :
    ((n+1)*2^extra-1)+1=(n+1)*2^extra := by
  have hp : 0 < 2^extra := Nat.pow_pos (by decide : 0<2)
  have hprod : 0 < (n+1)*2^extra := Nat.mul_pos (Nat.succ_pos n) hp
  omega

private theorem refined_coefficient (depth n extra : Nat) :
    Q'.eqv
      (Q'.ofNat (2^(depth+extra))*Q'.invSucc ((n+1)*2^extra-1))
      (Q'.ofNat (2^depth)*Q'.invSucc n) := by
  change
    (Q'.ofNat (2^(depth+extra))*Q'.invSucc ((n+1)*2^extra-1)).num *
      ((Q'.ofNat (2^depth)*Q'.invSucc n).den : Int) =
    (Q'.ofNat (2^depth)*Q'.invSucc n).num *
      ((Q'.ofNat (2^(depth+extra))*Q'.invSucc ((n+1)*2^extra-1)).den : Int)
  rw [Q'.ofNat_mul_invSucc_num,Q'.ofNat_mul_invSucc_den,
    Q'.ofNat_mul_invSucc_num,Q'.ofNat_mul_invSucc_den]
  have hs := refined_steps n extra
  have hs' : (((n+1)*2^extra-1 : Nat) : Int)+1 = ((n+1)*2^extra : Nat) := by
    exact_mod_cast hs
  rw [hs',Nat.pow_add]
  simp [Int.natCast_mul,Int.natCast_add,Int.mul_left_comm,Int.mul_comm]

theorem meshQuotient_refine (depth n extra : Nat) (x : V) :
    meshQuotient hw0 hw1 (depth+extra) ((n+1)*2^extra-1) x =
      meshQuotient hw0 hw1 depth n x := by
  unfold meshQuotient
  rw [refined_steps,mesh_refinement,
    completedSmul_congr hw0 hw1 (refined_coefficient depth n extra)]

/-- Refined averages of the actual derivative image converge, with the
quotient's supplied modulus, to a fixed coarse-time quotient. -/
theorem refined_average_close (X : (PD).Cauchy) (depth n : Nat)
    (epsilon : Q') (he : (0 : Q') < epsilon) (extra : Nat)
    (h : derivativeRate hw0 hw1 X epsilon ≤ extra) :
    RCle
      (d (timeAverage hw0 hw1 (depth+extra) ((n+1)*2^extra-1)
        (A (Class X))) (meshQuotient hw0 hw1 depth n (Class X)))
      (rat epsilon) := by
  rw [← meshQuotient_refine hw0 hw1 depth n extra (Class X),meshQuotient_average]
  have hb := timeAverage_contraction hw0 hw1 (depth+extra) ((n+1)*2^extra-1)
    (A (Class X)) (differenceQuotient hw0 hw1 (depth+extra) (Class X))
  exact RCle_trans hb (by
    rw [completedDist_symm]
    exact derivative_bound hw0 hw1 X epsilon he (depth+extra) (by omega))

/-- A fixed coarse-time quotient has norm at most the represented derivative
image norm. The approximating averages are on the same original carrier. -/
theorem meshQuotient_image_bound (depth n : Nat) (x : V) :
    RCle (B (meshQuotient hw0 hw1 depth n x)
      (meshQuotient hw0 hw1 depth n x)) (B (A x) (A x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  let f : Nat → V := fun k =>
    timeAverage hw0 hw1 (depth+k) ((n+1)*2^k-1) (A (Class X))
  have hclose : ∀ epsilon : Q', (0 : Q')<epsilon →
      ∀ k, derivativeRate hw0 hw1 X epsilon ≤ k →
      RCle (d (f k) (meshQuotient hw0 hw1 depth n (Class X))) (rat epsilon) := by
    intro epsilon he k hk
    exact refined_average_close hw0 hw1 X depth n epsilon he k hk
  have hconst : ∀ epsilon : Q', (0 : Q')<epsilon → ∀ k, 0≤k →
      RCle (d (A (Class X)) (A (Class X))) (rat epsilon) := by
    intro epsilon he k hk
    rw [(completedDist_zero_iff hw0 hw1 _ _).mpr rfl]
    exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt he)
  have hstage : ∀ k, RCle (B (f k) (f k)) (B (A (Class X)) (A (Class X))) := by
    intro k
    dsimp only [f,timeAverage]
    apply average_norm_bound hw0 hw1
    intro j hj
    exact mesh_norm_bound hw0 hw1 (depth+k) j (A (Class X))
  exact norm_limit_order hw0 hw1 f (fun _ => A (Class X))
    (meshQuotient hw0 hw1 depth n (Class X)) (A (Class X))
    (derivativeRate hw0 hw1 X) (fun _ => 0) hclose hconst hstage

theorem mesh_increment_quotient (depth n : Nat) (x : V) :
    completedSub hw0 hw1 (T 1 x) (S depth (n+1) (T 1 x)) =
      completedSmul hw0 hw1 (value ⟨depth,n+1⟩)
        (meshQuotient hw0 hw1 depth n x) := by
  unfold meshQuotient
  rw [completedSmul_mul,completedSmul_congr hw0 hw1
    (mesh_normalization depth n),completedSmul_one]

/-- Every dyadic increment of the original positive-time core `T(1)x` is
controlled by the norm of its constructed dyadic derivative image. -/
theorem mesh_increment_bound (depth steps : Nat) (x : V) :
    RCle (d (T 1 x) (S depth steps (T 1 x)))
      (RCscale (value ⟨depth,steps⟩*value ⟨depth,steps⟩)
        (B (A x) (A x))) := by
  cases steps with
  | zero =>
      change RCle (d (T 1 x) (T 1 x)) _
      rw [(completedDist_zero_iff hw0 hw1 _ _).mpr rfl]
      have h := RCscale_mono (SumOfSquares.q_mul_self_nonneg (value ⟨depth,0⟩))
        (completedInner_nonnegative hw0 hw1 (A x))
      rw [RCscale_RCzero] at h
      exact h
  | succ n =>
      unfold completedDist
      rw [mesh_increment_quotient,completedInner_smul_left,
        completedInner_smul_right,RCscale_RCscale]
      exact RCscale_mono (SumOfSquares.q_mul_self_nonneg _)
        (meshQuotient_image_bound hw0 hw1 depth n x)

#print axioms meshQuotient_refine
#print axioms refined_average_close
#print axioms meshQuotient_image_bound
#print axioms mesh_increment_quotient
#print axioms mesh_increment_bound

end YMGap.Continuum.BF4WilsonAllNomeDerivativeIncrement
