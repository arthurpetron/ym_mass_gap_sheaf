/-
The actual shrinking-dyadic-time resolvent sequence on the original carrier.
For lambda,h>0, R_h=h*((1+lambda*h)I-root depth)^(-1).
Root squaring and positive mixed moments give the sharp adjacent squared
error h^2/4 on EVERY original vector, including the original time kernel.
The represented limit, sector membership and generator equation remain next.
The original time unit is not identified here with physical lattice spacing.
-/

import YMGap.Continuum.BF4WilsonAllNomeAdjacentRootResolvent

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicResolvent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeTimeAverages (smul_sub)
open YMGap.Continuum.BF4WilsonAllNomeShiftedRootResolvent
open YMGap.Continuum.BF4WilsonAllNomeAdjacentRootResolvent (scaled_difference_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "F" => denominator hw0 hw1
local notation "J" => inverse hw0 hw1
local notation "half" => HalfPow.half
local notation "D" => seminorm hw0 hw1 (width := width)
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))

/-- An actual resolvent approximant, not a supplied inverse. -/
def atStep (depth : Nat) (lambda h : Q')
    (hl : (0 : Q') < lambda) (hh : (0 : Q') < h) (x : V) : V :=
  S h (J depth (lambda*h) 1 (Q'.mul_pos hl hh) (by decide) x)

theorem atStep_equation (depth : Nat) (lambda h : Q')
    (hl : (0 : Q') < lambda) (hh : (0 : Q') < h) (x : V) :
    F depth (lambda*h) 1 (atStep hw0 hw1 depth lambda h hl hh x) = S h x := by
  unfold atStep
  rw [denominator_smul, inverse_right]

private theorem half_denominator (depth : Nat) (lambda h : Q') (y : V) :
    F depth (lambda*(half*h)) 1 y = S half (F depth (lambda*h) 2 y) := by
  have hp : Q'.eqv (half*((lambda*h)+2)) (lambda*(half*h)+half*2) :=
    poly_identity_of_normal_eq
      (.mul (.var 2) (.add (.mul (.var 0) (.var 1)) (.const 2)))
      (.add (.mul (.var 0) (.mul (.var 2) (.var 1))) (.mul (.var 2) (.const 2)))
      (by decide) (fun | 0 => lambda | 1 => h | _ => half)
  have hc := Q'.eqv_trans _ _ _ hp (Q'.add_eqv_congr_left _ _ _
    (by decide : Q'.eqv (half*2) 1))
  unfold denominator
  rw [smul_sub, completedSmul_mul, completedSmul_mul,
    completedSmul_congr hw0 hw1 hc,
    completedSmul_congr hw0 hw1 (by decide : Q'.eqv (half*2) 1)]

/-- The half-step approximant is exactly the other inverse in the comparison. -/
theorem half_step_pin (depth : Nat) (lambda h : Q')
    (hl : (0 : Q') < lambda) (hh : (0 : Q') < h) (x : V) :
    atStep hw0 hw1 (depth+1) lambda (half*h) hl
      (Q'.mul_pos (by decide) hh) x =
      S h (J (depth+1) (lambda*h) 2 (Q'.mul_pos hl hh) (by decide) x) := by
  let y := S h (J (depth+1) (lambda*h) 2 (Q'.mul_pos hl hh) (by decide) x)
  have hy : F (depth+1) (lambda*(half*h)) 1 y = S (half*h) x := by
    rw [half_denominator]
    dsimp only [y]
    rw [denominator_smul, inverse_right, completedSmul_mul]
  have he := inverse_unique hw0 hw1 (depth+1) (lambda*(half*h)) 1
    (Q'.mul_pos hl (Q'.mul_pos (by decide) hh)) (by decide) (S (half*h) x) y hy
  rw [inverse_smul] at he
  exact he.symm

/-- Every adjacent refinement has the sharp h^2/4 squared error. -/
theorem atStep_refinement_bound (depth : Nat) (lambda h : Q')
    (hl : (0 : Q') < lambda) (hh : (0 : Q') < h) (x : V) :
    RCle
      (B (Sub (atStep hw0 hw1 depth lambda h hl hh x)
          (atStep hw0 hw1 (depth+1) lambda (half*h) hl (Q'.mul_pos (by decide) hh) x))
        (Sub (atStep hw0 hw1 depth lambda h hl hh x)
          (atStep hw0 hw1 (depth+1) lambda (half*h) hl (Q'.mul_pos (by decide) hh) x)))
      (RCscale (h*h*(half*half)) (B x x)) := by
  rw [half_step_pin hw0 hw1 depth lambda h hl hh x]
  exact scaled_difference_bound hw0 hw1 depth (lambda*h) h (Q'.mul_pos hl hh) x

theorem dyadicStep_positive (depth : Nat) : (0 : Q') < half^depth := by
  induction depth with
  | zero => exact (by decide : (0 : Q') < 1)
  | succ n ih => exact Q'.mul_pos (by decide) ih

/-- The concrete sequence whose norm limit will construct the generator resolvent. -/
def dyadic (depth : Nat) (lambda : Q') (hl : (0 : Q') < lambda) (x : V) : V :=
  atStep hw0 hw1 depth lambda (half^depth) hl (dyadicStep_positive depth) x

theorem dyadic_step_bound (depth : Nat) (lambda : Q')
    (hl : (0 : Q') < lambda) (x : V) :
    RCle
      (B (Sub (dyadic hw0 hw1 depth lambda hl x) (dyadic hw0 hw1 (depth+1) lambda hl x))
        (Sub (dyadic hw0 hw1 depth lambda hl x) (dyadic hw0 hw1 (depth+1) lambda hl x)))
      (RCscale ((half^depth)*(half^depth)*(half*half)) (B x x)) := by
  exact atStep_refinement_bound hw0 hw1 depth lambda (half^depth)
    hl (dyadicStep_positive depth) x

/-- Computed original Cauchy representative for each approximant. -/
def dyadicRepresentative (depth : Nat) (lambda : Q')
    (hl : (0 : Q') < lambda) (X : (D).Cauchy) : (D).Cauchy :=
  (scalarContinuous hw0 hw1 (half^depth)).mapCauchy
    (inverseRepresentative hw0 hw1 depth (lambda*(half^depth)) 1
      (Q'.mul_pos hl (dyadicStep_positive depth)) (by decide) X)

theorem dyadicRepresentative_pin (depth : Nat) (lambda : Q')
    (hl : (0 : Q') < lambda) (X : (D).Cauchy) :
    Class (dyadicRepresentative hw0 hw1 depth lambda hl X) =
      dyadic hw0 hw1 depth lambda hl (Class X) := by
  change S (half^depth) (Class (inverseRepresentative hw0 hw1 depth (lambda*(half^depth)) 1
    (Q'.mul_pos hl (dyadicStep_positive depth)) (by decide) X)) = _
  rw [inverseRepresentative_pin]
  rfl

#print axioms atStep
#print axioms atStep_equation
#print axioms half_step_pin
#print axioms atStep_refinement_bound
#print axioms dyadicStep_positive
#print axioms dyadic
#print axioms dyadic_step_bound
#print axioms dyadicRepresentative
#print axioms dyadicRepresentative_pin

end YMGap.Continuum.BF4WilsonAllNomeDyadicResolvent
