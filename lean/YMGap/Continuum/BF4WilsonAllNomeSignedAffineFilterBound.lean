/-
# Sharp endpoint cap for an actual signed affine time filter

On the SAME original Wilson completion, y=a*x+b*T*x has every-lag
response bounded by K times the response of x whenever a^2<=K and
(a+b)^2<=K. The exact chord remainder retains the signed cross term;
its three payments are positive original time/defect moments.

No spectral measure, source floor, vacuum exclusion, normalization inverse,
new observable or changing-family retention premise is introduced. This
source-preserving estimate does not produce the missing quantitative margin
or any continuum, physical Hamiltonian or gap conclusion.
-/

import YMGap.Continuum.BF4WilsonAllNomeBilinearTime
import YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments

namespace YMGap.Continuum.BF4WilsonAllNomeSignedAffineFilterBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation:max "R" x:arg n:arg => B x (T n x)
local notation:max "Y" x:arg a:arg b:arg => A (S a x) (S b (T 1 x))
attribute [local irreducible] completedInner completedTime

private theorem collect_cross (a b : Q') (r s t : RC) :
    RCadd (RCscale a (RCadd (RCscale a r) (RCscale b s)))
      (RCscale b (RCadd (RCscale a s) (RCscale b t))) =
    RCadd (RCadd (RCscale (a*a) r) (RCscale (2*a*b) s)) (RCscale (b*b) t) := by
  refine Quotient.inductionOn₃ r s t ?_
  intro X Z W
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.add (.mul (.var 0) (.var 2))
        (.mul (.var 1) (.var 3))))
        (.mul (.var 1) (.add (.mul (.var 0) (.var 3))
          (.mul (.var 1) (.var 4)))))
      (.add (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
        (.mul (.mul (.mul (.const 2) (.var 0)) (.var 1)) (.var 3)))
        (.mul (.mul (.var 1) (.var 1)) (.var 4)))
      (by decide) (fun | 0 => a | 1 => b | 2 => X.approx n | 3 => Z.approx n | _ => W.approx n)))

/-- Actual signed cross term, on the existing carrier and physical time map. -/
theorem affine_response_expand (x : V) (a b : Q') (n : Nat) :
    R (Y x a b) n =
      RCadd (RCadd (RCscale (a*a) (R x n)) (RCscale (2*a*b) (R x (n+1))))
        (RCscale (b*b) (R x (n+2))) := by
  have h01 : B x (T n (T 1 x)) = R x (n+1) := by
    rw [← completedTime_add]
  have h10 : B (T 1 x) (T n x) = R x (n+1) := by
    rw [completedInner_time_sum, show 1+n=n+1 by omega]
  have h11 : B (T 1 x) (T n (T 1 x)) = R x (n+2) := by
    rw [← completedTime_add, completedInner_time_sum, show 1+(n+1)=n+2 by omega]
  simp only [completedTime_additive, completedTime_smul, completedInner_add_left,
    completedInner_add_right, completedInner_smul_left, completedInner_smul_right, h01, h10, h11]
  exact collect_cross a b (R x n) (R x (n+1)) (R x (n+2))

private theorem chord_scalar (a b K : Q') (r s t : RC) :
    RCsub (RCscale K r)
      (RCadd (RCadd (RCscale (a*a) r) (RCscale (2*a*b) s)) (RCscale (b*b) t)) =
    RCadd (RCadd (RCscale (K-a*a) (RCsub r s)) (RCscale (K-(a+b)*(a+b)) s))
      (RCscale (b*b) (RCsub s t)) := by
  refine Quotient.inductionOn₃ r s t ?_
  intro X Z W
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 3))
        (.neg (.add (.add (.mul (.mul (.var 1) (.var 1)) (.var 3))
          (.mul (.mul (.mul (.const 2) (.var 1)) (.var 2)) (.var 4)))
          (.mul (.mul (.var 2) (.var 2)) (.var 5)))))
      (.add (.add (.mul (.add (.var 0) (.neg (.mul (.var 1) (.var 1))))
        (.add (.var 3) (.neg (.var 4))))
        (.mul (.add (.var 0) (.neg (.mul (.add (.var 1) (.var 2))
          (.add (.var 1) (.var 2))))) (.var 4)))
        (.mul (.mul (.var 2) (.var 2)) (.add (.var 4) (.neg (.var 5)))))
      (by decide) (fun | 0 => K | 1 => a | 2 => b | 3 => X.approx n | 4 => Z.approx n | _ => W.approx n)))

/-- Exact chord remainder; no endpoint-cap or response sign is assumed here. -/
theorem affine_chord_remainder (x : V) (a b K : Q') (n : Nat) :
    RCsub (RCscale K (R x n)) (R (Y x a b) n) =
      RCadd (RCadd (RCscale (K-a*a) (RCsub (R x n) (R x (n+1))))
        (RCscale (K-(a+b)*(a+b)) (R x (n+1))))
        (RCscale (b*b) (RCsub (R x (n+1)) (R x (n+2)))) := by
  rw [affine_response_expand]
  exact chord_scalar a b K (R x n) (R x (n+1)) (R x (n+2))

private theorem add_sub_first (a b : RC) : RCsub (RCadd a b) a = b := by
  refine Quotient.inductionOn₂ a b ?_
  intro X Z
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq (.add (.add (.var 0) (.var 1)) (.neg (.var 0)))
      (.var 1) (by decide) (fun | 0 => X.approx n | _ => Z.approx n)))

private theorem first_defect_pin (x : V) (n : Nat) :
    RCsub (R x n) (R x (n+1)) = mixedMoment hw0 hw1 x n 1 := by
  have h := mixedMoment_split hw0 hw1 x n 0
  change R x n = RCadd (R x (n+1)) (mixedMoment hw0 hw1 x n 1) at h
  rw [h, add_sub_first]

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (X.approx n))))

private theorem add_nonnegative {a b : RC} (ha : RCnonneg a) (hb : RCnonneg b) :
    RCnonneg (RCadd a b) := by
  have h := RCadd_le_add ha hb
  rwa [zero_add] at h

private theorem scale_nonnegative (c : Q') (hc : (0 : Q') ≤ c) {a : RC}
    (ha : RCnonneg a) : RCnonneg (RCscale c a) := by
  have h := RCscale_mono hc ha
  rwa [RCscale_RCzero] at h

private theorem le_of_sub_nonnegative {a b : RC} (h : RCnonneg (RCsub a b)) : RCle b a := by
  have hs : RCadd (RCsub a b) b = a := by
    refine Quotient.inductionOn₂ a b ?_
    intro X Z
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.sub_add_cancel_eqv (X.approx n) (Z.approx n)))
  have h' := RCadd_le_add h (RCle_refl b)
  rwa [zero_add, hs] at h'

/-- Every lag, including zero, vacuum and boundary time-kernel components.
Only the two literal rational endpoint caps are required. -/
theorem affine_response_le (x : V) (a b K : Q') (n : Nat)
    (h0 : a*a ≤ K) (h1 : (a+b)*(a+b) ≤ K) :
    RCle (R (Y x a b) n) (RCscale K (R x n)) := by
  apply le_of_sub_nonnegative
  rw [affine_chord_remainder hw0 hw1 x a b K n, first_defect_pin hw0 hw1 x n,
    show n+2=(n+1)+1 by omega, first_defect_pin hw0 hw1 x (n+1)]
  exact add_nonnegative
    (add_nonnegative
      (scale_nonnegative (K-a*a) (Q'.sub_nonneg_of_le h0)
        (mixedMoment_nonnegative hw0 hw1 x n 1))
      (scale_nonnegative (K-(a+b)*(a+b)) (Q'.sub_nonneg_of_le h1)
        (mixedMoment_nonnegative hw0 hw1 x (n+1) 0)))
    (scale_nonnegative (b*b) (SumOfSquares.q_mul_self_nonneg b)
      (mixedMoment_nonnegative hw0 hw1 x (n+1) 1))

/-- Literal rational endpoint maximum; computed from the supplied signed coefficients. -/
def affineEndpointCap (a b : Q') : Q' := Q'.max' (a*a) ((a+b)*(a+b))

/-- Computed endpoint maximum, with no absolute-value cross-term loss. -/
theorem affine_response_le_endpointMax (x : V) (a b : Q') (n : Nat) :
    RCle (R (Y x a b) n)
      (RCscale (affineEndpointCap a b) (R x n)) :=
  affine_response_le hw0 hw1 x a b _ n (Q'.le_max'_left _ _) (Q'.le_max'_right _ _)

end YMGap.Continuum.BF4WilsonAllNomeSignedAffineFilterBound

#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedAffineFilterBound.affine_response_expand
#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedAffineFilterBound.affine_chord_remainder
#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedAffineFilterBound.affine_response_le
#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedAffineFilterBound.affineEndpointCap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSignedAffineFilterBound.affine_response_le_endpointMax
