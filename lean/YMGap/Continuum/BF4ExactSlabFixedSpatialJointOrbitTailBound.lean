/- # Finite geometric bound for the even Neumann tail -/

import YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitCauchy
import YMGap.Continuum.RingNormaliser
import YMGap.Continuum.LargeFieldSuppression

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointLinear
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCompletedInner
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointBilinearTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitCauchy

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => JointCompletion hw0 hw1 width
local notation "B" => completedInner hw0 hw1 width
local notation "T" => jointCompletedTime hw0 hw1 width
local notation "U" => jointCompletedUnit hw0 hw1 width
local notation "q" => twoStepRate hw0 hw1 width

/-- The literal rational coefficient of a tail.  Keeping this recursion in
lockstep with `evenOrbitTail` makes the RC induction independent of division. -/
def tailCoeff (r : Q') (start : Nat) : Nat → Q'
  | 0 => 0
  | n+1 => tailCoeff r start n + r^(start+n)

private theorem scale_zero (z : RC) : RCscale 0 z = RCzero := by
  refine Quotient.inductionOn z ?_
  intro Z
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_zero_mul (Z.approx n)))

private theorem scale_add (a b : Q') (z : RC) :
    RCscale (a+b) z = RCadd (RCscale a z) (RCscale b z) := by
  refine Quotient.inductionOn z ?_
  intro Z
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_mul_eqv a b (Z.approx n)))

private theorem scale_congr {a b : Q'} (h : a.eqv b) (z : RC) :
    RCscale a z = RCscale b z := by
  refine Quotient.inductionOn z ?_
  intro Z
  exact Quotient.sound (YMGap.Continuum.Pivot2.mul_congr_left
    (CReal.ofQ'_equiv_of_eqv h))

/-- Additivity for the actual `HPow.hPow` powers used by the completed-time
contraction estimates. -/
theorem pow_add_eqv (a : Q') (m : Nat) : ∀ n : Nat,
    (a^(m+n)).eqv (a^m * a^n)
  | 0 => Q'.eqv_symm (Q'.mul_one_eqv (a^m))
  | n+1 => by
      show (a^(m+n+1)).eqv (a^m * a^(n+1))
      rw [Q'.pow_succ, Q'.pow_succ]
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (pow_add_eqv a m n)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv a (a^m) (a^n))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv a (a^m))) ?_
      exact Q'.mul_assoc_eqv (a^m) a (a^n)

/-- The strict `RGTransport.qpow` fold used by `geomSum` represents the same
rational value as the actual `HPow.hPow` fold used by contraction. -/
theorem rg_qpow_eqv_pow (a : Q') : ∀ n : Nat,
    (RGTransport.qpow a n).eqv (a^n)
  | 0 => Q'.eqv_refl _
  | n+1 => by
      rw [Q'.pow_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (RGTransport.qpow a n) (a^n) a
          (rg_qpow_eqv_pow a n)) ?_
      exact Q'.mul_comm_eqv (a^n) a

theorem tailCoeff_eqv_geom (r : Q') (p : Nat) : ∀ l : Nat,
    (tailCoeff r p l).eqv (r^p * geomSum r l)
  | 0 => by
      simp only [tailCoeff, geomSum_zero]
      exact Q'.eqv_symm (Q'.mul_zero_eqv (r^p))
  | l+1 => by
      simp only [tailCoeff, geomSum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (tailCoeff r p l) (r^p * geomSum r l)
          (r^(p+l)) (tailCoeff_eqv_geom r p l)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (r^p * geomSum r l) (r^(p+l))
          (r^p * r^l) (pow_add_eqv r p l)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (r^p * geomSum r l) (r^p * r^l)
          (r^p * RGTransport.qpow r l)
          (Q'.mul_eqv_congr_left (r^p) (r^l) (RGTransport.qpow r l)
            (Q'.eqv_symm (rg_qpow_eqv_pow r l)))) ?_
      exact RingNormaliser.poly_identity_of_normal_eq
        (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
        (.mul (.var 0) (.add (.var 1) (.var 2))) (by decide)
        (fun | 0 => r^p | 1 => geomSum r l | _ => RGTransport.qpow r l)

/-- Mixed tail/orbit estimate with the exact recursively accumulated
coefficient.  All cross terms are retained. -/
theorem even_translate_tail_le (x : V) (hx : B x U = RCzero) (i p : Nat) : ∀ l : Nat,
    RCle (B (T (2*i) x) (evenOrbitTail hw0 hw1 width x p l))
      (RCscale (q^i * tailCoeff q p l) (B x x))
  | 0 => by
      rw [evenOrbitTail, completedInner_zero_right, tailCoeff]
      have hz : (q^i * 0).eqv 0 := Q'.mul_zero_eqv (q^i)
      rw [scale_congr hz, scale_zero]
      exact RCle_refl _
  | l+1 => by
      rw [evenOrbitTail, completedInner_add_right, tailCoeff]
      have hs := RCadd_le_add (even_translate_tail_le x hx i p l)
        (even_cross_term_le hw0 hw1 width x hx i (p+l))
      refine RCle_trans hs ?_
      rw [← scale_add]
      have hc : (q^i * tailCoeff q p l + q^(i+(p+l))).eqv
          (q^i * (tailCoeff q p l + q^(p+l))) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (q^i * tailCoeff q p l) (q^(i+(p+l)))
            (q^i * q^(p+l)) (pow_add_eqv q i (p+l))) ?_
        exact RingNormaliser.poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
          (.mul (.var 0) (.add (.var 1) (.var 2))) (by decide)
          (fun | 0 => q^i | 1 => tailCoeff q p l | _ => q^(p+l))
      rw [scale_congr hc]
      exact RCle_refl _

/-- The squared norm of the literal finite tail is bounded by the square of
its exact geometric coefficient. -/
theorem evenOrbitTail_norm_le (x : V) (hx : B x U = RCzero) (p : Nat) : ∀ l : Nat,
    RCle (B (evenOrbitTail hw0 hw1 width x p l)
        (evenOrbitTail hw0 hw1 width x p l))
      (RCscale ((tailCoeff q p l) * (tailCoeff q p l)) (B x x))
  | 0 => by
      rw [evenOrbitTail, completedInner_zero_left, tailCoeff]
      have hz : ((0 : Q') * 0).eqv 0 := Q'.zero_mul_eqv 0
      rw [scale_congr hz, scale_zero]
      exact RCle_refl _
  | l+1 => by
      let c := tailCoeff q p l
      let a := q^(p+l)
      rw [evenOrbitTail, completedInner_add_left, completedInner_add_right,
        completedInner_add_right, tailCoeff]
      have hmix := even_translate_tail_le hw0 hw1 width x hx (p+l) p l
      have hmix' : RCle
          (B (evenOrbitTail hw0 hw1 width x p l) (T (2*(p+l)) x))
          (RCscale (a*c) (B x x)) := by
        rw [completedInner_symm]
        simpa only [a, c] using hmix
      have hdiag := even_cross_term_le hw0 hw1 width x hx (p+l) (p+l)
      have hs := RCadd_le_add
        (RCadd_le_add (evenOrbitTail_norm_le x hx p l) hmix')
        (RCadd_le_add hmix hdiag)
      refine RCle_trans hs ?_
      rw [← scale_add, ← scale_add, ← scale_add]
      have hc : (c*c + a*c + (q^(p+l)*c + q^((p+l)+(p+l)))).eqv
          ((c+a)*(c+a)) := by
        refine Q'.eqv_trans _ ((c*c + a*c) + (a*c + a*a)) _ ?_ ?_
        · exact Q'.add_eqv_congr_left (c*c + a*c) _ _
            (Q'.add_eqv_congr_left (a*c) _ _ (pow_add_eqv q (p+l) (p+l)))
        · exact RingNormaliser.poly_identity_of_normal_eq
            (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 0)))
              (.add (.mul (.var 1) (.var 0)) (.mul (.var 1) (.var 1))))
            (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))) (by decide)
            (fun | 0 => c | _ => a)
      rw [scale_congr hc]
      exact RCle_refl _

/-- Displayed geometric form of the finite tail estimate. -/
theorem evenOrbitTail_geometric_norm_le (x : V) (hx : B x U = RCzero)
    (p l : Nat) :
    RCle (B (evenOrbitTail hw0 hw1 width x p l)
        (evenOrbitTail hw0 hw1 width x p l))
      (RCscale ((q^p * geomSum q l) * (q^p * geomSum q l)) (B x x)) := by
  refine RCle_trans (evenOrbitTail_norm_le hw0 hw1 width x hx p l) ?_
  have hc := tailCoeff_eqv_geom q p l
  have hsquare : ((tailCoeff q p l) * (tailCoeff q p l)).eqv
      ((q^p * geomSum q l) * (q^p * geomSum q l)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (tailCoeff q p l) (q^p * geomSum q l)
        (tailCoeff q p l) hc)
      (Q'.mul_eqv_congr_left (q^p * geomSum q l) (tailCoeff q p l)
        (q^p * geomSum q l) hc)
  rw [scale_congr hsquare]
  exact RCle_refl _

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound.even_translate_tail_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound.pow_add_eqv
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound.rg_qpow_eqv_pow
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound.evenOrbitTail_norm_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound.tailCoeff_eqv_geom
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound.evenOrbitTail_geometric_norm_le

end YMGap.Continuum.BF4ExactSlabFixedSpatialJointOrbitTailBound
