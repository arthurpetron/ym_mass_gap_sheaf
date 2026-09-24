/-
# Quadratic Taylor remainder for a finite product of truncated SU(2) modes

This is the scalar joint-mode ingredient only.  It does not construct a
multi-block harmonic expansion or an operator Taylor theorem.
-/

import YMGap.Continuum.SU2HeatCutoffTaylorRemainder
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2HeatProductTaylorRemainder

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2HeatCutoffTaylorRemainder

local infix:50 " ≈ " => Q'.eqv

/-- Product of the actual finite-cutoff attenuations of a degree vector. -/
def productAttenuation (w : Q') (K : Nat) : List Nat → Q'
  | [] => 1
  | d :: ds => attenuation w K d * productAttenuation w K ds

/-- Rational total Casimir of a degree vector. -/
def totalCasimir : List Nat → Q'
  | [] => 0
  | d :: ds => Q'.ofNat (d * (d + 2)) + totalCasimir ds

/-- First-order remainder of the actual product attenuation. -/
def productRemainder (w : Q') (K : Nat) (degrees : List Nat) : Q' :=
  (productAttenuation w K degrees - (1 : Q')) +
    ((1 : Q') - w) * totalCasimir degrees

private theorem productAttenuation_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K : Nat) : ∀ degrees : List Nat,
    (0 : Q') ≤ productAttenuation w K degrees
  | [] => by
      change (0 : Q') ≤ 1
      exact Q'.zero_le_one
  | d :: ds => Q'.mul_nonneg _ _ (attenuation_nonnegative hw0 K d)
      (productAttenuation_nonnegative hw0 K ds)

private theorem productAttenuation_le_one {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K : Nat) : ∀ degrees : List Nat,
    productAttenuation w K degrees ≤ (1 : Q')
  | [] => Q'.le_refl' 1
  | d :: ds => by
      have hp0 := productAttenuation_nonnegative hw0 K ds
      have ha1 := attenuation_le_one hw0 hw1 K d
      have hp1 := productAttenuation_le_one hw0 hw1 K ds
      have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ ha1 hp0
      have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ 1 hp1 (by decide)
      exact Q'.le_trans' _ _ _ hfirst
        (Q'.le_trans' _ _ _ hsecond (Q'.le_of_eqv (Q'.one_mul_eqv 1)))

private theorem totalCasimir_nonnegative : ∀ degrees : List Nat,
    (0 : Q') ≤ totalCasimir degrees
  | [] => Q'.le_refl' 0
  | _ :: ds => Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat (Nat.zero_le _))
      (Q'.add_le_self_of_nonneg _ _ (totalCasimir_nonnegative ds))

/-- The product loses at most the linear sum of its Casimirs. -/
theorem one_sub_productAttenuation_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K : Nat)
    (hguard : (1 : Q') ≤
      ((1 : Q') - w) * Q'.ofNat ((K + 1) * (K + 3))) :
    ∀ degrees : List Nat,
      (1 : Q') - productAttenuation w K degrees ≤
        ((1 : Q') - w) * totalCasimir degrees
  | [] => by
      exact Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.const 1) (.neg (.const 1)))
        (.mul (.var 0) (.const 0)) (by decide)
        (fun _ => (1 : Q') - w))
  | d :: ds => by
      let a := attenuation w K d
      let p := productAttenuation w K ds
      let eps := (1 : Q') - w
      let c := Q'.ofNat (d * (d + 2))
      let t := totalCasimir ds
      have ha0 : (0 : Q') ≤ a := attenuation_nonnegative hw0 K d
      have ha1 : a ≤ (1 : Q') := attenuation_le_one hw0 hw1 K d
      have ht0 : (0 : Q') ≤ t := totalCasimir_nonnegative ds
      have he0 : (0 : Q') ≤ eps := Q'.sub_nonneg_of_le hw1
      have hhead : (1 : Q') - a ≤ eps*c :=
        one_sub_attenuation_le hw0 hw1 K d hguard
      have htail : (1 : Q') - p ≤ eps*t :=
        one_sub_productAttenuation_le hw0 hw1 K hguard ds
      have htail0 : (0 : Q') ≤ eps*t := Q'.mul_nonneg _ _ he0 ht0
      have hamul := Q'.mul_le_mul_of_nonneg_left _ _ a htail ha0
      have hatop := Q'.mul_le_mul_of_nonneg_right a 1 (eps*t) ha1 htail0
      have hscaled : a*((1 : Q')-p) ≤ eps*t :=
        Q'.le_trans' _ _ _ hamul
          (Q'.le_trans' _ _ _ hatop (Q'.le_of_eqv (Q'.one_mul_eqv (eps*t))))
      have hadd := Q'.add_le_add hhead hscaled
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (poly_identity_of_normal_eq
          (.add (.const 1) (.neg (.mul (.var 0) (.var 1))))
          (.add (.add (.const 1) (.neg (.var 0)))
            (.mul (.var 0) (.add (.const 1) (.neg (.var 1)))))
          (by decide) (fun | 0 => a | _ => p)))
        (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv
          (poly_identity_of_normal_eq
            (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
            (.mul (.var 0) (.add (.var 1) (.var 2)))
            (by decide) (fun | 0 => eps | 1 => c | _ => t))))

/-- The joint first-order remainder is nonnegative, including when one or more
degrees are omitted by the cutoff. -/
theorem productRemainder_nonnegative {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K : Nat)
    (hguard : (1 : Q') ≤
      ((1 : Q') - w) * Q'.ofNat ((K + 1) * (K + 3)))
    (degrees : List Nat) :
    (0 : Q') ≤ productRemainder w K degrees := by
  have h := one_sub_productAttenuation_le hw0 hw1 K hguard degrees
  exact Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le h)
    (Q'.le_of_eqv (by
      unfold productRemainder
      exact poly_identity_of_normal_eq
        (.add (.var 1) (.neg (.add (.const 1) (.neg (.var 0)))))
        (.add (.add (.var 0) (.neg (.const 1))) (.var 1))
        (by decide) (fun
          | 0 => productAttenuation w K degrees
          | _ => ((1 : Q')-w)*totalCasimir degrees)))

private theorem productRemainder_le_square_aux {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K : Nat)
    (hguard : (1 : Q') ≤
      ((1 : Q') - w) * Q'.ofNat ((K + 1) * (K + 3))) :
    ∀ degrees : List Nat,
      productRemainder w K degrees ≤
        (((1 : Q') - w) * ((1 : Q') - w)) *
          (totalCasimir degrees * totalCasimir degrees)
  | [] => by
      exact Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.add (.const 1) (.neg (.const 1))) (.mul (.var 0) (.const 0)))
        (.mul (.mul (.var 0) (.var 0)) (.mul (.const 0) (.const 0)))
        (by decide) (fun _ => (1 : Q')-w))
  | d :: ds => by
      let a := attenuation w K d
      let eps := (1 : Q') - w
      let c := Q'.ofNat (d * (d + 2))
      let t := totalCasimir ds
      let r := cutoffRemainder w K d
      let R := productRemainder w K ds
      change productRemainder w K (d::ds) ≤ (eps*eps)*((c+t)*(c+t))
      have he0 : (0 : Q') ≤ eps := Q'.sub_nonneg_of_le hw1
      have ht0 : (0 : Q') ≤ t := totalCasimir_nonnegative ds
      have ha0 : (0 : Q') ≤ a := attenuation_nonnegative hw0 K d
      have ha1 : a ≤ (1 : Q') := attenuation_le_one hw0 hw1 K d
      have hr0 := cutoffRemainder_le_square hw0 hw1 K d hguard
      have hr : r ≤ (eps*eps)*(c*c) := Q'.le_trans' _ _ _ hr0
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv
            (d*(d+2)) (d*(d+2))))))
      have hR := productRemainder_le_square_aux hw0 hw1 K hguard ds
      have hdef := one_sub_attenuation_le hw0 hw1 K d hguard
      have hcross : eps*t*((1 : Q')-a) ≤ (eps*eps)*(t*c) := by
        have het0 : (0 : Q') ≤ eps*t := Q'.mul_nonneg _ _ he0 ht0
        have hm := Q'.mul_le_mul_of_nonneg_left _ _ _ hdef het0
        exact Q'.le_trans' _ _ _ hm (Q'.le_of_eqv
          (poly_identity_of_normal_eq
            (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
            (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2)))
            (by decide) (fun | 0 => eps | 1 => t | _ => c)))
      have haR := Q'.mul_le_mul_of_nonneg_left _ _ a hR ha0
      have hsq0 : (0 : Q') ≤ (eps*eps)*(t*t) := Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ he0 he0) (Q'.mul_nonneg _ _ ht0 ht0)
      have haR' : a*R ≤ (eps*eps)*(t*t) :=
        Q'.le_trans' _ _ _ haR
          (Q'.le_trans' _ _ _
            (Q'.mul_le_mul_of_nonneg_right a 1 ((eps*eps)*(t*t)) ha1 hsq0)
            (Q'.le_of_eqv (Q'.one_mul_eqv _)))
      have hsum := Q'.add_le_add (Q'.add_le_add hr haR') hcross
      have hmissing0 : (0 : Q') ≤ (eps*eps)*(c*t) := Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ he0 he0)
        (Q'.mul_nonneg _ _ (CReal.ofNat_le_ofNat (Nat.zero_le _)) ht0)
      have hcomplete := Q'.add_le_self_of_nonneg
        (((eps*eps)*(c*c) + (eps*eps)*(t*t)) + (eps*eps)*(t*c))
        ((eps*eps)*(c*t)) hmissing0
      have hdecomp : productRemainder w K (d::ds) ≈ r+a*R+eps*t*((1 : Q')-a) := by
        dsimp only [productRemainder, productAttenuation, totalCasimir, r, R, a, eps, c, t,
          cutoffRemainder]
        exact poly_identity_of_normal_eq
          (.add (.add (.mul (.var 0) (.var 1)) (.neg (.const 1)))
            (.mul (.var 2) (.add (.var 3) (.var 4))))
          (.add (.add
            (.add (.add (.var 0) (.neg (.const 1))) (.mul (.var 2) (.var 3)))
            (.mul (.var 0) (.add (.add (.var 1) (.neg (.const 1)))
              (.mul (.var 2) (.var 4)))))
            (.mul (.mul (.var 2) (.var 4)) (.add (.const 1) (.neg (.var 0)))))
          (by decide) (fun
            | 0 => attenuation w K d
            | 1 => productAttenuation w K ds
            | 2 => (1 : Q')-w
            | 3 => Q'.ofNat (d*(d+2))
            | _ => totalCasimir ds)
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hdecomp)
        (Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ hcomplete
          (Q'.le_of_eqv
            (poly_identity_of_normal_eq
              (.add
                (.add (.add
                  (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
                  (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))))
                  (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 1))))
                (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 2))))
              (.mul (.mul (.var 0) (.var 0))
                (.mul (.add (.var 1) (.var 2)) (.add (.var 1) (.var 2))))
              (by decide) (fun | 0 => eps | 1 => c | _ => t)))))

/-- Loose but uniform joint quadratic envelope for the actual truncated
product attenuation. -/
theorem productRemainder_le_square {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (K : Nat)
    (hguard : (1 : Q') ≤
      ((1 : Q') - w) * Q'.ofNat ((K + 1) * (K + 3)))
    (degrees : List Nat) :
    productRemainder w K degrees ≤
      (((1 : Q') - w) * ((1 : Q') - w)) *
        (totalCasimir degrees * totalCasimir degrees) :=
  productRemainder_le_square_aux hw0 hw1 K hguard degrees

/-- Computed-cutoff specialization of both joint remainder bounds. -/
theorem productRemainder_bounds_of_sufficientCutoff {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) {K : Nat}
    (hK : sufficientCutoff w ≤ K) (degrees : List Nat) :
    (0 : Q') ≤ productRemainder w K degrees ∧
      productRemainder w K degrees ≤
        (((1 : Q') - w) * ((1 : Q') - w)) *
          (totalCasimir degrees * totalCasimir degrees) := by
  have hguard := cutoff_guard_of_le hw1 hK
  exact ⟨productRemainder_nonnegative hw0 (Q'.le_of_lt hw1) K hguard degrees,
    productRemainder_le_square hw0 (Q'.le_of_lt hw1) K hguard degrees⟩

/-- Computed-cutoff specialization of the joint linear defect bound. -/
theorem one_sub_productAttenuation_le_of_sufficientCutoff {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) {K : Nat}
    (hK : sufficientCutoff w ≤ K) (degrees : List Nat) :
    (1 : Q') - productAttenuation w K degrees ≤
      ((1 : Q') - w) * totalCasimir degrees :=
  one_sub_productAttenuation_le hw0 (Q'.le_of_lt hw1) K
    (cutoff_guard_of_le hw1 hK) degrees

end YMGap.Continuum.SU2HeatProductTaylorRemainder

#print axioms YMGap.Continuum.SU2HeatProductTaylorRemainder.one_sub_productAttenuation_le
#print axioms YMGap.Continuum.SU2HeatProductTaylorRemainder.productRemainder_nonnegative
#print axioms YMGap.Continuum.SU2HeatProductTaylorRemainder.productRemainder_le_square
#print axioms YMGap.Continuum.SU2HeatProductTaylorRemainder.productRemainder_bounds_of_sufficientCutoff
#print axioms YMGap.Continuum.SU2HeatProductTaylorRemainder.one_sub_productAttenuation_le_of_sufficientCutoff
