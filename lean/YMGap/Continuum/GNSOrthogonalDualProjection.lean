/-
# A cleared dual projection off the original nonunit source

Subtracting the source component preserves pairing with any source-orthogonal
excitation.  The source norm stays explicit throughout; only its positive
rational factor is cancelled in the final inequality.  No reciprocal of a
source, test or excitation norm is constructed.  The intended consumer is the
original finite kinetic GNS form, with OWN centering supplying orthogonality.
This algebra alone supplies no lower overlap or retained-response estimate.
-/

import YMGap.Continuum.GNSQuotient
import YMGap.Continuum.RingNormaliser
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.GNSOrthogonalDualProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem qsub {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) :
    a-c ≈ b-d :=
  QPoly.q_add_congr h (Q'.neg_eqv_congr _ _ k)

/-- The literal source-norm-cleared dual test. -/
def clearedDual (D : GNSData) (q t : D.V) : D.V :=
  D.sub (D.smul (D.B q q) t) (D.smul (D.B q t) q)

/-- The nonunit source Schur remainder; no inverse norm is used. -/
def schurRemainder (D : GNSData) (q t : D.V) : Q' :=
  D.B q q * D.B t t - D.B q t * D.B q t

private theorem pairing (D : GNSData) (v q t : D.V) :
    D.B v (clearedDual D q t) ≈
      D.B q q * D.B v t - D.B q t * D.B v q := by
  unfold clearedDual GNSData.sub
  refine Q'.eqv_trans _ _ _ (D.B_add_right v _ _) ?_
  exact QPoly.q_add_congr (D.B_smul_right _ v t)
    (Q'.eqv_trans _ _ _ (D.B_neg_right v _)
      (Q'.neg_eqv_congr _ _ (D.B_smul_right _ v q)))

/-- The cleared test is orthogonal to the SAME original source. -/
theorem clearedDual_orthogonal (D : GNSData) (q t : D.V) :
    D.B q (clearedDual D q t) ≈ 0 := by
  refine Q'.eqv_trans _ _ _ (pairing D q q t) ?_
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 1) (.var 0))))
    (.const 0) (by decide)
    (fun
      | 0 => D.B q q
      | _ => D.B q t)

/-- OWN/source orthogonality preserves the numerator, up to the explicit
source norm.  Neither test nor excitation needs a positive norm. -/
theorem clearedDual_mixed_pin (D : GNSData) (x q t : D.V)
    (hxq : D.B x q ≈ 0) :
    D.B x (clearedDual D q t) ≈ D.B q q * D.B x t := by
  refine Q'.eqv_trans _ _ _ (pairing D x q t) ?_
  refine Q'.eqv_trans _ _ _
    (qsub (Q'.eqv_refl _) (Q'.mul_eqv_congr_left _ _ _ hxq)) ?_
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1))
      (.neg (.mul (.var 2) (.const 0))))
    (.mul (.var 0) (.var 1)) (by decide)
    (fun
      | 0 => D.B q q
      | 1 => D.B x t
      | _ => D.B q t)

/-- The exact projected norm retains the actual mixed source coefficient. -/
theorem clearedDual_norm_pin (D : GNSData) (q t : D.V) :
    D.B (clearedDual D q t) (clearedDual D q t) ≈
      D.B q q * schurRemainder D q t := by
  let z := clearedDual D q t
  have ht : D.B z t ≈ schurRemainder D q t := by
    refine Q'.eqv_trans _ _ _ (D.B_symm z t) ?_
    refine Q'.eqv_trans _ _ _ (pairing D t q t) ?_
    exact qsub (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_left _ _ _ (D.B_symm t q))
  have hq : D.B z q ≈ 0 :=
    Q'.eqv_trans _ _ _ (D.B_symm z q) (clearedDual_orthogonal D q t)
  refine Q'.eqv_trans _ _ _ (pairing D z q t) ?_
  refine Q'.eqv_trans _ _ _
    (qsub (Q'.mul_eqv_congr_left _ _ _ ht)
      (Q'.mul_eqv_congr_left _ _ _ hq)) ?_
  exact poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.var 1))
      (.neg (.mul (.var 2) (.const 0))))
    (.mul (.var 0) (.var 1)) (by decide)
    (fun
      | 0 => D.B q q
      | 1 => schurRemainder D q t
      | _ => D.B q t)

/-- The Schur remainder is nonnegative even when the source is null. -/
theorem schur_nonnegative (D : GNSData) (q t : D.V) :
    (0 : Q') ≤ D.B q q * D.B t t - D.B q t * D.B q t := by
  let m := D.B q t * D.B q t
  have h := Q'.add_le_add_right _ _ (-m) (D.cauchy_schwarz q t)
  have hz : m-m ≈ 0 :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 0))) (.const 0)
      (by decide) (fun _ => m)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hz) h

/-- Sharp cleared Cauchy--Schwarz after source projection.  Positivity of
the original source norm cancels one factor, without introducing its inverse. -/
theorem cleared_bound (D : GNSData) (x q t : D.V)
    (hxq : D.B x q ≈ 0) (hZ : (0 : Q') < D.B q q) :
    D.B q q * (D.B x t * D.B x t) ≤
      D.B x x * (D.B q q * D.B t t - D.B q t * D.B q t) := by
  let Z := D.B q q
  let v := D.B x t
  let X := D.B x x
  let R := schurRemainder D q t
  have hm := clearedDual_mixed_pin D x q t hxq
  have hn := clearedDual_norm_pin D q t
  have hcs : (Z*v)*(Z*v) ≤ X*(Z*R) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (qmul hm hm))
      (Q'.le_trans' _ _ _ (D.cauchy_schwarz x (clearedDual D q t))
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ hn)))
  have hl : (Z*v)*(Z*v) ≈ Z*(Z*(v*v)) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 1))))
      (by decide)
      (fun
        | 0 => Z
        | _ => v)
  have hr : X*(Z*R) ≈ Z*(X*R) :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun
        | 0 => X
        | 1 => Z
        | _ => R)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hl)
      (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv hr))) hZ

#print axioms clearedDual
#print axioms schurRemainder
#print axioms clearedDual_orthogonal
#print axioms clearedDual_mixed_pin
#print axioms clearedDual_norm_pin
#print axioms schur_nonnegative
#print axioms cleared_bound

end YMGap.Continuum.GNSOrthogonalDualProjection
