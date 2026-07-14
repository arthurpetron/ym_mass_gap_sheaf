/-
# Linearity of the explicit quaternion product-Haar moment functional

`ObservableMeasure.ProbFunctional` deliberately has a minimal interface, so
packaging a positive normalized map in that record does not by itself say
that the map is an expectation in the algebraic sense.  This file records the
missing concrete facts for the quaternion-polynomial carrier: the explicit
finite moment fold is additive and rational homogeneous.  These identities
are also the bookkeeping needed by the all-degree SOS positivity proof.
-/

import YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

namespace YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

theorem productHaar_zero : productHaar polyZero ≈ 0 :=
  Q'.eqv_refl _

private theorem productHaar_cons (t : RatTerm) (p : RatPoly) :
    productHaar (t :: p) =
      match (productHaarMono t.1).num with
      | Int.ofNat 0 => productHaar p
      | _ => t.2 * productHaarMono t.1 + productHaar p := rfl

theorem productHaar_append_eqv : ∀ p q : RatPoly,
    productHaar (p ++ q) ≈ productHaar p + productHaar q
  | [], q => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | t :: p, q => by
      simp only [List.cons_append, productHaar_cons]
      generalize hmu : productHaarMono t.1 = mu
      cases hnum : mu.num with
      | ofNat n =>
          cases n with
          | zero =>
              simp only
              exact productHaar_append_eqv p q
          | succ n =>
              simp only
              refine Q'.eqv_trans _
                (t.2 * mu + (productHaar p + productHaar q)) _ ?_ ?_
              · exact Q'.add_eqv_congr_left _ _ _
                  (productHaar_append_eqv p q)
              · exact Q'.eqv_symm
                  (Q'.add_assoc_eqv (t.2 * mu) (productHaar p)
                    (productHaar q))
      | negSucc n =>
          simp only
          refine Q'.eqv_trans _
            (t.2 * mu + (productHaar p + productHaar q)) _ ?_ ?_
          · exact Q'.add_eqv_congr_left _ _ _
              (productHaar_append_eqv p q)
          · exact Q'.eqv_symm
              (Q'.add_assoc_eqv (t.2 * mu) (productHaar p)
                (productHaar q))

theorem productHaar_add (p q : RatPoly) :
    productHaar (polyAdd p q) ≈ productHaar p + productHaar q :=
  productHaar_append_eqv p q

theorem productHaar_smul : ∀ (c : Q') (p : RatPoly),
    productHaar (polySmul c p) ≈ c * productHaar p
  | c, [] => Q'.eqv_symm (Q'.mul_zero_eqv c)
  | c, t :: p => by
      change productHaar ((t.1, c * t.2) :: polySmul c p) ≈
        c * productHaar (t :: p)
      simp only [productHaar_cons]
      generalize hmu : productHaarMono t.1 = mu
      cases hnum : mu.num with
      | ofNat n =>
          cases n with
          | zero =>
              simp only
              exact productHaar_smul c p
          | succ n =>
              simp only
              refine Q'.eqv_trans _
                (c * (t.2 * mu) + c * productHaar p) _ ?_ ?_
              · exact Q'.add_eqv_congr'
                  (Q'.mul_assoc_eqv c t.2 mu)
                  (productHaar_smul c p)
              · exact Q'.eqv_symm
                  (Q'.mul_add_eqv c (t.2 * mu) (productHaar p))
      | negSucc n =>
          simp only
          refine Q'.eqv_trans _
            (c * (t.2 * mu) + c * productHaar p) _ ?_ ?_
          · exact Q'.add_eqv_congr'
              (Q'.mul_assoc_eqv c t.2 mu)
              (productHaar_smul c p)
          · exact Q'.eqv_symm
              (Q'.mul_add_eqv c (t.2 * mu) (productHaar p))

theorem productHaar_neg (p : RatPoly) :
    productHaar (polyNeg p) ≈ -productHaar p := by
  induction p with
  | nil => decide
  | cons t p ih =>
      change productHaar ((t.1, -t.2) :: polyNeg p) ≈
        -productHaar (t :: p)
      simp only [productHaar_cons]
      generalize hmu : productHaarMono t.1 = mu
      cases hnum : mu.num with
      | ofNat n =>
          cases n with
          | zero =>
              simp only
              exact ih
          | succ n =>
              simp only
              refine Q'.eqv_trans _
                (-(t.2 * mu) + (-productHaar p)) _ ?_ ?_
              · exact Q'.add_eqv_congr'
                  (Q'.neg_mul_eqv t.2 mu) ih
              · exact Q'.eqv_symm (Q'.neg_add_eqv _ _)
      | negSucc n =>
          simp only
          refine Q'.eqv_trans _
            (-(t.2 * mu) + (-productHaar p)) _ ?_ ?_
          · exact Q'.add_eqv_congr'
              (Q'.neg_mul_eqv t.2 mu) ih
          · exact Q'.eqv_symm (Q'.neg_add_eqv _ _)

end YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity

#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity.productHaar_append_eqv
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity.productHaar_smul
#print axioms YMGap.Continuum.SU2QuaternionPolynomialHaarLinearity.productHaar_neg
