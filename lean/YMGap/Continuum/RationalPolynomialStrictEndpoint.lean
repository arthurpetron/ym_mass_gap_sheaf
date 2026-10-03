/-
# Finite polynomial sign closure at a strict left endpoint

Actual rational interior points approach the endpoint with explicit mesh.
The literal finite Taylor estimate bounds their error by a computed absolute
derivative/Taylor budget; rational Archimedean cancellation closes the sign.
No continuity axiom or endpoint-order premise is used.

The consumer closes a scalar Laurent Euler numerator's strict-nome sign,
without substituting into a generic non-injective Haar-carrier equality.
-/

import YMGap.Continuum.RationalPolynomialTaylorCell
import YMGap.Constructive.RatNat

namespace YMGap.Continuum.RationalPolynomialStrictEndpoint

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.QPolyFormalDerivative
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.RationalPolynomialIntervalOrder
open YMGap.Continuum.RationalPolynomialTaylorCell

local infix:50 " ≈ " => Q'.eqv

private theorem difference_positive {a b : Q'} (hab : a < b) :
    (0 : Q') < b + -a := by
  have h : a.num * (b.den : Int) < b.num * (a.den : Int) := hab
  show (0 : Int) * ((b + -a).den : Int) < (b + -a).num * 1
  rw [Int.zero_mul, Int.mul_one]
  change (0 : Int) < b.num * (a.den : Int) + (-a.num) * (b.den : Int)
  rw [Int.neg_mul]
  omega

private theorem strict_add {a d : Q'} (hd : (0 : Q') < d) : a < a+d := by
  have had : (0 : Int) < (a.den : Int) := by
    have h := a.den_pos
    omega
  have hp : (0 : Int) < (d.num * (a.den : Int)) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos (Q'.num_pos_of_pos hd) had) had
  show a.num * ((a+d).den : Int) < (a+d).num * (a.den : Int)
  rw [Q'.add_den_cast]
  change a.num * ((a.den : Int)*(d.den : Int)) <
    (a.num*(d.den : Int)+d.num*(a.den : Int))*(a.den : Int)
  have hs : a.num * ((a.den : Int)*(d.den : Int)) =
      (a.num*(d.den : Int))*(a.den : Int) := by
    rw [Int.mul_comm (a.den : Int) (d.den : Int), ← Int.mul_assoc]
  rw [hs, Int.add_mul]
  omega

/-- A signed finite polynomial nonnegative at every strict interior point
has nonnegative value at the actual left endpoint. The mesh and its error
budget are concrete; no analytic continuity or endpoint sign is assumed. -/
theorem nonnegative_at_left_endpoint (p : Poly) (a b : Q')
    (ha0 : (0 : Q') ≤ a) (hab : a < b) (hb : b ≤ (1 : Q'))
    (hpos : ∀ x : Q', a < x → x ≤ b → (0 : Q') ≤ QPoly.eval p x) :
    (0 : Q') ≤ QPoly.eval p a := by
  let d := QPoly.eval (pderiv p) a
  let B := taylorCellBudget p
  let C := Q'.abs d+B
  have hB : (0 : Q') ≤ B := taylorCellBudget_nonnegative p
  have hC : (0 : Q') ≤ C := Q'.zero_le_add _ _ (Q'.abs_nonneg d) hB
  have hnat : C ≤ Q'.ofNat C.num.toNat := RatNat.le_ofNat_toNat C hC
  apply Q'.le_of_le_add_mul_invSucc 0 (QPoly.eval p a) C.num.toNat
  intro N
  let δ := intervalMesh a b N
  let y := a+δ
  have hδpos : (0 : Q') < δ := Q'.mul_pos (difference_positive hab) (Q'.invSucc_pos N)
  have hδ : (0 : Q') ≤ δ := Q'.le_of_lt hδpos
  have hδinv : δ ≤ Q'.invSucc N := mesh_le_inverse ha0 hb N
  have hinv1 : Q'.invSucc N ≤ (1 : Q') := by
    show (Q'.invSucc N).num * ((1 : Q').den : Int) ≤
      (1 : Q').num * ((Q'.invSucc N).den : Int)
    rw [Q'.invSucc_num, Q'.invSucc_den]
    change (1 : Int)*1 ≤ 1*((N+1 : Nat) : Int)
    simp only [Int.one_mul]
    omega
  have hδ1 : δ ≤ (1 : Q') := Q'.le_trans' _ _ _ hδinv hinv1
  have hay : a < y := strict_add hδpos
  have hwidth : δ ≤ b + -a :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ (b + -a) hinv1
        (Q'.le_of_lt (difference_positive hab)))
      (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have hyb : y ≤ b :=
    Q'.le_trans' _ _ _ (Q'.add_le_add_left a _ _ hwidth)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add (.var 0) (.add (.var 1) (.neg (.var 0)))) (.var 1)
        (by decide) (fun | 0 => a | _ => b)))
  have hy1 : y ≤ (1 : Q') := Q'.le_trans' _ _ _ hyb hb
  have hdiff : y + -a ≈ δ := poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1)) (.neg (.var 0))) (.var 1)
    (by decide) (fun | 0 => a | _ => δ)
  let e := (QPoly.eval p y + -QPoly.eval p a) + -(δ*d)
  have herr : Q'.abs e ≤ (δ*δ)*B := by
    have ht := polynomial_taylor_cell_error p a y ha0 (Q'.le_of_lt hay) hy1
    have he :
        (QPoly.eval p y + -QPoly.eval p a) + -((y + -a)*d) ≈ e :=
      Q'.add_eqv_congr_left _ _ _
        (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ d hdiff))
    have hs : ((y + -a)*(y + -a))*B ≈ (δ*δ)*B :=
      Q'.mul_eqv_congr_right _ _ B
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (y + -a) hdiff)
          (Q'.mul_eqv_congr_left δ _ _ hdiff))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.abs_eqv_congr he))
      (Q'.le_trans' _ _ _ ht (Q'.le_of_eqv hs))
  have he : e ≤ (δ*δ)*B := Q'.le_trans' _ _ _ (Q'.le_abs_self e) herr
  have hd : δ*d ≤ δ*Q'.abs d :=
    Q'.mul_le_mul_of_nonneg_left _ _ δ (Q'.le_abs_self d) hδ
  have hsquare : (δ*δ)*B ≤ δ*B :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ B
        (Q'.le_trans' _ _ _
          (Q'.mul_le_mul_of_nonneg_right _ _ δ hδ1 hδ)
          (Q'.le_of_eqv (Q'.one_mul_eqv δ))) hB)
      (Q'.le_refl' _)
  have hpin : QPoly.eval p y ≈ QPoly.eval p a + (δ*d+e) :=
    poly_identity_of_normal_eq (.var 0)
      (.add (.var 1) (.add (.mul (.var 2) (.var 3))
        (.add (.add (.var 0) (.neg (.var 1))) (.neg (.mul (.var 2) (.var 3))))))
      (by decide) (fun | 0 => QPoly.eval p y | 1 => QPoly.eval p a | 2 => δ | _ => d)
  have hupper : QPoly.eval p y ≤ QPoly.eval p a + δ*C :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hpin)
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_left _ _ _
          (Q'.add_le_add hd (Q'.le_trans' _ _ _ he hsquare)))
        (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _
          (Q'.eqv_symm (Q'.mul_add_eqv δ (Q'.abs d) B)))))
  have hbudget : δ*C ≤ Q'.ofNat C.num.toNat * Q'.invSucc N :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ C hδinv hC)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.invSucc N) hnat (Q'.invSucc_nonneg N))
        (Q'.le_of_eqv (Q'.mul_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _ (hpos y hay hyb)
    (Q'.le_trans' _ _ _ hupper (Q'.add_le_add_left _ _ _ hbudget))

end YMGap.Continuum.RationalPolynomialStrictEndpoint

#print axioms YMGap.Continuum.RationalPolynomialStrictEndpoint.nonnegative_at_left_endpoint
