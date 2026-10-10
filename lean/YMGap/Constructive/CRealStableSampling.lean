/-
Stable rational sampling of a constructive real with a supplied Type-level
inner regularity rate. The sample is computed from that rate. Sound `leRat`
bounds are used only propositionally in proofs; no eventual index is extracted
as computational data. In particular, no bound on every raw approximation is
assumed. This is not a completion or continuity theorem for Point-functions.
-/

import YMGap.Constructive.CRealInnerRegularity
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealExp
import YMGap.Constructive.RegularCReal
import YMGap.Continuum.RingNormaliser

namespace YMGap.Constructive.CReal

set_option autoImplicit false

open YMGap.Continuum.RingNormaliser

/-- A rational sample at the supplied, computable inner-regularity stage. -/
def sample (x : CReal) (R : InnerRegularity x) (tau : Q') : Q' :=
  x.approx (R.rate tau)

/-- An explicit output-row estimate at every stage past the computed rate. -/
theorem sample_error_bound (x : CReal) (R : InnerRegularity x)
    (tau : Q') (htau : (0 : Q') < tau) (k : Nat)
    (hk : R.rate tau ≤ k) :
    Q'.abs (sample x R tau + -(x.approx k)) ≤ tau := by
  obtain ⟨h1, h2⟩ := R.regular tau htau (R.rate tau) k
    (Nat.le_refl _) hk
  exact abs_sub_le_of_bounds h1 h2

private theorem cancel_unit_residual (a b : Q')
    (h : ∀ N : Nat, a ≤ b + Q'.invSucc N) : a ≤ b := by
  apply Q'.le_of_le_add_mul_invSucc a b 1
  intro N
  exact Q'.le_trans' _ _ _ (h N)
    (Q'.ge_of_eqv
      (Q'.add_eqv_congr_left b _ _ (Q'.one_mul_eqv (Q'.invSucc N))))

private theorem abs_transport (a b B tau e : Q')
    (hab : Q'.abs (a + -b) ≤ tau)
    (hb : Q'.abs b ≤ B + e) :
    Q'.abs a ≤ (B + tau) + e := by
  have hsum : Q'.abs a ≤ (B + e) + tau :=
    Q'.le_trans' _ _ _ (Q'.abs_le_abs_add_abs_sub a b)
      (Q'.add_le_add hb hab)
  have hswap : ((B + e) + tau).eqv ((B + tau) + e) :=
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.var 2))
      (.add (.add (.var 0) (.var 2)) (.var 1))
      (by decide) (fun | 0 => B | 1 => e | _ => tau)
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hswap)

/-- Sound upper bound for the computed sample, allowing exactly the selected
inner-regularity tolerance. No uniform bound on raw approximations is used. -/
theorem sample_abs_le (x : CReal) (R : InnerRegularity x)
    (M tau : Q') (hM : leRat (abs x) M) (htau : (0 : Q') < tau) :
    Q'.abs (sample x R tau) ≤ M + tau := by
  apply cancel_unit_residual
  intro N
  obtain ⟨K, hK⟩ := hM (Q'.invSucc N) (Q'.invSucc_pos N)
  let j := max K (R.rate tau)
  have hKj : K ≤ j := Nat.le_max_left _ _
  have hRj : R.rate tau ≤ j := Nat.le_max_right _ _
  have hlate : Q'.abs (x.approx j) ≤ M + Q'.invSucc N := by
    exact hK j hKj
  exact abs_transport (sample x R tau) (x.approx j) M tau
    (Q'.invSucc N) (sample_error_bound x R tau htau j hRj) hlate

private theorem abs_difference_telescope (a b c d eta tau e : Q')
    (hac : Q'.abs (a + -c) ≤ tau)
    (hcd : Q'.abs (c + -d) ≤ eta + e)
    (hdb : Q'.abs (d + -b) ≤ tau) :
    Q'.abs (a + -b) ≤ (eta + 2 * tau) + e := by
  have hpin : (a + -b).eqv ((a + -c) + ((c + -d) + (d + -b))) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.var 1)))
      (.add (.add (.var 0) (.neg (.var 2)))
        (.add (.add (.var 2) (.neg (.var 3)))
          (.add (.var 3) (.neg (.var 1)))))
      (by decide) (fun | 0 => a | 1 => b | 2 => c | _ => d)
  have htriangle : Q'.abs (a + -b) ≤
      Q'.abs (a + -c) + (Q'.abs (c + -d) + Q'.abs (d + -b)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (ExpNeg.abs_eqv_congr hpin))
      (Q'.le_trans' _ _ _ (ExpNeg.abs_add_le _ _)
        (Q'.add_le_add_left _ _ _ (ExpNeg.abs_add_le _ _)))
  have hbound : Q'.abs (a + -b) ≤ tau + ((eta + e) + tau) :=
    Q'.le_trans' _ _ _ htriangle
      (Q'.add_le_add hac (Q'.add_le_add hcd hdb))
  have hregroup : (tau + ((eta + e) + tau)).eqv
      ((eta + 2 * tau) + e) :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.add (.add (.var 1) (.var 2)) (.var 0)))
      (.add (.add (.var 1) (.mul (.const 2) (.var 0))) (.var 2))
      (by decide) (fun | 0 => tau | 1 => eta | _ => e)
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hregroup)

/-- Two stable samples inherit a sound limit-level variation bound with two
sampling tolerances. The eventual stage used in this proof is not output data. -/
theorem sample_difference_le (x y : CReal)
    (Rx : InnerRegularity x) (Ry : InnerRegularity y)
    (eta tau : Q')
    (hD : leRat (abs (add x (neg y))) eta)
    (htau : (0 : Q') < tau) :
    Q'.abs (sample x Rx tau + -(sample y Ry tau)) ≤ eta + 2 * tau := by
  apply cancel_unit_residual
  intro N
  obtain ⟨K, hK⟩ := hD (Q'.invSucc N) (Q'.invSucc_pos N)
  let j := max K (max (Rx.rate tau) (Ry.rate tau))
  have hKj : K ≤ j := Nat.le_max_left _ _
  have hRj : Rx.rate tau ≤ j :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hSj : Ry.rate tau ≤ j :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hlate : Q'.abs (x.approx j + -(y.approx j)) ≤
      eta + Q'.invSucc N := by
    exact hK j hKj
  have hy : Q'.abs (y.approx j + -(sample y Ry tau)) ≤ tau :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ExpNeg.abs_sub_comm (y.approx j) (sample y Ry tau)))
      (sample_error_bound y Ry tau htau j hSj)
  exact abs_difference_telescope (sample x Rx tau) (sample y Ry tau)
    (x.approx j) (y.approx j) eta tau (Q'.invSucc N)
    (sample_error_bound x Rx tau htau j hRj) hlate hy

/-- The computed sample is within `tau` of every approximation at the
computed rate and beyond, hence has a sound limit-level error bound. -/
theorem sample_error_leRat (x : CReal) (R : InnerRegularity x)
    (tau : Q') (htau : (0 : Q') < tau) :
    leRat (abs (add (ofQ' (sample x R tau)) (neg x))) tau := by
  apply leRat_of_eventually
  refine ⟨R.rate tau, ?_⟩
  intro k hk
  exact sample_error_bound x R tau htau k hk

end YMGap.Constructive.CReal

#print axioms YMGap.Constructive.CReal.sample
#print axioms YMGap.Constructive.CReal.sample_error_bound
#print axioms YMGap.Constructive.CReal.sample_abs_le
#print axioms YMGap.Constructive.CReal.sample_difference_le
#print axioms YMGap.Constructive.CReal.sample_error_leRat
