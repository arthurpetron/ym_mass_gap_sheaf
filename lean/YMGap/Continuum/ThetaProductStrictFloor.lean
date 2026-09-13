/-
# Strict lower floor for the ORIGINAL theta product on the real box

The elementary comparison Ppart(q,x,N) >= E_q(2N)^2 retains the actual
Euler and Jacobi factors. The computable Euler prefix/tail floor then
gives a positive rational lower bound for the actual completed theta
product, uniform in x in [-1,1] and N, at each NAMED 0<q<1.
There is no coupling-uniform claim and no spectral-gap conclusion.
-/

import YMGap.Continuum.EulerProductStrictFloor

namespace YMGap.Continuum.ThetaProductStrictFloor

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum.GaussQBinomEulerNormalization
open YMGap.Continuum.GaussQBinomEulerQuotient
open YMGap.Continuum.ThetaConv

local infix:50 " ≈ " => Q'.eqv

instance : Trans Q'.eqv Q'.eqv Q'.eqv where
  trans h₁ h₂ := Q'.eqv_trans _ _ _ h₁ h₂

private theorem one_sub_le_one {a : Q'} (ha : (0 : Q') ≤ a) :
    1 + -a ≤ (1 : Q') := by
  have h := Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg ha)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (by decide : (1 : Q') + -0 ≈ 1))

/-- Two Euler factors squared lie below one full Jacobi factor. -/
theorem euler_pair_square_le_gFac {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (hx : (-(1 : Q')) ≤ x) (N : Nat) :
    ((1 + -(q ^ (2 * N + 1))) * (1 + -(q ^ (2 * N + 2))))
      * ((1 + -(q ^ (2 * N + 1))) * (1 + -(q ^ (2 * N + 2))))
      ≤ gFac q x N := by
  let o := 1 + -(q ^ (2 * N + 1))
  let e := 1 + -(q ^ (2 * N + 2))
  have he0 : (0 : Q') ≤ e := Q'.le_of_lt (HKPos.one_sub_pos (uAmp_pos_lt_one hq0 hq1 N).2)
  have he1 : e ≤ (1 : Q') := one_sub_le_one (Q'.pow_nonneg q (Q'.le_of_lt hq0) _)
  have hee : e * e ≤ e := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ he1 he0) (Q'.le_of_eqv (Q'.mul_one_eqv _))
  have ho0 : (0 : Q') ≤ o * o := Q'.le_of_lt
    (HKPos.factorLB_pos (HKPos.pow_succ_pos_lt_one hq0 hq1 (2 * N)).2)
  have hfac : o * o ≤ HKPos.factor (HKPos.geoAmp q N) x :=
    HKPos.factorLB_le_factor (Q'.pow_nonneg q (Q'.le_of_lt hq0) _) hx
  have hreorder : (o * e) * (o * e) ≈ (e * e) * (o * o) := by
    exact Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)))
        (by show _ * (_ : Int) = _ * (_ : Int)
            simp only [Q'.mul_num_cast, Q'.mul_den_cast]
            ac_rfl))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder)
    (HKConv.mul_le_mul' (Q'.mul_nonneg _ _ he0 he0)
      (Q'.le_trans' _ _ _ ho0 hfac) hee hfac)

/-- The original finite theta product dominates the square of the Euler
product containing every power q^1 through q^(2N). -/
theorem euler_square_le_Ppart {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (hx : (-(1 : Q')) ≤ x) (N : Nat) :
    euler q (2 * N) * euler q (2 * N) ≤ Ppart q x N := by
  induction N with
  | zero => exact Q'.le_of_eqv (Q'.mul_one_eqv 1)
  | succ N ih =>
      have he : euler q (2 * (N + 1))
          ≈ euler q (2 * N) * ((1 + -(q ^ (2 * N + 1))) * (1 + -(q ^ (2 * N + 2)))) := by
        rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega, euler_succ, euler_succ]
        exact Q'.mul_assoc_eqv _ _ _
      have hs : euler q (2 * (N + 1)) * euler q (2 * (N + 1))
          ≈ (euler q (2 * N) * euler q (2 * N))
            * (((1 + -(q ^ (2 * N + 1))) * (1 + -(q ^ (2 * N + 2))))
              * ((1 + -(q ^ (2 * N + 1))) * (1 + -(q ^ (2 * N + 2))))) := by
        apply Q'.eqv_trans _ _ _ (Cheb.mul_eqv_congr _ _ _ _ he he)
        show _ * (_ : Int) = _ * (_ : Int)
        simp only [Q'.mul_num_cast, Q'.mul_den_cast]
        ac_rfl
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hs)
        (HKConv.mul_le_mul'
          (Q'.mul_nonneg _ _ (Q'.le_of_lt (euler_pos hq0 hq1 _)) (Q'.le_of_lt (euler_pos hq0 hq1 _)))
          (gFac_nonneg hq0 hq1 hx N) ih (euler_pair_square_le_gFac hq0 hq1 hx N))

/-- Positive floor as data, dependent on the named nome q only. -/
def floor (q : Q') : Q' := EulerProductStrictFloor.floor q * EulerProductStrictFloor.floor q

theorem floor_pos {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    (0 : Q') < floor q :=
  HKPos.q_mul_pos (EulerProductStrictFloor.floor_pos hq0 hq1) (EulerProductStrictFloor.floor_pos hq0 hq1)

/-- Uniform over N and x>=-1 at each supplied nome q, not uniform in q. -/
theorem floor_le_Ppart {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (hx : (-(1 : Q')) ≤ x) (N : Nat) :
    floor q ≤ Ppart q x N :=
  Q'.le_trans' _ _ _
    (HKConv.mul_le_mul' (Q'.le_of_lt (EulerProductStrictFloor.floor_pos hq0 hq1))
      (Q'.le_of_lt (euler_pos hq0 hq1 _))
      (EulerProductStrictFloor.floor_le_euler hq0 hq1 _) (EulerProductStrictFloor.floor_le_euler hq0 hq1 _))
    (euler_square_le_Ppart hq0 hq1 hx N)

/-- The floor holds for the EXISTING completed theta product, endpoints included. -/
theorem thetaConvCRealGen_geRat_floor {q x : Q'}
    (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    ExpPos.geRat (ThetaConvGen.thetaConvCRealGen hq0 hq1 hxLower hxUpper) (floor q) :=
  ExpPos.geRat_of_eventually ⟨0, fun N _ => floor_le_Ppart hq0 hq1 hxLower N⟩

end YMGap.Continuum.ThetaProductStrictFloor

#print axioms YMGap.Continuum.ThetaProductStrictFloor.euler_pair_square_le_gFac
#print axioms YMGap.Continuum.ThetaProductStrictFloor.euler_square_le_Ppart
#print axioms YMGap.Continuum.ThetaProductStrictFloor.floor
#print axioms YMGap.Continuum.ThetaProductStrictFloor.floor_pos
#print axioms YMGap.Continuum.ThetaProductStrictFloor.floor_le_Ppart
#print axioms YMGap.Continuum.ThetaProductStrictFloor.thetaConvCRealGen_geRat_floor
