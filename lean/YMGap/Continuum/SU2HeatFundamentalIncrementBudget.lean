/-
Finite scalar budgets for the fundamental four-link heat increment.

These are only rational polynomial inequalities on the closed nome interval.
They do not assert the character identities needed by a later plaquette
consumer.
-/

import YMGap.Continuum.HeatKernelRGStep
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.SU2HeatFundamentalIncrementBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv

private theorem add_nonneg (a b : Q') (ha : (0 : Q') ≤ a)
    (hb : (0 : Q') ≤ b) : (0 : Q') ≤ a + b :=
  Q'.le_trans' _ _ _ ha (Q'.add_le_self_of_nonneg a b hb)

/-- The degree-thirty-two heat deficit has its elementary linear budget. -/
theorem one_sub_qpow_thirtyTwo_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) :
    (1 : Q') - qpow w 32 ≤ Q'.ofNat 32 * ((1 : Q') - w) :=
  oneSub_qpow_le hw0 hw1 32

private def curvaturePolynomial (z : Q') : Q' :=
  Q'.ofNat 5 + Q'.ofNat 10 * qpow z 1 +
    Q'.ofNat 15 * qpow z 2 + Q'.ofNat 12 * qpow z 3 +
    Q'.ofNat 9 * qpow z 4 + Q'.ofNat 6 * qpow z 5 +
    Q'.ofNat 3 * qpow z 6

private theorem curvature_factor (z : Q') :
    Q'.ofNat 5 + -(Q'.ofNat 8 * qpow z 3) +
        Q'.ofNat 3 * qpow z 8 ≈
      (((1 : Q') - z) * ((1 : Q') - z)) * curvaturePolynomial z := by
  unfold curvaturePolynomial
  exact poly_identity_of_normal_eq
    (.add (.add (.const 5) (.neg (.mul (.const 8) (.pow (.var 0) 3))))
      (.mul (.const 3) (.pow (.var 0) 8)))
    (.mul (.mul (.add (.const 1) (.neg (.var 0)))
        (.add (.const 1) (.neg (.var 0))))
      (.add (.add (.add (.add (.add (.add (.const 5)
        (.mul (.const 10) (.pow (.var 0) 1)))
        (.mul (.const 15) (.pow (.var 0) 2)))
        (.mul (.const 12) (.pow (.var 0) 3)))
        (.mul (.const 9) (.pow (.var 0) 4)))
        (.mul (.const 6) (.pow (.var 0) 5)))
        (.mul (.const 3) (.pow (.var 0) 6))))
    (by decide) (fun _ => z)

private theorem curvaturePolynomial_nonneg {z : Q'} (hz0 : (0 : Q') ≤ z) :
    (0 : Q') ≤ curvaturePolynomial z := by
  unfold curvaturePolynomial
  have hp (c k : Nat) :
      (0 : Q') ≤ Q'.ofNat c * qpow z k :=
    Q'.mul_nonneg _ _ (zero_le_ofNat c) (qpow_nonneg z hz0 k)
  have h0 : (0 : Q') ≤ Q'.ofNat 5 + Q'.ofNat 10 * qpow z 1 :=
    add_nonneg _ _ (zero_le_ofNat 5) (hp 10 1)
  have h1 := add_nonneg _ _ h0 (hp 15 2)
  have h2 := add_nonneg _ _ h1 (hp 12 3)
  have h3 := add_nonneg _ _ h2 (hp 9 4)
  have h4 := add_nonneg _ _ h3 (hp 6 5)
  exact add_nonneg _ _ h4 (hp 3 6)

private theorem curvaturePolynomial_le_sixty {z : Q'} (hz0 : (0 : Q') ≤ z)
    (hz1 : z ≤ (1 : Q')) : curvaturePolynomial z ≤ Q'.ofNat 60 := by
  have h1 : qpow z 1 ≤ (1 : Q') := qpow_le_one hz0 hz1 1
  have h2 : qpow z 2 ≤ (1 : Q') := qpow_le_one hz0 hz1 2
  have h3 : qpow z 3 ≤ (1 : Q') := qpow_le_one hz0 hz1 3
  have h4 : qpow z 4 ≤ (1 : Q') := qpow_le_one hz0 hz1 4
  have h5 : qpow z 5 ≤ (1 : Q') := qpow_le_one hz0 hz1 5
  have h6 : qpow z 6 ≤ (1 : Q') := qpow_le_one hz0 hz1 6
  have hdiff : (0 : Q') ≤
      Q'.ofNat 10 * ((1 : Q') - qpow z 1) +
      Q'.ofNat 15 * ((1 : Q') - qpow z 2) +
      Q'.ofNat 12 * ((1 : Q') - qpow z 3) +
      Q'.ofNat 9 * ((1 : Q') - qpow z 4) +
      Q'.ofNat 6 * ((1 : Q') - qpow z 5) +
      Q'.ofNat 3 * ((1 : Q') - qpow z 6) := by
    have ht (c k : Nat) (hk : qpow z k ≤ (1 : Q')) :
        (0 : Q') ≤ Q'.ofNat c * ((1 : Q') - qpow z k) :=
      Q'.mul_nonneg _ _ (zero_le_ofNat c) (Q'.sub_nonneg_of_le hk)
    have h0 := add_nonneg _ _ (ht 10 1 h1) (ht 15 2 h2)
    have h1' := add_nonneg _ _ h0 (ht 12 3 h3)
    have h2' := add_nonneg _ _ h1' (ht 9 4 h4)
    have h3' := add_nonneg _ _ h2' (ht 6 5 h5)
    exact add_nonneg _ _ h3' (ht 3 6 h6)
  apply Q'.le_of_sub_nonneg
  exact Q'.le_trans' _ _ _ hdiff (Q'.le_of_eqv (by
    unfold curvaturePolynomial
    exact poly_identity_of_normal_eq
      (.add (.add (.add (.add (.add
        (.mul (.const 10) (.add (.const 1) (.neg (.pow (.var 0) 1))))
        (.mul (.const 15) (.add (.const 1) (.neg (.pow (.var 0) 2)))))
        (.mul (.const 12) (.add (.const 1) (.neg (.pow (.var 0) 3)))))
        (.mul (.const 9) (.add (.const 1) (.neg (.pow (.var 0) 4)))))
        (.mul (.const 6) (.add (.const 1) (.neg (.pow (.var 0) 5)))))
        (.mul (.const 3) (.add (.const 1) (.neg (.pow (.var 0) 6)))))
      (.add (.const 60) (.neg
        (.add (.add (.add (.add (.add (.add (.const 5)
          (.mul (.const 10) (.pow (.var 0) 1)))
          (.mul (.const 15) (.pow (.var 0) 2)))
          (.mul (.const 12) (.pow (.var 0) 3)))
          (.mul (.const 9) (.pow (.var 0) 4)))
          (.mul (.const 6) (.pow (.var 0) 5)))
          (.mul (.const 3) (.pow (.var 0) 6)))))
      (by decide) (fun _ => z)))

/-- The spin-one/spin-two curvature combination is nonnegative and has a
uniform quadratic nome-margin budget. -/
theorem fundamental_curvature_bounds {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) :
    (0 : Q') ≤ Q'.ofNat 5 + -(Q'.ofNat 8 * qpow w 12) +
        Q'.ofNat 3 * qpow w 32 ∧
    Q'.ofNat 5 + -(Q'.ofNat 8 * qpow w 12) +
        Q'.ofNat 3 * qpow w 32 ≤
      Q'.ofNat 960 * (((1 : Q') - w) * ((1 : Q') - w)) := by
  let z := qpow w 4
  have hz0 : (0 : Q') ≤ z := qpow_nonneg w hw0 4
  have hz1 : z ≤ (1 : Q') := qpow_le_one hw0 hw1 4
  have h12 : qpow z 3 ≈ qpow w 12 := by
    unfold z
    simpa using qpow_qpow w 4 3
  have h32 : qpow z 8 ≈ qpow w 32 := by
    unfold z
    simpa using qpow_qpow w 4 8
  have hrewrite :
      Q'.ofNat 5 + -(Q'.ofNat 8 * qpow w 12) + Q'.ofNat 3 * qpow w 32 ≈
      Q'.ofNat 5 + -(Q'.ofNat 8 * qpow z 3) + Q'.ofNat 3 * qpow z 8 := by
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm h12))))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm h32))
  have hfactor := curvature_factor z
  have hone0 : (0 : Q') ≤ (1 : Q') - z := Q'.sub_nonneg_of_le hz1
  have hsquare0 : (0 : Q') ≤ ((1 : Q') - z) * ((1 : Q') - z) :=
    Q'.mul_nonneg _ _ hone0 hone0
  have hnonneg : (0 : Q') ≤
      (((1 : Q') - z) * ((1 : Q') - z)) * curvaturePolynomial z :=
    Q'.mul_nonneg _ _ hsquare0 (curvaturePolynomial_nonneg hz0)
  constructor
  · exact Q'.le_trans' _ _ _ hnonneg
      (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ hrewrite hfactor))
  · have hpoly := curvaturePolynomial_le_sixty hz0 hz1
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hpoly hsquare0
    have hmargin := oneSub_qpow_le hw0 hw1 4
    have hmargin0 : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
    have h4margin0 : (0 : Q') ≤ Q'.ofNat 4 * ((1 : Q') - w) :=
      Q'.mul_nonneg _ _ (by decide) hmargin0
    have hsquare :
        ((1 : Q') - z) * ((1 : Q') - z) ≤
          (Q'.ofNat 4 * ((1 : Q') - w)) *
            (Q'.ofNat 4 * ((1 : Q') - w)) :=
      Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ ((1 : Q') - z) hmargin hone0)
        (Q'.mul_le_mul_of_nonneg_left _ _
          (Q'.ofNat 4 * ((1 : Q') - w)) hmargin h4margin0)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hrewrite) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) ?_
    refine Q'.le_trans' _ _ _ hscaled ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.ofNat 60) hsquare (by decide)) ?_
    exact Q'.le_of_eqv (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.const 4) (.var 0)) (.mul (.const 4) (.var 0)))
        (.const 60))
      (.mul (.const 960) (.mul (.var 0) (.var 0)))
      (by decide) (fun _ => (1 : Q') - w))

end YMGap.Continuum.SU2HeatFundamentalIncrementBudget

#print axioms YMGap.Continuum.SU2HeatFundamentalIncrementBudget.one_sub_qpow_thirtyTwo_le
#print axioms YMGap.Continuum.SU2HeatFundamentalIncrementBudget.fundamental_curvature_bounds
