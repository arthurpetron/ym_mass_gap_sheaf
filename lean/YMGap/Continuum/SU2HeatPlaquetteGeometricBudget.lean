/-
# Geometric scalar budget for the four-link plaquette heat cost

This module only combines the already proved fundamental curvature estimate
with two supplied nonnegativity facts.  It makes no assertion about source
normalization or interacting moments.
-/

import YMGap.Continuum.SU2HeatFundamentalIncrementBudget

namespace YMGap.Continuum.SU2HeatPlaquetteGeometricBudget

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.SU2HeatFundamentalIncrementBudget

local infix:50 " ≈ " => Q'.eqv

private theorem add_le_add {a b c d : Q'} (hab : a ≤ b) (hcd : c ≤ d) :
    a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a b c hab)
    (Q'.add_le_add_left b c d hcd)

private theorem theta_three_identity (w : Q') :
    Q'.ofNat 3 *
        (((1 : Q') - qpow w 32) - Q'.ofNat 2 * ((1 : Q') - qpow w 12)) ≈
      Q'.ofNat 2 * ((1 : Q') - qpow w 12) -
        (Q'.ofNat 5 + -(Q'.ofNat 8 * qpow w 12) +
          Q'.ofNat 3 * qpow w 32) :=
  poly_identity_of_normal_eq
    (.mul (.const 3)
      (.add (.add (.const 1) (.neg (.var 1)))
        (.neg (.mul (.const 2) (.add (.const 1) (.neg (.var 0)))))))
    (.add (.mul (.const 2) (.add (.const 1) (.neg (.var 0))))
      (.neg (.add (.add (.const 5) (.neg (.mul (.const 8) (.var 0))))
        (.mul (.const 3) (.var 1)))))
    (by decide) (fun | 0 => qpow w 12 | _ => qpow w 32)

/-- The signed plaquette coefficient left after extracting the curvature is
bounded linearly by the nome margin. -/
theorem theta_le_eight_margin {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) :
    ((1 : Q') - qpow w 32) - Q'.ofNat 2 * ((1 : Q') - qpow w 12) ≤
      Q'.ofNat 8 * ((1 : Q') - w) := by
  let theta := ((1 : Q') - qpow w 32) -
    Q'.ofNat 2 * ((1 : Q') - qpow w 12)
  let gamma := Q'.ofNat 5 + -(Q'.ofNat 8 * qpow w 12) +
    Q'.ofNat 3 * qpow w 32
  have hgamma : (0 : Q') ≤ gamma :=
    (fundamental_curvature_bounds hw0 hw1).1
  have hthree : Q'.ofNat 3 * theta ≈
      Q'.ofNat 2 * ((1 : Q') - qpow w 12) - gamma := by
    exact theta_three_identity w
  have hdrop : Q'.ofNat 2 * ((1 : Q') - qpow w 12) - gamma ≤
      Q'.ofNat 2 * ((1 : Q') - qpow w 12) := by
    apply Q'.le_of_sub_nonneg
    exact Q'.le_trans' _ _ _ hgamma (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.var 0)
        (.add (.var 1) (.neg (.add (.var 1) (.neg (.var 0)))))
        (by decide) (fun | 0 => gamma
                         | _ => Q'.ofNat 2 * ((1 : Q') - qpow w 12))))
  have h12 := oneSub_qpow_le hw0 hw1 12
  have hscaled :
      Q'.ofNat 2 * ((1 : Q') - qpow w 12) ≤
        Q'.ofNat 2 * (Q'.ofNat 12 * ((1 : Q') - w)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) h12 (by decide)
  have hmul : Q'.ofNat 3 * theta ≤
      Q'.ofNat 3 * (Q'.ofNat 8 * ((1 : Q') - w)) :=
    Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ (Q'.le_of_eqv hthree) hdrop)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv
        (poly_identity_of_normal_eq
          (.mul (.const 2) (.mul (.const 12) (.var 0)))
          (.mul (.const 3) (.mul (.const 8) (.var 0)))
          (by decide) (fun _ => (1 : Q') - w))))
  exact Q'.le_of_mul_le_mul_left hmul (by decide)

private theorem plaquette_cost_identity (w A F : Q') :
    ((1 : Q') - qpow w 32) * A +
        ((1 : Q') + qpow w 32 - Q'.ofNat 2 * qpow w 12) * F ≈
      (((1 : Q') - qpow w 32) -
          Q'.ofNat 2 * ((1 : Q') - qpow w 12)) *
          (Q'.ofNat 4 * A - F) +
        (Q'.ofNat 5 + -(Q'.ofNat 8 * qpow w 12) +
          Q'.ofNat 3 * qpow w 32) * A :=
  poly_identity_of_normal_eq
    (.add (.mul (.add (.const 1) (.neg (.var 1))) (.var 2))
      (.mul (.add (.add (.const 1) (.var 1))
        (.neg (.mul (.const 2) (.var 0)))) (.var 3)))
    (.add
      (.mul (.add (.add (.const 1) (.neg (.var 1)))
          (.neg (.mul (.const 2) (.add (.const 1) (.neg (.var 0))))))
        (.add (.mul (.const 4) (.var 2)) (.neg (.var 3))))
      (.mul (.add (.add (.const 5) (.neg (.mul (.const 8) (.var 0))))
        (.mul (.const 3) (.var 1))) (.var 2)))
    (by decide) (fun | 0 => qpow w 12 | 1 => qpow w 32 | 2 => A | _ => F)

/-- Scalar geometric budget for the collected plaquette channel cost.  The
two hypotheses are precisely the nonnegative mass and the pointwise-character
bound after Haar integration that a later source consumer must supply. -/
theorem plaquette_geometric_cost_le {w A F : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (hA : (0 : Q') ≤ A)
    (hgeom : (0 : Q') ≤ Q'.ofNat 4 * A - F) :
    ((1 : Q') - qpow w 32) * A +
        ((1 : Q') + qpow w 32 - Q'.ofNat 2 * qpow w 12) * F ≤
      Q'.ofNat 8 * ((1 : Q') - w) * (Q'.ofNat 4 * A - F) +
        Q'.ofNat 960 * (((1 : Q') - w) * ((1 : Q') - w)) * A := by
  have htheta := theta_le_eight_margin hw0 hw1
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.ofNat 4 * A - F) htheta hgeom
  have hgamma := (fundamental_curvature_bounds hw0 hw1).2
  have hsecond := Q'.mul_le_mul_of_nonneg_right _ _ A hgamma hA
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (plaquette_cost_identity w A F))
    (add_le_add hfirst hsecond)

end YMGap.Continuum.SU2HeatPlaquetteGeometricBudget

#print axioms YMGap.Continuum.SU2HeatPlaquetteGeometricBudget.theta_le_eight_margin
#print axioms YMGap.Continuum.SU2HeatPlaquetteGeometricBudget.plaquette_geometric_cost_le
