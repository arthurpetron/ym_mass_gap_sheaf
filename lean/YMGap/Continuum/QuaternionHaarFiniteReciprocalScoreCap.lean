/-
# Computed finite reciprocal-score cap and signed correction bound

The literal polynomial score has a computed two-sided certificate. Its
positive density floor turns this into a relative numerator certificate,
so the SAME weighted reciprocal-score square is bounded at every degree.
The constant retains the finite window floor and polynomial presentation;
no cutoff-, depth-, volume- or physical-scale uniformity is asserted.

The signed correction estimate retains the mixed sign before applying a
rational Young bound, and only then discards the favorable negative square.
These finite estimates do not supply the genuine energy/scaling bound.
-/

import YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
import YMGap.Continuum.QuaternionHaarRelativeReciprocalDualNorm
import YMGap.Continuum.QuaternionHaarRelativePredictionFloor

namespace YMGap.Continuum.QuaternionHaarFiniteReciprocalScoreCap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPositiveWindowInverse
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.QuaternionHaarRelativeReciprocalDualNorm
open YMGap.Continuum.QuaternionHaarRelativePredictionFloor (weighted_square_young)

local infix:50 " ≈ " => Q'.eqv

/-- Explicit finite relative cap, independent of reciprocal degree. -/
def computedScoreCap (ell : Q') (hell : (0 : Q') < ell) (S : RatPoly) : Q' :=
  polynomialCap S * Q'.recipPos ell hell

private def relative_cap_certificate {blocks : Nat} {A p : RatPoly}
    {ell c C : Q'} (hC : (0 : Q') ≤ C) (hcell : C*ell ≈ c)
    (L : Certificate blocks (polyAdd A (polyNeg (cap ell))))
    (P : Certificate blocks (polyAdd (cap c) p)) :
    Certificate blocks (polyAdd (polyMul (cap C) A) p) := by
  have hcap : RatPolyCoeffEqv (polyMul (cap C) (cap ell)) (cap c) :=
    (cap_mul C ell).trans (RatPolyCoeffEqv.smul_coefficient hcell polyOne)
  have hid : RatPolyCoeffEqv (polyAdd (polyMul (cap C) A) p)
      (polyAdd (polyMul (cap C) (polyAdd A (polyNeg (cap ell))))
        (polyAdd (polyMul (cap C) (cap ell)) p)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.var 1)) (.var 3))
      (.add (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.mul (.var 0) (.var 2)) (.var 3)))
      (by decide) (fun | 0 => cap C | 1 => A | 2 => cap ell | _ => p)
  exact Certificate.ofCoeff
    (hid.trans ((RatPolyCoeffEqv.refl _).add (hcap.add (RatPolyCoeffEqv.refl _))))
    (((Certificate.constant blocks C hC).mul L).add P)

/-- Every finite reciprocal degree uses the actual certified density window
and weight. The numerator cap is constructed, not an additional premise. -/
theorem reciprocal_score_finite_cap_le {blocks : Nat} {A S W : RatPoly}
    {ell u : Q'} (hA : SupportedQuaternionBlocks blocks A)
    (hS : SupportedQuaternionBlocks blocks S)
    (hell : (0 : Q') < ell) (hu : (0 : Q') < u) (hle : ell ≤ u)
    (L : Certificate blocks (polyAdd A (polyNeg (cap ell))))
    (U : Certificate blocks (polyAdd (cap u) (polyNeg A)))
    (MW : Certificate blocks W) (k : Nat) :
    quaternionHaar blocks (polyMul W
      (polyMul (polyMul (reciprocal A u hu k) S)
        (polyMul (reciprocal A u hu k) S))) ≤
      (computedScoreCap ell hell S * computedScoreCap ell hell S) *
        quaternionHaar blocks W := by
  let c := polynomialCap S
  let v := Q'.recipPos ell hell
  let C := computedScoreCap ell hell S
  have hC : (0 : Q') ≤ C :=
    Q'.mul_nonneg _ _ (polynomialCap_nonnegative S)
      (Q'.le_of_lt (Q'.recipPos_pos ell hell))
  have hcell : C*ell ≈ c :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 0) (.mul (.var 2) (.var 1)))
      (by decide) (fun | 0 => c | 1 => v | _ => ell))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left c _ _ (Q'.mul_recipPos_eqv ell hell))
        (Q'.mul_one_eqv c))
  let I := polynomialInterval blocks S hS
  exact reciprocal_dual_weighted_norm_le hA hS hell hu hle hC L U
    (relative_cap_certificate hC hcell L I.lower)
    (relative_cap_certificate hC hcell L I.upper) MW k

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | term :: rest =>
      Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.neg_mul_eqv term.2 (quaternionHaarMono blocks term.1))
          (haar_neg blocks rest))
        (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem cross_bound (tau : Q') (htau : (0 : Q') < tau)
    (pp ee cross : Q') (hy : 2*tau*cross ≤ tau*tau*pp+ee) :
    cross+cross ≤ tau*pp+Q'.recipPos tau htau*ee := by
  let v := Q'.recipPos tau htau
  have hv : tau*v ≈ 1 := Q'.mul_recipPos_eqv tau htau
  have hl : (2*tau*cross)*v ≈ cross+cross :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.mul (.const 2) (.var 0)) (.var 2)) (.var 1))
      (.mul (.const 2) (.mul (.mul (.var 0) (.var 1)) (.var 2)))
      (by decide) (fun | 0 => tau | 1 => v | _ => cross))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left 2 _ _ (Q'.mul_eqv_congr_right _ _ cross hv))
        (poly_identity_of_normal_eq
          (.mul (.const 2) (.mul (.const 1) (.var 0)))
          (.add (.var 0) (.var 0)) (by decide) (fun _ => cross)))
  have hr : (tau*tau*pp+ee)*v ≈ tau*pp+v*ee :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.add (.mul (.mul (.var 0) (.var 0)) (.var 2)) (.var 3)) (.var 1))
      (.add (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
        (.mul (.var 1) (.var 3)))
      (by decide) (fun | 0 => tau | 1 => v | 2 => pp | _ => ee))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ (tau*pp) hv)
          (Q'.eqv_refl _))
        (Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.eqv_refl _)))
  have hs := Q'.mul_le_mul_of_nonneg_right _ _ v hy
    (Q'.le_of_lt (Q'.recipPos_pos tau htau))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hl))
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr))

/-- Signed reciprocal debt in the SAME weighted form. Sigma is arbitrary;
only the explicit Young parameter tau is required to be positive. -/
theorem signed_debt_le {blocks : Nat} {W p e : RatPoly}
    (MW : Certificate blocks W)
    (hp : SupportedQuaternionBlocks blocks p)
    (he : SupportedQuaternionBlocks blocks e)
    (sigma tau : Q') (htau : (0 : Q') < tau) :
    (sigma*quaternionHaar blocks (polyMul W (polyMul p p)) +
      -(2*quaternionHaar blocks (polyMul W (polyMul p e)))) +
      -quaternionHaar blocks (polyMul W (polyMul e e)) ≤
    (sigma+tau)*quaternionHaar blocks (polyMul W (polyMul p p)) +
      Q'.recipPos tau htau*quaternionHaar blocks (polyMul W (polyMul e e)) := by
  let pp := quaternionHaar blocks (polyMul W (polyMul p p))
  let ee := quaternionHaar blocks (polyMul W (polyMul e e))
  let J := quaternionHaar blocks (polyMul W (polyMul p e))
  have hne : SupportedQuaternionBlocks blocks (polyNeg e) := by
    intro term hterm
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hterm
    exact he s hs
  have hJ : quaternionHaar blocks (polyMul W (polyMul p (polyNeg e))) ≈ -J :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.neg (.var 2))))
      (.neg (.mul (.var 0) (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => W | 1 => p | _ => e)))
      (haar_neg blocks _)
  have hE : quaternionHaar blocks
      (polyMul W (polyMul (polyNeg e) (polyNeg e))) ≈ ee :=
    haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.neg (.var 1)) (.neg (.var 1))))
      (.mul (.var 0) (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => W | _ => e))
  have hy : 2*tau*(-J) ≤ tau*tau*pp+ee :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_eqv_congr_left (2*tau) _ _ hJ)))
      (Q'.le_trans' _ _ _ (weighted_square_young MW hp hne tau)
        (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) hE)))
  have hx := cross_bound tau htau pp ee (-J) hy
  have hs := Q'.add_le_add_left (sigma*pp) _ _ hx
  have hleft : (sigma*pp+ -(2*J))+ -ee ≤ sigma*pp+ -(2*J) := by
    have hn : (0 : Q') ≤ ee := (MW.mul (Certificate.square e he)).haar_nonnegative
    have ha := Q'.add_le_self_of_nonneg ((sigma*pp+ -(2*J))+ -ee) ee hn
    exact Q'.le_trans' _ _ _ ha (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.const 2) (.var 2))))
        (.neg (.var 3))) (.var 3))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.const 2) (.var 2))))
      (by decide) (fun | 0 => sigma | 1 => pp | 2 => J | _ => ee)))
  have hl : sigma*pp+ -(2*J) ≈ sigma*pp+((-J)+(-J)) :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.const 2) (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.add (.neg (.var 2)) (.neg (.var 2))))
      (by decide) (fun | 0 => sigma | 1 => pp | _ => J)
  have hr : sigma*pp+(tau*pp+Q'.recipPos tau htau*ee) ≈
      (sigma+tau)*pp+Q'.recipPos tau htau*ee :=
    poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.var 2))
        (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
      (.add (.mul (.add (.var 0) (.var 1)) (.var 2)) (.mul (.var 3) (.var 4)))
      (by decide) (fun
        | 0 => sigma | 1 => tau | 2 => pp
        | 3 => Q'.recipPos tau htau | _ => ee)
  exact Q'.le_trans' _ _ _ hleft
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
      (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv hr)))

#print axioms reciprocal_score_finite_cap_le
#print axioms signed_debt_le

end YMGap.Continuum.QuaternionHaarFiniteReciprocalScoreCap
