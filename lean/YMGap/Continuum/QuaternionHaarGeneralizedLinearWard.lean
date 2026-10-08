/-
# Generalized exact Ward identity on the original Haar carrier

The auxiliary multiplier h is arbitrary. Angular differentiation of h
produces the energy term, while differentiation of the complete weight W
remains as an explicitly signed residual. No conditional measure, deleted
interaction, or analytic bound enters this identity.
-/

import YMGap.Continuum.QuaternionHaarLinearMeanWard
import YMGap.Continuum.QuaternionHaarRelativeAngularYoung
import YMGap.Continuum.QuaternionHaarRelativeCenteredWard

namespace YMGap.Continuum.QuaternionHaarGeneralizedLinearWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarLinearMeanWard
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarRelativeAngularYoung
open YMGap.Continuum.QuaternionHaarRelativeCenteredWard
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left cap_mul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The energy arising when the angular derivative strikes the auxiliary
multiplier. It remains under the complete original weight. -/
def generalizedEnergy (tail : Nat) (W h f : RatPoly) : Q' :=
  sixValue (fun i j => H (tail+1)
    (polyMul W (polyMul (angularDerivative i j h) (angularDerivative i j f))))

/-- The signed term where the derivative strikes the complete weight. -/
def generalizedResidual (tail : Nat) (W h f : RatPoly) : Q' :=
  sixValue (fun i j => H (tail+1)
    (polyMul (polyMul h (angularDerivative i j W)) (angularDerivative i j f)))

private theorem sixValue_add (a b : Nat → Nat → Q') :
    sixValue a + sixValue b ≈ sixValue (fun i j => a i j + b i j) :=
  poly_identity_of_normal_eq
    (.add
      (.add (.var 0) (.add (.var 1) (.add (.var 2)
        (.add (.var 3) (.add (.var 4) (.var 5))))))
      (.add (.var 6) (.add (.var 7) (.add (.var 8)
        (.add (.var 9) (.add (.var 10) (.var 11)))))))
    (.add (.add (.var 0) (.var 6))
      (.add (.add (.var 1) (.var 7))
        (.add (.add (.var 2) (.var 8))
          (.add (.add (.var 3) (.var 9))
            (.add (.add (.var 4) (.var 10)) (.add (.var 5) (.var 11)))))))
    (by decide) (fun
      | 0 => a 0 1 | 1 => a 0 2 | 2 => a 0 3
      | 3 => a 1 2 | 4 => a 1 3 | 5 => a 2 3
      | 6 => b 0 1 | 7 => b 0 2 | 8 => b 0 3
      | 9 => b 1 2 | 10 => b 1 3 | _ => b 2 3)

private theorem sixValue_affine (a : Q') (b : Nat → Nat → Q') :
    sixValue (fun i j => a + b i j) ≈ 6*a + sixValue b :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.var 1))
      (.add (.add (.var 0) (.var 2))
        (.add (.add (.var 0) (.var 3))
          (.add (.add (.var 0) (.var 4))
            (.add (.add (.var 0) (.var 5)) (.add (.var 0) (.var 6)))))))
    (.add (.mul (.const 6) (.var 0))
      (.add (.var 1) (.add (.var 2) (.add (.var 3)
        (.add (.var 4) (.add (.var 5) (.var 6)))))))
    (by decide) (fun
      | 0 => a | 1 => b 0 1 | 2 => b 0 2 | 3 => b 0 3
      | 4 => b 1 2 | 5 => b 1 3 | _ => b 2 3)

private theorem plane_split (tail i j : Nat) (W h f : RatPoly) :
    H (tail+1) (polyMul (angularDerivative i j (polyMul W h))
      (angularDerivative i j f)) ≈
    H (tail+1) (polyMul W
      (polyMul (angularDerivative i j h) (angularDerivative i j f))) +
    H (tail+1) (polyMul (polyMul h (angularDerivative i j W))
      (angularDerivative i j f)) := by
  let dh := angularDerivative i j h
  let dW := angularDerivative i j W
  let df := angularDerivative i j f
  have hp : RatPolyCoeffEqv
      (polyMul (angularDerivative i j (polyMul W h)) df)
      (polyAdd (polyMul W (polyMul dh df)) (polyMul (polyMul h dW) df)) :=
    ((angularDerivative_mul i j W h).mul_right df).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (.var 4))
        (.add (.mul (.var 1) (.mul (.var 3) (.var 4)))
          (.mul (.mul (.var 2) (.var 0)) (.var 4)))
        (by decide) (fun | 0 => dW | 1 => W | 2 => h | 3 => dh | _ => df))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp) (quaternionHaar_append (tail+1) _ _)

/-- Exact full-weight generalized Ward identity. The multiplier h need not
be linear, centered, independent, or supported. -/
theorem generalized_linear_ward (tail : Nat) (W h f : RatPoly)
    (hf : HasQuaternionBlockDegree 0 1 f) :
    generalizedEnergy tail W h f + generalizedResidual tail W h f ≈
      3 * H (tail+1) (polyMul (polyMul W h) f) := by
  let energy := fun i j => H (tail+1)
    (polyMul W (polyMul (angularDerivative i j h) (angularDerivative i j f)))
  let residual := fun i j => H (tail+1)
    (polyMul (polyMul h (angularDerivative i j W)) (angularDerivative i j f))
  have hp := sixValue_congr (fun i j => energy i j + residual i j)
    (fun i j => H (tail+1)
      (polyMul (angularDerivative i j (polyMul W h)) (angularDerivative i j f)))
    (fun i j _ _ => Q'.eqv_symm (plane_split tail i j W h f))
  exact Q'.eqv_trans _ _ _ (sixValue_add energy residual)
    (Q'.eqv_trans _ _ _ hp (weighted_linear_mean_ward tail (polyMul W h) f hf))

/-- Replacing the auxiliary multiplier by `f-q`, with q independent of the
head quaternion, turns its derivative into the derivative of f. This is an
exact identity and imposes no independence on the complete weight W. -/
theorem independent_shift_ward (tail : Nat) (W f q : RatPoly)
    (hf : HasQuaternionBlockDegree 0 1 f)
    (hq : HasQuaternionBlockDegree 0 0 q) :
    let h := polyAdd f (polySmul (-1) q)
    H (tail+1) (polyMul W (angularSquare f)) +
      generalizedResidual tail W h f ≈
      3 * H (tail+1) (polyMul (polyMul W h) f) := by
  let h := polyAdd f (polySmul (-1) q)
  have hd (i j : Nat) (hi : i < 4) (hj : j < 4) :
      RatPolyCoeffEqv (angularDerivative i j h) (angularDerivative i j f) := by
    have hz := angularDerivative_independent_zero hi hj q hq
    exact (angularDerivative_add i j f (polySmul (-1) q)).trans
      (((RatPolyCoeffEqv.refl _).add
        ((angularDerivative_smul i j (-1) q).trans
          ((hz.smul (-1)).trans (RatPolyCoeffEqv.smul_zero (-1))))).trans
        (RatPolyCoeffEqv.add_zero _))
  have he : generalizedEnergy tail W h f ≈
      H (tail+1) (polyMul W (angularSquare f)) := by
    unfold generalizedEnergy
    exact Q'.eqv_trans _ _ _
      (sixValue_congr _ _ (fun i j hi hj =>
        haar_of_coeff (((hd i j hi hj).mul_right
          (angularDerivative i j f)).mul_left W)))
      (Q'.eqv_symm (haar_six (tail+1) W
        (fun i j => polyMul (angularDerivative i j f) (angularDerivative i j f))))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_symm he) (Q'.eqv_refl _))
    (generalized_linear_ward tail W h f hf)

private theorem scaled_cross_pin (blocks i j : Nat) (W h f : RatPoly) (t : Q') :
    H blocks (polyMul (angularDerivative i j W)
      (polyMul h (polySmul t (angularDerivative i j f)))) ≈
      t * H blocks (polyMul (polyMul h (angularDerivative i j W))
        (angularDerivative i j f)) := by
  let dW := angularDerivative i j W
  let df := angularDerivative i j f
  have hp : RatPolyCoeffEqv (polyMul dW (polyMul h (polySmul t df)))
      (polySmul t (polyMul (polyMul h dW) df)) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.mul (.var 1) (.var 0)) (.var 2))
      (by decide) (fun | 0 => dW | 1 => h | _ => polySmul t df)).trans
      (RatPolyCoeffEqv.polyMul_smul_right t (polyMul h dW) df)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (quaternionHaar_polySmul blocks t _)

private theorem scaled_square_pin (blocks i j : Nat) (W f : RatPoly) (t : Q') :
    H blocks (polyMul W
      (polyMul (polySmul t (angularDerivative i j f))
        (polySmul t (angularDerivative i j f)))) ≈
      (t*t) * H blocks (polyMul W
        (polyMul (angularDerivative i j f) (angularDerivative i j f))) := by
  let df := angularDerivative i j f
  have hp : RatPolyCoeffEqv (polyMul W (polyMul (polySmul t df) (polySmul t df)))
      (polySmul (t*t) (polyMul W (polyMul df df))) :=
    (((RatPolyCoeffEqv.polyMul_smul_left t df (polySmul t df)).trans
      (((RatPolyCoeffEqv.polyMul_smul_right t df df).smul t).trans
        (RatPolyCoeffEqv.smul_assoc t t (polyMul df df)))).mul_left W).trans
      (RatPolyCoeffEqv.polyMul_smul_right (t*t) W (polyMul df df))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (quaternionHaar_polySmul blocks (t*t) _)

private theorem scaled_plane_lower {tail i j : Nat} {W h f : RatPoly} {C t : Q'}
    (hC : (0 : Q') < C)
    (R : RelativeBound (tail+1) i j W C)
    (hh : SupportedQuaternionBlocks (tail+1) h)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hi : i < 4) (hj : j < 4) :
    -(2 * (t * H (tail+1) (polyMul (polyMul h (angularDerivative i j W))
      (angularDerivative i j f)))) ≤
      (C*C) * H (tail+1) (polyMul W (polyMul h h)) +
      (t*t) * H (tail+1) (polyMul W
        (polyMul (angularDerivative i j f) (angularDerivative i j f))) := by
  let df := angularDerivative i j f
  have hdf := angularDerivative_supported (Nat.zero_lt_succ tail) hi hj hf
  have hs := relative_young_lower R hC hh (polySmul_supported hdf t)
  have hc := scaled_cross_pin (tail+1) i j W h f t
  have he := scaled_square_pin (tail+1) i j W f t
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left 2 _ _ (Q'.eqv_symm hc))))
    (Q'.le_trans' _ _ _ hs
      (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) he)))

private theorem scaled_plane_upper {tail i j : Nat} {W h f : RatPoly} {C t : Q'}
    (hC : (0 : Q') < C)
    (R : RelativeBound (tail+1) i j W C)
    (hh : SupportedQuaternionBlocks (tail+1) h)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hi : i < 4) (hj : j < 4) :
    2 * (t * H (tail+1) (polyMul (polyMul h (angularDerivative i j W))
      (angularDerivative i j f))) ≤
      (C*C) * H (tail+1) (polyMul W (polyMul h h)) +
      (t*t) * H (tail+1) (polyMul W
        (polyMul (angularDerivative i j f) (angularDerivative i j f))) := by
  let df := angularDerivative i j f
  have hdf := angularDerivative_supported (Nat.zero_lt_succ tail) hi hj hf
  have hs := relative_young_upper R hC hh (polySmul_supported hdf t)
  have hc := scaled_cross_pin (tail+1) i j W h f t
  have he := scaled_square_pin (tail+1) i j W f t
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left 2 _ _ (Q'.eqv_symm hc)))
    (Q'.le_trans' _ _ _ hs
      (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) he)))

private theorem scaled_rhs_pin (tail : Nat) (W h f : RatPoly) (C t : Q') :
    let A := H (tail+1) (polyMul W (polyMul h h))
    let e := fun i j => H (tail+1) (polyMul W
      (polyMul (angularDerivative i j f) (angularDerivative i j f)))
    sixValue (fun i j => (C*C)*A + (t*t)*e i j) ≈
      6*(C*C)*A + (t*t)*H (tail+1) (polyMul W (angularSquare f)) := by
  let A := H (tail+1) (polyMul W (polyMul h h))
  let e := fun i j => H (tail+1) (polyMul W
    (polyMul (angularDerivative i j f) (angularDerivative i j f)))
  exact Q'.eqv_trans _ _ _ (sixValue_affine ((C*C)*A) (fun i j => (t*t)*e i j))
    (Q'.add_eqv_congr'
      (Q'.eqv_symm (Q'.mul_assoc_eqv 6 (C*C) A))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (sixValue_mul_left (t*t) e))
        (Q'.mul_eqv_congr_left (t*t) _ _
          (Q'.eqv_symm (haar_six (tail+1) W
            (fun i j => polyMul (angularDerivative i j f)
              (angularDerivative i j f)))))))

/-- Lower signed control of the generalized Ward residual at any rational
scale. Positivity of t is not required: the Young certificate uses t². -/
theorem residual_lower_scaled {tail : Nat} {W h f : RatPoly} {C : Q'}
    (hC : (0 : Q') < C)
    (R : ∀ i j, i < 4 → j < 4 → RelativeBound (tail+1) i j W C)
    (hh : SupportedQuaternionBlocks (tail+1) h)
    (hf : SupportedQuaternionBlocks (tail+1) f) (t : Q') :
    -(2*t*generalizedResidual tail W h f) ≤
      6*(C*C)*H (tail+1) (polyMul W (polyMul h h)) +
      (t*t)*H (tail+1) (polyMul W (angularSquare f)) := by
  let r := fun i j => H (tail+1)
    (polyMul (polyMul h (angularDerivative i j W)) (angularDerivative i j f))
  let A := H (tail+1) (polyMul W (polyMul h h))
  let e := fun i j => H (tail+1) (polyMul W
    (polyMul (angularDerivative i j f) (angularDerivative i j f)))
  have hm := sixValue_mono (fun i j => -(2*(t*r i j)))
    (fun i j => (C*C)*A+(t*t)*e i j)
    (fun i j hi hj => scaled_plane_lower hC (R i j hi hj) hh hf hi hj)
  have hl : -(2*t*generalizedResidual tail W h f) ≈
      sixValue (fun i j => -(2*(t*r i j))) := by
    change -(2*t*sixValue r) ≈ _
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.neg (.mul (.mul (.const 2) (.var 0)) (.var 1)))
        (.mul (.neg (.mul (.const 2) (.var 0))) (.var 1))
        (by decide) (fun | 0 => t | _ => sixValue r))
      (Q'.eqv_trans _ _ _ (sixValue_mul_left (-(2*t)) r)
        (sixValue_congr _ _ (fun i j _ _ =>
          poly_identity_of_normal_eq
            (.mul (.neg (.mul (.const 2) (.var 0))) (.var 1))
            (.neg (.mul (.const 2) (.mul (.var 0) (.var 1))))
            (by decide) (fun | 0 => t | _ => r i j))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (scaled_rhs_pin tail W h f C t)))

/-- Upper signed control of the same residual at any rational scale. -/
theorem residual_upper_scaled {tail : Nat} {W h f : RatPoly} {C : Q'}
    (hC : (0 : Q') < C)
    (R : ∀ i j, i < 4 → j < 4 → RelativeBound (tail+1) i j W C)
    (hh : SupportedQuaternionBlocks (tail+1) h)
    (hf : SupportedQuaternionBlocks (tail+1) f) (t : Q') :
    2*t*generalizedResidual tail W h f ≤
      6*(C*C)*H (tail+1) (polyMul W (polyMul h h)) +
      (t*t)*H (tail+1) (polyMul W (angularSquare f)) := by
  let r := fun i j => H (tail+1)
    (polyMul (polyMul h (angularDerivative i j W)) (angularDerivative i j f))
  let A := H (tail+1) (polyMul W (polyMul h h))
  let e := fun i j => H (tail+1) (polyMul W
    (polyMul (angularDerivative i j f) (angularDerivative i j f)))
  have hm := sixValue_mono (fun i j => 2*(t*r i j))
    (fun i j => (C*C)*A+(t*t)*e i j)
    (fun i j hi hj => scaled_plane_upper hC (R i j hi hj) hh hf hi hj)
  have hl : 2*t*generalizedResidual tail W h f ≈
      sixValue (fun i j => 2*(t*r i j)) := by
    change 2*t*sixValue r ≈ _
    exact Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.mul (.const 2) (.var 0)) (.var 1))
        (.mul (.mul (.const 2) (.var 0)) (.var 1))
        (by decide) (fun | 0 => t | _ => sixValue r))
      (Q'.eqv_trans _ _ _ (sixValue_mul_left (2*t) r)
        (sixValue_congr _ _ (fun i j _ _ =>
          Q'.mul_assoc_eqv 2 t (r i j))))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (scaled_rhs_pin tail W h f C t)))

/-- The generalized Ward identity with its own head-linear multiplier. -/
theorem self_ward (tail : Nat) (W f : RatPoly)
    (hf : HasQuaternionBlockDegree 0 1 f) :
    H (tail+1) (polyMul W (angularSquare f)) +
      generalizedResidual tail W f f ≈
      3*H (tail+1) (polyMul (polyMul W f) f) := by
  have he : generalizedEnergy tail W f f ≈
      H (tail+1) (polyMul W (angularSquare f)) :=
    Q'.eqv_symm (haar_six (tail+1) W
      (fun i j => polyMul (angularDerivative i j f) (angularDerivative i j f)))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_symm he) (Q'.eqv_refl _))
    (generalized_linear_ward tail W f f hf)

/-- The score-only coefficient in the original-weight variance estimate. -/
def scoreVarianceFactor (C : Q') : Q' :=
  7 + 10*(C*C) + 4*((C*C)*(C*C))

theorem scoreVarianceFactor_positive (C : Q') :
    (0 : Q') < scoreVarianceFactor C := by
  have hu : (0 : Q') ≤ C*C := SumOfSquares.q_mul_self_nonneg C
  have huu : (0 : Q') ≤ (C*C)*(C*C) := Q'.mul_nonneg _ _ hu hu
  have h1 : (0 : Q') ≤ 10*(C*C) := Q'.mul_nonneg _ _ (by decide) hu
  have h2 : (0 : Q') ≤ 4*((C*C)*(C*C)) := Q'.mul_nonneg _ _ (by decide) huu
  have h7 : (0 : Q') < 7+10*(C*C) :=
    Q'.pos_of_lt_of_le (by decide) (Q'.add_le_self_of_nonneg 7 _ h1)
  exact Q'.pos_of_lt_of_le h7 (Q'.add_le_self_of_nonneg _ _ h2)

/-- A positive rational floor depending only on the supplied score bound. -/
def scoreVarianceFloor (C : Q') : Q' :=
  4 * Q'.recipPos (scoreVarianceFactor C) (scoreVarianceFactor_positive C)

theorem scoreVarianceFloor_positive (C : Q') :
    (0 : Q') < scoreVarianceFloor C :=
  Q'.mul_pos (by decide) (Q'.recipPos_pos _ (scoreVarianceFactor_positive C))

private theorem score_budget (C Z E m v : Q') (hZ : (0 : Q') < Z)
    (hmean : 3*((m*m)*Z) ≤ 2*(C*C)*E)
    (henergy : E ≤ 6*(1+C*C)*(Z*v))
    (hkin : E+Z*(v+m*m) ≈ 4*Z) :
    scoreVarianceFloor C ≤ v := by
  let u := C*C
  let P := scoreVarianceFactor C
  let r := Q'.recipPos P (scoreVarianceFactor_positive C)
  have hu : (0 : Q') ≤ u := SumOfSquares.q_mul_self_nonneg C
  have h2u : (0 : Q') ≤ 2*u := Q'.mul_nonneg _ _ (by decide) hu
  have ht : (0 : Q') ≤ 3+2*u := Q'.zero_le_add _ _ (by decide) h2u
  have hs := Q'.zero_le_add _ _ (Q'.sub_nonneg_of_le hmean)
    (Q'.mul_nonneg _ _ ht (Q'.sub_nonneg_of_le henergy))
  have he : (2*u*E + -(3*((m*m)*Z))) +
      (3+2*u)*(6*(1+u)*(Z*v) + -E) ≈
      3*(P*(Z*v) + -(E+Z*(v+m*m))) := by
    unfold P scoreVarianceFactor
    exact poly_identity_of_normal_eq
      (.add
        (.add (.mul (.mul (.const 2) (.var 0)) (.var 1))
          (.neg (.mul (.const 3) (.mul (.mul (.var 2) (.var 2)) (.var 3)))))
        (.mul (.add (.const 3) (.mul (.const 2) (.var 0)))
          (.add (.mul (.mul (.const 6) (.add (.const 1) (.var 0)))
            (.mul (.var 3) (.var 4))) (.neg (.var 1)))))
      (.mul (.const 3)
        (.add
          (.mul (.add (.add (.const 7) (.mul (.const 10) (.var 0)))
            (.mul (.const 4) (.mul (.var 0) (.var 0))))
            (.mul (.var 3) (.var 4)))
          (.neg (.add (.var 1)
            (.mul (.var 3) (.add (.var 4) (.mul (.var 2) (.var 2))))))))
      (by decide) (fun | 0 => u | 1 => E | 2 => m | 3 => Z | _ => v)
  have hnonneg : (0 : Q') ≤ 3*(P*(Z*v) + -(4*Z)) :=
    Q'.le_trans' _ _ _ hs (Q'.le_of_eqv (Q'.eqv_trans _ _ _ he
      (Q'.mul_eqv_congr_left 3 _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hkin)))))
  have hraw : 4*Z ≤ P*(Z*v) :=
    Q'.le_of_sub_nonneg (Q'.nonneg_of_mul_pos (by decide) hnonneg)
  have hswap : Z*4 ≤ Z*(P*v) := Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv Z 4))
    (Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => P | 1 => Z | _ => v))))
  have h4 : 4 ≤ P*v := Q'.le_of_mul_le_mul_left hswap hZ
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ r h4
    (Q'.le_of_lt (Q'.recipPos_pos P (scoreVarianceFactor_positive C)))
  have hr : (P*v)*r ≈ v := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 1) (.mul (.var 0) (.var 2)))
      (by decide) (fun | 0 => P | 1 => v | _ => r))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left v _ _ (Q'.mul_recipPos_eqv P (scoreVarianceFactor_positive C)))
      (Q'.mul_one_eqv v))
  exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hr)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    H blocks (polyNeg p) ≈ -(H blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | x::xs => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv x.2 (quaternionHaarMono blocks x.1))
        (haar_neg blocks xs)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem unit_amplitude_raw (blocks : Nat) (W f : RatPoly)
    (hunit : HaarCarrierEqv blocks (angularSquare f)
      (polyAdd (cap 4) (polyNeg (polyMul f f)))) :
    H blocks (polyMul W (angularSquare f)) +
      H blocks (polyMul W (polyMul f f)) ≈ 4*H blocks W := by
  have he : H blocks (polyMul W (angularSquare f)) ≈
      4*H blocks W + -(H blocks (polyMul W (polyMul f f))) :=
    Q'.eqv_trans _ _ _ (hunit W) (Q'.eqv_trans _ _ _
      (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 0) (.var 2))))
        (by decide) (fun | 0 => W | 1 => cap 4 | _ => polyMul f f)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left 4 W))
            (quaternionHaar_polySmul blocks 4 W)) (haar_neg blocks _))))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' he (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => 4*H blocks W | _ => H blocks (polyMul W (polyMul f f))))

private theorem raw_second_moment_pin (blocks : Nat) (W f : RatPoly)
    (hZ : (0 : Q') < H blocks W) :
    let Z := H blocks W
    let m := normalizedMoment blocks W f hZ
    let v := normalizedVariance blocks W f hZ
    Z*(v+m*m) ≈ H blocks (polyMul W (polyMul f f)) := by
  let Z := H blocks W
  let F := H blocks (polyMul W (polyMul f f))
  let m := normalizedMoment blocks W f hZ
  let v := normalizedVariance blocks W f hZ
  let r := Q'.recipPos Z hZ
  have hi : v+m*m ≈ F*r := by
    change (F*r + -(m*m)) + m*m ≈ F*r
    exact poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 1))
        (.neg (.mul (.var 2) (.var 2)))) (.mul (.var 2) (.var 2)))
      (.mul (.var 0) (.var 1)) (by decide)
      (fun | 0 => F | 1 => r | _ => m)
  exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left Z _ _ hi)
    (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (by decide) (fun | 0 => Z | 1 => F | _ => r))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left F _ _ (Q'.mul_recipPos_eqv Z hZ))
        (Q'.mul_one_eqv F)))

private theorem raw_mean_mass_pin (blocks : Nat) (W f : RatPoly)
    (hZ : (0 : Q') < H blocks W) :
    normalizedMoment blocks W f hZ * H blocks W ≈
      H blocks (polyMul W f) := by
  let Z := H blocks W
  let A := H blocks (polyMul W f)
  let r := Q'.recipPos Z hZ
  change (A*r)*Z ≈ A
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.var 0) (.mul (.var 2) (.var 1)))
      (by decide) (fun | 0 => A | 1 => r | _ => Z))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left A _ _ (Q'.mul_recipPos_eqv Z hZ))
      (Q'.mul_one_eqv A))

/-- The actual score controls the square of the OWN normalized mean. The
constant auxiliary multiplier has zero angular energy; no centered source
is substituted for the literal head-linear polynomial. -/
theorem raw_mean_square_le_energy {tail : Nat} {W f : RatPoly} {C : Q'}
    (hC : (0 : Q') < C)
    (R : ∀ i j, i < 4 → j < 4 → RelativeBound (tail+1) i j W C)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hlinear : HasQuaternionBlockDegree 0 1 f)
    (hZ : (0 : Q') < H (tail+1) W) :
    let m := normalizedMoment (tail+1) W f hZ
    3*((m*m)*H (tail+1) W) ≤
      2*(C*C)*H (tail+1) (polyMul W (angularSquare f)) := by
  let Z := H (tail+1) W
  let A := H (tail+1) (polyMul W f)
  let E := H (tail+1) (polyMul W (angularSquare f))
  let m := normalizedMoment (tail+1) W f hZ
  let M := (m*m)*Z
  let u := C*C
  let h := cap m
  let S := generalizedResidual tail W h f
  have hh : SupportedQuaternionBlocks (tail+1) h :=
    polySmul_supported (supported_one (tail+1)) m
  have hd (i j : Nat) : RatPolyCoeffEqv (angularDerivative i j h) polyZero :=
    (angularDerivative_smul i j m polyOne).trans
      (((angularDerivative_one i j).smul m).trans (RatPolyCoeffEqv.smul_zero m))
  have henergy : generalizedEnergy tail W h f ≈ 0 := by
    unfold generalizedEnergy
    have hplane (i j : Nat) :
        H (tail+1) (polyMul W
          (polyMul (angularDerivative i j h) (angularDerivative i j f))) ≈ 0 := by
      have hp : RatPolyCoeffEqv
          (polyMul W
            (polyMul (angularDerivative i j h) (angularDerivative i j f)))
          polyZero :=
        (((((hd i j).mul_right (angularDerivative i j f)).trans
          (RatPolyCoeffEqv.mul_zero_left _)).mul_left W).trans
            (RatPolyCoeffEqv.mul_zero_right W))
      exact haar_of_coeff hp
    exact Q'.eqv_trans _ _ _
      (sixValue_congr _ _ (fun i j _ _ => hplane i j)) (by decide)
  have hmul : H (tail+1) (polyMul (polyMul W h) f) ≈ m*A :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (((RatPolyCoeffEqv.mul_assoc W h f).trans
        ((cap_mul_left m f).mul_left W)).trans
        (RatPolyCoeffEqv.polyMul_smul_right m W f)))
      (quaternionHaar_polySmul (tail+1) m (polyMul W f))
  have hmean : m*A ≈ M := Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left m _ _
      (Q'.eqv_symm (raw_mean_mass_pin (tail+1) W f hZ)))
    (Q'.eqv_symm (Q'.mul_assoc_eqv m m Z))
  have hward : S ≈ 3*M := Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.var 0) (.add (.const 0) (.var 0))
      (by decide) (fun _ => S))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_symm henergy) (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _ (generalized_linear_ward tail W h f hlinear)
        (Q'.mul_eqv_congr_left 3 _ _
          (Q'.eqv_trans _ _ _ hmul hmean))))
  have hsquare : H (tail+1) (polyMul W (polyMul h h)) ≈ M :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (((cap_mul m m).mul_left W).trans
        ((RatPolyCoeffEqv.mul_comm W (cap (m*m))).trans
          (cap_mul_left (m*m) W))))
      (quaternionHaar_polySmul (tail+1) (m*m) W)
  have hy := residual_upper_scaled hC R hh hf (2*u)
  have hbound : 2*(2*u)*(3*M) ≤ 6*u*M+(2*u)*(2*u)*E :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left (2*(2*u)) _ _
        (Q'.eqv_symm hward)))
      (Q'.le_trans' _ _ _ hy
        (Q'.le_of_eqv (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left (6*u) _ _ hsquare) (Q'.eqv_refl _))))
  have hnonneg : (0 : Q') ≤ (2*u)*(2*u*E + -(3*M)) :=
    Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le hbound)
      (Q'.le_of_eqv (poly_identity_of_normal_eq
        (.add
          (.add (.mul (.mul (.const 6) (.var 0)) (.var 2))
            (.mul (.mul (.mul (.const 2) (.var 0))
              (.mul (.const 2) (.var 0))) (.var 1)))
          (.neg (.mul (.mul (.const 2) (.mul (.const 2) (.var 0)))
            (.mul (.const 3) (.var 2)))))
        (.mul (.mul (.const 2) (.var 0))
          (.add (.mul (.mul (.const 2) (.var 0)) (.var 1))
            (.neg (.mul (.const 3) (.var 2)))))
        (by decide) (fun | 0 => u | 1 => E | _ => M)))
  exact Q'.le_of_sub_nonneg
    (Q'.nonneg_of_mul_pos
      (Q'.mul_pos (by decide) (Q'.mul_pos hC hC)) hnonneg)

/-- A polynomial variance floor for the literal original weight and its OWN
mean. The kinematic amplitude is a carrier identity, while each of the six
relative score certificates concerns that same complete weight. No retention,
time evolution, or continuum assertion is implicit in this estimate. -/
theorem original_score_variance_floor {tail : Nat} {W f : RatPoly} {C : Q'}
    (hC : (0 : Q') < C)
    (R : ∀ i j, i < 4 → j < 4 → RelativeBound (tail+1) i j W C)
    (hf : SupportedQuaternionBlocks (tail+1) f)
    (hlinear : HasQuaternionBlockDegree 0 1 f)
    (hunit : HaarCarrierEqv (tail+1) (angularSquare f)
      (polyAdd (cap 4) (polyNeg (polyMul f f))))
    (hZ : (0 : Q') < H (tail+1) W) :
    scoreVarianceFloor C ≤ normalizedVariance (tail+1) W f hZ := by
  let Z := H (tail+1) W
  let E := H (tail+1) (polyMul W (angularSquare f))
  let m := normalizedMoment (tail+1) W f hZ
  let v := normalizedVariance (tail+1) W f hZ
  have hm : 3*((m*m)*Z) ≤ 2*(C*C)*E :=
    raw_mean_square_le_energy hC R hf hlinear hZ
  have he : E ≤ 6*(1+C*C)*(Z*v) :=
    energy_le_variance hC R hf hlinear hZ
  have hk : E+Z*(v+m*m) ≈ 4*Z :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl E)
        (raw_second_moment_pin (tail+1) W f hZ))
      (unit_amplitude_raw (tail+1) W f hunit)
  exact score_budget C Z E m v hZ hm he hk

#print axioms generalizedEnergy
#print axioms generalizedResidual
#print axioms generalized_linear_ward
#print axioms independent_shift_ward
#print axioms residual_lower_scaled
#print axioms residual_upper_scaled
#print axioms self_ward
#print axioms scoreVarianceFactor
#print axioms scoreVarianceFactor_positive
#print axioms scoreVarianceFloor
#print axioms scoreVarianceFloor_positive
#print axioms raw_mean_square_le_energy
#print axioms original_score_variance_floor

end YMGap.Continuum.QuaternionHaarGeneralizedLinearWard
