/-
# Generalized exact Ward identity on the original Haar carrier

The auxiliary multiplier h is arbitrary. Angular differentiation of h
produces the energy term, while differentiation of the complete weight W
remains as an explicitly signed residual. No conditional measure, deleted
interaction, or analytic bound enters this identity.
-/

import YMGap.Continuum.QuaternionHaarLinearMeanWard
import YMGap.Continuum.QuaternionHaarRelativeAngularYoung

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

#print axioms generalizedEnergy
#print axioms generalizedResidual
#print axioms generalized_linear_ward
#print axioms independent_shift_ward
#print axioms residual_lower_scaled
#print axioms residual_upper_scaled
#print axioms self_ward

end YMGap.Continuum.QuaternionHaarGeneralizedLinearWard
