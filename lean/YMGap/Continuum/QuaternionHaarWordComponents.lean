/-
# Full ordered quaternion word telescope

The existing one-factor replacement telescope is exact in all four
coordinates, not just the trace. No quaternion factors are commuted.
The consumer is the whole-word fourth moment in the original edge measure.
-/

import YMGap.Continuum.QuaternionHaarWordDifference

namespace YMGap.Continuum.QuaternionHaarWordComponents

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord (wordWith)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarWordDifference

local infixl:70 " ⋄ " => PolyQuaternion.mul

/-- Indices 0,1,2,3 select the four real coordinates. -/
def component : Nat → PolyQuaternion → RatPoly
  | 0, p => p.scalar
  | 1, p => p.iPart
  | 2, p => p.jPart
  | _+3, p => p.kPart

theorem component_difference (i : Nat) (p q : PolyQuaternion) :
    component i (difference p q) = polyAdd (component i p) (polyNeg (component i q)) := by
  match i with
  | 0 => rfl | 1 => rfl | 2 => rfl | _+3 => rfl

theorem component_congr (i : Nat) {p q : PolyQuaternion} (h : PolyQuaternionCoeffEqv p q) :
    RatPolyCoeffEqv (component i p) (component i q) := by
  match i with
  | 0 => exact h.scalar | 1 => exact h.iPart | 2 => exact h.jPart | _+3 => exact h.kPart

/-- Every coordinate of the literal noncommuting telescope cancels exactly. -/
theorem terms_component (i : Nat) (left right : OrientedBF4Link → PolyQuaternion) :
    ∀ (p : PolyQuaternion) (es : List OrientedBF4Link),
      RatPolyCoeffEqv (polySum ((terms left right p es).map (component i)))
        (component i (difference (p ⋄ wordWith left es) (p ⋄ wordWith right es)))
  | p, [] => by
      rw [component_difference]
      exact ((coeffEvalExpr_eqv_of_normalize_eq
        (.add (.var 0) (.neg (.var 0))) (.const 0) (by decide)
        (fun _ => component i (p ⋄ PolyQuaternion.one))).trans
        (RatPolyCoeffEqv.zero_smul polyOne)).symm
  | p, e::es => by
      have hh := component_congr i
        (((mul_difference p (left e) (right e)).mul
          (PolyQuaternionCoeffEqv.refl (wordWith right es))).trans
          (difference_mul (p ⋄ left e) (p ⋄ right e) (wordWith right es)))
      have hc : RatPolyCoeffEqv
          (polyAdd (component i (difference ((p ⋄ left e) ⋄ wordWith right es)
            ((p ⋄ right e) ⋄ wordWith right es)))
            (component i (difference ((p ⋄ left e) ⋄ wordWith left es)
              ((p ⋄ left e) ⋄ wordWith right es))))
          (component i (difference ((p ⋄ left e) ⋄ wordWith left es)
            ((p ⋄ right e) ⋄ wordWith right es))) := by
        simp only [component_difference]
        exact coeffEvalExpr_eqv_of_normalize_eq
          (.add (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 0))))
          (.add (.var 2) (.neg (.var 1))) (by decide)
          (fun | 0 => component i ((p ⋄ left e) ⋄ wordWith right es)
               | 1 => component i ((p ⋄ right e) ⋄ wordWith right es)
               | _ => component i ((p ⋄ left e) ⋄ wordWith left es))
      have ha : RatPolyCoeffEqv
          (component i (difference ((p ⋄ left e) ⋄ wordWith left es)
            ((p ⋄ right e) ⋄ wordWith right es)))
          (component i (difference (p ⋄ wordWith left (e::es))
            (p ⋄ wordWith right (e::es)))) := by
        simp only [component_difference]
        exact (component_congr i (PolyQuaternionCoeffEqv.mul_assoc p (left e) (wordWith left es))).add
          (RatPolyCoeffEqv.neg
            (component_congr i (PolyQuaternionCoeffEqv.mul_assoc p (right e) (wordWith right es))))
      exact (hh.add (terms_component i left right (p ⋄ left e) es)).trans (hc.trans ha)

/-- One coefficient-level quaternion identity packages all four telescopes. -/
theorem terms_components (left right : OrientedBF4Link → PolyQuaternion)
    (p : PolyQuaternion) (es : List OrientedBF4Link) :
    PolyQuaternionCoeffEqv
      ⟨polySum ((terms left right p es).map PolyQuaternion.scalar),
       polySum ((terms left right p es).map PolyQuaternion.iPart),
       polySum ((terms left right p es).map PolyQuaternion.jPart),
       polySum ((terms left right p es).map PolyQuaternion.kPart)⟩
      (difference (p ⋄ wordWith left es) (p ⋄ wordWith right es)) :=
  ⟨terms_component 0 left right p es, terms_component 1 left right p es,
    terms_component 2 left right p es, terms_component 3 left right p es⟩

#print axioms component_difference
#print axioms component_congr
#print axioms terms_component
#print axioms terms_components

end YMGap.Continuum.QuaternionHaarWordComponents
