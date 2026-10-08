/-
# Literal mixed and frozen paired chain rules

Every ordered mixed derivative is computed before multiplying by frozen
polynomial coefficients. The nine entries contract into the actual scalar
first-jet square and scalar frozen second jet. No coefficient is
differentiated, and no derivative of a completed value is inferred.
-/

import YMGap.Continuum.QPolyHaarAngularChain
import YMGap.Continuum.SU2QuaternionPairedFrozenComplement

namespace YMGap.Continuum.QPolyHaarFrozenChain

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly (Poly)
open YMGap.Constructive.QPolyFormalDerivative (pderiv)
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport (angularDerivative_one)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (pairedDerivative threeSum frozenSecondJet)
open YMGap.Continuum.SU2QuaternionPairedFrozenComplement (frozenFirstJet)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (subst)
open YMGap.Continuum.QPolyHaarAngularChain (paired_congr paired_mul paired_subst)

/-- Actual ordered mixed jet; acceleration is retained in either order. -/
theorem paired_subst_mixed (i j : Fin 3) (x : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (pairedDerivative i (pairedDerivative j (subst x p)))
      (polyAdd
        (polyMul (subst x (pderiv (pderiv p)))
          (polyMul (pairedDerivative i x) (pairedDerivative j x)))
        (polyMul (subst x (pderiv p)) (pairedDerivative i (pairedDerivative j x)))) := by
  refine (paired_congr i (paired_subst j x p)).trans ((paired_mul i _ _).trans ?_)
  exact (((paired_subst i x (pderiv p)).mul_right _).trans
    (RatPolyCoeffEqv.mul_assoc _ _ _)).add (RatPolyCoeffEqv.refl _)

theorem threeSum_congr {f g : Fin 3 → RatPoly}
    (h : ∀ i, RatPolyCoeffEqv (f i) (g i)) : RatPolyCoeffEqv (threeSum f) (threeSum g) :=
  (h 0).add ((h 1).add (h 2))

theorem threeSum_mul_left (a : RatPoly) (f : Fin 3 → RatPoly) :
    RatPolyCoeffEqv (threeSum (fun i => polyMul a (f i))) (polyMul a (threeSum f)) :=
  ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.mul_add_right a (f 1) (f 2)).symm).trans
    (RatPolyCoeffEqv.mul_add_right a (f 0) (polyAdd (f 1) (f 2))).symm

theorem threeSum_mul_right (f : Fin 3 → RatPoly) (a : RatPoly) :
    RatPolyCoeffEqv (threeSum (fun i => polyMul (f i) a)) (polyMul (threeSum f) a) :=
  (threeSum_congr (fun i => RatPolyCoeffEqv.mul_comm (f i) a)).trans
    ((threeSum_mul_left a f).trans (RatPolyCoeffEqv.mul_comm a (threeSum f)))

theorem threeSum_add (f g : Fin 3 → RatPoly) :
    RatPolyCoeffEqv (threeSum (fun i => polyAdd (f i) (g i)))
      (polyAdd (threeSum f) (threeSum g)) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.var 0) (.var 3))
      (.add (.add (.var 1) (.var 4)) (.add (.var 2) (.var 5))))
    (.add (.add (.var 0) (.add (.var 1) (.var 2)))
      (.add (.var 3) (.add (.var 4) (.var 5))))
    (by decide) (fun
      | 0 => f 0 | 1 => f 1 | 2 => f 2
      | 3 => g 0 | 4 => g 1 | _ => g 2)

theorem threeSum_cross (f g : Fin 3 → RatPoly) :
    RatPolyCoeffEqv (threeSum (fun i => threeSum (fun j => polyMul (f i) (g j))))
      (polyMul (threeSum f) (threeSum g)) :=
  (threeSum_congr (fun i => threeSum_mul_left (f i) g)).trans
    (threeSum_mul_right f (threeSum g))

theorem paired_one_add (i : Fin 3) (x : RatPoly) :
    RatPolyCoeffEqv (pairedDerivative i (polyAdd polyOne x)) (pairedDerivative i x) := by
  have h (a b : Nat) : RatPolyCoeffEqv
      (angularDerivative a b (polyAdd polyOne x)) (angularDerivative a b x) :=
    (angularDerivative_add a b polyOne x).trans
      (((angularDerivative_one a b).add (.refl _)).trans (RatPolyCoeffEqv.zero_add _))
  have hi : i=0 ∨ i=1 ∨ i=2 := by
    simp only [Fin.ext_iff]
    omega
  rcases hi with rfl | rfl | rfl
  · exact (h 0 1).add (h 2 3)
  · exact (h 0 2).add (RatPolyCoeffEqv.neg (h 1 3))
  · exact (h 0 3).add (h 1 2)

theorem frozen_one_add_first (u : Fin 3 → RatPoly) (x : RatPoly) :
    RatPolyCoeffEqv (frozenFirstJet u (polyAdd polyOne x)) (frozenFirstJet u x) :=
  threeSum_congr (fun i => (paired_one_add i x).mul_left (u i))

theorem frozen_one_add_second (u : Fin 3 → RatPoly) (x : RatPoly) :
    RatPolyCoeffEqv (frozenSecondJet u (polyAdd polyOne x)) (frozenSecondJet u x) :=
  threeSum_congr (fun i => threeSum_congr (fun j =>
    (paired_congr i (paired_one_add j x)).mul_left (polyMul (u i) (u j))))

/-- Frozen first jet of the SAME finite substitution. -/
theorem frozen_subst_first (u : Fin 3 → RatPoly) (x : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (frozenFirstJet u (subst x p))
      (polyMul (subst x (pderiv p)) (frozenFirstJet u x)) := by
  refine (threeSum_congr (fun i => ((RatPolyCoeffEqv.refl (u i)).mul
    (paired_subst i x p)).trans ?_)).trans (threeSum_mul_left _ _)
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2)))
    (by decide) (fun | 0 => u i | 1 => subst x (pderiv p) | _ => pairedDerivative i x)

/-- All NINE ordered actual jets; polynomial direction coefficients are
only multiplied afterward. This is not the square of a variable vector field. -/
theorem frozen_subst_second (u : Fin 3 → RatPoly) (x : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (frozenSecondJet u (subst x p))
      (polyAdd
        (polyMul (subst x (pderiv (pderiv p)))
          (polyMul (frozenFirstJet u x) (frozenFirstJet u x)))
        (polyMul (subst x (pderiv p)) (frozenSecondJet u x))) := by
  let hx := subst x (pderiv p)
  let hxx := subst x (pderiv (pderiv p))
  let v := fun i => polyMul (u i) (pairedDerivative i x)
  let second := fun i j => polyMul (polyMul (u i) (u j))
    (pairedDerivative i (pairedDerivative j x))
  have cell (i j : Fin 3) : RatPolyCoeffEqv
      (polyMul (polyMul (u i) (u j)) (pairedDerivative i (pairedDerivative j (subst x p))))
      (polyAdd (polyMul hxx (polyMul (v i) (v j))) (polyMul hx (second i j))) :=
    (((RatPolyCoeffEqv.refl _).mul (paired_subst_mixed i j x p)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1))
          (.add (.mul (.var 2) (.mul (.var 3) (.var 4))) (.mul (.var 5) (.var 6))))
        (.add (.mul (.var 2) (.mul (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 4))))
          (.mul (.var 5) (.mul (.mul (.var 0) (.var 1)) (.var 6))))
        (by decide) (fun
          | 0 => u i | 1 => u j | 2 => hxx
          | 3 => pairedDerivative i x | 4 => pairedDerivative j x
          | 5 => hx | _ => pairedDerivative i (pairedDerivative j x))))
  have inner (i : Fin 3) : RatPolyCoeffEqv
      (threeSum (fun j => polyMul (polyMul (u i) (u j))
        (pairedDerivative i (pairedDerivative j (subst x p)))))
      (polyAdd (polyMul hxx (threeSum (fun j => polyMul (v i) (v j))))
        (polyMul hx (threeSum (second i)))) :=
    (threeSum_congr (cell i)).trans
      ((threeSum_add _ _).trans ((threeSum_mul_left hxx _).add (threeSum_mul_left hx _)))
  refine (threeSum_congr inner).trans ((threeSum_add _ _).trans ?_)
  exact ((threeSum_mul_left hxx _).trans
    ((RatPolyCoeffEqv.refl hxx).mul (threeSum_cross v v))).add (threeSum_mul_left hx _)

end YMGap.Continuum.QPolyHaarFrozenChain

#print axioms YMGap.Continuum.QPolyHaarFrozenChain.paired_subst_mixed
#print axioms YMGap.Continuum.QPolyHaarFrozenChain.frozen_subst_first
#print axioms YMGap.Continuum.QPolyHaarFrozenChain.frozen_subst_second
