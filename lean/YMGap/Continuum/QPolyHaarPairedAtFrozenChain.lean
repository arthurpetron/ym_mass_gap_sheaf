/-
Finite Horner chain rules for the literal paired frame at any quaternion block.
All nine ordered jets are taken before multiplying frozen polynomial directions.
These are coefficient identities; no supported-Haar differentiation is inferred.
-/

import YMGap.Continuum.QPolyHaarFrozenChain
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFrozenHessian

namespace YMGap.Continuum.QPolyHaarPairedAtFrozenChain

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
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularDerivative)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFrozenHessian (frozenSecondAt)
open YMGap.Continuum.QPolyHaarPositiveSubstitution (subst)
open YMGap.Continuum.QPolyHaarAngularChain (angular_subst)
open YMGap.Continuum.QPolyHaarFrozenChain
  (threeSum_congr threeSum_mul_left threeSum_add threeSum_cross)

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

/-- The existing paired generator at a selected block respects coefficient equality. -/
theorem pairedAt_congr (block : Nat) (i : Fin 3) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (pairedDerivativeAt block i p) (pairedDerivativeAt block i q) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact (angularDerivative_congr _ _ h).add (angularDerivative_congr _ _ h)
  · exact (angularDerivative_congr _ _ h).add
      (RatPolyCoeffEqv.neg (angularDerivative_congr _ _ h))
  · exact (angularDerivative_congr _ _ h).add (angularDerivative_congr _ _ h)

/-- Leibniz for the literal paired frame, including its signed middle direction. -/
theorem pairedAt_mul (block : Nat) (i : Fin 3) (p q : RatPoly) :
    RatPolyCoeffEqv (pairedDerivativeAt block i (polyMul p q))
      (polyAdd (polyMul (pairedDerivativeAt block i p) q)
        (polyMul p (pairedDerivativeAt block i q))) := by
  have hp (a b c d : RatPoly) : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul a q) (polyMul p b))
        (polyAdd (polyMul c q) (polyMul p d)))
      (polyAdd (polyMul (polyAdd a c) q) (polyMul p (polyAdd b d))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 5) (.var 1)))
        (.add (.mul (.var 2) (.var 4)) (.mul (.var 5) (.var 3))))
      (.add (.mul (.add (.var 0) (.var 2)) (.var 4))
        (.mul (.var 5) (.add (.var 1) (.var 3))))
      (by decide) (fun | 0 => a | 1 => b | 2 => c | 3 => d | 4 => q | _ => p)
  have hm (a b c d : RatPoly) : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul a q) (polyMul p b))
        (polyNeg (polyAdd (polyMul c q) (polyMul p d))))
      (polyAdd (polyMul (polyAdd a (polyNeg c)) q)
        (polyMul p (polyAdd b (polyNeg d)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 5) (.var 1)))
        (.neg (.add (.mul (.var 2) (.var 4)) (.mul (.var 5) (.var 3)))))
      (.add (.mul (.add (.var 0) (.neg (.var 2))) (.var 4))
        (.mul (.var 5) (.add (.var 1) (.neg (.var 3)))))
      (by decide) (fun | 0 => a | 1 => b | 2 => c | 3 => d | 4 => q | _ => p)
  rcases direction_cases i with rfl | rfl | rfl
  · exact ((angularDerivative_mul _ _ p q).add (angularDerivative_mul _ _ p q)).trans
      (hp _ _ _ _)
  · exact ((angularDerivative_mul _ _ p q).add
      (RatPolyCoeffEqv.neg (angularDerivative_mul _ _ p q))).trans (hm _ _ _ _)
  · exact ((angularDerivative_mul _ _ p q).add (angularDerivative_mul _ _ p q)).trans
      (hp _ _ _ _)

/-- Literal first paired jet of a finite substitution at any block. -/
theorem pairedAt_subst (block : Nat) (i : Fin 3) (x : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (pairedDerivativeAt block i (subst x p))
      (polyMul (subst x (pderiv p)) (pairedDerivativeAt block i x)) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact ((angular_subst _ _ x p).add (angular_subst _ _ x p)).trans
      (RatPolyCoeffEqv.mul_add_right _ _ _).symm
  · exact ((angular_subst _ _ x p).add
      (RatPolyCoeffEqv.neg (angular_subst _ _ x p))).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (by decide) (fun
          | 0 => subst x (pderiv p)
          | 1 => blockAngularDerivative block 0 2 x
          | _ => blockAngularDerivative block 1 3 x))
  · exact ((angular_subst _ _ x p).add (angular_subst _ _ x p)).trans
      (RatPolyCoeffEqv.mul_add_right _ _ _).symm

/-- Every ordered mixed jet retains the actual scalar acceleration. -/
theorem pairedAt_subst_mixed (block : Nat) (i j : Fin 3) (x : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (pairedDerivativeAt block i (pairedDerivativeAt block j (subst x p)))
      (polyAdd
        (polyMul (subst x (pderiv (pderiv p)))
          (polyMul (pairedDerivativeAt block i x) (pairedDerivativeAt block j x)))
        (polyMul (subst x (pderiv p))
          (pairedDerivativeAt block i (pairedDerivativeAt block j x)))) := by
  refine (pairedAt_congr block i (pairedAt_subst block j x p)).trans
    ((pairedAt_mul block i _ _).trans ?_)
  exact (((pairedAt_subst block i x (pderiv p)).mul_right _).trans
    (RatPolyCoeffEqv.mul_assoc _ _ _)).add (RatPolyCoeffEqv.refl _)

/-- The existing frozen first jet at the selected block. -/
def frozenFirstAt (block : Nat) (u : Fin 3 → RatPoly) (x : RatPoly) : RatPoly :=
  threeSum (fun i => polyMul (u i) (pairedDerivativeAt block i x))

theorem pairedAt_one_add (block : Nat) (i : Fin 3) (x : RatPoly) :
    RatPolyCoeffEqv (pairedDerivativeAt block i (polyAdd polyOne x))
      (pairedDerivativeAt block i x) := by
  have h (a b : Nat) : RatPolyCoeffEqv
      (angularDerivative a b (polyAdd polyOne x)) (angularDerivative a b x) :=
    (angularDerivative_add a b polyOne x).trans
      (((angularDerivative_one a b).add (.refl _)).trans (RatPolyCoeffEqv.zero_add _))
  rcases direction_cases i with rfl | rfl | rfl
  · exact (h _ _).add (h _ _)
  · exact (h _ _).add (RatPolyCoeffEqv.neg (h _ _))
  · exact (h _ _).add (h _ _)

theorem frozenAt_one_add_first (block : Nat) (u : Fin 3 → RatPoly) (x : RatPoly) :
    RatPolyCoeffEqv (frozenFirstAt block u (polyAdd polyOne x)) (frozenFirstAt block u x) :=
  threeSum_congr (fun i => (pairedAt_one_add block i x).mul_left (u i))

theorem frozenAt_one_add_second (block : Nat) (u : Fin 3 → RatPoly) (x : RatPoly) :
    RatPolyCoeffEqv (frozenSecondAt block u (polyAdd polyOne x)) (frozenSecondAt block u x) :=
  threeSum_congr (fun i => threeSum_congr (fun j =>
    (pairedAt_congr block i (pairedAt_one_add block j x)).mul_left
      (polyMul (u i) (u j))))

/-- Frozen first jet of the same finite substitution. -/
theorem frozenAt_subst_first (block : Nat) (u : Fin 3 → RatPoly)
    (x : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (frozenFirstAt block u (subst x p))
      (polyMul (subst x (pderiv p)) (frozenFirstAt block u x)) := by
  refine (threeSum_congr (fun i => ((RatPolyCoeffEqv.refl (u i)).mul
    (pairedAt_subst block i x p)).trans ?_)).trans (threeSum_mul_left _ _)
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2)))
    (by decide) (fun
      | 0 => u i
      | 1 => subst x (pderiv p)
      | _ => pairedDerivativeAt block i x)

/-- All nine ordered jets are contracted only after differentiation. -/
theorem frozenAt_subst_second (block : Nat) (u : Fin 3 → RatPoly)
    (x : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (frozenSecondAt block u (subst x p))
      (polyAdd
        (polyMul (subst x (pderiv (pderiv p)))
          (polyMul (frozenFirstAt block u x) (frozenFirstAt block u x)))
        (polyMul (subst x (pderiv p)) (frozenSecondAt block u x))) := by
  let hx := subst x (pderiv p)
  let hxx := subst x (pderiv (pderiv p))
  let v := fun i => polyMul (u i) (pairedDerivativeAt block i x)
  let second := fun i j => polyMul (polyMul (u i) (u j))
    (pairedDerivativeAt block i (pairedDerivativeAt block j x))
  have cell (i j : Fin 3) : RatPolyCoeffEqv
      (polyMul (polyMul (u i) (u j))
        (pairedDerivativeAt block i (pairedDerivativeAt block j (subst x p))))
      (polyAdd (polyMul hxx (polyMul (v i) (v j))) (polyMul hx (second i j))) :=
    (((RatPolyCoeffEqv.refl _).mul (pairedAt_subst_mixed block i j x p)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1))
          (.add (.mul (.var 2) (.mul (.var 3) (.var 4))) (.mul (.var 5) (.var 6))))
        (.add (.mul (.var 2) (.mul (.mul (.var 0) (.var 3)) (.mul (.var 1) (.var 4))))
          (.mul (.var 5) (.mul (.mul (.var 0) (.var 1)) (.var 6))))
        (by decide) (fun
          | 0 => u i | 1 => u j | 2 => hxx
          | 3 => pairedDerivativeAt block i x | 4 => pairedDerivativeAt block j x
          | 5 => hx | _ => pairedDerivativeAt block i (pairedDerivativeAt block j x))))
  have inner (i : Fin 3) : RatPolyCoeffEqv
      (threeSum (fun j => polyMul (polyMul (u i) (u j))
        (pairedDerivativeAt block i (pairedDerivativeAt block j (subst x p)))))
      (polyAdd (polyMul hxx (threeSum (fun j => polyMul (v i) (v j))))
        (polyMul hx (threeSum (second i)))) :=
    (threeSum_congr (cell i)).trans
      ((threeSum_add _ _).trans ((threeSum_mul_left hxx _).add (threeSum_mul_left hx _)))
  refine (threeSum_congr inner).trans ((threeSum_add _ _).trans ?_)
  exact ((threeSum_mul_left hxx _).trans
    ((RatPolyCoeffEqv.refl hxx).mul (threeSum_cross v v))).add
      (threeSum_mul_left hx _)

/-- The first frozen jet of a radial polynomial evaluated at `1 + X`. -/
theorem frozenAt_subst_one_add_first (block : Nat) (u : Fin 3 → RatPoly)
    (x : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (frozenFirstAt block u (subst (polyAdd polyOne x) p))
      (polyMul (subst (polyAdd polyOne x) (pderiv p)) (frozenFirstAt block u x)) :=
  (frozenAt_subst_first block u (polyAdd polyOne x) p).trans
    ((RatPolyCoeffEqv.refl _).mul (frozenAt_one_add_first block u x))

/-- The complete frozen Hessian of a radial polynomial evaluated at `1 + X`. -/
theorem frozenAt_subst_one_add_second (block : Nat) (u : Fin 3 → RatPoly)
    (x : RatPoly) (p : Poly) :
    RatPolyCoeffEqv (frozenSecondAt block u (subst (polyAdd polyOne x) p))
      (polyAdd
        (polyMul (subst (polyAdd polyOne x) (pderiv (pderiv p)))
          (polyMul (frozenFirstAt block u x) (frozenFirstAt block u x)))
        (polyMul (subst (polyAdd polyOne x) (pderiv p)) (frozenSecondAt block u x))) :=
  (frozenAt_subst_second block u (polyAdd polyOne x) p).trans
    (RatPolyCoeffEqv.add
      ((RatPolyCoeffEqv.refl _).mul
        ((frozenAt_one_add_first block u x).mul
          (frozenAt_one_add_first block u x)))
      ((RatPolyCoeffEqv.refl _).mul (frozenAt_one_add_second block u x)))

end YMGap.Continuum.QPolyHaarPairedAtFrozenChain

#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenChain.pairedAt_congr
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenChain.pairedAt_mul
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenChain.pairedAt_subst
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenChain.pairedAt_subst_mixed
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenChain.pairedAt_one_add
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenChain.frozenAt_one_add_first
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenChain.frozenAt_one_add_second
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenChain.frozenAt_subst_first
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenChain.frozenAt_subst_second
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenChain.frozenAt_subst_one_add_first
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenChain.frozenAt_subst_one_add_second
