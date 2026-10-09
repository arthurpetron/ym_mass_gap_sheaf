/-
Raw finite product rules for the actual paired frame at any block.
The nine ordered second jets precede all frozen direction coefficients.
No commutation of ordered derivatives or differentiation of u is used.
-/

import YMGap.Continuum.QPolyHaarPairedAtFrozenChain

namespace YMGap.Continuum.QPolyHaarPairedAtFrozenProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularReindex (blockAngularDerivative)
open YMGap.Continuum.SU2QuaternionPairedFrameScalarJets (threeSum)
open YMGap.Continuum.SU2QuaternionPairedFrameAt (pairedDerivativeAt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFrozenHessian (frozenSecondAt)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.QPolyHaarPairedAtFrozenChain
  (pairedAt_congr pairedAt_mul frozenFirstAt)
open YMGap.Continuum.QPolyHaarFrozenChain
  (threeSum_congr threeSum_mul_left threeSum_mul_right threeSum_add threeSum_cross)

private theorem direction_cases (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  simp only [Fin.ext_iff]
  omega

/-- Additivity of the literal selected-block paired direction. -/
theorem pairedAt_add (block : Nat) (i : Fin 3) (p q : RatPoly) :
    RatPolyCoeffEqv (pairedDerivativeAt block i (polyAdd p q))
      (polyAdd (pairedDerivativeAt block i p) (pairedDerivativeAt block i q)) := by
  rcases direction_cases i with rfl | rfl | rfl
  · exact ((angularDerivative_add _ _ p q).add
      (angularDerivative_add _ _ p q)).trans (RatPolyCoeffEqv.four_add_swap _ _ _ _)
  · refine (RatPolyCoeffEqv.add (angularDerivative_add _ _ p q)
      (RatPolyCoeffEqv.neg (angularDerivative_add _ _ p q))).trans ?_
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
      (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3))))
      (by decide) (fun
        | 0 => blockAngularDerivative block 0 2 p
        | 1 => blockAngularDerivative block 0 2 q
        | 2 => blockAngularDerivative block 1 3 p
        | _ => blockAngularDerivative block 1 3 q)
  · exact ((angularDerivative_add _ _ p q).add
      (angularDerivative_add _ _ p q)).trans (RatPolyCoeffEqv.four_add_swap _ _ _ _)

/-- Coefficient equality transports through the frozen first jet. -/
theorem frozenFirstAt_congr (block : Nat) (u : Fin 3 → RatPoly)
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (frozenFirstAt block u p) (frozenFirstAt block u q) :=
  threeSum_congr (fun i => (pairedAt_congr block i h).mul_left (u i))

/-- Coefficient equality transports through every ordered frozen second jet. -/
theorem frozenSecondAt_congr (block : Nat) (u : Fin 3 → RatPoly)
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (frozenSecondAt block u p) (frozenSecondAt block u q) :=
  threeSum_congr (fun i => threeSum_congr (fun j =>
    (pairedAt_congr block i (pairedAt_congr block j h)).mul_left
      (polyMul (u i) (u j))))

/-- Frozen first derivative obeys Leibniz on arbitrary raw polynomials. -/
theorem frozenFirstAt_mul (block : Nat) (u : Fin 3 → RatPoly) (p q : RatPoly) :
    RatPolyCoeffEqv (frozenFirstAt block u (polyMul p q))
      (polyAdd (polyMul (frozenFirstAt block u p) q)
        (polyMul p (frozenFirstAt block u q))) := by
  have hcell (i : Fin 3) : RatPolyCoeffEqv
      (polyMul (u i) (pairedDerivativeAt block i (polyMul p q)))
      (polyAdd
        (polyMul (polyMul (u i) (pairedDerivativeAt block i p)) q)
        (polyMul p (polyMul (u i) (pairedDerivativeAt block i q)))) :=
    ((RatPolyCoeffEqv.refl _).mul (pairedAt_mul block i p q)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.mul (.var 1) (.var 3)) (.mul (.var 2) (.var 4))))
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 3))
          (.mul (.var 2) (.mul (.var 0) (.var 4))))
        (by decide) (fun
          | 0 => u i | 1 => pairedDerivativeAt block i p
          | 2 => p | 3 => q | _ => pairedDerivativeAt block i q))
  exact (threeSum_congr hcell).trans
    ((threeSum_add _ _).trans
      ((threeSum_mul_right _ q).add (threeSum_mul_left p _)))

private theorem threeSum_four (a b c d : Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (threeSum (fun i => polyAdd (polyAdd (a i) (b i)) (polyAdd (c i) (d i))))
      (polyAdd (polyAdd (threeSum a) (threeSum b))
        (polyAdd (threeSum c) (threeSum d))) :=
  (threeSum_add _ _).trans ((threeSum_add a b).add (threeSum_add c d))

private theorem doubleSum_four
    (a b c d : Fin 3 → Fin 3 → RatPoly) :
    RatPolyCoeffEqv
      (threeSum (fun i => threeSum (fun j =>
        polyAdd (polyAdd (a i j) (b i j)) (polyAdd (c i j) (d i j)))))
      (polyAdd
        (polyAdd (threeSum (fun i => threeSum (a i)))
          (threeSum (fun i => threeSum (b i))))
        (polyAdd (threeSum (fun i => threeSum (c i)))
          (threeSum (fun i => threeSum (d i))))) :=
  (threeSum_congr (fun i => threeSum_four (a i) (b i) (c i) (d i))).trans
    (threeSum_four _ _ _ _)

/-- Every ordered second product jet has both distinct cross terms. -/
theorem pairedAt_mul_mixed (block : Nat) (i j : Fin 3) (p q : RatPoly) :
    RatPolyCoeffEqv
      (pairedDerivativeAt block i (pairedDerivativeAt block j (polyMul p q)))
      (polyAdd
        (polyAdd
          (polyMul (pairedDerivativeAt block i (pairedDerivativeAt block j p)) q)
          (polyMul (pairedDerivativeAt block j p) (pairedDerivativeAt block i q)))
        (polyAdd
          (polyMul (pairedDerivativeAt block i p) (pairedDerivativeAt block j q))
          (polyMul p (pairedDerivativeAt block i (pairedDerivativeAt block j q))))) :=
  (pairedAt_congr block i (pairedAt_mul block j p q)).trans
    ((pairedAt_add block i _ _).trans
      ((pairedAt_mul block i _ _).add (pairedAt_mul block i _ _)))

/-- Full nine-entry frozen product Hessian. The two mixed sums combine only
after contraction, using coefficient commutativity and the three-sum cross law. -/
theorem frozenSecondAt_mul (block : Nat) (u : Fin 3 → RatPoly) (p q : RatPoly) :
    RatPolyCoeffEqv (frozenSecondAt block u (polyMul p q))
      (polyAdd
        (polyAdd (polyMul (frozenSecondAt block u p) q)
          (polySmul 2 (polyMul (frozenFirstAt block u p) (frozenFirstAt block u q))))
        (polyMul p (frozenSecondAt block u q))) := by
  let v : Fin 3 → RatPoly := fun i => polyMul (u i) (pairedDerivativeAt block i p)
  let w : Fin 3 → RatPoly := fun i => polyMul (u i) (pairedDerivativeAt block i q)
  let A : Fin 3 → Fin 3 → RatPoly := fun i j =>
    polyMul (polyMul (polyMul (u i) (u j))
      (pairedDerivativeAt block i (pairedDerivativeAt block j p))) q
  let B : Fin 3 → Fin 3 → RatPoly := fun i j => polyMul (w i) (v j)
  let C : Fin 3 → Fin 3 → RatPoly := fun i j => polyMul (v i) (w j)
  let D : Fin 3 → Fin 3 → RatPoly := fun i j =>
    polyMul p (polyMul (polyMul (u i) (u j))
      (pairedDerivativeAt block i (pairedDerivativeAt block j q)))
  have hcell (i j : Fin 3) : RatPolyCoeffEqv
      (polyMul (polyMul (u i) (u j))
        (pairedDerivativeAt block i (pairedDerivativeAt block j (polyMul p q))))
      (polyAdd (polyAdd (A i j) (B i j)) (polyAdd (C i j) (D i j))) :=
    ((RatPolyCoeffEqv.refl _).mul (pairedAt_mul_mixed block i j p q)).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.var 0) (.var 1))
          (.add (.add (.mul (.var 2) (.var 9)) (.mul (.var 3) (.var 4)))
            (.add (.mul (.var 5) (.var 6)) (.mul (.var 8) (.var 7)))))
        (.add
          (.add (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 9))
            (.mul (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 3))))
          (.add (.mul (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 6)))
            (.mul (.var 8) (.mul (.mul (.var 0) (.var 1)) (.var 7)))))
        (by decide) (fun
          | 0 => u i | 1 => u j
          | 2 => pairedDerivativeAt block i (pairedDerivativeAt block j p)
          | 3 => pairedDerivativeAt block j p
          | 4 => pairedDerivativeAt block i q
          | 5 => pairedDerivativeAt block i p
          | 6 => pairedDerivativeAt block j q
          | 7 => pairedDerivativeAt block i (pairedDerivativeAt block j q)
          | 8 => p | _ => q))
  have hA : RatPolyCoeffEqv
      (threeSum (fun i => threeSum (A i)))
      (polyMul (frozenSecondAt block u p) q) :=
    (threeSum_congr (fun i => threeSum_mul_right _ q)).trans
      (threeSum_mul_right _ q)
  have hB : RatPolyCoeffEqv
      (threeSum (fun i => threeSum (B i)))
      (polyMul (frozenFirstAt block u q) (frozenFirstAt block u p)) :=
    threeSum_cross w v
  have hC : RatPolyCoeffEqv
      (threeSum (fun i => threeSum (C i)))
      (polyMul (frozenFirstAt block u p) (frozenFirstAt block u q)) :=
    threeSum_cross v w
  have hD : RatPolyCoeffEqv
      (threeSum (fun i => threeSum (D i)))
      (polyMul p (frozenSecondAt block u q)) :=
    (threeSum_congr (fun i => threeSum_mul_left p _)).trans
      (threeSum_mul_left p _)
  have hfour : RatPolyCoeffEqv
      (frozenSecondAt block u (polyMul p q))
      (polyAdd
        (polyAdd (polyMul (frozenSecondAt block u p) q)
          (polyMul (frozenFirstAt block u q) (frozenFirstAt block u p)))
        (polyAdd (polyMul (frozenFirstAt block u p) (frozenFirstAt block u q))
          (polyMul p (frozenSecondAt block u q)))) :=
    (threeSum_congr (fun i => threeSum_congr (hcell i))).trans
      ((doubleSum_four A B C D).trans ((hA.add hB).add (hC.add hD)))
  refine hfour.trans ?_
  let P := frozenFirstAt block u p
  let Q := frozenFirstAt block u q
  let L := polyMul (frozenSecondAt block u p) q
  let R := polyMul p (frozenSecondAt block u q)
  have hcomm : RatPolyCoeffEqv (polyMul Q P) (polyMul P Q) :=
    RatPolyCoeffEqv.mul_comm Q P
  have hsum : RatPolyCoeffEqv
      (polyAdd (polyAdd L (polyMul P Q)) (polyAdd (polyMul P Q) R))
      (polyAdd (polyAdd L (polySmul 2 (polyMul P Q))) R) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2)))
      (.add (.add (.var 0) (.mul (.const 2) (.var 1))) (.var 2))
      (by decide) (fun | 0 => L | 1 => polyMul P Q | _ => R)).trans
      (((RatPolyCoeffEqv.refl _).add (cap_mul_left 2 (polyMul P Q))).add
        (RatPolyCoeffEqv.refl _))
  exact (((RatPolyCoeffEqv.refl L).add hcomm).add
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.refl R))).trans hsum

end YMGap.Continuum.QPolyHaarPairedAtFrozenProduct

#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenProduct.pairedAt_add
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenProduct.frozenFirstAt_congr
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenProduct.frozenSecondAt_congr
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenProduct.frozenFirstAt_mul
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenProduct.pairedAt_mul_mixed
#print axioms YMGap.Continuum.QPolyHaarPairedAtFrozenProduct.frozenSecondAt_mul
