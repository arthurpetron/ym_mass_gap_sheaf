/-
# Original-carrier moments of the single-ended Young cost

The doubled-kernel cost from `ProductHeatSourceYoung` is expanded without
changing the actual product heat kernel.  Distinct valid selected blocks give
the normalized upper marginal, while the two mixed terms are the original
`productMap` pairing.  No pointwise source bound or interacting-law
normalization is introduced.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSourceYoung

namespace YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem haar_neg (n : Nat) (p : RatPoly) :
    H n (polyNeg p) ≈ -(H n p) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (QuaternionHaarAngularCarrier.neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
        (.neg (.var 0)) (by decide) (fun _ => H n p)))

private theorem upperEnded_expand (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (a f : RatPoly) :
    weightedPair (n+n) (productHeat n w K ids)
        (polyMul (liftBoundary n a) (jump n f))
        (polyMul (liftBoundary n a) (jump n f)) ≈
      H (n+n) (polyMul (productHeat n w K ids)
        (polyMul (polyMul f f) (liftBoundary n (polyMul a a)))) +
      (H (n+n) (polyMul (productHeat n w K ids)
          (liftBoundary n (polyMul (polyMul a a) (polyMul f f)))) +
        -((2 : Q') * H (n+n) (polyMul (productHeat n w K ids)
          (polyMul f (liftBoundary n (polyMul (polyMul a a) f)))))) := by
  unfold weightedPair jump
  simp only [lift_product]
  have hp := coeffEvalExpr_eqv_of_normalize_eq
    (.mul
      (.mul
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))) (.var 3))
    (.add
      (.mul (.var 3) (.mul (.mul (.var 1) (.var 1)) (.mul (.var 0) (.var 0))))
      (.add
        (.mul (.var 3) (.mul (.mul (.var 0) (.var 0)) (.mul (.var 2) (.var 2))))
        (.neg (.mul (.const 2)
          (.mul (.var 3) (.mul (.var 1) (.mul (.mul (.var 0) (.var 0)) (.var 2))))))))
    (by decide) (fun | 0 => liftBoundary n a | 1 => f
                     | 2 => liftBoundary n f | _ => productHeat n w K ids)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (Q'.eqv_trans _ _ _ (haar_neg _ _)
              (Q'.neg_eqv_congr _ _
                (Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left 2 _))
                  (quaternionHaar_polySmul _ 2 _))))))))

/-- Exact original-carrier three-moment expansion of the one-ended cost. -/
theorem singleEndedCost_eq_moments (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hnd : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) {a f : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f) :
    singleEndedCost n w K ids a f ≈
      H n (polyMul (polyMul a a) (polyMul f f)) +
      (H n (polyMul (polyMul a a) (productMap n w K ids (polyMul f f))) +
        -((2 : Q') * H n (polyMul (polyMul (polyMul a a) f)
          (productMap n w K ids f)))) := by
  have hs := singleEnded_swap n w K ids hids ha hf
  have hx := upperEnded_expand n w K ids a f
  have haa : SupportedQuaternionBlocks n (polyMul a a) := supported_polyMul ha ha
  have hff : SupportedQuaternionBlocks n (polyMul f f) := supported_polyMul hf hf
  have haaff : SupportedQuaternionBlocks n (polyMul (polyMul a a) (polyMul f f)) :=
    supported_polyMul haa hff
  have hfirst := Q'.eqv_symm
    (productMap_pairing n w K ids (polyMul f f) (polyMul a a))
  have hsecond := productHeat_upper_marginal n w K ids hnd hids
    (polyMul (polyMul a a) (polyMul f f)) haaff
  have hthird := Q'.eqv_symm
    (productMap_pairing n w K ids f (polyMul (polyMul a a) f))
  exact Q'.eqv_trans _ _ _ hs
    (Q'.eqv_trans _ _ _ hx
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hfirst
          (Q'.add_eqv_congr' hsecond
            (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _ hthird))))
        (poly_identity_of_normal_eq
          (.add (.var 0) (.add (.var 1) (.neg (.mul (.const 2) (.var 2)))))
          (.add (.var 1) (.add (.var 0) (.neg (.mul (.const 2) (.var 2)))))
          (by decide)
          (fun | 0 => H n (polyMul (polyMul a a)
                       (productMap n w K ids (polyMul f f)))
               | 1 => H n (polyMul (polyMul a a) (polyMul f f))
               | _ => H n (polyMul (polyMul (polyMul a a) f)
                       (productMap n w K ids f))))))

private theorem collect_three_moments (n : Nat) (A f Pf2 Pf : RatPoly) :
    H n (polyMul A (polyMul f f)) +
      (H n (polyMul A Pf2) +
        -((2 : Q') * H n (polyMul (polyMul A f) Pf))) ≈
      H n (polyMul A
        (polyAdd (polyMul f f)
          (polyAdd Pf2 (polyNeg (polyMul (cap 2) (polyMul f Pf)))))) := by
  have hc := haar_of_coeff (blocks := n) (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0)
        (.add (.mul (.var 1) (.var 1))
          (.add (.var 2) (.neg (.mul (.const 2) (.mul (.var 1) (.var 3)))))))
      (.add
        (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.add
          (.mul (.var 0) (.var 2))
          (.neg (.mul (.const 2)
            (.mul (.mul (.var 0) (.var 1)) (.var 3))))))
      (by decide) (fun | 0 => A | 1 => f | 2 => Pf2 | _ => Pf))
  apply Q'.eqv_symm
  refine Q'.eqv_trans _ _ _ hc ?_
  exact Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
          (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (Q'.eqv_trans _ _ _ (haar_neg _ _)
              (Q'.neg_eqv_congr _ _
                (Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left 2 _))
                  (quaternionHaar_polySmul _ 2 _)))))))

/-- The same expansion collected under one original Haar functional. -/
theorem singleEndedCost_eq_weightedPolynomial (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hnd : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) {a f : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f) :
    singleEndedCost n w K ids a f ≈
      H n (polyMul (polyMul a a)
        (polyAdd (polyMul f f)
          (polyAdd (productMap n w K ids (polyMul f f))
            (polyNeg (polyMul (cap 2) (polyMul f (productMap n w K ids f))))))) :=
  Q'.eqv_trans _ _ _ (singleEndedCost_eq_moments n w K ids hnd hids ha hf)
    (collect_three_moments n (polyMul a a) f
      (productMap n w K ids (polyMul f f)) (productMap n w K ids f))

end YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments

#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments.singleEndedCost_eq_moments
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments.singleEndedCost_eq_weightedPolynomial
