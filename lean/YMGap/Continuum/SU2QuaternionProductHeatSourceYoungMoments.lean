/-
# Original-carrier moments of the single-ended Young cost

The doubled-kernel cost from `ProductHeatSourceYoung` is expanded without
changing the actual product heat kernel.  Distinct valid selected blocks give
the normalized upper marginal, while the two mixed terms are the original
`productMap` pairing.  No pointwise source bound or interacting-law
normalization is introduced.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
import YMGap.Continuum.SU2QuaternionProductHeatDualForm
import YMGap.Continuum.QuaternionHaarWordDifference

namespace YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionProductHeatDualForm (kineticPair_symm)
open YMGap.Continuum.SU2QuaternionProductHeatContraction (productHeatCertificate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump_supported)
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.QuaternionHaarWordDifference (finite_square_bound)
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

/-- The entire source/observable increment is bounded by the role-swapped
one-ended square. This uses the SAME positive two-copy heat and symmetry,
without a sign or ground-state premise on either source or observable. -/
theorem sourceIncrement_le_four_swapped_singleEnded (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {q f : RatPoly}
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f) :
    sourceIncrementCost n w K ids q f ≤ 4*singleEndedCost n w K ids f q := by
  let W := productHeat n w K ids
  let u := polyMul f (jump n q)
  let v := polyMul (liftBoundary n f) (jump n q)
  let C := singleEndedCost n w K ids f q
  have hfl : SupportedQuaternionBlocks (n+n) f :=
    fun t ht => Nat.le_trans (hf t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right n n))
  have hu := supported_polyMul hfl (jump_supported hq)
  have hv := supported_polyMul (lift_supported hf n) (jump_supported hq)
  have hneg : RatPolyCoeffEqv (polySmul (-1) v) (polyNeg v) :=
    (QuaternionHaarAngularCarrier.neg_smul v).symm
  have hup : H (n+n) (polyMul W (polyMul u u)) ≈ C :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm W (polyMul u u))
  have hvp : H (n+n) (polyMul W (polyMul (polySmul (-1) v) (polySmul (-1) v))) ≈ C :=
    Q'.eqv_trans _ _ _ (haar_of_coeff ((RatPolyCoeffEqv.refl W).mul (hneg.mul hneg)))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.neg (.var 1)) (.neg (.var 1))))
      (.mul (.mul (.var 1) (.var 1)) (.var 0))
      (by decide) (fun | 0 => W | _ => v)))
      (singleEnded_swap n w K ids hids hf hq).symm)
  have hs : ∀ p, p ∈ [u, polySmul (-1) v] → SupportedQuaternionBlocks (n+n) p := by
    intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · subst p; exact hu
    · have he := List.mem_singleton.mp hp
      subst p; exact polySmul_supported hv (-1)
  have hb : ∀ p, p ∈ [u, polySmul (-1) v] →
      H (n+n) (polyMul W (polyMul p p)) ≤ C := by
    intro p hp
    rcases List.mem_cons.mp hp with hp | hp
    · subst p; exact Q'.le_of_eqv hup
    · have he := List.mem_singleton.mp hp
      subst p; exact Q'.le_of_eqv hvp
  have hbound := finite_square_bound (productHeatCertificate n hw0 hw1 K hK ids hids)
    [u, polySmul (-1) v] hs C hb
  have hsum : RatPolyCoeffEqv (polySum [u, polySmul (-1) v])
      (polyMul (jump n q) (jump n f)) := by
    change RatPolyCoeffEqv (polyAdd u (polyAdd (polySmul (-1) v) polyZero)) _
    refine ((RatPolyCoeffEqv.refl u).add (RatPolyCoeffEqv.add_zero _)).trans ?_
    refine ((RatPolyCoeffEqv.refl u).add hneg).trans ?_
    unfold u v jump
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 0) (.add (.var 2) (.neg (.var 3))))
        (.neg (.mul (.var 1) (.add (.var 2) (.neg (.var 3))))))
      (.mul (.add (.var 2) (.neg (.var 3))) (.add (.var 0) (.neg (.var 1))))
      (by decide) (fun | 0 => f | 1 => liftBoundary n f | 2 => q | _ => liftBoundary n q)
  have hleft : sourceIncrementCost n w K ids q f ≈
      H (n+n) (polyMul W (polyMul (polySum [u, polySmul (-1) v])
        (polySum [u, polySmul (-1) v]))) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ W))
      (haar_of_coeff ((RatPolyCoeffEqv.refl W).mul (hsum.symm.mul hsum.symm)))
  have hfour : (Q'.ofNat [u, polySmul (-1) v].length *
      Q'.ofNat [u, polySmul (-1) v].length)*C ≈ 4*C :=
    Q'.mul_eqv_congr_right _ _ C (by decide : (2 : Q')*2 ≈ 4)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hfour))

/-- Joint original-versus-raw second-moment comparison retaining the ENTIRE
increment. The positive role-swapped square pays both terms together; no
source loss, absolute band or substitute probability law is introduced. -/
theorem eight_sourceMoment_add_increment_le_raw_heat_square (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : headCutoff w ≤ K) (ids : List Nat) (hnd : ids.Nodup)
    (hids : ∀ i, i ∈ ids → i < n) {q f : RatPoly}
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f) :
    8*sourceMoment n w K ids q (polyMul f f)+sourceIncrementCost n w K ids q f ≤
      4*(H n (polyMul (polyMul q q) (polyMul f f))+
        H n (polyMul (polyMul q q) (productMap n w K ids (polyMul f f)))) := by
  let Q := H n (polyMul (polyMul q q) (polyMul f f))
  let R := H n (polyMul (polyMul q q) (productMap n w K ids (polyMul f f)))
  let U := sourceMoment n w K ids q (polyMul f f)
  let I := sourceIncrementCost n w K ids q f
  let C := singleEndedCost n w K ids f q
  have hQ : H n (polyMul (polyMul f f) (polyMul q q)) ≈ Q :=
    haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)
  have hR : H n (polyMul (polyMul f f) (productMap n w K ids (polyMul q q))) ≈ R :=
    kineticPair_symm n w K ids hids (polyMul f f) (polyMul q q)
      (supported_polyMul hf hf) (supported_polyMul hq hq)
  have hU : H n (polyMul (polyMul (polyMul f f) q) (productMap n w K ids q)) ≈ U :=
    haar_of_coeff ((RatPolyCoeffEqv.mul_comm (polyMul f f) q).mul_right _)
  have hC : C ≈ Q+R-2*U := Q'.eqv_trans _ _ _
    (singleEndedCost_eq_moments n w K ids hnd hids hf hq)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hQ
      (Q'.add_eqv_congr' hR (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _ hU))))
      (Q'.add_assoc_eqv Q R (-(2*U))).symm)
  have h := Q'.add_le_add_left (8*U) _ _
    (sourceIncrement_le_four_swapped_singleEnded n hw0 hw1 K hK ids hids hq hf)
  have hr : 8*U+4*C ≈ 4*(Q+R) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_left 4 _ _ hC))
      (poly_identity_of_normal_eq
        (.add (.mul (.const 8) (.var 0))
          (.mul (.const 4) (.add (.add (.var 1) (.var 2)) (.neg (.mul (.const 2) (.var 0))))))
        (.mul (.const 4) (.add (.var 1) (.var 2)))
        (by decide) (fun | 0 => U | 1 => Q | _ => R))
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hr)

end YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments

#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments.sourceIncrement_le_four_swapped_singleEnded
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments.eight_sourceMoment_add_increment_le_raw_heat_square

#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments.singleEndedCost_eq_moments
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceYoungMoments.singleEndedCost_eq_weightedPolynomial
