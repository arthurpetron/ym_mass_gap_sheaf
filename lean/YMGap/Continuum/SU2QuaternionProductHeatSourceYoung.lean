/-
# A symmetric-kernel Young bound for the original source energy

The product heat kernel is positive and invariant under interchange of its
two slices.  Consequently the actual endpoint product `a(x)a(y)` in the
source energy can be bounded by the single-ended square `a(x)^2`, without a
derivative of `a` and without changing the heat kernel or its normalization.

The stronger identity retains the discarded nonnegative square
`(a(x)-a(y))^2 (f(x)-f(y))^2`.  This is a finite rational statement.  It is
not a comparison with the interacting variance and has no cutoff-, volume-
or spacing-uniform consequence by itself.
-/

import YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
import YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy

namespace YMGap.Continuum.SU2QuaternionProductHeatSourceYoung

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugePolynomialSemantics
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionTwoSliceSwap
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem haar_neg (n : Nat) (p : RatPoly) :
    H n (polyNeg p) ≈ -(H n p) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff (QuaternionHaarAngularCarrier.neg_smul p))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) p)
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
        (.neg (.var 0)) (by decide) (fun _ => H n p)))

private theorem support_lower {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks (n+n) p :=
  fun t ht => Nat.le_trans (hp t ht)
    (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

private theorem support_neg {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (polyNeg p) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact hp s hs

private theorem padded_neg {blocks : Nat} {p q : RatPoly}
    (h : PaddedPolynomialCoeffEqv blocks p q) :
    PaddedPolynomialCoeffEqv blocks (polyNeg p) (polyNeg q) :=
  (PaddedPolynomialCoeffEqv.of_coeff
      (QuaternionHaarAngularCarrier.neg_smul p)).trans
    ((h.smul (-1)).trans (PaddedPolynomialCoeffEqv.of_coeff
      (QuaternionHaarAngularCarrier.neg_smul q).symm))

/-- The one-sided doubled-carrier cost, retaining the complete original
source on the lower endpoint. -/
def singleEndedCost (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (a f : RatPoly) : Q' :=
  weightedPair (n+n) (productHeat n w K ids)
    (polyMul a (jump n f)) (polyMul a (jump n f))

/-- The nonnegative source-increment correction discarded by Young's
inequality. -/
def sourceIncrementCost (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (a f : RatPoly) : Q' :=
  weightedPair (n+n) (productHeat n w K ids)
    (polyMul (jump n a) (jump n f)) (polyMul (jump n a) (jump n f))

private theorem jump_swap {n : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    PaddedPolynomialCoeffEqv (n+n)
      (reindexQuaternionPolynomial (swap n) (jump n p)) (polyNeg (jump n p)) := by
  unfold jump
  rw [reindexQuaternionPolynomial_add, reindexQuaternionPolynomial_neg]
  have hl := PaddedPolynomialCoeffEqv.of_prefix (lower_prefix n p hp)
  have hu := PaddedPolynomialCoeffEqv.of_prefix (upper_prefix n p hp)
  exact (hl.add (padded_neg hu)).trans (PaddedPolynomialCoeffEqv.of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.neg (.var 1)))
      (.neg (.add (.var 1) (.neg (.var 0)))) (by decide)
      (fun | 0 => liftBoundary n p | _ => p)))

theorem singleEnded_swap (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {a f : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f) :
    singleEndedCost n w K ids a f ≈
      weightedPair (n+n) (productHeat n w K ids)
        (polyMul (liftBoundary n a) (jump n f))
        (polyMul (liftBoundary n a) (jump n f)) := by
  let p := polyMul (polyMul (polyMul a (jump n f)) (polyMul a (jump n f)))
    (productHeat n w K ids)
  let q := polyMul
    (polyMul (polyMul (liftBoundary n a) (jump n f))
      (polyMul (liftBoundary n a) (jump n f))) (productHeat n w K ids)
  have hj := jump_swap hf
  have ha' := PaddedPolynomialCoeffEqv.of_prefix (lower_prefix n a ha)
  have hk := productHeat_swap n w K ids hids
  have hpin : PaddedPolynomialCoeffEqv (n+n)
      (reindexQuaternionPolynomial (swap n) p) q := by
    dsimp only [p, q]
    simp only [reindexQuaternionPolynomial_mul]
    exact (((ha'.mul hj).mul (ha'.mul hj)).mul hk).trans
      (PaddedPolynomialCoeffEqv.of_coeff (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.mul (.mul (.var 0) (.neg (.var 1)))
          (.mul (.var 0) (.neg (.var 1)))) (.var 2))
        (.mul (.mul (.mul (.var 0) (.var 1))
          (.mul (.var 0) (.var 1))) (.var 2))
        (by decide) (fun | 0 => liftBoundary n a | 1 => jump n f
                         | _ => productHeat n w K ids)))
  have hp : SupportedQuaternionBlocks (n+n) p :=
    supported_polyMul
      (supported_polyMul
        (supported_polyMul (support_lower ha) (jump_supported hf))
        (supported_polyMul (support_lower ha) (jump_supported hf)))
      (productHeat_supported n w K ids hids)
  have hq : SupportedQuaternionBlocks (n+n) q :=
    supported_polyMul
      (supported_polyMul
        (supported_polyMul (lift_supported ha n) (jump_supported hf))
        (supported_polyMul (lift_supported ha n) (jump_supported hf)))
      (productHeat_supported n w K ids hids)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (SU2QuaternionTwoSliceSwap.haar n p hp))
    (hpin.haar (SU2QuaternionTwoSliceSwap.polynomial_supported n p) hq)

private theorem residual_expansion (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (a f : RatPoly) :
    sourceIncrementCost n w K ids a f ≈
      singleEndedCost n w K ids a f +
      weightedPair (n+n) (productHeat n w K ids)
        (polyMul (liftBoundary n a) (jump n f))
        (polyMul (liftBoundary n a) (jump n f)) +
      -((2 : Q') * weightedPair (n+n) (edgeWeight n w K ids a)
        (jump n f) (jump n f)) := by
  unfold sourceIncrementCost singleEndedCost weightedPair edgeWeight jump
  have hp := coeffEvalExpr_eqv_of_normalize_eq
    (.mul
      (.mul
        (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3))))
        (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 2) (.neg (.var 3)))))
      (.var 4))
    (.add
      (.add
        (.mul (.mul (.mul (.var 0) (.add (.var 2) (.neg (.var 3))))
          (.mul (.var 0) (.add (.var 2) (.neg (.var 3))))) (.var 4))
        (.mul (.mul (.mul (.var 1) (.add (.var 2) (.neg (.var 3))))
          (.mul (.var 1) (.add (.var 2) (.neg (.var 3))))) (.var 4)))
      (.neg (.mul (.const 2)
        (.mul (.mul (.add (.var 2) (.neg (.var 3)))
          (.add (.var 2) (.neg (.var 3))))
          (.mul (.mul (.var 4) (.var 0)) (.var 1))))))
    (by decide) (fun | 0 => a | 1 => liftBoundary n a | 2 => f
                     | 3 => liftBoundary n f | _ => productHeat n w K ids)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hp)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.add_eqv_congr' (quaternionHaar_append _ _ _)
        (Q'.eqv_trans _ _ _
          (haar_neg _ _)
          (Q'.neg_eqv_congr _ _
            (Q'.eqv_trans _ _ _ (haar_of_coeff (cap_mul_left 2 _))
              (quaternionHaar_polySmul _ 2 _))))))

private theorem jumpPair_eq_two_sourceEnergy (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n) {a f : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f) :
    weightedPair (n+n) (edgeWeight n w K ids a) (jump n f) (jump n f) ≈
      (2 : Q') * sourceEnergy n w K ids a f := by
  exact Q'.eqv_trans _ _ _
    (full_jump_pairing n w K ids hids ha hf hf)
    (Q'.mul_eqv_congr_left 2 _ _ (by
      unfold marginalPair sourceEnergy sourceMoment
      exact Q'.add_eqv_congr'
        (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
          (.mul (.mul (.var 0) (.mul (.var 2) (.var 2))) (.var 1))
          (by decide) (fun | 0 => a | 1 => productMap n w K ids a | _ => f)))
        (Q'.eqv_refl _)))

/-- Exact symmetric-kernel Young identity.  The last term is retained with
its favorable sign rather than replaced by a source-derivative budget. -/
theorem four_mul_sourceEnergy_add_increment_eq_two_singleEnded
    (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {a f : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f) :
    (4 : Q') * sourceEnergy n w K ids a f + sourceIncrementCost n w K ids a f ≈
      (2 : Q') * singleEndedCost n w K ids a f := by
  have hs := singleEnded_swap n w K ids hids ha hf
  have hr := residual_expansion n w K ids a f
  have he := jumpPair_eq_two_sourceEnergy n w K ids hids ha hf
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hr)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_symm hs))
          (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left 2 _ _ he))))
      (poly_identity_of_normal_eq
        (.add (.mul (.const 4) (.var 0))
          (.add (.add (.var 1) (.var 1))
            (.neg (.mul (.const 2) (.mul (.const 2) (.var 0))))))
        (.mul (.const 2) (.var 1)) (by decide)
        (fun | 0 => sourceEnergy n w K ids a f
             | _ => singleEndedCost n w K ids a f)))

/-- Young/Schur upper bound for the actual source energy.  The source occurs
only as the zeroth-order one-ended square. -/
theorem two_mul_sourceEnergy_le_singleEndedCost
    (n : Nat) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) {a f : RatPoly}
    (ha : SupportedQuaternionBlocks n a) (hf : SupportedQuaternionBlocks n f) :
    (2 : Q') * sourceEnergy n w K ids a f ≤ singleEndedCost n w K ids a f := by
  let r := polyMul (jump n a) (jump n f)
  have hr : SupportedQuaternionBlocks (n+n) r :=
    supported_polyMul (jump_supported ha) (jump_supported hf)
  have hnonneg : (0 : Q') ≤ sourceIncrementCost n w K ids a f :=
    (productHeatCertificate n hw0 hw1 K hK ids hids).square_insertion_nonnegative r hr
  have hid := four_mul_sourceEnergy_add_increment_eq_two_singleEnded
    n w K ids hids ha hf
  -- Clearing the positive factor two avoids introducing a rational half.
  have htwice : (4 : Q') * sourceEnergy n w K ids a f ≤
      (2 : Q') * singleEndedCost n w K ids a f :=
    Q'.le_trans' _ _ _
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.eqv_symm (QPoly.q_add_zero_eqv _)))
        (Q'.add_le_add_left ((4 : Q') * sourceEnergy n w K ids a f)
          0 (sourceIncrementCost n w K ids a f) hnonneg))
      (Q'.le_of_eqv hid)
  apply Q'.le_of_mul_le_mul_left (c := 2) _ (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (poly_identity_of_normal_eq
    (.mul (.const 2) (.mul (.const 2) (.var 0)))
    (.mul (.const 4) (.var 0)) (by decide)
    (fun _ => sourceEnergy n w K ids a f))) htwice

end YMGap.Continuum.SU2QuaternionProductHeatSourceYoung

#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceYoung.four_mul_sourceEnergy_add_increment_eq_two_singleEnded
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceYoung.two_mul_sourceEnergy_le_singleEndedCost
#print axioms YMGap.Continuum.SU2QuaternionProductHeatSourceYoung.singleEnded_swap
