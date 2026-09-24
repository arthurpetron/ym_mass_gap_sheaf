/-
# Error-free heat-prefix alignment from a positive cutoff endpoint

At prefix length `K+1`, the top bulk fusion coefficient and the negative
boundary coefficient combine to `coeffW w K - coeffW w 1 * coeffW w (K+1)`.
When this explicit scalar is nonnegative, every remaining character quadratic
is nonnegative.  Thus alignment has no cutoff-error term and requires no
certificate for the signed source or its endpoint square.
-/

import YMGap.Continuum.SU2QuaternionHeatFusionQuadratic

namespace YMGap.Continuum.SU2QuaternionHeatFusionCutoffPositive

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BondMovingStep (coeffW coeffW_nonneg)
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionProductHeatPositive
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeatFusionResidual
open YMGap.Continuum.SU2HeatFusionCoefficientPositive
open YMGap.Continuum.QuaternionHaarHeatCertificate (heatPrefix)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)

local infix:50 " ≈ " => Q'.eqv

private theorem haar_neg (n : Nat) : ∀ p : RatPoly,
    quaternionHaar n (polyNeg p) ≈ -(quaternionHaar n p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono n t.1)) (haar_neg n p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem insertion_neg (n : Nat) (W a p : RatPoly) :
    insertion n W a (polyNeg p) ≈ -(insertion n W a p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 0) (.var 1)))
    (by decide) (fun | 0 => polyMul W (polyMul a (liftBoundary n a)) | _ => p)))
    (haar_neg (n+n) _)

private theorem bulk_step (w : Q') (K : Nat) (x : RatPoly) :
    RatPolyCoeffEqv (bulkResidual w (K+1) x)
      (polyAdd (bulkResidual w K x)
        (polySmul (fusionCoeff w (K+1)) (characterPolynomial x (K+1)))) := by
  unfold bulkResidual
  rw [List.range_succ, PolynomialWeightedSumBounds.sum_append]
  exact (RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_zero _)

private theorem endpoint_nonnegative {a b : Q'} (h : b ≤ a) :
    (0 : Q') ≤ a + -b := by
  have hs := Q'.add_le_add_right b a (-b) h
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.add_neg_self_eqv b))) hs

private theorem le_of_difference_nonnegative {a b : Q'} (h : (0 : Q') ≤ a + -b) :
    b ≤ a := by
  have hs := Q'.add_le_add_right 0 (a + -b) b h
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (QPoly.q_zero_add_eqv b))
    (Q'.le_trans' _ _ _ hs (Q'.le_of_eqv
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
        (by decide) (fun | 0 => a | _ => b))))

/-- Alignment of the complete prefix through spin `K+1`, with the cutoff
boundary absorbed by the last bulk coefficient.  The source `a` is arbitrary
apart from support; no square certificate is used. -/
theorem prefix_alignment_no_error {n i : Nat} (hi : i < n) {W a : RatPoly}
    (hW : SupportedQuaternionBlocks (n+n) W)
    (hpositive : ∀ f, SupportedQuaternionBlocks n f → (0 : Q') ≤ haarQuadratic n W f)
    (ha : SupportedQuaternionBlocks n a)
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K : Nat)
    (hendpoint : coeffW w 1 * coeffW w (K+1) ≤ coeffW w K) :
    coeffW w 1 * insertion n W a
        (heatPrefix w (K+1) (scalarAt (n+i) i)) ≤
      insertion n W a
        (polyMul (characterPolynomial (scalarAt (n+i) i) 1)
          (heatPrefix w (K+1) (scalarAt (n+i) i))) := by
  let x := scalarAt (n+i) i
  let H := heatPrefix w (K+1) x
  let c := coeffW w 1
  let top := insertion n W a (characterPolynomial x (K+1))
  let edge := insertion n W a (characterPolynomial x (K+2))
  have hbulk : (0 : Q') ≤ insertion n W a (bulkResidual w K x) := by
    apply sum_insertion_nonnegative
    intro j _
    exact Q'.le_trans' _ _ _
      (Q'.mul_nonneg _ _ (fusionCoeff_nonnegative hw0 hw1 j)
        (character_insertion_nonnegative hi hW hpositive ha (j+1)))
      (Q'.ge_of_eqv (insertion_smul n W a _ _))
  have htop : (0 : Q') ≤ top := character_insertion_nonnegative hi hW hpositive ha (K+1)
  have hedge : (0 : Q') ≤ edge := character_insertion_nonnegative hi hW hpositive ha (K+2)
  have hcoef : (0 : Q') ≤ coeffW w K + -(c * coeffW w (K+1)) :=
    endpoint_nonnegative hendpoint
  have htopTerm : (0 : Q') ≤
      (coeffW w K + -(c * coeffW w (K+1))) * top :=
    Q'.mul_nonneg _ _ hcoef htop
  have hedgeTerm : (0 : Q') ≤ coeffW w (K+1) * edge :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 _) hedge
  have hresEq : insertion n W a
      (polyAdd (bulkResidual w (K+1) x) (boundaryResidual w (K+1) x)) ≈
      insertion n W a (bulkResidual w K x) +
        ((coeffW w K + -(c * coeffW w (K+1))) * top +
          coeffW w (K+1) * edge) := by
    have hb0 := insertion_coeff n W a (bulk_step w K x)
    have hb : insertion n W a (bulkResidual w (K+1) x) ≈
        insertion n W a (bulkResidual w K x) +
          fusionCoeff w (K+1) * top :=
      Q'.eqv_trans _ _ _ hb0
        (Q'.eqv_trans _ _ _ (insertion_add n W a _ _)
          (Q'.add_eqv_congr_left _ _ _ (insertion_smul n W a _ _)))
    simp only [fusionCoeff, Nat.add_sub_cancel] at hb
    unfold boundaryResidual
    exact Q'.eqv_trans _ _ _ (insertion_add n W a _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hb
          (Q'.eqv_trans _ _ _ (insertion_add n W a _ _)
            (Q'.add_eqv_congr' (insertion_smul n W a _ _)
              (Q'.eqv_trans _ _ _ (insertion_neg n W a _)
                (Q'.neg_eqv_congr _ _ (insertion_smul n W a _ _))))))
        (poly_identity_of_normal_eq
          (.add (.add (.var 0)
              (.mul (.add (.add (.var 3) (.var 6))
                (.neg (.mul (.var 5) (.var 1)))) (.var 2)))
            (.add (.mul (.var 1) (.var 4)) (.neg (.mul (.var 6) (.var 2)))))
          (.add (.var 0)
            (.add (.mul (.add (.var 3) (.neg (.mul (.var 5) (.var 1)))) (.var 2))
              (.mul (.var 1) (.var 4)))) (by decide)
          (fun
            | 0 => insertion n W a (bulkResidual w K x)
            | 1 => coeffW w (K+1) | 2 => top | 3 => coeffW w K
            | 4 => edge | 5 => c | _ => coeffW w (K+2))))
  have hres : (0 : Q') ≤ insertion n W a
      (polyAdd (bulkResidual w (K+1) x) (boundaryResidual w (K+1) x)) :=
    Q'.le_trans' _ _ _
      (Q'.zero_le_add _ _ hbulk (Q'.zero_le_add _ _ htopTerm hedgeTerm))
      (Q'.ge_of_eqv hresEq)
  have hl : insertion n W a
      (polyMul (polyAdd (characterPolynomial x 1) (polyNeg (cap c))) H) ≈
      insertion n W a (polyMul (characterPolynomial x 1) H) +
        -(c * insertion n W a H) := by
    have he : RatPolyCoeffEqv
        (polyMul (polyAdd (characterPolynomial x 1) (polyNeg (cap c))) H)
        (polyAdd (polyMul (characterPolynomial x 1) H)
          (polyNeg (polySmul c H))) :=
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
        (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
        (by decide) (fun | 0 => characterPolynomial x 1 | 1 => cap c | _ => H)).trans
        ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left _ _)))
    exact Q'.eqv_trans _ _ _ (insertion_coeff n W a he)
      (Q'.eqv_trans _ _ _ (insertion_add n W a _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _ _ _ (insertion_neg n W a _)
          (Q'.neg_eqv_congr _ _ (insertion_smul n W a _ _)))))
  have hdiff : (0 : Q') ≤
      insertion n W a (polyMul (characterPolynomial x 1) H) +
        -(c * insertion n W a H) :=
    Q'.le_trans' _ _ _ hres (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (insertion_coeff n W a (heat_fusion_residual w (K+1) x))) hl))
  exact le_of_difference_nonnegative hdiff

#print axioms YMGap.Continuum.SU2QuaternionHeatFusionCutoffPositive.prefix_alignment_no_error

end YMGap.Continuum.SU2QuaternionHeatFusionCutoffPositive
