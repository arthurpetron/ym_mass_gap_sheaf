/-
# Paying a moving OWN center in original chronological lag differences

The SAME rational center is retained in both endpoint copies and at both
lags. Its square cancels exactly. Only the difference of the original
endpoint means remains; it is paid by the original boundary-forgetting
bound, uniformly in both lags and the late heat cutoff. The OWN odd-window
center is bounded by the supplied finite polynomial interval, not by an
additional analytic premise.

This is a fixed-nome, fixed-width finite estimate. It neither bounds the
remaining raw two-point difference relative to the interacting variance
nor supplies spatial, coupling, spacing or physical-mass uniformity.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowCenteredProduct
import YMGap.Constructive.CRealMul
import YMGap.Constructive.CRealAdd

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowLagMeanControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarPolynomialInterval (Interval)
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval (polynomialInterval polynomialCap)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

/-- Original two-point value, with its actual lag-dependent partition. -/
def rawPair {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n L : Nat) (f : RatPoly) : Q' :=
  windowRatio hw0 hw1 K width hK n L n (polyMul f (liftBoundary (L*(N width)) f))

/-- Both copies retain the supplied center; no recentering at lag L. -/
def centeredPair {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n L : Nat) (f : RatPoly) (c : Q') : Q' :=
  windowRatio hw0 hw1 K width hK n L n
    (polyMul (shifted f c) (liftBoundary (L*(N width)) (shifted f c)))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem shifted_pair {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n L : Nat) (p q : RatPoly) (c : Q') :
    windowRatio hw0 hw1 K width hK n L n (polyMul (shifted p c) (shifted q c)) ≈
      windowRatio hw0 hw1 K width hK n L n (polyMul p q) +
        -(c * (windowRatio hw0 hw1 K width hK n L n p +
          windowRatio hw0 hw1 K width hK n L n q)) + c*c := by
  let F := windowRatio hw0 hw1 K width hK n L n
  have addL (a b d : RatPoly) : F (polyMul (polyAdd a b) d) ≈
      F (polyMul a d) + F (polyMul b d) := by
    rw [polyMul_add_left_exact]
    exact windowRatio_add hw0 hw1 K width hK n L n _ _
  have addR (a b d : RatPoly) : F (polyMul a (polyAdd b d)) ≈
      F (polyMul a b) + F (polyMul a d) :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK n L n
        (RatPolyCoeffEqv.mul_add_right a b d))
      (windowRatio_add hw0 hw1 K width hK n L n _ _)
  have scaleL (a : Q') (b d : RatPoly) : F (polyMul (polySmul a b) d) ≈
      a * F (polyMul b d) :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK n L n
        (RatPolyCoeffEqv.polyMul_smul_left a b d))
      (windowRatio_smul hw0 hw1 K width hK n L n a _)
  have scaleR (a : Q') (b d : RatPoly) : F (polyMul b (polySmul a d)) ≈
      a * F (polyMul b d) :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK n L n
        (RatPolyCoeffEqv.polyMul_smul_right a b d))
      (windowRatio_smul hw0 hw1 K width hK n L n a _)
  have right (a : RatPoly) : F (polyMul a (shifted q c)) ≈
      1 * F (polyMul a q) + (-c) * F (polyMul a polyOne) :=
    Q'.eqv_trans _ _ _ (addR a _ _)
      (Q'.add_eqv_congr' (scaleR 1 a q) (scaleR (-c) a polyOne))
  have hpo : F (polyMul p polyOne) ≈ F p :=
    windowRatio_congr hw0 hw1 K width hK n L n (RatPolyCoeffEqv.mul_one p)
  have hoq : F (polyMul polyOne q) ≈ F q :=
    windowRatio_congr hw0 hw1 K width hK n L n (RatPolyCoeffEqv.one_mul q)
  have hoo : F (polyMul polyOne polyOne) ≈ 1 :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK n L n (RatPolyCoeffEqv.mul_one polyOne))
      (windowRatio_one hw0 hw1 K width hK n L n)
  have he : F (polyMul (shifted p c) (shifted q c)) ≈
      1 * (1 * F (polyMul p q) + (-c)*F p) +
        (-c) * (1*F q + (-c)*1) :=
    Q'.eqv_trans _ _ _ (addL _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (scaleL 1 p _) (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (right p)
            (Q'.add_eqv_congr' (Q'.eqv_refl _) (qmul (Q'.eqv_refl _) hpo)))))
        (Q'.eqv_trans _ _ _ (scaleL (-c) polyOne _) (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (right polyOne)
            (Q'.add_eqv_congr' (qmul (Q'.eqv_refl _) hoq)
              (qmul (Q'.eqv_refl _) hoo))))))
  exact Q'.eqv_trans _ _ _ he
    (poly_identity_of_normal_eq
      (.add (.mul (.const 1) (.add (.mul (.const 1) (.var 0))
        (.mul (.neg (.var 3)) (.var 1))))
        (.mul (.neg (.var 3)) (.add (.mul (.const 1) (.var 2))
          (.mul (.neg (.var 3)) (.const 1)))))
      (.add (.add (.var 0) (.neg (.mul (.var 3) (.add (.var 1) (.var 2)))))
        (.mul (.var 3) (.var 3))) (by decide)
      (fun | 0 => F (polyMul p q) | 1 => F p | 2 => F q | _ => c))

/-- The finite center need not be the mean at this longer horizon. -/
theorem centered_pair_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n L : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (c : Q') :
    centeredPair hw0 hw1 K width hK n L f c ≈
      rawPair hw0 hw1 K width hK n L f +
        -((c+c) * windowRatio hw0 hw1 K width hK n L n f) + c*c := by
  have hsize : (L+1)*(N width)=N width+L*(N width) := by
    rw [Nat.succ_mul]; omega
  have hs := shifted_supported hf c
  have hsf : SupportedQuaternionBlocks ((L+1)*(N width)) (shifted f c) :=
    fun t ht => Nat.le_trans (hs t ht) (Nat.mul_le_mul_left 4 (by rw [hsize]; omega))
  have hlf : SupportedQuaternionBlocks ((L+1)*(N width)) (liftBoundary (L*(N width)) f) :=
    by rw [hsize]; exact lift_supported hf (L*(N width))
  have hls : SupportedQuaternionBlocks ((L+1)*(N width))
      (liftBoundary (L*(N width)) (shifted f c)) :=
    by rw [hsize]; exact lift_supported hs (L*(N width))
  have he : PaddedPolynomialCoeffEqv ((L+1)*(N width))
      (liftBoundary (L*(N width)) (shifted f c))
      (shifted (liftBoundary (L*(N width)) f) c) := by
    unfold shifted
    rw [lift_add, lift_smul, lift_smul]
    exact ((PaddedPolynomialCoeffEqv.refl _ _).smul 1).add
      ((lift_one ((L+1)*(N width)) (L*(N width))).smul (-c))
  have hex := Q'.eqv_trans _ _ _
    (windowRatio_padded_congr hw0 hw1 K width hK n L n
      (supported_polyMul hsf hls) (supported_polyMul hsf (shifted_supported hlf c))
      ((PaddedPolynomialCoeffEqv.refl _ _).mul he))
    (shifted_pair hw0 hw1 K width hK n L f (liftBoundary (L*(N width)) f) c)
  have hm := endpoint_means_eqv hw0 hw1 K width hK n L hf
  have hreplace : rawPair hw0 hw1 K width hK n L f +
      -(c*(windowRatio hw0 hw1 K width hK n L n f +
        windowRatio hw0 hw1 K width hK n L n (liftBoundary (L*(N width)) f))) + c*c ≈
      rawPair hw0 hw1 K width hK n L f +
        -(c*(windowRatio hw0 hw1 K width hK n L n f +
          windowRatio hw0 hw1 K width hK n L n f)) + c*c := Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (Q'.eqv_refl (rawPair hw0 hw1 K width hK n L f))
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.eqv_symm hm))))) (Q'.eqv_refl (c*c))
  exact Q'.eqv_trans _ _ _ hex (Q'.eqv_trans _ _ _ hreplace
    (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.mul (.var 1) (.add (.var 2) (.var 2)))))
        (.mul (.var 1) (.var 1)))
      (.add (.add (.var 0) (.neg (.mul (.add (.var 1) (.var 1)) (.var 2))))
        (.mul (.var 1) (.var 1))) (by decide)
      (fun
        | 0 => rawPair hw0 hw1 K width hK n L f
        | 1 => c
        | _ => windowRatio hw0 hw1 K width hK n L n f)))

/-- The common center's square cancels before any limit is invoked. -/
theorem centered_lag_difference_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n L J : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) (c : Q') :
    centeredPair hw0 hw1 K width hK n L f c +
        -(centeredPair hw0 hw1 K width hK n J f c) ≈
      rawPair hw0 hw1 K width hK n L f + -(rawPair hw0 hw1 K width hK n J f) +
        -((c+c) * (windowRatio hw0 hw1 K width hK n L n f +
          -(windowRatio hw0 hw1 K width hK n J n f))) :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (centered_pair_pin hw0 hw1 K width hK n L hf c)
      (Q'.neg_eqv_congr _ _ (centered_pair_pin hw0 hw1 K width hK n J hf c)))
    (poly_identity_of_normal_eq
      (.add (.add (.add (.var 0) (.neg (.mul (.add (.var 4) (.var 4)) (.var 2))))
        (.mul (.var 4) (.var 4)))
        (.neg (.add (.add (.var 1) (.neg (.mul (.add (.var 4) (.var 4)) (.var 3))))
          (.mul (.var 4) (.var 4)))))
      (.add (.add (.var 0) (.neg (.var 1)))
        (.neg (.mul (.add (.var 4) (.var 4)) (.add (.var 2) (.neg (.var 3)))))) (by decide)
      (fun
        | 0 => rawPair hw0 hw1 K width hK n L f
        | 1 => rawPair hw0 hw1 K width hK n J f
        | 2 => windowRatio hw0 hw1 K width hK n L n f
        | 3 => windowRatio hw0 hw1 K width hK n J n f
        | _ => c))

private theorem signed_perturbation_bounds {x y u v B d : Q'}
    (h : x ≈ y + -(u*v)) (hB : (0 : Q') ≤ B) (hd : (0 : Q') ≤ d)
    (hu : -B ≤ u ∧ u ≤ B) (hv : -d ≤ v ∧ v ≤ d) :
    x ≤ y+B*d ∧ y ≤ x+B*d := by
  have hp := Q'.mul_le_of_bounds hB hd hu.1 hu.2 hv.1 hv.2
  have hnu : -B ≤ -u ∧ -u ≤ B :=
    ⟨Q'.neg_le_neg hu.2, Q'.le_trans' _ _ _ (Q'.neg_le_neg hu.1)
      (Q'.le_of_eqv (Q'.neg_neg_eqv B))⟩
  have hnp : -(u*v) ≤ B*d := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.neg_mul_eqv u v))
    (Q'.mul_le_of_bounds hB hd hnu.1 hnu.2 hv.1 hv.2)
  have hreverse : y ≈ x+u*v := Q'.eqv_symm
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (u*v) h)
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0) (by decide)
        (fun | 0 => y | _ => u*v)))
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv h) (Q'.add_le_add_left y _ _ hnp),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hreverse) (Q'.add_le_add_left x _ _ hp)⟩

/-- The ACTUAL moving odd-window mean is paid, with no longer-lag mean
substitution. Both lags (including zero) and late K share the same bound.
Only the displayed nome/width-dependent q is used. -/
theorem own_centered_lag_difference_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n L J : Nat)
    {f : RatPoly} {C : Q'} (I : Interval (N width) f C) :
    let c := middleRatio hw0 hw1 K width hK (n+1) n f
    let error := mixRate hw0 hw1 width ^ n * ((C+C)*(C+C))
    centeredPair hw0 hw1 K width hK n L f c +
        -(centeredPair hw0 hw1 K width hK n J f c) ≤
      rawPair hw0 hw1 K width hK n L f + -(rawPair hw0 hw1 K width hK n J f) + error ∧
    rawPair hw0 hw1 K width hK n L f + -(rawPair hw0 hw1 K width hK n J f) ≤
      centeredPair hw0 hw1 K width hK n L f c +
        -(centeredPair hw0 hw1 K width hK n J f c) + error := by
  dsimp only
  let c := middleRatio hw0 hw1 K width hK (n+1) n f
  let q := mixRate hw0 hw1 width
  let d := q^n*(C+C)
  have hc := middleRatio_interval_bounds hw0 hw1 K width hK (n+1) n I
  have hC := Q'.zero_le_add C C I.nonnegative I.nonnegative
  have hu : -(C+C) ≤ c+c ∧ c+c ≤ C+C :=
    ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.neg_add_eqv C C))
      (Q'.add_le_add hc.1 hc.1), Q'.add_le_add hc.2 hc.2⟩
  have hmeans := endpoint_mean_lags_commonTail hw0 hw1 K width hK n L J I
  have hv : -d ≤ windowRatio hw0 hw1 K width hK n L n f +
        -(windowRatio hw0 hw1 K width hK n J n f) ∧
      windowRatio hw0 hw1 K width hK n L n f +
        -(windowRatio hw0 hw1 K width hK n J n f) ≤ d :=
    ⟨Q'.neg_le_sub_of_le_add hmeans.2, Q'.sub_le_of_le_add hmeans.1⟩
  have hd : (0 : Q') ≤ d := Q'.mul_nonneg _ _
    (Q'.pow_nonneg q (mixRate_nonnegative hw0 hw1 width) n) hC
  have h := signed_perturbation_bounds
    (centered_lag_difference_pin hw0 hw1 K width hK n L J I.support c) hC hd hu hv
  have herror : (C+C)*d ≈ q^n*((C+C)*(C+C)) :=
    poly_identity_of_normal_eq (.mul (.var 0) (.mul (.var 1) (.var 0)))
      (.mul (.var 1) (.mul (.var 0) (.var 0))) (by decide)
      (fun | 0 => C+C | _ => q^n)
  exact ⟨Q'.le_trans' _ _ _ h.1
      (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) herror)),
    Q'.le_trans' _ _ _ h.2
      (Q'.le_of_eqv (Q'.add_eqv_congr' (Q'.eqv_refl _) herror))⟩

/-- Every supported original polynomial receives a computed cap and error;
there is no interval or mean estimate left to supply. -/
theorem polynomial_own_centered_lag_difference_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n L J : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) :
    let c := middleRatio hw0 hw1 K width hK (n+1) n f
    let C := polynomialCap f
    let error := mixRate hw0 hw1 width ^ n * ((C+C)*(C+C))
    centeredPair hw0 hw1 K width hK n L f c +
        -(centeredPair hw0 hw1 K width hK n J f c) ≤
      rawPair hw0 hw1 K width hK n L f + -(rawPair hw0 hw1 K width hK n J f) + error ∧
    rawPair hw0 hw1 K width hK n L f + -(rawPair hw0 hw1 K width hK n J f) ≤
      centeredPair hw0 hw1 K width hK n L f c +
        -(centeredPair hw0 hw1 K width hK n J f c) + error :=
  own_centered_lag_difference_bounds hw0 hw1 K width hK n L J
    (polynomialInterval (N width) f hf)

end YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference.centered_pair_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference.centered_lag_difference_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference.own_centered_lag_difference_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMovingCenterLagDifference.polynomial_own_centered_lag_difference_bounds
