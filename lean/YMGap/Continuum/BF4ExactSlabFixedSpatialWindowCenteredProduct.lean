/-
# Centering the original one-step window before taking limits

The finite marginal center changes with the cutoff and terminal depth.
This exact identity replaces the shifted insertion by a two-point value
minus the product of two endpoint values of FIXED polynomials. Thus the
existing fixed-source convergence theorems can be applied termwise.
The original action and partition remain unchanged throughout.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEndpointMean
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
import YMGap.Continuum.QuaternionHaarDensityVariance
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWindowCenteredProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowEndpointMean
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem shifted_pair {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (p q : RatPoly) (m : Q')
    (hp : windowRatio hw0 hw1 K width hK n 1 n p ≈ m)
    (hq : windowRatio hw0 hw1 K width hK n 1 n q ≈ m) :
    windowRatio hw0 hw1 K width hK n 1 n (polyMul (shifted p m) (shifted q m)) ≈
      windowRatio hw0 hw1 K width hK n 1 n (polyMul p q) +
        -(windowRatio hw0 hw1 K width hK n 1 n p *
          windowRatio hw0 hw1 K width hK n 1 n q) := by
  let F := windowRatio hw0 hw1 K width hK n 1 n
  have addL (a b c : RatPoly) : F (polyMul (polyAdd a b) c) ≈
      F (polyMul a c) + F (polyMul b c) := by
    rw [polyMul_add_left_exact]
    exact windowRatio_add hw0 hw1 K width hK n 1 n _ _
  have addR (a b c : RatPoly) : F (polyMul a (polyAdd b c)) ≈
      F (polyMul a b) + F (polyMul a c) :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK n 1 n
        (RatPolyCoeffEqv.mul_add_right a b c))
      (windowRatio_add hw0 hw1 K width hK n 1 n _ _)
  have scaleL (c : Q') (a b : RatPoly) : F (polyMul (polySmul c a) b) ≈
      c * F (polyMul a b) :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK n 1 n
        (RatPolyCoeffEqv.polyMul_smul_left c a b))
      (windowRatio_smul hw0 hw1 K width hK n 1 n c _)
  have scaleR (c : Q') (a b : RatPoly) : F (polyMul a (polySmul c b)) ≈
      c * F (polyMul a b) :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK n 1 n
        (RatPolyCoeffEqv.polyMul_smul_right c a b))
      (windowRatio_smul hw0 hw1 K width hK n 1 n c _)
  have right (a : RatPoly) : F (polyMul a (shifted q m)) ≈
      1 * F (polyMul a q) + (-m) * F (polyMul a polyOne) :=
    Q'.eqv_trans _ _ _ (addR a _ _)
      (Q'.add_eqv_congr' (scaleR 1 a q) (scaleR (-m) a polyOne))
  have hpo : F (polyMul p polyOne) ≈ m :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK n 1 n (RatPolyCoeffEqv.mul_one p)) hp
  have hoq : F (polyMul polyOne q) ≈ m :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK n 1 n (RatPolyCoeffEqv.one_mul q)) hq
  have hoo : F (polyMul polyOne polyOne) ≈ 1 :=
    Q'.eqv_trans _ _ _
      (windowRatio_congr hw0 hw1 K width hK n 1 n (RatPolyCoeffEqv.mul_one polyOne))
      (windowRatio_one hw0 hw1 K width hK n 1 n)
  have he : F (polyMul (shifted p m) (shifted q m)) ≈
      1 * (1 * F (polyMul p q) + (-m)*m) +
        (-m) * (1*m + (-m)*1) :=
    Q'.eqv_trans _ _ _ (addL _ _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (scaleL 1 p _) (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (right p)
            (Q'.add_eqv_congr' (Q'.eqv_refl _) (qmul (Q'.eqv_refl _) hpo)))))
        (Q'.eqv_trans _ _ _ (scaleL (-m) polyOne _) (Q'.mul_eqv_congr_left _ _ _
          (Q'.eqv_trans _ _ _ (right polyOne)
            (Q'.add_eqv_congr' (qmul (Q'.eqv_refl _) hoq)
              (qmul (Q'.eqv_refl _) hoo))))))
  have hr : 1 * (1 * F (polyMul p q) + (-m)*m) +
      (-m) * (1*m + (-m)*1) ≈ F (polyMul p q) + -(m*m) :=
    poly_identity_of_normal_eq
      (.add (.mul (.const 1) (.add (.mul (.const 1) (.var 0))
        (.mul (.neg (.var 1)) (.var 1))))
        (.mul (.neg (.var 1)) (.add (.mul (.const 1) (.var 1))
          (.mul (.neg (.var 1)) (.const 1)))))
      (.add (.var 0) (.neg (.mul (.var 1) (.var 1)))) (by decide)
      (fun | 0 => F (polyMul p q) | _ => m)
  exact Q'.eqv_trans _ _ _ he (Q'.eqv_trans _ _ _ hr
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ (Q'.eqv_symm (qmul hp hq)))))

/-- Exact connected-product identity with the ACTUAL finite endpoint mean.
Padded unit equality is used only on supported original-window insertions. -/
theorem centered_product_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    let m := middleRatio hw0 hw1 K width hK (n+1) n f
    windowRatio hw0 hw1 K width hK n 1 n
        (polyMul (shifted f m) (liftBoundary (N width) (shifted f m))) ≈
      windowRatio hw0 hw1 K width hK n 1 n (polyMul f (liftBoundary (N width) f)) +
        -(windowRatio hw0 hw1 K width hK n 1 n f *
          windowRatio hw0 hw1 K width hK n 1 n (liftBoundary (N width) f)) := by
  dsimp only
  let m := middleRatio hw0 hw1 K width hK (n+1) n f
  have hs := shifted_supported hf m
  have hsf : SupportedQuaternionBlocks ((1+1)*(N width)) (shifted f m) := by
    intro t ht
    exact Nat.le_trans (hs t ht) (by omega)
  have hlf : SupportedQuaternionBlocks ((1+1)*(N width)) (liftBoundary (N width) f) := by
    simpa only [show (1 : Nat)+1=2 by rfl, Nat.two_mul] using lift_supported hf (N width)
  have hls : SupportedQuaternionBlocks ((1+1)*(N width))
      (liftBoundary (N width) (shifted f m)) := by
    simpa only [show (1 : Nat)+1=2 by rfl, Nat.two_mul] using lift_supported hs (N width)
  have he : PaddedPolynomialCoeffEqv ((1+1)*(N width))
      (liftBoundary (N width) (shifted f m)) (shifted (liftBoundary (N width) f) m) := by
    unfold shifted
    rw [lift_add, lift_smul, lift_smul]
    exact ((PaddedPolynomialCoeffEqv.refl _ _).smul 1).add
      ((lift_one ((1+1)*(N width)) (N width)).smul (-m))
  exact Q'.eqv_trans _ _ _
    (windowRatio_padded_congr hw0 hw1 K width hK n 1 n
      (supported_polyMul hsf hls) (supported_polyMul hsf (shifted_supported hlf m))
      ((PaddedPolynomialCoeffEqv.refl _ _).mul he))
    (shifted_pair hw0 hw1 K width hK n f (liftBoundary (N width) f) m
      (Q'.eqv_trans _ _ _ (endpoint_means_eqv hw0 hw1 K width hK n hf)
        (upper_endpoint_mean hw0 hw1 K width hK n hf))
      (upper_endpoint_mean hw0 hw1 K width hK n hf))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWindowCenteredProduct

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWindowCenteredProduct.centered_product_pin
