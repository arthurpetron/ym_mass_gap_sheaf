/-
# Finite-time endpoint-weighted head heat with a quadratic remainder

The actual head heat, with all spectator variables shared, has an exact
first-order expansion and a computed signed remainder. The existing cutoff
guard controls even omitted harmonic degrees; the source degree need not be
below the heat cutoff. After retaining the endpoint correction, angular Haar
integration by parts cancels all source derivatives at first order.

The resulting upper bound is
  E(a,f) <= (1-w) H[a^2 Gamma(f)] + (1-w)^2 budget(a,a*f^2).
The budget is a finite Casimir-squared sum of absolute MIXED group pairings,
not a uniform constant. Sources may depend on cutoff, coupling and volume.
This local shared-spectator estimate is not yet the full product-transfer
estimate, a useful normalized survival bound, or a continuum statement.
-/

import YMGap.Continuum.SU2HeatCutoffTaylorRemainder
import YMGap.Continuum.SU2QuaternionHeadAngularPair
import YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
import YMGap.Continuum.QuaternionHaarWeightedAngularCancellation
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.SU2QuaternionHeadHeatWeightedTaylor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHarmonicExpansion
open YMGap.Continuum.SU2QuaternionHeadHomogeneousComponents
open YMGap.Continuum.SU2QuaternionGroupedHarmonicNorm
open YMGap.Continuum.SU2QuaternionHeadHeatDiagonal
open YMGap.Continuum.SU2QuaternionHeadAngularPair
open YMGap.Continuum.SU2HeatCutoffCasimirBound
open YMGap.Continuum.SU2HeatCutoffTaylorRemainder
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarWeightedAngularCancellation
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Signed spectral remainder of the ACTUAL finite head heat pairing. -/
def pairRemainder (tail : Nat) (w : Q') (K : Nat) (p q : RatPoly) : Q' :=
  let ms := modes (tail+1) (by omega) p
  qListSum ((headDegrees (sumHarmonics ms)).map fun d =>
    cutoffRemainder w K d * H (tail+1) (polyMul (grouped d ms) q))

/-- Computed mixed Casimir-squared budget; no source-independent bound is
asserted. Equal-degree signed contributions are grouped BEFORE absolute values. -/
def pairBudget (tail : Nat) (p q : RatPoly) : Q' :=
  let ms := modes (tail+1) (by omega) p
  qListSum ((headDegrees (sumHarmonics ms)).map fun d =>
    Q'.ofNat ((d*(d+2))*(d*(d+2))) *
      Q'.abs (H (tail+1) (polyMul (grouped d ms) q)))

private theorem sum_taylor (w : Q') (K : Nat) (b : Nat → Q') : ∀ ids : List Nat,
    qListSum (ids.map fun d => attenuation w K d * b d) ≈
      qListSum (ids.map b) - ((1 : Q')-w) *
        qListSum (ids.map fun d => Q'.ofNat (d*(d+2))*b d) +
      qListSum (ids.map fun d => cutoffRemainder w K d*b d)
  | [] => by
      change (0 : Q') ≈ 0 - ((1 : Q')-w)*0+0
      exact poly_identity_of_normal_eq (.const 0)
        (.add (.add (.const 0) (.neg (.mul (.var 0) (.const 0)))) (.const 0))
        (by decide) (fun _ => (1 : Q')-w)
  | d::ds => by
      have hd : attenuation w K d*b d ≈
          b d - ((1 : Q')-w)*(Q'.ofNat (d*(d+2))*b d) +
            cutoffRemainder w K d*b d := by
        unfold cutoffRemainder
        exact poly_identity_of_normal_eq (.mul (.var 0) (.var 1))
          (.add (.add (.var 1) (.neg (.mul (.var 2) (.mul (.var 3) (.var 1)))))
            (.mul (.add (.add (.var 0) (.neg (.const 1)))
              (.mul (.var 2) (.var 3))) (.var 1)))
          (by decide) (fun
            | 0 => attenuation w K d | 1 => b d
            | 2 => (1 : Q')-w | _ => Q'.ofNat (d*(d+2)))
      exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hd (sum_taylor w K b ds))
        (poly_identity_of_normal_eq
          (.add (.add (.add (.var 0) (.neg (.mul (.var 2) (.var 3)))) (.var 5))
            (.add (.add (.var 1) (.neg (.mul (.var 2) (.var 4)))) (.var 6)))
          (.add (.add (.add (.var 0) (.var 1))
            (.neg (.mul (.var 2) (.add (.var 3) (.var 4)))))
            (.add (.var 5) (.var 6)))
          (by decide) (fun
            | 0 => b d | 1 => qListSum (ds.map b) | 2 => (1 : Q')-w
            | 3 => Q'.ofNat (d*(d+2))*b d
            | 4 => qListSum (ds.map fun k => Q'.ofNat (k*(k+2))*b k)
            | 5 => cutoffRemainder w K d*b d
            | _ => qListSum (ds.map fun k => cutoffRemainder w K k*b k)))

/-- Exact finite-time expansion on the original head heat, before any absolute
values are taken. It is an identity at EVERY cutoff and rational nome. -/
theorem heatPair_taylor (tail : Nat) (w : Q') (K : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks (tail+1) p) :
    heatPair tail w K p q ≈
      H (tail+1) (polyMul p q) + ((1 : Q')-w) *
        H (tail+1) (polyMul (angularLaplacian p) q) +
      pairRemainder tail w K p q := by
  let ms := modes (tail+1) (by omega) p
  let b := fun d => H (tail+1) (polyMul (grouped d ms) q)
  have h0 := polynomial_pair_decomposition tail p q hp
  have h1 := polynomial_generator_pair tail p q hp
  exact Q'.eqv_trans _ _ _ (polynomial_pair tail w K p q hp)
    (Q'.eqv_trans _ _ _ (sum_taylor w K b (headDegrees (sumHarmonics ms)))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.add_eqv_congr' (Q'.eqv_symm h0)
            (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left _ _ _ h1)))
          (Q'.eqv_refl _))
        (poly_identity_of_normal_eq
          (.add (.add (.var 0) (.neg (.mul (.var 1) (.neg (.var 2))))) (.var 3))
          (.add (.add (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
          (by decide) (fun
            | 0 => H (tail+1) (polyMul p q) | 1 => (1 : Q')-w
            | 2 => H (tail+1) (polyMul (angularLaplacian p) q)
            | _ => pairRemainder tail w K p q))))

private theorem sum_remainder_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : sufficientCutoff w ≤ K)
    (b : Nat → Q') : ∀ ids : List Nat,
    qListSum (ids.map fun d => cutoffRemainder w K d*b d) ≤
      (((1 : Q')-w)*((1 : Q')-w)) * qListSum (ids.map fun d =>
        Q'.ofNat ((d*(d+2))*(d*(d+2))) * Q'.abs (b d))
  | [] => Q'.ge_of_eqv (Q'.mul_zero_eqv _)
  | d::ds => by
      have hr := cutoffRemainder_bounds_of_sufficientCutoff hw0 hw1 hK d
      have hm := Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_abs_self (b d)) hr.1)
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hr.2 (Q'.abs_nonneg (b d)))
      have hm' := Q'.le_trans' _ _ _ hm (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add hm' (sum_remainder_le hw0 hw1 K hK b ds))
        (Q'.ge_of_eqv (Q'.mul_add_eqv _ _ _))

/-- The source-dependent error is genuinely quadratic, including omitted modes.
No hypothesis restricts the degree of p to lie below K. -/
theorem pairRemainder_le (tail : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w < (1 : Q')) (K : Nat) (hK : sufficientCutoff w ≤ K)
    (p q : RatPoly) :
    pairRemainder tail w K p q ≤
      (((1 : Q')-w)*((1 : Q')-w))*pairBudget tail p q :=
  sum_remainder_le hw0 hw1 K hK _ _

/-- Original endpoint-weighted local temporal energy, not a bare heat defect. -/
def weightedEnergy (tail : Nat) (w : Q') (K : Nat) (a f : RatPoly) : Q' :=
  heatPair tail w K a (polyMul a (polyMul f f)) -
    heatPair tail w K (polyMul a f) (polyMul a f)

/-- Source derivatives cancel at first order in the actual finite heat energy.
The diagonal defect is bounded as a whole; only the mixed SOURCE remainder
needs an explicit upper-error budget. -/
theorem weightedEnergy_le_angular_add_quadratic (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    weightedEnergy tail w K a f ≤
      ((1 : Q')-w)*H (tail+1) (polyMul (polyMul a a) (angularSquare f)) +
        (((1 : Q')-w)*((1 : Q')-w))*pairBudget tail a (polyMul a (polyMul f f)) := by
  let q := polyMul a (polyMul f f)
  let u := polyMul a f
  let eps := (1 : Q')-w
  let A := H (tail+1) (polyMul a q)
  let L := H (tail+1) (polyMul (angularLaplacian a) q)
  let G := H (tail+1) (angularSquare u)
  let F := H (tail+1) (polyMul (polyMul a a) (angularSquare f))
  let R := pairRemainder tail w K a q
  have ht : heatPair tail w K a q ≈ A + eps*L + R :=
    heatPair_taylor tail w K a q ha
  have hs : H (tail+1) (polyMul u u) ≈ A := haar_of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
      (.mul (.var 0) (.mul (.var 0) (.mul (.var 1) (.var 1))))
      (by decide) (fun | 0 => a | _ => f))
  have hd := polynomial_defect_le_angular tail hw0 hw1 K hK u (supported_polyMul ha hf)
  have hcancel : G+L ≈ F := Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (haar_of_coeff (RatPolyCoeffEqv.mul_comm (angularLaplacian a) q)))
    (weighted_angular_cancellation tail a f)
  have he : weightedEnergy tail w K a f ≈
      (H (tail+1) (polyMul u u) - heatPair tail w K u u) + (eps*L+R) := by
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' ht (Q'.eqv_refl _))
      (Q'.eqv_trans _ _ _
        (poly_identity_of_normal_eq
          (.add (.add (.add (.var 0) (.mul (.var 1) (.var 2))) (.var 3)) (.neg (.var 4)))
          (.add (.add (.var 0) (.neg (.var 4))) (.add (.mul (.var 1) (.var 2)) (.var 3)))
          (by decide) (fun
            | 0 => A | 1 => eps | 2 => L | 3 => R
            | _ => heatPair tail w K u u))
        (Q'.add_eqv_congr' (Q'.add_eqv_congr' (Q'.eqv_symm hs) (Q'.eqv_refl _))
          (Q'.eqv_refl _)))
  have hfirst : weightedEnergy tail w K a f ≤ eps*F+R :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hd)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _
          (poly_identity_of_normal_eq
            (.add (.mul (.var 0) (.var 1)) (.add (.mul (.var 0) (.var 2)) (.var 3)))
            (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.var 3))
            (by decide) (fun | 0 => eps | 1 => G | 2 => L | _ => R))
          (Q'.add_eqv_congr' (Q'.mul_eqv_congr_left _ _ _ hcancel) (Q'.eqv_refl _)))))
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.add_le_add_left _ _ _ (pairRemainder_le tail hw0 hw1 K hK a q))

end YMGap.Continuum.SU2QuaternionHeadHeatWeightedTaylor

#print axioms YMGap.Continuum.SU2QuaternionHeadHeatWeightedTaylor.pairRemainder
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatWeightedTaylor.pairBudget
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatWeightedTaylor.weightedEnergy
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatWeightedTaylor.heatPair_taylor
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatWeightedTaylor.pairRemainder_le
#print axioms YMGap.Continuum.SU2QuaternionHeadHeatWeightedTaylor.weightedEnergy_le_angular_add_quadratic
