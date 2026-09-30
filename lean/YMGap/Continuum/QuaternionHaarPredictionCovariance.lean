/-
# Covariance deficit from original weighted-Haar prediction errors

The weight, positive mass, and both observables are the same finite
quaternion-Haar data throughout. A lower squared prediction error against
every rational affine function of the second observable bounds the centered
covariance. No independence or continuum premise is inserted.
-/

import YMGap.Continuum.QuaternionHaarCenteredResponse
import YMGap.Continuum.RationalPredictionCovariance

namespace YMGap.Continuum.QuaternionHaarPredictionCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.QuaternionHaarNormalizedMomentLinear
open YMGap.Continuum.QuaternionHaarCenteredResponse

local infix:50 " ≈ " => Q'.eqv

private theorem ratWeightedSum_polyNeg (weight : List Nat → Q') :
    ∀ p : RatPoly, ratWeightedSum weight (polyNeg p) ≈ -(ratWeightedSum weight p)
  | [] => by change (0 : Q') ≈ -0; decide
  | term :: rest => by
      change (-term.2)*weight term.1 + ratWeightedSum weight (polyNeg rest) ≈
        -(term.2*weight term.1 + ratWeightedSum weight rest)
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.neg_mul_eqv _ _) (ratWeightedSum_polyNeg weight rest))
        (Q'.eqv_symm (Q'.neg_add_eqv _ _))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem normalized_pair {blocks : Nat} {W : RatPoly}
    (hZ : (0 : Q') < quaternionHaar blocks W) (p q : RatPoly) :
    weightedPair blocks W p q * Q'.recipPos (quaternionHaar blocks W) hZ ≈
      normalizedMoment blocks W (polyMul p q) hZ :=
  Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))

/-- Centered covariance for the SAME original certified Haar weight. -/
def normalizedCovariance (blocks : Nat) (W p q : RatPoly)
    (hZ : (0 : Q') < quaternionHaar blocks W) : Q' :=
  normalizedMoment blocks W (polyMul p q) hZ +
    -(normalizedMoment blocks W p hZ * normalizedMoment blocks W q hZ)

/-- Positivity of the existing normalized variance follows from the square
certificate and the explicitly centered polynomial. -/
theorem normalizedVariance_nonnegative {blocks : Nat} {W p : RatPoly}
    (H : Certificate blocks W)
    (hZ : (0 : Q') < quaternionHaar blocks W)
    (hp : SupportedQuaternionBlocks blocks p) :
    (0 : Q') ≤ normalizedVariance blocks W p hZ := by
  let x := shifted p (normalizedMoment blocks W p hZ)
  have hx : SupportedQuaternionBlocks blocks x := shifted_supported hp _
  have hn : (0 : Q') ≤ normalizedMoment blocks W (polyMul x x) hZ := by
    unfold normalizedMoment
    have hraw : (0 : Q') ≤ quaternionHaar blocks (polyMul W (polyMul x x)) :=
      Q'.le_trans' _ _ _ (H.square_insertion_nonnegative x hx)
        (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _)))
    exact Q'.mul_nonneg _ _ hraw (Q'.le_of_lt (Q'.recipPos_pos _ hZ))
  exact Q'.le_trans' _ _ _ hn (Q'.le_of_eqv (own_mean_pin H hp hZ))

private theorem centered_mean_zero {blocks : Nat} {W q : RatPoly}
    (hZ : (0 : Q') < quaternionHaar blocks W) :
    normalizedMoment blocks W
      (shifted q (normalizedMoment blocks W q hZ)) hZ ≈ 0 := by
  let m := normalizedMoment blocks W q hZ
  have h := normalizedMoment_add hZ (p := polySmul 1 q)
    (q := polySmul (-m) polyOne)
  change normalizedMoment blocks W (shifted q m) hZ ≈ _ + _ at h
  exact Q'.eqv_trans _ _ _ h
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (normalizedMoment_smul hZ) (Q'.one_mul_eqv _))
        (Q'.eqv_trans _ _ _ (normalizedMoment_smul hZ)
          (Q'.mul_eqv_congr_left _ _ _ (normalizedMoment_one hZ))))
      (poly_identity_of_normal_eq
        (.add (.var 0) (.mul (.neg (.var 0)) (.const 1))) (.const 0)
        (by decide) (fun _ => m)))

private theorem centered_cross_pin {blocks : Nat} {W p q : RatPoly}
    (hZ : (0 : Q') < quaternionHaar blocks W) :
    normalizedMoment blocks W
      (polyMul (shifted p (normalizedMoment blocks W p hZ))
        (shifted q (normalizedMoment blocks W q hZ))) hZ ≈
      normalizedCovariance blocks W p q hZ := by
  let mp := normalizedMoment blocks W p hZ
  let mq := normalizedMoment blocks W q hZ
  have hzero := centered_mean_zero (W := W) hZ (q := q)
  have hp := centered_pair_pin (p := p) (q := shifted q mq) hZ hzero mp
  have hcoeff : RatPolyCoeffEqv (polyMul p (shifted q mq))
      (polyAdd (polySmul 1 (polyMul p q)) (polySmul (-mq) p)) := by
    unfold shifted
    exact (RatPolyCoeffEqv.mul_add_right p _ _).trans
      ((RatPolyCoeffEqv.polyMul_smul_right 1 p q).add
        ((RatPolyCoeffEqv.polyMul_smul_right (-mq) p polyOne).trans
          ((RatPolyCoeffEqv.mul_one p).smul (-mq))))
  have hc := normalizedMoment_congr hZ hZ (RatPolyCoeffEqv.refl W) hcoeff
  have hl := normalizedMoment_add hZ
    (p := polySmul 1 (polyMul p q)) (q := polySmul (-mq) p)
  have hr : normalizedMoment blocks W (polyMul p (shifted q mq)) hZ ≈
      normalizedMoment blocks W (polyMul p q) hZ + -(mp*mq) :=
    Q'.eqv_trans _ _ _ hc (Q'.eqv_trans _ _ _ hl
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _ (normalizedMoment_smul hZ) (Q'.one_mul_eqv _))
          (normalizedMoment_smul hZ))
        (poly_identity_of_normal_eq
          (.add (.var 0) (.mul (.neg (.var 2)) (.var 1)))
          (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
          (by decide)
          (fun | 0 => normalizedMoment blocks W (polyMul p q) hZ | 1 => mp | _ => mq))))
  exact Q'.eqv_trans _ _ _ hp hr

private theorem prediction_error_shift {p q : RatPoly} (a t : Q') :
    RatPolyCoeffEqv
      (polyAdd p (polyNeg (polyAdd (polySmul a polyOne) (polySmul t q))))
      (shifted (polyAdd p (polySmul (-t) q)) a) := by
  intro weight
  let P := ratWeightedSum weight p
  let Q := ratWeightedSum weight q
  let O := ratWeightedSum weight polyOne
  have hl : ratWeightedSum weight
      (polyAdd p (polyNeg (polyAdd (polySmul a polyOne) (polySmul t q)))) ≈
      P + -((a*O) + (t*Q)) :=
    Q'.eqv_trans _ _ _ (ratWeightedSum_add weight _ _)
      (Q'.add_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (ratWeightedSum_polyNeg weight _)
          (Q'.neg_eqv_congr _ _
            (Q'.eqv_trans _ _ _ (ratWeightedSum_add weight _ _)
              (Q'.add_eqv_congr'
                (ratWeightedSum_smul weight a polyOne)
                (ratWeightedSum_smul weight t q))))))
  have hr : ratWeightedSum weight (shifted (polyAdd p (polySmul (-t) q)) a) ≈
      1*(P + (-t)*Q) + (-a)*O := by
    unfold shifted
    exact Q'.eqv_trans _ _ _ (ratWeightedSum_add weight _ _)
      (Q'.add_eqv_congr'
        (Q'.eqv_trans _ _ _ (ratWeightedSum_smul weight 1 _)
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_trans _ _ _ (ratWeightedSum_add weight _ _)
              (Q'.add_eqv_congr_left _ _ _ (ratWeightedSum_smul weight (-t) q)))))
        (ratWeightedSum_smul weight (-a) polyOne))
  exact Q'.eqv_trans _ _ _ hl
    (Q'.eqv_trans _ _ _
      (poly_identity_of_normal_eq
        (.add (.var 0) (.neg (.add (.mul (.var 2) (.var 4))
          (.mul (.var 3) (.var 1)))))
        (.add (.mul (.const 1) (.add (.var 0) (.mul (.neg (.var 3)) (.var 1))))
          (.mul (.neg (.var 2)) (.var 4)))
        (by decide) (fun | 0 => P | 1 => Q | 2 => a | 3 => t | _ => O))
      (Q'.eqv_symm hr))

private theorem affine_variance_pin {blocks : Nat} {W p q : RatPoly}
    (H : Certificate blocks W) (hZ : (0 : Q') < quaternionHaar blocks W)
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q) (t : Q') :
    normalizedVariance blocks W (polyAdd p (polySmul (-t) q)) hZ ≈
      normalizedVariance blocks W p hZ +
        -(2*t*normalizedCovariance blocks W p q hZ) +
        t*t*normalizedVariance blocks W q hZ := by
  let r := Q'.recipPos (quaternionHaar blocks W) hZ
  let G := weightedGNSData blocks W H
  let pt := polyAdd p (polySmul (-t) q)
  let P := weightedPair blocks W p p
  let M := weightedPair blocks W p q
  let Q := weightedPair blocks W q q
  have hpt : SupportedQuaternionBlocks blocks pt :=
    supported_add hp (by
      intro s hs
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
      exact hq u hu)
  have hcoeff : G.veq
      (G.add (G.smul 1 ⟨p, hp⟩) (G.smul (-t) ⟨q, hq⟩))
      ⟨pt, hpt⟩ := (RatPolyCoeffEqv.one_smul p).add (RatPolyCoeffEqv.refl _)
  have hdiag := G.diag_expand 1 (-t) ⟨p, hp⟩ ⟨q, hq⟩
  have hraw : weightedPair blocks W pt pt ≈
      ((1*(1*P) + 1*((-t)*M)) +
        ((-t)*(1*M) + (-t)*((-t)*Q))) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (G.B_diag_congr hcoeff)) hdiag
  have hsecond : normalizedMoment blocks W (polyMul pt pt) hZ ≈
      normalizedMoment blocks W (polyMul p p) hZ +
        -(2*t*normalizedMoment blocks W (polyMul p q) hZ) +
        t*t*normalizedMoment blocks W (polyMul q q) hZ := by
    have hpoly :
        (((1*(1*P) + 1*((-t)*M)) +
          ((-t)*(1*M) + (-t)*((-t)*Q)))*r) ≈
        (P*r + -(2*t*(M*r))) + t*t*(Q*r) :=
      poly_identity_of_normal_eq
        (.mul
          (.add
            (.add (.mul (.const 1) (.mul (.const 1) (.var 0)))
              (.mul (.const 1) (.mul (.neg (.var 4)) (.var 1))))
            (.add (.mul (.neg (.var 4)) (.mul (.const 1) (.var 1)))
              (.mul (.neg (.var 4)) (.mul (.neg (.var 4)) (.var 2)))))
          (.var 3))
        (.add (.add (.mul (.var 0) (.var 3))
          (.neg (.mul (.mul (.const 2) (.var 4)) (.mul (.var 1) (.var 3)))))
          (.mul (.mul (.var 4) (.var 4)) (.mul (.var 2) (.var 3))))
        (by decide) (fun | 0 => P | 1 => M | 2 => Q | 3 => r | _ => t)
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (normalized_pair hZ pt pt))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ r hraw)
        (Q'.eqv_trans _ _ _ hpoly
          (Q'.add_eqv_congr'
            (Q'.add_eqv_congr' (normalized_pair hZ p p)
              (Q'.neg_eqv_congr _ _
                (Q'.mul_eqv_congr_left (2*t) _ _ (normalized_pair hZ p q))))
            (Q'.mul_eqv_congr_left (t*t) _ _ (normalized_pair hZ q q)))))
  have hmean : normalizedMoment blocks W pt hZ ≈
      normalizedMoment blocks W p hZ +
        -(t*normalizedMoment blocks W q hZ) := by
    exact Q'.eqv_trans _ _ _ (normalizedMoment_add hZ)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (normalizedMoment_smul hZ))
        (poly_identity_of_normal_eq
          (.add (.var 0) (.mul (.neg (.var 2)) (.var 1)))
          (.add (.var 0) (.neg (.mul (.var 2) (.var 1))))
          (by decide)
          (fun | 0 => normalizedMoment blocks W p hZ | 1 => normalizedMoment blocks W q hZ | _ => t)))
  unfold normalizedVariance normalizedCovariance
  have hstart := Q'.add_eqv_congr' hsecond
    (Q'.neg_eqv_congr _ _ (qmul hmean hmean))
  exact Q'.eqv_trans _ _ _ hstart
    (poly_identity_of_normal_eq
      (.add
        (.add (.add (.var 0) (.neg (.mul (.mul (.const 2) (.var 5)) (.var 1))))
          (.mul (.mul (.var 5) (.var 5)) (.var 2)))
        (.neg (.mul
          (.add (.var 3) (.neg (.mul (.var 5) (.var 4))))
          (.add (.var 3) (.neg (.mul (.var 5) (.var 4)))))))
      (.add
        (.add (.add (.var 0) (.neg (.mul (.var 3) (.var 3))))
          (.neg (.mul (.mul (.const 2) (.var 5))
            (.add (.var 1) (.neg (.mul (.var 3) (.var 4)))))))
        (.mul (.mul (.var 5) (.var 5))
          (.add (.var 2) (.neg (.mul (.var 4) (.var 4))))))
      (by decide)
      (fun | 0 => normalizedMoment blocks W (polyMul p p) hZ
           | 1 => normalizedMoment blocks W (polyMul p q) hZ
           | 2 => normalizedMoment blocks W (polyMul q q) hZ
           | 3 => normalizedMoment blocks W p hZ
           | 4 => normalizedMoment blocks W q hZ
           | _ => t))

/-- A prediction floor against every rational affine function of `q`
subtracts directly from the original normalized variance budget. The
certificate is for the SAME weight as all displayed moments. -/
theorem covariance_sq_le_variance_deficit {blocks : Nat} {W p q : RatPoly}
    (H : Certificate blocks W)
    (hZ : (0 : Q') < quaternionHaar blocks W)
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (delta : Q')
    (hprediction : ∀ a t : Q',
      delta ≤ normalizedMoment blocks W
        (polyMul
          (polyAdd p (polyNeg
            (polyAdd (polySmul a polyOne) (polySmul t q))))
          (polyAdd p (polyNeg
            (polyAdd (polySmul a polyOne) (polySmul t q))))) hZ) :
    normalizedCovariance blocks W p q hZ *
        normalizedCovariance blocks W p q hZ ≤
      (normalizedVariance blocks W p hZ + -delta) *
        normalizedVariance blocks W q hZ := by
  let mp := normalizedMoment blocks W p hZ
  let mq := normalizedMoment blocks W q hZ
  let xp := shifted p mp
  let yq := shifted q mq
  have hcs := normalized_cauchySchwarz H hZ
    (shifted_supported hp mp) (shifted_supported hq mq)
  have hcross := centered_cross_pin (W := W) (p := p) (q := q) hZ
  have hpp := own_mean_pin H hp hZ
  have hqq := own_mean_pin H hq hZ
  have hcovCS :
      normalizedCovariance blocks W p q hZ *
          normalizedCovariance blocks W p q hZ ≤
        normalizedVariance blocks W p hZ * normalizedVariance blocks W q hZ :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (qmul hcross hcross))
      (Q'.le_trans' _ _ _ hcs (Q'.le_of_eqv (qmul hpp hqq)))
  have hfloor (t : Q') :
      delta ≤ normalizedVariance blocks W p hZ +
        -(2*t*normalizedCovariance blocks W p q hZ) +
        t*t*normalizedVariance blocks W q hZ := by
    let pt := polyAdd p (polySmul (-t) q)
    let a := normalizedMoment blocks W pt hZ
    let e := polyAdd p (polyNeg
      (polyAdd (polySmul a polyOne) (polySmul t q)))
    have hpt : SupportedQuaternionBlocks blocks pt :=
      supported_add hp (by
        intro s hs
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
        exact hq u hu)
    have he := prediction_error_shift (p := p) (q := q) a t
    have he2 : RatPolyCoeffEqv (polyMul e e)
        (polyMul (shifted pt a) (shifted pt a)) :=
      (he.mul_right e).trans (he.mul_left (shifted pt a))
    have hmoment := normalizedMoment_congr hZ hZ
      (RatPolyCoeffEqv.refl W) he2
    have hown := own_mean_pin H hpt hZ
    exact Q'.le_trans' _ _ _ (hprediction a t)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hmoment)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hown)
          (Q'.le_of_eqv (affine_variance_pin H hZ hp hq t))))
  exact RationalPredictionCovariance.covariance_budget
    (normalizedVariance blocks W p hZ)
    (normalizedCovariance blocks W p q hZ)
    (normalizedVariance blocks W q hZ) delta
    (normalizedVariance_nonnegative H hZ hq) hcovCS hfloor

#print axioms normalizedCovariance
#print axioms normalizedVariance_nonnegative
#print axioms covariance_sq_le_variance_deficit

end YMGap.Continuum.QuaternionHaarPredictionCovariance
