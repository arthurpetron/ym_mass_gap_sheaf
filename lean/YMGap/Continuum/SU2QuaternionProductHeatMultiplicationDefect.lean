/-
# The actual signed source/observable heat multiplication defect

C=P(q*f)-a*(Pq)*f is a computed polynomial on the original carrier.
Centering the SAME source moment removes its exact first-moment term.
No source independence, source eigenpin or sign of the defect is assumed.
-/

import YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
import YMGap.Continuum.SU2QuaternionProductHeatConstant
import YMGap.Continuum.QuaternionHaarDensityVariance

namespace YMGap.Continuum.SU2QuaternionProductHeatMultiplicationDefect

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularSupport (polySmul_supported)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment sourceEnergy)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap cap_mul_left)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- Actual polynomial difference, with no positivity assertion. -/
def multiplicationDefect (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (q f : RatPoly) (a : Q') : RatPoly :=
  polyAdd (productMap n w K ids (polyMul q f))
    (polySmul (-a) (polyMul (productMap n w K ids q) f))

theorem multiplicationDefect_supported (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (q f : RatPoly) (a : Q')
    (hq : SupportedQuaternionBlocks n q) (hf : SupportedQuaternionBlocks n f) :
    SupportedQuaternionBlocks n (multiplicationDefect n w K ids q f a) :=
  supported_add (productMap_supported n w K ids hids (supported_polyMul hq hf))
    (polySmul_supported
      (supported_polyMul (productMap_supported n w K ids hids hq) hf) (-a))

private theorem shifted_restore (f : RatPoly) (mu : Q') :
    RatPolyCoeffEqv f (polyAdd (shifted f mu) (cap mu)) := by
  have hn : RatPolyCoeffEqv (polyNeg (cap mu)) (polySmul (-mu) polyOne) :=
    (QuaternionHaarAngularCarrier.neg_smul (cap mu)).trans
      ((RatPolyCoeffEqv.smul_assoc (-1) mu polyOne).trans
        (RatPolyCoeffEqv.smul_coefficient
          (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0))
            (.neg (.var 0)) (by decide) (fun _ => mu)) polyOne))
  have hs : RatPolyCoeffEqv (shifted f mu) (polyAdd f (polyNeg (cap mu))) :=
    (RatPolyCoeffEqv.one_smul f).add hn.symm
  exact ((hs.add (RatPolyCoeffEqv.refl (cap mu))).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => f | _ => cap mu))).symm

private theorem source_shift (q f : RatPoly) (mu : Q') :
    RatPolyCoeffEqv (polyMul q (shifted f mu))
      (polyAdd (polyMul q f) (polySmul (-mu) q)) :=
  (RatPolyCoeffEqv.mul_add_right q (polySmul 1 f) (polySmul (-mu) polyOne)).trans
    (((RatPolyCoeffEqv.polyMul_smul_right 1 q f).trans
      (RatPolyCoeffEqv.one_smul (polyMul q f))).add
      ((RatPolyCoeffEqv.polyMul_smul_right (-mu) q polyOne).trans
        ((RatPolyCoeffEqv.mul_one q).smul (-mu))))

/-- Exact signed identity before removing the SAME source's first moment.
It holds without even a bare-observable eigenpin. -/
theorem sourceEnergy_shifted_multiplicationDefect (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (q f : RatPoly) (a mu : Q') :
    let psi := shifted f mu
    sourceEnergy n w K ids q psi ≈
      (1-a)*sourceMoment n w K ids q (polyMul psi psi)+
      (1-a)*mu*sourceMoment n w K ids q psi-
      H n (polyMul (polyMul q psi) (multiplicationDefect n w K ids q f a)) := by
  dsimp only
  let psi := shifted f mu
  let pq := productMap n w K ids q
  let v := polyMul q psi
  let S := sourceMoment n w K ids q (polyMul psi psi)
  let J := sourceMoment n w K ids q psi
  let B := H n (polyMul v (productMap n w K ids (polyMul q f)))
  let F := H n (polyMul v (polyMul pq f))
  let C := H n (polyMul v (multiplicationDefect n w K ids q f a))
  have hmap : RatPolyCoeffEqv (productMap n w K ids v)
      (polyAdd (productMap n w K ids (polyMul q f)) (polySmul (-mu) pq)) :=
    (productMap_congr n w K ids (source_shift q f mu)).trans
      ((productMap_add n w K ids _ _).trans
        ((RatPolyCoeffEqv.refl _).add (productMap_smul n w K ids (-mu) q)))
  have hkin : H n (polyMul v (productMap n w K ids v)) ≈ B-mu*J :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (hmap.mul_left v))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right n v _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (quaternionHaar_polyMul_smul_right n (-mu) v pq))
          (poly_identity_of_normal_eq
            (.add (.var 0) (.mul (.neg (.var 1)) (.var 2)))
            (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
            (by decide) (fun | 0 => B | 1 => mu | _ => J))))
  have hF : F ≈ S+mu*J := by
    have hpoly : RatPolyCoeffEqv (polyMul v (polyMul pq f))
        (polyAdd (polyMul (polyMul q (polyMul psi psi)) pq)
          (polySmul mu (polyMul v pq))) :=
      (((RatPolyCoeffEqv.refl v).mul
        ((RatPolyCoeffEqv.refl pq).mul (shifted_restore f mu))).trans
        (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.add (.var 1) (.var 3))))
          (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
            (.mul (.var 3) (.mul (.mul (.var 0) (.var 1)) (.var 2))))
          (by decide) (fun | 0 => q | 1 => psi | 2 => pq | _ => cap mu))).trans
        ((RatPolyCoeffEqv.refl _).add (cap_mul_left mu (polyMul v pq)))
    exact Q'.eqv_trans _ _ _ (haar_of_coeff hpoly)
      (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (quaternionHaar_polySmul n mu _)))
  have hC : C ≈ B-a*(S+mu*J) :=
    Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right n v _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right n (-a) v (polyMul pq f))
          (Q'.mul_eqv_congr_left (-a) _ _ hF)))
        (poly_identity_of_normal_eq
          (.add (.var 0) (.mul (.neg (.var 1)) (.var 2)))
          (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
          (by decide) (fun | 0 => B | 1 => a | _ => S+mu*J)))
  apply Q'.eqv_symm
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hC))
    (Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.add (.add (.mul (.add (.const 1) (.neg (.var 0))) (.var 1))
        (.mul (.mul (.add (.const 1) (.neg (.var 0))) (.var 2)) (.var 3)))
        (.neg (.add (.var 4) (.neg (.mul (.var 0)
          (.add (.var 1) (.mul (.var 2) (.var 3))))))))
      (.add (.var 1) (.neg (.add (.var 4) (.neg (.mul (.var 2) (.var 3))))))
      (by decide) (fun | 0 => a | 1 => S | 2 => mu | 3 => J | _ => B))
      (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.neg_eqv_congr _ _ hkin.symm)))

/-- The exact source first moment, not a raw/Haar substitute, removes the
mean term. The signed multiplication-defect pairing remains literal. -/
theorem sourceEnergy_centered_multiplicationDefect (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (q f : RatPoly) (a mu : Q')
    (hzero : sourceMoment n w K ids q (shifted f mu) ≈ 0) :
    let psi := shifted f mu
    sourceEnergy n w K ids q psi ≈
      (1-a)*sourceMoment n w K ids q (polyMul psi psi)-
      H n (polyMul (polyMul q psi) (multiplicationDefect n w K ids q f a)) := by
  dsimp only
  exact Q'.eqv_trans _ _ _
    (sourceEnergy_shifted_multiplicationDefect n w K ids q f a mu)
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.mul_eqv_congr_left ((1-a)*mu) _ _ hzero)) (Q'.eqv_refl _))
      (poly_identity_of_normal_eq
        (.add (.add (.var 0) (.mul (.var 1) (.const 0))) (.neg (.var 2)))
        (.add (.var 0) (.neg (.var 2))) (by decide)
        (fun | 0 => (1-a)*sourceMoment n w K ids q (polyMul (shifted f mu) (shifted f mu))
             | 1 => (1-a)*mu
             | _ => H n (polyMul (polyMul q (shifted f mu))
                 (multiplicationDefect n w K ids q f a)))))

#print axioms multiplicationDefect
#print axioms multiplicationDefect_supported
#print axioms sourceEnergy_shifted_multiplicationDefect
#print axioms sourceEnergy_centered_multiplicationDefect

end YMGap.Continuum.SU2QuaternionProductHeatMultiplicationDefect
