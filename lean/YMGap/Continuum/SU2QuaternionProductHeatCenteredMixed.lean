/-
# Exact centered mixed source moment under a finite heat eigenimage

The actual source remains arbitrary and supported. The observable eigenimage
is a tested-Haar input, which the literal plaquette heat theorem supplies.
The source correction remains signed and explicit.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSourceCentering
import YMGap.Continuum.SU2QuaternionProductHeatConstant

namespace YMGap.Continuum.SU2QuaternionProductHeatCenteredMixed

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
  (sourceMoment sourceCorrection)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff supported_one)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

private theorem shifted_haar (n : Nat) (T f : RatPoly) (c : Q') :
    H n (polyMul T (shifted f c)) ≈
      H n (polyMul T f) + -(c*H n T) := by
  unfold shifted
  have ha := quaternionHaar_polyMul_add_right n T (polySmul 1 f)
    (polySmul (-c) polyOne)
  have hb := quaternionHaar_polyMul_smul_right n 1 T f
  have hc := quaternionHaar_polyMul_smul_right n (-c) T polyOne
  have hd : H n (polyMul T polyOne) ≈ H n T :=
    haar_of_coeff (RatPolyCoeffEqv.mul_one T)
  exact Q'.eqv_trans _ _ _ ha
    (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hb
      (Q'.eqv_trans _ _ _ hc (Q'.mul_eqv_congr_left (-c) _ _ hd)))
      (poly_identity_of_normal_eq
        (.add (.mul (.const 1) (.var 0)) (.mul (.neg (.var 1)) (.var 2)))
        (.add (.var 0) (.neg (.mul (.var 1) (.var 2))))
        (by decide) (fun | 0 => H n (polyMul T f) | 1 => c | _ => H n T)))

private theorem correction_expansion (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (q psi : RatPoly) :
    sourceCorrection n w K ids q psi ≈
      sourceMoment n w K ids q (polyMul psi psi) +
        -(H n (polyMul (polyMul q q) (polyMul psi psi))) := by
  let Pq := productMap n w K ids q
  have hc : RatPolyCoeffEqv
      (polyMul (polyMul q (polyMul psi psi)) (polyAdd Pq (polyNeg q)))
      (polyAdd (polyMul (polyMul q (polyMul psi psi)) Pq)
        (polyNeg (polyMul (polyMul q q) (polyMul psi psi)))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.add (.var 2) (.neg (.var 0))))
      (.add (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 2))
        (.neg (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))))
      (by decide) (fun | 0 => q | 1 => psi | _ => Pq)
  have hn : H n (polyNeg (polyMul (polyMul q q) (polyMul psi psi))) ≈
      -(H n (polyMul (polyMul q q) (polyMul psi psi))) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (YMGap.Continuum.QuaternionHaarAngularCarrier.neg_smul _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul n (-1) _)
        (poly_identity_of_normal_eq
          (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
          (by decide) (fun _ => H n (polyMul (polyMul q q) (polyMul psi psi)))))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hc)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append n _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _) hn))

/-- Tested heat image of the centered observable. The source is absent from
this purely finite heat identity. -/
theorem shifted_image (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    {f : RatPoly} (hf : SupportedQuaternionBlocks n f)
    (lambda c : Q')
    (heig : SupportedHaarEqv n (productMap n w K ids f) (polySmul lambda f)) :
    SupportedHaarEqv n (productMap n w K ids (shifted f c))
      (polyAdd (polySmul lambda f) (polySmul (-c) polyOne)) := by
  have hpoly : RatPolyCoeffEqv
      (productMap n w K ids (shifted f c))
      (polyAdd (polySmul 1 (productMap n w K ids f))
        (polySmul (-c) (productMap n w K ids polyOne))) := by
    unfold shifted
    exact (productMap_add n w K ids _ _).trans
      ((productMap_smul n w K ids 1 f).add
        (productMap_smul n w K ids (-c) polyOne))
  exact (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier hpoly)).trans
    ((heig.smul 1).add ((productMap_one n w K ids hnd hids).smul (-c))) |>.trans
      (SupportedHaarEqv.of_carrier (RatPolyCoeffEqv.haarCarrier
        ((RatPolyCoeffEqv.one_smul (polySmul lambda f)).add
          (RatPolyCoeffEqv.refl _))))

/-- The mixed norm term of a centered heat eigenobservable uses the SAME
source moment and the existing signed source correction. -/
theorem centered_mixed_pin (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hnd : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    {q f : RatPoly} (hq : SupportedQuaternionBlocks n q)
    (hf : SupportedQuaternionBlocks n f)
    (lambda c : Q')
    (heig : SupportedHaarEqv n (productMap n w K ids f) (polySmul lambda f)) :
    let psi := shifted f c
    H n (polyMul (polyMul (polyMul q q) psi)
      (productMap n w K ids psi)) ≈
      lambda*sourceMoment n w K ids q (polyMul psi psi) +
        -(lambda*sourceCorrection n w K ids q psi) +
        -((1-lambda)*c*H n (polyMul (polyMul q q) psi)) := by
  dsimp only
  let psi := shifted f c
  let T := polyMul (polyMul q q) psi
  let A := H n T
  let B := H n (polyMul T f)
  let Q := H n (polyMul (polyMul q q) (polyMul psi psi))
  let V := sourceMoment n w K ids q (polyMul psi psi)
  let C := sourceCorrection n w K ids q psi
  have hpsi := shifted_supported hf c
  have hT := supported_polyMul (supported_polyMul hq hq) hpsi
  have hi := (shifted_image n w K ids hnd hids hf lambda c heig) T hT
  have ha : H n (polyMul T (polyAdd (polySmul lambda f)
      (polySmul (-c) polyOne))) ≈ lambda*B + -(c*A) := by
    have hs := quaternionHaar_polyMul_add_right n T (polySmul lambda f)
      (polySmul (-c) polyOne)
    have hf' := quaternionHaar_polyMul_smul_right n lambda T f
    have hc' := quaternionHaar_polyMul_smul_right n (-c) T polyOne
    have hone : H n (polyMul T polyOne) ≈ H n T :=
      haar_of_coeff (RatPolyCoeffEqv.mul_one T)
    exact Q'.eqv_trans _ _ _ hs
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hf'
        (Q'.eqv_trans _ _ _ hc' (Q'.mul_eqv_congr_left (-c) _ _ hone)))
        (poly_identity_of_normal_eq
          (.add (.mul (.var 0) (.var 1)) (.mul (.neg (.var 2)) (.var 3)))
          (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
          (by decide) (fun | 0 => lambda | 1 => B | 2 => c | _ => A)))
  have hshift := shifted_haar n T f c
  have hQ : H n (polyMul T psi) ≈ Q :=
    haar_of_coeff (RatPolyCoeffEqv.mul_assoc (polyMul q q) psi psi)
  have hC := correction_expansion n w K ids q psi
  have hB : B ≈ Q + c*A := by
    have h := Q'.eqv_trans _ _ _ (Q'.eqv_symm hshift) hQ
    exact Q'.eqv_trans _ _ _ (Q'.add_sub_cancel_eqv B (c*A))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ h)
        (Q'.add_comm_eqv (c*A) Q))
  have hQVC : Q ≈ V-C := by
    have hn := Q'.neg_eqv_congr _ _ hC
    have h : V-C ≈ Q :=
      Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hn)
        (poly_identity_of_normal_eq
          (.add (.var 0) (.neg (.add (.var 0) (.neg (.var 1)))))
          (.var 1) (by decide) (fun | 0 => V | _ => Q))
    exact Q'.eqv_symm h
  exact Q'.eqv_trans _ _ _ hi
    (Q'.eqv_trans _ _ _ ha
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_left lambda _ _ hB) (Q'.eqv_refl _))
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.mul_eqv_congr_left lambda _ _
              (Q'.add_eqv_congr' hQVC (Q'.eqv_refl _)))
            (Q'.eqv_refl _))
          (poly_identity_of_normal_eq
            (.add (.mul (.var 0) (.add (.add (.var 1) (.neg (.var 2)))
              (.mul (.var 3) (.var 4)))) (.neg (.mul (.var 3) (.var 4))))
            (.add (.add (.mul (.var 0) (.var 1))
              (.neg (.mul (.var 0) (.var 2))))
              (.neg (.mul
                (.mul (.add (.const 1) (.neg (.var 0))) (.var 3))
                (.var 4))))
            (by decide) (fun | 0 => lambda | 1 => V | 2 => C | 3 => c | _ => A)))))

#print axioms shifted_image
#print axioms centered_mixed_pin

end YMGap.Continuum.SU2QuaternionProductHeatCenteredMixed
