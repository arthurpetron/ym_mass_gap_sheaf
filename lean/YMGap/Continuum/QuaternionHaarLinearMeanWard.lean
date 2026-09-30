/-
# Weighted Ward identity for a head-linear quaternion polynomial

The weight is arbitrary: its full angular derivative is retained. Summing
the six exact Haar integration-by-parts identities and using the head-linear
angular Casimir gives the mean identity without a positivity or support
assumption. No bound on the logarithmic derivative is asserted here.
-/

import YMGap.Continuum.QuaternionHaarLinearAngularEnergy

namespace YMGap.Continuum.QuaternionHaarLinearMeanWard

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy

local infix:50 " ≈ " => Q'.eqv

private theorem sixValue_neg (g : Nat → Nat → Q') :
    sixValue (fun i j => -(g i j)) ≈ -(sixValue g) := by
  have h (a b c : Q') (hbc : b ≈ -c) : -a+b ≈ -(a+c) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hbc)
      (Q'.eqv_symm (Q'.neg_add_eqv a c))
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _
    (Q'.eqv_symm (Q'.neg_add_eqv (g 1 3) (g 2 3))))))

private theorem weighted_pair (tail : Nat) {i j : Nat}
    (hi : i < 4) (hj : j < 4) (W f : RatPoly) :
    quaternionHaar (tail+1)
      (polyMul (angularDerivative i j W) (angularDerivative i j f)) ≈
      -(quaternionHaar (tail+1)
        (polyMul W (angularDerivative i j (angularDerivative i j f)))) := by
  have h := quaternionHaar_weighted_angular tail hi hj W (angularDerivative i j f)
  have he : quaternionHaar (tail+1)
      (polyMul (angularDerivative i j W) (angularDerivative i j f)) +
      quaternionHaar (tail+1)
        (polyMul W (angularDerivative i j (angularDerivative i j f))) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append (tail+1) _ _)) h
  apply QPoly.q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.neg (.var 1))))
      (.add (.var 0) (.var 1)) (by decide)
      (fun n => if n = 0 then quaternionHaar (tail+1)
        (polyMul (angularDerivative i j W) (angularDerivative i j f))
      else quaternionHaar (tail+1)
        (polyMul W (angularDerivative i j (angularDerivative i j f))))) he

/-- Exact weighted six-direction Ward identity for any head-linear test.
The original polynomial weight and every spectator coordinate are retained. -/
theorem weighted_linear_mean_ward (tail : Nat) (W f : RatPoly)
    (hf : HasQuaternionBlockDegree 0 1 f) :
    sixValue (fun i j => quaternionHaar (tail+1)
      (polyMul (angularDerivative i j W) (angularDerivative i j f))) ≈
      3 * quaternionHaar (tail+1) (polyMul W f) := by
  let m := fun i j => quaternionHaar (tail+1)
    (polyMul W (angularDerivative i j (angularDerivative i j f)))
  have hp : sixValue (fun i j => quaternionHaar (tail+1)
      (polyMul (angularDerivative i j W) (angularDerivative i j f))) ≈
      sixValue (fun i j => -(m i j)) :=
    sixValue_congr _ _ (fun _ _ hi hj => weighted_pair tail hi hj W f)
  have hs : quaternionHaar (tail+1) (polyMul W (polySmul (-3) f)) ≈
      (-3) * quaternionHaar (tail+1) (polyMul W f) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right (-3) W f))
      (quaternionHaar_polySmul (tail+1) (-3) _)
  have hm : sixValue m ≈ (-3) * quaternionHaar (tail+1) (polyMul W f) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_six (tail+1) W _))
      (Q'.eqv_trans _ _ _
        (linear_angularLaplacian (Nat.zero_lt_succ tail) f hf W) hs)
  exact Q'.eqv_trans _ _ _ hp (Q'.eqv_trans _ _ _ (sixValue_neg m)
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hm)
      (poly_identity_of_normal_eq (.neg (.mul (.const (-3)) (.var 0)))
        (.mul (.const 3) (.var 0)) (by decide)
        (fun _ => quaternionHaar (tail+1) (polyMul W f)))))

end YMGap.Continuum.QuaternionHaarLinearMeanWard

#print axioms YMGap.Continuum.QuaternionHaarLinearMeanWard.weighted_linear_mean_ward
