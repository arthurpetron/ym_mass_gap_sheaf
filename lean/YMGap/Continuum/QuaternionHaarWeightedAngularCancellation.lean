/-
# Exact cancellation of endpoint-weight derivatives

For any polynomial endpoint weight a and signed observable f, Haar
integration by parts gives

  H[Gamma(a*f)] + H[a*f^2 * L a] = H[a^2 * Gamma(f)].

Here L is the existing six-plane angular Laplacian and Gamma its summed
derivative square. The correction is retained with its actual sign; all
derivatives of a cancel. No positive lower bound, reciprocal, eigenvector,
independence or estimate of a is required. This is a local differential
identity, not a finite-time heat comparison or a physical generator pin.
-/

import YMGap.Continuum.QuaternionHaarLinearAngularEnergy

namespace YMGap.Continuum.QuaternionHaarWeightedAngularCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy

local infix:50 " ≈ " => Q'.eqv
local notation:max "H" n:arg => quaternionHaar n

/-- The explicitly constructed divergence witness. -/
def angularFlux (i j : Nat) (a f : RatPoly) : RatPoly :=
  polyMul (polyMul a (polyMul f f)) (angularDerivative i j a)

/-- The cancellation is polynomial algebra modulo one exact divergence. -/
theorem angular_weight_divergence (i j : Nat) (a f : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd
        (polyMul (angularDerivative i j (polyMul a f))
          (angularDerivative i j (polyMul a f)))
        (polyMul (polyMul a (polyMul f f))
          (angularDerivative i j (angularDerivative i j a))))
      (polyAdd
        (polyMul (polyMul a a)
          (polyMul (angularDerivative i j f) (angularDerivative i j f)))
        (angularDerivative i j (angularFlux i j a f))) := by
  let da := angularDerivative i j a
  let df := angularDerivative i j f
  let dda := angularDerivative i j da
  have haf := angularDerivative_mul i j a f
  have hff := angularDerivative_mul i j f f
  have haff := (angularDerivative_mul i j a (polyMul f f)).trans
    ((RatPolyCoeffEqv.refl _).add (hff.mul_left a))
  have hflux := (angularDerivative_mul i j (polyMul a (polyMul f f)) da).trans
    ((haff.mul_right da).add (RatPolyCoeffEqv.refl _))
  have hp := coeffEvalExpr_eqv_of_normalize_eq
    (.add
      (.mul (.add (.mul (.var 2) (.var 1)) (.mul (.var 0) (.var 3)))
        (.add (.mul (.var 2) (.var 1)) (.mul (.var 0) (.var 3))))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 4)))
    (.add
      (.mul (.mul (.var 0) (.var 0)) (.mul (.var 3) (.var 3)))
      (.add
        (.mul (.add (.mul (.var 2) (.mul (.var 1) (.var 1)))
          (.mul (.var 0) (.add (.mul (.var 3) (.var 1)) (.mul (.var 1) (.var 3)))))
          (.var 2))
        (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.var 4))))
    (by decide) (fun | 0 => a | 1 => f | 2 => da | 3 => df | _ => dda)
  exact ((haf.mul haf).add (RatPolyCoeffEqv.refl _)).trans
    (hp.trans ((RatPolyCoeffEqv.refl _).add hflux).symm)

/-- One selected plane: keep the weight correction until after Haar
integration. This holds even for signed a and f. -/
theorem angular_weight_cancellation (tail : Nat) {i j : Nat}
    (hi : i < 4) (hj : j < 4) (a f : RatPoly) :
    H (tail+1) (polyMul (angularDerivative i j (polyMul a f))
      (angularDerivative i j (polyMul a f))) +
      H (tail+1) (polyMul (polyMul a (polyMul f f))
        (angularDerivative i j (angularDerivative i j a))) ≈
    H (tail+1) (polyMul (polyMul a a)
      (polyMul (angularDerivative i j f) (angularDerivative i j f))) := by
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append (tail+1) _ _))
    (Q'.eqv_trans _ _ _ (haar_of_coeff (angular_weight_divergence i j a f))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append (tail+1) _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl _)
            (quaternionHaar_angularDerivative_zero tail hi hj (angularFlux i j a f)))
          (QPoly.q_add_zero_eqv _))))

private theorem sixValue_add (f g : Nat → Nat → Q') :
    sixValue f + sixValue g ≈ sixValue (fun i j => f i j + g i j) :=
  poly_identity_of_normal_eq
    (.add
      (.add (.var 0) (.add (.var 1) (.add (.var 2)
        (.add (.var 3) (.add (.var 4) (.var 5))))))
      (.add (.var 6) (.add (.var 7) (.add (.var 8)
        (.add (.var 9) (.add (.var 10) (.var 11)))))))
    (.add (.add (.var 0) (.var 6))
      (.add (.add (.var 1) (.var 7))
        (.add (.add (.var 2) (.var 8))
          (.add (.add (.var 3) (.var 9))
            (.add (.add (.var 4) (.var 10)) (.add (.var 5) (.var 11)))))))
    (by decide) (fun
      | 0 => f 0 1 | 1 => f 0 2 | 2 => f 0 3
      | 3 => f 1 2 | 4 => f 1 3 | 5 => f 2 3
      | 6 => g 0 1 | 7 => g 0 2 | 8 => g 0 3
      | 9 => g 1 2 | 10 => g 1 3 | _ => g 2 3)

private theorem haar_six_unweighted (blocks : Nat) (f : Nat → Nat → RatPoly) :
    H blocks (six f) ≈ sixValue (fun i j => H blocks (f i j)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff (RatPolyCoeffEqv.one_mul (six f))))
    (Q'.eqv_trans _ _ _ (haar_six blocks polyOne f)
      (sixValue_congr _ _ (fun _ _ _ _ => haar_of_coeff (RatPolyCoeffEqv.one_mul _))))

/-- The complete six-direction cancellation on the original Haar measure.
No endpoint regularity constant enters: its derivatives cancel exactly. -/
theorem weighted_angular_cancellation (tail : Nat) (a f : RatPoly) :
    H (tail+1) (angularSquare (polyMul a f)) +
      H (tail+1) (polyMul (polyMul a (polyMul f f)) (angularLaplacian a)) ≈
    H (tail+1) (polyMul (polyMul a a) (angularSquare f)) := by
  let left := fun i j => H (tail+1)
    (polyMul (angularDerivative i j (polyMul a f))
      (angularDerivative i j (polyMul a f)))
  let correction := fun i j => H (tail+1)
    (polyMul (polyMul a (polyMul f f))
      (angularDerivative i j (angularDerivative i j a)))
  let right := fun i j => H (tail+1)
    (polyMul (polyMul a a)
      (polyMul (angularDerivative i j f) (angularDerivative i j f)))
  have hl : H (tail+1) (angularSquare (polyMul a f)) ≈ sixValue left :=
    haar_six_unweighted (tail+1) _
  have hc : H (tail+1)
      (polyMul (polyMul a (polyMul f f)) (angularLaplacian a)) ≈
      sixValue correction := haar_six (tail+1) (polyMul a (polyMul f f)) _
  have hr : H (tail+1) (polyMul (polyMul a a) (angularSquare f)) ≈
      sixValue right := haar_six (tail+1) (polyMul a a) _
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hl hc)
    (Q'.eqv_trans _ _ _ (sixValue_add left correction)
      (Q'.eqv_trans _ _ _
        (sixValue_congr _ right (fun _ _ hi hj => angular_weight_cancellation tail hi hj a f))
        (Q'.eqv_symm hr)))

end YMGap.Continuum.QuaternionHaarWeightedAngularCancellation

#print axioms YMGap.Continuum.QuaternionHaarWeightedAngularCancellation.angular_weight_divergence
#print axioms YMGap.Continuum.QuaternionHaarWeightedAngularCancellation.angular_weight_cancellation
#print axioms YMGap.Continuum.QuaternionHaarWeightedAngularCancellation.weighted_angular_cancellation
