/-
# All-degree retained harmonic angular energy

Tangential Haar integration by parts and the exact SU(2) angular Casimir
identify the complete six-plane energy of every homogeneous harmonic while
retaining an arbitrary head-independent background.  This is a local Haar
identity, not an interacting transfer-energy estimate.
-/

import YMGap.Continuum.QuaternionHaarAngularCasimir

namespace YMGap.Continuum.QuaternionHaarHarmonicAngularEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionHeadDegreeDifferential
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.QuaternionHaarLinearAngularEnergy
open YMGap.Continuum.QuaternionHaarAngularCasimir
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem haar_mul_add (blocks : Nat) (r p q : RatPoly) :
    quaternionHaar blocks (polyMul r (polyAdd p q)) ≈
      quaternionHaar blocks (polyMul r p) + quaternionHaar blocks (polyMul r q) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right r p q))
    (quaternionHaar_append blocks _ _)

/-- One-plane Dirichlet identity with every head-independent tail factor
retained.  No degree or harmonicity premise is used at this stage. -/
private theorem energy_pair (tail : Nat) {i j : Nat} (hi : i < 4) (hj : j < 4)
    (r p : RatPoly) (hr : HasQuaternionBlockDegree 0 0 r) :
    quaternionHaar (tail+1) (polyMul r
      (polyMul (angularDerivative i j p) (angularDerivative i j p))) ≈
      -(quaternionHaar (tail+1) (polyMul (polyMul r p)
        (angularDerivative i j (angularDerivative i j p)))) := by
  let d := angularDerivative i j p
  let dd := angularDerivative i j d
  have hz := quaternionHaar_retained_background tail hi hj r p d hr
  have he : quaternionHaar (tail+1) (polyMul r (polyMul d d)) +
      quaternionHaar (tail+1) (polyMul (polyMul r p) dd) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (haar_of_coeff (RatPolyCoeffEqv.mul_assoc r p dd)))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_mul_add (tail+1) r _ _)) hz)
  apply q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.neg (.var 1))))
      (.add (.var 0) (.var 1)) (by decide)
      (fun n => if n = 0 then quaternionHaar (tail+1) (polyMul r (polyMul d d))
        else quaternionHaar (tail+1) (polyMul (polyMul r p) dd))) he

private theorem sixValue_neg (f : Nat → Nat → Q') :
    sixValue (fun i j => -(f i j)) ≈ -(sixValue f) := by
  have h (a b c : Q') (hbc : b ≈ -c) : -a+b ≈ -(a+c) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hbc)
      (Q'.eqv_symm (Q'.neg_add_eqv a c))
  exact h _ _ _ (h _ _ _ (h _ _ _ (h _ _ _
    (Q'.eqv_symm (Q'.neg_add_eqv (f 1 3) (f 2 3))))))

/-- Exact all-degree angular energy with every head-independent background
retained.  All six coordinate planes are essential. -/
theorem retained_harmonic_energy (tail n : Nat) (r p : RatPoly)
    (hr : HasQuaternionBlockDegree 0 0 r)
    (hp : HasQuaternionBlockDegree 0 n p)
    (hh : RatPolyCoeffEqv (headLaplacian p) polyZero) :
    quaternionHaar (tail+1) (polyMul r (angularSquare p)) ≈
      (Q'.ofNat n * (Q'.ofNat n + 2)) *
        quaternionHaar (tail+1) (polyMul r (polyMul p p)) := by
  let eigenvalue := Q'.ofNat n * (Q'.ofNat n + 2)
  let m := fun i j => quaternionHaar (tail+1) (polyMul (polyMul r p)
    (angularDerivative i j (angularDerivative i j p)))
  have hpair := sixValue_congr
    (fun i j => quaternionHaar (tail+1) (polyMul r
      (polyMul (angularDerivative i j p) (angularDerivative i j p))))
    (fun i j => -(m i j)) (fun _ _ hi hj => energy_pair tail hi hj r p hr)
  have hscale : quaternionHaar (tail+1)
      (polyMul (polyMul r p) (polySmul (-eigenvalue) p)) ≈
      (-eigenvalue) * quaternionHaar (tail+1) (polyMul r (polyMul p p)) :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff (RatPolyCoeffEqv.polyMul_smul_right (-eigenvalue) _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul (tail+1) (-eigenvalue) _)
        (Q'.mul_eqv_congr_left (-eigenvalue) _ _
          (haar_of_coeff (RatPolyCoeffEqv.mul_assoc r p p))))
  have hm : sixValue m ≈
      (-eigenvalue) * quaternionHaar (tail+1) (polyMul r (polyMul p p)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_six (tail+1) (polyMul r p) _))
      (Q'.eqv_trans _ _ _
        (harmonic_angularLaplacian (Nat.zero_lt_succ tail) p hp hh (polyMul r p)) hscale)
  exact Q'.eqv_trans _ _ _ (haar_six (tail+1) r _)
    (Q'.eqv_trans _ _ _ hpair
      (Q'.eqv_trans _ _ _ (sixValue_neg m)
        (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hm)
          (poly_identity_of_normal_eq
            (.neg (.mul (.neg (.var 0)) (.var 1)))
            (.mul (.var 0) (.var 1)) (by decide)
            (fun k => if k = 0 then eigenvalue
              else quaternionHaar (tail+1) (polyMul r (polyMul p p)))))))

end YMGap.Continuum.QuaternionHaarHarmonicAngularEnergy

#print axioms YMGap.Continuum.QuaternionHaarHarmonicAngularEnergy.retained_harmonic_energy
