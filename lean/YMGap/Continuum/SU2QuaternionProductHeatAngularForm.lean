/-
# Signed angular directions in the original product-heat pairing

Simultaneous rotation of the two endpoints of each selected heat factor,
together with exact product-Haar integration by parts, makes every angular
direction skew-adjoint in the ORIGINAL kinetic pairing. Finite signed sums
retain all mixed terms. Positivity of that same pairing then gives a
nonpositive second angular response, without a number-of-directions loss.

This is not a normalized Wilson-jump estimate, a variance comparison, or a
physical mass gap. No interaction factor in the supplied source is removed.
-/

import YMGap.Continuum.SU2QuaternionRelativeHeatAngularInvariant
import YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
import YMGap.Continuum.SU2QuaternionAngularLift
import YMGap.Continuum.SU2QuaternionProductHeatDualForm
import YMGap.Continuum.SU2QuaternionProductHeatConstant

namespace YMGap.Continuum.SU2QuaternionProductHeatAngularForm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularLift
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionRelativeHeatAngularInvariant
open YMGap.Continuum.SU2QuaternionHaarAngularIBPAt
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private def paired (n s u v : Nat) (p : RatPoly) : RatPoly :=
  polyAdd (angularDerivative (4*s+u) (4*s+v) p)
    (angularDerivative (4*(n+s)+u) (4*(n+s)+v) p)

private theorem paired_mul (n s u v : Nat) (p q : RatPoly) :
    RatPolyCoeffEqv (paired n s u v (polyMul p q))
      (polyAdd (polyMul (paired n s u v p) q)
        (polyMul p (paired n s u v q))) :=
  pairedAt_mul s (n+s) u v p q

/-- Every selected kinetic factor remains in the simultaneous-rotation law.
Repeated selected indices are allowed; no normalization or cutoff guard is
needed for this invariance. -/
theorem productHeat_pairedAngular_carrier (n s u v : Nat)
    (hs : s < n) (hu : u < 4) (hv : v < 4) (w : Q') (K : Nat) :
    ∀ ids : List Nat, (∀ i, i ∈ ids → i < n) →
      HaarCarrierEqv (n+n) (paired n s u v (productHeat n w K ids)) polyZero
  | [], _ => RatPolyCoeffEqv.haarCarrier
      ((angularDerivative_one _ _).add (angularDerivative_one _ _))
  | i::ids, hids => by
      have hi := hids i List.mem_cons_self
      have hhead : HaarCarrierEqv (n+n)
          (paired n s u v (heatAt i (n+i) w K)) polyZero := by
        by_cases hsi : s = i
        · subst i
          exact heatAt_pairedAngular_carrier_at (n+n) s (n+s) u v
            (by omega) (by omega) (Nat.ne_of_lt (by omega)) hu hv w K
        · have hl := angularDerivative_blockIndependent_zero hu hv
            (degree_zero_independent
              (heat_independent s i (n+i) hsi (Nat.ne_of_lt (by omega)) w K))
          have hr := angularDerivative_blockIndependent_zero hu hv
            (degree_zero_independent
              (heat_independent (n+s) i (n+i) (Nat.ne_of_gt (by omega))
                (by intro he; exact hsi (by omega)) w K))
          exact RatPolyCoeffEqv.haarCarrier (hl.add hr)
      exact (RatPolyCoeffEqv.haarCarrier
        (paired_mul n s u v (heatAt i (n+i) w K) (productHeat n w K ids))).trans
          ((HaarCarrierEqv.add (HaarCarrierEqv.mul_right _ hhead)
            ((productHeat_pairedAngular_carrier n s u v hs hu hv w K ids
              (fun j hj => hids j (List.mem_cons_of_mem i hj))).mul_left _)).trans
            (RatPolyCoeffEqv.haarCarrier
              ((RatPolyCoeffEqv.mul_zero_left _).add
                (RatPolyCoeffEqv.mul_zero_right _))))

private theorem paired_sources (n s u v : Nat) (hs : s<n) (hu : u<4) (hv : v<4)
    (f g : RatPoly) (hf : SupportedQuaternionBlocks n f) :
    RatPolyCoeffEqv (paired n s u v (polyMul f (liftBoundary n g)))
      (polyAdd
        (polyMul (angularDerivative (4*s+u) (4*s+v) f) (liftBoundary n g))
        (polyMul f (liftBoundary n (angularDerivative (4*s+u) (4*s+v) g)))) := by
  have hl := angularDerivative_blockIndependent_zero hu hv
    (lift_lower_independent n g s hs)
  have hr := angularDerivative_blockIndependent_zero hu hv (supported_upper_independent hf s)
  have ht := angularDerivative_liftBoundary n (4*s+u) (4*s+v) g
  rw [show 4*n+(4*s+u)=4*(n+s)+u by omega,
    show 4*n+(4*s+v)=4*(n+s)+v by omega] at ht
  have low := (angularDerivative_mul (4*s+u) (4*s+v) f (liftBoundary n g)).trans
    (((RatPolyCoeffEqv.refl _).add
      ((hl.mul_left f).trans (RatPolyCoeffEqv.mul_zero_right _))).trans
        (RatPolyCoeffEqv.add_zero _))
  have high := (angularDerivative_mul (4*(n+s)+u) (4*(n+s)+v) f (liftBoundary n g)).trans
    ((((hr.mul_right _).trans (RatPolyCoeffEqv.mul_zero_left _)).add
      (ht.mul_left f)).trans (RatPolyCoeffEqv.zero_add _))
  exact low.add high

/-- Angular skew-adjointness in the SAME selected product-heat form.
This keeps every kinetic factor; the inputs may have either sign. -/
theorem kineticPair_angular_sum_zero (n s u v : Nat)
    (hs : s<n) (hu : u<4) (hv : v<4) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i<n)
    (f g : RatPoly) (_hf : SupportedQuaternionBlocks n f)
    (hg : SupportedQuaternionBlocks n g) :
    kineticPair n w K ids (angularDerivative (4*s+u) (4*s+v) f) g +
      kineticPair n w K ids f (angularDerivative (4*s+u) (4*s+v) g) ≈ 0 := by
  let W := productHeat n w K ids
  let R := polyMul g (liftBoundary n f)
  let S := polyAdd
    (polyMul (angularDerivative (4*s+u) (4*s+v) g) (liftBoundary n f))
    (polyMul g (liftBoundary n (angularDerivative (4*s+u) (4*s+v) f)))
  have hi : HaarCarrierEqv (n+n) (paired n s u v (polyMul W R))
      (polyMul W S) :=
    (RatPolyCoeffEqv.haarCarrier (paired_mul n s u v W R)).trans
      ((HaarCarrierEqv.add
        (HaarCarrierEqv.mul_right R
          (productHeat_pairedAngular_carrier n s u v hs hu hv w K ids hids))
        (RatPolyCoeffEqv.haarCarrier ((paired_sources n s u v hs hu hv g f hg).mul_left W))).trans
          (RatPolyCoeffEqv.haarCarrier
            (((RatPolyCoeffEqv.mul_zero_left R).add (RatPolyCoeffEqv.refl _)).trans
              (RatPolyCoeffEqv.zero_add _))))
  have hz : quaternionHaar (n+n) (paired n s u v (polyMul W R)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (quaternionHaar_append (n+n) _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
        (quaternionHaar_angularDerivative_at (by omega : s<n+n) hu hv (polyMul W R))
        (quaternionHaar_angularDerivative_at (by omega : n+s<n+n) hu hv (polyMul W R)))
        (Q'.eqv_refl 0))
  have he : quaternionHaar (n+n) (polyMul W S) ≈
      kineticPair n w K ids f (angularDerivative (4*s+u) (4*s+v) g) +
      kineticPair n w K ids (angularDerivative (4*s+u) (4*s+v) f) g :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_add_right _ _ _))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append (n+n) _ _)
        (Q'.add_eqv_congr'
          (Q'.eqv_symm (productMap_pairing n w K ids _ _))
          (Q'.eqv_symm (productMap_pairing n w K ids _ _))))
  exact Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm he)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_carrier hi)) hz))

end YMGap.Continuum.SU2QuaternionProductHeatAngularForm

#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularForm.productHeat_pairedAngular_carrier
#print axioms YMGap.Continuum.SU2QuaternionProductHeatAngularForm.kineticPair_angular_sum_zero
