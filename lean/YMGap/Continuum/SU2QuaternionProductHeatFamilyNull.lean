/-
# Full absent-family nullity for the original product heat

If integrating a finite family of absent lower coordinates gives zero
coefficientwise, the original product heat map annihilates the input under
every Haar test. All other coordinates remain in the input, and the whole
family is integrated against one unchanged spectator polynomial.

The conclusion is a Haar-pairing identity, not raw coefficient equality
of the output. No support, positivity, distinctness or late-cutoff premise
is required. This is not a completed OS-kernel or spectral-gap statement.
-/

import YMGap.Continuum.SU2QuaternionHaarFamilyProjection
import YMGap.Continuum.SU2QuaternionProductHeatMarginals

namespace YMGap.Continuum.SU2QuaternionProductHeatFamilyNull

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
  (quaternionHaar_polyMul_eq_after_integratingBlocks)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
  (productHeat productMap productMap_pairing productHeat_independent_lower lift_lower_independent)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv

/-- Full-family conditional nullity suffices; individual coordinate nullity
is not assumed. Repeated indices in either list cause no difficulty. -/
theorem productMap_family_pair_zero (n : Nat) (w : Q') (K : Nat) (ids : List Nat)
    (hids : ∀ i, i ∈ ids → i < n) (F : List Nat)
    (hF : ∀ i, i ∈ F → i < n) (hnot : ∀ i, i ∈ F → i ∉ ids)
    (f g : RatPoly) (hc : RatPolyCoeffEqv (familyProject F f) polyZero) :
    quaternionHaar n (polyMul g (productMap n w K ids f)) ≈ 0 := by
  let r := polyMul (productHeat n w K ids) (liftBoundary n g)
  have hr : ∀ i, i ∈ F → QuaternionBlockIndependent i r := fun i hi =>
    quaternionBlockIndependent_polyMul
      (productHeat_independent_lower n w K ids hids i (hF i hi) (hnot i hi))
      (lift_lower_independent n g i (hF i hi))
  have halg : RatPolyCoeffEqv
      (polyMul (productHeat n w K ids) (polyMul f (liftBoundary n g))) (polyMul r f) :=
    ((RatPolyCoeffEqv.mul_comm f (liftBoundary n g)).mul_left _).trans
      (RatPolyCoeffEqv.mul_assoc _ _ _).symm
  exact Q'.eqv_trans _ _ _ (productMap_pairing n w K ids f g)
    (Q'.eqv_trans _ _ _ (haar_of_coeff halg)
      (Q'.eqv_trans _ _ _
        (quaternionHaar_polyMul_eq_after_integratingBlocks (n+n) F r f
          (fun i hi => Nat.lt_of_lt_of_le (hF i hi) (Nat.le_add_right n n)) hr)
        (haar_of_coeff ((hc.mul_left r).trans (RatPolyCoeffEqv.mul_zero_right r)))))

end YMGap.Continuum.SU2QuaternionProductHeatFamilyNull

#print axioms YMGap.Continuum.SU2QuaternionProductHeatFamilyNull.productMap_family_pair_zero
