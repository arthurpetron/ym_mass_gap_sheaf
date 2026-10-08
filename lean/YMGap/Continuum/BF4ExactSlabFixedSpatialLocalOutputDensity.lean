/-
# The literal last-step density with one outgoing heat factor removed

Every other original kinetic factor, the complete lower-slice spatial weight,
and the literal lifted unit remain in the density. Distinct active blocks make
this density independent of the selected outgoing quaternion. The product
factorization is coefficient-exact, before Haar integration or differentiation.
This is a finite original-action input for the conditional signed Gram join;
no marginal-derivative, Hessian-sign or scaling conclusion is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScorePin
import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
import YMGap.Continuum.SU2QuaternionWeightedProductLocalGap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialLocalOutputDensity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepPairedScorePin (lastStepAction)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarCertificateLift
open YMGap.Continuum.SU2QuaternionHeadWindowContraction (halfOpenAction)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatContraction
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight kineticWeight

/-- Remove precisely one selected original kinetic factor, not its spatial
weight or the lifted terminal unit. -/
def localOutputDensity (w : Q') (K width s : Nat) : RatPoly :=
  polyMul (productHeat (N width) w K (eraseIndex s (activeBlocks width)))
    (polyMul (spatialWeight w K width) (liftBoundary (N width) polyOne))

private theorem remaining_lt (width s j : Nat)
    (hj : j ∈ eraseIndex s (activeBlocks width)) : j < N width :=
  activeBlocks_lt width j (mem_of_mem_erase s hj)

private theorem support_extend {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (hle : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 hle)

/-- The density uses the unchanged lower-then-upper original carrier. -/
theorem localOutputDensity_supported (w : Q') (K width s : Nat) :
    SupportedQuaternionBlocks (N width+N width) (localOutputDensity w K width s) :=
  supported_polyMul
    (productHeat_supported (N width) w K _ (remaining_lt width s))
    (supported_polyMul
      (support_extend (spatialWeight_supported w K width) (by omega))
      (lift_supported (supported_one (N width)) (N width)))

/-- Constructed positivity keeps every remaining heat factor; its cutoff is
exactly the original all-nome head cutoff. -/
def localOutputDensity_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (hK : headCutoff w ≤ K) (width s : Nat) :
    Certificate (N width+N width) (localOutputDensity w K width s) :=
  (productHeatCertificate (N width) hw0 hw1 K hK _ (remaining_lt width s)).mul
    ((spatialCertificate hw0 hw1 K width (N width+N width) (by omega) hK).mul
      (lift_certificate (N width) (Certificate.one (N width))))

/-- All remaining factors are independent of the selected OUTPUT block.
Nodup of the original active list is used, not an assumed independence law. -/
theorem localOutputDensity_independent (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) :
    QuaternionBlockIndependent (N width+s) (localOutputDensity w K width s) :=
  quaternionBlockIndependent_polyMul
    (productHeat_independent_upper (N width) w K _ (remaining_lt width s)
      s (activeBlocks_lt width s hs) (not_mem_erase s (activeBlocks_nodup width)))
    (quaternionBlockIndependent_polyMul
      (supported_upper_independent (spatialWeight_supported w K width) s)
      (lift_upper_independent (N width)
        (degree_zero_independent (hasQuaternionBlockDegree_one s))))

/-- Multiplying back the selected factor recovers the literal full last-step
action coefficientwise, including its lifted unit. -/
theorem localOutputDensity_action_pin (w : Q') (K width s : Nat)
    (hs : s ∈ activeBlocks width) :
    RatPolyCoeffEqv
      (polyMul (localOutputDensity w K width s) (heatAt s (N width+s) w K))
      (lastStepAction w K width) := by
  have hkin : RatPolyCoeffEqv (kineticWeight w K width)
      (polyMul (heatAt s (N width+s) w K)
        (productHeat (N width) w K (eraseIndex s (activeBlocks width)))) := by
    rw [kineticWeight_eq_indexedProduct]
    exact polynomialProduct_perm _ (select_perm s hs)
  have hreorder : RatPolyCoeffEqv
      (polyMul (localOutputDensity w K width s) (heatAt s (N width+s) w K))
      (polyMul (polyMul (heatAt s (N width+s) w K)
        (productHeat (N width) w K (eraseIndex s (activeBlocks width))))
        (polyMul (spatialWeight w K width) (liftBoundary (N width) polyOne))) := by
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 2))) (.var 3))
      (.mul (.mul (.var 3) (.var 0)) (.mul (.var 1) (.var 2)))
      (by decide) (fun
        | 0 => productHeat (N width) w K (eraseIndex s (activeBlocks width))
        | 1 => spatialWeight w K width
        | 2 => liftBoundary (N width) polyOne
        | _ => heatAt s (N width+s) w K)
  exact hreorder.trans (hkin.symm.mul_right
    (polyMul (spatialWeight w K width) (liftBoundary (N width) polyOne)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialLocalOutputDensity

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalOutputDensity.localOutputDensity_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalOutputDensity.localOutputDensity_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalOutputDensity.localOutputDensity_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialLocalOutputDensity.localOutputDensity_action_pin
