/-
# Weighted symmetry of the actual fixed-spatial transfer and its powers

The pairing is the original spatially weighted Haar pairing H[V*g*T f].
Ordered-head Fubini displays it as the double integral with BOTH spatial
weights V(x)V(y). Swapping the two actual slice carriers preserves Haar and
the original kinetic product, hence interchanges the two insertions.

All statements are finite signed rational identities, for arbitrary rational
nome and cutoff, with explicit support guards. No positive weight, division,
stationary normalization, completion, reflected OS form or self-adjoint
physical Hamiltonian is assumed or concluded.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight kineticWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticSymmetry (kineticWeight_swap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep transferStep_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

private theorem support_pair {blocks : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks blocks p) :
    SupportedQuaternionBlocks (blocks+blocks) p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _))

/-- Finite polynomial change of variables for one symmetric kernel.
The inserted lower/upper polynomials may themselves share all slice links. -/
theorem kernel_pairing_swap {blocks : Nat} {kernel lower upper : RatPoly}
    (hk : SupportedQuaternionBlocks (blocks+blocks) kernel)
    (hl : SupportedQuaternionBlocks blocks lower)
    (hu : SupportedQuaternionBlocks blocks upper)
    (hs : PaddedPolynomialCoeffEqv (blocks+blocks)
      (reindexQuaternionPolynomial (SU2QuaternionTwoSliceSwap.swap blocks) kernel) kernel) :
    quaternionHaar (blocks+blocks)
        (polyMul (polyMul kernel lower) (liftBoundary blocks upper)) ≈
      quaternionHaar (blocks+blocks)
        (polyMul (polyMul kernel upper) (liftBoundary blocks lower)) := by
  let p := polyMul (polyMul kernel lower) (liftBoundary blocks upper)
  have hp : SupportedQuaternionBlocks (blocks+blocks) p :=
    supported_polyMul (supported_polyMul hk (support_pair hl)) (lift_supported hu blocks)
  have hq : SupportedQuaternionBlocks (blocks+blocks)
      (polyMul (polyMul kernel upper) (liftBoundary blocks lower)) :=
    supported_polyMul (supported_polyMul hk (support_pair hu)) (lift_supported hl blocks)
  have hpin : PaddedPolynomialCoeffEqv (blocks+blocks)
      (reindexQuaternionPolynomial (SU2QuaternionTwoSliceSwap.swap blocks) p)
      (polyMul (polyMul kernel upper) (liftBoundary blocks lower)) := by
    dsimp only [p]
    rw [reindexQuaternionPolynomial_mul, reindexQuaternionPolynomial_mul]
    exact ((hs.mul (PaddedPolynomialCoeffEqv.of_prefix
        (SU2QuaternionTwoSliceSwap.lower_prefix blocks lower hl))).mul
      (PaddedPolynomialCoeffEqv.of_prefix
        (SU2QuaternionTwoSliceSwap.upper_prefix blocks upper hu))).trans
      (PaddedPolynomialCoeffEqv.of_coeff
        ((RatPolyCoeffEqv.mul_assoc kernel (liftBoundary blocks lower) upper).trans
          ((RatPolyCoeffEqv.mul_left kernel
            (RatPolyCoeffEqv.mul_comm (liftBoundary blocks lower) upper)).trans
            (RatPolyCoeffEqv.mul_assoc kernel upper (liftBoundary blocks lower)).symm)))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (SU2QuaternionTwoSliceSwap.haar blocks p hp))
    (hpin.haar (SU2QuaternionTwoSliceSwap.polynomial_supported blocks p) hq)

private theorem weighted_step_pairing (blocks : Nat) (kernel weight f g : RatPoly) :
    quaternionHaar blocks (polyMul weight (polyMul g (step blocks kernel weight f))) ≈
      quaternionHaar (blocks+blocks)
        (polyMul (polyMul kernel (polyMul weight f))
          (liftBoundary blocks (polyMul weight g))) :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff ((RatPolyCoeffEqv.mul_assoc weight g (step blocks kernel weight f)).symm.trans
      (RatPolyCoeffEqv.mul_comm (polyMul weight g) (step blocks kernel weight f))))
    (Q'.eqv_symm (step_pairing blocks blocks kernel weight f (polyMul weight g)))

/-- Symmetry in the actual V-weighted Haar form. Both spatial factors are
retained, and neither positivity of w nor a late-cutoff guard is needed. -/
theorem transferStep_weighted_symmetric (w : Q') (K width : Nat) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hg : SupportedQuaternionBlocks (N width) g) :
    weightedMass w K width (polyMul g (transferStep w K width f)) ≈
      weightedMass w K width (polyMul f (transferStep w K width g)) :=
  Q'.eqv_trans _ _ _
    (weighted_step_pairing (N width) (kineticWeight w K width) (spatialWeight w K width) f g)
    (Q'.eqv_trans _ _ _
      (kernel_pairing_swap (kineticWeight_supported w K width)
        (supported_polyMul (spatialWeight_supported w K width) hf)
        (supported_polyMul (spatialWeight_supported w K width) hg)
        (kineticWeight_swap w K width))
      (Q'.eqv_symm
        (weighted_step_pairing (N width) (kineticWeight w K width) (spatialWeight w K width) g f)))

private theorem weighted_product_comm (w : Q') (K width : Nat) (f g : RatPoly) :
    weightedMass w K width (polyMul f g) ≈ weightedMass w K width (polyMul g f) :=
  haar_of_coeff (RatPolyCoeffEqv.mul_left _ (RatPolyCoeffEqv.mul_comm f g))

/-- The existing right-recursive iterate also satisfies the left successor
identity by finite function iteration alone. -/
private theorem iterate_succ_left (blocks : Nat) (kernel weight : RatPoly) :
    ∀ (count : Nat) (f : RatPoly),
      iterateStep blocks kernel weight (count+1) f =
        step blocks kernel weight (iterateStep blocks kernel weight count f)
  | 0, _ => rfl
  | count+1, f => iterate_succ_left blocks kernel weight count (step blocks kernel weight f)

/-- Every actual finite transfer power has the same weighted symmetry on
the supported fixed-spatial carrier. This remains an unnormalized finite
identity, not a completed-operator or physical OS assertion. -/
theorem iterateStep_weighted_symmetric (w : Q') (K width count : Nat) {f g : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f)
    (hg : SupportedQuaternionBlocks (N width) g) :
    weightedMass w K width
        (polyMul g (iterateStep (N width) (kineticWeight w K width)
          (spatialWeight w K width) count f)) ≈
      weightedMass w K width
        (polyMul f (iterateStep (N width) (kineticWeight w K width)
          (spatialWeight w K width) count g)) := by
  induction count generalizing f g with
  | zero => exact weighted_product_comm w K width g f
  | succ count ih =>
      let fg := iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) count g
      have hfg : SupportedQuaternionBlocks (N width) fg :=
        iterateStep_supported (kineticWeight_supported w K width)
          (spatialWeight_supported w K width) count hg
      have hfirst := ih (transferStep_supported w K width hf) hg
      have hlast := transferStep_weighted_symmetric w K width hf hfg
      have he := Q'.eqv_trans _ _ _ hfirst
        (Q'.eqv_trans _ _ _ (weighted_product_comm w K width (transferStep w K width f) fg) hlast)
      change weightedMass w K width
          (polyMul g (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width)
            count (transferStep w K width f))) ≈
        weightedMass w K width (polyMul f
          (step (N width) (kineticWeight w K width) (spatialWeight w K width)
            (iterateStep (N width) (kineticWeight w K width) (spatialWeight w K width) count g))) at he
      rw [← iterate_succ_left (N width) (kineticWeight w K width) (spatialWeight w K width) count g] at he
      exact he

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry.kernel_pairing_swap

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry.transferStep_weighted_symmetric
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry.iterateStep_weighted_symmetric
