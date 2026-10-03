/-
# The ORIGINAL own-mean variance endpoint of the product heat sweep

The selected updates remove their actual lower inputs. Every unselected
lower input must already be absent from the source; this is an explicit
independence hypothesis, not a discarded Haar-variance debt. All outputs
and their shared weight remain on the original carrier.

Under that hypothesis the joint sweep loss is exactly the original
conditional determinant variance. Its angular Poincare bound therefore
uses the original source, full heat law, and one computed fixed-source
cutoff, with no link-count prefactor. No interacting transfer, changing-
family, physical mass, OS or continuum conclusion is asserted here.
-/

import YMGap.Continuum.SU2QuaternionProductHeatEfronStein
import YMGap.Continuum.SU2QuaternionIndependentHeadsLift
import YMGap.Continuum.SU2QuaternionConditionalVarianceTower
import YMGap.Continuum.SU2QuaternionProductHeatConstant

namespace YMGap.Continuum.SU2QuaternionProductHeatConditionalVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarKernelBound
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex (carrier_of_supported)
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatConstant
open YMGap.Continuum.SU2QuaternionWeightedProjectionSweep
open YMGap.Continuum.SU2QuaternionProductHeatHybridSweep
open YMGap.Continuum.SU2QuaternionProductHeatEfronStein
open YMGap.Continuum.SU2QuaternionIndependentHeadsLift
open YMGap.Continuum.SU2QuaternionConditionalVarianceTower
open YMGap.Continuum.SU2QuaternionMultiHeadVarianceReplica (determinant)
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Actual normalized conditional mass, proved under EVERY surviving
insertion. This is not a free-coefficient equality to one. -/
theorem product_conditional_unit (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n) :
    HaarCarrierEqv n (partialHaarHeads n (productHeat n w K ids)) polyOne := by
  have hone := carrier_of_supported
    (productMap_supported n w K ids hids (supported_one n))
    (supported_one n) (productMap_one n w K ids hn hids)
  exact (RatPolyCoeffEqv.haarCarrier
    (partialHaarHeads_congr n (RatPolyCoeffEqv.mul_one (productHeat n w K ids)))).symm.trans hone

/-- The inactive-coordinate premise pays precisely the final lower Haar
integration; active coordinates are removed by the actual heat updates. -/
theorem sweep_all_lower_independent (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n) (p : RatPoly)
    (inactive : ∀ i, i < n → i ∉ ids → QuaternionBlockIndependent i p) :
    ∀ i, i < n → QuaternionBlockIndependent i (hybridSweep n w K ids p) := by
  intro i hi
  by_cases hm : i ∈ ids
  · exact hybridSweep_lower_independent n w K ids hids i hm p
  · apply weightedSweep_independent i (fun j => heatAt j (n+j) w K) ids
    · intro j hj
      apply degree_zero_independent
      exact heat_independent i j (n+j) (by intro he; subst j; exact hm hj)
        (by have := hids j hj; omega) w K
    · exact inactive i hi hm

/-- The SAME joint norm of the final sweep is the original own conditional
mean square, not the square of a surrogate or independently averaged output. -/
theorem joint_sweep_square_mean_pin (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (W p : RatPoly) (hW : SupportedQuaternionBlocks n W)
    (hp : SupportedQuaternionBlocks (n+n) p)
    (inactive : ∀ i, i < n → i ∉ ids → QuaternionBlockIndependent i p) :
    jointSquare n w K ids W (hybridSweep n w K ids p) ≈
      quaternionHaar n (polyMul W (polyMul
        (mean n (productHeat n w K ids) p)
        (mean n (productHeat n w K ids) p))) := by
  let S := hybridSweep n w K ids p
  let H := partialHaarHeads n S
  have hS := hybridSweep_supported n w K ids hids hp
  have hH := partialHaarHeads_supported n n S hS
  have hind := sweep_all_lower_independent n w K ids hids p inactive
  have hSL := independent_heads_lift n n S hS hind
  have hreplace := (HaarCarrierEqv.mul hSL hSL) (jointWeight n w K ids W)
  have horder : RatPolyCoeffEqv
      (polyMul (jointWeight n w K ids W)
        (polyMul (liftBoundary n H) (liftBoundary n H)))
      (polyMul (productHeat n w K ids) (liftBoundary n (polyMul W (polyMul H H)))) := by
    rw [lift_product, lift_product]
    exact coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.mul (.var 2) (.var 2))))
      (by decide) (fun | 0 => liftBoundary n W | 1 => productHeat n w K ids
                       | _ => liftBoundary n H)
  have hm : HaarCarrierEqv n H (mean n (productHeat n w K ids) p) :=
    hybridMap_carrier n w K ids hn hids p
  exact Q'.eqv_trans _ _ _ hreplace
    (Q'.eqv_trans _ _ _ (haar_of_coeff horder)
      (Q'.eqv_trans _ _ _
        (productHeat_upper_marginal n w K ids hn hids (polyMul W (polyMul H H))
          (supported_polyMul hW (supported_polyMul hH hH)))
        ((HaarCarrierEqv.mul hm hm) W)))

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -quaternionHaar blocks p
  | [] => by change (0 : Q') ≈ -0; decide
  | t::ps => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1))
        (haar_neg blocks ps)) (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem weighted_neg (blocks : Nat) (W p : RatPoly) :
    quaternionHaar blocks (polyMul W (polyNeg p)) ≈
      -quaternionHaar blocks (polyMul W p) :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.neg (.var 1))) (.neg (.mul (.var 0) (.var 1)))
    (by decide) (fun | 0 => W | _ => p))) (haar_neg blocks _)

/-- Exact own determinant variance = SAME joint-law sweep loss. The unit
mass, inactive-coordinate payment and own-mean pin are all proved above.
The identity does not require positivity or a late heat cutoff. -/
theorem determinant_sweep_loss_pin (n : Nat) (w : Q') (K : Nat)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (W p : RatPoly) (hW : SupportedQuaternionBlocks n W)
    (hp : SupportedQuaternionBlocks (n+n) p)
    (inactive : ∀ i, i < n → i ∉ ids → QuaternionBlockIndependent i p) :
    quaternionHaar n (polyMul W (determinant n (productHeat n w K ids) p)) ≈
      jointSquare n w K ids W p +
        -jointSquare n w K ids W (hybridSweep n w K ids p) := by
  have hv := determinant_variance_pin n n (productHeat n w K ids) p
    (product_conditional_unit n w K ids hn hids)
  have hsecond := joint_sweep_square_mean_pin n w K ids hn hids W p hW hp inactive
  have hfirst : quaternionHaar n (polyMul W (mean n (productHeat n w K ids) (polyMul p p))) ≈
      jointSquare n w K ids W p :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm (head_pairing n n
        (polyMul (productHeat n w K ids) (polyMul p p)) W))
        (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
          (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.mul (.var 2) (.var 0)) (.var 1)) (by decide)
          (fun | 0 => productHeat n w K ids | 1 => polyMul p p | _ => liftBoundary n W))))
  exact Q'.eqv_trans _ _ _ (hv W)
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_add_right n W _ _)
      (Q'.add_eqv_congr' hfirst (Q'.eqv_trans _ _ _
        (weighted_neg n W (polyMul (mean n (productHeat n w K ids) p)
          (mean n (productHeat n w K ids) p)))
        (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hsecond)))))

/-- Original conditional variance Poincare, with all shared output weights
and all selected heat factors retained. Its onset belongs to THIS source. -/
theorem conditional_variance_angular_poincare (n : Nat) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K : Nat)
    (ids : List Nat) (hn : ids.Nodup) (hids : ∀ i, i ∈ ids → i < n)
    (W p : RatPoly) (hW : SupportedQuaternionBlocks n W) (P : Certificate n W)
    (hp : SupportedQuaternionBlocks (n+n) p)
    (inactive : ∀ i, i < n → i ∉ ids → QuaternionBlockIndependent i p)
    (hK : jointPoincareCutoff n w ids p ≤ K) :
    quaternionHaar n (polyMul W (determinant n (productHeat n w K ids) p)) ≤
      (1-w*w)*jointAngularEnergy n w K ids W p ids :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv (determinant_sweep_loss_pin n w K ids hn hids W p hW hp inactive))
    (joint_sweep_angular_poincare_at_cutoff n hw0 hw1 K ids hn hids W hW P p hp hK)

end YMGap.Continuum.SU2QuaternionProductHeatConditionalVariance

#print axioms YMGap.Continuum.SU2QuaternionProductHeatConditionalVariance.product_conditional_unit
#print axioms YMGap.Continuum.SU2QuaternionProductHeatConditionalVariance.sweep_all_lower_independent
#print axioms YMGap.Continuum.SU2QuaternionProductHeatConditionalVariance.joint_sweep_square_mean_pin
#print axioms YMGap.Continuum.SU2QuaternionProductHeatConditionalVariance.determinant_sweep_loss_pin
#print axioms YMGap.Continuum.SU2QuaternionProductHeatConditionalVariance.conditional_variance_angular_poincare
