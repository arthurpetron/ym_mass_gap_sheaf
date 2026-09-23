/-
# The actual product heat operator as a fresh-output cyclic sweep

A step adjoins its output at block `n`, integrates source block zero, and
deletes that source block. On an n-block input the survivors again form an
n-block carrier, ordered as the remaining sources followed by produced
outputs. After n steps their order is the original upper-slice order.

The prefix invariant uses n+m variables, not a fixed doubled carrier: after
m source integrations it leaves n variables. At m=n it is exactly the
existing `productMap` on the fully active list. No selected-link/head-map
certificate, independence of an existing neighbor, or analytic bound is
assumed. Every right insertion is retained by Haar-carrier equality.

This is an operator identity, not the angular defect estimate. In particular
the cyclic coordinate rotation does NOT make each intermediate map positive
or self-adjoint. The commuting local-smoothing estimate, inactive-link
residuals for proper active subsets, signed interacting correction, and
physical OS/scaling/continuum joins remain open.
-/

import YMGap.Continuum.SU2QuaternionProductHeatPrefix
import YMGap.Continuum.SU2QuaternionHaarCertificateIntegration

namespace YMGap.Continuum.SU2QuaternionProductHeatCyclicFold

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpoint
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHeadLinearHaar
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionHaarCertificateIntegration
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionFullHeatTubeVacuum
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatPrefix
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Smooth the first source against a fresh LAST block, then remove the
integrated source. This rotates the n-block window by one position. -/
def cycleStep (n : Nat) (w : Q') (K : Nat) (p : RatPoly) : RatPoly :=
  partialHaarHead (polyMul (heatAt 0 n w K) p)

/-- Actual composition of the computed polynomial maps, not an assumed
realization or an operator selected from a certificate. -/
def cycleIterate (n : Nat) (w : Q') (K : Nat) : Nat → RatPoly → RatPoly
  | 0, p => p
  | m+1, p => cycleIterate n w K m (cycleStep n w K p)

theorem cycleStep_supported (n : Nat) (w : Q') (K : Nat) {p : RatPoly}
    (hp : SupportedQuaternionBlocks n p) :
    SupportedQuaternionBlocks n (cycleStep n w K p) := by
  apply partialHaarHead_supported (blocks := n)
  exact supported_polyMul (heat_supported (by omega) (by omega) w K)
    (fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (by omega)))

theorem cycleIterate_supported (n : Nat) (w : Q') (K : Nat) :
    ∀ (m : Nat) (p : RatPoly), SupportedQuaternionBlocks n p →
      SupportedQuaternionBlocks n (cycleIterate n w K m p)
  | 0, _, hp => hp
  | m+1, _, hp => cycleIterate_supported n w K m _
      (cycleStep_supported n w K hp)

/-- The fresh output is genuinely unused by the input. Its heat marginal
therefore preserves the original mean, at every finite heat cutoff. -/
theorem cycleStep_mean (n : Nat) (hn : 0 < n) (w : Q') (K : Nat)
    {p : RatPoly} (hp : SupportedQuaternionBlocks n p) :
    quaternionHaar n (cycleStep n w K p) ≈ quaternionHaar n p := by
  have hp' : SupportedQuaternionBlocks (n+1) p :=
    fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 (by omega))
  have hd := independent_has_degree_zero (supported_upper_independent hp 0)
  have hv := pair_vacuum n hn ⟨n, by omega⟩ ⟨0, by omega⟩ (by
      change n ≠ 0
      omega) w K p hp' (by simpa only [Nat.add_zero] using hd)
  exact Q'.eqv_trans _ _ _ (quaternionHaar_partialHaarHead n _)
    (Q'.eqv_trans _ _ _ (haar_of_coeff ((heatAt_symm 0 n w K).mul_right p))
      (Q'.eqv_trans _ _ _ hv
        (quaternionHaar_extend_supported_endpoint (by omega : n ≤ n+1) p hp)))

theorem cycleIterate_mean (n : Nat) (hn : 0 < n) (w : Q') (K : Nat) :
    ∀ (m : Nat) (p : RatPoly), SupportedQuaternionBlocks n p →
      quaternionHaar n (cycleIterate n w K m p) ≈ quaternionHaar n p
  | 0, _, _ => Q'.eqv_refl _
  | m+1, _, hp => Q'.eqv_trans _ _ _
      (cycleIterate_mean n hn w K m _ (cycleStep_supported n w K hp))
      (cycleStep_mean n hn w K hp)

/-- One Fubini step with every remaining heat factor still present. -/
private theorem prefix_step (n : Nat) (w : Q') (K m : Nat) (p : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads (m+1)
        (polyMul (polyMul (heatAt 0 n w K)
          (liftHead (productHeat n w K (List.range m)))) p))
      (partialHaarHeads m
        (polyMul (productHeat n w K (List.range m)) (cycleStep n w K p))) := by
  let A := heatAt 0 n w K
  let B := productHeat n w K (List.range m)
  have hr : RatPolyCoeffEqv (polyMul (polyMul A (liftHead B)) p)
      (polyMul (polyMul A p) (liftHead B)) :=
    (RatPolyCoeffEqv.mul_assoc A (liftHead B) p).trans
      (((RatPolyCoeffEqv.mul_comm (liftHead B) p).mul_left A).trans
        (RatPolyCoeffEqv.mul_assoc A p (liftHead B)).symm)
  exact partialHaarHeads_congr m
    ((partialHaarHead_congr hr).trans
      ((partialHaarHead_mul_lift (polyMul A p) B).trans
        (RatPolyCoeffEqv.mul_comm _ B)))

/-- Prefix invariant on n+m variables. No support premise is needed for
this insertion-preserving algebraic identity; the support theorem above
separately establishes that supported inputs stay on the n-block window. -/
theorem productHeat_prefix_fold_carrier (n : Nat) (w : Q') (K : Nat) :
    ∀ (m : Nat) (p : RatPoly),
      HaarCarrierEqv n
        (partialHaarHeads m
          (polyMul (productHeat n w K (List.range m)) p))
        (cycleIterate n w K m p)
  | 0, p => RatPolyCoeffEqv.haarCarrier (RatPolyCoeffEqv.one_mul p)
  | m+1, p => by
      have hkernel := HaarCarrierEqv.mul_right p
        (productHeat_prefix_succ_carrier n w K m)
      have hhead := partialHaarHeads_carrier (tailBlocks := n)
        (headBlocks := m+1) hkernel
      exact HaarCarrierEqv.trans hhead (HaarCarrierEqv.trans
        (RatPolyCoeffEqv.haarCarrier (prefix_step n w K m p))
        (productHeat_prefix_fold_carrier n w K m (cycleStep n w K p)))

/-- The fully active original product operator is exactly n fresh-output
steps, with its original output ordering and ALL insertion tests. -/
theorem productMap_range_cycle_carrier (n : Nat) (w : Q') (K : Nat)
    (p : RatPoly) :
    HaarCarrierEqv n (productMap n w K (List.range n) p)
      (cycleIterate n w K n p) :=
  productHeat_prefix_fold_carrier n w K n p

/-- Exact endpoint pairing, including arbitrary signed tests. -/
theorem productMap_range_cycle_pairing (n : Nat) (w : Q') (K : Nat)
    (p test : RatPoly) :
    quaternionHaar n (polyMul test (productMap n w K (List.range n) p)) ≈
      quaternionHaar n (polyMul test (cycleIterate n w K n p)) :=
  productMap_range_cycle_carrier n w K p test

/-- The actual quadratic defect can be computed from the cyclic endpoint.
No sign is assigned to intermediate steps or their cross terms. -/
theorem productMap_range_cycle_defect (n : Nat) (w : Q') (K : Nat)
    (p : RatPoly) :
    quaternionHaar n (polyMul p p) -
        quaternionHaar n (polyMul p (productMap n w K (List.range n) p)) ≈
      quaternionHaar n (polyMul p p) -
        quaternionHaar n (polyMul p (cycleIterate n w K n p)) :=
  Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.neg_eqv_congr _ _ (productMap_range_cycle_pairing n w K p p))

end YMGap.Continuum.SU2QuaternionProductHeatCyclicFold

#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicFold.cycleStep
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicFold.cycleIterate
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicFold.cycleStep_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicFold.cycleIterate_supported
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicFold.cycleStep_mean
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicFold.cycleIterate_mean
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicFold.productHeat_prefix_fold_carrier
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicFold.productMap_range_cycle_carrier
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicFold.productMap_range_cycle_pairing
#print axioms YMGap.Continuum.SU2QuaternionProductHeatCyclicFold.productMap_range_cycle_defect
