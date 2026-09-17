/-
# The entire actual fringe residual sum is one transfer-kernel test

Every inactive-coordinate residual is centered in a=V*T^n1. The missing
kinetic factor annihilates it under arbitrary Haar testing. Linearity
retains this property for the full signed fringe sum. Its exact edge-jump
pairing is twice the SAME odd-marginal pairing, so one Cauchy--Schwarz
estimate charges the norm of the entire sum, not the sum of its norms.

This removes an artificial componentwise fringe cost. The active part
and its interaction with this sum still need stable control. No completed
OS-kernel identification, uniform full-sector gap or continuum claim.
-/

import YMGap.Continuum.SU2QuaternionAbsentHeatFamily
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported terminalMessage_certificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
  (edgeDensity energy energy_identity edgeCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalWeight_supported marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual
  (terminal_product fringeResidual_centered)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure (labels)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost (corrected correctedSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeedFamily
  (sum_supported familySeeds familySeeds_supported familyTests)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap productMap_congr)
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (edgeWeight)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported)
open YMGap.Continuum.SU2QuaternionAbsentHeatFamily
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] spatialWeight baseLinks kineticWeight

private theorem full_edge (w : Q') (K width n : Nat) :
    edgeWeight (N width) w K (activeBlocks width)
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) =
      edgeDensity w K width (terminalMessage w K width n) := by
  unfold edgeWeight edgeDensity
  rw [kineticWeight_eq_indexedProduct]
  rfl

private theorem transfer_product (w : Q') (K width : Nat) (f : RatPoly) :
    transferStep w K width f = productMap (N width) w K (activeBlocks width)
      (polyMul (spatialWeight w K width) f) := by
  unfold transferStep step productMap kernelMap
  rw [kineticWeight_eq_indexedProduct]
  rfl

private theorem cancel_two {x y : Q'} (h : (2 : Q')*x ≈ (2 : Q')*y) : x ≈ y := by
  have hh (z : Q') : HalfPow.half*((2 : Q')*z) ≈ z :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ z (by decide : HalfPow.half*(2 : Q') ≈ 1))
        (Q'.one_mul_eqv z))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (hh x))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left HalfPow.half _ _ h) (hh y))

def fringeSum (w : Q') (K width n : Nat) (seeds : Nat → RatPoly) : RatPoly :=
  polySum ((fringeBlocks width).map (fun i => weightedResidual i (marginalWeight w K width n) (seeds i)))

theorem fringeSum_supported (w : Q') (K width n : Nat) (seeds : Nat → RatPoly)
    (hs : ∀ i, i ∈ fringeBlocks width → SupportedQuaternionBlocks (N width) (seeds i)) :
    SupportedQuaternionBlocks (N width) (fringeSum w K width n seeds) :=
  sum_supported _ _ (fun i hi => weightedResidual_supported i (marginalWeight_supported w K width n) (hs i hi))

/-- Actual weighted transfer annihilation under EVERY Haar test. This does
not assert raw coefficient equality of the transferred polynomial. -/
theorem fringeSum_transfer_pair_zero (w : Q') (K width n : Nat)
    (seeds : Nat → RatPoly) (p : RatPoly) :
    quaternionHaar (N width) (polyMul p (transferStep w K width
      (polyMul (terminalMessage w K width n) (fringeSum w K width n seeds)))) ≈ 0 := by
  rw [transfer_product]
  have he := productMap_congr (N width) w K (activeBlocks width)
    (RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) (terminalMessage w K width n)
      (fringeSum w K width n seeds)).symm
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (he.mul_left p))
    (absent_sum_pair_zero (N width) w K (activeBlocks width) (activeBlocks_lt width)
      (polyMul (spatialWeight w K width) (terminalMessage w K width n))
      (fun i => weightedResidual i (marginalWeight w K width n) (seeds i)) (fringeBlocks width)
      (fun i hi => ((fringeBlocks_mem_iff width i).mp hi).1)
      (fun i hi => ((fringeBlocks_mem_iff width i).mp hi).2)
      (fun i hi => fringeResidual_centered w K width n i
        ((fringeBlocks_mem_iff width i).mp hi).1 ((fringeBlocks_mem_iff width i).mp hi).2 (seeds i)) p)

theorem fringeSum_jump_pairing (w : Q') (K width n : Nat)
    (seeds : Nat → RatPoly)
    (hs : ∀ i, i ∈ fringeBlocks width → SupportedQuaternionBlocks (N width) (seeds i))
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    weightedPair (N width+N width) (edgeDensity w K width (terminalMessage w K width n))
      (jump (N width) f) (jump (N width) (fringeSum w K width n seeds)) ≈
      (2 : Q')*marginalPair w K width n f (fringeSum w K width n seeds) := by
  have h := absent_sum_jump_pairing (N width) w K (activeBlocks width) (activeBlocks_lt width)
    (polyMul (spatialWeight w K width) (terminalMessage w K width n))
    (fun i => weightedResidual i (marginalWeight w K width n) (seeds i)) (fringeBlocks width)
    (fun i hi => ((fringeBlocks_mem_iff width i).mp hi).1)
    (fun i hi => ((fringeBlocks_mem_iff width i).mp hi).2)
    (fun i hi => fringeResidual_centered w K width n i
      ((fringeBlocks_mem_iff width i).mp hi).1 ((fringeBlocks_mem_iff width i).mp hi).2 (seeds i)) f
    (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n)) hf
    (fun i hi => weightedResidual_supported i (marginalWeight_supported w K width n) (hs i hi))
  rw [full_edge] at h
  unfold SU2QuaternionWeightedProductDualEnergy.marginalPair at h
  rw [← terminal_product] at h
  exact h

/-- The entire signed fringe sum has energy exactly equal to its original
marginal norm. No sum of component norms or number-of-links factor. -/
theorem fringeSum_energy_eq (w : Q') (K width n : Nat) (seeds : Nat → RatPoly)
    (hs : ∀ i, i ∈ fringeBlocks width → SupportedQuaternionBlocks (N width) (seeds i)) :
    energy w K width (terminalMessage w K width n) (fringeSum w K width n seeds) ≈
      marginalPair w K width n (fringeSum w K width n seeds) (fringeSum w K width n seeds) := by
  have hr := fringeSum_supported w K width n seeds hs
  apply cancel_two
  exact Q'.eqv_trans _ _ _ (energy_identity w K width (terminalMessage_supported w K width n) hr)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (fringeSum_jump_pairing w K width n seeds hs hr))

/-- One Cauchy--Schwarz inequality pays the WHOLE fringe test, preserving
all signed fringe cross terms inside its actual squared norm. -/
theorem fringeSum_dual_energy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (seeds : Nat → RatPoly)
    (hs : ∀ i, i ∈ fringeBlocks width → SupportedQuaternionBlocks (N width) (seeds i))
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    let r := fringeSum w K width n seeds
    marginalPair w K width n f r * marginalPair w K width n f r ≤
      energy w K width (terminalMessage w K width n) f * marginalPair w K width n r r := by
  let r := fringeSum w K width n seeds
  let e := edgeDensity w K width (terminalMessage w K width n)
  have hr := fringeSum_supported w K width n seeds hs
  have hc := fringeSum_jump_pairing w K width n seeds hs hf
  have hd := fringeSum_jump_pairing w K width n seeds hs hr
  have hj : weightedPair (N width+N width) e (jump (N width) f) (jump (N width) f) ≈
      (2 : Q')*energy w K width (terminalMessage w K width n) f :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_symm (energy_identity w K width (terminalMessage_supported w K width n) hf))
  have hcs := weighted_cauchySchwarz (N width+N width) e (jump (N width) f) (jump (N width) r)
    (edgeCertificate hw0 hw1 K width hK (terminalMessage_supported w K width n)
      (terminalMessage_certificate hw0 hw1 K width hK n)) (jump_supported hf) (jump_supported hr)
  have he := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hc)
      (Q'.mul_eqv_congr_left _ _ _ hc)))
    (Q'.le_trans' _ _ _ hcs
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hj)
        (Q'.mul_eqv_congr_left _ _ _ hd))))
  have factor (x y : Q') : ((2 : Q')*x)*((2 : Q')*y) ≈ (4 : Q')*(x*y) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1)))
      (.mul (.const 4) (.mul (.var 0) (.var 1))) (by decide) (fun | 0 => x | _ => y)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (factor _ _))
      (Q'.le_trans' _ _ _ he (Q'.le_of_eqv (factor _ _)))) (by decide : (0 : Q') < (4 : Q'))

/-- The already constructed approximation seeds require no new centering
input to enter the grouped coefficient-one estimate. -/
theorem actualFamily_fringe_dual_energy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n k : Nat)
    {f : RatPoly} (hf : SupportedQuaternionBlocks (N width) f) :
    let r := fringeSum w K width n (familySeeds hw0 hw1 K width hK n k f)
    marginalPair w K width n f r * marginalPair w K width n f r ≤
      energy w K width (terminalMessage w K width n) f * marginalPair w K width n r r :=
  fringeSum_dual_energy hw0 hw1 K width hK n (familySeeds hw0 hw1 K width hK n k f)
    (fun i _ => familySeeds_supported hw0 hw1 K width hK n k i hf) hf

/-- The grouped fringe is literally the inactive part of the existing
corrected sum. The active part and every correction degree are unchanged. -/
theorem correctedSum_partition {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)
    (seeds : Nat → RatPoly) (degrees : Nat → Nat) :
    let qs := fun i => weightedResidual i (marginalWeight w K width n) (seeds i)
    RatPolyCoeffEqv (correctedSum hw0 hw1 K width hK n qs degrees)
      (polyAdd (polySum ((activeBlocks width).map (corrected hw0 hw1 K width hK n qs degrees)))
        (fringeSum w K width n seeds)) := by
  dsimp only
  let qs := fun i => weightedResidual i (marginalWeight w K width n) (seeds i)
  have he : (fringeBlocks width).map (corrected hw0 hw1 K width hK n qs degrees) =
      (fringeBlocks width).map qs := by
    apply List.map_congr_left
    intro i hi
    exact if_neg (((fringeBlocks_mem_iff width i).mp hi).2)
  unfold correctedSum labels
  rw [List.map_append]
  exact (RatPolyCoeffEqv.polySum_append _ _).symm.trans
    ((RatPolyCoeffEqv.refl _).add (by rw [he]; exact .refl _))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel.fringeSum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel.fringeSum_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel.fringeSum_transfer_pair_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel.fringeSum_jump_pairing
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel.fringeSum_energy_eq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel.fringeSum_dual_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel.actualFamily_fringe_dual_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel.correctedSum_partition
