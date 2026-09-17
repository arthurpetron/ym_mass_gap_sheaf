/-
# Exact active-seed and grouped-fringe split

Zero the supplied seeds outside the ORIGINAL active kinetic list. Active
residual tests are unchanged, while inactive tests vanish coefficientwise.
The corrected sum from these seeds, plus the whole original fringe residual
sum, is coefficient-equivalent to the original full corrected sum.

The same marginal nu, finite reciprocal degrees and all active heat factors
are retained. These are exact finite polynomial identities, not a bound on
the active signed cost, a completed OS-kernel assertion or a continuum gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyErasure (labels)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyMarginals (residualTests)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyCost (corrected correctedSum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel (fringeSum)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra (project_congr)
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering (weightedResidual)

local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks activeBlocks

/-- Keep exactly the seeds at original active kinetic coordinates. -/
def activeSeeds (width : Nat) (seeds : Nat → RatPoly) (i : Nat) : RatPoly :=
  if i ∈ activeBlocks width then seeds i else polyZero

theorem activeSeeds_active (width : Nat) (seeds : Nat → RatPoly) (i : Nat)
    (hi : i ∈ activeBlocks width) : activeSeeds width seeds i = seeds i := by
  unfold activeSeeds
  rw [if_pos hi]

theorem activeSeeds_inactive (width : Nat) (seeds : Nat → RatPoly) (i : Nat)
    (hi : i ∉ activeBlocks width) : activeSeeds width seeds i = polyZero := by
  unfold activeSeeds
  rw [if_neg hi]

theorem activeSeeds_supported (width : Nat) (seeds : Nat → RatPoly)
    (hs : ∀ i, i < N width → SupportedQuaternionBlocks (N width) (seeds i))
    (i : Nat) (hi : i < N width) :
    SupportedQuaternionBlocks (N width) (activeSeeds width seeds i) := by
  by_cases ha : i ∈ activeBlocks width
  · rw [activeSeeds_active width seeds i ha]
    exact hs i hi
  · rw [activeSeeds_inactive width seeds i ha]
    intro t ht
    cases ht

/-- A zero seed gives a zero residual in the coefficient quotient. -/
theorem weightedResidual_zero (i : Nat) (a : RatPoly) :
    RatPolyCoeffEqv (weightedResidual i a polyZero) polyZero := by
  have hp : RatPolyCoeffEqv (project i (polyMul a polyZero)) polyZero :=
    project_congr i (RatPolyCoeffEqv.mul_zero_right a)
  exact ((RatPolyCoeffEqv.mul_zero_right (project i a)).add
    (RatPolyCoeffEqv.neg hp)).trans (RatPolyCoeffEqv.add_zero polyZero)

private theorem sum_congr (f g : Nat → RatPoly) : ∀ ids : List Nat,
    (∀ i, i ∈ ids → RatPolyCoeffEqv (f i) (g i)) →
      RatPolyCoeffEqv (polySum (ids.map f)) (polySum (ids.map g))
  | [], _ => .refl _
  | i::ids, h => (h i List.mem_cons_self).add
      (sum_congr f g ids (fun j hj => h j (List.mem_cons_of_mem i hj)))

private theorem sum_zero (f : Nat → RatPoly) : ∀ ids : List Nat,
    (∀ i, i ∈ ids → RatPolyCoeffEqv (f i) polyZero) →
      RatPolyCoeffEqv (polySum (ids.map f)) polyZero
  | [], _ => .refl _
  | i::ids, h => ((h i List.mem_cons_self).add
      (sum_zero f ids (fun j hj => h j (List.mem_cons_of_mem i hj)))).trans
        (RatPolyCoeffEqv.add_zero polyZero)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat)

theorem residualTests_active (seeds : Nat → RatPoly) (degrees : Nat → Nat)
    (i : Nat) (hi : i ∈ activeBlocks width) :
    residualTests hw0 hw1 K width hK n (activeSeeds width seeds) degrees i =
      residualTests hw0 hw1 K width hK n seeds degrees i := by
  unfold residualTests
  rw [activeSeeds_active width seeds i hi]

theorem residualTests_inactive (seeds : Nat → RatPoly) (degrees : Nat → Nat)
    (i : Nat) (hi : i ∉ activeBlocks width) :
    RatPolyCoeffEqv
      (residualTests hw0 hw1 K width hK n (activeSeeds width seeds) degrees i) polyZero := by
  simp only [residualTests, activeSeeds, if_neg hi]
  exact weightedResidual_zero i _

theorem corrected_active (seeds : Nat → RatPoly) (degrees : Nat → Nat)
    (i : Nat) (hi : i ∈ activeBlocks width) :
    corrected hw0 hw1 K width hK n
        (fun j => weightedResidual j (marginalWeight w K width n) (activeSeeds width seeds j)) degrees i =
      corrected hw0 hw1 K width hK n
        (fun j => weightedResidual j (marginalWeight w K width n) (seeds j)) degrees i := by
  simp only [corrected, activeSeeds, if_pos hi]

theorem corrected_inactive (seeds : Nat → RatPoly) (degrees : Nat → Nat)
    (i : Nat) (hi : i ∉ activeBlocks width) :
    RatPolyCoeffEqv
      (corrected hw0 hw1 K width hK n
        (fun j => weightedResidual j (marginalWeight w K width n) (activeSeeds width seeds j)) degrees i)
      polyZero := by
  simp only [corrected, activeSeeds, if_neg hi]
  exact weightedResidual_zero i _

/-- Active-only seeds remove the inactive summands, not their heat factors. -/
theorem correctedSum_active (seeds : Nat → RatPoly) (degrees : Nat → Nat) :
    RatPolyCoeffEqv
      (correctedSum hw0 hw1 K width hK n
        (fun i => weightedResidual i (marginalWeight w K width n) (activeSeeds width seeds i)) degrees)
      (polySum ((activeBlocks width).map
        (corrected hw0 hw1 K width hK n
          (fun i => weightedResidual i (marginalWeight w K width n) (seeds i)) degrees))) := by
  let ca := corrected hw0 hw1 K width hK n
    (fun i => weightedResidual i (marginalWeight w K width n) (activeSeeds width seeds i)) degrees
  let c := corrected hw0 hw1 K width hK n
    (fun i => weightedResidual i (marginalWeight w K width n) (seeds i)) degrees
  change RatPolyCoeffEqv (polySum ((labels width).map ca)) (polySum ((activeBlocks width).map c))
  rw [labels, List.map_append]
  refine (RatPolyCoeffEqv.polySum_append _ _).symm.trans ?_
  have ha := sum_congr ca c (activeBlocks width) (fun i hi => by
    rw [show ca i = c i from corrected_active hw0 hw1 K width hK n seeds degrees i hi]
    exact RatPolyCoeffEqv.refl _)
  have hf := sum_zero ca (fringeBlocks width) (fun i hi =>
    corrected_inactive hw0 hw1 K width hK n seeds degrees i ((fringeBlocks_mem_iff width i).mp hi).2)
  exact (ha.add hf).trans (RatPolyCoeffEqv.add_zero _)

/-- The grouped fringe restores precisely the ORIGINAL full corrected sum. -/
theorem correctedSum_split (seeds : Nat → RatPoly) (degrees : Nat → Nat) :
    RatPolyCoeffEqv
      (polyAdd
        (correctedSum hw0 hw1 K width hK n
          (fun i => weightedResidual i (marginalWeight w K width n) (activeSeeds width seeds i)) degrees)
        (fringeSum w K width n seeds))
      (correctedSum hw0 hw1 K width hK n
        (fun i => weightedResidual i (marginalWeight w K width n) (seeds i)) degrees) := by
  let c := corrected hw0 hw1 K width hK n
    (fun i => weightedResidual i (marginalWeight w K width n) (seeds i)) degrees
  have hf : RatPolyCoeffEqv (polySum ((fringeBlocks width).map c)) (fringeSum w K width n seeds) := by
    apply sum_congr c (fun i => weightedResidual i (marginalWeight w K width n) (seeds i))
    intro i hi
    have hnot := ((fringeBlocks_mem_iff width i).mp hi).2
    change RatPolyCoeffEqv (corrected hw0 hw1 K width hK n
      (fun j => weightedResidual j (marginalWeight w K width n) (seeds j)) degrees i) _
    simp only [corrected, if_neg hnot]
    exact RatPolyCoeffEqv.refl _
  have hs : RatPolyCoeffEqv
      (correctedSum hw0 hw1 K width hK n
        (fun i => weightedResidual i (marginalWeight w K width n) (seeds i)) degrees)
      (polyAdd (polySum ((activeBlocks width).map c)) (fringeSum w K width n seeds)) := by
    change RatPolyCoeffEqv (polySum ((labels width).map c)) _
    rw [labels, List.map_append]
    exact (RatPolyCoeffEqv.polySum_append _ _).symm.trans ((RatPolyCoeffEqv.refl _).add hf)
  exact ((correctedSum_active hw0 hw1 K width hK n seeds degrees).add
    (RatPolyCoeffEqv.refl _)).trans hs.symm

end YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds.activeSeeds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds.activeSeeds_active
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds.activeSeeds_inactive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds.activeSeeds_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds.weightedResidual_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds.residualTests_active
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds.residualTests_inactive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds.corrected_active
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds.corrected_inactive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds.correctedSum_active
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialActiveSeeds.correctedSum_split
