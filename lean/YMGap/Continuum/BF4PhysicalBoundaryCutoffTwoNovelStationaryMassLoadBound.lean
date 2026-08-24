/-
# Retain the novel stationary mass in the fixed-edge load bound

The shell-linear bound discarded how little stationary probability may sit on
novel endpoints.  This module retains that factor.  Define the novel endpoint
mass as the stationary-product sum over the exact novel ordered-pair list.
Then every fixed directed-edge load is bounded by

  carrierLength * novelEndpointMass.

The mass is exactly the sum of the new--new and two directed cross products,
and it is zero at cutoff two.  Thus the refined analytic bound responds to
probability in the new shell, not merely to the number of new states.

No cofinal decay estimate for the novel stationary mass, comparison with the
positive-edge floor, completed contraction, thermodynamic/continuum
construction, or Clay mass gap is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellEdgeFloorPayment

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassLoadBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The exact stationary mass of novel endpoint pairs -/

def cutoffTwoNovelEndpointWeightMass (later : Nat) : Q' :=
  listQSum
    (fun pair =>
      cutoffTwoEdgeLoadWeight later pair.1 *
        cutoffTwoEdgeLoadWeight later pair.2)
    (cutoffTwoNovelEndpointPairs later)

theorem cutoffTwoNovelEndpointWeightMass_eqv_newNew_add_cross
    (later : Nat) :
    cutoffTwoNovelEndpointWeightMass later ≈
      cutoffTwoNewMass later * cutoffTwoNewMass later +
        (cutoffTwoOldMass later * cutoffTwoNewMass later +
          cutoffTwoNewMass later * cutoffTwoOldMass later) := by
  let entry : Nat × Nat → Q' := fun pair =>
    cutoffTwoEdgeLoadWeight later pair.1 *
      cutoffTwoEdgeLoadWeight later pair.2
  unfold cutoffTwoNovelEndpointWeightMass cutoffTwoNovelEndpointPairs
  refine Q'.eqv_trans _
    (listQSum entry
        (cartesian
          (cutoffTwoEdgeLoadNewStates later)
          (cutoffTwoEdgeLoadNewStates later)) +
      (listQSum entry
          (cartesian
            (cutoffTwoEdgeLoadOldStates later)
            (cutoffTwoEdgeLoadNewStates later)) +
        listQSum entry
          (cartesian
            (cutoffTwoEdgeLoadNewStates later)
            (cutoffTwoEdgeLoadOldStates later)))) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum entry
          (cartesian
            (cutoffTwoEdgeLoadNewStates later)
            (cutoffTwoEdgeLoadNewStates later)) +
        listQSum entry
          (cutoffTwoCanonicalCrossEndpointPairs later)) _
      (listQSum_append _ _ _) ?_
    unfold cutoffTwoCanonicalCrossEndpointPairs
    exact Q'.add_eqv_congr_left _ _ _ (listQSum_append _ _ _)
  · dsimp only [entry]
    unfold cutoffTwoOldMass cutoffTwoNewMass finiteWeightedMass
      cutoffTwoEdgeLoadWeight cutoffTwoEdgeLoadOldStates
      cutoffTwoEdgeLoadNewStates
    exact Q'.add_eqv_congr'
      (listQSum_cartesian_product _ _ _ _)
      (Q'.add_eqv_congr'
        (listQSum_cartesian_product _ _ _ _)
        (listQSum_cartesian_product _ _ _ _))

theorem cutoffTwoNovelEndpointWeightMass_nonnegative (later : Nat) :
    (0 : Q') ≤ cutoffTwoNovelEndpointWeightMass later := by
  unfold cutoffTwoNovelEndpointWeightMass
  apply listQSum_nonnegative_on
  intro pair _hpair
  exact Q'.mul_nonneg _ _
    (BF4SU2FixedMagneticPhysicalMarkov.centralPhysicalRowMarginal_nonnegative
      (by decide) later 0 _)
    (BF4SU2FixedMagneticPhysicalMarkov.centralPhysicalRowMarginal_nonnegative
      (by decide) later 0 _)

theorem cutoffTwoNovelEndpointWeightMass_self_eqv_zero :
    cutoffTwoNovelEndpointWeightMass 2 ≈ 0 := by
  unfold cutoffTwoNovelEndpointWeightMass
  rw [cutoffTwoNovelEndpointPairs_self]
  exact Q'.eqv_refl 0

/-! ## 2. The mass-refined fixed-edge load bound -/

theorem cutoffTwoNovelPathLoadSum_le_sizeWeightedPairSum
    (later source target : Nat) :
    listQSum
        (fun pair => weightedDirectedEdgeLoad
          (cutoffTwoSimpleWeightedPathOccurrences
            later pair.1 pair.2) source target)
        (cutoffTwoNovelEndpointPairs later) ≤
      listQSum
        (fun pair =>
          Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length *
            (cutoffTwoEdgeLoadWeight later pair.1 *
              cutoffTwoEdgeLoadWeight later pair.2))
        (cutoffTwoNovelEndpointPairs later) := by
  apply listQSum_mono
  intro pair hpair
  have hfull := cutoffTwoNovelEndpointPair_mem_full hpair
  have hpath :=
    cutoffTwoSimpleWeightedPathEdgeLoad_le_pairWeight_mul_sectorSize
      later pair.1 pair.2 source target hfull.1 hfull.2
  exact Q'.le_trans' _ _ _ hpath
    (Q'.le_of_eqv
      (Q'.mul_comm_eqv
        (cutoffTwoEdgeLoadWeight later pair.1 *
          cutoffTwoEdgeLoadWeight later pair.2)
        (Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length)))

theorem cutoffTwoNovelSizeWeightedPairSum_eqv_size_mul_mass
    (later : Nat) :
    listQSum
        (fun pair =>
          Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length *
            (cutoffTwoEdgeLoadWeight later pair.1 *
              cutoffTwoEdgeLoadWeight later pair.2))
        (cutoffTwoNovelEndpointPairs later) ≈
      Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length *
        cutoffTwoNovelEndpointWeightMass later := by
  let sizeQ := Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length
  let pairWeight : Nat × Nat → Q' := fun pair =>
    cutoffTwoEdgeLoadWeight later pair.1 *
      cutoffTwoEdgeLoadWeight later pair.2
  let pairs := cutoffTwoNovelEndpointPairs later
  unfold cutoffTwoNovelEndpointWeightMass
  change listQSum (fun pair => sizeQ * pairWeight pair) pairs ≈
    sizeQ * listQSum pairWeight pairs
  exact FiniteDeterministicKernelPushforward.listQSum_mul_left
    sizeQ pairWeight pairs

theorem cutoffTwoNovelSimpleEdgeLoad_le_size_mul_endpointMass
    (later source target : Nat) :
    cutoffTwoNovelSimpleEdgeLoad later source target ≤
      Q'.ofNat (cutoffTwoEdgeLoadFullStates later).length *
        cutoffTwoNovelEndpointWeightMass later := by
  let pathLoad : Nat × Nat → Q' := fun pair =>
    weightedDirectedEdgeLoad
      (cutoffTwoSimpleWeightedPathOccurrences later pair.1 pair.2)
      source target
  have hregroup : cutoffTwoNovelSimpleEdgeLoad later source target ≈
      listQSum pathLoad (cutoffTwoNovelEndpointPairs later) := by
    unfold cutoffTwoNovelSimpleEdgeLoad
      cutoffTwoNovelSimpleWeightedEdgeOccurrences pathLoad
    exact weightedDirectedEdgeLoad_flatMap_eqv
      (cutoffTwoNovelEndpointPairs later)
      (fun pair => cutoffTwoSimpleWeightedPathOccurrences
        later pair.1 pair.2) source target
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
    (Q'.le_trans' _ _ _
      (cutoffTwoNovelPathLoadSum_le_sizeWeightedPairSum
        later source target)
      (Q'.le_of_eqv
        (cutoffTwoNovelSizeWeightedPairSum_eqv_size_mul_mass later)))

theorem cutoffTwoNovelSimpleEdgeLoad_le_shellSize_mul_endpointMass
    {later : Nat} (hcutoff : 2 ≤ later)
    (source target : Nat) :
    cutoffTwoNovelSimpleEdgeLoad later source target ≤
      Q'.ofNat (65 + (cutoffTwoEdgeLoadNewStates later).length) *
        cutoffTwoNovelEndpointWeightMass later := by
  have hload := cutoffTwoNovelSimpleEdgeLoad_le_size_mul_endpointMass
    later source target
  rw [BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding.cutoffTwoEdgeLoadFullStates_length_eq_65_add_new
    hcutoff] at hload
  exact hload

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassLoadBound

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassLoadBound.cutoffTwoNovelEndpointWeightMass_eqv_newNew_add_cross
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassLoadBound.cutoffTwoNovelEndpointWeightMass_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassLoadBound.cutoffTwoNovelEndpointWeightMass_self_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassLoadBound.cutoffTwoNovelPathLoadSum_le_sizeWeightedPairSum
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassLoadBound.cutoffTwoNovelSimpleEdgeLoad_le_size_mul_endpointMass
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassLoadBound.cutoffTwoNovelSimpleEdgeLoad_le_shellSize_mul_endpointMass
