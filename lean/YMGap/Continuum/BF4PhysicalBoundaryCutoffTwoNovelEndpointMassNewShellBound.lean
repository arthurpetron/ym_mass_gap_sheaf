/-
# Bound novel endpoint mass by new-shell stationary mass

The old and new cutoff-two blocks partition the later canonical vacuum
sector.  Their stationary masses are nonnegative and add exactly to the full
sector mass, which is at most one.  Combining this with the exact novel-pair
decomposition gives

  novelEndpointMass <= 2 * newMass.

This removes the old-block mass from the open capacity payment.  It does not
prove decay of the new-shell mass, compare that decay with the positive-edge
floor, construct a thermodynamic/continuum limit, or prove the Clay mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassEdgeFloorPayment

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointMassNewShellBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelStationaryMassLoadBound
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullSectorCost
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The old/new masses form a nonnegative subprobability partition -/

theorem cutoffTwoOldMass_nonnegative (later : Nat) :
    (0 : Q') ≤ cutoffTwoOldMass later := by
  unfold cutoffTwoOldMass finiteWeightedMass
  apply listQSum_nonnegative_on
  intro index _hindex
  exact centralPhysicalRowMarginal_nonnegative (by decide) later 0 _

theorem cutoffTwoNewMass_nonnegative (later : Nat) :
    (0 : Q') ≤ cutoffTwoNewMass later := by
  unfold cutoffTwoNewMass finiteWeightedMass
  apply listQSum_nonnegative_on
  intro index _hindex
  exact centralPhysicalRowMarginal_nonnegative (by decide) later 0 _

theorem cutoffTwoOldMass_add_newMass_eqv_fullSectorMass (later : Nat) :
    cutoffTwoOldMass later + cutoffTwoNewMass later ≈
      centralPhysicalFiniteVacuumSectorMass
        cutoffTwoHalfCoupling (by decide) later 0 := by
  unfold cutoffTwoOldMass cutoffTwoNewMass
    centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
    centralPhysicalFiniteVacuumSectorOldBlockIndices
    centralPhysicalFiniteVacuumSectorNewBlockIndices
  exact Q'.eqv_symm
    (listQSum_filter_partition
      (centralPhysicalFiniteWeight
        cutoffTwoHalfCoupling (by decide) later 0)
      (centralPhysicalFiniteEmbeddedVacuumSectorB
        cutoffTwoHalfCoupling (by decide) 2 later 0)
      (centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) later 0))

theorem cutoffTwoOldMass_add_newMass_le_one (later : Nat) :
    cutoffTwoOldMass later + cutoffTwoNewMass later ≤ 1 :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (cutoffTwoOldMass_add_newMass_eqv_fullSectorMass later))
    (cutoffTwoFullSectorMass_le_one later)

theorem cutoffTwoOldMass_le_one (later : Nat) :
    cutoffTwoOldMass later ≤ 1 :=
  Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg
      (cutoffTwoOldMass later) (cutoffTwoNewMass later)
      (cutoffTwoNewMass_nonnegative later))
    (cutoffTwoOldMass_add_newMass_le_one later)

theorem cutoffTwoNewMass_le_one (later : Nat) :
    cutoffTwoNewMass later ≤ 1 := by
  have hle : cutoffTwoNewMass later ≤
      cutoffTwoNewMass later + cutoffTwoOldMass later :=
    Q'.add_le_self_of_nonneg
      (cutoffTwoNewMass later) (cutoffTwoOldMass later)
      (cutoffTwoOldMass_nonnegative later)
  exact Q'.le_trans' _ _ _ hle
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.add_comm_eqv
          (cutoffTwoNewMass later) (cutoffTwoOldMass later)))
      (cutoffTwoOldMass_add_newMass_le_one later))

/-! ## 2. Novel-pair mass is at most twice the new-shell mass -/

theorem cutoffTwoNovelEndpointWeightMass_le_newMass_add_newMass
    (later : Nat) :
    cutoffTwoNovelEndpointWeightMass later ≤
      cutoffTwoNewMass later + cutoffTwoNewMass later := by
  let oldMass := cutoffTwoOldMass later
  let newMass := cutoffTwoNewMass later
  have hold0 : (0 : Q') ≤ oldMass := cutoffTwoOldMass_nonnegative later
  have hnew0 : (0 : Q') ≤ newMass := cutoffTwoNewMass_nonnegative later
  have hsum1 : oldMass + newMass ≤ 1 :=
    cutoffTwoOldMass_add_newMass_le_one later
  have hold1 : oldMass ≤ 1 := cutoffTwoOldMass_le_one later
  have hfirstRaw : (oldMass + newMass) * newMass ≤ 1 * newMass :=
    Q'.mul_le_mul_of_nonneg_right _ _ newMass hsum1 hnew0
  have hfirst : (oldMass + newMass) * newMass ≤ newMass :=
    Q'.le_trans' _ _ _ hfirstRaw
      (Q'.le_of_eqv (Q'.one_mul_eqv newMass))
  have hsecondRaw : newMass * oldMass ≤ newMass * 1 :=
    Q'.mul_le_mul_of_nonneg_left oldMass 1 newMass hold1 hnew0
  have hsecond : newMass * oldMass ≤ newMass :=
    Q'.le_trans' _ _ _ hsecondRaw
      (Q'.le_of_eqv (Q'.mul_one_eqv newMass))
  have hregroup :
      cutoffTwoNovelEndpointWeightMass later ≈
        (oldMass + newMass) * newMass + newMass * oldMass := by
    refine Q'.eqv_trans _
      (newMass * newMass +
        (oldMass * newMass + newMass * oldMass)) _ ?_ ?_
    · exact cutoffTwoNovelEndpointWeightMass_eqv_newNew_add_cross later
    · ring_qeqv
  have hleft :
      (oldMass + newMass) * newMass + newMass * oldMass ≤
        newMass + newMass * oldMass :=
    Q'.add_le_add_right _ _ _ hfirst
  have hright : newMass + newMass * oldMass ≤
      newMass + newMass :=
    Q'.add_le_add_left _ _ _ hsecond
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
    (Q'.le_trans' _ _ _ hleft hright)

theorem cutoffTwoNovelEndpointWeightMass_le_two_mul_newMass
    (later : Nat) :
    cutoffTwoNovelEndpointWeightMass later ≤
      Q'.ofNat 2 * cutoffTwoNewMass later := by
  have htwo : Q'.ofNat 2 * cutoffTwoNewMass later ≈
      cutoffTwoNewMass later + cutoffTwoNewMass later := by
    refine Q'.eqv_trans _
      (((1 : Q') + 1) * cutoffTwoNewMass later) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    · refine Q'.eqv_trans _
        (1 * cutoffTwoNewMass later +
          1 * cutoffTwoNewMass later) _
        (Q'.add_mul_eqv 1 1 (cutoffTwoNewMass later)) ?_
      exact Q'.add_eqv_congr'
        (Q'.one_mul_eqv (cutoffTwoNewMass later))
        (Q'.one_mul_eqv (cutoffTwoNewMass later))
  exact Q'.le_trans' _
    (cutoffTwoNewMass later + cutoffTwoNewMass later) _
    (cutoffTwoNovelEndpointWeightMass_le_newMass_add_newMass later)
    (Q'.le_of_eqv (Q'.eqv_symm htwo))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointMassNewShellBound

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointMassNewShellBound.cutoffTwoOldMass_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointMassNewShellBound.cutoffTwoNewMass_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointMassNewShellBound.cutoffTwoOldMass_add_newMass_eqv_fullSectorMass
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointMassNewShellBound.cutoffTwoOldMass_add_newMass_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointMassNewShellBound.cutoffTwoNovelEndpointWeightMass_le_newMass_add_newMass
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelEndpointMassNewShellBound.cutoffTwoNovelEndpointWeightMass_le_two_mul_newMass
