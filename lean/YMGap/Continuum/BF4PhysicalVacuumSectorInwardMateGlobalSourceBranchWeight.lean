/-
# Exact fixed-physical weight of the two full-source branches

Every retained SU(2) intertwiner over a fixed physical field has one Haar
counting unit, hence the same heat-kernel face factor.  The exact full-source
cardinality split can therefore be lifted without loss to the genuine BF4
physical summand.  This module assigns that common atom to the all-target
carrier, identifies the already used first-stretched source weight with the
same atom, and proves that their two finite sums reconstruct the fixed-
physical term.

The result is not yet summed over physical fields and is not a pointwise
conditional transition lower bound, posterior estimate, or spectral claim.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchCardinality

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchCardinality
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _head :: tail => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat tail.length * constant) _
        (Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant tail)) ?_
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv
          (Q'.ofNat tail.length * constant) constant)

/-! ## 1. Both branches have the same physical atom -/

/-- The all-target pushforward carrier inherits the common unnormalized
physical source atom. -/
def cubeInwardMateCertifiedTargetFullSourceWeight
    (K : Nat) (physical : EdgeLabelling)
    (_source : CubeInwardMateCertifiedTargetFullSource K physical) : Q' :=
  slabParametricKPhysicalFaceFactor anchorCoupling K 1 physical

/-- The complete all-target branch sum is its exact cardinality times the
common physical face factor. -/
theorem cubeInwardMateCertifiedTargetFullSources_weight_total
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    listQSum (cubeInwardMateCertifiedTargetFullSourceWeight K physical)
        (cubeInwardMateCertifiedTargetFullSources
          K physical hK hbounded) ≈
      Q'.ofNat
          (cubeInwardMateCertifiedTargetFullSources
            K physical hK hbounded).length *
        slabParametricKPhysicalFaceFactor
          anchorCoupling K 1 physical := by
  unfold cubeInwardMateCertifiedTargetFullSourceWeight
  exact listQSum_const_local
    (slabParametricKPhysicalFaceFactor anchorCoupling K 1 physical)
    (cubeInwardMateCertifiedTargetFullSources K physical hK hbounded)

/-- The existing first-stretched summand is exactly the same fixed-physical
Haar counting atom; its adaptive peel is not used in this identity. -/
theorem cubeInwardMateFullSourceEntryWeight_eqv_faceFactor
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :
    cubeInwardMateFullSourceEntryWeight K entry ≈
      slabParametricKPhysicalFaceFactor
        anchorCoupling K 1 physical := by
  unfold cubeInwardMateFullSourceEntryWeight
  simpa only [SlabPhysicalData.extent, centralExtent,
    Nat.zero_add, Nat.add_zero] using
      retainedFineIntertwinerPhysicalFiberWeight_eqv_faceFactor
        ({ coupling := anchorCoupling
           coupling_nonnegative := by decide
           cutoff := K
           half := 0 } : SlabPhysicalData)
        physical entry.raw

/-- Summing the actual first-stretched entry weight gives its exact
cardinality times the common physical face factor. -/
theorem cubeInwardMateEnumeratedFirstStretched_weight_total
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    listQSum (cubeInwardMateFullSourceEntryWeight K)
        (enumeratedCubeInwardMateFullSources
          K physical hK hbounded) ≈
      Q'.ofNat
          (enumeratedCubeInwardMateFullSources
            K physical hK hbounded).length *
        slabParametricKPhysicalFaceFactor
          anchorCoupling K 1 physical := by
  refine Q'.eqv_trans _
    (listQSum
      (fun _entry => slabParametricKPhysicalFaceFactor
        anchorCoupling K 1 physical)
      (enumeratedCubeInwardMateFullSources
        K physical hK hbounded)) _ ?_ ?_
  · apply listQSum_congr_on
    intro entry _
    exact cubeInwardMateFullSourceEntryWeight_eqv_faceFactor entry
  · exact listQSum_const_local
      (slabParametricKPhysicalFaceFactor anchorCoupling K 1 physical)
      (enumeratedCubeInwardMateFullSources
        K physical hK hbounded)

/-! ## 2. Exact fixed-physical weighted normalization -/

/-- **Exact weighted branch conservation.**  The all-target pushforward mass
plus the actual first-stretched mass reconstructs the genuine fixed-physical
BF4 summand. -/
theorem cubeInwardMateFullSourceBranches_weight_total
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    listQSum (cubeInwardMateCertifiedTargetFullSourceWeight K physical)
        (cubeInwardMateCertifiedTargetFullSources
          K physical hK hbounded) +
      listQSum (cubeInwardMateFullSourceEntryWeight K)
        (enumeratedCubeInwardMateFullSources
          K physical hK hbounded) ≈
      slabParametricKPhysicalTerm anchorCoupling K 1 physical := by
  let targetCount :=
    (cubeInwardMateCertifiedTargetFullSources
      K physical hK hbounded).length
  let stretchedCount :=
    (enumeratedCubeInwardMateFullSources
      K physical hK hbounded).length
  let factor :=
    slabParametricKPhysicalFaceFactor anchorCoupling K 1 physical
  refine Q'.eqv_trans _
    (Q'.ofNat targetCount * factor +
      Q'.ofNat stretchedCount * factor) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (cubeInwardMateCertifiedTargetFullSources_weight_total
        K physical hK hbounded)
      (cubeInwardMateEnumeratedFirstStretched_weight_total
        K physical hK hbounded)
  refine Q'.eqv_trans _
    ((Q'.ofNat targetCount + Q'.ofNat stretchedCount) * factor) _
    (Q'.eqv_symm
      (Q'.add_mul_eqv
        (Q'.ofNat targetCount) (Q'.ofNat stretchedCount) factor)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat (targetCount + stretchedCount) * factor) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ factor
      (Q'.eqv_symm (Q'.ofNat_add_eqv targetCount stretchedCount))
  have hlength : targetCount + stretchedCount =
      slabExplicitLinkMultiplicityProduct K 1 physical := by
    exact cubeInwardMateCertifiedTarget_add_enumeratedFirstStretched_length
      K physical hK hbounded
  rw [hlength]
  unfold slabParametricKPhysicalTerm factor
  exact Q'.mul_comm_eqv _ _

#print axioms cubeInwardMateCertifiedTargetFullSources_weight_total
#print axioms cubeInwardMateFullSourceEntryWeight_eqv_faceFactor
#print axioms cubeInwardMateEnumeratedFirstStretched_weight_total
#print axioms cubeInwardMateFullSourceBranches_weight_total

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchWeight
