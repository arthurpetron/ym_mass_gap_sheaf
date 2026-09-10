/-
# Expanded-source disintegration and the enriched target marginal

The component compiler works with a fine physical labelling together with an
accepted global intertwiner assignment, while the corrected all-cutoff kernel
is conditioned only on the physical labelling.  This module places both in one
finite disintegration: for every attached physical source, enumerate its
complete accepted intertwiner fiber and weight each witness by its literal
fine-intertwiner contribution divided by the physical partition.

Summing the witness fiber reconstructs the normalized physical source mass.
It follows targetwise that pushing this expanded source law through the
corrected kernel gives exactly the enriched blocked mass.  Cartesian
factorization then proves that the two-copy expanded joint law has target
marginal equal to the product of the two enriched blocked masses.

No connected-event comparison, reflected observable, strict form bound,
continuum limit, or Clay theorem is claimed here.

## Axiom gate

Finite flat-map and Cartesian summation, the exact SU(2) intertwiner-fiber
identity, and rational quotient algebra only.  No classical choice,
placeholder, trusted external computation, computability escape, heartbeat
increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedJointFlow
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerExpandedMarginal

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A physical source with its complete fine-intertwiner fiber -/

abbrev AllCutoffExpandedSource (D : SlabPhysicalData) :=
  SlabPhysicalSourceEntry D × SlabFusionWitnessAssignment

/-- The complete fine-intertwiner fiber above one attached physical source. -/
def allCutoffExpandedSourceBlock
    (D : SlabPhysicalData) (source : SlabPhysicalSourceEntry D) :
    List (AllCutoffExpandedSource D) :=
  (slabFineFusionWitnesses D source.1).map fun witness =>
    (source, witness)

/-- Group the expanded carrier by its attached physical source. -/
def allCutoffExpandedSources (D : SlabPhysicalData) :
    List (AllCutoffExpandedSource D) :=
  (slabPhysicalSourceEntries D).flatMap
    (allCutoffExpandedSourceBlock D)

/-- Literal unnormalized SU(2) weight of one grouped expanded source. -/
def allCutoffExpandedSourceWeight
    (D : SlabPhysicalData) (source : AllCutoffExpandedSource D) : Q' :=
  retainedFineIntertwinerPhysicalFiberWeight
    D source.1.1 source.2

/-- Its normalized probability in the expanded source law. -/
def allCutoffExpandedSourceNormalizedMass
    (D : SlabPhysicalData) (source : AllCutoffExpandedSource D) : Q' :=
  Q'.divPos
    (allCutoffExpandedSourceWeight D source)
    D.physicalPartition
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)

/-- The corrected enriched output row depends only on the physical coordinate
of the grouped expanded source. -/
def allCutoffExpandedSourceKernel
    (S : SlabScalePair) (source : AllCutoffExpandedSource S.fine)
    (target : AllCutoffRetainedTarget) : Q' :=
  allCutoffRetainedFineIntertwinerKernel S source.1 target

/-- Joint density of one grouped expanded source and one enriched target. -/
def allCutoffExpandedSourceJointWeight
    (S : SlabScalePair) (target : AllCutoffRetainedTarget)
    (source : AllCutoffExpandedSource S.fine) : Q' :=
  allCutoffExpandedSourceNormalizedMass S.fine source *
    allCutoffExpandedSourceKernel S source target

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- For one physical source and one enriched target, summing all accepted
fine-intertwiner labels reconstructs the ordinary normalized physical-source
contribution to that target. -/
theorem allCutoffExpandedSourceFiberJointMass
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (target : AllCutoffRetainedTarget) :
    listQSum
        (fun witness =>
          Q'.divPos
              (retainedFineIntertwinerPhysicalFiberWeight
                S.fine source.1 witness)
              S.fine.physicalPartition
              (slabParametricKPhysicalPartition_pos
                S.fine.coupling_nonnegative
                S.fine.cutoff S.fine.extent) *
            allCutoffRetainedFineIntertwinerKernel S source target)
        (slabFineFusionWitnesses S.fine source.1) ≈
      S.fine.normalizedMass source.1 *
        allCutoffRetainedFineIntertwinerKernel S source target := by
  let partitionPos := slabParametricKPhysicalPartition_pos
    S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent
  let inverse := Q'.recipPos S.fine.physicalPartition partitionPos
  let rowValue := allCutoffRetainedFineIntertwinerKernel S source target
  refine Q'.eqv_trans _
    (listQSum
        (fun witness => Q'.divPos
          (retainedFineIntertwinerPhysicalFiberWeight
            S.fine source.1 witness)
          S.fine.physicalPartition partitionPos)
        (slabFineFusionWitnesses S.fine source.1) * rowValue) _ ?_ ?_
  · exact listQSum_mul_right
      (fun witness => Q'.divPos
        (retainedFineIntertwinerPhysicalFiberWeight
          S.fine source.1 witness)
        S.fine.physicalPartition partitionPos)
      rowValue (slabFineFusionWitnesses S.fine source.1)
  refine Q'.eqv_trans _
    ((listQSum
        (retainedFineIntertwinerPhysicalFiberWeight S.fine source.1)
        (slabFineFusionWitnesses S.fine source.1) * inverse) *
      rowValue) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (listQSum_mul_right
        (retainedFineIntertwinerPhysicalFiberWeight S.fine source.1)
        inverse (slabFineFusionWitnesses S.fine source.1))
  unfold SlabPhysicalData.normalizedMass Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (retainedFineIntertwinerPhysicalFiberWeight_total
        S.fine source.1))

/-- The grouped block above one physical source has exactly that source's
ordinary normalized contribution to the selected enriched target. -/
theorem allCutoffExpandedSourceBlockJointMass
    (S : SlabScalePair) (source : SlabPhysicalSourceEntry S.fine)
    (target : AllCutoffRetainedTarget) :
    listQSum (allCutoffExpandedSourceJointWeight S target)
        (allCutoffExpandedSourceBlock S.fine source) ≈
      S.fine.normalizedMass source.1 *
        allCutoffRetainedFineIntertwinerKernel S source target := by
  unfold allCutoffExpandedSourceBlock
  rw [listQSum_map]
  simpa only [allCutoffExpandedSourceJointWeight,
    allCutoffExpandedSourceNormalizedMass,
    allCutoffExpandedSourceWeight,
    allCutoffExpandedSourceKernel] using
      allCutoffExpandedSourceFiberJointMass S source target

/-! ## 2. One-copy target marginal -/

/-- Push the complete grouped expanded source law through the corrected
all-cutoff kernel. -/
def allCutoffExpandedSourceBlockedMass
    (S : SlabScalePair) (target : AllCutoffRetainedTarget) : Q' :=
  listQSum (allCutoffExpandedSourceJointWeight S target)
    (allCutoffExpandedSources S.fine)

/-- Forgetting the expanded source label gives exactly the actual enriched
blocked mass at every target. -/
theorem allCutoffExpandedSourceBlockedMass_eqv_blockedMass
    (S : SlabScalePair) (target : AllCutoffRetainedTarget) :
    allCutoffExpandedSourceBlockedMass S target ≈
      allCutoffRetainedFineIntertwinerBlockedMass S target := by
  refine Q'.eqv_trans _
    (listQSum
      (fun physicalSource : SlabPhysicalSourceEntry S.fine =>
        listQSum (allCutoffExpandedSourceJointWeight S target)
          (allCutoffExpandedSourceBlock S.fine physicalSource))
      (slabPhysicalSourceEntries S.fine)) _ ?_ ?_
  · unfold allCutoffExpandedSourceBlockedMass allCutoffExpandedSources
    exact listQSum_flatMap
      (allCutoffExpandedSourceJointWeight S target)
      (allCutoffExpandedSourceBlock S.fine)
      (slabPhysicalSourceEntries S.fine)
  · unfold allCutoffRetainedFineIntertwinerBlockedMass
    apply listQSum_congr
    intro physicalSource
    exact allCutoffExpandedSourceBlockJointMass
      S physicalSource target

/-! ## 3. Two-copy target marginal -/

/-- Targetwise mass obtained by independently drawing two grouped expanded
sources and applying the two enriched kernel rows. -/
def allCutoffExpandedTwoReplicaTargetMass
    (S : SlabScalePair)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget) : Q' :=
  listQSum
    (fun sources =>
      (allCutoffExpandedSourceNormalizedMass S.fine sources.1 *
        allCutoffExpandedSourceKernel S sources.1 target.1) *
      (allCutoffExpandedSourceNormalizedMass S.fine sources.2 *
        allCutoffExpandedSourceKernel S sources.2 target.2))
    (cartesian
      (allCutoffExpandedSources S.fine)
      (allCutoffExpandedSources S.fine))

/-- The target marginal of the full expanded two-copy joint law is exactly
the product of the two actual enriched blocked masses. -/
theorem allCutoffExpandedTwoReplicaTargetMass_eqv_blockedProduct
    (S : SlabScalePair)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget) :
    allCutoffExpandedTwoReplicaTargetMass S target ≈
      allCutoffRetainedFineIntertwinerBlockedMass S target.1 *
        allCutoffRetainedFineIntertwinerBlockedMass S target.2 := by
  refine Q'.eqv_trans _
    (allCutoffExpandedSourceBlockedMass S target.1 *
      allCutoffExpandedSourceBlockedMass S target.2) _ ?_ ?_
  · exact listQSum_cartesian_product
      (fun source =>
        allCutoffExpandedSourceNormalizedMass S.fine source *
          allCutoffExpandedSourceKernel S source target.1)
      (fun source =>
        allCutoffExpandedSourceNormalizedMass S.fine source *
          allCutoffExpandedSourceKernel S source target.2)
      (allCutoffExpandedSources S.fine)
      (allCutoffExpandedSources S.fine)
  · exact mul_eqv_both_local
      (allCutoffExpandedSourceBlockedMass_eqv_blockedMass S target.1)
      (allCutoffExpandedSourceBlockedMass_eqv_blockedMass S target.2)

/-! ## Axiom audit -/

#print axioms allCutoffExpandedSourceFiberJointMass
#print axioms allCutoffExpandedSourceBlockedMass_eqv_blockedMass
#print axioms allCutoffExpandedTwoReplicaTargetMass_eqv_blockedProduct

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerExpandedMarginal
