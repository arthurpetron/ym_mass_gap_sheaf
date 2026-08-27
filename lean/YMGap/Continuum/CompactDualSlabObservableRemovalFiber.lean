/-
# Actual fixed-target fibers of the observable-rooted slab carrier

The adaptive component estimate accepts an explicit duplicate-free family of
sources with one common lowered target and peel size.  This module supplies
that family from the literal expanded finite measure.

We attach membership proofs to the positive fixed-face source carrier, build
the canonical observable-rooted seed of each attached source, and filter by
the decidable pair consisting of its exact finite-support target key and its
peel size.  Injectivity of target keys then upgrades key equality to equality
of the actual lowered physical labelling and complete auxiliary assignment.
Thus every retained source constructs the fixed-target removal witness needed
by the weighted inverse-fiber theorem.

Constructive contract: finite attachment, Boolean filtering, exact target-key
decoding, and existing component witnesses only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabExpandedTargetKey

namespace YMGap.Continuum.CompactDualSlabObservableRemovalFiber

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveInverseFiber
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableRootSeed
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Attached positive sources and their canonical seeds -/

/-- A positive fixed-face source together with its literal carrier
membership proof. -/
abbrev SlabObservablePositiveSourceEntry
    (D : SlabPhysicalData) (faceId : Nat) :=
  {source : SlabLabelling × SlabFusionWitnessAssignment //
    source ∈ slabObservablePositiveExpandedSources D faceId}

/-- Attach membership evidence to every literal positive source. -/
def slabObservablePositiveSourceEntries
    (D : SlabPhysicalData) (faceId : Nat) :
    List (SlabObservablePositiveSourceEntry D faceId) :=
  (slabObservablePositiveExpandedSources D faceId).attach

theorem SlabObservablePositiveSourceEntry.source_mem_expanded
    {D : SlabPhysicalData} {faceId : Nat}
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    entry.1 ∈ slabExpandedFineSources D :=
  (mem_slabObservablePositiveExpandedSources_iff.mp entry.2).1

theorem SlabObservablePositiveSourceEntry.source_positive
    {D : SlabPhysicalData} {faceId : Nat}
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    0 < entry.1.1 faceId :=
  (mem_slabObservablePositiveExpandedSources_iff.mp entry.2).2

theorem SlabObservablePositiveSourceEntry.physical_mem
    {D : SlabPhysicalData} {faceId : Nat}
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    entry.1.1 ∈ D.physicalLabellings :=
  (mem_slabExpandedFineSources_iff.mp entry.source_mem_expanded).1

/-- The exact assignment-membership proof used by the canonical seed below. -/
def SlabObservablePositiveSourceEntry.assignment_mem
    {D : SlabPhysicalData} {faceId : Nat}
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    entry.1.2 ∈ slabFusionWitnessAssignmentsOn
      D.cutoff D.extent entry.1.1
        (boundaryCompleteSlabLinks D.extent) :=
  (mem_slabExpandedFineSources_iff.mp entry.source_mem_expanded).2

/-- The slot-zero component rooted at the chosen observable face. -/
def SlabObservablePositiveSourceEntry.seed
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    SlabFusionWitnessFaceStrandSeed D.cutoff D.extent entry.1.1
      (boundaryCompleteSlabLinks D.extent) entry.1.2
        entry.assignment_mem :=
  slabObservableRootSeed D.cutoff D.extent faceId hface entry.1.1
    entry.source_positive entry.1.2 entry.assignment_mem

/-! ## 2. Decidable removal keys and literal source fibers -/

/-- A decidable lowered-target key paired with the exact component peel
size. -/
structure SlabExpandedFineRemovalKey : Type where
  targetKey : SlabExpandedFineTargetKey
  peelSize : Nat
  deriving DecidableEq

/-- The removal key computed from one actual positive source. -/
def SlabObservablePositiveSourceEntry.removalKey
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    SlabExpandedFineRemovalKey :=
  let seed := entry.seed D faceId hface
  { targetKey := slabExpandedFineTargetKey D
      (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
      (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed)
    peelSize := (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length }

/-- The key represented by a chosen literal target pair and peel size. -/
def slabExpandedFineRemovalKey
    (D : SlabPhysicalData)
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (peelSize : Nat) : SlabExpandedFineRemovalKey :=
  { targetKey := slabExpandedFineTargetKey D target.1 target.2
    peelSize := peelSize }

/-- Attached positive sources whose canonical peel has one chosen literal
target key and size. -/
def slabObservablePositiveRemovalFiberEntries
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (peelSize : Nat) :
    List (SlabObservablePositiveSourceEntry D faceId) :=
  (slabObservablePositiveSourceEntries D faceId).filter fun entry =>
    decide (entry.removalKey D faceId hface =
      slabExpandedFineRemovalKey D target peelSize)

/-- The corresponding literal list of expanded source pairs. -/
def slabObservablePositiveRemovalFiber
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (peelSize : Nat) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  (slabObservablePositiveRemovalFiberEntries
    D faceId hface target peelSize).map Subtype.val

/-- Every actual fixed-key source fiber is duplicate-free. -/
theorem slabObservablePositiveRemovalFiber_nodup
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (peelSize : Nat) :
    (slabObservablePositiveRemovalFiber
      D faceId hface target peelSize).Nodup := by
  unfold slabObservablePositiveRemovalFiber
  apply nodup_map_of_injOn
  · unfold slabObservablePositiveRemovalFiberEntries
    exact (attach_nodup_of_nodup _
      (slabObservablePositiveExpandedSources_nodup D faceId)).filter _
  · intro left _ right _ heq
    exact Subtype.ext heq

/-! ## 3. Every fiber member carries the required fixed-target witness -/

/-- A source occurring in a fixed-key fiber still belongs to the original
positive observable carrier. -/
theorem slabObservablePositiveRemovalFiber_source_mem_positive
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (peelSize : Nat)
    (source : SlabLabelling × SlabFusionWitnessAssignment)
    (hsource : source ∈ slabObservablePositiveRemovalFiber
      D faceId hface target peelSize) :
    source ∈ slabObservablePositiveExpandedSources D faceId := by
  obtain ⟨entry, _, heq⟩ := List.mem_map.mp hsource
  rw [← heq]
  exact entry.2

/-- The canonical attached version of a fiber source has exactly the selected
removal key. -/
theorem slabObservablePositiveRemovalFiber_removalKey_eq
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (peelSize : Nat)
    (source : SlabLabelling × SlabFusionWitnessAssignment)
    (hsource : source ∈ slabObservablePositiveRemovalFiber
      D faceId hface target peelSize) :
    let entry : SlabObservablePositiveSourceEntry D faceId :=
      ⟨source, slabObservablePositiveRemovalFiber_source_mem_positive
        D faceId hface target peelSize source hsource⟩
    entry.removalKey D faceId hface =
      slabExpandedFineRemovalKey D target peelSize := by
  dsimp only
  obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hsource
  let canonical : SlabObservablePositiveSourceEntry D faceId :=
    ⟨source, slabObservablePositiveRemovalFiber_source_mem_positive
      D faceId hface target peelSize source hsource⟩
  have hentryEq : entry = canonical := Subtype.ext heq
  subst entry
  exact of_decide_eq_true (List.mem_filter.mp hentry).2

/-- Membership in the Boolean fixed-key fiber upgrades to an actual common
lowered target and common peel-size witness. -/
def slabObservablePositiveRemovalFiber_witness
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (htarget : target ∈ slabExpandedFineSources D)
    (peelSize : Nat)
    (source : SlabLabelling × SlabFusionWitnessAssignment)
    (hsource : source ∈ slabObservablePositiveRemovalFiber
      D faceId hface target peelSize) :
    ComponentAdaptiveRemovalWitness D.cutoff D.extent faceId peelSize
      target.1 target.2 source := by
  let entry : SlabObservablePositiveSourceEntry D faceId :=
    ⟨source, slabObservablePositiveRemovalFiber_source_mem_positive
      D faceId hface target peelSize source hsource⟩
  have hkey : entry.removalKey D faceId hface =
      slabExpandedFineRemovalKey D target peelSize :=
    slabObservablePositiveRemovalFiber_removalKey_eq
      D faceId hface target peelSize source hsource
  let seed := entry.seed D faceId hface
  have htargetKey := congrArg SlabExpandedFineRemovalKey.targetKey hkey
  have hpeelSize := congrArg SlabExpandedFineRemovalKey.peelSize hkey
  change slabExpandedFineTargetKey D
      (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
      (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) =
    slabExpandedFineTargetKey D target.1 target.2 at htargetKey
  change (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length =
    peelSize at hpeelSize
  have hlowerMem :
      (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed,
        SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) ∈
          slabExpandedFineSources D :=
    SlabFusionWitnessFaceStrandSeed.lowerTarget_mem_expanded
      D entry.physical_mem seed
  have htargetEq := slabExpandedFineTargetKey_eq_source_eq
    D hlowerMem htarget htargetKey
  exact
    { sourceAssignment_mem := entry.assignment_mem
      seed := seed
      rootFaceId_eq := rfl
      peelSize_eq := hpeelSize
      lowerPhysical_eq := congrArg Prod.fst htargetEq
      lowerAssignment_eq := congrArg Prod.snd htargetEq }

/-- An inhabited observable-rooted removal fiber always has positive peel
size. -/
theorem slabObservablePositiveRemovalFiber_peelSize_pos
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (htarget : target ∈ slabExpandedFineSources D)
    (peelSize : Nat)
    {source : SlabLabelling × SlabFusionWitnessAssignment}
    (hsource : source ∈ slabObservablePositiveRemovalFiber
      D faceId hface target peelSize) :
    0 < peelSize := by
  let witness := slabObservablePositiveRemovalFiber_witness
    D faceId hface target htarget peelSize source hsource
  rw [← witness.peelSize_eq]
  exact SlabFusionWitnessFaceStrandSeed.peelFaces_length_pos witness.seed

/-- Every source retained from the production carrier obeys the required
physical cutoff bound. -/
theorem slabObservablePositiveRemovalFiber_bounded
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (peelSize : Nat)
    (source : SlabLabelling × SlabFusionWitnessAssignment)
    (hsource : source ∈ slabObservablePositiveRemovalFiber
      D faceId hface target peelSize) :
    SlabFaceLabellingBounded D.cutoff D.extent source.1 := by
  let entry : SlabObservablePositiveSourceEntry D faceId :=
    ⟨source, slabObservablePositiveRemovalFiber_source_mem_positive
      D faceId hface target peelSize source hsource⟩
  have hsound := boundedEdgeLabellings_sound
    D.cutoff D.faceEdges source.1 entry.physical_mem
  intro selected hselected
  exact Nat.le_of_lt_succ (hsound.1 selected hselected)

/-! ## 4. Apply the strict fixed-fiber estimate on the actual measure -/

/-- The production corrected slab at the fixed strong-coupling anchor. -/
def anchorSlabPhysicalData (cutoff half : Nat) : SlabPhysicalData :=
  { coupling := anchorCoupling
    coupling_nonnegative := by decide
    cutoff := cutoff
    half := half }

/-- **Actual fixed-key fiber bound.**  The literal positive observable source
fiber with one common target and peel size has weight at most `(8/25)^n`
times the literal target weight. -/
theorem slabObservablePositiveRemovalFiber_weight_sum_le
    (cutoff half faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (htarget : target ∈
      slabExpandedFineSources (anchorSlabPhysicalData cutoff half))
    (peelSize : Nat) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabExpandedFineSourceWeight D)
        (slabObservablePositiveRemovalFiber
          D faceId hface target peelSize) <=
      componentAdaptiveEntropyAnchorRatio ^ peelSize *
        slabExpandedFineSourceWeight D target := by
  dsimp only [anchorSlabPhysicalData]
  exact componentAdaptiveRemovalSources_weight_sum_le
    cutoff half faceId peelSize target.1 target.2
    (slabObservablePositiveRemovalFiber
      (anchorSlabPhysicalData cutoff half)
      faceId hface target peelSize)
    (slabObservablePositiveRemovalFiber_nodup
      (anchorSlabPhysicalData cutoff half)
      faceId hface target peelSize)
    (fun source hsource =>
      slabObservablePositiveRemovalFiber_witness
        (anchorSlabPhysicalData cutoff half)
        faceId hface target htarget peelSize source hsource)
    (fun source hsource =>
      slabObservablePositiveRemovalFiber_bounded
        (anchorSlabPhysicalData cutoff half)
        faceId hface target peelSize source hsource)

#print axioms SlabObservablePositiveSourceEntry
#print axioms slabObservablePositiveSourceEntries
#print axioms SlabObservablePositiveSourceEntry.source_mem_expanded
#print axioms SlabObservablePositiveSourceEntry.source_positive
#print axioms SlabObservablePositiveSourceEntry.physical_mem
#print axioms SlabObservablePositiveSourceEntry.assignment_mem
#print axioms SlabObservablePositiveSourceEntry.seed
#print axioms SlabExpandedFineRemovalKey
#print axioms SlabObservablePositiveSourceEntry.removalKey
#print axioms slabExpandedFineRemovalKey
#print axioms slabObservablePositiveRemovalFiberEntries
#print axioms slabObservablePositiveRemovalFiber
#print axioms slabObservablePositiveRemovalFiber_nodup
#print axioms slabObservablePositiveRemovalFiber_source_mem_positive
#print axioms slabObservablePositiveRemovalFiber_removalKey_eq
#print axioms slabObservablePositiveRemovalFiber_witness
#print axioms slabObservablePositiveRemovalFiber_peelSize_pos
#print axioms slabObservablePositiveRemovalFiber_bounded
#print axioms anchorSlabPhysicalData
#print axioms slabObservablePositiveRemovalFiber_weight_sum_le

end YMGap.Continuum.CompactDualSlabObservableRemovalFiber
