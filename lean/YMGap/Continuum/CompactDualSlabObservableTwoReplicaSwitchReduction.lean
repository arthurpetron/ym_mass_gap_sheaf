/-
# The exact two-replica switch reduction for the rooted slab observable

The rooted-component estimate controls a literal event in the expanded
finite SU(2) measure.  Turning that estimate into a covariance requires an
additional cancellation statement.  This module isolates the smallest
constructive finite certificate for that cancellation and proves everything
after it.

The four Boolean cells refer to positive physical spin at two fixed faces.
The first replica is rooted at the first face.  A supplied switch must map
each source-cell pair whose first rooted component does not reach the second
face into the opposite cell, preserve the exact two-replica product weight,
and carry an explicit left inverse.  These are concrete combinatorial data,
not a covariance inequality in disguise.

No inhabitant of the switch certificate is constructed here.  In particular,
the one-replica rooted component is not silently identified with the
two-replica disagreement component of the existing Z4 switch.  Conditional
on the certificate, the only residue is bounded by the already proved
same-measure connected event, giving a geometric four-cell defect at the
fixed anchor.

This still does not identify the positive-spin cell observable with a dense
gauge-invariant link-cylinder observable or an OS transfer matrix element.

Constructive contract: literal finite lists, explicit encode/decode data,
exact rational Fubini, and the proved connected-event estimate only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
`noncomputable`, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableConnectedDecay
import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableConnectedComponent
open YMGap.Continuum.CompactDualSlabObservableConnectedDecay
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact attached carrier and its decidable finite-support equality -/

/-- One literal expanded source together with its carrier membership. -/
abbrev SlabExpandedFineSourceEntry (D : SlabPhysicalData) :=
  {source : SlabLabelling × SlabFusionWitnessAssignment //
    source ∈ slabExpandedFineSources D}

/-- Attach membership to every source without changing its order or weight. -/
def slabExpandedFineSourceEntries (D : SlabPhysicalData) :
    List (SlabExpandedFineSourceEntry D) :=
  (slabExpandedFineSources D).attach

/-- Weight of one attached expanded source. -/
def slabExpandedFineEntryWeight
    (D : SlabPhysicalData) (entry : SlabExpandedFineSourceEntry D) : Q' :=
  slabExpandedFineSourceWeight D entry.1

/-- The existing exact finite-support key, restricted to attached entries. -/
def SlabExpandedFineSourceEntry.key
    {D : SlabPhysicalData} (entry : SlabExpandedFineSourceEntry D) :
    SlabExpandedFineTargetKey :=
  slabExpandedFineTargetKey D entry.1.1 entry.1.2

/-- Equality of exact finite-support keys decides equality of attached
expanded entries. -/
theorem SlabExpandedFineSourceEntry.eq_of_key_eq
    {D : SlabPhysicalData} {left right : SlabExpandedFineSourceEntry D}
    (hkey : left.key = right.key) : left = right := by
  apply Subtype.ext
  exact slabExpandedFineTargetKey_eq_source_eq
    D left.2 right.2 hkey

private def slabExpandedFineSourceEntryDecidableEq
    (D : SlabPhysicalData) : DecidableEq (SlabExpandedFineSourceEntry D) :=
  fun left right =>
    if hkey : left.key = right.key then
      isTrue (SlabExpandedFineSourceEntry.eq_of_key_eq hkey)
    else
      isFalse (fun heq => hkey (congrArg SlabExpandedFineSourceEntry.key heq))

local instance (D : SlabPhysicalData) :
    DecidableEq (SlabExpandedFineSourceEntry D) :=
  slabExpandedFineSourceEntryDecidableEq D

/-- The positive-root subtype inherits constructive decidable equality from
the same exact finite-support key. -/
private def slabObservablePositiveSourceEntryDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservablePositiveSourceEntry D rootFaceId) :=
  fun left right =>
    if hkey :
        slabExpandedFineTargetKey D left.1.1 left.1.2 =
          slabExpandedFineTargetKey D right.1.1 right.1.2 then
      isTrue (Subtype.ext (slabExpandedFineTargetKey_eq_source_eq D
        left.source_mem_expanded right.source_mem_expanded hkey))
    else
      isFalse (fun heq => hkey (by rw [heq]))

local instance (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservablePositiveSourceEntry D rootFaceId) :=
  slabObservablePositiveSourceEntryDecidableEq D rootFaceId

theorem slabExpandedFineSourceEntries_nodup (D : SlabPhysicalData) :
    (slabExpandedFineSourceEntries D).Nodup := by
  unfold slabExpandedFineSourceEntries
  exact attach_nodup_of_nodup _ (slabExpandedFineSources_nodup D)

/-- Attaching the exact expanded carrier preserves its total weight. -/
theorem slabExpandedFineSourceEntries_weight_total (D : SlabPhysicalData) :
    listQSum (slabExpandedFineEntryWeight D)
        (slabExpandedFineSourceEntries D) ≈
      D.physicalPartition := by
  refine Q'.eqv_trans _
    (listQSum (slabExpandedFineSourceWeight D)
      (slabExpandedFineSources D)) _ ?_ ?_
  · exact Q'.eqv_of_eq
      (listQSum_attach (slabExpandedFineSourceWeight D)
        (slabExpandedFineSources D))
  · exact slabExpandedFineSources_weight_total D

/-! ## 2. The literal two-face four cells -/

/-- Positive spin at one face, evaluated on a full attached source. -/
def SlabExpandedFineSourceEntry.facePositiveB
    {D : SlabPhysicalData} (entry : SlabExpandedFineSourceEntry D)
    (faceId : Nat) : Bool :=
  decide (0 < entry.1.1 faceId)

/-- Positive spin at a second face, evaluated on a source already known to
be positive at the root face. -/
def SlabObservablePositiveSourceEntry.facePositiveB
    {D : SlabPhysicalData} {rootFaceId : Nat}
    (entry : SlabObservablePositiveSourceEntry D rootFaceId)
    (faceId : Nat) : Bool :=
  decide (0 < entry.1.1 faceId)

/-- Cell `11`: root-positive entries also positive at the target face. -/
def slabObservableRootTargetEntries
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservablePositiveSourceEntry D rootFaceId) :=
  (slabObservablePositiveSourceEntries D rootFaceId).filter fun entry =>
    SlabObservablePositiveSourceEntry.facePositiveB entry targetFaceId

/-- Cell `10`: root-positive entries not positive at the target face. -/
def slabObservableRootTargetComplementEntries
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservablePositiveSourceEntry D rootFaceId) :=
  (slabObservablePositiveSourceEntries D rootFaceId).filter fun entry =>
    !(SlabObservablePositiveSourceEntry.facePositiveB entry targetFaceId)

/-- Cell `01`: root-zero entries positive at the target face. -/
def slabObservableRootComplementTargetEntries
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabExpandedFineSourceEntry D) :=
  (slabExpandedFineSourceEntries D).filter fun entry =>
    !(SlabExpandedFineSourceEntry.facePositiveB entry rootFaceId) &&
      SlabExpandedFineSourceEntry.facePositiveB entry targetFaceId

/-- Cell `00`: entries positive at neither selected face. -/
def slabObservableRootComplementTargetComplementEntries
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabExpandedFineSourceEntry D) :=
  (slabExpandedFineSourceEntries D).filter fun entry =>
    !(SlabExpandedFineSourceEntry.facePositiveB entry rootFaceId) &&
      !(SlabExpandedFineSourceEntry.facePositiveB entry targetFaceId)

/-- A rooted first replica and an arbitrary attached second replica. -/
abbrev SlabObservableTwoReplicaPair
    (D : SlabPhysicalData) (rootFaceId : Nat) :=
  SlabObservablePositiveSourceEntry D rootFaceId ×
    SlabExpandedFineSourceEntry D

/-- The exact two-replica product weight. -/
def slabObservableTwoReplicaPairWeight
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) : Q' :=
  slabObservablePositiveEntryWeight D pair.1 *
    slabExpandedFineEntryWeight D pair.2

/-- Source determinant cell `11 × 00`. -/
def slabObservableFourCellSourcePairs
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservableTwoReplicaPair D rootFaceId) :=
  cartesian
    (slabObservableRootTargetEntries D rootFaceId targetFaceId)
    (slabObservableRootComplementTargetComplementEntries
      D rootFaceId targetFaceId)

/-- Opposite determinant cell `10 × 01`. -/
def slabObservableFourCellTargetPairs
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    List (SlabObservableTwoReplicaPair D rootFaceId) :=
  cartesian
    (slabObservableRootTargetComplementEntries
      D rootFaceId targetFaceId)
    (slabObservableRootComplementTargetEntries
      D rootFaceId targetFaceId)

/-- Whether the first replica's canonical root component reaches the target
face plaquette. -/
def SlabObservableTwoReplicaPair.reachesTargetB
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (targetFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair D rootFaceId) : Bool :=
  SlabObservablePositiveSourceEntry.reachesPlaquetteB
    D rootFaceId hroot pair.1
    (slabPlaquetteAt D.extent targetFaceId)

/-- Source pairs on which the rooted component is disconnected from the
target face. -/
def slabObservableSeparatedFourCellSourcePairs
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (targetFaceId : Nat) :
    List (SlabObservableTwoReplicaPair D rootFaceId) :=
  (slabObservableFourCellSourcePairs
    D rootFaceId targetFaceId).filter fun pair =>
      !(pair.reachesTargetB D rootFaceId hroot targetFaceId)

/-- The literal connected residue inside the source determinant cell. -/
def slabObservableConnectedFourCellSourcePairs
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (targetFaceId : Nat) :
    List (SlabObservableTwoReplicaPair D rootFaceId) :=
  (slabObservableFourCellSourcePairs
    D rootFaceId targetFaceId).filter fun pair =>
      pair.reachesTargetB D rootFaceId hroot targetFaceId

/-! ## 3. Exact Fubini and the connected residue -/

theorem slabObservableFourCellSourcePairs_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    (slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId).Nodup := by
  apply cartesian_nodup
  · unfold slabObservableRootTargetEntries
      slabObservablePositiveSourceEntries
    exact (attach_nodup_of_nodup _
      (slabObservablePositiveExpandedSources_nodup
        D rootFaceId)).filter _
  · exact (slabExpandedFineSourceEntries_nodup D).filter _

theorem slabObservableFourCellTargetPairs_nodup
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    (slabObservableFourCellTargetPairs
      D rootFaceId targetFaceId).Nodup := by
  apply cartesian_nodup
  · unfold slabObservableRootTargetComplementEntries
      slabObservablePositiveSourceEntries
    exact (attach_nodup_of_nodup _
      (slabObservablePositiveExpandedSources_nodup
        D rootFaceId)).filter _
  · exact (slabExpandedFineSourceEntries_nodup D).filter _

/-- Exact Fubini for the source determinant cell. -/
theorem slabObservableFourCellSourcePairs_weight_product
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellSourcePairs
          D rootFaceId targetFaceId) ≈
      listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableRootTargetEntries
            D rootFaceId targetFaceId) *
        listQSum (slabExpandedFineEntryWeight D)
          (slabObservableRootComplementTargetComplementEntries
            D rootFaceId targetFaceId) := by
  exact listQSum_cartesian_product
    (slabObservablePositiveEntryWeight D)
    (slabExpandedFineEntryWeight D)
    (slabObservableRootTargetEntries D rootFaceId targetFaceId)
    (slabObservableRootComplementTargetComplementEntries
      D rootFaceId targetFaceId)

/-- Exact Fubini for the opposite determinant cell. -/
theorem slabObservableFourCellTargetPairs_weight_product
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs
          D rootFaceId targetFaceId) ≈
      listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableRootTargetComplementEntries
            D rootFaceId targetFaceId) *
        listQSum (slabExpandedFineEntryWeight D)
          (slabObservableRootComplementTargetEntries
            D rootFaceId targetFaceId) := by
  exact listQSum_cartesian_product
    (slabObservablePositiveEntryWeight D)
    (slabExpandedFineEntryWeight D)
    (slabObservableRootTargetComplementEntries
      D rootFaceId targetFaceId)
    (slabObservableRootComplementTargetEntries
      D rootFaceId targetFaceId)

/-- The source cell is exactly the disjoint sum of its separated and
connected parts. -/
theorem slabObservableFourCellSourcePairs_partition
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (targetFaceId : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellSourcePairs
          D rootFaceId targetFaceId) ≈
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableSeparatedFourCellSourcePairs
            D rootFaceId hroot targetFaceId) +
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableConnectedFourCellSourcePairs
            D rootFaceId hroot targetFaceId) := by
  have hpartition := listQSum_filter_partition
    (slabObservableTwoReplicaPairWeight D)
    (fun pair : SlabObservableTwoReplicaPair D rootFaceId =>
      pair.reachesTargetB D rootFaceId hroot targetFaceId)
    (slabObservableFourCellSourcePairs D rootFaceId targetFaceId)
  change _ ≈
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableConnectedFourCellSourcePairs
            D rootFaceId hroot targetFaceId) +
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableSeparatedFourCellSourcePairs
            D rootFaceId hroot targetFaceId) at hpartition
  exact Q'.eqv_trans _ _ _ hpartition (Q'.add_comm_eqv _ _)

/-- Every expanded entry has nonnegative weight at the production anchor. -/
theorem slabExpandedFineEntryWeight_anchor_nonnegative
    (cutoff half : Nat)
    (entry : SlabExpandedFineSourceEntry
      (anchorSlabPhysicalData cutoff half)) :
    (0 : Q') ≤ slabExpandedFineEntryWeight
      (anchorSlabPhysicalData cutoff half) entry := by
  unfold slabExpandedFineEntryWeight slabExpandedFineSourceWeight
    anchorSlabPhysicalData
  exact retainedFineIntertwinerPhysicalFiberWeight_anchor_nonnegative
    cutoff half entry.1.1 entry.1.2

/-- Every rooted entry has nonnegative weight at the production anchor. -/
theorem slabObservablePositiveEntryWeight_anchor_nonnegative
    (cutoff half rootFaceId : Nat)
    (entry : SlabObservablePositiveSourceEntry
      (anchorSlabPhysicalData cutoff half) rootFaceId) :
    (0 : Q') ≤ slabObservablePositiveEntryWeight
      (anchorSlabPhysicalData cutoff half) entry := by
  unfold slabObservablePositiveEntryWeight slabExpandedFineSourceWeight
    anchorSlabPhysicalData
  exact retainedFineIntertwinerPhysicalFiberWeight_anchor_nonnegative
    cutoff half entry.1.1 entry.1.2

/-- The exact two-replica product weight is nonnegative at the anchor. -/
theorem slabObservableTwoReplicaPairWeight_anchor_nonnegative
    (cutoff half rootFaceId : Nat)
    (pair : SlabObservableTwoReplicaPair
      (anchorSlabPhysicalData cutoff half) rootFaceId) :
    (0 : Q') ≤ slabObservableTwoReplicaPairWeight
      (anchorSlabPhysicalData cutoff half) pair := by
  exact Q'.mul_nonneg _ _
    (slabObservablePositiveEntryWeight_anchor_nonnegative
      cutoff half rootFaceId pair.1)
    (slabExpandedFineEntryWeight_anchor_nonnegative
      cutoff half pair.2)

/-- The connected source-cell residue is no larger than the complete
connected first-replica weight times the physical partition. -/
theorem slabObservableConnectedFourCellSourcePairs_weight_le
    (cutoff half rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (targetFaceId : Nat) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableConnectedFourCellSourcePairs
          D rootFaceId hroot targetFaceId) ≤
      listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableConnectedSourceEntries D rootFaceId hroot
            (slabPlaquetteAt D.extent targetFaceId)) *
        D.physicalPartition := by
  let D := anchorSlabPhysicalData cutoff half
  let broad : List (SlabObservableTwoReplicaPair D rootFaceId) :=
    cartesian
      (slabObservableConnectedSourceEntries D rootFaceId hroot
        (slabPlaquetteAt D.extent targetFaceId))
      (slabExpandedFineSourceEntries D)
  have hsourceNodup :
      (slabObservableConnectedFourCellSourcePairs
        D rootFaceId hroot targetFaceId).Nodup :=
    (slabObservableFourCellSourcePairs_nodup
      D rootFaceId targetFaceId).filter _
  have hsub :
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableConnectedFourCellSourcePairs
            D rootFaceId hroot targetFaceId) ≤
        listQSum (slabObservableTwoReplicaPairWeight D) broad := by
    apply listQSum_le_of_injective
      (slabObservableConnectedFourCellSourcePairs
        D rootFaceId hroot targetFaceId)
      broad
      (slabObservableTwoReplicaPairWeight D)
      (slabObservableTwoReplicaPairWeight D)
      (fun pair => pair)
      hsourceNodup
    · intro pair hpair
      have hfiltered := List.mem_filter.mp hpair
      have hsource := mem_cartesian_iff
        (slabObservableRootTargetEntries
          D rootFaceId targetFaceId)
        (slabObservableRootComplementTargetComplementEntries
          D rootFaceId targetFaceId) pair |>.mp hfiltered.1
      apply mem_cartesian_iff _ _ pair |>.mpr
      constructor
      · unfold slabObservableConnectedSourceEntries
        apply List.mem_filter.mpr
        have hfirst := List.mem_filter.mp hsource.1
        exact ⟨hfirst.1, hfiltered.2⟩
      · exact (List.mem_filter.mp hsource.2).1
    · intro first _ second _ heq
      exact heq
    · intro pair _
      exact Q'.le_refl' _
    · intro pair _
      exact slabObservableTwoReplicaPairWeight_anchor_nonnegative
        cutoff half rootFaceId pair
  have hbroad :
      listQSum (slabObservableTwoReplicaPairWeight D) broad ≈
        listQSum (slabObservablePositiveEntryWeight D)
            (slabObservableConnectedSourceEntries D rootFaceId hroot
              (slabPlaquetteAt D.extent targetFaceId)) *
          D.physicalPartition := by
    refine Q'.eqv_trans _
      (listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableConnectedSourceEntries D rootFaceId hroot
            (slabPlaquetteAt D.extent targetFaceId)) *
        listQSum (slabExpandedFineEntryWeight D)
          (slabExpandedFineSourceEntries D)) _ ?_ ?_
    · exact listQSum_cartesian_product
        (slabObservablePositiveEntryWeight D)
        (slabExpandedFineEntryWeight D)
        (slabObservableConnectedSourceEntries D rootFaceId hroot
          (slabPlaquetteAt D.extent targetFaceId))
        (slabExpandedFineSourceEntries D)
    · exact Q'.mul_eqv_congr_left _ _ _
        (slabExpandedFineSourceEntries_weight_total D)
  exact Q'.le_trans' _ _ _ hsub (Q'.le_of_eqv hbroad)

/-! ## 4. The missing exact switch, isolated as data -/

/-- **OPEN finite combinatorial input.**  A recoverable exact switch from
every disconnected `11 × 00` pair into `10 × 01` on the literal expanded
SU(2) carrier.

An inhabitant must construct both maps.  It must prove target-cell membership,
left-inverse recovery on the separated source list, and exact preservation of
the full physical-plus-intertwiner product weight.  None of these fields is a
four-cell inequality or covariance bound. -/
structure SlabObservableDisconnectedSwitchCertificate
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (targetFaceId : Nat)
    (_htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) : Type where
  encode : SlabObservableTwoReplicaPair D rootFaceId →
    SlabObservableTwoReplicaPair D rootFaceId
  decode : SlabObservableTwoReplicaPair D rootFaceId →
    SlabObservableTwoReplicaPair D rootFaceId
  encode_mem_target : ∀ pair,
    pair ∈ slabObservableSeparatedFourCellSourcePairs
        D rootFaceId hroot targetFaceId →
      encode pair ∈ slabObservableFourCellTargetPairs
        D rootFaceId targetFaceId
  decode_encode : ∀ pair,
    pair ∈ slabObservableSeparatedFourCellSourcePairs
        D rootFaceId hroot targetFaceId →
      decode (encode pair) = pair
  weight_preserved : ∀ pair,
    pair ∈ slabObservableSeparatedFourCellSourcePairs
        D rootFaceId hroot targetFaceId →
      slabObservableTwoReplicaPairWeight D (encode pair) ≈
        slabObservableTwoReplicaPairWeight D pair

theorem SlabObservableDisconnectedSwitchCertificate.encode_injective
    {D : SlabPhysicalData} {rootFaceId : Nat}
    {hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent}
    {targetFaceId : Nat}
    {htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent}
    (certificate : SlabObservableDisconnectedSwitchCertificate
      D rootFaceId hroot targetFaceId htarget)
    (first : SlabObservableTwoReplicaPair D rootFaceId)
    (hfirst : first ∈ slabObservableSeparatedFourCellSourcePairs
      D rootFaceId hroot targetFaceId)
    (second : SlabObservableTwoReplicaPair D rootFaceId)
    (hsecond : second ∈ slabObservableSeparatedFourCellSourcePairs
      D rootFaceId hroot targetFaceId)
    (heq : certificate.encode first = certificate.encode second) :
    first = second := by
  rw [← certificate.decode_encode first hfirst,
    ← certificate.decode_encode second hsecond, heq]

/-- A recoverable exact switch cancels the complete separated source weight
against the opposite four-cell weight. -/
theorem slabObservableSeparatedFourCellSourcePairs_weight_le
    (cutoff half rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (certificate : SlabObservableDisconnectedSwitchCertificate
      (anchorSlabPhysicalData cutoff half) rootFaceId hroot
      targetFaceId htarget) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableSeparatedFourCellSourcePairs
          D rootFaceId hroot targetFaceId) ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs
          D rootFaceId targetFaceId) := by
  let D := anchorSlabPhysicalData cutoff half
  apply listQSum_le_of_injective
    (slabObservableSeparatedFourCellSourcePairs
      D rootFaceId hroot targetFaceId)
    (slabObservableFourCellTargetPairs D rootFaceId targetFaceId)
    (slabObservableTwoReplicaPairWeight D)
    (slabObservableTwoReplicaPairWeight D)
    certificate.encode
    ((slabObservableFourCellSourcePairs_nodup
      D rootFaceId targetFaceId).filter _)
  · exact certificate.encode_mem_target
  · exact certificate.encode_injective
  · intro pair hpair
    exact Q'.le_of_eqv (Q'.eqv_symm
      (certificate.weight_preserved pair hpair))
  · intro pair _
    exact slabObservableTwoReplicaPairWeight_anchor_nonnegative
      cutoff half rootFaceId pair

/-! ## 5. Contract the open switch into the proved connected-event rate -/

/-- Conditional on the explicit switch data, the full source four-cell sum
is bounded by the opposite cell plus the literal connected-event mass times
one physical partition. -/
theorem slabObservableFourCellSourcePairs_weight_le_connected
    (cutoff half rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (certificate : SlabObservableDisconnectedSwitchCertificate
      (anchorSlabPhysicalData cutoff half) rootFaceId hroot
      targetFaceId htarget) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellSourcePairs
          D rootFaceId targetFaceId) ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableFourCellTargetPairs
            D rootFaceId targetFaceId) +
        listQSum (slabObservablePositiveEntryWeight D)
            (slabObservableConnectedSourceEntries D rootFaceId hroot
              (slabPlaquetteAt D.extent targetFaceId)) *
          D.physicalPartition := by
  let D := anchorSlabPhysicalData cutoff half
  have hpartition := slabObservableFourCellSourcePairs_partition
    D rootFaceId hroot targetFaceId
  have hseparated :=
    slabObservableSeparatedFourCellSourcePairs_weight_le
      cutoff half rootFaceId hroot targetFaceId htarget certificate
  have hconnected :=
    slabObservableConnectedFourCellSourcePairs_weight_le
      cutoff half rootFaceId hroot targetFaceId
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hpartition)
    (Q'.add_le_add hseparated hconnected)

/-- **Conditional finite-anchor four-cell decay.**  An explicit exact
disconnected switch contracts the Boolean two-face determinant source cell
to its opposite cell plus the proved geometric connected-component rate
times `Z²`.

This is the strongest conclusion supported by the present carrier.  It is
not yet a signed covariance in a link-cylinder algebra or an OS form bound. -/
theorem slabObservableFourCell_defect_le_anchorRate_of_switch
    (cutoff half rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (certificate : SlabObservableDisconnectedSwitchCertificate
      (anchorSlabPhysicalData cutoff half) rootFaceId hroot
      targetFaceId htarget) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabObservablePositiveEntryWeight D)
          (slabObservableRootTargetEntries
            D rootFaceId targetFaceId) *
        listQSum (slabExpandedFineEntryWeight D)
          (slabObservableRootComplementTargetComplementEntries
            D rootFaceId targetFaceId) ≤
      listQSum (slabObservablePositiveEntryWeight D)
            (slabObservableRootTargetComplementEntries
              D rootFaceId targetFaceId) *
          listQSum (slabExpandedFineEntryWeight D)
            (slabObservableRootComplementTargetEntries
              D rootFaceId targetFaceId) +
        (slabObservableConnectedAnchorRate D rootFaceId
            (slabPlaquetteAt D.extent targetFaceId) *
          D.physicalPartition) * D.physicalPartition := by
  let D := anchorSlabPhysicalData cutoff half
  have hsource := slabObservableFourCellSourcePairs_weight_product
    D rootFaceId targetFaceId
  have htargetPair := slabObservableFourCellTargetPairs_weight_product
    D rootFaceId targetFaceId
  have hfour := slabObservableFourCellSourcePairs_weight_le_connected
    cutoff half rootFaceId hroot targetFaceId htarget certificate
  have hconnected :=
    slabObservableConnectedSourceEntries_weight_le_partition
      cutoff half rootFaceId hroot
        (slabPlaquetteAt D.extent targetFaceId)
  have hpartitionNonnegative : (0 : Q') ≤ D.physicalPartition :=
    Q'.le_of_lt (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)
  have hconnectedScaled := Q'.mul_le_mul_of_nonneg_right
    _ _ D.physicalPartition hconnected hpartitionNonnegative
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsource))
    (Q'.le_trans' _ _ _ hfour
      (Q'.add_le_add (Q'.le_of_eqv htargetPair) hconnectedScaled))

#print axioms SlabExpandedFineSourceEntry.eq_of_key_eq
#print axioms slabExpandedFineSourceEntries_nodup
#print axioms slabExpandedFineSourceEntries_weight_total
#print axioms slabObservableFourCellSourcePairs_nodup
#print axioms slabObservableFourCellSourcePairs_weight_product
#print axioms slabObservableFourCellTargetPairs_weight_product
#print axioms slabObservableFourCellSourcePairs_partition
#print axioms slabObservableConnectedFourCellSourcePairs_weight_le
#print axioms SlabObservableDisconnectedSwitchCertificate.encode_injective
#print axioms slabObservableSeparatedFourCellSourcePairs_weight_le
#print axioms slabObservableFourCellSourcePairs_weight_le_connected
#print axioms slabObservableFourCell_defect_le_anchorRate_of_switch

end YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
