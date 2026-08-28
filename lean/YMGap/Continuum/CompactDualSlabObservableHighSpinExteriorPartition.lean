/-
# Localized observable-rooted high-spin exterior partition

The global canonical exterior classifier leaves a volume-growing root
congestion.  A positive one-face observable already supplies a distinguished
root, so this module instead filters its canonical rooted component by the
arbitrary-coupling high-spin reserve check.

The retained exterior entries are partitioned by their existing exact removal
key `(lower target, component size)`.  Every realized fiber retains an actual
source representative, has the adaptive entropy cardinality, and pays the
arbitrary-coupling Casimir factor.  Consequently

```text
localized exterior fiber weight <= (8/25)^n * target weight,
```

and the total localized exterior weight is bounded by the explicit sum over
realized target/size representatives.  The root is fixed by construction, so
no root or volume multiplicity appears.  Summation over distinct sizes and
the complementary core-blocked carrier are left to subsequent modules.

Constructive contract: literal finite filtering, realized-key partition,
adaptive entropy injection, and the accepted high-spin weight estimate only.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
import YMGap.Continuum.CompactDualSlabObservableRemovalPartition
import YMGap.Continuum.FiniteKeyRepresentativePartition

namespace YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition

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
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableRootSeed
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal fixed-root exterior entries -/

/-- Positive observable-rooted entries whose selected component passes the
finite high-spin reserve check. -/
def slabObservableHighSpinExteriorEntries
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    List (SlabObservablePositiveSourceEntry D faceId) :=
  (slabObservablePositiveSourceEntries D faceId).filter fun entry =>
    decide
      (SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
        (entry.seed D faceId hface) threshold = true)

/-- Literal expanded source pairs carried by the localized exterior branch. -/
def slabObservableHighSpinExteriorSources
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  (slabObservableHighSpinExteriorEntries D faceId hface threshold).map
    Subtype.val

/-- Membership in the exterior filter exposes the paid reserve check. -/
theorem slabObservableHighSpinExteriorEntry_reserve_paid
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (entry : SlabObservablePositiveSourceEntry D faceId)
    (hentry : entry ∈
      slabObservableHighSpinExteriorEntries D faceId hface threshold) :
    SlabFusionWitnessFaceStrandSeed.highSpinReserveCheck
        (entry.seed D faceId hface) threshold = true :=
  of_decide_eq_true (List.mem_filter.mp hentry).2

/-- Localized exterior sources remain duplicate-free literal expanded pairs. -/
theorem slabObservableHighSpinExteriorSources_nodup
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    (slabObservableHighSpinExteriorSources
      D faceId hface threshold).Nodup := by
  unfold slabObservableHighSpinExteriorSources
  apply nodup_map_of_injOn
  · unfold slabObservableHighSpinExteriorEntries
    exact (attach_nodup_of_nodup _
      (slabObservablePositiveExpandedSources_nodup D faceId)).filter _
  · intro left _ right _ heq
    exact Subtype.ext heq

/-! ## 2. Complete removal keys and concrete representative data -/

/-- The actual lower target of one positive observable entry. -/
def slabObservableHighSpinExteriorTarget
    {D : SlabPhysicalData} {faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    SlabLabelling × SlabFusionWitnessAssignment :=
  (SlabFusionWitnessFaceStrandSeed.lowerPhysical
      (entry.seed D faceId hface),
    SlabFusionWitnessFaceStrandSeed.lowerAssignment
      (entry.seed D faceId hface))

/-- Every actual lower target remains in the expanded production carrier. -/
theorem slabObservableHighSpinExteriorTarget_mem
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    slabObservableHighSpinExteriorTarget hface entry ∈
      slabExpandedFineSources D :=
  SlabFusionWitnessFaceStrandSeed.lowerTarget_mem_expanded
    D entry.physical_mem (entry.seed D faceId hface)

/-- Exact serialized size of the selected observable-rooted component. -/
def slabObservableHighSpinExteriorPeelSize
    {D : SlabPhysicalData} {faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservablePositiveSourceEntry D faceId) : Nat :=
  (SlabFusionWitnessFaceStrandSeed.peelFaces
    (entry.seed D faceId hface)).length

/-- Equal removal keys force equal concrete lower targets. -/
theorem slabObservableHighSpinExteriorTarget_eq_of_removalKey_eq
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    (left right : SlabObservablePositiveSourceEntry D faceId)
    (hkey : left.removalKey D faceId hface =
      right.removalKey D faceId hface) :
    slabObservableHighSpinExteriorTarget hface left =
      slabObservableHighSpinExteriorTarget hface right :=
  slabExpandedFineTargetKey_eq_source_eq D
    (slabObservableHighSpinExteriorTarget_mem left)
    (slabObservableHighSpinExteriorTarget_mem right)
    (congrArg SlabExpandedFineRemovalKey.targetKey hkey)

/-- Equal removal keys force equal component sizes. -/
theorem slabObservableHighSpinExteriorPeelSize_eq_of_removalKey_eq
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    (left right : SlabObservablePositiveSourceEntry D faceId)
    (hkey : left.removalKey D faceId hface =
      right.removalKey D faceId hface) :
    slabObservableHighSpinExteriorPeelSize hface left =
      slabObservableHighSpinExteriorPeelSize hface right :=
  congrArg SlabExpandedFineRemovalKey.peelSize hkey

/-- Adaptive inverse-fiber code of one fixed-root exterior entry. -/
def slabObservableHighSpinExteriorEntropyCode
    {D : SlabPhysicalData} {faceId : Nat}
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    ComponentAdaptiveEntropyCode :=
  componentAdaptiveEntropyCode (entry.seed D faceId hface)

/-! ## 3. Realized complete-key fibers -/

/-- One actual exterior entry for every realized `(target, size)` key. -/
def slabObservableHighSpinExteriorRepresentatives
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    List (SlabObservablePositiveSourceEntry D faceId) :=
  keyRepresentatives
    (SlabObservablePositiveSourceEntry.removalKey D faceId hface)
    (slabObservableHighSpinExteriorEntries D faceId hface threshold)

/-- Exterior entries with the same complete removal key as one actual
representative. -/
def slabObservableHighSpinExteriorRepresentativeFiberEntries
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (representative : SlabObservablePositiveSourceEntry D faceId) :
    List (SlabObservablePositiveSourceEntry D faceId) :=
  representativeFiber
    (slabObservableHighSpinExteriorEntries D faceId hface threshold)
    (SlabObservablePositiveSourceEntry.removalKey D faceId hface)
    representative

/-- Literal expanded source pairs in one realized complete-key fiber. -/
def slabObservableHighSpinExteriorRepresentativeFiberSources
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (representative : SlabObservablePositiveSourceEntry D faceId) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  (slabObservableHighSpinExteriorRepresentativeFiberEntries
    (hface := hface) (threshold := threshold) representative).map Subtype.val

/-- Literal sources in every representative fiber are duplicate-free. -/
theorem slabObservableHighSpinExteriorRepresentativeFiberSources_nodup
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (representative : SlabObservablePositiveSourceEntry D faceId) :
    (slabObservableHighSpinExteriorRepresentativeFiberSources
      (hface := hface) (threshold := threshold) representative).Nodup := by
  unfold slabObservableHighSpinExteriorRepresentativeFiberSources
  apply nodup_map_of_injOn
  · unfold slabObservableHighSpinExteriorRepresentativeFiberEntries
    exact List.filter_sublist.nodup
      (List.filter_sublist.nodup
        (attach_nodup_of_nodup _
          (slabObservablePositiveExpandedSources_nodup D faceId)))
  · intro left _ right _ heq
    exact Subtype.ext heq

/-- Every entry in a representative fiber has the representative's complete
removal key. -/
theorem slabObservableHighSpinExteriorRepresentativeFiberEntry_key_eq
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (representative entry : SlabObservablePositiveSourceEntry D faceId)
    (hentry : entry ∈
      slabObservableHighSpinExteriorRepresentativeFiberEntries
        (hface := hface) (threshold := threshold) representative) :
    representative.removalKey D faceId hface =
      entry.removalKey D faceId hface :=
  of_decide_eq_true (List.mem_filter.mp hentry).2

/-- Every exterior entry obeys the physical cutoff bound. -/
theorem slabObservableHighSpinExteriorEntry_bounded
    {D : SlabPhysicalData} {faceId : Nat}
    (entry : SlabObservablePositiveSourceEntry D faceId) :
    SlabFaceLabellingBounded D.cutoff D.extent entry.1.1 := by
  have hsound := boundedEdgeLabellings_sound
    D.cutoff D.faceEdges entry.1.1 entry.physical_mem
  intro selected hselected
  exact Nat.le_of_lt_succ (hsound.1 selected hselected)

private theorem nodup_of_map_nodup {A B : Type} (map : A -> B) :
    forall {items : List A}, (items.map map).Nodup -> items.Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_of_map_nodup map hparts.2⟩
      intro hmem
      exact hparts.1 (List.mem_map.mpr ⟨head, hmem, rfl⟩)

/-- Adaptive entropy codes in one localized representative fiber are
duplicate-free. -/
theorem slabObservableHighSpinExteriorRepresentativeFiberCodes_nodup
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (representative : SlabObservablePositiveSourceEntry D faceId) :
    ((slabObservableHighSpinExteriorRepresentativeFiberEntries
        (hface := hface) (threshold := threshold) representative).map
      (slabObservableHighSpinExteriorEntropyCode hface)).Nodup := by
  let items := slabObservableHighSpinExteriorRepresentativeFiberEntries
    (hface := hface) (threshold := threshold) representative
  have hitems : items.Nodup :=
    nodup_of_map_nodup Subtype.val
      (slabObservableHighSpinExteriorRepresentativeFiberSources_nodup
        (hface := hface) (threshold := threshold) representative)
  apply nodup_map_of_injOn (slabObservableHighSpinExteriorEntropyCode hface)
    items hitems
  intro left hleft right hright hcode
  have hleftKey :=
    slabObservableHighSpinExteriorRepresentativeFiberEntry_key_eq
      representative left hleft
  have hrightKey :=
    slabObservableHighSpinExteriorRepresentativeFiberEntry_key_eq
      representative right hright
  have hkey : left.removalKey D faceId hface =
      right.removalKey D faceId hface := hleftKey.symm.trans hrightKey
  have htarget := slabObservableHighSpinExteriorTarget_eq_of_removalKey_eq
    left right hkey
  have hsourceData := componentAdaptiveEntropyCode_eq_sourceData_eq
    (left.seed D faceId hface) (right.seed D faceId hface)
    (by simp [SlabObservablePositiveSourceEntry.seed])
    (congrArg Prod.fst htarget) (congrArg Prod.snd htarget) hcode
  exact Subtype.ext (Prod.ext hsourceData.1 hsourceData.2)

/-- One localized realized fiber has at most the adaptive entropy base to its
representative component-size power. -/
theorem slabObservableHighSpinExteriorRepresentativeFiberEntries_length_le
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (representative : SlabObservablePositiveSourceEntry D faceId) :
    (slabObservableHighSpinExteriorRepresentativeFiberEntries
        (hface := hface) (threshold := threshold) representative).length <=
      componentAdaptiveEntropyBase ^
        slabObservableHighSpinExteriorPeelSize hface representative := by
  let items := slabObservableHighSpinExteriorRepresentativeFiberEntries
    (hface := hface) (threshold := threshold) representative
  have hsubset : forall code,
      code ∈ items.map (slabObservableHighSpinExteriorEntropyCode hface) ->
        code ∈ componentAdaptiveEntropyCarrier D.extent faceId
          (slabObservableHighSpinExteriorPeelSize hface representative) := by
    intro code hcode
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hcode
    have hkey := slabObservableHighSpinExteriorRepresentativeFiberEntry_key_eq
      representative entry hentry
    have hsize :=
      slabObservableHighSpinExteriorPeelSize_eq_of_removalKey_eq
        representative entry hkey
    have hmem := componentAdaptiveEntropyCode_mem_carrier
      (entry.seed D faceId hface)
    change slabObservableHighSpinExteriorEntropyCode hface entry ∈
      componentAdaptiveEntropyCarrier D.extent faceId
        (slabObservableHighSpinExteriorPeelSize hface entry) at hmem
    rw [← hsize] at hmem
    exact hmem
  have hbound := nodup_subset_length_le
    (items.map (slabObservableHighSpinExteriorEntropyCode hface))
    (componentAdaptiveEntropyCarrier D.extent faceId
      (slabObservableHighSpinExteriorPeelSize hface representative))
    (slabObservableHighSpinExteriorRepresentativeFiberCodes_nodup
      (hface := hface) (threshold := threshold) representative)
    hsubset
  calc
    items.length =
        (items.map (slabObservableHighSpinExteriorEntropyCode hface)).length :=
      (List.length_map _).symm
    _ <= (componentAdaptiveEntropyCarrier D.extent faceId
          (slabObservableHighSpinExteriorPeelSize hface representative)).length :=
      hbound
    _ <= componentAdaptiveEntropyBase ^
          slabObservableHighSpinExteriorPeelSize hface representative :=
      componentAdaptiveEntropyCarrier_length_le _ _ _

/-! ## 4. Exact fiber partition and arbitrary-coupling contraction -/

/-- Corrected-slab data at an arbitrary nonnegative rational coupling. -/
def observableCouplingSlabPhysicalData
    (w : Q') (hw0 : (0 : Q') <= w) (cutoff half : Nat) : SlabPhysicalData :=
  { coupling := w
    coupling_nonnegative := hw0
    cutoff := cutoff
    half := half }

private theorem listQSum_map_local {A B : Type}
    (value : B -> Q') (map : A -> B) : forall items : List A,
    listQSum value (items.map map) =
      listQSum (fun item => value (map item)) items
  | [] => rfl
  | head :: tail =>
      congrArg (fun rest => value (map head) + rest)
        (listQSum_map_local value map tail)

/-- Realized localized exterior fibers recover the complete exterior source
weight exactly. -/
theorem slabObservableHighSpinExteriorRepresentativeFibers_weight_total
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold : Nat) :
    listQSum
        (fun representative =>
          listQSum
            (fun entry => slabExpandedFineSourceWeight D entry.1)
            (slabObservableHighSpinExteriorRepresentativeFiberEntries
              (hface := hface) (threshold := threshold) representative))
        (slabObservableHighSpinExteriorRepresentatives
          D faceId hface threshold) ≈
      listQSum (slabExpandedFineSourceWeight D)
        (slabObservableHighSpinExteriorSources
          D faceId hface threshold) := by
  have htotal := keyRepresentativeFibers_weight_total
    (slabObservableHighSpinExteriorEntries D faceId hface threshold)
    (fun entry => slabExpandedFineSourceWeight D entry.1)
    (SlabObservablePositiveSourceEntry.removalKey D faceId hface)
  unfold slabObservableHighSpinExteriorRepresentatives
    slabObservableHighSpinExteriorRepresentativeFiberEntries
    slabObservableHighSpinExteriorSources
  simp only [listQSum_map_local]
  exact htotal

/-- Every realized localized exterior fiber obeys the arbitrary-coupling
strict `(8/25)^n` bound against its concrete representative target. -/
theorem slabObservableHighSpinExteriorRepresentativeFiber_weight_sum_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (representative : SlabObservablePositiveSourceEntry D faceId) :
    listQSum
        (fun entry => slabExpandedFineSourceWeight D entry.1)
        (slabObservableHighSpinExteriorRepresentativeFiberEntries
          (hface := hface) (threshold := anchorPaidExteriorThreshold w)
            representative) <=
      componentAdaptiveEntropyAnchorRatio ^
          slabObservableHighSpinExteriorPeelSize hface representative *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinExteriorTarget hface representative) := by
  subst D
  apply fixedCardinalityWeightedSum_le
  · exact slabObservableHighSpinExteriorRepresentativeFiberEntries_length_le
      (hface := hface) (threshold := anchorPaidExteriorThreshold w)
        representative
  · decide
  · exact retainedFineIntertwinerPhysicalFiberWeight_nonnegative
      (Q'.le_of_lt hw0) cutoff half
      (slabObservableHighSpinExteriorTarget hface representative).1
      (slabObservableHighSpinExteriorTarget hface representative).2
  · intro entry hentry
    have hentryExterior : entry ∈
        slabObservableHighSpinExteriorEntries
          (observableCouplingSlabPhysicalData
            w (Q'.le_of_lt hw0) cutoff half)
          faceId hface (anchorPaidExteriorThreshold w) :=
      (List.mem_filter.mp hentry).1
    have hreserve := slabObservableHighSpinExteriorEntry_reserve_paid
      entry hentryExterior
    have hkey :=
      slabObservableHighSpinExteriorRepresentativeFiberEntry_key_eq
        representative entry hentry
    have hpeel :=
      slabObservableHighSpinExteriorPeelSize_eq_of_removalKey_eq
        representative entry hkey
    have htarget :=
      slabObservableHighSpinExteriorTarget_eq_of_removalKey_eq
        representative entry hkey
    have hweight :=
      SlabFusionWitnessFaceStrandSeed.expandedFiberWeight_anchorPaidExterior_le
        hw0 hw1 cutoff half
          (entry.seed
            (observableCouplingSlabPhysicalData
              w (Q'.le_of_lt hw0) cutoff half)
            faceId hface)
          hreserve
          (slabObservableHighSpinExteriorEntry_bounded entry)
    have hentryWeight :
        slabExpandedFineSourceWeight
            (observableCouplingSlabPhysicalData
              w (Q'.le_of_lt hw0) cutoff half) entry.1 <=
          anchorFaceCoefficient ^
              slabObservableHighSpinExteriorPeelSize hface entry *
            slabExpandedFineSourceWeight
              (observableCouplingSlabPhysicalData
                w (Q'.le_of_lt hw0) cutoff half)
              (slabObservableHighSpinExteriorTarget hface entry) := by
      change
        retainedFineIntertwinerPhysicalFiberWeight
            (observableCouplingSlabPhysicalData
              w (Q'.le_of_lt hw0) cutoff half) entry.1.1 entry.1.2 <=
          anchorFaceCoefficient ^
              (SlabFusionWitnessFaceStrandSeed.peelFaces
                (entry.seed
                  (observableCouplingSlabPhysicalData
                    w (Q'.le_of_lt hw0) cutoff half)
                  faceId hface)).length *
            retainedFineIntertwinerPhysicalFiberWeight
              (observableCouplingSlabPhysicalData
                w (Q'.le_of_lt hw0) cutoff half)
              (SlabFusionWitnessFaceStrandSeed.lowerPhysical
                (entry.seed
                  (observableCouplingSlabPhysicalData
                    w (Q'.le_of_lt hw0) cutoff half)
                  faceId hface))
              (SlabFusionWitnessFaceStrandSeed.lowerAssignment
                (entry.seed
                  (observableCouplingSlabPhysicalData
                    w (Q'.le_of_lt hw0) cutoff half)
                  faceId hface))
      exact hweight
    calc
      slabExpandedFineSourceWeight
          (observableCouplingSlabPhysicalData
            w (Q'.le_of_lt hw0) cutoff half) entry.1 <=
          anchorFaceCoefficient ^
              slabObservableHighSpinExteriorPeelSize hface entry *
            slabExpandedFineSourceWeight
              (observableCouplingSlabPhysicalData
                w (Q'.le_of_lt hw0) cutoff half)
              (slabObservableHighSpinExteriorTarget hface entry) := hentryWeight
      _ = anchorFaceCoefficient ^
              slabObservableHighSpinExteriorPeelSize hface representative *
            slabExpandedFineSourceWeight
              (observableCouplingSlabPhysicalData
                w (Q'.le_of_lt hw0) cutoff half)
              (slabObservableHighSpinExteriorTarget hface representative) :=
        (congrArg
          (fun size => anchorFaceCoefficient ^ size *
            slabExpandedFineSourceWeight
              (observableCouplingSlabPhysicalData
                w (Q'.le_of_lt hw0) cutoff half)
              (slabObservableHighSpinExteriorTarget hface entry))
          hpeel.symm).trans
        (congrArg
          (fun target => anchorFaceCoefficient ^
              slabObservableHighSpinExteriorPeelSize hface representative *
            slabExpandedFineSourceWeight
              (observableCouplingSlabPhysicalData
                w (Q'.le_of_lt hw0) cutoff half) target)
          htarget.symm)

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A -> Q') : forall items : List A,
    (forall item, item ∈ items -> left item <= right item) ->
      listQSum left items <= listQSum right items
  | [], _ => Q'.le_refl' 0
  | item :: items, hbound =>
      Q'.add_le_add
        (hbound item List.mem_cons_self)
        (listQSum_le_termwise_local left right items
          (fun other hother =>
            hbound other (List.mem_cons_of_mem item hother)))

/-- **Localized total exterior contraction with exposed target/size sum.**
The complete fixed-root exterior weight is bounded by strict rates times the
actual lower-target weights of the realized representatives. -/
theorem slabObservableHighSpinExteriorSources_weight_sum_le_target_congestion
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (cutoff half : Nat) (D : SlabPhysicalData)
    (hD : D = observableCouplingSlabPhysicalData
      w (Q'.le_of_lt hw0) cutoff half)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges D.extent) :
    listQSum (slabExpandedFineSourceWeight D)
        (slabObservableHighSpinExteriorSources
          D faceId hface (anchorPaidExteriorThreshold w)) <=
      listQSum
        (fun representative =>
          componentAdaptiveEntropyAnchorRatio ^
              slabObservableHighSpinExteriorPeelSize hface representative *
            slabExpandedFineSourceWeight D
              (slabObservableHighSpinExteriorTarget hface representative))
        (slabObservableHighSpinExteriorRepresentatives
          D faceId hface (anchorPaidExteriorThreshold w)) := by
  have htotal :=
    slabObservableHighSpinExteriorRepresentativeFibers_weight_total
      D faceId hface (anchorPaidExteriorThreshold w)
  have hsum := listQSum_le_termwise_local
    (fun representative =>
      listQSum
        (fun entry => slabExpandedFineSourceWeight D entry.1)
        (slabObservableHighSpinExteriorRepresentativeFiberEntries
          (hface := hface) (threshold := anchorPaidExteriorThreshold w)
            representative))
    (fun representative =>
      componentAdaptiveEntropyAnchorRatio ^
          slabObservableHighSpinExteriorPeelSize hface representative *
        slabExpandedFineSourceWeight D
          (slabObservableHighSpinExteriorTarget hface representative))
    (slabObservableHighSpinExteriorRepresentatives
      D faceId hface (anchorPaidExteriorThreshold w))
    (fun representative _ =>
      slabObservableHighSpinExteriorRepresentativeFiber_weight_sum_le
        hw0 hw1 cutoff half D hD faceId hface representative)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv htotal) hsum

#print axioms slabObservableHighSpinExteriorEntries
#print axioms slabObservableHighSpinExteriorSources
#print axioms slabObservableHighSpinExteriorEntry_reserve_paid
#print axioms slabObservableHighSpinExteriorSources_nodup
#print axioms slabObservableHighSpinExteriorTarget
#print axioms slabObservableHighSpinExteriorTarget_mem
#print axioms slabObservableHighSpinExteriorPeelSize
#print axioms slabObservableHighSpinExteriorTarget_eq_of_removalKey_eq
#print axioms slabObservableHighSpinExteriorPeelSize_eq_of_removalKey_eq
#print axioms slabObservableHighSpinExteriorEntropyCode
#print axioms slabObservableHighSpinExteriorRepresentatives
#print axioms slabObservableHighSpinExteriorRepresentativeFiberEntries
#print axioms slabObservableHighSpinExteriorRepresentativeFiberSources
#print axioms slabObservableHighSpinExteriorRepresentativeFiberSources_nodup
#print axioms slabObservableHighSpinExteriorRepresentativeFiberEntry_key_eq
#print axioms slabObservableHighSpinExteriorEntry_bounded
#print axioms slabObservableHighSpinExteriorRepresentativeFiberCodes_nodup
#print axioms slabObservableHighSpinExteriorRepresentativeFiberEntries_length_le
#print axioms observableCouplingSlabPhysicalData
#print axioms slabObservableHighSpinExteriorRepresentativeFibers_weight_total
#print axioms slabObservableHighSpinExteriorRepresentativeFiber_weight_sum_le
#print axioms slabObservableHighSpinExteriorSources_weight_sum_le_target_congestion

end YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition
