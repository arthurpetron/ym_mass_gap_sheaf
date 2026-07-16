/-
# Finite four-cell summation for the corrected-slab switch

The marked recoverable switch injects the separated part of
  boundary-event × supported-complement
into
  boundary-complement × supported-event.
Consequently the only uncancelled cross-product mass is the connected source
residue.  This is the exact same-volume algebra needed before the geometric
carrier estimate and normalization.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalBoundaryReverseRecovery
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderEventTransport
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalMarkedRootSeparation
open YMGap.Continuum.Z4CanonicalMarkedRootSwitch
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

abbrev PolymerFamily := List (List Nat)
abbrev RawFamilyPair := PolymerFamily × PolymerFamily

def slabMarkedCylinderEvent
    {extent : Nat} (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : PolymerFamily → Bool :=
  cylinderEvent (roots.map Subtype.val) predicate

/-! ## 1. The four finite cells -/

def slabBoundaryCylinderEventFamilyList
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : List PolymerFamily :=
  (canonicalSlabBoundaryFamilies extent).filter
    (slabMarkedCylinderEvent roots predicate)

def slabSupportedCylinderComplementFamilyList
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : List PolymerFamily :=
  (canonicalSlabSupportedFamilies extent).filter
    (fun family => !(slabMarkedCylinderEvent roots predicate family))

def slabBoundaryCylinderComplementFamilyList
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : List PolymerFamily :=
  (canonicalSlabBoundaryFamilies extent).filter
    (fun family => !(slabMarkedCylinderEvent roots predicate family))

def slabSupportedCylinderEventFamilyList
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : List PolymerFamily :=
  (canonicalSlabSupportedFamilies extent).filter
    (slabMarkedCylinderEvent roots predicate)

abbrev SlabBoundaryCylinderEventEntry
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :=
  {family : PolymerFamily // family ∈
    slabBoundaryCylinderEventFamilyList extent roots predicate}

abbrev SlabSupportedCylinderComplementEntry
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :=
  {family : PolymerFamily // family ∈
    slabSupportedCylinderComplementFamilyList extent roots predicate}

abbrev SlabCylinderSourcePair
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :=
  SlabBoundaryCylinderEventEntry extent roots predicate ×
    SlabSupportedCylinderComplementEntry extent roots predicate

def slabBoundaryCylinderEventEntries
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    List (SlabBoundaryCylinderEventEntry extent roots predicate) :=
  (slabBoundaryCylinderEventFamilyList extent roots predicate).attach

def slabSupportedCylinderComplementEntries
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    List (SlabSupportedCylinderComplementEntry extent roots predicate) :=
  (slabSupportedCylinderComplementFamilyList extent roots predicate).attach

def slabCylinderSourcePairList
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    List (SlabCylinderSourcePair extent roots predicate) :=
  cartesian
    (slabBoundaryCylinderEventEntries extent roots predicate)
    (slabSupportedCylinderComplementEntries extent roots predicate)

def slabCylinderTargetPairList
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) : List RawFamilyPair :=
  cartesian
    (slabBoundaryCylinderComplementFamilyList extent roots predicate)
    (slabSupportedCylinderEventFamilyList extent roots predicate)

def slabCylinderSourceLeftBoundary
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate) :
    pair.1.val ∈ canonicalSlabBoundaryFamilies extent :=
  (List.mem_filter.mp pair.1.property).1

def slabCylinderSourceRightSupported
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate) :
    pair.2.val ∈ canonicalSlabSupportedFamilies extent :=
  (List.mem_filter.mp pair.2.property).1

def slabCylinderSourceLeftCompatible
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate) :
    pair.1.val ∈ canonicalCompatibleAmbientFamilies (extent + 1) :=
  (mem_canonicalSlabBoundaryFamilies_iff.mp
    (slabCylinderSourceLeftBoundary pair)).1

def slabCylinderSourceRightCompatible
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate) :
    pair.2.val ∈ canonicalCompatibleAmbientFamilies (extent + 1) :=
  (mem_canonicalSlabSupportedFamilies_iff.mp
    (slabCylinderSourceRightSupported pair)).1

/-! ## 2. Connected/separated split and the switch encoder -/

def slabCylinderSourceSeparatedB
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate) : Bool :=
  !(slabBoundaryOutsideMarkedReachB
    (slabCylinderSourceLeftCompatible pair)
    (slabCylinderSourceRightCompatible pair) roots)

def separatedSlabCylinderSourcePairs
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool} :
    List (SlabCylinderSourcePair extent roots predicate) :=
  (slabCylinderSourcePairList extent roots predicate).filter
    slabCylinderSourceSeparatedB

def connectedSlabCylinderSourcePairs
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool} :
    List (SlabCylinderSourcePair extent roots predicate) :=
  (slabCylinderSourcePairList extent roots predicate).filter
    (fun pair => !(slabCylinderSourceSeparatedB pair))

def slabSeparatedCylinderSwitchEncode
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate) :
    RawFamilyPair :=
  (recoverableMarkedSwitchedLeftFamily
      (slabCylinderSourceLeftCompatible pair)
      (slabCylinderSourceRightCompatible pair) roots,
    recoverableMarkedSwitchedRightFamily
      (slabCylinderSourceLeftCompatible pair)
      (slabCylinderSourceRightCompatible pair) roots)

theorem slabSeparatedCylinderSwitchEncode_mem_target
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate)
    (hpair : pair ∈ separatedSlabCylinderSourcePairs) :
    slabSeparatedCylinderSwitchEncode pair ∈
      slabCylinderTargetPairList extent roots predicate := by
  have htest := (List.mem_filter.mp hpair).2
  have hdecision : slabBoundaryOutsideMarkedReachB
      (slabCylinderSourceLeftCompatible pair)
      (slabCylinderSourceRightCompatible pair) roots = false := by
    unfold slabCylinderSourceSeparatedB at htest
    cases hvalue : slabBoundaryOutsideMarkedReachB
        (slabCylinderSourceLeftCompatible pair)
        (slabCylinderSourceRightCompatible pair) roots <;> simp_all
  have hseparated := slabBoundaryOutsideMarkedReachB_false_separated
    (slabCylinderSourceLeftCompatible pair)
    (slabCylinderSourceRightCompatible pair) roots hdecision
  have hpackage := separated_recoverable_slab_switch anchorCoupling
    (slabCylinderSourceLeftBoundary pair)
    (slabCylinderSourceRightSupported pair) roots predicate hseparated
  apply (mem_cartesian_iff
    (slabBoundaryCylinderComplementFamilyList extent roots predicate)
    (slabSupportedCylinderEventFamilyList extent roots predicate)
    (slabSeparatedCylinderSwitchEncode pair)).2
  constructor
  · apply List.mem_filter.mpr
    refine ⟨hpackage.1, ?_⟩
    have hrightEventFalse : slabMarkedCylinderEvent roots predicate
        pair.2.val = false := by
      have hraw := (List.mem_filter.mp pair.2.property).2
      cases hvalue : slabMarkedCylinderEvent roots predicate pair.2.val <;>
        simp_all
    unfold slabMarkedCylinderEvent at hrightEventFalse ⊢
    unfold slabSeparatedCylinderSwitchEncode
    rw [hpackage.2.2.1, hrightEventFalse]
    rfl
  · apply List.mem_filter.mpr
    refine ⟨hpackage.2.1, ?_⟩
    have hleftEvent : slabMarkedCylinderEvent roots predicate
        pair.1.val = true :=
      (List.mem_filter.mp pair.1.property).2
    unfold slabMarkedCylinderEvent at hleftEvent ⊢
    unfold slabSeparatedCylinderSwitchEncode
    rw [hpackage.2.2.2.1]
    exact hleftEvent

theorem slabSeparatedCylinderSwitchEncode_injective
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (first second : SlabCylinderSourcePair extent roots predicate)
    (_hfirst : first ∈ separatedSlabCylinderSourcePairs)
    (_hsecond : second ∈ separatedSlabCylinderSourcePairs)
    (heq : slabSeparatedCylinderSwitchEncode first =
      slabSeparatedCylinderSwitchEncode second) : first = second := by
  have hleftOutput := congrArg Prod.fst heq
  have hrightOutput := congrArg Prod.snd heq
  have hsources := recoverableMarkedSwitchedFamilies_injective roots
    (slabCylinderSourceLeftCompatible first)
    (slabCylinderSourceRightCompatible first)
    (slabCylinderSourceLeftCompatible second)
    (slabCylinderSourceRightCompatible second)
    hleftOutput hrightOutput
  apply Prod.ext
  · exact Subtype.ext hsources.1
  · exact Subtype.ext hsources.2

/-! ## 3. Exact anchor-weight cancellation -/

def slabCylinderSourcePairWeight
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling (extent + 1) pair.1.val *
    canonicalSurfaceFamilyActivity anchorCoupling (extent + 1) pair.2.val

def slabCylinderRawPairWeight (extent : Nat)
    (pair : RawFamilyPair) : Q' :=
  canonicalSurfaceFamilyActivity anchorCoupling (extent + 1) pair.1 *
    canonicalSurfaceFamilyActivity anchorCoupling (extent + 1) pair.2

theorem slabSeparatedSwitchEncode_weight
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (pair : SlabCylinderSourcePair extent roots predicate) :
    slabCylinderRawPairWeight extent
        (slabSeparatedCylinderSwitchEncode pair) ≈
      slabCylinderSourcePairWeight pair := by
  exact recoverableMarkedSwitchedFamilies_weight_preserved
    anchorCoupling
    (slabCylinderSourceLeftCompatible pair)
    (slabCylinderSourceRightCompatible pair) roots

theorem slabBoundaryCylinderEventFamilyList_nodup
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    (slabBoundaryCylinderEventFamilyList
      extent roots predicate).Nodup :=
  List.filter_sublist.nodup (canonicalSlabBoundaryFamilies_nodup extent)

theorem slabSupportedCylinderComplementFamilyList_nodup
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    (slabSupportedCylinderComplementFamilyList
      extent roots predicate).Nodup :=
  List.filter_sublist.nodup (canonicalSlabSupportedFamilies_nodup extent)

theorem slabBoundaryCylinderComplementFamilyList_nodup
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    (slabBoundaryCylinderComplementFamilyList
      extent roots predicate).Nodup :=
  List.filter_sublist.nodup (canonicalSlabBoundaryFamilies_nodup extent)

theorem slabSupportedCylinderEventFamilyList_nodup
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    (slabSupportedCylinderEventFamilyList
      extent roots predicate).Nodup :=
  List.filter_sublist.nodup (canonicalSlabSupportedFamilies_nodup extent)

theorem slabCylinderSourcePairList_nodup
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    (slabCylinderSourcePairList extent roots predicate).Nodup := by
  exact cartesian_nodup _ _
    (attach_nodup_of_nodup _
      (slabBoundaryCylinderEventFamilyList_nodup
        extent roots predicate))
    (attach_nodup_of_nodup _
      (slabSupportedCylinderComplementFamilyList_nodup
        extent roots predicate))

theorem separatedSlabCylinderSourcePairs_nodup
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    (separatedSlabCylinderSourcePairs
      (extent := extent) (roots := roots)
      (predicate := predicate)).Nodup :=
  List.filter_sublist.nodup
    (slabCylinderSourcePairList_nodup extent roots predicate)

theorem slabCylinderTargetPairList_nodup
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    (slabCylinderTargetPairList extent roots predicate).Nodup :=
  cartesian_nodup _ _
    (slabBoundaryCylinderComplementFamilyList_nodup
      extent roots predicate)
    (slabSupportedCylinderEventFamilyList_nodup
      extent roots predicate)

theorem separatedSlabCylinderPairSum_le_target
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    listQSum slabCylinderSourcePairWeight
        (separatedSlabCylinderSourcePairs
          (extent := extent) (roots := roots)
          (predicate := predicate)) ≤
      listQSum (slabCylinderRawPairWeight extent)
        (slabCylinderTargetPairList extent roots predicate) := by
  apply listQSum_le_of_injective
    (separatedSlabCylinderSourcePairs
      (extent := extent) (roots := roots)
      (predicate := predicate))
    (slabCylinderTargetPairList extent roots predicate)
    slabCylinderSourcePairWeight
    (slabCylinderRawPairWeight extent)
    slabSeparatedCylinderSwitchEncode
    (separatedSlabCylinderSourcePairs_nodup extent roots predicate)
  · exact slabSeparatedCylinderSwitchEncode_mem_target
  · intro first hfirst second hsecond heq
    exact slabSeparatedCylinderSwitchEncode_injective
      first second hfirst hsecond heq
  · intro pair _
    exact Q'.le_of_eqv
      (Q'.eqv_symm (slabSeparatedSwitchEncode_weight pair))
  · intro pair _
    exact Q'.mul_nonneg _ _
      (canonicalSurfaceFamilyActivity_nonnegative (extent + 1) pair.1)
      (canonicalSurfaceFamilyActivity_nonnegative (extent + 1) pair.2)

/-! ## 4. Products, partition, and the connected residue -/

theorem slabCylinderSourcePairList_sum_eqv_product
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    listQSum slabCylinderSourcePairWeight
        (slabCylinderSourcePairList extent roots predicate) ≈
      listQSum
          (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
          (slabBoundaryCylinderEventFamilyList extent roots predicate) *
        listQSum
          (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
          (slabSupportedCylinderComplementFamilyList
            extent roots predicate) := by
  have hproduct := listQSum_cartesian_product
    (fun entry : SlabBoundaryCylinderEventEntry extent roots predicate =>
      canonicalSurfaceFamilyActivity anchorCoupling
        (extent + 1) entry.val)
    (fun entry : SlabSupportedCylinderComplementEntry
        extent roots predicate =>
      canonicalSurfaceFamilyActivity anchorCoupling
        (extent + 1) entry.val)
    (slabBoundaryCylinderEventEntries extent roots predicate)
    (slabSupportedCylinderComplementEntries extent roots predicate)
  unfold slabCylinderSourcePairList at hproduct ⊢
  refine Q'.eqv_trans _ _ _ hproduct ?_
  unfold slabBoundaryCylinderEventEntries
    slabSupportedCylinderComplementEntries
  rw [listQSum_attach, listQSum_attach]
  exact Q'.eqv_refl _

theorem slabCylinderTargetPairList_sum_eqv_product
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    listQSum (slabCylinderRawPairWeight extent)
        (slabCylinderTargetPairList extent roots predicate) ≈
      listQSum
          (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
          (slabBoundaryCylinderComplementFamilyList
            extent roots predicate) *
        listQSum
          (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
          (slabSupportedCylinderEventFamilyList
            extent roots predicate) := by
  exact listQSum_cartesian_product
    (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
    (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
    (slabBoundaryCylinderComplementFamilyList extent roots predicate)
    (slabSupportedCylinderEventFamilyList extent roots predicate)

theorem slabCylinderSourcePairList_partition
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    listQSum slabCylinderSourcePairWeight
        (slabCylinderSourcePairList extent roots predicate) ≈
      listQSum slabCylinderSourcePairWeight
          (separatedSlabCylinderSourcePairs
            (extent := extent) (roots := roots)
            (predicate := predicate)) +
        listQSum slabCylinderSourcePairWeight
          (connectedSlabCylinderSourcePairs
            (extent := extent) (roots := roots)
            (predicate := predicate)) := by
  exact listQSum_filter_partition
    slabCylinderSourcePairWeight slabCylinderSourceSeparatedB
    (slabCylinderSourcePairList extent roots predicate)

/-- The finite cross-product cancellation.  The right-hand residue is a
literal list sum over precisely the connected source pairs. -/
theorem slabBoundaryEvent_supportedComplement_le
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    listQSum
          (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
          (slabBoundaryCylinderEventFamilyList extent roots predicate) *
        listQSum
          (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
          (slabSupportedCylinderComplementFamilyList
            extent roots predicate) ≤
      listQSum
            (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
            (slabBoundaryCylinderComplementFamilyList
              extent roots predicate) *
          listQSum
            (canonicalSurfaceFamilyActivity anchorCoupling (extent + 1))
            (slabSupportedCylinderEventFamilyList
              extent roots predicate) +
        listQSum slabCylinderSourcePairWeight
          (connectedSlabCylinderSourcePairs
            (extent := extent) (roots := roots)
            (predicate := predicate)) := by
  have hsource := slabCylinderSourcePairList_sum_eqv_product
    extent roots predicate
  have htarget := slabCylinderTargetPairList_sum_eqv_product
    extent roots predicate
  have hpartition := slabCylinderSourcePairList_partition
    extent roots predicate
  have hinjection := separatedSlabCylinderPairSum_le_target
    extent roots predicate
  have hsepAdd := Q'.add_le_add hinjection (Q'.le_refl'
    (listQSum slabCylinderSourcePairWeight
      (connectedSlabCylinderSourcePairs
        (extent := extent) (roots := roots)
        (predicate := predicate))))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hsource))
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hpartition)
      (Q'.le_trans' _ _ _ hsepAdd
        (Q'.add_le_add (Q'.le_of_eqv htarget) (Q'.le_refl' _))))

#print axioms slabSeparatedCylinderSwitchEncode_mem_target
#print axioms slabSeparatedCylinderSwitchEncode_injective
#print axioms separatedSlabCylinderPairSum_le_target
#print axioms slabCylinderSourcePairList_sum_eqv_product
#print axioms slabCylinderSourcePairList_partition
#print axioms slabBoundaryEvent_supportedComplement_le

end YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
