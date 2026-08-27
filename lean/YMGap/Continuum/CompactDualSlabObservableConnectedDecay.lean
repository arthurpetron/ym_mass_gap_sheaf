/-
# Geometric decay of the same-object connected component event

The connected source carrier pays a minimum component size equal to the
L-infinity endpoint separation plus one.  This module inserts that geometric
floor into the exact target/size partition and sums the shifted adaptive
anchor tail.

For a root face and target plaquette at separation `d`, the resulting
normalized connected-event mass is bounded by

    (25/17) * (8/25)^(d+1).

This is a finite corrected-slab probability bound on a literal event in the
same expanded measure.  It is not yet an equality or domination theorem for
a chosen observable covariance or OS transfer form, and it remains fixed at
the strong-coupling anchor.

Constructive contract: Boolean subfilters, exact deterministic Fubini, and
finite rational geometric summation only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableConnectedComponent

namespace YMGap.Continuum.CompactDualSlabObservableConnectedDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CharacterTail
open YMGap.Constructive.RationalTail
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableConnectedComponent
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.SepLatticeZ4Linf

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite-list arithmetic for a shifted geometric tail -/

private theorem listQSum_range_eqv_finSum_local (value : Nat -> Q') :
    forall count : Nat,
      listQSum value (List.range count) ≈ finSum value count
  | 0 => Q'.eqv_refl 0
  | count + 1 => by
      rw [List.range_succ, finSum_succ]
      exact Q'.eqv_trans _
        (listQSum value (List.range count) + listQSum value [count]) _
        (listQSum_append value (List.range count) [count])
        (Q'.add_eqv_congr'
          (listQSum_range_eqv_finSum_local value count)
          (Q'.eqv_of_eq (Q'.add_zero' (value count))))

/-- A range sum killed below `floor` is exactly the shifted finite sum above
that floor. -/
private theorem listQSum_range_floor_eqv_shifted_finSum
    (value : Nat -> Q') (floor : Nat) : forall count : Nat,
    listQSum
        (fun index => if floor <= index then value index else 0)
        (List.range count) ≈
      finSum (fun offset => value (floor + offset)) (count - floor)
  | 0 => by
      rw [Nat.zero_sub, finSum_zero]
      exact Q'.eqv_refl 0
  | count + 1 => by
      let killed : Nat -> Q' := fun index =>
        if floor <= index then value index else 0
      have happend :
          listQSum killed (List.range (count + 1)) ≈
            listQSum killed (List.range count) + killed count := by
        rw [List.range_succ]
        exact Q'.eqv_trans _ _ _
          (listQSum_append killed (List.range count) [count])
          (Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (Q'.eqv_of_eq (Q'.add_zero' (killed count))))
      refine Q'.eqv_trans _ _ _ happend ?_
      by_cases hfloor : floor <= count
      · have hsub : count + 1 - floor = (count - floor) + 1 := by
          omega
        rw [hsub, finSum_succ]
        refine Q'.add_eqv_congr'
          (listQSum_range_floor_eqv_shifted_finSum
            value floor count) ?_
        unfold killed
        rw [if_pos hfloor]
        have hindex : floor + (count - floor) = count := by omega
        rw [hindex]
        exact Q'.eqv_refl _
      · have hlt : count < floor := Nat.lt_of_not_ge hfloor
        have hsubLeft : count - floor = 0 := by omega
        have hsubRight : count + 1 - floor = 0 := by omega
        rw [hsubRight, finSum_zero]
        unfold killed
        rw [if_neg hfloor]
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (listQSum_range_floor_eqv_shifted_finSum
              value floor count)
            (Q'.eqv_refl 0)) ?_
        rw [hsubLeft, finSum_zero]
        exact Q'.eqv_of_eq (Q'.add_zero' 0)

/-- All finite partial sums of the adaptive anchor powers, beginning at
exponent zero, are bounded by `25/17 = 1/(1-8/25)`. -/
theorem componentAdaptiveEntropyAnchorRatio_fullTail_le (count : Nat) :
    listQSum (fun index => componentAdaptiveEntropyAnchorRatio ^ index)
        (List.range count) <= Q'.mkPos 25 17 (by decide) := by
  have hfinite : finSum
      (fun index => componentAdaptiveEntropyAnchorRatio ^ index) count <=
        Q'.mkPos 25 17 (by decide) := by
    apply geom_series_le
      (fun index => componentAdaptiveEntropyAnchorRatio ^ index)
      1 componentAdaptiveEntropyAnchorRatio
      (Q'.mkPos 25 17 (by decide))
    · decide
    · decide
    · rw [Q'.pow_zero]
      exact Q'.le_refl' 1
    · intro index
      rw [show index + 1 = index + 1 by rfl, Q'.pow_succ]
      exact Q'.le_refl' _
    · decide
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (listQSum_range_eqv_finSum_local
        (fun index => componentAdaptiveEntropyAnchorRatio ^ index) count))
    hfinite

/-- The finite geometric mass at exponents at least `floor` is bounded by
the exact shifted tail `(25/17) * (8/25)^floor`. -/
theorem componentAdaptiveEntropyAnchorRatio_shiftedTail_le
    (floor count : Nat) :
    listQSum
        (fun index =>
          if floor <= index then
            componentAdaptiveEntropyAnchorRatio ^ index
          else 0)
        (List.range count) <=
      Q'.mkPos 25 17 (by decide) *
        componentAdaptiveEntropyAnchorRatio ^ floor := by
  let shiftedCount := count - floor
  have hshift := listQSum_range_floor_eqv_shifted_finSum
    (fun index => componentAdaptiveEntropyAnchorRatio ^ index)
    floor count
  have hback := Q'.eqv_symm
    (listQSum_range_eqv_finSum_local
      (fun offset =>
        componentAdaptiveEntropyAnchorRatio ^ (floor + offset))
      shiftedCount)
  have hsplit :
      listQSum
          (fun offset =>
            componentAdaptiveEntropyAnchorRatio ^ (floor + offset))
          (List.range shiftedCount) ≈
        listQSum
          (fun offset =>
            componentAdaptiveEntropyAnchorRatio ^ floor *
              componentAdaptiveEntropyAnchorRatio ^ offset)
          (List.range shiftedCount) := by
    apply listQSum_congr
    intro offset
    exact Q'.pow_add_eqv componentAdaptiveEntropyAnchorRatio floor offset
  have hfactor := listQSum_mul_left
    (componentAdaptiveEntropyAnchorRatio ^ floor)
    (fun offset => componentAdaptiveEntropyAnchorRatio ^ offset)
    (List.range shiftedCount)
  have hbase := componentAdaptiveEntropyAnchorRatio_fullTail_le shiftedCount
  have hscaled :
      componentAdaptiveEntropyAnchorRatio ^ floor *
          listQSum
            (fun offset => componentAdaptiveEntropyAnchorRatio ^ offset)
            (List.range shiftedCount) <=
        componentAdaptiveEntropyAnchorRatio ^ floor *
          Q'.mkPos 25 17 (by decide) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hbase
      (Q'.pow_nonneg componentAdaptiveEntropyAnchorRatio (by decide) floor)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hshift
        (Q'.eqv_trans _ _ _ hback
          (Q'.eqv_trans _ _ _ hsplit hfactor))))
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv
          (componentAdaptiveEntropyAnchorRatio ^ floor)
          (Q'.mkPos 25 17 (by decide)))))

/-! ## 2. Connected fixed-key fibers -/

private theorem filter_and_eq_filter_filter_local {A : Type}
    (first second : A -> Bool) (ambient : List A) :
    ambient.filter (fun item => first item && second item) =
      (ambient.filter first).filter second := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (first item) (second item)

private theorem fiberWeight_filter_le_local
    {A B : Type} [DecidableEq B]
    (source : List A) (weight : A -> Q') (code : A -> B)
    (selected : B) (keep : A -> Bool)
    (hweight : forall item, (0 : Q') <= weight item) :
    fiberWeight (source.filter keep) weight code selected <=
      fiberWeight source weight code selected := by
  unfold fiberWeight
  rw [← filter_and_eq_filter_filter_local]
  exact listQSum_filter_le_filter weight
    (fun item => keep item && decide (selected = code item))
    (fun item => decide (selected = code item))
    hweight
    (fun item hboth => by
      cases hkeep : keep item <;>
        cases hkey : decide (selected = code item) <;>
        simp [hkeep, hkey] at hboth ⊢)
    source

/-- Below the root-to-target separation floor, a connected deterministic key
fiber is literally empty. -/
theorem slabObservableConnectedKeyFiber_empty_of_lt
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (targetPlaquette : Z4Plaq)
    (loweredTarget : SlabLabelling × SlabFusionWitnessAssignment)
    (peelSize : Nat)
    (hsmall : peelSize <
      linfDist (slabPlaquetteAt D.extent rootFaceId) targetPlaquette + 1) :
    (slabObservableConnectedSourceEntries
        D rootFaceId hroot targetPlaquette).filter
        (fun entry => decide
          (slabExpandedFineRemovalKey D loweredTarget peelSize =
            slabObservablePositiveEntryCode
              D rootFaceId hroot entry)) = [] := by
  cases hfiber :
      (slabObservableConnectedSourceEntries
        D rootFaceId hroot targetPlaquette).filter
        (fun entry => decide
          (slabExpandedFineRemovalKey D loweredTarget peelSize =
            slabObservablePositiveEntryCode
              D rootFaceId hroot entry)) with
  | nil => rfl
  | cons entry rest =>
      have hentryFiber : entry ∈
          (slabObservableConnectedSourceEntries
            D rootFaceId hroot targetPlaquette).filter
            (fun item => decide
              (slabExpandedFineRemovalKey D loweredTarget peelSize =
                slabObservablePositiveEntryCode
                  D rootFaceId hroot item)) := by
        rw [hfiber]
        exact List.mem_cons_self
      have hparts := List.mem_filter.mp hentryFiber
      have hfloor :=
        SlabObservablePositiveSourceEntry.connected_removalKey_size_floor
          D rootFaceId hroot targetPlaquette entry hparts.1
      have hkey := congrArg SlabExpandedFineRemovalKey.peelSize
        (of_decide_eq_true hparts.2)
      change peelSize =
        (entry.removalKey D rootFaceId hroot).peelSize at hkey
      omega

/-- At the production anchor, restricting a fixed removal fiber to the
connected event preserves the full `(8/25)^n` target-weight upper bound. -/
theorem slabObservableConnectedKeyFiber_weight_le
    (cutoff half rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (targetPlaquette : Z4Plaq)
    (loweredTarget : SlabLabelling × SlabFusionWitnessAssignment)
    (hloweredTarget : loweredTarget ∈
      slabExpandedFineSources (anchorSlabPhysicalData cutoff half))
    (peelSize : Nat) :
    let D := anchorSlabPhysicalData cutoff half
    fiberWeight
        (slabObservableConnectedSourceEntries
          D rootFaceId hroot targetPlaquette)
        (slabObservablePositiveEntryWeight D)
        (slabObservablePositiveEntryCode D rootFaceId hroot)
        (slabExpandedFineRemovalKey D loweredTarget peelSize) <=
      componentAdaptiveEntropyAnchorRatio ^ peelSize *
        slabExpandedFineSourceWeight D loweredTarget := by
  let D := anchorSlabPhysicalData cutoff half
  let keep : SlabObservablePositiveSourceEntry D rootFaceId -> Bool :=
    fun entry =>
      SlabObservablePositiveSourceEntry.reachesPlaquetteB
        D rootFaceId hroot entry targetPlaquette
  have hentryNonnegative : forall
      entry : SlabObservablePositiveSourceEntry D rootFaceId,
      (0 : Q') <= slabObservablePositiveEntryWeight D entry := by
    intro entry
    unfold slabObservablePositiveEntryWeight slabExpandedFineSourceWeight D
    exact retainedFineIntertwinerPhysicalFiberWeight_anchor_nonnegative
      cutoff half entry.1.1 entry.1.2
  have hsub := fiberWeight_filter_le_local
    (slabObservablePositiveSourceEntries D rootFaceId)
    (slabObservablePositiveEntryWeight D)
    (slabObservablePositiveEntryCode D rootFaceId hroot)
    (slabExpandedFineRemovalKey D loweredTarget peelSize)
    keep hentryNonnegative
  have hfull := slabObservablePositiveFiberWeight_eqv_removalFiber
    D rootFaceId hroot loweredTarget peelSize
  have hbound := slabObservablePositiveRemovalFiber_weight_sum_le
    cutoff half rootFaceId hroot loweredTarget hloweredTarget peelSize
  change fiberWeight
      (slabObservablePositiveSourceEntries D rootFaceId |>.filter keep)
      (slabObservablePositiveEntryWeight D)
      (slabObservablePositiveEntryCode D rootFaceId hroot)
      (slabExpandedFineRemovalKey D loweredTarget peelSize) <= _
  exact Q'.le_trans' _ _ _ hsub
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfull) hbound)

/-! ## 3. Sum the separation-shifted fibers -/

private theorem listQSum_mono_local {A : Type} (lower upper : A -> Q') :
    forall items : List A,
      (forall item, item ∈ items -> lower item <= upper item) ->
      listQSum lower items <= listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hbound =>
      Q'.add_le_add
        (hbound head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem =>
            hbound item (List.mem_cons_of_mem head hitem)))

/-- The explicit endpoint-separation rate at the fixed anchor. -/
def slabObservableConnectedAnchorRate
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (targetPlaquette : Z4Plaq) : Q' :=
  Q'.mkPos 25 17 (by decide) *
    componentAdaptiveEntropyAnchorRatio ^
      (linfDist (slabPlaquetteAt D.extent rootFaceId) targetPlaquette + 1)

/-- For one lowered target, the complete connected size-fiber sum is bounded
by the explicit endpoint-separation rate times that target's weight. -/
theorem slabObservableConnectedKeyFiber_sizes_sum_le
    (cutoff half rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (targetPlaquette : Z4Plaq)
    (loweredTarget : SlabLabelling × SlabFusionWitnessAssignment)
    (hloweredTarget : loweredTarget ∈
      slabExpandedFineSources (anchorSlabPhysicalData cutoff half)) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum
        (fun peelSize =>
          fiberWeight
            (slabObservableConnectedSourceEntries
              D rootFaceId hroot targetPlaquette)
            (slabObservablePositiveEntryWeight D)
            (slabObservablePositiveEntryCode D rootFaceId hroot)
            (slabExpandedFineRemovalKey
              D loweredTarget peelSize))
        (List.range (slabObservableRemovalMaxSize D + 1)) <=
      slabObservableConnectedAnchorRate
          D rootFaceId targetPlaquette *
        slabExpandedFineSourceWeight D loweredTarget := by
  let D := anchorSlabPhysicalData cutoff half
  let floor :=
    linfDist (slabPlaquetteAt D.extent rootFaceId) targetPlaquette + 1
  let connectedFiber : Nat -> Q' := fun peelSize =>
    fiberWeight
      (slabObservableConnectedSourceEntries
        D rootFaceId hroot targetPlaquette)
      (slabObservablePositiveEntryWeight D)
      (slabObservablePositiveEntryCode D rootFaceId hroot)
      (slabExpandedFineRemovalKey D loweredTarget peelSize)
  let retainedRate : Nat -> Q' := fun peelSize =>
    if floor <= peelSize then
      componentAdaptiveEntropyAnchorRatio ^ peelSize
    else 0
  have hpoint : forall peelSize,
      peelSize ∈ List.range (slabObservableRemovalMaxSize D + 1) ->
      connectedFiber peelSize <=
        retainedRate peelSize *
          slabExpandedFineSourceWeight D loweredTarget := by
    intro peelSize _
    by_cases hfloor : floor <= peelSize
    · unfold connectedFiber retainedRate
      rw [if_pos hfloor]
      exact slabObservableConnectedKeyFiber_weight_le
        cutoff half rootFaceId hroot targetPlaquette
        loweredTarget hloweredTarget peelSize
    · have hsmall : peelSize < floor := Nat.lt_of_not_ge hfloor
      have hempty := slabObservableConnectedKeyFiber_empty_of_lt
        D rootFaceId hroot targetPlaquette loweredTarget peelSize hsmall
      unfold connectedFiber fiberWeight retainedRate
      rw [hempty, if_neg hfloor]
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.zero_mul_eqv (slabExpandedFineSourceWeight D loweredTarget)))
  have hmono :
      listQSum connectedFiber
          (List.range (slabObservableRemovalMaxSize D + 1)) <=
        listQSum
          (fun peelSize =>
            retainedRate peelSize *
              slabExpandedFineSourceWeight D loweredTarget)
          (List.range (slabObservableRemovalMaxSize D + 1)) :=
    listQSum_mono_local _ _ _ hpoint
  have hfactor := listQSum_mul_right
    retainedRate (slabExpandedFineSourceWeight D loweredTarget)
    (List.range (slabObservableRemovalMaxSize D + 1))
  have htail :
      listQSum retainedRate
          (List.range (slabObservableRemovalMaxSize D + 1)) <=
        Q'.mkPos 25 17 (by decide) *
          componentAdaptiveEntropyAnchorRatio ^ floor := by
    unfold retainedRate
    exact componentAdaptiveEntropyAnchorRatio_shiftedTail_le
      floor (slabObservableRemovalMaxSize D + 1)
  have htargetNonnegative :
      (0 : Q') <= slabExpandedFineSourceWeight D loweredTarget := by
    unfold D slabExpandedFineSourceWeight
    exact retainedFineIntertwinerPhysicalFiberWeight_anchor_nonnegative
      cutoff half loweredTarget.1 loweredTarget.2
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    _ _ (slabExpandedFineSourceWeight D loweredTarget)
    htail htargetNonnegative
  change listQSum connectedFiber
      (List.range (slabObservableRemovalMaxSize D + 1)) <=
    slabObservableConnectedAnchorRate D rootFaceId targetPlaquette *
      slabExpandedFineSourceWeight D loweredTarget
  unfold slabObservableConnectedAnchorRate
  exact Q'.le_trans' _ _ _ hmono
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) hscaled)

/-! ## 4. Normalize the complete connected event -/

/-- The complete unnormalized connected-event weight is bounded by the
endpoint-separation rate times the genuine physical partition. -/
theorem slabObservableConnectedSourceEntries_weight_le_partition
    (cutoff half rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (targetPlaquette : Z4Plaq) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabObservablePositiveEntryWeight D)
        (slabObservableConnectedSourceEntries
          D rootFaceId hroot targetPlaquette) <=
      slabObservableConnectedAnchorRate
        D rootFaceId targetPlaquette * D.physicalPartition := by
  let D := anchorSlabPhysicalData cutoff half
  let connectedTargetFiberWeight :
      (SlabLabelling × SlabFusionWitnessAssignment) -> Q' :=
    fun loweredTarget =>
      listQSum
        (fun peelSize =>
          fiberWeight
            (slabObservableConnectedSourceEntries
              D rootFaceId hroot targetPlaquette)
            (slabObservablePositiveEntryWeight D)
            (slabObservablePositiveEntryCode D rootFaceId hroot)
            (slabExpandedFineRemovalKey
              D loweredTarget peelSize))
        (List.range (slabObservableRemovalMaxSize D + 1))
  have hpartition :=
    slabObservableConnectedSourceEntries_nestedFiberWeight_total
      D rootFaceId hroot targetPlaquette
  have htarget : forall loweredTarget,
      loweredTarget ∈ slabExpandedFineSources D ->
      connectedTargetFiberWeight loweredTarget <=
        slabObservableConnectedAnchorRate
            D rootFaceId targetPlaquette *
          slabExpandedFineSourceWeight D loweredTarget := by
    intro loweredTarget hloweredTarget
    unfold connectedTargetFiberWeight
    exact slabObservableConnectedKeyFiber_sizes_sum_le
      cutoff half rootFaceId hroot targetPlaquette
      loweredTarget hloweredTarget
  have hnested :
      listQSum connectedTargetFiberWeight
          (slabExpandedFineSources D) <=
        listQSum
          (fun loweredTarget =>
            slabObservableConnectedAnchorRate
                D rootFaceId targetPlaquette *
              slabExpandedFineSourceWeight D loweredTarget)
          (slabExpandedFineSources D) :=
    listQSum_mono_local _ _ _ htarget
  have hscale := listQSum_mul_left
    (slabObservableConnectedAnchorRate D rootFaceId targetPlaquette)
    (slabExpandedFineSourceWeight D)
    (slabExpandedFineSources D)
  have htotal := slabExpandedFineSources_weight_total D
  change
    listQSum (slabObservablePositiveEntryWeight D)
        (slabObservableConnectedSourceEntries
          D rootFaceId hroot targetPlaquette) <=
      slabObservableConnectedAnchorRate
        D rootFaceId targetPlaquette * D.physicalPartition
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hpartition)
    (Q'.le_trans' _ _ _ hnested
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ hscale
          (Q'.mul_eqv_congr_left
            (slabObservableConnectedAnchorRate
              D rootFaceId targetPlaquette) _ _ htotal))))

/-- Normalized mass of the literal event that the canonical rooted component
reaches the chosen target plaquette. -/
def slabObservableConnectedMass
    (D : SlabPhysicalData) (rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges D.extent)
    (targetPlaquette : Z4Plaq) : Q' :=
  Q'.divPos
    (listQSum (slabObservablePositiveEntryWeight D)
      (slabObservableConnectedSourceEntries
        D rootFaceId hroot targetPlaquette))
    D.physicalPartition
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)

/-- **Finite same-object connected-event decay.**  At the fixed anchor, the
probability that the canonical component rooted at a chosen face reaches a
target plaquette decays geometrically in their genuine Z4 L-infinity
separation. -/
theorem slabObservableConnectedMass_le_anchorRate
    (cutoff half rootFaceId : Nat)
    (hroot : rootFaceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (targetPlaquette : Z4Plaq) :
    slabObservableConnectedMass
        (anchorSlabPhysicalData cutoff half)
        rootFaceId hroot targetPlaquette <=
      slabObservableConnectedAnchorRate
        (anchorSlabPhysicalData cutoff half)
        rootFaceId targetPlaquette := by
  unfold slabObservableConnectedMass
  apply Q'.divPos_le_of_le_mul
  exact slabObservableConnectedSourceEntries_weight_le_partition
    cutoff half rootFaceId hroot targetPlaquette

#print axioms componentAdaptiveEntropyAnchorRatio_fullTail_le
#print axioms componentAdaptiveEntropyAnchorRatio_shiftedTail_le
#print axioms slabObservableConnectedKeyFiber_empty_of_lt
#print axioms slabObservableConnectedKeyFiber_weight_le
#print axioms slabObservableConnectedAnchorRate
#print axioms slabObservableConnectedKeyFiber_sizes_sum_le
#print axioms slabObservableConnectedSourceEntries_weight_le_partition
#print axioms slabObservableConnectedMass
#print axioms slabObservableConnectedMass_le_anchorRate

end YMGap.Continuum.CompactDualSlabObservableConnectedDecay
