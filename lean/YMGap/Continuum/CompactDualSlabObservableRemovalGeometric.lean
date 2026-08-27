/-
# Geometric contraction of observable-rooted removal fibers

The exact deterministic partition of positive observable sources is indexed
by a lowered target and the size of the rooted component that was removed.
Every inhabited fiber has positive size.  Consequently the size-zero fiber
is literally empty, while the positive fibers carry the proved anchor rate
`(8/25)^n`.

This module sums that rate without introducing a target multiplicity.  The
literal target enumeration is already duplicate-free and its total weight is
the physical partition, so finite Fubini contracts the complete positive-face
expanded mass by the geometric constant `8/17`.

The conclusion is deliberately local and finite: it is stated only at the
fixed strong-coupling anchor, for one physical face in one finite corrected
slab.  It is not a conditional posterior-variance estimate, an OS transfer
gap, a beta-uniform estimate, or a continuum statement.

Constructive contract: finite-list induction and exact rational order only.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableRemovalPartition
import YMGap.Constructive.CharacterTail

namespace YMGap.Continuum.CompactDualSlabObservableRemovalGeometric

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CharacterTail
open YMGap.Constructive.RationalTail
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The size-zero fiber vanishes -/

/-- No positive observable source can remove a component of size zero. -/
theorem slabObservablePositiveRemovalFiber_zero
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (htarget : target ∈ slabExpandedFineSources D) :
    slabObservablePositiveRemovalFiber D faceId hface target 0 = [] := by
  cases hfiber : slabObservablePositiveRemovalFiber
      D faceId hface target 0 with
  | nil => rfl
  | cons source rest =>
      have hsource : source ∈ slabObservablePositiveRemovalFiber
          D faceId hface target 0 := by
        rw [hfiber]
        exact List.mem_cons_self
      have hpos := slabObservablePositiveRemovalFiber_peelSize_pos
        D faceId hface target htarget 0 hsource
      omega

/-! ## 2. The exact positive geometric tail -/

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

private theorem finSum_succ_eqv_shift_of_zero
    (value : Nat -> Q') (hzero : value 0 ≈ 0) :
    forall count : Nat,
      finSum value (count + 1) ≈
        finSum (fun index => value (index + 1)) count
  | 0 => by
      change (0 : Q') + value 0 ≈ 0
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq (Q'.zero_add' (value 0))) hzero
  | count + 1 => by
      change
        finSum value (count + 1) + value (count + 1) ≈
          finSum (fun index => value (index + 1)) count +
            value (count + 1)
      exact Q'.add_eqv_congr'
        (finSum_succ_eqv_shift_of_zero value hzero count)
        (Q'.eqv_refl _)

private theorem listQSum_range_succ_eqv_shift_of_zero
    (value : Nat -> Q') (hzero : value 0 ≈ 0) (count : Nat) :
    listQSum value (List.range (count + 1)) ≈
      listQSum (fun index => value (index + 1)) (List.range count) := by
  exact Q'.eqv_trans _ _ _
    (listQSum_range_eqv_finSum_local value (count + 1))
    (Q'.eqv_trans _ _ _
      (finSum_succ_eqv_shift_of_zero value hzero count)
      (Q'.eqv_symm
        (listQSum_range_eqv_finSum_local
          (fun index => value (index + 1)) count)))

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

private theorem listQSum_mul_right_local {A : Type}
    (value : A -> Q') (scalar : Q') :
    forall items : List A,
      listQSum (fun item => value item * scalar) items ≈
        listQSum value items * scalar
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv scalar)
  | head :: tail => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.eqv_refl (value head * scalar))
          (listQSum_mul_right_local value scalar tail))
        (Q'.eqv_symm
          (Q'.add_mul_eqv (value head) (listQSum value tail) scalar))

/-- The positive powers of the exact adaptive anchor rate have total finite
mass at most `8/17`, uniformly in the finite truncation length. -/
theorem componentAdaptiveEntropyAnchorRatio_positiveTail_le
    (count : Nat) :
    listQSum
        (fun index => componentAdaptiveEntropyAnchorRatio ^ (index + 1))
        (List.range count) <= Q'.mkPos 8 17 (by decide) := by
  have hfinite : finSum
      (fun index => componentAdaptiveEntropyAnchorRatio ^ (index + 1))
      count <= Q'.mkPos 8 17 (by decide) := by
    apply geom_series_le
      (fun index => componentAdaptiveEntropyAnchorRatio ^ (index + 1))
      componentAdaptiveEntropyAnchorRatio
      componentAdaptiveEntropyAnchorRatio
      (Q'.mkPos 8 17 (by decide))
    · decide
    · decide
    · rw [Q'.pow_succ, Q'.pow_zero]
      exact Q'.le_of_eqv
        (Q'.mul_one_eqv componentAdaptiveEntropyAnchorRatio)
    · intro index
      rw [show index + 1 + 1 = (index + 1) + 1 by omega,
        Q'.pow_succ]
      exact Q'.le_refl' _
    · decide
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (listQSum_range_eqv_finSum_local
        (fun index => componentAdaptiveEntropyAnchorRatio ^ (index + 1))
        count))
    hfinite

/-! ## 3. Sum every positive size over one fixed target -/

/-- For one literal lowered target, summing all actual component-removal
fibers through the explicit physical ceiling costs at most `8/17` of the
target weight. -/
theorem slabObservablePositiveRemovalFiber_sizes_sum_le
    (cutoff half faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges (centralExtent half))
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (htarget : target ∈
      slabExpandedFineSources (anchorSlabPhysicalData cutoff half)) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum
        (fun peelSize =>
          listQSum (slabExpandedFineSourceWeight D)
            (slabObservablePositiveRemovalFiber
              D faceId hface target peelSize))
        (List.range (slabObservableRemovalMaxSize D + 1)) <=
      Q'.mkPos 8 17 (by decide) *
        slabExpandedFineSourceWeight D target := by
  let D := anchorSlabPhysicalData cutoff half
  let fiberWeight : Nat -> Q' := fun peelSize =>
    listQSum (slabExpandedFineSourceWeight D)
      (slabObservablePositiveRemovalFiber
        D faceId hface target peelSize)
  have hzero : fiberWeight 0 ≈ 0 := by
    unfold fiberWeight
    rw [slabObservablePositiveRemovalFiber_zero
      D faceId hface target htarget]
    exact Q'.eqv_refl 0
  have hshift :
      listQSum fiberWeight
          (List.range (slabObservableRemovalMaxSize D + 1)) ≈
        listQSum (fun index => fiberWeight (index + 1))
          (List.range (slabObservableRemovalMaxSize D)) :=
    listQSum_range_succ_eqv_shift_of_zero fiberWeight hzero
      (slabObservableRemovalMaxSize D)
  have hpoint : forall index,
      index ∈ List.range (slabObservableRemovalMaxSize D) ->
      fiberWeight (index + 1) <=
        componentAdaptiveEntropyAnchorRatio ^ (index + 1) *
          slabExpandedFineSourceWeight D target := by
    intro index _
    exact slabObservablePositiveRemovalFiber_weight_sum_le
      cutoff half faceId hface target htarget (index + 1)
  have hmono :
      listQSum (fun index => fiberWeight (index + 1))
          (List.range (slabObservableRemovalMaxSize D)) <=
        listQSum
          (fun index =>
            componentAdaptiveEntropyAnchorRatio ^ (index + 1) *
              slabExpandedFineSourceWeight D target)
          (List.range (slabObservableRemovalMaxSize D)) :=
    listQSum_mono_local _ _ _ hpoint
  have htargetNonnegative :
      (0 : Q') <= slabExpandedFineSourceWeight D target := by
    unfold D slabExpandedFineSourceWeight
    exact retainedFineIntertwinerPhysicalFiberWeight_anchor_nonnegative
      cutoff half target.1 target.2
  have htail := componentAdaptiveEntropyAnchorRatio_positiveTail_le
    (slabObservableRemovalMaxSize D)
  have hscaled :
      listQSum
          (fun index => componentAdaptiveEntropyAnchorRatio ^ (index + 1))
          (List.range (slabObservableRemovalMaxSize D)) *
          slabExpandedFineSourceWeight D target <=
        Q'.mkPos 8 17 (by decide) *
          slabExpandedFineSourceWeight D target :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ htail htargetNonnegative
  change listQSum fiberWeight
      (List.range (slabObservableRemovalMaxSize D + 1)) <= _
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hshift)
    (Q'.le_trans' _ _ _ hmono
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (listQSum_mul_right_local
            (fun index =>
              componentAdaptiveEntropyAnchorRatio ^ (index + 1))
            (slabExpandedFineSourceWeight D target)
            (List.range (slabObservableRemovalMaxSize D))))
        hscaled))

/-! ## 4. Contract the complete positive observable source mass -/

/-- **Finite anchor one-face occupation bound.**  In the literal expanded
corrected-slab measure at the fixed anchor coupling, the total unnormalized
weight of sources carrying positive spin at a chosen physical face is at
most `8/17` of the physical partition.

The estimate is uniform in the finite cutoff and slab half-width only because
the coupling is fixed definitionally to `anchorCoupling`; it makes no claim
of beta- or lattice-spacing uniformity. -/
theorem slabObservablePositiveExpandedSources_weight_le_partition
    (cutoff half faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges (centralExtent half)) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabExpandedFineSourceWeight D)
        (slabObservablePositiveExpandedSources D faceId) <=
      Q'.mkPos 8 17 (by decide) * D.physicalPartition := by
  let D := anchorSlabPhysicalData cutoff half
  let nestedFiberWeight :
      (SlabLabelling × SlabFusionWitnessAssignment) -> Q' := fun target =>
    listQSum
      (fun peelSize =>
        listQSum (slabExpandedFineSourceWeight D)
          (slabObservablePositiveRemovalFiber
            D faceId hface target peelSize))
      (List.range (slabObservableRemovalMaxSize D + 1))
  have hpartition := slabObservablePositiveRemovalFibers_weight_total
    D faceId hface
  have htarget : forall target,
      target ∈ slabExpandedFineSources D ->
      nestedFiberWeight target <=
        Q'.mkPos 8 17 (by decide) *
          slabExpandedFineSourceWeight D target := by
    intro target htargetMem
    unfold nestedFiberWeight
    exact slabObservablePositiveRemovalFiber_sizes_sum_le
      cutoff half faceId hface target htargetMem
  have hnested :
      listQSum nestedFiberWeight (slabExpandedFineSources D) <=
        listQSum
          (fun target =>
            Q'.mkPos 8 17 (by decide) *
              slabExpandedFineSourceWeight D target)
          (slabExpandedFineSources D) :=
    listQSum_mono_local _ _ _ htarget
  have hscale :
      listQSum
          (fun target =>
            Q'.mkPos 8 17 (by decide) *
              slabExpandedFineSourceWeight D target)
          (slabExpandedFineSources D) ≈
        Q'.mkPos 8 17 (by decide) *
          listQSum (slabExpandedFineSourceWeight D)
            (slabExpandedFineSources D) :=
    listQSum_mul_left
      (Q'.mkPos 8 17 (by decide))
      (slabExpandedFineSourceWeight D)
      (slabExpandedFineSources D)
  have htotal := slabExpandedFineSources_weight_total D
  change
    listQSum (slabExpandedFineSourceWeight D)
        (slabObservablePositiveExpandedSources D faceId) <=
      Q'.mkPos 8 17 (by decide) * D.physicalPartition
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hpartition)
    (Q'.le_trans' _ _ _ hnested
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ hscale
          (Q'.mul_eqv_congr_left
            (Q'.mkPos 8 17 (by decide)) _ _ htotal))))

/-- The normalized expanded mass of sources carrying positive spin at one
chosen face.  The partition-positivity witness is computed from the physical
datum itself. -/
def slabObservablePositiveExpandedMass
    (D : SlabPhysicalData) (faceId : Nat) : Q' :=
  Q'.divPos
    (listQSum (slabExpandedFineSourceWeight D)
      (slabObservablePositiveExpandedSources D faceId))
    D.physicalPartition
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)

/-- Normalized form of the finite anchor one-face occupation bound. -/
theorem slabObservablePositiveExpandedMass_le_eightSeventeenths
    (cutoff half faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges (centralExtent half)) :
    slabObservablePositiveExpandedMass
        (anchorSlabPhysicalData cutoff half) faceId <=
      Q'.mkPos 8 17 (by decide) := by
  let D := anchorSlabPhysicalData cutoff half
  unfold slabObservablePositiveExpandedMass
  apply Q'.divPos_le_of_le_mul
  exact slabObservablePositiveExpandedSources_weight_le_partition
    cutoff half faceId hface

#print axioms slabObservablePositiveRemovalFiber_zero
#print axioms componentAdaptiveEntropyAnchorRatio_positiveTail_le
#print axioms slabObservablePositiveRemovalFiber_sizes_sum_le
#print axioms slabObservablePositiveExpandedSources_weight_le_partition
#print axioms slabObservablePositiveExpandedMass
#print axioms slabObservablePositiveExpandedMass_le_eightSeventeenths

end YMGap.Continuum.CompactDualSlabObservableRemovalGeometric
