/-
# Two-face geometric contraction of observable-rooted removal fibers

Every rooted physical strand component contains both the root endpoint and
the opposite endpoint of one displayed physical strand edge.  Those endpoints
lie on distinct faces.  The component-removal size is therefore at least two,
so both the size-zero and size-one removal fibers vanish.

Starting the already proved anchor geometric series at size two sharpens the
one-face occupation constant from `8/17` to `64/425`.  The conclusion remains
only a finite-volume statement at the named SU(2) strong-coupling anchor; it
does not assert beta-, lattice-spacing-, or continuum-uniformity.

Constructive contract: typed strand endpoints, finite-list induction, and
exact rational order only.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableRemovalGeometric

namespace YMGap.Continuum.CompactDualSlabObservableRemovalTwoFaceGeometric

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CharacterTail
open YMGap.Constructive.RationalTail
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalGeometric
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The size-one fiber also vanishes -/

/-- No positive observable source can remove a component of size one. -/
theorem slabObservablePositiveRemovalFiber_one
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (target : SlabLabelling × SlabFusionWitnessAssignment)
    (htarget : target ∈ slabExpandedFineSources D) :
    slabObservablePositiveRemovalFiber D faceId hface target 1 = [] := by
  cases hfiber : slabObservablePositiveRemovalFiber
      D faceId hface target 1 with
  | nil => rfl
  | cons source rest =>
      have hsource : source ∈ slabObservablePositiveRemovalFiber
          D faceId hface target 1 := by
        rw [hfiber]
        exact List.mem_cons_self
      let witness := slabObservablePositiveRemovalFiber_witness
        D faceId hface target htarget 1 source hsource
      have htwo :=
        SlabFusionWitnessFaceStrandSeed.two_le_peelFaces_length witness.seed
      rw [witness.peelSize_eq] at htwo
      omega

/-! ## 2. The exact size-two geometric tail -/

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

/-- The powers of the adaptive anchor rate starting at exponent two have
total finite mass at most `64/425`. -/
theorem componentAdaptiveEntropyAnchorRatio_twoTail_le
    (count : Nat) :
    listQSum
        (fun index => componentAdaptiveEntropyAnchorRatio ^ (index + 2))
        (List.range count) <= Q'.mkPos 64 425 (by decide) := by
  have hfinite : finSum
      (fun index => componentAdaptiveEntropyAnchorRatio ^ (index + 2))
      count <= Q'.mkPos 64 425 (by decide) := by
    apply geom_series_le
      (fun index => componentAdaptiveEntropyAnchorRatio ^ (index + 2))
      (componentAdaptiveEntropyAnchorRatio ^ 2)
      componentAdaptiveEntropyAnchorRatio
      (Q'.mkPos 64 425 (by decide))
    · decide
    · decide
    · exact Q'.le_refl' _
    · intro index
      rw [show index + 1 + 2 = (index + 2) + 1 by omega,
        Q'.pow_succ]
      exact Q'.le_refl' _
    · decide
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (listQSum_range_eqv_finSum_local
        (fun index => componentAdaptiveEntropyAnchorRatio ^ (index + 2))
        count))
    hfinite

/-- Removing the first two zero terms from an arbitrary finite sequence and
then applying the size-two anchor tail is independent of the surrounding slab
data.  Keeping this case split at the generic sequence level also keeps Lean's
dependent elaboration small. -/
private theorem listQSum_range_succ_le_anchor_twoTail
    (value : Nat -> Q') (scalar : Q')
    (hzero : value 0 ≈ 0) (hone : value 1 ≈ 0)
    (hscalar : (0 : Q') <= scalar)
    (hpoint : forall index,
      value (index + 2) <=
        componentAdaptiveEntropyAnchorRatio ^ (index + 2) * scalar) :
    forall maximum : Nat,
      listQSum value (List.range (maximum + 1)) <=
        Q'.mkPos 64 425 (by decide) * scalar
  | 0 => by
      have hshift :=
        listQSum_range_succ_eqv_shift_of_zero value hzero 0
      change listQSum value (List.range (0 + 1)) ≈ 0 at hshift
      exact Q'.le_trans' _ 0 _
        (Q'.le_of_eqv hshift)
        (Q'.mul_nonneg _ _ (by decide) hscalar)
  | count + 1 => by
      have hshiftOne :=
        listQSum_range_succ_eqv_shift_of_zero value hzero (count + 1)
      have hshiftTwo :
          listQSum (fun index => value (index + 1))
              (List.range (count + 1)) ≈
            listQSum (fun index => value (index + 2))
              (List.range count) := by
        simpa [Nat.add_assoc] using
          (listQSum_range_succ_eqv_shift_of_zero
            (fun index => value (index + 1)) hone count)
      have hmono :
          listQSum (fun index => value (index + 2))
              (List.range count) <=
            listQSum
              (fun index =>
                componentAdaptiveEntropyAnchorRatio ^ (index + 2) * scalar)
              (List.range count) :=
        listQSum_mono_local _ _ _
          (fun index _ => hpoint index)
      have hscaled :
          listQSum
              (fun index =>
                componentAdaptiveEntropyAnchorRatio ^ (index + 2))
              (List.range count) * scalar <=
            Q'.mkPos 64 425 (by decide) * scalar :=
        Q'.mul_le_mul_of_nonneg_right _ _ _
          (componentAdaptiveEntropyAnchorRatio_twoTail_le count) hscalar
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (Q'.eqv_trans _ _ _ hshiftOne hshiftTwo))
        (Q'.le_trans' _ _ _ hmono
          (Q'.le_trans' _ _ _
            (Q'.le_of_eqv
              (listQSum_mul_right_local
                (fun index =>
                  componentAdaptiveEntropyAnchorRatio ^ (index + 2))
                scalar (List.range count)))
            hscaled))

/-! ## 3. Sharpened fixed-target and one-face contractions -/

/-- For one lowered target, all actual component-removal fibers cost at most
`64/425` of the target weight because sizes zero and one are impossible. -/
theorem slabObservablePositiveRemovalFiber_sizes_sum_le_sixtyFourFourTwentyFive
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
      Q'.mkPos 64 425 (by decide) *
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
  have hone : fiberWeight 1 ≈ 0 := by
    unfold fiberWeight
    rw [slabObservablePositiveRemovalFiber_one
      D faceId hface target htarget]
    exact Q'.eqv_refl 0
  have htargetNonnegative :
      (0 : Q') <= slabExpandedFineSourceWeight D target := by
    unfold D slabExpandedFineSourceWeight
    exact retainedFineIntertwinerPhysicalFiberWeight_anchor_nonnegative
      cutoff half target.1 target.2
  apply listQSum_range_succ_le_anchor_twoTail
    fiberWeight (slabExpandedFineSourceWeight D target)
    hzero hone htargetNonnegative
  intro index
  exact slabObservablePositiveRemovalFiber_weight_sum_le
    cutoff half faceId hface target htarget (index + 2)

/-- The unnormalized positive one-face mass at the SU(2) anchor is at most
`64/425` of the physical partition. -/
theorem slabObservablePositiveExpandedSources_weight_le_partition_sixtyFourFourTwentyFive
    (cutoff half faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges (centralExtent half)) :
    let D := anchorSlabPhysicalData cutoff half
    listQSum (slabExpandedFineSourceWeight D)
        (slabObservablePositiveExpandedSources D faceId) <=
      Q'.mkPos 64 425 (by decide) * D.physicalPartition := by
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
        Q'.mkPos 64 425 (by decide) *
          slabExpandedFineSourceWeight D target := by
    intro target htargetMem
    unfold nestedFiberWeight
    exact
      slabObservablePositiveRemovalFiber_sizes_sum_le_sixtyFourFourTwentyFive
        cutoff half faceId hface target htargetMem
  have hnested :
      listQSum nestedFiberWeight (slabExpandedFineSources D) <=
        listQSum
          (fun target =>
            Q'.mkPos 64 425 (by decide) *
              slabExpandedFineSourceWeight D target)
          (slabExpandedFineSources D) :=
    listQSum_mono_local _ _ _ htarget
  have hscale :
      listQSum
          (fun target =>
            Q'.mkPos 64 425 (by decide) *
              slabExpandedFineSourceWeight D target)
          (slabExpandedFineSources D) ≈
        Q'.mkPos 64 425 (by decide) *
          listQSum (slabExpandedFineSourceWeight D)
            (slabExpandedFineSources D) :=
    listQSum_mul_left
      (Q'.mkPos 64 425 (by decide))
      (slabExpandedFineSourceWeight D)
      (slabExpandedFineSources D)
  have htotal := slabExpandedFineSources_weight_total D
  change
    listQSum (slabExpandedFineSourceWeight D)
        (slabObservablePositiveExpandedSources D faceId) <=
      Q'.mkPos 64 425 (by decide) * D.physicalPartition
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hpartition)
    (Q'.le_trans' _ _ _ hnested
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ hscale
          (Q'.mul_eqv_congr_left
            (Q'.mkPos 64 425 (by decide)) _ _ htotal))))

/-- Normalized form of the sharpened finite anchor one-face bound. -/
theorem slabObservablePositiveExpandedMass_le_sixtyFourFourTwentyFive
    (cutoff half faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges (centralExtent half)) :
    slabObservablePositiveExpandedMass
        (anchorSlabPhysicalData cutoff half) faceId <=
      Q'.mkPos 64 425 (by decide) := by
  let D := anchorSlabPhysicalData cutoff half
  unfold slabObservablePositiveExpandedMass
  apply Q'.divPos_le_of_le_mul
  exact
    slabObservablePositiveExpandedSources_weight_le_partition_sixtyFourFourTwentyFive
      cutoff half faceId hface

#print axioms slabObservablePositiveRemovalFiber_one
#print axioms componentAdaptiveEntropyAnchorRatio_twoTail_le
#print axioms slabObservablePositiveRemovalFiber_sizes_sum_le_sixtyFourFourTwentyFive
#print axioms slabObservablePositiveExpandedSources_weight_le_partition_sixtyFourFourTwentyFive
#print axioms slabObservablePositiveExpandedMass_le_sixtyFourFourTwentyFive

end YMGap.Continuum.CompactDualSlabObservableRemovalTwoFaceGeometric
