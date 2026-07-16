/-
# Uniform deletion of one pinned canonical-polymer layer

For the exact cutoff-one canonical Z4 gas at the proved strong-coupling
anchor, mark every polymer containing one fixed numerical face.  This module
proves that the total marked single-polymer activity is at most `1/2`,
uniformly in the box and the face.  The generic finite-gas marked-family bound
then shows that deleting the complete pinned layer costs at most the exact
rational factor two.

The proof is finite and constructive.  Every marked polymer is injected into
its unique positive-size bucket, the unweighted size sum is dominated by the
already-proved KP-weighted sum, and the geometric tail starts at size one.
-/

import YMGap.Continuum.FiniteCompatibilityMarkedBound
import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
import YMGap.Continuum.Z4CanonicalPinnedPolymerBound

namespace YMGap.Continuum.Z4CanonicalPinnedLayerDeletion

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityMarkedBound
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.KPCriterion
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The marked layer and its finite positive-size cover -/

def canonicalContainsFaceB (rootId : Nat) (polymer : List Nat) : Bool :=
  decide (rootId ∈ polymer)

def canonicalPinnedLayerPolymers (n rootId : Nat) : List (List Nat) :=
  (canonicalSurfacePolymers n).filter (canonicalContainsFaceB rootId)

theorem mem_canonicalPinnedLayerPolymers_iff
    {n rootId : Nat} {polymer : List Nat} :
    polymer ∈ canonicalPinnedLayerPolymers n rootId ↔
      polymer ∈ canonicalSurfacePolymers n ∧ rootId ∈ polymer := by
  unfold canonicalPinnedLayerPolymers canonicalContainsFaceB
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]

def canonicalPinnedLayerActivity (n rootId : Nat) : Q' :=
  markedActivitySum (canonicalSurfaceActivity anchorCoupling n)
    (canonicalContainsFaceB rootId) (canonicalSurfacePolymers n)

def canonicalPinnedPositiveSizeLayers (n rootId : Nat) : List (List Nat) :=
  (List.range (physicalFaceEdges n).length).flatMap (fun offset =>
    canonicalPinnedSizePolymers n rootId (1 + offset))

private theorem length_le_of_mem_sublists {A : Type} :
    ∀ (ambient support : List A), support ∈ sublists ambient →
      support.length ≤ ambient.length
  | [], support, hsupport => by
      have hsingle : support ∈ ([[]] : List (List A)) := hsupport
      have heq : support = [] := List.mem_singleton.mp hsingle
      rw [heq]
      exact Nat.le_refl 0
  | head :: tail, support, hsupport => by
      rw [sublists_cons'] at hsupport
      rcases List.mem_append.mp hsupport with htail | hhead
      · have ih := length_le_of_mem_sublists tail support htail
        simp only [List.length_cons]
        omega
      · obtain ⟨rest, hrest, heq⟩ := List.mem_map.mp hhead
        rw [← heq]
        have ih := length_le_of_mem_sublists tail rest hrest
        simp only [List.length_cons]
        omega

theorem canonicalPinnedLayerPolymers_nodup (n rootId : Nat) :
    (canonicalPinnedLayerPolymers n rootId).Nodup := by
  unfold canonicalPinnedLayerPolymers
  exact List.filter_sublist.nodup (canonicalSurfacePolymers_nodup n)

theorem canonicalPinnedLayer_mem_positiveSizeLayers
    {n rootId : Nat} {polymer : List Nat}
    (hpolymer : polymer ∈ canonicalPinnedLayerPolymers n rootId) :
    polymer ∈ canonicalPinnedPositiveSizeLayers n rootId := by
  have hfacts := mem_canonicalPinnedLayerPolymers_iff.mp hpolymer
  obtain ⟨face, hface⟩ :=
    canonicalSurfacePolymers_allNonempty n polymer hfacts.1
  have hsizePos : 0 < polymer.length := by
    cases polymer with
    | nil => exact absurd hface List.not_mem_nil
    | cons head tail => simp only [List.length_cons]; omega
  have hsupport := canonicalSurfacePolymer_mem_faceSupports hfacts.1
  have hsizeLe : polymer.length ≤ (physicalFaceEdges n).length := by
    unfold cutoffOneFaceSupports at hsupport
    exact length_le_of_mem_sublists (physicalFaceEdges n) polymer hsupport
  unfold canonicalPinnedPositiveSizeLayers
  apply List.mem_flatMap.mpr
  refine ⟨polymer.length - 1, List.mem_range.mpr ?_, ?_⟩
  · omega
  · apply mem_canonicalPinnedSizePolymers_iff.mpr
    refine ⟨hfacts.1, hfacts.2, ?_⟩
    omega

/-! ## 2. Reindexing by size and dropping the KP exponential weight -/

private theorem listQSum_range_eqv_finSum (value : Nat → Q') :
    ∀ cutoff : Nat,
      listQSum value (List.range cutoff) ≈ finSum value cutoff
  | 0 => Q'.eqv_refl 0
  | cutoff + 1 => by
      rw [List.range_succ, finSum_succ]
      exact Q'.eqv_trans _ _ _
        (listQSum_append value (List.range cutoff) [cutoff])
        (Q'.add_eqv_congr'
          (listQSum_range_eqv_finSum value cutoff)
          (Q'.eqv_of_eq (Q'.add_zero' (value cutoff))))

def canonicalPinnedShiftedActivitySum
    (n rootId sizeFloor depth : Nat) : Q' :=
  finSum (fun offset =>
    canonicalPinnedSizeActivitySum n rootId (sizeFloor + offset)) depth

theorem canonicalPinnedPositiveSizeLayers_activity_eqv
    (n rootId : Nat) :
    listQSum (canonicalSurfaceActivity anchorCoupling n)
        (canonicalPinnedPositiveSizeLayers n rootId) ≈
      canonicalPinnedShiftedActivitySum n rootId 1
        (physicalFaceEdges n).length := by
  unfold canonicalPinnedPositiveSizeLayers canonicalPinnedShiftedActivitySum
  exact Q'.eqv_trans _ _ _
    (listQSum_flatMap (canonicalSurfaceActivity anchorCoupling n)
      (fun offset => canonicalPinnedSizePolymers n rootId (1 + offset))
      (List.range (physicalFaceEdges n).length))
    (listQSum_range_eqv_finSum
      (fun offset => canonicalPinnedSizeActivitySum n rootId (1 + offset))
      (physicalFaceEdges n).length)

theorem canonicalPinnedLayerActivity_le_shiftedActivitySum
    (n rootId : Nat) :
    canonicalPinnedLayerActivity n rootId ≤
      canonicalPinnedShiftedActivitySum n rootId 1
        (physicalFaceEdges n).length := by
  have hinjection :
      listQSum (canonicalSurfaceActivity anchorCoupling n)
          (canonicalPinnedLayerPolymers n rootId) ≤
        listQSum (canonicalSurfaceActivity anchorCoupling n)
          (canonicalPinnedPositiveSizeLayers n rootId) := by
    apply listQSum_le_of_injective
      (canonicalPinnedLayerPolymers n rootId)
      (canonicalPinnedPositiveSizeLayers n rootId)
      (canonicalSurfaceActivity anchorCoupling n)
      (canonicalSurfaceActivity anchorCoupling n)
      (fun polymer => polymer)
      (canonicalPinnedLayerPolymers_nodup n rootId)
    · intro polymer hpolymer
      exact canonicalPinnedLayer_mem_positiveSizeLayers hpolymer
    · intro left _ right _ heq
      exact heq
    · intro polymer _
      exact Q'.le_refl' _
    · intro polymer _
      exact canonicalSurfacePolymer_activity_nonnegative n polymer
  unfold canonicalPinnedLayerActivity markedActivitySum
  change listQSum (canonicalSurfaceActivity anchorCoupling n)
      (canonicalPinnedLayerPolymers n rootId) ≤ _
  exact Q'.le_trans' _ _ _ hinjection
    (Q'.le_of_eqv
      (canonicalPinnedPositiveSizeLayers_activity_eqv n rootId))

private theorem one_le_eSurrogate_pow : ∀ size : Nat,
    (1 : Q') ≤ eSurrogate ^ size
  | 0 => Q'.le_refl' 1
  | size + 1 => by
      rw [Q'.pow_succ]
      have hpow0 : (0 : Q') ≤ eSurrogate ^ size :=
        Q'.pow_nonneg eSurrogate eSurrogate_nonneg size
      have hbase : (1 : Q') ≤ eSurrogate := by
        unfold eSurrogate
        decide
      have hmul : (1 : Q') * eSurrogate ^ size ≤
          eSurrogate * eSurrogate ^ size :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ hbase hpow0
      exact Q'.le_trans' _ _ _ (one_le_eSurrogate_pow size)
        (Q'.le_trans' _ _ _
          (Q'.ge_of_eqv (Q'.one_mul_eqv (eSurrogate ^ size))) hmul)

theorem canonicalPinnedSizeActivitySum_le_weighted
    (n rootId size : Nat) :
    canonicalPinnedSizeActivitySum n rootId size ≤
      canonicalPinnedSizeWeightedActivity n rootId size := by
  unfold canonicalPinnedSizeWeightedActivity
  have hactivity0 :=
    canonicalPinnedSizeActivitySum_nonnegative n rootId size
  have hscaled :
      canonicalPinnedSizeActivitySum n rootId size * (1 : Q') ≤
        canonicalPinnedSizeActivitySum n rootId size *
          eSurrogate ^ size :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (one_le_eSurrogate_pow size) hactivity0
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (Q'.mul_one_eqv (canonicalPinnedSizeActivitySum n rootId size)))
    hscaled

theorem canonicalPinnedShiftedActivitySum_le_KPSum
    (n rootId sizeFloor depth : Nat) :
    canonicalPinnedShiftedActivitySum n rootId sizeFloor depth ≤
      canonicalPinnedShiftedKPSum n rootId sizeFloor depth := by
  unfold canonicalPinnedShiftedActivitySum canonicalPinnedShiftedKPSum
  exact YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
    (fun offset => canonicalPinnedSizeActivitySum_le_weighted
      n rootId (sizeFloor + offset)) depth

/-! ## 3. The uniform half bound and exact factor-two deletion -/

theorem two_mul_anchorEffectiveRatio_pow_one_le_half :
    Q'.ofNat 2 * anchorEffectiveRatio ^ 1 ≤
      Q'.mkPos 1 2 (by decide) := by
  decide

theorem canonicalPinnedLayerActivity_le_half (n rootId : Nat) :
    canonicalPinnedLayerActivity n rootId ≤
      Q'.mkPos 1 2 (by decide) := by
  exact Q'.le_trans' _ _ _
    (canonicalPinnedLayerActivity_le_shiftedActivitySum n rootId)
    (Q'.le_trans' _ _ _
      (canonicalPinnedShiftedActivitySum_le_KPSum n rootId 1
        (physicalFaceEdges n).length)
      (Q'.le_trans' _ _ _
        (canonicalPinnedShiftedKPSum_le_tail n rootId 1
          (physicalFaceEdges n).length)
        two_mul_anchorEffectiveRatio_pow_one_le_half))

/-- Deleting every canonical polymer that contains one fixed numerical face
changes the exact anchor partition by at most the factor two.  The constant is
independent of the box and of the chosen face identifier. -/
theorem canonicalPolymerPartition_le_two_mul_avoidingFace
    (n rootId : Nat) :
    canonicalPolymerPartition anchorCoupling n (canonicalSurfacePolymers n) ≤
      Q'.ofNat 2 *
        canonicalPolymerPartition anchorCoupling n
          ((canonicalSurfacePolymers n).filter
            (fun polymer => !(canonicalContainsFaceB rootId polymer))) := by
  unfold canonicalPolymerPartition
  exact partition_le_two_mul_avoiding_of_activitySum_le_half
    (canonicalPolymerCompatibleB n)
    (canonicalSurfaceActivity anchorCoupling n)
    (canonicalSurfacePolymer_activity_nonnegative n)
    (canonicalContainsFaceB rootId)
    (canonicalSurfacePolymers n)
    (canonicalPinnedLayerActivity_le_half n rootId)

end YMGap.Continuum.Z4CanonicalPinnedLayerDeletion

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalPinnedLayerDeletion.canonicalPinnedLayer_mem_positiveSizeLayers
#print axioms YMGap.Continuum.Z4CanonicalPinnedLayerDeletion.canonicalPinnedPositiveSizeLayers_activity_eqv
#print axioms YMGap.Continuum.Z4CanonicalPinnedLayerDeletion.canonicalPinnedLayerActivity_le_shiftedActivitySum
#print axioms YMGap.Continuum.Z4CanonicalPinnedLayerDeletion.canonicalPinnedSizeActivitySum_le_weighted
#print axioms YMGap.Continuum.Z4CanonicalPinnedLayerDeletion.canonicalPinnedLayerActivity_le_half
#print axioms YMGap.Continuum.Z4CanonicalPinnedLayerDeletion.canonicalPolymerPartition_le_two_mul_avoidingFace
