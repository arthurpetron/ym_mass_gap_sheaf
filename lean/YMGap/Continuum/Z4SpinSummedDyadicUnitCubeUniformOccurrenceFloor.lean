/-
# A cutoff- and volume-uniform occurrence floor for the dyadic unit cube

The complete spin-summed compatible gas uses the same canonical hard-core
geometry as the cutoff-one anchor.  The cutoff-uniform pinned-layer estimate
therefore permits the same finite contact deletion.  A literal cutoff-one
component labelling remains present at every larger representation cutoff and
its exact weight is cutoff-stable, so the root activity is bounded below by
the already derived positive cube activity.

Combining contact deletion with weighted root insertion gives the same fixed
positive rational floor at every cutoff at least one and every box containing
the cube.  No measured constant or limiting compactness enters the proof.
-/

import YMGap.Continuum.FiniteCompatibilityRootInsertion
import YMGap.Continuum.Z4CanonicalContactLayerDeletion
import YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor
import YMGap.Continuum.Z4SpinSummedCutoffEventBridge
import YMGap.Continuum.Z4SpinSummedPinnedLayerDeletion

namespace YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityLayerDeletion
open YMGap.Continuum.FiniteCompatibilityMarkedBound
open YMGap.Continuum.FiniteCompatibilityRootInsertion
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalContactLayerDeletion
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeUniformOccurrenceFloor
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedPinnedLayerDeletion
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact generic presentation of the spin-summed gas -/

def parametricKCanonicalPolymerPartition
    (cutoff n : Nat) (ambient : List (List Nat)) : Q' :=
  partition (canonicalPolymerCompatibleB n)
    (parametricKSupportActivity cutoff n) ambient

def parametricKCanonicalPolymerEventNumerator
    (cutoff n : Nat) (ambient : List (List Nat))
    (event : List (List Nat) → Bool) : Q' :=
  eventNumerator (canonicalPolymerCompatibleB n)
    (parametricKSupportActivity cutoff n) ambient event

theorem genericFamilyWeight_eq_parametricK
    (cutoff n : Nat) : ∀ family : List (List Nat),
    familyWeight (parametricKSupportActivity cutoff n) family =
      parametricKSupportFamilyActivity cutoff n family
  | [] => rfl
  | _ :: tail => by
      change parametricKSupportActivity cutoff n _ *
          familyWeight (parametricKSupportActivity cutoff n) tail =
        parametricKSupportActivity cutoff n _ *
          parametricKSupportFamilyActivity cutoff n tail
      rw [genericFamilyWeight_eq_parametricK cutoff n tail]

theorem parametricKCanonicalPolymerPartition_eqv_compatible
    (cutoff n : Nat) :
    parametricKCanonicalPolymerPartition cutoff n
        (canonicalSurfacePolymers n) ≈
      parametricKCompatibleSupportGasPartition cutoff n := by
  unfold parametricKCanonicalPolymerPartition partition
    parametricKCompatibleSupportGasPartition
  rw [genericCompatibleFamilies_eq_canonical]
  exact listQSum_congr
    (fun family => Q'.eqv_of_eq
      (genericFamilyWeight_eq_parametricK cutoff n family)) _

theorem parametricKCanonicalPolymerEventNumerator_eqv_compatible
    (cutoff n : Nat) (event : List (List Nat) → Bool) :
    parametricKCanonicalPolymerEventNumerator cutoff n
        (canonicalSurfacePolymers n) event ≈
      parametricKCompatibleSupportEventNumerator cutoff n event := by
  unfold parametricKCanonicalPolymerEventNumerator eventNumerator
    parametricKCompatibleSupportEventNumerator
  rw [genericCompatibleFamilies_eq_canonical]
  exact listQSum_congr
    (fun family => Q'.eqv_of_eq
      (genericFamilyWeight_eq_parametricK cutoff n family)) _

theorem parametricKCanonicalPolymerPartition_nonnegative
    (cutoff n : Nat) (ambient : List (List Nat)) :
    (0 : Q') ≤ parametricKCanonicalPolymerPartition cutoff n ambient := by
  unfold parametricKCanonicalPolymerPartition
  exact partition_nonnegative
    (canonicalPolymerCompatibleB n)
    (parametricKSupportActivity cutoff n)
    (parametricKSupportActivity_nonnegative cutoff n) ambient

/-! ## 2. The cutoff-one root term survives every larger cutoff -/

theorem componentLabel_mem_bounded_of_one_le
    {cutoff n : Nat} (hcutoff : 1 ≤ cutoff)
    {support : List Nat} (hsupport : support ∈ cutoffOneFaceSupports n) :
    componentLabel support ∈
      boundedEdgeLabellings cutoff (List.range (plaquetteEdgeCount n)) := by
  have hone : componentLabel support ∈
      boundedEdgeLabellings 1 (List.range (plaquetteEdgeCount n)) := by
    exact componentLabel_mem_explicitPhysicalLabellings_one hsupport
  have hfilter := boundedEdgeLabellings_filter_cutoff hcutoff
    (List.range (plaquetteEdgeCount n)) (by
      simpa [physicalFaceEdges] using physicalFaceEdges_nodup n)
  have hfiltered : componentLabel support ∈
      (boundedEdgeLabellings cutoff
        (List.range (plaquetteEdgeCount n))).filter
          (labelWithinB 1 (List.range (plaquetteEdgeCount n))) := by
    rw [hfilter]
    exact hone
  exact (List.mem_filter.mp hfiltered).1

/-- The literal fundamental-spin labelling of a support provides a uniform
lower bound on its complete spin-summed activity. -/
theorem canonicalSurfaceActivity_le_parametricKSupportActivity
    {cutoff n : Nat} (hcutoff : 1 ≤ cutoff)
    {support : List Nat} (hsupport : support ∈ cutoffOneFaceSupports n) :
    canonicalSurfaceActivity anchorCoupling n support ≤
      parametricKSupportActivity cutoff n support := by
  have hone : componentLabel support ∈
      boundedEdgeLabellings 1 (List.range (plaquetteEdgeCount n)) :=
    componentLabel_mem_explicitPhysicalLabellings_one hsupport
  have hcut : componentLabel support ∈
      boundedEdgeLabellings cutoff (List.range (plaquetteEdgeCount n)) :=
    componentLabel_mem_bounded_of_one_le hcutoff hsupport
  have hsupportExact : componentLabel support ∈
      physicalLabellingsWithSupport cutoff n support := by
    apply mem_physicalLabellingsWithSupport_iff.mpr
    exact ⟨hcut, excitedPlaquetteIds_componentLabel_eq_support hsupport⟩
  have hmember := listQSum_member_le
    (parametricKPhysicalTerm anchorCoupling cutoff n)
    (parametricKPhysicalTerm_nonnegative (by decide) cutoff n)
    (physicalLabellingsWithSupport cutoff n support)
    hsupportExact
  have hstable := parametricKPhysicalTerm_cutoff_stable
    (w := anchorCoupling) hcutoff hone
  have honeEq :
      parametricKPhysicalTerm anchorCoupling 1 n
          (componentLabel support) ≈
        canonicalSurfaceActivity anchorCoupling n support := by
    unfold canonicalSurfaceActivity
    exact parametricKPhysicalTerm_one_eqv_localized
      anchorCoupling n (componentLabel support)
  have hrootTerm :
      canonicalSurfaceActivity anchorCoupling n support ≈
        parametricKPhysicalTerm anchorCoupling cutoff n
          (componentLabel support) := by
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm honeEq)
      (Q'.eqv_of_eq hstable.symm)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrootTerm) hmember

/-! ## 3. Cutoff-uniform contact deletion -/

theorem parametricKCanonicalPolymerPartition_le_contactDeleted
    (cutoff n : Nat) (root : List Nat) :
    parametricKCanonicalPolymerPartition cutoff n
        (canonicalSurfacePolymers n) ≤
      (Q'.ofNat 2) ^ (canonicalContactFaceCandidates n root).length *
        parametricKCanonicalPolymerPartition cutoff n
          (canonicalContactDeletedAmbient n root) := by
  unfold parametricKCanonicalPolymerPartition canonicalContactDeletedAmbient
  apply partition_le_two_pow_mul_deleteMarkedLayers
    (canonicalPolymerCompatibleB n)
    (parametricKSupportActivity cutoff n)
    (parametricKSupportActivity_nonnegative cutoff n)
    (fun face polymer => canonicalContainsFaceB face polymer)
    (canonicalContactFaceCandidates n root)
    (canonicalSurfacePolymers n)
  intro face _
  change parametricKCanonicalPinnedLayerActivity cutoff n face ≤
    Q'.mkPos 1 2 (by decide)
  exact parametricKCanonicalPinnedLayerActivity_le_half cutoff n face

private theorem qpow_le_succ_of_one_le_local {base : Q'}
    (hbase : (1 : Q') ≤ base) (exponent : Nat) :
    base ^ exponent ≤ base ^ (exponent + 1) := by
  rw [Q'.pow_succ]
  have hpow0 : (0 : Q') ≤ base ^ exponent :=
    Q'.pow_nonneg base
      (Q'.le_trans' _ _ _ Q'.zero_le_one hbase) exponent
  have hscaled : (1 : Q') * base ^ exponent ≤
      base * base ^ exponent :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hbase hpow0
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv (base ^ exponent))) hscaled

private theorem qpow_add_mono_of_one_le_local {base : Q'}
    (hbase : (1 : Q') ≤ base) (first : Nat) :
    ∀ offset : Nat, base ^ first ≤ base ^ (first + offset)
  | 0 => Q'.le_refl' _
  | offset + 1 => by
      have hindex : first + (offset + 1) =
          (first + offset) + 1 := by omega
      rw [hindex]
      exact Q'.le_trans' _ _ _
        (qpow_add_mono_of_one_le_local hbase first offset)
        (qpow_le_succ_of_one_le_local hbase (first + offset))

private theorem qpow_mono_exponent_of_one_le_local {base : Q'}
    (hbase : (1 : Q') ≤ base) {first second : Nat}
    (hle : first ≤ second) : base ^ first ≤ base ^ second := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact qpow_add_mono_of_one_le_local hbase first offset

theorem parametricKDyadicUnitCubePartition_le_cost_mul_deleted
    {cutoff n : Nat} (hn : 4 ≤ n) :
    parametricKCanonicalPolymerPartition cutoff n
        (canonicalSurfacePolymers n) ≤
      dyadicUnitCubeOccurrenceCost *
        parametricKCanonicalPolymerPartition cutoff n
          (dyadicUnitCubeContactDeletedAmbient n) := by
  have hraw := parametricKCanonicalPolymerPartition_le_contactDeleted
    cutoff n (dyadicUnitCubeSupportIdsAt n)
  have hlength :=
    dyadicUnitCubeContactFaceCandidates_length_le_six_hundred hn
  have hpow :
      (Q'.ofNat 2) ^ (dyadicUnitCubeContactFaceCandidates n).length ≤
        (Q'.ofNat 2) ^ 600 :=
    qpow_mono_exponent_of_one_le_local (by decide) hlength
  have hdeleted0 : (0 : Q') ≤
      parametricKCanonicalPolymerPartition cutoff n
        (dyadicUnitCubeContactDeletedAmbient n) :=
    parametricKCanonicalPolymerPartition_nonnegative cutoff n _
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hdeleted0
  unfold dyadicUnitCubeContactFaceCandidates at hscaled
  unfold dyadicUnitCubeContactDeletedAmbient at hraw hscaled ⊢
  unfold dyadicUnitCubeOccurrenceCost
  exact Q'.le_trans' _ _ _ hraw hscaled

/-! ## 4. Root insertion and the normalized floor -/

theorem parametricKDyadicUnitCube_rootActivity_mul_deleted_le_numerator
    {cutoff n : Nat} (hn : 4 ≤ n) :
    parametricKSupportActivity cutoff n (dyadicUnitCubeSupportIdsAt n) *
        parametricKCanonicalPolymerPartition cutoff n
          (dyadicUnitCubeContactDeletedAmbient n) ≤
      parametricKCanonicalPolymerEventNumerator cutoff n
        (canonicalSurfacePolymers n)
        (familyContainsPolymerB (dyadicUnitCubeSupportIdsAt n)) := by
  have hgeneric := root_weight_mul_partition_le_occurrenceNumerator
    (canonicalPolymerCompatibleB n)
    (canonicalPolymerCompatibleB_symm n)
    (parametricKSupportActivity cutoff n)
    (parametricKSupportActivity_nonnegative cutoff n)
    (canonicalSurfacePolymers n)
    (dyadicUnitCubeContactDeletedAmbient n)
    (dyadicUnitCubeSupportIdsAt n)
    (canonicalSurfacePolymers_nodup n)
    (dyadicUnitCubeContactDeletedAmbient_nodup n)
    (dyadicUnitCubeSupportIdsAt_mem_canonicalSurfacePolymers hn)
    (dyadicUnitCubeSupportIdsAt_not_mem_contactDeleted hn)
    (fun atom hatom =>
      dyadicUnitCubeContactDeletedAmbient_mem_source hatom)
    (fun atom hatom =>
      canonicalContactDeletedAmbient_survivor_compatible hatom)
  have hevent :
      (fun family => memberB family (dyadicUnitCubeSupportIdsAt n)) =
        familyContainsPolymerB (dyadicUnitCubeSupportIdsAt n) := by
    funext family
    apply Bool.eq_iff_iff.mpr
    simp [memberB, familyContainsPolymerB]
  unfold parametricKCanonicalPolymerPartition
    parametricKCanonicalPolymerEventNumerator
  rw [← hevent]
  exact hgeneric

/-- The cutoff-one activity used in the fixed floor is a lower bound for the
transported root activity at every physical cutoff at least one. -/
theorem dyadicUnitCube_baseActivity_le_parametricKRootActivity
    {cutoff n : Nat} (hcutoff : 1 ≤ cutoff) (hn : 4 ≤ n) :
    canonicalSurfaceActivity anchorCoupling 4 dyadicUnitCubeSupportIds ≤
      parametricKSupportActivity cutoff n
        (dyadicUnitCubeSupportIdsAt n) := by
  have htransport :
      canonicalSurfaceActivity anchorCoupling 4 dyadicUnitCubeSupportIds ≈
        canonicalSurfaceActivity anchorCoupling n
          (dyadicUnitCubeSupportIdsAt n) := by
    unfold dyadicUnitCubeSupportIdsAt
    exact canonicalSurfaceActivity_transport anchorCoupling hn
      dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports
  have hrootSupport : dyadicUnitCubeSupportIdsAt n ∈
      cutoffOneFaceSupports n :=
    canonicalSurfacePolymer_mem_faceSupports
      (dyadicUnitCubeSupportIdsAt_mem_canonicalSurfacePolymers hn)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htransport)
    (canonicalSurfaceActivity_le_parametricKSupportActivity
      hcutoff hrootSupport)

/-- Uniform in both the representation cutoff and the containing volume. -/
theorem dyadicUnitCubeUniformOccurrenceFloor_le_parametricK_probability
    {cutoff n : Nat} (hcutoff : 1 ≤ cutoff) (hn : 4 ≤ n) :
    dyadicUnitCubeUniformOccurrenceFloor ≤
      parametricKCompatibleSupportEventProbability cutoff n
        (familyContainsPolymerB (dyadicUnitCubeSupportIdsAt n)) := by
  let baseActivity := canonicalSurfaceActivity anchorCoupling 4
    dyadicUnitCubeSupportIds
  let fullPartition := parametricKCanonicalPolymerPartition cutoff n
    (canonicalSurfacePolymers n)
  let deletedPartition := parametricKCanonicalPolymerPartition cutoff n
    (dyadicUnitCubeContactDeletedAmbient n)
  let genericNumerator := parametricKCanonicalPolymerEventNumerator cutoff n
    (canonicalSurfacePolymers n)
    (familyContainsPolymerB (dyadicUnitCubeSupportIdsAt n))
  let gasPartition := parametricKCompatibleSupportGasPartition cutoff n
  let numerator := parametricKCompatibleSupportEventNumerator cutoff n
    (familyContainsPolymerB (dyadicUnitCubeSupportIdsAt n))
  have hdeleted0 : (0 : Q') ≤ deletedPartition := by
    unfold deletedPartition
    exact parametricKCanonicalPolymerPartition_nonnegative cutoff n _
  have hpartition : fullPartition ≤
      dyadicUnitCubeOccurrenceCost * deletedPartition := by
    unfold fullPartition deletedPartition
    exact parametricKDyadicUnitCubePartition_le_cost_mul_deleted hn
  have hinsertion :
      parametricKSupportActivity cutoff n
          (dyadicUnitCubeSupportIdsAt n) * deletedPartition ≤
        genericNumerator := by
    unfold deletedPartition genericNumerator
    exact parametricKDyadicUnitCube_rootActivity_mul_deleted_le_numerator hn
  have hbaseRoot : baseActivity ≤
      parametricKSupportActivity cutoff n
        (dyadicUnitCubeSupportIdsAt n) := by
    unfold baseActivity
    exact dyadicUnitCube_baseActivity_le_parametricKRootActivity hcutoff hn
  have hbaseInsertion : baseActivity * deletedPartition ≤
      genericNumerator := by
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hbaseRoot hdeleted0)
      hinsertion
  have hfloor0 : (0 : Q') ≤ dyadicUnitCubeUniformOccurrenceFloor :=
    Q'.le_of_lt dyadicUnitCubeUniformOccurrenceFloor_pos
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    hpartition hfloor0
  have hcollapse :
      dyadicUnitCubeUniformOccurrenceFloor *
          (dyadicUnitCubeOccurrenceCost * deletedPartition) ≈
        baseActivity * deletedPartition := by
    refine Q'.eqv_trans _
      ((dyadicUnitCubeUniformOccurrenceFloor *
          dyadicUnitCubeOccurrenceCost) * deletedPartition) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    apply Q'.mul_eqv_congr_right
    unfold dyadicUnitCubeUniformOccurrenceFloor baseActivity
    exact Q'.divPos_mul_eqv _ _ dyadicUnitCubeOccurrenceCost_pos
  have hgeneric : dyadicUnitCubeUniformOccurrenceFloor * fullPartition ≤
      genericNumerator :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollapse) hbaseInsertion)
  have hfullGas : fullPartition ≈ gasPartition := by
    unfold fullPartition gasPartition
    exact parametricKCanonicalPolymerPartition_eqv_compatible cutoff n
  have hgenericNumerator : genericNumerator ≈ numerator := by
    unfold genericNumerator numerator
    exact parametricKCanonicalPolymerEventNumerator_eqv_compatible
      cutoff n (familyContainsPolymerB (dyadicUnitCubeSupportIdsAt n))
  have hmul : dyadicUnitCubeUniformOccurrenceFloor * gasPartition ≤
      numerator := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left dyadicUnitCubeUniformOccurrenceFloor
          gasPartition fullPartition (Q'.eqv_symm hfullGas)))
      (Q'.le_trans' _ _ _ hgeneric
        (Q'.le_of_eqv hgenericNumerator))
  unfold parametricKCompatibleSupportEventProbability
  exact Q'.le_divPos_of_mul_le numerator gasPartition
    (parametricKCompatibleSupportGasPartition_pos cutoff n) hmul

end YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor.parametricKCanonicalPolymerPartition_eqv_compatible
#print axioms YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor.componentLabel_mem_bounded_of_one_le
#print axioms YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor.canonicalSurfaceActivity_le_parametricKSupportActivity
#print axioms YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor.parametricKCanonicalPolymerPartition_le_contactDeleted
#print axioms YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor.parametricKDyadicUnitCube_rootActivity_mul_deleted_le_numerator
#print axioms YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor.dyadicUnitCubeUniformOccurrenceFloor_le_parametricK_probability
