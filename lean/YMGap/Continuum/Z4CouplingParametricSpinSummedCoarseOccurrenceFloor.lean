/-
# All-cutoff shifted coarse-cube occurrence floor

The coupling-parametric compatible support gas has the same hard-core
geometry as the anchor gas.  Below the anchor, its face-pinned activity is at
most one half, so finite contact deletion applies uniformly in the
representation cutoff.  A fundamental-spin decoration of the transported
six-face coarse cube survives every cutoff at least one.  Exact bare-coupling
matching then supplies the same positive `2^150` occurrence floor as at
cutoff one, uniformly in the containing volume.
-/

import YMGap.Continuum.FiniteCompatibilityRootInsertion
import YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence
import YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor
import YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
import YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor

namespace YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityLayerDeletion
open YMGap.Continuum.FiniteCompatibilityRootInsertion
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedUnitCubeOccurrence
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalContactLayerDeletion
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CoarseUnitCubeActivity
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CouplingParametricContactOccurrenceFloor
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UnitCubeBareCouplingShift

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic coupling-parametric spin-summed hard-core gas -/

def couplingParametricKCanonicalPolymerPartition
    (coupling : Q') (cutoff n : Nat)
    (ambient : List (List Nat)) : Q' :=
  partition (canonicalPolymerCompatibleB n)
    (couplingParametricKSupportActivity coupling cutoff n) ambient

def couplingParametricKCanonicalPolymerEventNumerator
    (coupling : Q') (cutoff n : Nat)
    (ambient : List (List Nat))
    (event : List (List Nat) → Bool) : Q' :=
  eventNumerator (canonicalPolymerCompatibleB n)
    (couplingParametricKSupportActivity coupling cutoff n) ambient event

theorem genericFamilyWeight_eq_couplingParametricK
    (coupling : Q') (cutoff n : Nat) :
    ∀ family : List (List Nat),
      familyWeight
          (couplingParametricKSupportActivity coupling cutoff n) family =
        couplingParametricKSupportFamilyActivity
          coupling cutoff n family
  | [] => rfl
  | _ :: tail => by
      change couplingParametricKSupportActivity coupling cutoff n _ *
          familyWeight
            (couplingParametricKSupportActivity coupling cutoff n) tail =
        couplingParametricKSupportActivity coupling cutoff n _ *
          couplingParametricKSupportFamilyActivity coupling cutoff n tail
      rw [genericFamilyWeight_eq_couplingParametricK
        coupling cutoff n tail]

theorem couplingParametricKCanonicalPolymerPartition_eqv_compatible
    (coupling : Q') (cutoff n : Nat) :
    couplingParametricKCanonicalPolymerPartition coupling cutoff n
        (canonicalSurfacePolymers n) ≈
      couplingParametricKCompatibleSupportGasPartition
        coupling cutoff n := by
  unfold couplingParametricKCanonicalPolymerPartition partition
    couplingParametricKCompatibleSupportGasPartition
  rw [genericCompatibleFamilies_eq_canonical]
  exact listQSum_congr
    (fun family => Q'.eqv_of_eq
      (genericFamilyWeight_eq_couplingParametricK
        coupling cutoff n family)) _

theorem couplingParametricKCanonicalPolymerEventNumerator_eqv_compatible
    (coupling : Q') (cutoff n : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKCanonicalPolymerEventNumerator coupling cutoff n
        (canonicalSurfacePolymers n) event ≈
      couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff n event := by
  unfold couplingParametricKCanonicalPolymerEventNumerator eventNumerator
    couplingParametricKCompatibleSupportEventNumerator
  rw [genericCompatibleFamilies_eq_canonical]
  exact listQSum_congr
    (fun family => Q'.eqv_of_eq
      (genericFamilyWeight_eq_couplingParametricK
        coupling cutoff n family)) _

theorem couplingParametricKCanonicalPolymerPartition_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (ambient : List (List Nat)) :
    (0 : Q') ≤
      couplingParametricKCanonicalPolymerPartition
        coupling cutoff n ambient := by
  unfold couplingParametricKCanonicalPolymerPartition
  exact partition_nonnegative
    (canonicalPolymerCompatibleB n)
    (couplingParametricKSupportActivity coupling cutoff n)
    (couplingParametricKSupportActivity_nonnegative
      hcoupling cutoff n) ambient

/-! ## 2. Contact deletion and root insertion below the anchor -/

theorem couplingParametricKCanonicalPolymerPartition_le_contactDeleted
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (cutoff n : Nat) (root : List Nat) :
    couplingParametricKCanonicalPolymerPartition coupling cutoff n
        (canonicalSurfacePolymers n) ≤
      (Q'.ofNat 2) ^
          (canonicalContactFaceCandidates n root).length *
        couplingParametricKCanonicalPolymerPartition coupling cutoff n
          (canonicalContactDeletedAmbient n root) := by
  unfold couplingParametricKCanonicalPolymerPartition
    canonicalContactDeletedAmbient
  apply partition_le_two_pow_mul_deleteMarkedLayers
    (canonicalPolymerCompatibleB n)
    (couplingParametricKSupportActivity coupling cutoff n)
    (couplingParametricKSupportActivity_nonnegative
      hcoupling cutoff n)
    (fun face polymer => canonicalContainsFaceB face polymer)
    (canonicalContactFaceCandidates n root)
    (canonicalSurfacePolymers n)
  intro face _
  change couplingParametricKCanonicalPinnedLayerActivity
      coupling cutoff n face ≤ Q'.mkPos 1 2 (by decide)
  exact couplingParametricKCanonicalPinnedLayerActivity_le_half
    hcoupling hle cutoff n face

theorem couplingParametricKRootActivity_mul_deleted_le_numerator
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {n : Nat} {root : List Nat}
    (hroot : root ∈ canonicalSurfacePolymers n) :
    couplingParametricKSupportActivity coupling cutoff n root *
        couplingParametricKCanonicalPolymerPartition coupling cutoff n
          (canonicalContactDeletedAmbient n root) ≤
      couplingParametricKCanonicalPolymerEventNumerator coupling cutoff n
        (canonicalSurfacePolymers n)
        (familyContainsPolymerB root) := by
  have hgeneric := root_weight_mul_partition_le_occurrenceNumerator
    (canonicalPolymerCompatibleB n)
    (canonicalPolymerCompatibleB_symm n)
    (couplingParametricKSupportActivity coupling cutoff n)
    (couplingParametricKSupportActivity_nonnegative
      hcoupling cutoff n)
    (canonicalSurfacePolymers n)
    (canonicalContactDeletedAmbient n root)
    root
    (canonicalSurfacePolymers_nodup n)
    (canonicalContactDeletedAmbient_nodup n root)
    hroot
    (canonicalRoot_not_mem_contactDeleted hroot)
    (fun atom hatom =>
      mem_deleteMarkedLayers_source
        (fun face candidate => canonicalContainsFaceB face candidate)
        (canonicalContactFaceCandidates n root)
        (canonicalSurfacePolymers n) atom hatom)
    (fun atom hatom =>
      canonicalContactDeletedAmbient_survivor_compatible hatom)
  have hevent :
      (fun family => memberB family root) =
        familyContainsPolymerB root := by
    funext family
    apply Bool.eq_iff_iff.mpr
    simp [memberB, familyContainsPolymerB]
  unfold couplingParametricKCanonicalPolymerPartition
    couplingParametricKCanonicalPolymerEventNumerator
  rw [← hevent]
  exact hgeneric

/-! ## 3. The fundamental root term survives every cutoff -/

theorem canonicalSurfaceActivity_le_couplingParametricKSupportActivity
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    {cutoff n : Nat} (hcutoff : 1 ≤ cutoff)
    {support : List Nat} (hsupport : support ∈ cutoffOneFaceSupports n) :
    canonicalSurfaceActivity coupling n support ≤
      couplingParametricKSupportActivity
        coupling cutoff n support := by
  have hone : componentLabel support ∈
      boundedEdgeLabellings 1
        (List.range (plaquetteEdgeCount n)) :=
    componentLabel_mem_explicitPhysicalLabellings_one hsupport
  have hbounded : componentLabel support ∈
      boundedEdgeLabellings cutoff
        (List.range (plaquetteEdgeCount n)) :=
    componentLabel_mem_bounded_of_one_le hcutoff hsupport
  have hfiber : componentLabel support ∈
      physicalLabellingsWithSupport cutoff n support := by
    apply mem_physicalLabellingsWithSupport_iff.mpr
    exact ⟨hbounded,
      excitedPlaquetteIds_componentLabel_eq_support hsupport⟩
  have hmember := listQSum_member_le
    (parametricKPhysicalTerm coupling cutoff n)
    (parametricKPhysicalTerm_nonnegative hcoupling cutoff n)
    (physicalLabellingsWithSupport cutoff n support) hfiber
  have hstable := parametricKPhysicalTerm_cutoff_stable
    (w := coupling) hcutoff hone
  have honeEq :
      parametricKPhysicalTerm coupling 1 n (componentLabel support) ≈
        canonicalSurfaceActivity coupling n support := by
    unfold canonicalSurfaceActivity
    exact parametricKPhysicalTerm_one_eqv_localized
      coupling n (componentLabel support)
  have hrootTerm :
      canonicalSurfaceActivity coupling n support ≈
        parametricKPhysicalTerm coupling cutoff n
          (componentLabel support) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm honeEq)
      (Q'.eqv_of_eq hstable.symm)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrootTerm) hmember

/-! ## 4. The transported coarse root has contact cost at most `2^150` -/

theorem coarseUnitCubeBlockRoot_contactCandidates_length_le_one_fifty
    {volume : Nat} (hvolume : 4 ≤ volume) :
    (canonicalContactFaceCandidates volume
      (coarseUnitCubeBlockRootAt volume)).length ≤ 150 := by
  have hraw := canonicalContactFaceCandidates_length_le volume
    (coarseUnitCubeBlockRootAt volume)
  have hrootFour : transportPolymer 2 4 coarseUnitCubeSupportIds ∈
      canonicalSurfacePolymers 4 :=
    transportPolymer_mem_canonicalSurfacePolymers (by omega)
      coarseUnitCubeSupportIds_mem_canonicalSurfacePolymers
  have hsecond :
      (transportPolymer 4 volume
        (transportPolymer 2 4 coarseUnitCubeSupportIds)).length =
          (transportPolymer 2 4 coarseUnitCubeSupportIds).length :=
    transportPolymer_length_eq hvolume
      (canonicalSurfacePolymer_mem_faceSupports hrootFour)
  have hfirst :
      (transportPolymer 2 4 coarseUnitCubeSupportIds).length =
        coarseUnitCubeSupportIds.length :=
    transportPolymer_length_eq (by omega)
      coarseUnitCubeSupportIds_mem_cutoffOneFaceSupports
  unfold coarseUnitCubeBlockRootAt at hraw
  rw [hsecond, hfirst, coarseUnitCubeSupportIds_length] at hraw
  simpa using hraw

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

theorem shiftedCoarseSpinSummedPartition_le_cost_mul_deleted
    {cutoff volume : Nat} (hvolume : 4 ≤ volume) :
    couplingParametricKCanonicalPolymerPartition
        (unitCubeBlockCoupling anchorCoupling) cutoff volume
        (canonicalSurfacePolymers volume) ≤
      activityMatchedCoarseUnitCubeOccurrenceCost *
        couplingParametricKCanonicalPolymerPartition
          (unitCubeBlockCoupling anchorCoupling) cutoff volume
          (canonicalContactDeletedAmbient volume
            (coarseUnitCubeBlockRootAt volume)) := by
  let coupling := unitCubeBlockCoupling anchorCoupling
  let root := coarseUnitCubeBlockRootAt volume
  let deleted := canonicalContactDeletedAmbient volume root
  have hcoupling : (0 : Q') ≤ coupling := by
    unfold coupling
    exact unitCubeBlockCoupling_nonnegative (by decide)
  have hraw :=
    couplingParametricKCanonicalPolymerPartition_le_contactDeleted
      hcoupling anchor_unitCubeBlockCoupling_le cutoff volume root
  have hlength :=
    coarseUnitCubeBlockRoot_contactCandidates_length_le_one_fifty hvolume
  have hpow :
      (Q'.ofNat 2) ^
          (canonicalContactFaceCandidates volume root).length ≤
        (Q'.ofNat 2) ^ 150 :=
    qpow_mono_exponent_of_one_le_local (by decide) hlength
  have hdeleted0 : (0 : Q') ≤
      couplingParametricKCanonicalPolymerPartition
        coupling cutoff volume deleted :=
    couplingParametricKCanonicalPolymerPartition_nonnegative
      hcoupling cutoff volume deleted
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hdeleted0
  unfold activityMatchedCoarseUnitCubeOccurrenceCost
  exact Q'.le_trans' _ _ _ hraw hscaled

theorem shiftedCoarse_baseActivity_le_spinSummedRootActivity
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    canonicalSurfaceActivity anchorCoupling 4
        dyadicUnitCubeSupportIds ≤
      couplingParametricKSupportActivity
        (unitCubeBlockCoupling anchorCoupling) cutoff volume
        (coarseUnitCubeBlockRootAt volume) := by
  have hrootSupport : coarseUnitCubeBlockRootAt volume ∈
      cutoffOneFaceSupports volume :=
    canonicalSurfacePolymer_mem_faceSupports
      (coarseUnitCubeBlockRootAt_mem_canonicalSurfacePolymers hvolume)
  have hactivity :
      canonicalSurfaceActivity anchorCoupling 4
          dyadicUnitCubeSupportIds ≈
        canonicalSurfaceActivity
          (unitCubeBlockCoupling anchorCoupling) volume
          (coarseUnitCubeBlockRootAt volume) := by
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (coarse_shifted_activity_eqv_dyadic_activity anchorCoupling))
      (Q'.eqv_symm
        (coarseUnitCubeBlockRootAt_activity_eqv_base
          (unitCubeBlockCoupling anchorCoupling) hvolume))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hactivity)
    (canonicalSurfaceActivity_le_couplingParametricKSupportActivity
      (unitCubeBlockCoupling_nonnegative (by decide))
      hcutoff hrootSupport)

/-! ## 5. Uniform compatible-gas and physical-law floors -/

theorem activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_spinSummedProbability
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor ≤
      couplingParametricKCompatibleSupportEventProbability
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide)) cutoff volume
        (familyContainsPolymerB
          (coarseUnitCubeBlockRootAt volume)) := by
  let coupling := unitCubeBlockCoupling anchorCoupling
  let root := coarseUnitCubeBlockRootAt volume
  let fullPartition := couplingParametricKCanonicalPolymerPartition
    coupling cutoff volume (canonicalSurfacePolymers volume)
  let deletedPartition := couplingParametricKCanonicalPolymerPartition
    coupling cutoff volume
      (canonicalContactDeletedAmbient volume root)
  let genericNumerator :=
    couplingParametricKCanonicalPolymerEventNumerator
      coupling cutoff volume (canonicalSurfacePolymers volume)
      (familyContainsPolymerB root)
  let gasPartition := couplingParametricKCompatibleSupportGasPartition
    coupling cutoff volume
  let numerator := couplingParametricKCompatibleSupportEventNumerator
    coupling cutoff volume (familyContainsPolymerB root)
  have hcoupling : (0 : Q') ≤ coupling := by
    unfold coupling
    exact unitCubeBlockCoupling_nonnegative (by decide)
  have hroot : root ∈ canonicalSurfacePolymers volume := by
    unfold root
    exact coarseUnitCubeBlockRootAt_mem_canonicalSurfacePolymers hvolume
  have hdeleted0 : (0 : Q') ≤ deletedPartition := by
    unfold deletedPartition
    exact couplingParametricKCanonicalPolymerPartition_nonnegative
      hcoupling cutoff volume _
  have hpartition : fullPartition ≤
      activityMatchedCoarseUnitCubeOccurrenceCost * deletedPartition := by
    unfold fullPartition deletedPartition root
    exact shiftedCoarseSpinSummedPartition_le_cost_mul_deleted hvolume
  have hinsertion :
      couplingParametricKSupportActivity coupling cutoff volume root *
          deletedPartition ≤ genericNumerator := by
    unfold deletedPartition genericNumerator
    exact couplingParametricKRootActivity_mul_deleted_le_numerator
      hcoupling cutoff hroot
  have hbaseRoot :
      canonicalSurfaceActivity anchorCoupling 4 dyadicUnitCubeSupportIds ≤
        couplingParametricKSupportActivity
          coupling cutoff volume root := by
    unfold coupling root
    exact shiftedCoarse_baseActivity_le_spinSummedRootActivity
      hcutoff hvolume
  have hbaseInsertion :
      canonicalSurfaceActivity anchorCoupling 4 dyadicUnitCubeSupportIds *
          deletedPartition ≤ genericNumerator :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hbaseRoot hdeleted0)
      hinsertion
  have hfloor0 : (0 : Q') ≤
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor :=
    Q'.le_of_lt activityMatchedCoarseUnitCubeUniformOccurrenceFloor_pos
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    hpartition hfloor0
  have hcollapse :
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor *
          (activityMatchedCoarseUnitCubeOccurrenceCost * deletedPartition) ≈
        canonicalSurfaceActivity anchorCoupling 4
          dyadicUnitCubeSupportIds * deletedPartition := by
    refine Q'.eqv_trans _
      ((activityMatchedCoarseUnitCubeUniformOccurrenceFloor *
          activityMatchedCoarseUnitCubeOccurrenceCost) *
        deletedPartition) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    apply Q'.mul_eqv_congr_right
    unfold activityMatchedCoarseUnitCubeUniformOccurrenceFloor
    exact Q'.divPos_mul_eqv _ _
      activityMatchedCoarseUnitCubeOccurrenceCost_pos
  have hgeneric :
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor *
          fullPartition ≤ genericNumerator :=
    Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollapse) hbaseInsertion)
  have hfullGas : fullPartition ≈ gasPartition := by
    unfold fullPartition gasPartition
    exact couplingParametricKCanonicalPolymerPartition_eqv_compatible
      coupling cutoff volume
  have hgenericNumerator : genericNumerator ≈ numerator := by
    unfold genericNumerator numerator
    exact couplingParametricKCanonicalPolymerEventNumerator_eqv_compatible
      coupling cutoff volume (familyContainsPolymerB root)
  have hmul :
      activityMatchedCoarseUnitCubeUniformOccurrenceFloor * gasPartition ≤
        numerator :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          activityMatchedCoarseUnitCubeUniformOccurrenceFloor
          gasPartition fullPartition (Q'.eqv_symm hfullGas)))
      (Q'.le_trans' _ _ _ hgeneric
        (Q'.le_of_eqv hgenericNumerator))
  unfold couplingParametricKCompatibleSupportEventProbability
  exact Q'.le_divPos_of_mul_le numerator gasPartition
    (couplingParametricKCompatibleSupportGasPartition_pos
      hcoupling cutoff volume) hmul

theorem activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_allCutoffPhysicalProbability
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor ≤
      couplingKFamilyEventProbability
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide)) cutoff volume
        (familyContainsPolymerB
          (coarseUnitCubeBlockRootAt volume)) := by
  have hcompatible :=
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_spinSummedProbability
      hcutoff hvolume
  have hbridge := couplingKFamilyEventProbability_eqv_compatible
    (unitCubeBlockCoupling anchorCoupling)
    (unitCubeBlockCoupling_nonnegative (by decide)) cutoff volume
    (familyContainsPolymerB (coarseUnitCubeBlockRootAt volume))
  exact Q'.le_trans' _ _ _ hcompatible (Q'.ge_of_eqv hbridge)

/-- Production block-coordinate form of the all-cutoff shifted coarse floor. -/
theorem activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_blockCoarseProbability
    {cutoff volume : Nat} (hcutoff : 1 ≤ cutoff)
    (hvolume : 4 ≤ volume) :
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor ≤
      couplingKUnitCubeBlockCoarseProbability
        (unitCubeBlockCoupling anchorCoupling)
        (unitCubeBlockCoupling_nonnegative (by decide)) cutoff volume := by
  unfold couplingKUnitCubeBlockCoarseProbability
  rw [unitCubeBlock_targetCoarse_eq_occurrence]
  exact
    activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_allCutoffPhysicalProbability
      hcutoff hvolume

#print axioms genericFamilyWeight_eq_couplingParametricK
#print axioms couplingParametricKCanonicalPolymerPartition_eqv_compatible
#print axioms couplingParametricKCanonicalPolymerEventNumerator_eqv_compatible
#print axioms couplingParametricKCanonicalPolymerPartition_nonnegative
#print axioms couplingParametricKCanonicalPolymerPartition_le_contactDeleted
#print axioms couplingParametricKRootActivity_mul_deleted_le_numerator
#print axioms canonicalSurfaceActivity_le_couplingParametricKSupportActivity
#print axioms coarseUnitCubeBlockRoot_contactCandidates_length_le_one_fifty
#print axioms shiftedCoarseSpinSummedPartition_le_cost_mul_deleted
#print axioms shiftedCoarse_baseActivity_le_spinSummedRootActivity
#print axioms activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_spinSummedProbability
#print axioms activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_allCutoffPhysicalProbability
#print axioms activityMatchedCoarseUnitCubeUniformOccurrenceFloor_le_blockCoarseProbability

end YMGap.Continuum.Z4CouplingParametricSpinSummedCoarseOccurrenceFloor
