/-
# Explicit coupling-parametric tail for the uniformly padded carrier

The carrier selected from every connected shifted cylinder pair is summed by
its exact union-support size.  The two path colors receive the derived
decorated face envelope; the two background colors keep their exact
coupling-parametric activities.  The resulting finite Cartesian sum factors
as the full target partition times the affine embedded partition, and the
shifted-shell size floor gives an explicit geometric tail.
-/

import YMGap.Continuum.Z4UniformShiftConnectedCarrier
import YMGap.Continuum.Z4CouplingParametricConnectedCarrierTail

namespace YMGap.Continuum.Z4UniformShiftConnectedCarrierTail

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilitySwitching
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalColoredSupportCount
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize
open YMGap.Continuum.Z4CanonicalConnectedCarrierTail
open YMGap.Continuum.Z4CanonicalConnectedCarrierWeight
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricConnectedCarrierTail
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricCylinderWeights
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ShiftedSubboxCarrierTail
open YMGap.Continuum.Z4SpinSummedColoredSupportWeight
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftConnectedCarrier
open YMGap.Continuum.Z4UniformShiftCylinderSwitchSummation
open YMGap.Continuum.Z4UniformShiftEmbeddedCylinder
open YMGap.Continuum.Z4UniformShiftEmbeddedRegion
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-! ## 1. Exact path/background factorization and envelope -/

def couplingSpinSummedUniformShiftConnectedPathPairWeight
    (coupling : Q') (cutoff : Nat)
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff (uniformPaddedBase padding base)
      (uniformShiftConnectedPathLeftFamily entry) *
    couplingParametricKSupportFamilyActivity coupling cutoff (uniformPaddedBase padding base)
      (uniformShiftConnectedPathRightFamily entry)

def couplingSpinSummedUniformShiftConnectedBackgroundPairWeight
    (coupling : Q') (cutoff : Nat)
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff (uniformPaddedBase padding base)
      (uniformShiftConnectedBackgroundLeftFamily entry) *
    couplingParametricKSupportFamilyActivity coupling cutoff (uniformPaddedBase padding base)
      (uniformShiftConnectedBackgroundRightFamily entry)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem couplingSpinSummedUniformShiftConnectedSourceWeight_factor
    (coupling : Q') (cutoff : Nat)
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    couplingSpinSummedUniformShiftCylinderSourcePairWeight
        coupling cutoff entry.val ≈
      couplingSpinSummedUniformShiftConnectedPathPairWeight
          coupling cutoff entry *
        couplingSpinSummedUniformShiftConnectedBackgroundPairWeight
          coupling cutoff entry := by
  have hleft := couplingParametricKSupportFamilyActivity_filter_partition
    coupling cutoff (uniformPaddedBase padding base) entry.val.1.val
      (uniformShiftConnectedPathTest entry)
  have hright := couplingParametricKSupportFamilyActivity_filter_partition
    coupling cutoff (uniformPaddedBase padding base) entry.val.2.val
      (uniformShiftConnectedPathTest entry)
  refine Q'.eqv_trans _ _ _ (mul_eqv_both_local hleft hright) ?_
  unfold couplingSpinSummedUniformShiftConnectedPathPairWeight
    couplingSpinSummedUniformShiftConnectedBackgroundPairWeight
    uniformShiftConnectedPathLeftFamily
    uniformShiftConnectedBackgroundLeftFamily
    uniformShiftConnectedPathRightFamily
    uniformShiftConnectedBackgroundRightFamily
  ring_qeqv

theorem uniformShiftConnectedCarrierSupport_length_le_pathFaceCount
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    (uniformShiftConnectedCarrierSupport entry).length ≤
      familyFaceCount (uniformShiftConnectedPathLeftFamily entry) +
        familyFaceCount (uniformShiftConnectedPathRightFamily entry) := by
  have hbound := familyUnionSupport_length_le_familyFaceCount
    (uniformPaddedBase padding base)
    (uniformShiftConnectedPathLeftFamily entry ++
      uniformShiftConnectedPathRightFamily entry)
  rw [familyFaceCount_append] at hbound
  exact hbound

theorem couplingSpinSummedUniformShiftConnectedPathWeight_le_supportPow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    couplingSpinSummedUniformShiftConnectedPathPairWeight
        coupling cutoff entry ≤
      anchorDecoratedFaceEnvelope ^
        (uniformShiftConnectedCarrierSupport entry).length := by
  have hleft := couplingParametricKSupportFamilyActivity_le_totalFacePow
    hcoupling hle cutoff (uniformPaddedBase padding base)
      (uniformShiftConnectedPathLeftFamily entry)
  have hright := couplingParametricKSupportFamilyActivity_le_totalFacePow
    hcoupling hle cutoff (uniformPaddedBase padding base)
      (uniformShiftConnectedPathRightFamily entry)
  have hright0 := couplingParametricKSupportFamilyActivity_nonnegative
    hcoupling cutoff (uniformPaddedBase padding base)
      (uniformShiftConnectedPathRightFamily entry)
  have hleftPow0 : (0 : Q') ≤ anchorDecoratedFaceEnvelope ^
      familyFaceCount (uniformShiftConnectedPathLeftFamily entry) :=
    Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative _
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftPow0
  have htotal : couplingSpinSummedUniformShiftConnectedPathPairWeight
      coupling cutoff entry ≤
        anchorDecoratedFaceEnvelope ^
          (familyFaceCount (uniformShiftConnectedPathLeftFamily entry) +
            familyFaceCount (uniformShiftConnectedPathRightFamily entry)) := by
    unfold couplingSpinSummedUniformShiftConnectedPathPairWeight
    exact Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _ hsecond
        (Q'.le_of_eqv (Q'.eqv_symm
          (Q'.pow_add_eqv anchorDecoratedFaceEnvelope _ _))))
  exact Q'.le_trans' _ _ _ htotal
    (pow_base_antitone (r := anchorDecoratedFaceEnvelope)
      anchorDecoratedFaceEnvelope_nonnegative (by decide)
      (uniformShiftConnectedCarrierSupport_length_le_pathFaceCount entry))

theorem couplingSpinSummedUniformShiftConnectedSourceWeight_le_carrier
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    couplingSpinSummedUniformShiftCylinderSourcePairWeight
        coupling cutoff entry.val ≤
      anchorDecoratedFaceEnvelope ^
          (uniformShiftConnectedCarrierSupport entry).length *
        couplingSpinSummedUniformShiftConnectedBackgroundPairWeight
          coupling cutoff entry := by
  have hbackground0 : (0 : Q') ≤
      couplingSpinSummedUniformShiftConnectedBackgroundPairWeight
        coupling cutoff entry := by
    unfold couplingSpinSummedUniformShiftConnectedBackgroundPairWeight
    exact Q'.mul_nonneg _ _
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff (uniformPaddedBase padding base) _)
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff (uniformPaddedBase padding base) _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (couplingSpinSummedUniformShiftConnectedSourceWeight_factor
        coupling cutoff entry))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (couplingSpinSummedUniformShiftConnectedPathWeight_le_supportPow
        hcoupling hle cutoff entry) hbackground0)

/-! ## 2. Fixed-size injective carrier summation -/

def uniformShiftConnectedColorPair
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    ColoredSupportPair :=
  (uniformShiftConnectedLeftColorSupport entry,
    uniformShiftConnectedRightColorSupport entry)

theorem uniformShiftConnectedColorPair_union
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    coloredSupportUnion (uniformPaddedBase padding base)
        (uniformShiftConnectedColorPair entry) =
      uniformShiftConnectedCarrierSupport entry := by
  exact coloredFamilyUnion_eq_appendUnion (uniformPaddedBase padding base)
    (uniformShiftConnectedPathLeftFamily entry)
    (uniformShiftConnectedPathRightFamily entry)

theorem uniformShiftConnectedCarrierSupport_mem_canonical
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (entry : UniformShiftConnectedEntry padding base roots predicate)
    {rootFace : Nat}
    (hrootFace : rootFace ∈ (uniformShiftSourceRootAtom entry.val).val) :
    uniformShiftConnectedCarrierSupport entry ∈
      canonicalSurfacePolymers (uniformPaddedBase padding base) :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (uniformShiftConnectedCarrierSupport_mem_faceSupports entry)
    ⟨rootFace, uniformShiftConnectedCarrierSupport_root_mem
      hrootsInside entry hrootFace⟩
    (uniformShiftConnectedCarrierSupport_internallyConnected
      hrootsInside entry hrootFace)

theorem uniformShiftConnectedColorPair_mem_fixed
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (entry : UniformShiftConnectedEntry padding base roots predicate)
    {rootFace size : Nat}
    (hrootFace : rootFace ∈ (uniformShiftSourceRootAtom entry.val).val)
    (hsize : (uniformShiftConnectedCarrierSupport entry).length = size) :
    uniformShiftConnectedColorPair entry ∈
      canonicalColoredPinnedSizePairs
        (uniformPaddedBase padding base) rootFace size := by
  unfold canonicalColoredPinnedSizePairs
  apply List.mem_filter.mpr
  constructor
  · apply (mem_cartesian_iff _ _ _).2
    exact ⟨familyUnionSupport_mem_cutoffOneFaceSupports
        (uniformPaddedBase padding base) _,
      familyUnionSupport_mem_cutoffOneFaceSupports
        (uniformPaddedBase padding base) _⟩
  · apply (memberB_eq_true_iff _ _).2
    rw [uniformShiftConnectedColorPair_union entry]
    exact mem_canonicalPinnedSizePolymers_iff.mpr
      ⟨uniformShiftConnectedCarrierSupport_mem_canonical
          hrootsInside entry hrootFace,
        uniformShiftConnectedCarrierSupport_root_mem
          hrootsInside entry hrootFace,
        hsize⟩

def uniformShiftConnectedCarrierTargetList
    (padding base rootFace size : Nat) : List ConnectedCarrier :=
  cartesian
    (canonicalColoredPinnedSizePairs (uniformPaddedBase padding base) rootFace size)
    (cartesian (canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
      (uniformShiftEmbeddedTargetFamilies padding base))

def uniformShiftConnectedCarrierTargetWeight
    (coupling : Q') (cutoff padding base size : Nat)
    (carrier : ConnectedCarrier) : Q' :=
  anchorDecoratedFaceEnvelope ^ size *
    (couplingParametricKSupportFamilyActivity coupling cutoff
        (uniformPaddedBase padding base) carrier.2.1 *
      couplingParametricKSupportFamilyActivity coupling cutoff
        (uniformPaddedBase padding base) carrier.2.2)

theorem uniformShiftConnectedCarrier_mem_target
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (entry : UniformShiftConnectedEntry padding base roots predicate)
    {rootFace size : Nat}
    (hrootFace : rootFace ∈ (uniformShiftSourceRootAtom entry.val).val)
    (hsize : (uniformShiftConnectedCarrierSupport entry).length = size) :
    uniformShiftConnectedCarrier entry ∈
      uniformShiftConnectedCarrierTargetList
        padding base rootFace size := by
  unfold uniformShiftConnectedCarrierTargetList uniformShiftConnectedCarrier
  apply (mem_cartesian_iff _ _ _).2
  constructor
  · exact uniformShiftConnectedColorPair_mem_fixed
      hrootsInside entry hrootFace hsize
  · apply (mem_cartesian_iff _ _ _).2
    exact ⟨uniformShiftConnectedBackgroundLeftFamily_mem entry,
      uniformShiftConnectedBackgroundRightFamily_mem_embedded entry⟩

theorem uniformShiftConnectedCarrierTargetSum_eqv
    (coupling : Q') (cutoff padding base rootFace size : Nat) :
    listQSum
        (uniformShiftConnectedCarrierTargetWeight
          coupling cutoff padding base size)
        (uniformShiftConnectedCarrierTargetList
          padding base rootFace size) ≈
      spinSummedColoredPinnedSizeWeightSum
          (uniformPaddedBase padding base) rootFace size *
        (couplingParametricKCompatibleSupportGasPartition
            coupling cutoff (uniformPaddedBase padding base) *
          couplingParametricKUniformShiftEmbeddedTargetPartition
            coupling cutoff padding base) := by
  have houter := listQSum_cartesian_product
    (fun _ : ColoredSupportPair => anchorDecoratedFaceEnvelope ^ size)
    (fun background : List (List Nat) × List (List Nat) =>
      couplingParametricKSupportFamilyActivity coupling cutoff
          (uniformPaddedBase padding base) background.1 *
        couplingParametricKSupportFamilyActivity coupling cutoff
          (uniformPaddedBase padding base) background.2)
    (canonicalColoredPinnedSizePairs (uniformPaddedBase padding base) rootFace size)
    (cartesian (canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
      (uniformShiftEmbeddedTargetFamilies padding base))
  have hinner := listQSum_cartesian_product
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (uniformPaddedBase padding base))
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (uniformPaddedBase padding base))
    (canonicalCompatibleAmbientFamilies (uniformPaddedBase padding base))
    (uniformShiftEmbeddedTargetFamilies padding base)
  unfold uniformShiftConnectedCarrierTargetList
    uniformShiftConnectedCarrierTargetWeight
    spinSummedColoredPinnedSizeWeightSum
  refine Q'.eqv_trans _ _ _ houter ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _ hinner ?_
  unfold couplingParametricKCompatibleSupportGasPartition
    couplingParametricKUniformShiftEmbeddedTargetPartition
  exact Q'.eqv_refl _

def uniformShiftConnectedSourceEntriesAtSize
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool} (size : Nat) :
    List (UniformShiftConnectedEntry padding base roots predicate) :=
  (connectedUniformShiftCylinderSourcePairs
    (padding := padding) (base := base)
    (roots := roots) (predicate := predicate)).attach.filter
      (fun entry => decide
        ((uniformShiftConnectedCarrierSupport entry).length = size))

theorem uniformShiftConnectedSourceEntriesAtSize_nodup
    (padding base : Nat) (roots : List (CanonicalAtom (uniformPaddedBase padding base)))
    (predicate : List Bool → Bool) (size : Nat) :
    (uniformShiftConnectedSourceEntriesAtSize
      (padding := padding) (base := base)
      (roots := roots) (predicate := predicate) size).Nodup := by
  unfold uniformShiftConnectedSourceEntriesAtSize
  exact List.filter_sublist.nodup
    (attach_nodup_of_nodup _
      (List.filter_sublist.nodup
        (uniformShiftCylinderSourcePairList_nodup
          padding base roots predicate)))

def uniformShiftRootCarrierTargetList
    {padding base : Nat}
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base))) (size : Nat) :
    List (CanonicalAtom (uniformPaddedBase padding base) × ConnectedCarrier) :=
  roots.flatMap (fun root =>
    (uniformShiftConnectedCarrierTargetList
      padding base (rootStart root) size).map
        (fun carrier => (root, carrier)))

def uniformShiftRootCarrierTargetWeight
    (coupling : Q') (cutoff padding base size : Nat)
    (tagged : CanonicalAtom (uniformPaddedBase padding base) × ConnectedCarrier) : Q' :=
  uniformShiftConnectedCarrierTargetWeight
    coupling cutoff padding base size tagged.2

def uniformShiftConnectedRootCarrierEncode
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    CanonicalAtom (uniformPaddedBase padding base) × ConnectedCarrier :=
  (uniformShiftSourceRootAtom entry.val, uniformShiftConnectedCarrier entry)

theorem uniformShiftConnectedRootCarrierEncode_mem
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    {size : Nat}
    (entry : UniformShiftConnectedEntry padding base roots predicate)
    (hsize : (uniformShiftConnectedCarrierSupport entry).length = size) :
    uniformShiftConnectedRootCarrierEncode entry ∈
      uniformShiftRootCarrierTargetList rootStart roots size := by
  apply List.mem_flatMap.mpr
  refine ⟨uniformShiftSourceRootAtom entry.val,
    (uniformShiftSourceRootAtom_spec entry).2, ?_⟩
  apply List.mem_map.mpr
  refine ⟨uniformShiftConnectedCarrier entry, ?_, rfl⟩
  exact uniformShiftConnectedCarrier_mem_target hrootsInside entry
    (hstartMem _ (uniformShiftSourceRootAtom_spec entry).2) hsize

theorem uniformShiftConnectedRootCarrierEncode_injective
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (first second : UniformShiftConnectedEntry padding base roots predicate)
    (heq : uniformShiftConnectedRootCarrierEncode first =
      uniformShiftConnectedRootCarrierEncode second) : first = second :=
  uniformShiftConnectedCarrier_injective first second
    (congrArg Prod.snd heq)

theorem couplingSpinSummedUniformShiftConnectedSizeSum_le_target
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    (size : Nat) :
    listQSum
        (fun entry : UniformShiftConnectedEntry padding base roots predicate =>
          couplingSpinSummedUniformShiftCylinderSourcePairWeight
            coupling cutoff entry.val)
        (uniformShiftConnectedSourceEntriesAtSize size) ≤
      listQSum
        (uniformShiftRootCarrierTargetWeight
          coupling cutoff padding base size)
        (uniformShiftRootCarrierTargetList rootStart roots size) := by
  apply listQSum_le_of_injective
    (uniformShiftConnectedSourceEntriesAtSize
      (padding := padding) (base := base)
      (roots := roots) (predicate := predicate) size)
    (uniformShiftRootCarrierTargetList rootStart roots size)
    (fun entry : UniformShiftConnectedEntry padding base roots predicate =>
      couplingSpinSummedUniformShiftCylinderSourcePairWeight
        coupling cutoff entry.val)
    (uniformShiftRootCarrierTargetWeight
      coupling cutoff padding base size)
    uniformShiftConnectedRootCarrierEncode
    (uniformShiftConnectedSourceEntriesAtSize_nodup
      padding base roots predicate size)
  · intro entry hentry
    have hsize : (uniformShiftConnectedCarrierSupport entry).length = size :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    exact uniformShiftConnectedRootCarrierEncode_mem
      hrootsInside rootStart hstartMem entry hsize
  · intro first _ second _ heq
    exact uniformShiftConnectedRootCarrierEncode_injective first second heq
  · intro entry hentry
    have hsize : (uniformShiftConnectedCarrierSupport entry).length = size :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    have hbound :=
      couplingSpinSummedUniformShiftConnectedSourceWeight_le_carrier
        hcoupling hle cutoff entry
    rw [hsize] at hbound
    simpa [uniformShiftRootCarrierTargetWeight,
      uniformShiftConnectedRootCarrierEncode,
      uniformShiftConnectedCarrierTargetWeight,
      couplingSpinSummedUniformShiftConnectedBackgroundPairWeight,
      uniformShiftConnectedCarrier] using hbound
  · intro tagged _
    unfold uniformShiftRootCarrierTargetWeight
      uniformShiftConnectedCarrierTargetWeight
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorDecoratedFaceEnvelope
        anchorDecoratedFaceEnvelope_nonnegative size)
      (Q'.mul_nonneg _ _
        (couplingParametricKSupportFamilyActivity_nonnegative
          hcoupling cutoff (uniformPaddedBase padding base) tagged.2.2.1)
        (couplingParametricKSupportFamilyActivity_nonnegative
          hcoupling cutoff (uniformPaddedBase padding base) tagged.2.2.2))

theorem uniformShiftEmbeddedTargetPartition_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff padding base : Nat) :
    (0 : Q') ≤ couplingParametricKUniformShiftEmbeddedTargetPartition
      coupling cutoff padding base := by
  unfold couplingParametricKUniformShiftEmbeddedTargetPartition
  exact listQSum_nonnegative_generic _ (fun family =>
    couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff (uniformPaddedBase padding base) family)
    (uniformShiftEmbeddedTargetFamilies padding base)

theorem uniformShiftRootCarrierTargetSum_eqv
    (coupling : Q') (cutoff padding base size : Nat)
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base))) :
    listQSum
        (uniformShiftRootCarrierTargetWeight
          coupling cutoff padding base size)
        (uniformShiftRootCarrierTargetList rootStart roots size) ≈
      listQSum
        (fun root =>
          listQSum
            (uniformShiftConnectedCarrierTargetWeight
              coupling cutoff padding base size)
            (uniformShiftConnectedCarrierTargetList
              padding base (rootStart root) size)) roots := by
  unfold uniformShiftRootCarrierTargetList
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (uniformShiftRootCarrierTargetWeight
        coupling cutoff padding base size)
      (fun root =>
        (uniformShiftConnectedCarrierTargetList
          padding base (rootStart root) size).map
          (fun carrier => (root, carrier))) roots) ?_
  apply listQSum_congr
  intro root
  rw [listQSum_map]
  exact Q'.eqv_refl _

theorem uniformShiftRootCarrierTargetSum_le_geom
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff padding base size : Nat)
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base))) :
    listQSum
        (uniformShiftRootCarrierTargetWeight
          coupling cutoff padding base size)
        (uniformShiftRootCarrierTargetList rootStart roots size) ≤
      Q'.ofNat roots.length *
        (anchorDecoratedEffectiveRatio ^ size *
          (couplingParametricKCompatibleSupportGasPartition
              coupling cutoff (uniformPaddedBase padding base) *
            couplingParametricKUniformShiftEmbeddedTargetPartition
              coupling cutoff padding base)) := by
  let partitionProduct :=
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (uniformPaddedBase padding base) *
      couplingParametricKUniformShiftEmbeddedTargetPartition
        coupling cutoff padding base
  have hpartition0 : (0 : Q') ≤ partitionProduct :=
    Q'.mul_nonneg _ _
      (couplingParametricKCompatibleSupportGasPartition_nonnegative
        hcoupling cutoff (uniformPaddedBase padding base))
      (uniformShiftEmbeddedTargetPartition_nonnegative
        hcoupling cutoff padding base)
  have hterm0 : (0 : Q') ≤
      anchorDecoratedEffectiveRatio ^ size * partitionProduct :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorDecoratedEffectiveRatio
        anchorDecoratedEffectiveRatio_nonnegative size) hpartition0
  have hrootSum := uniformShiftRootCarrierTargetSum_eqv
    coupling cutoff padding base size rootStart roots
  apply Q'.le_trans' _ _ _ (Q'.le_of_eqv hrootSum)
  apply listQSum_le_length_mul
    (fun root => listQSum
      (uniformShiftConnectedCarrierTargetWeight
        coupling cutoff padding base size)
      (uniformShiftConnectedCarrierTargetList
        padding base (rootStart root) size))
    hterm0 roots
  intro root _
  have hfactor := uniformShiftConnectedCarrierTargetSum_eqv
    coupling cutoff padding base (rootStart root) size
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (spinSummedColoredPinnedSizeWeightSum_le_geom
        (uniformPaddedBase padding base) (rootStart root) size) hpartition0)

#print axioms couplingSpinSummedUniformShiftConnectedSourceWeight_le_carrier
#print axioms uniformShiftConnectedCarrier_mem_target
#print axioms uniformShiftConnectedCarrierTargetSum_eqv
#print axioms couplingSpinSummedUniformShiftConnectedSizeSum_le_target
#print axioms uniformShiftRootCarrierTargetSum_le_geom

end YMGap.Continuum.Z4UniformShiftConnectedCarrierTail
