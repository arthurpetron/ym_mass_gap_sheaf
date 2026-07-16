/-
# Explicit coupling-parametric tail for the affine shifted carrier

The carrier selected from every connected shifted cylinder pair is summed by
its exact union-support size.  The two path colors receive the derived
decorated face envelope; the two background colors keep their exact
coupling-parametric activities.  The resulting finite Cartesian sum factors
as the full target partition times the affine embedded partition, and the
shifted-shell size floor gives an explicit geometric tail.
-/

import YMGap.Continuum.Z4TimeShiftedConnectedCarrier
import YMGap.Continuum.Z4CouplingParametricConnectedCarrierTail

namespace YMGap.Continuum.Z4TimeShiftedConnectedCarrierTail

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
open YMGap.Continuum.Z4TimeShiftedConnectedCarrier
open YMGap.Continuum.Z4TimeShiftedCylinderSwitchSummation
open YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder
open YMGap.Continuum.Z4TimeShiftedEmbeddedRegion

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-! ## 1. Exact path/background factorization and envelope -/

def couplingSpinSummedTimeShiftConnectedPathPairWeight
    (coupling : Q') (cutoff : Nat)
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff (base + shift)
      (timeShiftConnectedPathLeftFamily entry) *
    couplingParametricKSupportFamilyActivity coupling cutoff (base + shift)
      (timeShiftConnectedPathRightFamily entry)

def couplingSpinSummedTimeShiftConnectedBackgroundPairWeight
    (coupling : Q') (cutoff : Nat)
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) : Q' :=
  couplingParametricKSupportFamilyActivity coupling cutoff (base + shift)
      (timeShiftConnectedBackgroundLeftFamily entry) *
    couplingParametricKSupportFamilyActivity coupling cutoff (base + shift)
      (timeShiftConnectedBackgroundRightFamily entry)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem couplingSpinSummedTimeShiftConnectedSourceWeight_factor
    (coupling : Q') (cutoff : Nat)
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    couplingSpinSummedTimeShiftCylinderSourcePairWeight
        coupling cutoff entry.val ≈
      couplingSpinSummedTimeShiftConnectedPathPairWeight
          coupling cutoff entry *
        couplingSpinSummedTimeShiftConnectedBackgroundPairWeight
          coupling cutoff entry := by
  have hleft := couplingParametricKSupportFamilyActivity_filter_partition
    coupling cutoff (base + shift) entry.val.1.val
      (timeShiftConnectedPathTest entry)
  have hright := couplingParametricKSupportFamilyActivity_filter_partition
    coupling cutoff (base + shift) entry.val.2.val
      (timeShiftConnectedPathTest entry)
  refine Q'.eqv_trans _ _ _ (mul_eqv_both_local hleft hright) ?_
  unfold couplingSpinSummedTimeShiftConnectedPathPairWeight
    couplingSpinSummedTimeShiftConnectedBackgroundPairWeight
    timeShiftConnectedPathLeftFamily
    timeShiftConnectedBackgroundLeftFamily
    timeShiftConnectedPathRightFamily
    timeShiftConnectedBackgroundRightFamily
  ring_qeqv

theorem timeShiftConnectedCarrierSupport_length_le_pathFaceCount
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    (timeShiftConnectedCarrierSupport entry).length ≤
      familyFaceCount (timeShiftConnectedPathLeftFamily entry) +
        familyFaceCount (timeShiftConnectedPathRightFamily entry) := by
  have hbound := familyUnionSupport_length_le_familyFaceCount
    (base + shift)
    (timeShiftConnectedPathLeftFamily entry ++
      timeShiftConnectedPathRightFamily entry)
  rw [familyFaceCount_append] at hbound
  exact hbound

theorem couplingSpinSummedTimeShiftConnectedPathWeight_le_supportPow
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    couplingSpinSummedTimeShiftConnectedPathPairWeight
        coupling cutoff entry ≤
      anchorDecoratedFaceEnvelope ^
        (timeShiftConnectedCarrierSupport entry).length := by
  have hleft := couplingParametricKSupportFamilyActivity_le_totalFacePow
    hcoupling hle cutoff (base + shift)
      (timeShiftConnectedPathLeftFamily entry)
  have hright := couplingParametricKSupportFamilyActivity_le_totalFacePow
    hcoupling hle cutoff (base + shift)
      (timeShiftConnectedPathRightFamily entry)
  have hright0 := couplingParametricKSupportFamilyActivity_nonnegative
    hcoupling cutoff (base + shift)
      (timeShiftConnectedPathRightFamily entry)
  have hleftPow0 : (0 : Q') ≤ anchorDecoratedFaceEnvelope ^
      familyFaceCount (timeShiftConnectedPathLeftFamily entry) :=
    Q'.pow_nonneg anchorDecoratedFaceEnvelope
      anchorDecoratedFaceEnvelope_nonnegative _
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ _ hleft hright0
  have hsecond := Q'.mul_le_mul_of_nonneg_left _ _ _ hright hleftPow0
  have htotal : couplingSpinSummedTimeShiftConnectedPathPairWeight
      coupling cutoff entry ≤
        anchorDecoratedFaceEnvelope ^
          (familyFaceCount (timeShiftConnectedPathLeftFamily entry) +
            familyFaceCount (timeShiftConnectedPathRightFamily entry)) := by
    unfold couplingSpinSummedTimeShiftConnectedPathPairWeight
    exact Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _ hsecond
        (Q'.le_of_eqv (Q'.eqv_symm
          (Q'.pow_add_eqv anchorDecoratedFaceEnvelope _ _))))
  exact Q'.le_trans' _ _ _ htotal
    (pow_base_antitone (r := anchorDecoratedFaceEnvelope)
      anchorDecoratedFaceEnvelope_nonnegative (by decide)
      (timeShiftConnectedCarrierSupport_length_le_pathFaceCount entry))

theorem couplingSpinSummedTimeShiftConnectedSourceWeight_le_carrier
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    couplingSpinSummedTimeShiftCylinderSourcePairWeight
        coupling cutoff entry.val ≤
      anchorDecoratedFaceEnvelope ^
          (timeShiftConnectedCarrierSupport entry).length *
        couplingSpinSummedTimeShiftConnectedBackgroundPairWeight
          coupling cutoff entry := by
  have hbackground0 : (0 : Q') ≤
      couplingSpinSummedTimeShiftConnectedBackgroundPairWeight
        coupling cutoff entry := by
    unfold couplingSpinSummedTimeShiftConnectedBackgroundPairWeight
    exact Q'.mul_nonneg _ _
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff (base + shift) _)
      (couplingParametricKSupportFamilyActivity_nonnegative
        hcoupling cutoff (base + shift) _)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (couplingSpinSummedTimeShiftConnectedSourceWeight_factor
        coupling cutoff entry))
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (couplingSpinSummedTimeShiftConnectedPathWeight_le_supportPow
        hcoupling hle cutoff entry) hbackground0)

/-! ## 2. Fixed-size injective carrier summation -/

def timeShiftConnectedColorPair
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    ColoredSupportPair :=
  (timeShiftConnectedLeftColorSupport entry,
    timeShiftConnectedRightColorSupport entry)

theorem timeShiftConnectedColorPair_union
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    coloredSupportUnion (base + shift)
        (timeShiftConnectedColorPair entry) =
      timeShiftConnectedCarrierSupport entry := by
  exact coloredFamilyUnion_eq_appendUnion (base + shift)
    (timeShiftConnectedPathLeftFamily entry)
    (timeShiftConnectedPathRightFamily entry)

theorem timeShiftConnectedCarrierSupport_mem_canonical
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (entry : TimeShiftConnectedEntry shift base roots predicate)
    {rootFace : Nat}
    (hrootFace : rootFace ∈ (timeShiftSourceRootAtom entry.val).val) :
    timeShiftConnectedCarrierSupport entry ∈
      canonicalSurfacePolymers (base + shift) :=
  connectedFaceSupport_mem_canonicalSurfacePolymers
    (timeShiftConnectedCarrierSupport_mem_faceSupports entry)
    ⟨rootFace, timeShiftConnectedCarrierSupport_root_mem
      hrootsInside entry hrootFace⟩
    (timeShiftConnectedCarrierSupport_internallyConnected
      hrootsInside entry hrootFace)

theorem timeShiftConnectedColorPair_mem_fixed
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (entry : TimeShiftConnectedEntry shift base roots predicate)
    {rootFace size : Nat}
    (hrootFace : rootFace ∈ (timeShiftSourceRootAtom entry.val).val)
    (hsize : (timeShiftConnectedCarrierSupport entry).length = size) :
    timeShiftConnectedColorPair entry ∈
      canonicalColoredPinnedSizePairs
        (base + shift) rootFace size := by
  unfold canonicalColoredPinnedSizePairs
  apply List.mem_filter.mpr
  constructor
  · apply (mem_cartesian_iff _ _ _).2
    exact ⟨familyUnionSupport_mem_cutoffOneFaceSupports
        (base + shift) _,
      familyUnionSupport_mem_cutoffOneFaceSupports
        (base + shift) _⟩
  · apply (memberB_eq_true_iff _ _).2
    rw [timeShiftConnectedColorPair_union entry]
    exact mem_canonicalPinnedSizePolymers_iff.mpr
      ⟨timeShiftConnectedCarrierSupport_mem_canonical
          hrootsInside entry hrootFace,
        timeShiftConnectedCarrierSupport_root_mem
          hrootsInside entry hrootFace,
        hsize⟩

def timeShiftConnectedCarrierTargetList
    (shift base rootFace size : Nat) : List ConnectedCarrier :=
  cartesian
    (canonicalColoredPinnedSizePairs (base + shift) rootFace size)
    (cartesian (canonicalCompatibleAmbientFamilies (base + shift))
      (timeShiftEmbeddedTargetFamilies shift base))

def timeShiftConnectedCarrierTargetWeight
    (coupling : Q') (cutoff shift base size : Nat)
    (carrier : ConnectedCarrier) : Q' :=
  anchorDecoratedFaceEnvelope ^ size *
    (couplingParametricKSupportFamilyActivity coupling cutoff
        (base + shift) carrier.2.1 *
      couplingParametricKSupportFamilyActivity coupling cutoff
        (base + shift) carrier.2.2)

theorem timeShiftConnectedCarrier_mem_target
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (entry : TimeShiftConnectedEntry shift base roots predicate)
    {rootFace size : Nat}
    (hrootFace : rootFace ∈ (timeShiftSourceRootAtom entry.val).val)
    (hsize : (timeShiftConnectedCarrierSupport entry).length = size) :
    timeShiftConnectedCarrier entry ∈
      timeShiftConnectedCarrierTargetList
        shift base rootFace size := by
  unfold timeShiftConnectedCarrierTargetList timeShiftConnectedCarrier
  apply (mem_cartesian_iff _ _ _).2
  constructor
  · exact timeShiftConnectedColorPair_mem_fixed
      hrootsInside entry hrootFace hsize
  · apply (mem_cartesian_iff _ _ _).2
    exact ⟨timeShiftConnectedBackgroundLeftFamily_mem entry,
      timeShiftConnectedBackgroundRightFamily_mem_embedded entry⟩

theorem timeShiftConnectedCarrierTargetSum_eqv
    (coupling : Q') (cutoff shift base rootFace size : Nat) :
    listQSum
        (timeShiftConnectedCarrierTargetWeight
          coupling cutoff shift base size)
        (timeShiftConnectedCarrierTargetList
          shift base rootFace size) ≈
      spinSummedColoredPinnedSizeWeightSum
          (base + shift) rootFace size *
        (couplingParametricKCompatibleSupportGasPartition
            coupling cutoff (base + shift) *
          couplingParametricKTimeShiftEmbeddedTargetPartition
            coupling cutoff shift base) := by
  have houter := listQSum_cartesian_product
    (fun _ : ColoredSupportPair => anchorDecoratedFaceEnvelope ^ size)
    (fun background : List (List Nat) × List (List Nat) =>
      couplingParametricKSupportFamilyActivity coupling cutoff
          (base + shift) background.1 *
        couplingParametricKSupportFamilyActivity coupling cutoff
          (base + shift) background.2)
    (canonicalColoredPinnedSizePairs (base + shift) rootFace size)
    (cartesian (canonicalCompatibleAmbientFamilies (base + shift))
      (timeShiftEmbeddedTargetFamilies shift base))
  have hinner := listQSum_cartesian_product
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (base + shift))
    (couplingParametricKSupportFamilyActivity
      coupling cutoff (base + shift))
    (canonicalCompatibleAmbientFamilies (base + shift))
    (timeShiftEmbeddedTargetFamilies shift base)
  unfold timeShiftConnectedCarrierTargetList
    timeShiftConnectedCarrierTargetWeight
    spinSummedColoredPinnedSizeWeightSum
  refine Q'.eqv_trans _ _ _ houter ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _ hinner ?_
  unfold couplingParametricKCompatibleSupportGasPartition
    couplingParametricKTimeShiftEmbeddedTargetPartition
  exact Q'.eqv_refl _

def timeShiftConnectedSourceEntriesAtSize
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool} (size : Nat) :
    List (TimeShiftConnectedEntry shift base roots predicate) :=
  (connectedTimeShiftCylinderSourcePairs
    (shift := shift) (base := base)
    (roots := roots) (predicate := predicate)).attach.filter
      (fun entry => decide
        ((timeShiftConnectedCarrierSupport entry).length = size))

theorem timeShiftConnectedSourceEntriesAtSize_nodup
    (shift base : Nat) (roots : List (CanonicalAtom (base + shift)))
    (predicate : List Bool → Bool) (size : Nat) :
    (timeShiftConnectedSourceEntriesAtSize
      (shift := shift) (base := base)
      (roots := roots) (predicate := predicate) size).Nodup := by
  unfold timeShiftConnectedSourceEntriesAtSize
  exact List.filter_sublist.nodup
    (attach_nodup_of_nodup _
      (List.filter_sublist.nodup
        (timeShiftCylinderSourcePairList_nodup
          shift base roots predicate)))

def timeShiftRootCarrierTargetList
    {shift base : Nat}
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (roots : List (CanonicalAtom (base + shift))) (size : Nat) :
    List (CanonicalAtom (base + shift) × ConnectedCarrier) :=
  roots.flatMap (fun root =>
    (timeShiftConnectedCarrierTargetList
      shift base (rootStart root) size).map
        (fun carrier => (root, carrier)))

def timeShiftRootCarrierTargetWeight
    (coupling : Q') (cutoff shift base size : Nat)
    (tagged : CanonicalAtom (base + shift) × ConnectedCarrier) : Q' :=
  timeShiftConnectedCarrierTargetWeight
    coupling cutoff shift base size tagged.2

def timeShiftConnectedRootCarrierEncode
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    CanonicalAtom (base + shift) × ConnectedCarrier :=
  (timeShiftSourceRootAtom entry.val, timeShiftConnectedCarrier entry)

theorem timeShiftConnectedRootCarrierEncode_mem
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    {size : Nat}
    (entry : TimeShiftConnectedEntry shift base roots predicate)
    (hsize : (timeShiftConnectedCarrierSupport entry).length = size) :
    timeShiftConnectedRootCarrierEncode entry ∈
      timeShiftRootCarrierTargetList rootStart roots size := by
  apply List.mem_flatMap.mpr
  refine ⟨timeShiftSourceRootAtom entry.val,
    (timeShiftSourceRootAtom_spec entry).2, ?_⟩
  apply List.mem_map.mpr
  refine ⟨timeShiftConnectedCarrier entry, ?_, rfl⟩
  exact timeShiftConnectedCarrier_mem_target hrootsInside entry
    (hstartMem _ (timeShiftSourceRootAtom_spec entry).2) hsize

theorem timeShiftConnectedRootCarrierEncode_injective
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (first second : TimeShiftConnectedEntry shift base roots predicate)
    (heq : timeShiftConnectedRootCarrierEncode first =
      timeShiftConnectedRootCarrierEncode second) : first = second :=
  timeShiftConnectedCarrier_injective first second
    (congrArg Prod.snd heq)

theorem couplingSpinSummedTimeShiftConnectedSizeSum_le_target
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    (size : Nat) :
    listQSum
        (fun entry : TimeShiftConnectedEntry shift base roots predicate =>
          couplingSpinSummedTimeShiftCylinderSourcePairWeight
            coupling cutoff entry.val)
        (timeShiftConnectedSourceEntriesAtSize size) ≤
      listQSum
        (timeShiftRootCarrierTargetWeight
          coupling cutoff shift base size)
        (timeShiftRootCarrierTargetList rootStart roots size) := by
  apply listQSum_le_of_injective
    (timeShiftConnectedSourceEntriesAtSize
      (shift := shift) (base := base)
      (roots := roots) (predicate := predicate) size)
    (timeShiftRootCarrierTargetList rootStart roots size)
    (fun entry : TimeShiftConnectedEntry shift base roots predicate =>
      couplingSpinSummedTimeShiftCylinderSourcePairWeight
        coupling cutoff entry.val)
    (timeShiftRootCarrierTargetWeight
      coupling cutoff shift base size)
    timeShiftConnectedRootCarrierEncode
    (timeShiftConnectedSourceEntriesAtSize_nodup
      shift base roots predicate size)
  · intro entry hentry
    have hsize : (timeShiftConnectedCarrierSupport entry).length = size :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    exact timeShiftConnectedRootCarrierEncode_mem
      hrootsInside rootStart hstartMem entry hsize
  · intro first _ second _ heq
    exact timeShiftConnectedRootCarrierEncode_injective first second heq
  · intro entry hentry
    have hsize : (timeShiftConnectedCarrierSupport entry).length = size :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    have hbound :=
      couplingSpinSummedTimeShiftConnectedSourceWeight_le_carrier
        hcoupling hle cutoff entry
    rw [hsize] at hbound
    simpa [timeShiftRootCarrierTargetWeight,
      timeShiftConnectedRootCarrierEncode,
      timeShiftConnectedCarrierTargetWeight,
      couplingSpinSummedTimeShiftConnectedBackgroundPairWeight,
      timeShiftConnectedCarrier] using hbound
  · intro tagged _
    unfold timeShiftRootCarrierTargetWeight
      timeShiftConnectedCarrierTargetWeight
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorDecoratedFaceEnvelope
        anchorDecoratedFaceEnvelope_nonnegative size)
      (Q'.mul_nonneg _ _
        (couplingParametricKSupportFamilyActivity_nonnegative
          hcoupling cutoff (base + shift) tagged.2.2.1)
        (couplingParametricKSupportFamilyActivity_nonnegative
          hcoupling cutoff (base + shift) tagged.2.2.2))

theorem timeShiftEmbeddedTargetPartition_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base : Nat) :
    (0 : Q') ≤ couplingParametricKTimeShiftEmbeddedTargetPartition
      coupling cutoff shift base := by
  unfold couplingParametricKTimeShiftEmbeddedTargetPartition
  exact listQSum_nonnegative_generic _ (fun family =>
    couplingParametricKSupportFamilyActivity_nonnegative
      hcoupling cutoff (base + shift) family)
    (timeShiftEmbeddedTargetFamilies shift base)

theorem timeShiftRootCarrierTargetSum_eqv
    (coupling : Q') (cutoff shift base size : Nat)
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (roots : List (CanonicalAtom (base + shift))) :
    listQSum
        (timeShiftRootCarrierTargetWeight
          coupling cutoff shift base size)
        (timeShiftRootCarrierTargetList rootStart roots size) ≈
      listQSum
        (fun root =>
          listQSum
            (timeShiftConnectedCarrierTargetWeight
              coupling cutoff shift base size)
            (timeShiftConnectedCarrierTargetList
              shift base (rootStart root) size)) roots := by
  unfold timeShiftRootCarrierTargetList
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap
      (timeShiftRootCarrierTargetWeight
        coupling cutoff shift base size)
      (fun root =>
        (timeShiftConnectedCarrierTargetList
          shift base (rootStart root) size).map
          (fun carrier => (root, carrier))) roots) ?_
  apply listQSum_congr
  intro root
  rw [listQSum_map]
  exact Q'.eqv_refl _

theorem timeShiftRootCarrierTargetSum_le_geom
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base size : Nat)
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (roots : List (CanonicalAtom (base + shift))) :
    listQSum
        (timeShiftRootCarrierTargetWeight
          coupling cutoff shift base size)
        (timeShiftRootCarrierTargetList rootStart roots size) ≤
      Q'.ofNat roots.length *
        (anchorDecoratedEffectiveRatio ^ size *
          (couplingParametricKCompatibleSupportGasPartition
              coupling cutoff (base + shift) *
            couplingParametricKTimeShiftEmbeddedTargetPartition
              coupling cutoff shift base)) := by
  let partitionProduct :=
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (base + shift) *
      couplingParametricKTimeShiftEmbeddedTargetPartition
        coupling cutoff shift base
  have hpartition0 : (0 : Q') ≤ partitionProduct :=
    Q'.mul_nonneg _ _
      (couplingParametricKCompatibleSupportGasPartition_nonnegative
        hcoupling cutoff (base + shift))
      (timeShiftEmbeddedTargetPartition_nonnegative
        hcoupling cutoff shift base)
  have hterm0 : (0 : Q') ≤
      anchorDecoratedEffectiveRatio ^ size * partitionProduct :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorDecoratedEffectiveRatio
        anchorDecoratedEffectiveRatio_nonnegative size) hpartition0
  have hrootSum := timeShiftRootCarrierTargetSum_eqv
    coupling cutoff shift base size rootStart roots
  apply Q'.le_trans' _ _ _ (Q'.le_of_eqv hrootSum)
  apply listQSum_le_length_mul
    (fun root => listQSum
      (timeShiftConnectedCarrierTargetWeight
        coupling cutoff shift base size)
      (timeShiftConnectedCarrierTargetList
        shift base (rootStart root) size))
    hterm0 roots
  intro root _
  have hfactor := timeShiftConnectedCarrierTargetSum_eqv
    coupling cutoff shift base (rootStart root) size
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (spinSummedColoredPinnedSizeWeightSum_le_geom
        (base + shift) (rootStart root) size) hpartition0)

#print axioms couplingSpinSummedTimeShiftConnectedSourceWeight_le_carrier
#print axioms timeShiftConnectedCarrier_mem_target
#print axioms timeShiftConnectedCarrierTargetSum_eqv
#print axioms couplingSpinSummedTimeShiftConnectedSizeSum_le_target
#print axioms timeShiftRootCarrierTargetSum_le_geom

end YMGap.Continuum.Z4TimeShiftedConnectedCarrierTail
