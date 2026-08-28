/-
# Aggregate posterior transport for the literal paired face observable

A pointwise positive recoupling mass on every support-connected source is
stronger than the covariance argument needs, and can fail on locally forced
strand sheets.  The honest coercivity datum is aggregate: after weighting by
the physical two-replica Gibbs law, the successful mass on the complete
connected sector is at least a displayed positive fraction of that sector.

This module proves that one shared-column finite transport, full row mass on
the disconnected sector, and the aggregate connected-sector floor imply the
same strict face-covariance estimate as a pointwise posterior fraction.  No
aggregate floor or column-capacity certificate is inhabited here.  In
particular, no uniformity in coupling, cutoff, volume, or lattice spacing is
asserted, and no completed or continuum mass gap follows.

Constructive contract: exact finite `Q'` algebra, finite lists, and explicit
dependent kernels only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport
open YMGap.Continuum.CompactDualSlabObservablePairedSupportTwoStep
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local instance aggregatePosteriorPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D rootFaceId

private theorem q_lt_of_lt_of_le_local {a b c : Q'}
    (hab : a < b) (hbc : b ≤ c) : a < c := by
  have habCross :
      a.num * (b.den : Int) < b.num * (a.den : Int) := hab
  have hbcCross :
      b.num * (c.den : Int) ≤ c.num * (b.den : Int) := hbc
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hfirst :
      (a.num * (c.den : Int)) * (b.den : Int) <
        (b.num * (a.den : Int)) * (c.den : Int) := by
    have hscaled := Int.mul_lt_mul_of_pos_right habCross
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have hreorder :
        (a.num * (b.den : Int)) * (c.den : Int) =
          (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hreorder] at hscaled
  have hsecond :
      (b.num * (a.den : Int)) * (c.den : Int) ≤
        (c.num * (a.den : Int)) * (b.den : Int) := by
    have hscaled := Int.mul_le_mul_of_nonneg_right hbcCross
      (by exact_mod_cast Nat.zero_le a.den : (0 : Int) ≤ (a.den : Int))
    have hleft :
        (b.num * (c.den : Int)) * (a.den : Int) =
          (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (c.den : Int) (a.den : Int)]
    have hright :
        (c.num * (b.den : Int)) * (a.den : Int) =
          (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (b.den : Int) (a.den : Int)]
    rwa [hleft, hright] at hscaled
  have hcombined := Int.lt_of_lt_of_le hfirst hsecond
  exact Int.lt_of_mul_lt_mul_right hcombined
    (by exact_mod_cast Nat.zero_le b.den)

private theorem lt_add_of_pos_right_local
    (a b : Q') (hb : (0 : Q') < b) : a < a + b := by
  show a.num * ((a + b).den : Int) <
    (a + b).num * (a.den : Int)
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int) <
    (a.num * (b.den : Int) + b.num * (a.den : Int)) *
      (a.den : Int)
  have hcast : ((a.den * b.den : Nat) : Int) =
      (a.den : Int) * (b.den : Int) := by
    push_cast
    rfl
  rw [hcast]
  have hden : (0 : Int) < (a.den : Int) := by exact_mod_cast a.den_pos
  have key :
      (0 : Int) < b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hden) hden
  have hexpand :
      (a.num * (b.den : Int) + b.num * (a.den : Int)) *
          (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) +
          b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have efirst :
        a.num * (b.den : Int) * (a.den : Int) =
          a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc,
        Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [efirst]
  rw [hexpand]
  omega

private theorem one_sub_add_eqv_one (fraction : Q') :
    ((1 : Q') + -fraction) + fraction ≈ 1 := by
  exact Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv 1 (-fraction) fraction)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left 1 ((-fraction) + fraction) 0
        (Q'.neg_add_self_eqv fraction))
      (Q'.eqv_of_eq (Q'.add_zero' 1)))

private theorem bool_eq_false_of_not_eq_true_local
    (value : Bool) (hvalue : (!value) = true) : value = false := by
  cases value <;> simp_all

private theorem add_connected_le_target_add_complement
    (disconnected connected target fraction : Q')
    (hspent : disconnected + fraction * connected ≤ target) :
    disconnected + connected ≤
      target + ((1 : Q') + -fraction) * connected := by
  let complement := (1 : Q') + -fraction
  have hcoeff : fraction + complement ≈ 1 :=
    Q'.eqv_trans _ _ _
      (Q'.add_comm_eqv fraction complement)
      (one_sub_add_eqv_one fraction)
  have hrecombine :
      fraction * connected + complement * connected ≈ connected :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv fraction complement connected))
      (Q'.eqv_trans _ (1 * connected) _
        (Q'.mul_eqv_congr_right
          (fraction + complement) 1 connected hcoeff)
        (Q'.one_mul_eqv connected))
  have hsourceToSpent :
      disconnected + connected ≈
        (disconnected + fraction * connected) +
          complement * connected :=
    Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv disconnected
          (fraction * connected) (complement * connected))
        (Q'.add_eqv_congr_left disconnected
          (fraction * connected + complement * connected)
          connected hrecombine))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hsourceToSpent)
    (Q'.add_le_add hspent
      (Q'.le_refl' (complement * connected)))

/-! ## 1. The aggregate shared-column certificate -/

/-- A shared finite posterior kernel with an aggregate connected-sector
coercivity floor.  `disconnected_row_mass` spends the complete successful row
where separation is already present.  `connected_transported_floor` permits
individual connected rows to have zero mass, but requires their Gibbs-weighted
average to retain the displayed positive fraction. -/
structure SlabObservablePairedAggregatePosteriorTransport
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Type 1 where
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ (1 : Q')
  rowMass : SlabObservableTwoReplicaPair D rootFaceId → Q'
  Choice : SlabObservableTwoReplicaPair D rootFaceId → Type
  choices : (source : SlabObservableTwoReplicaPair D rootFaceId) →
    List (Choice source)
  localWeight : (source : SlabObservableTwoReplicaPair D rootFaceId) →
    Choice source → Q'
  localWeight_nonnegative : ∀ source,
    source ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId →
    ∀ choice, choice ∈ choices source →
      (0 : Q') ≤ localWeight source choice
  realize : (source : SlabObservableTwoReplicaPair D rootFaceId) →
    Choice source → SlabObservableTwoReplicaPair D rootFaceId
  coverage : ∀ source,
    source ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId →
    ∀ choice, choice ∈ choices source →
      realize source choice ∈
        slabObservableFourCellTargetPairs D rootFaceId targetFaceId
  row_mass : ∀ source,
    source ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId →
    listQSum (localWeight source) (choices source) ≈ rowMass source
  disconnected_row_mass : ∀ source,
    source ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId →
    slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId source = false →
    rowMass source ≈ 1
  connected_transported_floor :
    fraction *
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            D rootFaceId targetFaceId) ≤
      listQSum
        (fun source =>
          slabObservableTwoReplicaPairWeight D source * rowMass source)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId)
  column_capacity : ∀ target,
    target ∈ slabObservableFourCellTargetPairs
      D rootFaceId targetFaceId →
    listQSum
        (fun source => slabObservableTwoReplicaPairWeight D source *
          dependentKernelPushforwardWeight
            Choice choices localWeight realize source target)
        (slabObservableFourCellSourcePairs
          D rootFaceId targetFaceId) ≤
      slabObservableTwoReplicaPairWeight D target

namespace SlabObservablePairedAggregatePosteriorTransport

theorem complement_nonnegative
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedAggregatePosteriorTransport
      D rootFaceId targetFaceId) :
    (0 : Q') ≤ (1 : Q') + -data.fraction :=
  Q'.sub_nonneg_of_le data.fraction_le_one

theorem complement_lt_one
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedAggregatePosteriorTransport
      D rootFaceId targetFaceId) :
    (1 : Q') + -data.fraction < (1 : Q') := by
  have hadd := lt_add_of_pos_right_local
    ((1 : Q') + -data.fraction) data.fraction data.fraction_pos
  exact q_lt_of_lt_of_le_local hadd
    (Q'.le_of_eqv (one_sub_add_eqv_one data.fraction))

/-! ## 2. Aggregate finite Fubini and defect contraction -/

/-- One shared column budget bounds the total successfully transported
physical source weight, with the source-dependent row mass left explicit. -/
theorem transportedRowMass_weight_le_target
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedAggregatePosteriorTransport
      D rootFaceId targetFaceId) :
    listQSum
        (fun source =>
          slabObservableTwoReplicaPairWeight D source * data.rowMass source)
        (slabObservableFourCellSourcePairs
          D rootFaceId targetFaceId) ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs
          D rootFaceId targetFaceId) := by
  exact sourceWeightedRowMass_total_le_of_dependentKernelCapacity
    (slabObservableFourCellSourcePairs D rootFaceId targetFaceId)
    (slabObservableTwoReplicaPairWeight D)
    data.rowMass
    (slabObservableFourCellTargetPairs D rootFaceId targetFaceId)
    (slabObservableTwoReplicaPairWeight D)
    data.Choice data.choices data.localWeight data.realize
    (slabObservableFourCellTargetPairs_nodup
      D rootFaceId targetFaceId)
    data.coverage data.row_mass data.column_capacity

/-- Full row mass on the disconnected sector makes its transported weight
exactly the original disconnected physical weight. -/
theorem disconnectedTransportedWeight_eqv
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedAggregatePosteriorTransport
      D rootFaceId targetFaceId) :
    listQSum
        (fun source =>
          slabObservableTwoReplicaPairWeight D source * data.rowMass source)
        (slabObservablePairedSupportSeparatedFourCellSourcePairs
          D rootFaceId targetFaceId) ≈
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportSeparatedFourCellSourcePairs
          D rootFaceId targetFaceId) := by
  apply listQSum_congr_on
  intro source hsource
  have hfour : source ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId := (List.mem_filter.mp hsource).1
  have hnot := (List.mem_filter.mp hsource).2
  have hfalse := bool_eq_false_of_not_eq_true_local
    (slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId source) hnot
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left
      (slabObservableTwoReplicaPairWeight D source)
      (data.rowMass source) 1
      (data.disconnected_row_mass source hfour hfalse))
    (Q'.mul_one_eqv (slabObservableTwoReplicaPairWeight D source))

/-- The aggregate floor and full disconnected rows spend at least
`disconnected + fraction * connected` of the source carrier. -/
theorem disconnected_add_fraction_mul_connected_le_target
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedAggregatePosteriorTransport
      D rootFaceId targetFaceId) :
    let disconnected :=
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportSeparatedFourCellSourcePairs
          D rootFaceId targetFaceId)
    let connected :=
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId)
    let target :=
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs
          D rootFaceId targetFaceId)
    disconnected + data.fraction * connected ≤ target := by
  let transported := fun source =>
    slabObservableTwoReplicaPairWeight D source * data.rowMass source
  let sources := slabObservableFourCellSourcePairs
    D rootFaceId targetFaceId
  let connectedSources :=
    slabObservablePairedSupportConnectedFourCellSourcePairs
      D rootFaceId targetFaceId
  let disconnectedSources :=
    slabObservablePairedSupportSeparatedFourCellSourcePairs
      D rootFaceId targetFaceId
  let connectedTransported := listQSum transported connectedSources
  let disconnectedTransported := listQSum transported disconnectedSources
  let disconnected := listQSum (slabObservableTwoReplicaPairWeight D)
    disconnectedSources
  let connected := listQSum (slabObservableTwoReplicaPairWeight D)
    connectedSources
  let target := listQSum (slabObservableTwoReplicaPairWeight D)
    (slabObservableFourCellTargetPairs D rootFaceId targetFaceId)
  have hpartition := listQSum_filter_partition transported
    (fun source => slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId source) sources
  have hsplit :
      listQSum transported sources ≈
        disconnected + connectedTransported := by
    exact Q'.eqv_trans _ _ _ hpartition
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left connectedTransported
          disconnectedTransported disconnected
          data.disconnectedTransportedWeight_eqv)
        (Q'.add_comm_eqv connectedTransported disconnected))
  have hfull : disconnected + connectedTransported ≤ target :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm hsplit))
      data.transportedRowMass_weight_le_target
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add (Q'.le_refl' disconnected)
      data.connected_transported_floor)
    hfull

/-- The aggregate posterior fraction improves the connected residue from
coefficient one to the exact complement `1 - fraction`. -/
theorem sourceWeight_le_target_add_connectedDefect
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedAggregatePosteriorTransport
      D rootFaceId targetFaceId) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellSourcePairs
          D rootFaceId targetFaceId) ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableFourCellTargetPairs
            D rootFaceId targetFaceId) +
        ((1 : Q') + -data.fraction) *
          listQSum (slabObservableTwoReplicaPairWeight D)
            (slabObservablePairedSupportConnectedFourCellSourcePairs
              D rootFaceId targetFaceId) := by
  let disconnected :=
    listQSum (slabObservableTwoReplicaPairWeight D)
      (slabObservablePairedSupportSeparatedFourCellSourcePairs
        D rootFaceId targetFaceId)
  let connected :=
    listQSum (slabObservableTwoReplicaPairWeight D)
      (slabObservablePairedSupportConnectedFourCellSourcePairs
        D rootFaceId targetFaceId)
  let target :=
    listQSum (slabObservableTwoReplicaPairWeight D)
      (slabObservableFourCellTargetPairs D rootFaceId targetFaceId)
  have hspent : disconnected + data.fraction * connected ≤ target :=
    data.disconnected_add_fraction_mul_connected_le_target
  have hpartition :=
    slabObservableFourCellSourcePairs_pairedSupport_partition
      D rootFaceId targetFaceId
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hpartition)
    (add_connected_le_target_add_complement
      disconnected connected target data.fraction hspent)

/-! ## 3. Contraction of the genuine observable -/

/-- The normalized connected carrier is at most one.  This statement is
independent of how the aggregate transport is subsequently constructed. -/
theorem normalizedConnectedMass_le_one
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (_data : SlabObservablePairedAggregatePosteriorTransport
      D rootFaceId targetFaceId) :
    slabObservableNormalizedPairedSupportConnectedMass
        D rootFaceId targetFaceId ≤ (1 : Q') := by
  let positive := slabObservablePositiveSourceWeight D rootFaceId
  let partition := D.physicalPartition
  have hpartition : (0 : Q') < partition :=
    slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent
  have hpositiveAdd :=
    slabObservablePositiveSourceWeight_add_one_le_partition
      D rootFaceId
  have hpositive : positive ≤ partition :=
    Q'.le_trans' _ (positive + 1) _
      (Q'.add_le_self_of_nonneg positive 1 (by decide))
      hpositiveAdd
  have hconnected :=
    slabObservablePairedSupportConnected_weight_le_positiveSourceProduct
      D rootFaceId targetFaceId
  have hscaled : positive * partition ≤ partition * partition :=
    Q'.mul_le_mul_of_nonneg_right _ _ partition hpositive
      (Q'.le_of_lt hpartition)
  have hnumerator := Q'.le_trans' _ _ _ hconnected hscaled
  unfold slabObservableNormalizedPairedSupportConnectedMass
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ hnumerator
    (Q'.ge_of_eqv (Q'.one_mul_eqv (partition * partition)))

/-- The ordinary centered Boolean face covariance is bounded by the aggregate
posterior complement times the exact connected-carrier probability. -/
theorem faceBooleanCovariance_le_complement_mul_connectedMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedAggregatePosteriorTransport
      D rootFaceId targetFaceId) :
    slabObservableFaceBooleanCovariance D rootFaceId targetFaceId ≤
      ((1 : Q') + -data.fraction) *
        slabObservableNormalizedPairedSupportConnectedMass
          D rootFaceId targetFaceId := by
  let connected := listQSum (slabObservableTwoReplicaPairWeight D)
    (slabObservablePairedSupportConnectedFourCellSourcePairs
      D rootFaceId targetFaceId)
  let denominator := D.physicalPartition * D.physicalPartition
  have hdenominator : (0 : Q') < denominator :=
    YMGap.Continuum.HKPos.q_mul_pos
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)
  have hsource := data.sourceWeight_le_target_add_connectedDefect
  have hsourceProduct := slabObservableFourCellSourcePairs_weight_product
    D rootFaceId targetFaceId
  have htargetProduct := slabObservableFourCellTargetPairs_weight_product
    D rootFaceId targetFaceId
  have hdefect :
      listQSum (slabObservablePositiveEntryWeight D)
            (slabObservableRootTargetEntries
              D rootFaceId targetFaceId) *
          listQSum (slabExpandedFineEntryWeight D)
            (slabObservableRootComplementTargetComplementEntries
              D rootFaceId targetFaceId) ≤
        listQSum (slabObservablePositiveEntryWeight D)
              (slabObservableRootTargetComplementEntries
                D rootFaceId targetFaceId) *
            listQSum (slabExpandedFineEntryWeight D)
              (slabObservableRootComplementTargetEntries
                D rootFaceId targetFaceId) +
          ((1 : Q') + -data.fraction) * connected := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm hsourceProduct))
      (Q'.le_trans' _ _ _ hsource
        (Q'.add_le_add
          (Q'.le_of_eqv htargetProduct) (Q'.le_refl' _)))
  have hnumerator := Q'.sub_le_of_le_add hdefect
  have hnormalized :
      slabObservableNormalizedFourCellExcess
          D rootFaceId targetFaceId ≤
        ((1 : Q') + -data.fraction) *
          Q'.divPos connected denominator hdenominator := by
    unfold slabObservableNormalizedFourCellExcess
    apply Q'.divPos_le_of_le_mul
    have hrecover :
        (((1 : Q') + -data.fraction) *
            Q'.divPos connected denominator hdenominator) * denominator ≈
          ((1 : Q') + -data.fraction) * connected := by
      exact Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv
          ((1 : Q') + -data.fraction)
          (Q'.divPos connected denominator hdenominator) denominator)
        (Q'.mul_eqv_congr_left ((1 : Q') + -data.fraction) _ _
          (Q'.divPos_mul_eqv connected denominator hdenominator))
    exact Q'.le_trans' _ _ _ hnumerator (Q'.ge_of_eqv hrecover)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (slabObservableFaceBooleanCovariance_eqv_normalizedFourCellExcess
        D rootFaceId targetFaceId))
    hnormalized

/-- **Strict finite observable rate from an aggregate posterior floor.** -/
theorem faceBooleanCovariance_le_complement
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedAggregatePosteriorTransport
      D rootFaceId targetFaceId) :
    slabObservableFaceBooleanCovariance D rootFaceId targetFaceId ≤
      (1 : Q') + -data.fraction := by
  exact Q'.le_trans' _ _ _
    data.faceBooleanCovariance_le_complement_mul_connectedMass
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _
        ((1 : Q') + -data.fraction)
        data.normalizedConnectedMass_le_one
        data.complement_nonnegative)
      (Q'.le_of_eqv
        (Q'.mul_one_eqv ((1 : Q') + -data.fraction))))

theorem faceBooleanCovariance_lt_one
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedAggregatePosteriorTransport
      D rootFaceId targetFaceId) :
    slabObservableFaceBooleanCovariance D rootFaceId targetFaceId <
      (1 : Q') :=
  Q'.lt_of_le_of_lt data.faceBooleanCovariance_le_complement
    data.complement_lt_one

/-! ## 4. The same rate on the genuine same-object OS moment -/

/-- For a lower face and its reflected partner, the aggregate posterior rate
bounds the connected form of one literal face indicator under the physical
BF4 conditional operator. -/
theorem sameObjectConnectedMarkovMoment_le_complement
    {D : SlabPhysicalData} {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half)
    (data : SlabObservablePairedAggregatePosteriorTransport
      D rootFaceId (slabFaceReflectId D.extent rootFaceId)) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId ≤
      (1 : Q') + -data.fraction := by
  let targetFaceId := slabFaceReflectId D.extent rootFaceId
  have hsame := slabPhysicalReflectedFaceBooleanCovariance_eqv_sameObject
    D hroot
  have hphysical := slabObservableFaceBooleanCovariance_eqv_physical
    D rootFaceId targetFaceId
  have htoObservable :
      slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId ≈
        slabObservableFaceBooleanCovariance D rootFaceId targetFaceId :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm hsame) (Q'.eqv_symm hphysical)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htoObservable)
    data.faceBooleanCovariance_le_complement

theorem sameObjectConnectedMarkovMoment_lt_one
    {D : SlabPhysicalData} {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half)
    (data : SlabObservablePairedAggregatePosteriorTransport
      D rootFaceId (slabFaceReflectId D.extent rootFaceId)) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId <
      (1 : Q') :=
  Q'.lt_of_le_of_lt
    (data.sameObjectConnectedMarkovMoment_le_complement hroot)
    data.complement_lt_one

end SlabObservablePairedAggregatePosteriorTransport

end YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport.SlabObservablePairedAggregatePosteriorTransport.complement_lt_one
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport.SlabObservablePairedAggregatePosteriorTransport.transportedRowMass_weight_le_target
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport.SlabObservablePairedAggregatePosteriorTransport.disconnectedTransportedWeight_eqv
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport.SlabObservablePairedAggregatePosteriorTransport.disconnected_add_fraction_mul_connected_le_target
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport.SlabObservablePairedAggregatePosteriorTransport.sourceWeight_le_target_add_connectedDefect
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport.SlabObservablePairedAggregatePosteriorTransport.normalizedConnectedMass_le_one
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport.SlabObservablePairedAggregatePosteriorTransport.faceBooleanCovariance_le_complement_mul_connectedMass
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport.SlabObservablePairedAggregatePosteriorTransport.faceBooleanCovariance_lt_one
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport.SlabObservablePairedAggregatePosteriorTransport.sameObjectConnectedMarkovMoment_le_complement
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportAggregatePosteriorTransport.SlabObservablePairedAggregatePosteriorTransport.sameObjectConnectedMarkovMoment_lt_one
