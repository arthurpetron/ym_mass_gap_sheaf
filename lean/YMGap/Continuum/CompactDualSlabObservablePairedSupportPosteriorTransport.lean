/-
# A shared-column posterior fraction for the literal paired face observable

The arbitrary-coupling SU(2) switch transports every support-disconnected
source row into the opposite Boolean four-cell.  The connected carrier is the
only obstruction.  A second, independently normalized transport would be
mathematically invalid: it could spend the same target-column capacity a
second time.

This module exposes the weakest honest strengthening.  One joint dependent
kernel is defined on the complete source four-cell.  Its row mass is exactly
one on disconnected sources and a displayed positive fraction `delta` on
connected sources, while one shared weighted column-capacity inequality is
required over both sectors together.  Exact finite Fubini then leaves only
the complementary fraction `1 - delta` of the connected carrier.

Since the connected carrier has normalized mass at most one, this gives the
literal face covariance the strict rate `1 - delta < 1`.  Thus the certificate
is an observable-connected posterior-variance/coercivity interface, rather
than an opaque assumption that the desired covariance is already small.

No posterior transport is inhabited here.  In particular, no positive
fraction uniform in coupling, cutoff, volume, or lattice spacing is asserted;
no all-observable completed spectral gap, continuum Yang--Mills theory, or
Clay conclusion follows.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness
import YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport

set_option autoImplicit false

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
open YMGap.Continuum.CompactDualSlabObservablePairedSupportTwoStep
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelCapacity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

local instance posteriorPairDecidableEq
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

private theorem listQSum_mul_if_eqv_mul_filter
    {A : Type} (weight : A → Q') (coefficient : Q')
    (test : A → Bool) : ∀ items : List A,
    listQSum
        (fun item => weight item *
          (if test item then coefficient else 0))
        items ≈
      coefficient * listQSum weight (items.filter test)
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv coefficient)
  | head :: tail => by
      cases htest : test head with
      | false =>
          simp only [listQSum, List.filter_cons, htest,
            Bool.false_eq_true, if_false]
          exact Q'.eqv_trans _ _ _
            (Q'.add_eqv_congr'
              (Q'.mul_zero_eqv (weight head))
              (listQSum_mul_if_eqv_mul_filter
                weight coefficient test tail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [listQSum, List.filter_cons, htest, if_true]
          refine Q'.eqv_trans _
            (coefficient * weight head +
              coefficient * listQSum weight (tail.filter test)) _ ?_ ?_
          · exact Q'.add_eqv_congr'
              (Q'.mul_comm_eqv (weight head) coefficient)
              (listQSum_mul_if_eqv_mul_filter
                weight coefficient test tail)
          · exact Q'.eqv_symm
              (Q'.mul_add_eqv coefficient
                (weight head) (listQSum weight (tail.filter test)))

/-! ## 1. Exact transported and untransported row fractions -/

/-- Row mass requested from the joint posterior kernel: all disconnected
mass, but only the displayed fraction of connected mass. -/
def slabObservablePairedPosteriorRowMass
    (fraction : Q') (D : SlabPhysicalData)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservableTwoReplicaPair D rootFaceId) : Q' :=
  if slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId source then fraction else 1

/-- The exact untransported complement of the preceding row mass. -/
def slabObservablePairedPosteriorDefectRate
    (fraction : Q') (D : SlabPhysicalData)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservableTwoReplicaPair D rootFaceId) : Q' :=
  if slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId source
    then (1 : Q') + -fraction else 0

theorem slabObservablePairedPosteriorRowMass_add_defectRate
    (fraction : Q') (D : SlabPhysicalData)
    (rootFaceId targetFaceId : Nat)
    (source : SlabObservableTwoReplicaPair D rootFaceId) :
    slabObservablePairedPosteriorRowMass
          fraction D rootFaceId targetFaceId source +
        slabObservablePairedPosteriorDefectRate
          fraction D rootFaceId targetFaceId source ≈ 1 := by
  unfold slabObservablePairedPosteriorRowMass
    slabObservablePairedPosteriorDefectRate
  cases hconnected :
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId source with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_of_eq (Q'.add_zero' 1)
  | true =>
      simp only [if_true]
      exact Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv fraction ((1 : Q') + -fraction))
        (one_sub_add_eqv_one fraction)

/-! ## 2. The one shared-column posterior transport certificate -/

/-- A literal posterior transport on the complete observable source cell.
The load-bearing field is `column_capacity`: disconnected and connected rows
share one target budget.  `localWeight_nonnegative` records that the rows are
actual finite positive kernels, although finite Fubini needs only their exact
mass and the weighted column inequality. -/
structure SlabObservablePairedPosteriorTransport
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Type 1 where
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ (1 : Q')
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
    listQSum (localWeight source) (choices source) ≈
      slabObservablePairedPosteriorRowMass
        fraction D rootFaceId targetFaceId source
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

namespace SlabObservablePairedPosteriorTransport

/-- The explicit posterior complement is nonnegative. -/
theorem complement_nonnegative
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedPosteriorTransport
      D rootFaceId targetFaceId) :
    (0 : Q') ≤ (1 : Q') + -data.fraction :=
  Q'.sub_nonneg_of_le data.fraction_le_one

/-- A positive transported posterior fraction makes its complement strictly
subunit. -/
theorem complement_lt_one
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedPosteriorTransport
      D rootFaceId targetFaceId) :
    (1 : Q') + -data.fraction < (1 : Q') := by
  have hadd := lt_add_of_pos_right_local
    ((1 : Q') + -data.fraction) data.fraction data.fraction_pos
  exact q_lt_of_lt_of_le_local hadd
    (Q'.le_of_eqv (one_sub_add_eqv_one data.fraction))

/-- Finite Fubini spends the common target columns only once. -/
theorem transportedRowMass_weight_le_target
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedPosteriorTransport
      D rootFaceId targetFaceId) :
    listQSum
        (fun source =>
          slabObservableTwoReplicaPairWeight D source *
            slabObservablePairedPosteriorRowMass
              data.fraction D rootFaceId targetFaceId source)
        (slabObservableFourCellSourcePairs
          D rootFaceId targetFaceId) ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs
          D rootFaceId targetFaceId) := by
  exact sourceWeightedRowMass_total_le_of_dependentKernelCapacity
    (slabObservableFourCellSourcePairs D rootFaceId targetFaceId)
    (slabObservableTwoReplicaPairWeight D)
    (slabObservablePairedPosteriorRowMass
      data.fraction D rootFaceId targetFaceId)
    (slabObservableFourCellTargetPairs D rootFaceId targetFaceId)
    (slabObservableTwoReplicaPairWeight D)
    data.Choice data.choices data.localWeight data.realize
    (slabObservableFourCellTargetPairs_nodup
      D rootFaceId targetFaceId)
    data.coverage data.row_mass data.column_capacity

/-- The untransported row weight is exactly the complementary fraction of
the literal connected carrier, not a surrogate observable. -/
theorem defectRowMass_weight_eqv_connected
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedPosteriorTransport
      D rootFaceId targetFaceId) :
    listQSum
        (fun source =>
          slabObservableTwoReplicaPairWeight D source *
            slabObservablePairedPosteriorDefectRate
              data.fraction D rootFaceId targetFaceId source)
        (slabObservableFourCellSourcePairs
          D rootFaceId targetFaceId) ≈
      ((1 : Q') + -data.fraction) *
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            D rootFaceId targetFaceId) := by
  unfold slabObservablePairedPosteriorDefectRate
    slabObservablePairedSupportConnectedFourCellSourcePairs
  exact listQSum_mul_if_eqv_mul_filter
    (slabObservableTwoReplicaPairWeight D)
    ((1 : Q') + -data.fraction)
    (fun source =>
      slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId source)
    (slabObservableFourCellSourcePairs D rootFaceId targetFaceId)

/-- Exact decomposition of total source mass into the transported row mass
and the untransported connected fraction. -/
theorem sourceWeight_eqv_transported_add_connectedDefect
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedPosteriorTransport
      D rootFaceId targetFaceId) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellSourcePairs
          D rootFaceId targetFaceId) ≈
      listQSum
          (fun source =>
            slabObservableTwoReplicaPairWeight D source *
              slabObservablePairedPosteriorRowMass
                data.fraction D rootFaceId targetFaceId source)
          (slabObservableFourCellSourcePairs
            D rootFaceId targetFaceId) +
        ((1 : Q') + -data.fraction) *
          listQSum (slabObservableTwoReplicaPairWeight D)
            (slabObservablePairedSupportConnectedFourCellSourcePairs
              D rootFaceId targetFaceId) := by
  let sources := slabObservableFourCellSourcePairs
    D rootFaceId targetFaceId
  let weight : SlabObservableTwoReplicaPair D rootFaceId → Q' :=
    fun source => slabObservableTwoReplicaPairWeight D source
  let transported := fun source => weight source *
    slabObservablePairedPosteriorRowMass
      data.fraction D rootFaceId targetFaceId source
  let defect := fun source => weight source *
    slabObservablePairedPosteriorDefectRate
      data.fraction D rootFaceId targetFaceId source
  have hpoint : ∀ source,
      weight source ≈ transported source + defect source := by
    intro source
    let row := slabObservablePairedPosteriorRowMass
      data.fraction D rootFaceId targetFaceId source
    let missing := slabObservablePairedPosteriorDefectRate
      data.fraction D rootFaceId targetFaceId source
    have hrow : row + missing ≈ 1 :=
      slabObservablePairedPosteriorRowMass_add_defectRate
        data.fraction D rootFaceId targetFaceId source
    have hcollapse : weight source * (row + missing) ≈ weight source :=
      Q'.eqv_trans _ (weight source * 1) _
        (Q'.mul_eqv_congr_left (weight source) _ _ hrow)
        (Q'.mul_one_eqv (weight source))
    have hdistribute : weight source * (row + missing) ≈
        weight source * row + weight source * missing :=
      Q'.mul_add_eqv (weight source) row missing
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm hcollapse) hdistribute
  have hsplit :
      listQSum weight sources ≈
        listQSum transported sources + listQSum defect sources := by
    exact Q'.eqv_trans _ _ _
      (listQSum_congr hpoint sources)
      (listQSum_add transported defect sources)
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.add_eqv_congr_left
      (listQSum transported sources)
      (listQSum defect sources)
      (((1 : Q') + -data.fraction) *
        listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            D rootFaceId targetFaceId))
      data.defectRowMass_weight_eqv_connected)

/-- The joint posterior transport improves the old connected-residue defect
from coefficient one to the exact complement `1 - delta`. -/
theorem sourceWeight_le_target_add_connectedDefect
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedPosteriorTransport
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
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv data.sourceWeight_eqv_transported_add_connectedDefect)
    (Q'.add_le_add data.transportedRowMass_weight_le_target
      (Q'.le_refl' _))

/-! ## 3. Posterior fraction contracts the actual Boolean covariance -/

/-- The normalized connected carrier is at most one.  This uses only its
literal inclusion in the positive-first-replica product and the exact vacuum
complement in the one-replica partition. -/
theorem normalizedConnectedMass_le_one
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (_data : SlabObservablePairedPosteriorTransport
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

/-- The ordinary centered Boolean face covariance is bounded by the exact
posterior complement times the exact connected-carrier probability. -/
theorem faceBooleanCovariance_le_complement_mul_connectedMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedPosteriorTransport
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
        (Q'.add_le_add (Q'.le_of_eqv htargetProduct) (Q'.le_refl' _)))
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

/-- **Strict finite observable rate from a positive posterior fraction.** -/
theorem faceBooleanCovariance_le_complement
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedPosteriorTransport
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
      (Q'.le_of_eqv (Q'.mul_one_eqv ((1 : Q') + -data.fraction))))

theorem faceBooleanCovariance_lt_one
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedPosteriorTransport
      D rootFaceId targetFaceId) :
    slabObservableFaceBooleanCovariance D rootFaceId targetFaceId <
      (1 : Q') :=
  Q'.lt_of_le_of_lt data.faceBooleanCovariance_le_complement
    data.complement_lt_one

/-! ## 4. The same rate is on the genuine same-object OS moment -/

/-- For a lower face and its reflected partner, the posterior rate bounds the
connected form of one literal face indicator under the physical BF4
conditional operator. -/
theorem sameObjectConnectedMarkovMoment_le_complement
    {D : SlabPhysicalData} {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half)
    (data : SlabObservablePairedPosteriorTransport
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
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hsame) (Q'.eqv_symm hphysical)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htoObservable)
    data.faceBooleanCovariance_le_complement

theorem sameObjectConnectedMarkovMoment_lt_one
    {D : SlabPhysicalData} {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half)
    (data : SlabObservablePairedPosteriorTransport
      D rootFaceId (slabFaceReflectId D.extent rootFaceId)) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId <
      (1 : Q') :=
  Q'.lt_of_le_of_lt
    (data.sameObjectConnectedMarkovMoment_le_complement hroot)
    data.complement_lt_one

end SlabObservablePairedPosteriorTransport

end YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport.slabObservablePairedPosteriorRowMass_add_defectRate
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport.SlabObservablePairedPosteriorTransport.complement_lt_one
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport.SlabObservablePairedPosteriorTransport.transportedRowMass_weight_le_target
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport.SlabObservablePairedPosteriorTransport.defectRowMass_weight_eqv_connected
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport.SlabObservablePairedPosteriorTransport.sourceWeight_le_target_add_connectedDefect
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport.SlabObservablePairedPosteriorTransport.normalizedConnectedMass_le_one
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport.SlabObservablePairedPosteriorTransport.faceBooleanCovariance_le_complement_mul_connectedMass
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport.SlabObservablePairedPosteriorTransport.faceBooleanCovariance_lt_one
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport.SlabObservablePairedPosteriorTransport.sameObjectConnectedMarkovMoment_le_complement
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportPosteriorTransport.SlabObservablePairedPosteriorTransport.sameObjectConnectedMarkovMoment_lt_one
