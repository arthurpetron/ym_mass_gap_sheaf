/-
# Strict observable contraction from the split retained fraction

The disconnected full switch and the thinned connected switch already spend
disjoint target sectors.  Once the retained connected mass is written as
`delta * connectedSourceMass`, their shared budget becomes

  disconnected + delta * connected <= target.

This module packages exactly that inequality and contracts it through the
literal Boolean four-cell identity.  The result is a strict finite bound by
`1 - delta` for both the face covariance and, at a reflected face pair, the
same-object connected moment of the genuine physical BF4 conditional
operator.

The construction remains conditional on one positive connected channel and
on positive coupling.  Its `delta` depends on the complete finite datum; no
parameter-uniform spectral or continuum conclusion is asserted.

Constructive contract: exact finite sector algebra, positive rational order,
and the existing observable/OS equalities only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction
import YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge

namespace YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity
open YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabObservablePairedSupportTwoStep
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

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
  exact Int.lt_of_mul_lt_mul_right
    (Int.lt_of_lt_of_le hfirst hsecond)
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
  have hden : (0 : Int) < (a.den : Int) := by
    exact_mod_cast a.den_pos
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
    (Q'.add_le_add hspent (Q'.le_refl' _))

/-! ## 1. The contracted split-sector certificate -/

structure SlabObservablePairedSplitRetainedContraction
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) where
  fraction : Q'
  fraction_pos : (0 : Q') < fraction
  fraction_le_one : fraction ≤ 1
  disconnected_add_fraction_mul_connected_le_target :
    listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservablePairedSupportSeparatedFourCellSourcePairs
            D rootFaceId targetFaceId) +
        fraction * slabObservablePairedConnectedSourceMass
          D rootFaceId targetFaceId ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellTargetPairs
          D rootFaceId targetFaceId)

/-- The actual split transport and a positive-channel witness construct the
finite contraction certificate. -/
def slabObservablePairedSplitRetainedContraction
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (witness : SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId) :
    SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId := by
  let retained :=
    slabObservablePairedConnectedRetainedFractionCertificate
      D hcoupling rootFaceId targetFaceId htarget witness
  refine
    { fraction := retained.delta
      fraction_pos := retained.delta_pos
      fraction_le_one := retained.delta_le_one
      disconnected_add_fraction_mul_connected_le_target := ?_ }
  have hid : retained.delta *
      slabObservablePairedConnectedSourceMass
        D rootFaceId targetFaceId ≈
    slabObservablePairedConnectedStrandThinnedTransportedMass
      D rootFaceId targetFaceId htarget :=
    retained.delta_mul_sourceMass_eqv
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.add_eqv_congr'
        (Q'.eqv_refl _)
        hid))
    (slabObservablePairedSplitTransportedMass_le_target
      D rootFaceId targetFaceId htarget)

namespace SlabObservablePairedSplitRetainedContraction

theorem complement_nonnegative
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId) :
    (0 : Q') ≤ (1 : Q') + -data.fraction :=
  Q'.sub_nonneg_of_le data.fraction_le_one

theorem complement_lt_one
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId) :
    (1 : Q') + -data.fraction < (1 : Q') := by
  have hadd := lt_add_of_pos_right_local
    ((1 : Q') + -data.fraction) data.fraction data.fraction_pos
  exact q_lt_of_lt_of_le_local hadd
    (Q'.le_of_eqv (one_sub_add_eqv_one data.fraction))

theorem sourceWeight_le_target_add_connectedDefect
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservableFourCellSourcePairs
          D rootFaceId targetFaceId) ≤
      listQSum (slabObservableTwoReplicaPairWeight D)
          (slabObservableFourCellTargetPairs
            D rootFaceId targetFaceId) +
        ((1 : Q') + -data.fraction) *
          slabObservablePairedConnectedSourceMass
            D rootFaceId targetFaceId := by
  have hpartition :=
    slabObservableFourCellSourcePairs_pairedSupport_partition
      D rootFaceId targetFaceId
  unfold slabObservablePairedConnectedSourceMass
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hpartition)
    (add_connected_le_target_add_complement _ _ _ data.fraction
      data.disconnected_add_fraction_mul_connected_le_target)

theorem normalizedConnectedMass_le_one
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (_data : SlabObservablePairedSplitRetainedContraction
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
  unfold slabObservableNormalizedPairedSupportConnectedMass
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _ hconnected hscaled)
    (Q'.ge_of_eqv (Q'.one_mul_eqv (partition * partition)))

theorem faceBooleanCovariance_le_complement_mul_connectedMass
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId) :
    slabObservableFaceBooleanCovariance D rootFaceId targetFaceId ≤
      ((1 : Q') + -data.fraction) *
        slabObservableNormalizedPairedSupportConnectedMass
          D rootFaceId targetFaceId := by
  let connected := slabObservablePairedConnectedSourceMass
    D rootFaceId targetFaceId
  let denominator := D.physicalPartition * D.physicalPartition
  have hdenominator : (0 : Q') < denominator :=
    Q'.mul_pos
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
            Q'.divPos connected denominator hdenominator) *
              denominator ≈
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

theorem faceBooleanCovariance_le_complement
    {D : SlabPhysicalData} {rootFaceId targetFaceId : Nat}
    (data : SlabObservablePairedSplitRetainedContraction
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
    (data : SlabObservablePairedSplitRetainedContraction
      D rootFaceId targetFaceId) :
    slabObservableFaceBooleanCovariance D rootFaceId targetFaceId < 1 :=
  Q'.lt_of_le_of_lt data.faceBooleanCovariance_le_complement
    data.complement_lt_one

/-- At a reflected face pair, the same finite fraction contracts the genuine
same-object connected BF4 conditional moment. -/
theorem sameObjectConnectedMarkovMoment_le_complement
    {D : SlabPhysicalData} {rootFaceId : Nat}
    (hroot : rootFaceId ∈ centralLowerFaceIds D.half)
    (data : SlabObservablePairedSplitRetainedContraction
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
    (data : SlabObservablePairedSplitRetainedContraction
      D rootFaceId (slabFaceReflectId D.extent rootFaceId)) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment D rootFaceId < 1 :=
  Q'.lt_of_le_of_lt
    (data.sameObjectConnectedMarkovMoment_le_complement hroot)
    data.complement_lt_one

end SlabObservablePairedSplitRetainedContraction

end YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction.slabObservablePairedSplitRetainedContraction
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction.SlabObservablePairedSplitRetainedContraction.sourceWeight_le_target_add_connectedDefect
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction.SlabObservablePairedSplitRetainedContraction.faceBooleanCovariance_le_complement
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction.SlabObservablePairedSplitRetainedContraction.faceBooleanCovariance_lt_one
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction.SlabObservablePairedSplitRetainedContraction.sameObjectConnectedMarkovMoment_le_complement
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction.SlabObservablePairedSplitRetainedContraction.sameObjectConnectedMarkovMoment_lt_one
