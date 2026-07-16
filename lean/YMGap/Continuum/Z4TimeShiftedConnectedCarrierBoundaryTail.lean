/-
# Geometric shell summation for the affine shifted carrier

This file sums the frozen fixed-size carrier estimate over every possible
support size.  The shifted geometric floor is used in an explicit finite
injection, and the derived ratio `anchorDecoratedEffectiveRatio <= 1/2`
closes the shell with no limiting or compactness hypothesis.
-/

import YMGap.Continuum.Z4TimeShiftedConnectedCarrierTail

namespace YMGap.Continuum.Z4TimeShiftedConnectedCarrierBoundaryTail

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4ShiftedSubboxCarrierTail
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4TimeShiftedConnectedCarrier
open YMGap.Continuum.Z4TimeShiftedConnectedCarrierTail
open YMGap.Continuum.Z4TimeShiftedCylinderSwitchSummation
open YMGap.Continuum.Z4TimeShiftedEmbeddedCylinder
open YMGap.Continuum.Z4TimeShiftedEmbeddedRegion
open YMGap.Continuum.Z4TimeShiftedPhysicalTransport

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

private theorem ofNat_nonnegative_local (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

abbrev TimeShiftShiftedRootCarrier (shift base : Nat) :=
  Nat × (CanonicalAtom (base + shift) × ConnectedCarrier)

local instance timeShiftShiftedRootCarrierDecidableEq
    (shift base : Nat) :
    DecidableEq (TimeShiftShiftedRootCarrier shift base) := by
  letI : DecidableEq
      (CanonicalAtom (base + shift) × ConnectedCarrier) := inferInstance
  exact inferInstance

def timeShiftShiftedRootCarrierTargetWeight
    (coupling : Q') (cutoff shift base floor : Nat)
    (tagged : TimeShiftShiftedRootCarrier shift base) : Q' :=
  timeShiftRootCarrierTargetWeight coupling cutoff shift base
    (floor + tagged.1) tagged.2

def timeShiftShiftedRootCarrierTargetList
    (shift base : Nat)
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (roots : List (CanonicalAtom (base + shift))) (floor : Nat) :
    Nat → List (TimeShiftShiftedRootCarrier shift base)
  | 0 => []
  | depth + 1 =>
      timeShiftShiftedRootCarrierTargetList
          shift base rootStart roots floor depth ++
        (timeShiftRootCarrierTargetList rootStart roots
          (floor + depth)).map (fun tagged => (depth, tagged))

theorem mem_timeShiftShiftedRootCarrierTargetList_of_lt
    (shift base : Nat)
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (roots : List (CanonicalAtom (base + shift))) (floor : Nat)
    {offset depth : Nat}
    (hoffset : offset < depth)
    {tagged : CanonicalAtom (base + shift) × ConnectedCarrier}
    (htagged : tagged ∈ timeShiftRootCarrierTargetList
      rootStart roots (floor + offset)) :
    (offset, tagged) ∈ timeShiftShiftedRootCarrierTargetList
      shift base rootStart roots floor depth := by
  induction depth with
  | zero => omega
  | succ depth ih =>
      unfold timeShiftShiftedRootCarrierTargetList
      cases heq : decide (offset = depth) with
      | true =>
          have hoffEq : offset = depth := of_decide_eq_true heq
          subst offset
          apply List.mem_append_right
          exact List.mem_map.mpr ⟨tagged, htagged, rfl⟩
      | false =>
          have hoffNe : offset ≠ depth := of_decide_eq_false heq
          apply List.mem_append_left
          apply ih
          omega

theorem timeShiftShiftedRootCarrierTargetSum_eqv_finSum
    (coupling : Q') (cutoff shift base floor : Nat)
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (roots : List (CanonicalAtom (base + shift))) :
    ∀ depth : Nat,
    listQSum
        (timeShiftShiftedRootCarrierTargetWeight
          coupling cutoff shift base floor)
        (timeShiftShiftedRootCarrierTargetList
          shift base rootStart roots floor depth) ≈
      finSum (fun offset =>
        listQSum
          (timeShiftRootCarrierTargetWeight coupling cutoff
            shift base (floor + offset))
          (timeShiftRootCarrierTargetList rootStart roots
            (floor + offset))) depth
  | 0 => Q'.eqv_refl 0
  | depth + 1 => by
      rw [finSum_succ]
      unfold timeShiftShiftedRootCarrierTargetList
      refine Q'.eqv_trans _ _ _
        (listQSum_append
          (timeShiftShiftedRootCarrierTargetWeight
            coupling cutoff shift base floor)
          (timeShiftShiftedRootCarrierTargetList
            shift base rootStart roots floor depth)
          ((timeShiftRootCarrierTargetList rootStart roots
            (floor + depth)).map (fun tagged => (depth, tagged)))) ?_
      refine Q'.add_eqv_congr'
        (timeShiftShiftedRootCarrierTargetSum_eqv_finSum
          coupling cutoff shift base floor rootStart roots depth) ?_
      rw [listQSum_map]
      exact Q'.eqv_refl _

theorem timeShiftShiftedRootCarrierTargetSum_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff shift base floor : Nat)
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (roots : List (CanonicalAtom (base + shift))) (depth : Nat) :
    listQSum
        (timeShiftShiftedRootCarrierTargetWeight
          coupling cutoff shift base floor)
        (timeShiftShiftedRootCarrierTargetList
          shift base rootStart roots floor depth) ≤
      Q'.ofNat roots.length *
        ((couplingParametricKCompatibleSupportGasPartition
              coupling cutoff (base + shift) *
            couplingParametricKTimeShiftEmbeddedTargetPartition
              coupling cutoff shift base) *
          (anchorDecoratedEffectiveRatio ^ floor * Q'.ofNat 2)) := by
  let partitionProduct :=
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (base + shift) *
      couplingParametricKTimeShiftEmbeddedTargetPartition
        coupling cutoff shift base
  let rootScale := Q'.ofNat roots.length
  have htargets := timeShiftShiftedRootCarrierTargetSum_eqv_finSum
    coupling cutoff shift base floor rootStart roots depth
  have hterms :
      finSum (fun offset =>
          listQSum
            (timeShiftRootCarrierTargetWeight coupling cutoff
              shift base (floor + offset))
            (timeShiftRootCarrierTargetList rootStart roots
              (floor + offset))) depth ≤
        finSum (fun offset =>
          rootScale *
            (anchorDecoratedEffectiveRatio ^ (floor + offset) *
              partitionProduct)) depth :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (fun offset => timeShiftRootCarrierTargetSum_le_geom
        hcoupling cutoff shift base (floor + offset) rootStart roots)
      depth
  have hreorder :
      (finSum (fun offset =>
          rootScale *
            (anchorDecoratedEffectiveRatio ^ (floor + offset) *
              partitionProduct)) depth).eqv
        (finSum (fun offset =>
          ((rootScale * partitionProduct) *
              anchorDecoratedEffectiveRatio ^ floor) *
            anchorDecoratedEffectiveRatio ^ offset) depth) := by
    apply RationalTail.finSum_eqv_congr
    intro offset
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left rootScale _ _
        (Q'.mul_eqv_congr_right _ _ partitionProduct
          (Q'.pow_add_eqv anchorDecoratedEffectiveRatio floor offset))) ?_
    ring_qeqv
  have hpull :
      (finSum (fun offset =>
          ((rootScale * partitionProduct) *
              anchorDecoratedEffectiveRatio ^ floor) *
            anchorDecoratedEffectiveRatio ^ offset) depth).eqv
        (((rootScale * partitionProduct) *
            anchorDecoratedEffectiveRatio ^ floor) *
          finSum (fun offset =>
            anchorDecoratedEffectiveRatio ^ offset) depth) :=
    Q'.eqv_symm (RationalTail.const_mul_finSum
      (fun offset => anchorDecoratedEffectiveRatio ^ offset)
      ((rootScale * partitionProduct) *
        anchorDecoratedEffectiveRatio ^ floor) depth)
  have hgeo : finSum (fun offset =>
      anchorDecoratedEffectiveRatio ^ offset) depth ≤ Q'.ofNat 2 :=
    geom_partial_le_two anchorDecoratedEffectiveRatio_nonnegative
      anchorDecoratedEffectiveRatio_le_half depth
  have hpartition0 : (0 : Q') ≤ partitionProduct :=
    Q'.mul_nonneg _ _
      (couplingParametricKCompatibleSupportGasPartition_nonnegative
        hcoupling cutoff (base + shift))
      (timeShiftEmbeddedTargetPartition_nonnegative
        hcoupling cutoff shift base)
  have hscale0 : (0 : Q') ≤
      (rootScale * partitionProduct) *
        anchorDecoratedEffectiveRatio ^ floor :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (ofNat_nonnegative_local roots.length)
        hpartition0)
      (Q'.pow_nonneg anchorDecoratedEffectiveRatio
        anchorDecoratedEffectiveRatio_nonnegative floor)
  have hscaled :
      ((rootScale * partitionProduct) *
            anchorDecoratedEffectiveRatio ^ floor) *
          finSum (fun offset =>
            anchorDecoratedEffectiveRatio ^ offset) depth ≤
        ((rootScale * partitionProduct) *
            anchorDecoratedEffectiveRatio ^ floor) * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgeo hscale0
  have hfinal :
      (((rootScale * partitionProduct) *
          anchorDecoratedEffectiveRatio ^ floor) * Q'.ofNat 2).eqv
        (rootScale *
          (partitionProduct *
            (anchorDecoratedEffectiveRatio ^ floor * Q'.ofNat 2))) := by
    ring_qeqv
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htargets)
    (Q'.le_trans' _ _ _ hterms
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpull)
          (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hfinal)))))

/-! ## 2. Injection of every connected residue into the finite shell -/

theorem timeShiftConnectedCarrierSupport_length_le_ambient
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    (timeShiftConnectedCarrierSupport entry).length ≤
      (physicalFaceEdges (base + shift)).length := by
  have hsupport := timeShiftConnectedCarrierSupport_mem_faceSupports entry
  have hnodup := nodup_of_mem_sublists
    (physicalFaceEdges (base + shift))
    (timeShiftConnectedCarrierSupport entry)
    (physicalFaceEdges_nodup (base + shift)) hsupport
  exact length_le_of_unique_representation
    (fun source target : Nat => source = target)
    (timeShiftConnectedCarrierSupport entry)
    (physicalFaceEdges (base + shift)) hnodup
    (fun face hface =>
      ⟨face, mem_of_mem_sublists (physicalFaceEdges (base + shift))
        (timeShiftConnectedCarrierSupport entry) hsupport face hface, rfl⟩)
    (fun left _ right _ target hleft hright =>
      hleft.trans hright.symm)

def timeShiftConnectedCarrierShiftEncode
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool} (floor : Nat)
    (entry : TimeShiftConnectedEntry shift base roots predicate) :
    TimeShiftShiftedRootCarrier shift base :=
  ((timeShiftConnectedCarrierSupport entry).length - floor,
    timeShiftConnectedRootCarrierEncode entry)

theorem couplingSpinSummedConnectedTimeShiftCylinderPairSum_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {shift base : Nat} {roots : List (CanonicalAtom (base + shift))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideTimeShiftB shift base root.val = true)
    (rootStart : CanonicalAtom (base + shift) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    {lower : Z4Vertex} {inner distance : Nat}
    (hrootCore : ∀ root, root ∈ roots →
      insideShiftedBoxB (addUniform lower distance) inner
        (boxPlaquetteAt (base + shift) (rootStart root)) = true)
    (houterExit : ∀ plaquette,
      plaquette ∉ timeShiftedPlaquetteList shift base →
        outsideShiftedBoxB lower (inner + distance + distance)
          plaquette = true) :
    listQSum
        (couplingSpinSummedTimeShiftCylinderSourcePairWeight
          coupling cutoff)
        (connectedTimeShiftCylinderSourcePairs
          (shift := shift) (base := base)
          (roots := roots) (predicate := predicate)) ≤
      Q'.ofNat roots.length *
        ((couplingParametricKCompatibleSupportGasPartition
              coupling cutoff (base + shift) *
            couplingParametricKTimeShiftEmbeddedTargetPartition
              coupling cutoff shift base) *
          (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2)) := by
  have hinjection := listQSum_le_of_injective
    (connectedTimeShiftCylinderSourcePairs
      (shift := shift) (base := base)
      (roots := roots) (predicate := predicate)).attach
    (timeShiftShiftedRootCarrierTargetList shift base rootStart roots
      (distance + 2) ((physicalFaceEdges (base + shift)).length + 1))
    (fun entry : TimeShiftConnectedEntry shift base roots predicate =>
      couplingSpinSummedTimeShiftCylinderSourcePairWeight
        coupling cutoff entry.val)
    (timeShiftShiftedRootCarrierTargetWeight
      coupling cutoff shift base (distance + 2))
    (timeShiftConnectedCarrierShiftEncode (distance + 2))
    (attach_nodup_of_nodup _
      (List.filter_sublist.nodup
        (timeShiftCylinderSourcePairList_nodup
          shift base roots predicate)))
    (fun entry _ => by
      have hrootMem := timeShiftSourceRootAtom_spec entry |>.2
      have hfloor :=
        timeShiftConnectedCarrierSupport_shifted_boundary_floor
          hrootsInside entry
          (hstartMem _ hrootMem)
          (hrootCore _ hrootMem) houterExit
      have hmax := timeShiftConnectedCarrierSupport_length_le_ambient entry
      let offset := (timeShiftConnectedCarrierSupport entry).length -
        (distance + 2)
      have hoffset : offset <
          (physicalFaceEdges (base + shift)).length + 1 := by
        unfold offset
        omega
      have hsize : (timeShiftConnectedCarrierSupport entry).length =
          distance + 2 + offset := by
        unfold offset
        omega
      apply mem_timeShiftShiftedRootCarrierTargetList_of_lt
        shift base rootStart roots (distance + 2) hoffset
      exact timeShiftConnectedRootCarrierEncode_mem
        hrootsInside rootStart hstartMem entry hsize)
    (fun first _ second _ heq => by
      apply timeShiftConnectedRootCarrierEncode_injective first second
      exact congrArg Prod.snd heq)
    (fun entry _ => by
      have hrootMem := timeShiftSourceRootAtom_spec entry |>.2
      have hfloor :=
        timeShiftConnectedCarrierSupport_shifted_boundary_floor
          hrootsInside entry
          (hstartMem _ hrootMem)
          (hrootCore _ hrootMem) houterExit
      have hsize : distance + 2 +
            ((timeShiftConnectedCarrierSupport entry).length -
              (distance + 2)) =
          (timeShiftConnectedCarrierSupport entry).length := by
        omega
      have hbound :=
        couplingSpinSummedTimeShiftConnectedSourceWeight_le_carrier
          hcoupling hle cutoff entry
      unfold timeShiftConnectedCarrierShiftEncode
        timeShiftShiftedRootCarrierTargetWeight
        timeShiftRootCarrierTargetWeight
        timeShiftConnectedCarrierTargetWeight
        timeShiftConnectedRootCarrierEncode
        timeShiftConnectedCarrier
      rw [hsize]
      simpa [couplingSpinSummedTimeShiftConnectedBackgroundPairWeight]
        using hbound)
    (fun tagged _ => by
      unfold timeShiftShiftedRootCarrierTargetWeight
        timeShiftRootCarrierTargetWeight
        timeShiftConnectedCarrierTargetWeight
      exact Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedFaceEnvelope
          anchorDecoratedFaceEnvelope_nonnegative _)
        (Q'.mul_nonneg _ _
          (couplingParametricKSupportFamilyActivity_nonnegative
            hcoupling cutoff (base + shift) tagged.2.2.2.1)
          (couplingParametricKSupportFamilyActivity_nonnegative
            hcoupling cutoff (base + shift) tagged.2.2.2.2)))
  rw [listQSum_attach] at hinjection
  exact Q'.le_trans' _ _ _ hinjection
    (timeShiftShiftedRootCarrierTargetSum_le_tail
      hcoupling cutoff shift base (distance + 2) rootStart roots
      ((physicalFaceEdges (base + shift)).length + 1))

#print axioms timeShiftShiftedRootCarrierTargetSum_le_tail
#print axioms timeShiftConnectedCarrierSupport_length_le_ambient
#print axioms couplingSpinSummedConnectedTimeShiftCylinderPairSum_le_tail

end YMGap.Continuum.Z4TimeShiftedConnectedCarrierBoundaryTail
