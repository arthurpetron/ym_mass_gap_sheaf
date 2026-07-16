/-
# Geometric shell summation for the affine shifted carrier

This file sums the frozen fixed-size carrier estimate over every possible
support size.  The shifted geometric floor is used in an explicit finite
injection, and the derived ratio `anchorDecoratedEffectiveRatio <= 1/2`
closes the shell with no limiting or compactness hypothesis.
-/

import YMGap.Continuum.Z4UniformShiftConnectedCarrierTail

namespace YMGap.Continuum.Z4UniformShiftConnectedCarrierBoundaryTail

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
open YMGap.Continuum.Z4UniformShiftConnectedCarrier
open YMGap.Continuum.Z4UniformShiftConnectedCarrierTail
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

private theorem ofNat_nonnegative_local (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

abbrev UniformShiftShiftedRootCarrier (padding base : Nat) :=
  Nat × (CanonicalAtom (uniformPaddedBase padding base) × ConnectedCarrier)

local instance uniformShiftShiftedRootCarrierDecidableEq
    (padding base : Nat) :
    DecidableEq (UniformShiftShiftedRootCarrier padding base) := by
  letI : DecidableEq
      (CanonicalAtom (uniformPaddedBase padding base) × ConnectedCarrier) := inferInstance
  exact inferInstance

def uniformShiftShiftedRootCarrierTargetWeight
    (coupling : Q') (cutoff padding base floor : Nat)
    (tagged : UniformShiftShiftedRootCarrier padding base) : Q' :=
  uniformShiftRootCarrierTargetWeight coupling cutoff padding base
    (floor + tagged.1) tagged.2

def uniformShiftShiftedRootCarrierTargetList
    (padding base : Nat)
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base))) (floor : Nat) :
    Nat → List (UniformShiftShiftedRootCarrier padding base)
  | 0 => []
  | depth + 1 =>
      uniformShiftShiftedRootCarrierTargetList
          padding base rootStart roots floor depth ++
        (uniformShiftRootCarrierTargetList rootStart roots
          (floor + depth)).map (fun tagged => (depth, tagged))

theorem mem_uniformShiftShiftedRootCarrierTargetList_of_lt
    (padding base : Nat)
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base))) (floor : Nat)
    {offset depth : Nat}
    (hoffset : offset < depth)
    {tagged : CanonicalAtom (uniformPaddedBase padding base) × ConnectedCarrier}
    (htagged : tagged ∈ uniformShiftRootCarrierTargetList
      rootStart roots (floor + offset)) :
    (offset, tagged) ∈ uniformShiftShiftedRootCarrierTargetList
      padding base rootStart roots floor depth := by
  induction depth with
  | zero => omega
  | succ depth ih =>
      unfold uniformShiftShiftedRootCarrierTargetList
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

theorem uniformShiftShiftedRootCarrierTargetSum_eqv_finSum
    (coupling : Q') (cutoff padding base floor : Nat)
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base))) :
    ∀ depth : Nat,
    listQSum
        (uniformShiftShiftedRootCarrierTargetWeight
          coupling cutoff padding base floor)
        (uniformShiftShiftedRootCarrierTargetList
          padding base rootStart roots floor depth) ≈
      finSum (fun offset =>
        listQSum
          (uniformShiftRootCarrierTargetWeight coupling cutoff
            padding base (floor + offset))
          (uniformShiftRootCarrierTargetList rootStart roots
            (floor + offset))) depth
  | 0 => Q'.eqv_refl 0
  | depth + 1 => by
      rw [finSum_succ]
      unfold uniformShiftShiftedRootCarrierTargetList
      refine Q'.eqv_trans _ _ _
        (listQSum_append
          (uniformShiftShiftedRootCarrierTargetWeight
            coupling cutoff padding base floor)
          (uniformShiftShiftedRootCarrierTargetList
            padding base rootStart roots floor depth)
          ((uniformShiftRootCarrierTargetList rootStart roots
            (floor + depth)).map (fun tagged => (depth, tagged)))) ?_
      refine Q'.add_eqv_congr'
        (uniformShiftShiftedRootCarrierTargetSum_eqv_finSum
          coupling cutoff padding base floor rootStart roots depth) ?_
      rw [listQSum_map]
      exact Q'.eqv_refl _

theorem uniformShiftShiftedRootCarrierTargetSum_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff padding base floor : Nat)
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (roots : List (CanonicalAtom (uniformPaddedBase padding base))) (depth : Nat) :
    listQSum
        (uniformShiftShiftedRootCarrierTargetWeight
          coupling cutoff padding base floor)
        (uniformShiftShiftedRootCarrierTargetList
          padding base rootStart roots floor depth) ≤
      Q'.ofNat roots.length *
        ((couplingParametricKCompatibleSupportGasPartition
              coupling cutoff (uniformPaddedBase padding base) *
            couplingParametricKUniformShiftEmbeddedTargetPartition
              coupling cutoff padding base) *
          (anchorDecoratedEffectiveRatio ^ floor * Q'.ofNat 2)) := by
  let partitionProduct :=
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (uniformPaddedBase padding base) *
      couplingParametricKUniformShiftEmbeddedTargetPartition
        coupling cutoff padding base
  let rootScale := Q'.ofNat roots.length
  have htargets := uniformShiftShiftedRootCarrierTargetSum_eqv_finSum
    coupling cutoff padding base floor rootStart roots depth
  have hterms :
      finSum (fun offset =>
          listQSum
            (uniformShiftRootCarrierTargetWeight coupling cutoff
              padding base (floor + offset))
            (uniformShiftRootCarrierTargetList rootStart roots
              (floor + offset))) depth ≤
        finSum (fun offset =>
          rootScale *
            (anchorDecoratedEffectiveRatio ^ (floor + offset) *
              partitionProduct)) depth :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (fun offset => uniformShiftRootCarrierTargetSum_le_geom
        hcoupling cutoff padding base (floor + offset) rootStart roots)
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
        hcoupling cutoff (uniformPaddedBase padding base))
      (uniformShiftEmbeddedTargetPartition_nonnegative
        hcoupling cutoff padding base)
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

theorem uniformShiftConnectedCarrierSupport_length_le_ambient
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    (uniformShiftConnectedCarrierSupport entry).length ≤
      (physicalFaceEdges (uniformPaddedBase padding base)).length := by
  have hsupport := uniformShiftConnectedCarrierSupport_mem_faceSupports entry
  have hnodup := nodup_of_mem_sublists
    (physicalFaceEdges (uniformPaddedBase padding base))
    (uniformShiftConnectedCarrierSupport entry)
    (physicalFaceEdges_nodup (uniformPaddedBase padding base)) hsupport
  exact length_le_of_unique_representation
    (fun source target : Nat => source = target)
    (uniformShiftConnectedCarrierSupport entry)
    (physicalFaceEdges (uniformPaddedBase padding base)) hnodup
    (fun face hface =>
      ⟨face, mem_of_mem_sublists (physicalFaceEdges (uniformPaddedBase padding base))
        (uniformShiftConnectedCarrierSupport entry) hsupport face hface, rfl⟩)
    (fun left _ right _ target hleft hright =>
      hleft.trans hright.symm)

def uniformShiftConnectedCarrierShiftEncode
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool} (floor : Nat)
    (entry : UniformShiftConnectedEntry padding base roots predicate) :
    UniformShiftShiftedRootCarrier padding base :=
  ((uniformShiftConnectedCarrierSupport entry).length - floor,
    uniformShiftConnectedRootCarrierEncode entry)

theorem couplingSpinSummedConnectedUniformShiftCylinderPairSum_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {padding base : Nat} {roots : List (CanonicalAtom (uniformPaddedBase padding base))}
    {predicate : List Bool → Bool}
    (hrootsInside : ∀ root, root ∈ roots →
      targetRootInsideUniformShiftB padding base root.val = true)
    (rootStart : CanonicalAtom (uniformPaddedBase padding base) → Nat)
    (hstartMem : ∀ root, root ∈ roots → rootStart root ∈ root.val)
    {lower : Z4Vertex} {inner distance : Nat}
    (hrootCore : ∀ root, root ∈ roots →
      insideShiftedBoxB (addUniform lower distance) inner
        (boxPlaquetteAt (uniformPaddedBase padding base) (rootStart root)) = true)
    (houterExit : ∀ plaquette,
      plaquette ∉ uniformShiftedPlaquetteList padding base →
        outsideShiftedBoxB lower (inner + distance + distance)
          plaquette = true) :
    listQSum
        (couplingSpinSummedUniformShiftCylinderSourcePairWeight
          coupling cutoff)
        (connectedUniformShiftCylinderSourcePairs
          (padding := padding) (base := base)
          (roots := roots) (predicate := predicate)) ≤
      Q'.ofNat roots.length *
        ((couplingParametricKCompatibleSupportGasPartition
              coupling cutoff (uniformPaddedBase padding base) *
            couplingParametricKUniformShiftEmbeddedTargetPartition
              coupling cutoff padding base) *
          (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2)) := by
  have hinjection := listQSum_le_of_injective
    (connectedUniformShiftCylinderSourcePairs
      (padding := padding) (base := base)
      (roots := roots) (predicate := predicate)).attach
    (uniformShiftShiftedRootCarrierTargetList padding base rootStart roots
      (distance + 2) ((physicalFaceEdges (uniformPaddedBase padding base)).length + 1))
    (fun entry : UniformShiftConnectedEntry padding base roots predicate =>
      couplingSpinSummedUniformShiftCylinderSourcePairWeight
        coupling cutoff entry.val)
    (uniformShiftShiftedRootCarrierTargetWeight
      coupling cutoff padding base (distance + 2))
    (uniformShiftConnectedCarrierShiftEncode (distance + 2))
    (attach_nodup_of_nodup _
      (List.filter_sublist.nodup
        (uniformShiftCylinderSourcePairList_nodup
          padding base roots predicate)))
    (fun entry _ => by
      have hrootMem := uniformShiftSourceRootAtom_spec entry |>.2
      have hfloor :=
        uniformShiftConnectedCarrierSupport_shifted_boundary_floor
          hrootsInside entry
          (hstartMem _ hrootMem)
          (hrootCore _ hrootMem) houterExit
      have hmax := uniformShiftConnectedCarrierSupport_length_le_ambient entry
      let offset := (uniformShiftConnectedCarrierSupport entry).length -
        (distance + 2)
      have hoffset : offset <
          (physicalFaceEdges (uniformPaddedBase padding base)).length + 1 := by
        unfold offset
        omega
      have hsize : (uniformShiftConnectedCarrierSupport entry).length =
          distance + 2 + offset := by
        unfold offset
        omega
      apply mem_uniformShiftShiftedRootCarrierTargetList_of_lt
        padding base rootStart roots (distance + 2) hoffset
      exact uniformShiftConnectedRootCarrierEncode_mem
        hrootsInside rootStart hstartMem entry hsize)
    (fun first _ second _ heq => by
      apply uniformShiftConnectedRootCarrierEncode_injective first second
      exact congrArg Prod.snd heq)
    (fun entry _ => by
      have hrootMem := uniformShiftSourceRootAtom_spec entry |>.2
      have hfloor :=
        uniformShiftConnectedCarrierSupport_shifted_boundary_floor
          hrootsInside entry
          (hstartMem _ hrootMem)
          (hrootCore _ hrootMem) houterExit
      have hsize : distance + 2 +
            ((uniformShiftConnectedCarrierSupport entry).length -
              (distance + 2)) =
          (uniformShiftConnectedCarrierSupport entry).length := by
        omega
      have hbound :=
        couplingSpinSummedUniformShiftConnectedSourceWeight_le_carrier
          hcoupling hle cutoff entry
      unfold uniformShiftConnectedCarrierShiftEncode
        uniformShiftShiftedRootCarrierTargetWeight
        uniformShiftRootCarrierTargetWeight
        uniformShiftConnectedCarrierTargetWeight
        uniformShiftConnectedRootCarrierEncode
        uniformShiftConnectedCarrier
      rw [hsize]
      simpa [couplingSpinSummedUniformShiftConnectedBackgroundPairWeight]
        using hbound)
    (fun tagged _ => by
      unfold uniformShiftShiftedRootCarrierTargetWeight
        uniformShiftRootCarrierTargetWeight
        uniformShiftConnectedCarrierTargetWeight
      exact Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedFaceEnvelope
          anchorDecoratedFaceEnvelope_nonnegative _)
        (Q'.mul_nonneg _ _
          (couplingParametricKSupportFamilyActivity_nonnegative
            hcoupling cutoff (uniformPaddedBase padding base) tagged.2.2.2.1)
          (couplingParametricKSupportFamilyActivity_nonnegative
            hcoupling cutoff (uniformPaddedBase padding base) tagged.2.2.2.2)))
  rw [listQSum_attach] at hinjection
  exact Q'.le_trans' _ _ _ hinjection
    (uniformShiftShiftedRootCarrierTargetSum_le_tail
      hcoupling cutoff padding base (distance + 2) rootStart roots
      ((physicalFaceEdges (uniformPaddedBase padding base)).length + 1))

#print axioms uniformShiftShiftedRootCarrierTargetSum_le_tail
#print axioms uniformShiftConnectedCarrierSupport_length_le_ambient
#print axioms couplingSpinSummedConnectedUniformShiftCylinderPairSum_le_tail

end YMGap.Continuum.Z4UniformShiftConnectedCarrierBoundaryTail
