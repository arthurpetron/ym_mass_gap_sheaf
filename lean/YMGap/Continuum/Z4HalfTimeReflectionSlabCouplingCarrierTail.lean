/-
# Uniform finite-cutoff tail for the corrected-slab connected residue

The arbitrary-cutoff fixed-size carrier shells are summed from any geometric
support floor.  Their exact background factor remains the full compatible
spin-summed partition times the corrected-slab support numerator.  For the
two central reflected cube roots, the already proved time geometry supplies
the floor `half + 1`.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierFixedSize
import YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierTail

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierTail

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierFixedSize
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierTail
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
open YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierFixedSize
open YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierWeight
open YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingSwitchSummation
open YMGap.Continuum.Z4SpinSummedFaceActivityBound

local infix:50 " ≈ " => Q'.eqv

private instance canonicalAtomDecidableEqLocal {n : Nat} :
    DecidableEq (CanonicalAtom n) := fun first second =>
  if h : first.val = second.val then
    isTrue (Subtype.ext h)
  else
    isFalse (fun heq => h (congrArg Subtype.val heq))

private def couplingSlabShiftedCarrierKey {extent : Nat}
    (tagged : Nat × SlabRootedConnectedCarrier extent) :
    Nat × (List Nat × SlabConnectedCarrier) :=
  (tagged.1, (tagged.2.1.val, tagged.2.2))

private theorem couplingSlabShiftedCarrierKey_injective
    {extent : Nat}
    (first second : Nat × SlabRootedConnectedCarrier extent)
    (heq : couplingSlabShiftedCarrierKey first =
      couplingSlabShiftedCarrierKey second) :
    first = second := by
  apply Prod.ext
  · exact congrArg (fun key => key.1) heq
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun key => key.2.1) heq
    · exact congrArg (fun key => key.2.2) heq

private instance couplingSlabShiftedCarrierDecidableEqLocal {extent : Nat} :
    DecidableEq (Nat × SlabRootedConnectedCarrier extent) :=
  fun first second =>
    if h : couplingSlabShiftedCarrierKey first =
        couplingSlabShiftedCarrierKey second then
      isTrue (couplingSlabShiftedCarrierKey_injective first second h)
    else
      isFalse (fun heq => h (congrArg couplingSlabShiftedCarrierKey heq))

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

def couplingSpinSummedSlabShiftedCarrierTargetWeight
    (coupling : Q') (cutoff extent floor : Nat)
    (tagged : Nat × SlabRootedConnectedCarrier extent) : Q' :=
  couplingSpinSummedSlabRootedConnectedCarrierTargetWeight
    coupling cutoff extent (floor + tagged.1) tagged.2

theorem couplingSpinSummedSlabShiftedCarrierTargetSum_eqv_finSum
    (coupling : Q') (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (floor : Nat) : ∀ depth : Nat,
    listQSum
        (couplingSpinSummedSlabShiftedCarrierTargetWeight
          coupling cutoff extent floor)
        (slabShiftedCarrierTargetList extent roots floor depth) ≈
      finSum (fun offset =>
        listQSum
          (couplingSpinSummedSlabRootedConnectedCarrierTargetWeight
            coupling cutoff extent (floor + offset))
          (slabConnectedCarrierTargetList extent roots
            (floor + offset))) depth
  | 0 => Q'.eqv_refl 0
  | depth + 1 => by
      rw [finSum_succ]
      unfold slabShiftedCarrierTargetList
      refine Q'.eqv_trans _ _ _
        (listQSum_append
          (couplingSpinSummedSlabShiftedCarrierTargetWeight
            coupling cutoff extent floor)
          (slabShiftedCarrierTargetList extent roots floor depth)
          ((slabConnectedCarrierTargetList extent roots
              (floor + depth)).map (fun carrier => (depth, carrier)))) ?_
      refine Q'.add_eqv_congr'
        (couplingSpinSummedSlabShiftedCarrierTargetSum_eqv_finSum
          coupling cutoff extent roots floor depth) ?_
      rw [listQSum_map]
      exact Q'.eqv_refl _

theorem couplingSpinSummedSlabConnectedSourcePairSum_le_shiftedTarget
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
    (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (floor : Nat)
    (hfloor : ∀ entry : SlabConnectedSourceEntry extent roots predicate,
      floor ≤ (slabConnectedCarrierSupport defaultRoot entry).length) :
    listQSum
        (couplingSpinSummedSlabCylinderSourcePairWeight coupling cutoff)
        (connectedSlabCylinderSourcePairs
          (extent := extent) (roots := roots)
          (predicate := predicate)) ≤
      listQSum
        (couplingSpinSummedSlabShiftedCarrierTargetWeight
          coupling cutoff extent floor)
        (slabShiftedCarrierTargetList extent roots floor
          ((physicalFaceEdges (extent + 1)).length + 1)) := by
  have hinjection := listQSum_le_of_injective
    (connectedSlabCylinderSourcePairs
      (extent := extent) (roots := roots)
      (predicate := predicate)).attach
    (slabShiftedCarrierTargetList extent roots floor
      ((physicalFaceEdges (extent + 1)).length + 1))
    (fun entry : SlabConnectedSourceEntry extent roots predicate =>
      couplingSpinSummedSlabCylinderSourcePairWeight
        coupling cutoff entry.val)
    (couplingSpinSummedSlabShiftedCarrierTargetWeight
      coupling cutoff extent floor)
    (slabConnectedCarrierShiftEncode defaultRoot floor)
    (attach_nodup_of_nodup _
      (connectedSlabCylinderSourcePairs_nodup extent roots predicate))
    (fun entry _ => by
      have hmin := hfloor entry
      have hmax := slabConnectedCarrierSupport_length_le_ambient
        defaultRoot entry
      let offset :=
        (slabConnectedCarrierSupport defaultRoot entry).length - floor
      have hoffset : offset <
          (physicalFaceEdges (extent + 1)).length + 1 := by
        unfold offset
        omega
      have hsize :
          (slabConnectedCarrierSupport defaultRoot entry).length =
            floor + offset := by
        unfold offset
        omega
      apply mem_slabShiftedCarrierTargetList_of_lt
        extent roots floor
        ((physicalFaceEdges (extent + 1)).length + 1) hoffset
      exact slabRootedConnectedCarrier_mem_target
        defaultRoot hrootsSupported entry hsize)
    (fun first _ second _ heq => by
      apply slabConnectedCarrier_injective defaultRoot first second
      exact congrArg (fun encoded => encoded.2.2) heq)
    (fun entry _ => by
      have hmin := hfloor entry
      have hsize : floor +
          ((slabConnectedCarrierSupport defaultRoot entry).length - floor) =
          (slabConnectedCarrierSupport defaultRoot entry).length := by
        omega
      have hbound :=
        couplingSpinSummedSlabConnectedSourcePairWeight_le_support_background
          hcoupling hle cutoff defaultRoot entry
      unfold slabConnectedCarrierShiftEncode
        couplingSpinSummedSlabShiftedCarrierTargetWeight
        couplingSpinSummedSlabRootedConnectedCarrierTargetWeight
        couplingSpinSummedSlabConnectedCarrierTargetWeight
        slabRootedConnectedCarrier slabConnectedCarrier
      rw [hsize]
      simpa [couplingSpinSummedSlabConnectedBackgroundPairWeight]
        using hbound)
    (fun tagged _ => by
      unfold couplingSpinSummedSlabShiftedCarrierTargetWeight
        couplingSpinSummedSlabRootedConnectedCarrierTargetWeight
        couplingSpinSummedSlabConnectedCarrierTargetWeight
      exact Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedFaceEnvelope
          anchorDecoratedFaceEnvelope_nonnegative _)
        (Q'.mul_nonneg _ _
          (couplingParametricKSupportFamilyActivity_nonnegative
            hcoupling cutoff (extent + 1) tagged.2.2.2.1)
          (couplingParametricKSupportFamilyActivity_nonnegative
            hcoupling cutoff (extent + 1) tagged.2.2.2.2)))
  rw [listQSum_attach] at hinjection
  exact hinjection

theorem couplingSpinSummedSlabShiftedCarrierTargetSum_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff extent : Nat)
    (roots : List (CanonicalAtom (extent + 1)))
    (floor depth : Nat) :
    listQSum
        (couplingSpinSummedSlabShiftedCarrierTargetWeight
          coupling cutoff extent floor)
        (slabShiftedCarrierTargetList extent roots floor depth) ≤
      (Q'.ofNat roots.length *
          (couplingParametricKCompatibleSupportGasPartition
              coupling cutoff (extent + 1) *
            couplingParametricKCompatibleSupportEventNumerator
              coupling cutoff (extent + 1)
                (canonicalFamilySlabSupportedB extent))) *
        (anchorDecoratedEffectiveRatio ^ floor * Q'.ofNat 2) := by
  let partitionProduct :=
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff (extent + 1) *
      couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff (extent + 1)
          (canonicalFamilySlabSupportedB extent)
  let scale := Q'.ofNat roots.length * partitionProduct
  have htargets :=
    couplingSpinSummedSlabShiftedCarrierTargetSum_eqv_finSum
      coupling cutoff extent roots floor depth
  have hterms :
      finSum (fun offset =>
          listQSum
            (couplingSpinSummedSlabRootedConnectedCarrierTargetWeight
              coupling cutoff extent (floor + offset))
            (slabConnectedCarrierTargetList extent roots
              (floor + offset))) depth ≤
        finSum (fun offset =>
          Q'.ofNat roots.length *
            (anchorDecoratedEffectiveRatio ^ (floor + offset) *
              partitionProduct)) depth :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (fun offset =>
        couplingSpinSummedSlabConnectedCarrierTargetSum_le_geom_partition
          hcoupling cutoff extent roots (floor + offset)) depth
  have hreorder :
      finSum (fun offset =>
          Q'.ofNat roots.length *
            (anchorDecoratedEffectiveRatio ^ (floor + offset) *
              partitionProduct)) depth ≈
        finSum (fun offset =>
          (scale * anchorDecoratedEffectiveRatio ^ floor) *
            anchorDecoratedEffectiveRatio ^ offset) depth := by
    apply RationalTail.finSum_eqv_congr
    intro offset
    have hpow := Q'.pow_add_eqv
      anchorDecoratedEffectiveRatio floor offset
    refine Q'.eqv_trans _
      (Q'.ofNat roots.length *
        ((anchorDecoratedEffectiveRatio ^ floor *
          anchorDecoratedEffectiveRatio ^ offset) * partitionProduct)) _
      (Q'.mul_eqv_congr_left _ _ _
        (mul_eqv_both hpow (Q'.eqv_refl partitionProduct))) ?_
    unfold scale
    ring_qeqv
  have hpull :
      finSum (fun offset =>
          (scale * anchorDecoratedEffectiveRatio ^ floor) *
            anchorDecoratedEffectiveRatio ^ offset) depth ≈
        (scale * anchorDecoratedEffectiveRatio ^ floor) *
          finSum (fun offset =>
            anchorDecoratedEffectiveRatio ^ offset) depth :=
    Q'.eqv_symm (RationalTail.const_mul_finSum
      (fun offset => anchorDecoratedEffectiveRatio ^ offset)
      (scale * anchorDecoratedEffectiveRatio ^ floor) depth)
  have hgeo :
      finSum (fun offset =>
          anchorDecoratedEffectiveRatio ^ offset) depth ≤ Q'.ofNat 2 :=
    geom_partial_le_two anchorDecoratedEffectiveRatio_nonnegative
      anchorDecoratedEffectiveRatio_le_half depth
  have hpartition0 : (0 : Q') ≤ partitionProduct :=
    Q'.mul_nonneg _ _
      (couplingParametricKCompatibleSupportGasPartition_nonnegative
        hcoupling cutoff (extent + 1))
      (couplingParametricKCompatibleSupportEventNumerator_nonnegative
        hcoupling cutoff (extent + 1)
          (canonicalFamilySlabSupportedB extent))
  have hrootCount0 : (0 : Q') ≤ Q'.ofNat roots.length := by
    rw [Q'.zero_le_iff_num_nonneg]
    exact Int.natCast_nonneg roots.length
  have hscale0 : (0 : Q') ≤
      scale * anchorDecoratedEffectiveRatio ^ floor :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ hrootCount0 hpartition0)
      (Q'.pow_nonneg anchorDecoratedEffectiveRatio
        anchorDecoratedEffectiveRatio_nonnegative floor)
  have hscaled :
      (scale * anchorDecoratedEffectiveRatio ^ floor) *
          finSum (fun offset =>
            anchorDecoratedEffectiveRatio ^ offset) depth ≤
        (scale * anchorDecoratedEffectiveRatio ^ floor) * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgeo hscale0
  have hfinal :
      (scale * anchorDecoratedEffectiveRatio ^ floor) * Q'.ofNat 2 ≈
        scale * (anchorDecoratedEffectiveRatio ^ floor * Q'.ofNat 2) :=
    Q'.mul_assoc_eqv scale
      (anchorDecoratedEffectiveRatio ^ floor) (Q'.ofNat 2)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htargets)
    (Q'.le_trans' _ _ _ hterms
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpull)
          (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hfinal)))))

theorem couplingSpinSummedSlabConnectedCylinderResidue_le_tail_of_floor
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
    (cutoff : Nat)
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (floor : Nat)
    (hfloor : ∀ entry : SlabConnectedSourceEntry extent roots predicate,
      floor ≤ (slabConnectedCarrierSupport defaultRoot entry).length) :
    couplingSpinSummedSlabConnectedCylinderResidue
        coupling cutoff extent roots predicate ≤
      (Q'.ofNat roots.length *
          (anchorDecoratedEffectiveRatio ^ floor * Q'.ofNat 2)) *
        (couplingParametricKCompatibleSupportEventNumerator
            coupling cutoff (extent + 1)
              (canonicalFamilySlabSupportedB extent) *
          couplingParametricKCompatibleSupportGasPartition
            coupling cutoff (extent + 1)) := by
  have hinject :=
    couplingSpinSummedSlabConnectedSourcePairSum_le_shiftedTarget
      hcoupling hle cutoff defaultRoot hrootsSupported floor hfloor
  have htail := couplingSpinSummedSlabShiftedCarrierTargetSum_le_tail
    hcoupling cutoff extent roots floor
      ((physicalFaceEdges (extent + 1)).length + 1)
  have hbound := Q'.le_trans' _ _ _ hinject htail
  unfold couplingSpinSummedSlabConnectedCylinderResidue
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv (by ring_qeqv))

theorem centralCouplingSpinSummedSlabConnectedCylinderResidue_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling)
    (cutoff : Nat) {half : Nat} (hhalf : 1 ≤ half)
    (predicate : List Bool → Bool) :
    couplingSpinSummedSlabConnectedCylinderResidue coupling cutoff
        (centralExtent half) (centralSlabCanonicalRoots half hhalf)
        predicate ≤
      (Q'.ofNat 2 *
          (anchorDecoratedEffectiveRatio ^ (half + 1) * Q'.ofNat 2)) *
        (couplingParametricKCompatibleSupportEventNumerator coupling cutoff
            (centralAmbient half)
              (canonicalFamilySlabSupportedB (centralExtent half)) *
          couplingParametricKCompatibleSupportGasPartition coupling cutoff
            (centralAmbient half)) := by
  have htail :=
    couplingSpinSummedSlabConnectedCylinderResidue_le_tail_of_floor
      hcoupling hle cutoff (predicate := predicate)
      (centralLowerCanonicalAtom half hhalf)
      (centralSlabCanonicalRoots_supported half hhalf)
      (half + 1)
      (fun entry => centralSlabConnectedCarrierSupport_floor hhalf entry)
  simpa [centralSlabCanonicalRoots, centralAmbient] using htail

#print axioms couplingSpinSummedSlabShiftedCarrierTargetSum_eqv_finSum
#print axioms couplingSpinSummedSlabConnectedSourcePairSum_le_shiftedTarget
#print axioms couplingSpinSummedSlabShiftedCarrierTargetSum_le_tail
#print axioms couplingSpinSummedSlabConnectedCylinderResidue_le_tail_of_floor
#print axioms centralCouplingSpinSummedSlabConnectedCylinderResidue_le_tail

end YMGap.Continuum.Z4HalfTimeReflectionSlabCouplingCarrierTail
