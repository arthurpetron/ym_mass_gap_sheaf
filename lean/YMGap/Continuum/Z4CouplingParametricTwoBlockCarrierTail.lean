/-
# Uniform arbitrary-cutoff temporal tail for the two-block residue

The strict doubled-time colored carrier has at least `2 * shift + 6` faces.
Encode each connected pair by its size offset, selected lower root, colored
carrier, and two exact spin-summed backgrounds.  Summing the fixed-size bound
gives a geometric temporal tail with the square of the same physical support
gas partition, uniformly in cutoff and ambient volume.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockCarrierTail
import YMGap.Continuum.Z4CouplingParametricTwoBlockCarrierFixedSize

namespace YMGap.Continuum.Z4CouplingParametricTwoBlockCarrierTail

set_option maxRecDepth 100000
set_option maxHeartbeats 7000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalConnectedCarrierTail
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockCarrierFixedSize
open YMGap.Continuum.Z4CanonicalTwoBlockCarrierTail
open YMGap.Continuum.Z4CanonicalTwoBlockColoredCarrierGeometry
open YMGap.Continuum.Z4CanonicalTwoBlockColoredPathCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CouplingParametricTwoBlockCarrierFixedSize
open YMGap.Continuum.Z4CouplingParametricTwoBlockColoredCarrierWeight
open YMGap.Continuum.Z4CouplingParametricTwoBlockProbabilityCovariance
open YMGap.Continuum.Z4CouplingParametricTwoBlockSwitchSummation
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeCarrierFloor
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedEventRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

private def couplingTwoBlockShiftedCarrierKey {n : Nat}
    (tagged : Nat × TwoBlockRootedCarrier n) :
    Nat × (List Nat ×
      YMGap.Continuum.Z4CanonicalConnectedPathCarrier.ConnectedCarrier) :=
  (tagged.1, (tagged.2.1.val, tagged.2.2))

private theorem couplingTwoBlockShiftedCarrierKey_injective
    {n : Nat} (first second : Nat × TwoBlockRootedCarrier n)
    (heq : couplingTwoBlockShiftedCarrierKey first =
      couplingTwoBlockShiftedCarrierKey second) : first = second := by
  apply Prod.ext
  · exact congrArg (fun key => key.1) heq
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun key => key.2.1) heq
    · exact congrArg (fun key => key.2.2) heq

private instance couplingTwoBlockShiftedCarrierDecidableEqLocal {n : Nat} :
    DecidableEq (Nat × TwoBlockRootedCarrier n) :=
  fun first second =>
    if h : couplingTwoBlockShiftedCarrierKey first =
        couplingTwoBlockShiftedCarrierKey second then
      isTrue (couplingTwoBlockShiftedCarrierKey_injective first second h)
    else
      isFalse (fun heq => h
        (congrArg couplingTwoBlockShiftedCarrierKey heq))

def couplingSpinSummedTwoBlockShiftedCarrierTargetWeight
    (coupling : Q') (cutoff n floor : Nat)
    (tagged : Nat × TwoBlockRootedCarrier n) : Q' :=
  couplingSpinSummedTwoBlockRootCarrierTargetWeight
    coupling cutoff n (floor + tagged.1) tagged.2

theorem couplingSpinSummedTwoBlockShiftedCarrierTargetSum_eqv_finSum
    (coupling : Q') (cutoff n : Nat)
    (rootStart : CanonicalAtom n → Nat)
    (roots : List (CanonicalAtom n)) (floor : Nat) : ∀ depth : Nat,
    listQSum
        (couplingSpinSummedTwoBlockShiftedCarrierTargetWeight
          coupling cutoff n floor)
        (twoBlockShiftedCarrierTargetList
          n rootStart roots floor depth) ≈
      finSum (fun offset =>
        listQSum
          (couplingSpinSummedTwoBlockRootCarrierTargetWeight
            coupling cutoff n (floor + offset))
          (twoBlockRootCarrierTargetList
            n rootStart roots (floor + offset))) depth
  | 0 => Q'.eqv_refl 0
  | depth + 1 => by
      rw [finSum_succ]
      unfold twoBlockShiftedCarrierTargetList
      refine Q'.eqv_trans _ _ _
        (listQSum_append
          (couplingSpinSummedTwoBlockShiftedCarrierTargetWeight
            coupling cutoff n floor)
          (twoBlockShiftedCarrierTargetList
            n rootStart roots floor depth)
          ((twoBlockRootCarrierTargetList n rootStart roots
            (floor + depth)).map (fun carrier => (depth, carrier)))) ?_
      refine Q'.add_eqv_congr'
        (couplingSpinSummedTwoBlockShiftedCarrierTargetSum_eqv_finSum
          coupling cutoff n rootStart roots floor depth) ?_
      rw [listQSum_map]
      exact Q'.eqv_refl _

theorem couplingSpinSummedTwoBlockConnectedSourcePairSum_le_shiftedTarget
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (rootStart : CanonicalAtom n → Nat)
    (hstartMem : ∀ root, root ∈ firstRoots → rootStart root ∈ root.val)
    (floor : Nat)
    (hfloor : ∀ entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate,
      floor ≤ (twoBlockConnectedColoredSupport entry).length)
    (hne : ∀ entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate,
      twoBlockConnectedFirst entry ≠ twoBlockConnectedSecond entry) :
    listQSum
        (couplingSpinSummedTwoBlockSourcePairWeight coupling cutoff)
        (connectedTwoBlockSourcePairs
          (firstRoots := firstRoots) (secondRoots := secondRoots)
          (firstPredicate := firstPredicate)
          (secondPredicate := secondPredicate)) ≤
      listQSum
        (couplingSpinSummedTwoBlockShiftedCarrierTargetWeight
          coupling cutoff n floor)
        (twoBlockShiftedCarrierTargetList n rootStart firstRoots floor
          ((physicalFaceEdges n).length + 1)) := by
  have hinjection :
      listQSum
          (fun entry : TwoBlockConnectedEntry firstRoots secondRoots
            firstPredicate secondPredicate =>
            couplingSpinSummedTwoBlockSourcePairWeight
              coupling cutoff entry.val)
          (connectedTwoBlockSourcePairs
            (firstRoots := firstRoots) (secondRoots := secondRoots)
            (firstPredicate := firstPredicate)
            (secondPredicate := secondPredicate)).attach ≤
        listQSum
          (couplingSpinSummedTwoBlockShiftedCarrierTargetWeight
            coupling cutoff n floor)
          (twoBlockShiftedCarrierTargetList n rootStart firstRoots floor
            ((physicalFaceEdges n).length + 1)) := by
    apply listQSum_le_of_injective
      (A := TwoBlockConnectedEntry firstRoots secondRoots
        firstPredicate secondPredicate)
      (B := Nat × TwoBlockRootedCarrier n)
      (connectedTwoBlockSourcePairs
        (firstRoots := firstRoots) (secondRoots := secondRoots)
        (firstPredicate := firstPredicate)
        (secondPredicate := secondPredicate)).attach
      (twoBlockShiftedCarrierTargetList n rootStart firstRoots floor
        ((physicalFaceEdges n).length + 1))
      (fun entry => couplingSpinSummedTwoBlockSourcePairWeight
        coupling cutoff entry.val)
      (couplingSpinSummedTwoBlockShiftedCarrierTargetWeight
        coupling cutoff n floor)
      (twoBlockConnectedCarrierShiftEncode floor)
      (attach_nodup_of_nodup _
        (connectedTwoBlockSourcePairs_nodup
          firstRoots secondRoots firstPredicate secondPredicate))
    · intro entry _
      have hmin := hfloor entry
      have hmax := twoBlockConnectedColoredSupport_length_le_ambient entry
      let offset := (twoBlockConnectedColoredSupport entry).length - floor
      have hoffset : offset < (physicalFaceEdges n).length + 1 := by
        unfold offset
        omega
      have hsize : (twoBlockConnectedColoredSupport entry).length =
          floor + offset := by
        unfold offset
        omega
      apply mem_twoBlockShiftedCarrierTargetList_of_lt
        n rootStart firstRoots floor
        ((physicalFaceEdges n).length + 1) hoffset
      exact twoBlockConnectedRootCarrierEncode_mem_target
        rootStart hstartMem entry (hne entry) hsize
    · intro first _ second _ heq
      apply twoBlockConnectedRootCarrierEncode_injective first second
      exact congrArg Prod.snd heq
    · intro entry _
      have hmin := hfloor entry
      have hsize : floor +
          ((twoBlockConnectedColoredSupport entry).length - floor) =
        (twoBlockConnectedColoredSupport entry).length := by
        omega
      have hbound :=
        couplingSpinSummedTwoBlockConnectedSourcePairWeight_le_support_background
          hcoupling hle cutoff entry
      unfold couplingSpinSummedTwoBlockConnectedBackgroundPairWeight at hbound
      unfold twoBlockConnectedCarrierShiftEncode
        couplingSpinSummedTwoBlockShiftedCarrierTargetWeight
        couplingSpinSummedTwoBlockRootCarrierTargetWeight
        couplingSpinSummedTwoBlockConnectedCarrierTargetWeight
        twoBlockConnectedRootCarrierEncode
        twoBlockConnectedColoredCarrier
      rw [hsize]
      simpa using hbound
    · intro tagged _
      unfold couplingSpinSummedTwoBlockShiftedCarrierTargetWeight
        couplingSpinSummedTwoBlockRootCarrierTargetWeight
        couplingSpinSummedTwoBlockConnectedCarrierTargetWeight
      exact Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedFaceEnvelope
          anchorDecoratedFaceEnvelope_nonnegative _)
        (Q'.mul_nonneg _ _
          (couplingParametricKSupportFamilyActivity_nonnegative
            hcoupling cutoff n tagged.2.2.2.1)
          (couplingParametricKSupportFamilyActivity_nonnegative
            hcoupling cutoff n tagged.2.2.2.2))
  rw [listQSum_attach] at hinjection
  exact hinjection

theorem couplingSpinSummedTwoBlockShiftedCarrierTargetSum_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff n : Nat) (rootStart : CanonicalAtom n → Nat)
    (roots : List (CanonicalAtom n)) (floor depth : Nat) :
    listQSum
        (couplingSpinSummedTwoBlockShiftedCarrierTargetWeight
          coupling cutoff n floor)
        (twoBlockShiftedCarrierTargetList
          n rootStart roots floor depth) ≤
      (Q'.ofNat roots.length *
          (couplingParametricKCompatibleSupportGasPartition
              coupling cutoff n *
            couplingParametricKCompatibleSupportGasPartition
              coupling cutoff n)) *
        (anchorDecoratedEffectiveRatio ^ floor * Q'.ofNat 2) := by
  let partitionProduct :=
    couplingParametricKCompatibleSupportGasPartition coupling cutoff n *
      couplingParametricKCompatibleSupportGasPartition coupling cutoff n
  let scale := Q'.ofNat roots.length * partitionProduct
  have htargets :=
    couplingSpinSummedTwoBlockShiftedCarrierTargetSum_eqv_finSum
      coupling cutoff n rootStart roots floor depth
  have hterms :
      finSum (fun offset =>
          listQSum
            (couplingSpinSummedTwoBlockRootCarrierTargetWeight
              coupling cutoff n (floor + offset))
            (twoBlockRootCarrierTargetList
              n rootStart roots (floor + offset))) depth ≤
        finSum (fun offset =>
          Q'.ofNat roots.length *
            (anchorDecoratedEffectiveRatio ^ (floor + offset) *
              partitionProduct)) depth :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (fun offset =>
        couplingSpinSummedTwoBlockRootCarrierTargetSum_le_geom
          hcoupling cutoff n (floor + offset) rootStart roots) depth
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
        (Q'.mul_eqv_congr_right _ _ _ hpow)) ?_
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
  have hrootCount0 : (0 : Q') ≤ Q'.ofNat roots.length := by
    rw [Q'.zero_le_iff_num_nonneg]
    exact Int.natCast_nonneg roots.length
  have hpartition0 : (0 : Q') ≤ partitionProduct :=
    Q'.mul_nonneg _ _
      (couplingParametricKCompatibleSupportGasPartition_nonnegative
        hcoupling cutoff n)
      (couplingParametricKCompatibleSupportGasPartition_nonnegative
        hcoupling cutoff n)
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

theorem couplingSpinSummedStrictDoubledTimeConnectedPairSum_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :
    listQSum
        (couplingSpinSummedTwoBlockSourcePairWeight coupling cutoff)
        (connectedTwoBlockSourcePairs
          (firstRoots := strictJointDoubledTimeLowerRootAtoms
            hadmissible hroots)
          (secondRoots := strictJointDoubledTimeUpperRootAtoms
            hadmissible hroots)
          (firstPredicate := firstPredicate)
          (secondPredicate := secondPredicate)) ≤
      (Q'.ofNat
          (strictJointDoubledTimeLowerRootAtoms
            hadmissible hroots).length *
        (couplingParametricKCompatibleSupportGasPartition coupling cutoff
            (centralAmbient radius) *
          couplingParametricKCompatibleSupportGasPartition coupling cutoff
            (centralAmbient radius))) *
        (anchorDecoratedEffectiveRatio ^ (shift + shift + 6) *
          Q'.ofNat 2) := by
  exact Q'.le_trans' _ _ _
    (couplingSpinSummedTwoBlockConnectedSourcePairSum_le_shiftedTarget
      hcoupling hle cutoff canonicalAtomFirstFace
      (fun root _ => canonicalAtomFirstFace_mem root)
      (shift + shift + 6)
      (fun entry =>
        strictDoubledTimeConnectedColoredSupport_size_floor entry)
      (fun entry => strictDoubledTimeConnectedEndpoints_ne entry))
    (couplingSpinSummedTwoBlockShiftedCarrierTargetSum_le_tail
      hcoupling cutoff (centralAmbient radius) canonicalAtomFirstFace
      (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
      (shift + shift + 6)
      ((physicalFaceEdges (centralAmbient radius)).length + 1))

theorem couplingSpinSummedStrictDoubledTimeFourCellCrossDifference_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :
    couplingParametricKTwoBlockFourCellCrossNumerator coupling cutoff
        (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
        (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
        firstPredicate secondPredicate ≤
      (Q'.ofNat
          (strictJointDoubledTimeLowerRootAtoms
            hadmissible hroots).length *
        (couplingParametricKCompatibleSupportGasPartition coupling cutoff
            (centralAmbient radius) *
          couplingParametricKCompatibleSupportGasPartition coupling cutoff
            (centralAmbient radius))) *
        (anchorDecoratedEffectiveRatio ^ (shift + shift + 6) *
          Q'.ofNat 2) := by
  exact Q'.le_trans' _ _ _
    (couplingSpinSummedTwoBlockFourCellCrossDifference_le_connected
      hcoupling cutoff
      (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
      (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
      firstPredicate secondPredicate)
    (couplingSpinSummedStrictDoubledTimeConnectedPairSum_le_tail
      hcoupling hle cutoff hadmissible hroots
      firstPredicate secondPredicate)

#print axioms couplingSpinSummedTwoBlockConnectedSourcePairSum_le_shiftedTarget
#print axioms couplingSpinSummedTwoBlockShiftedCarrierTargetSum_le_tail
#print axioms couplingSpinSummedStrictDoubledTimeConnectedPairSum_le_tail
#print axioms couplingSpinSummedStrictDoubledTimeFourCellCrossDifference_le_tail

end YMGap.Continuum.Z4CouplingParametricTwoBlockCarrierTail
