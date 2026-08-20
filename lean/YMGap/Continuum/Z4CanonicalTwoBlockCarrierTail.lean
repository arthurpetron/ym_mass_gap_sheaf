/-
# Uniform temporal tail for the two-block connected residue

The strict doubled-time carrier starts at size `2 * shift + 6`.  Encode every
connected source pair into its size offset, selected lower root, colored
carrier, and two backgrounds.  Summing the fixed-size bounds gives a finite
geometric tail uniform in the ambient box.  The prefactor retains the finite
number of lower observable roots and two canonical partition functions.
-/

import YMGap.Continuum.Z4CanonicalTwoBlockCarrierFixedSize
import YMGap.Continuum.Z4CanonicalConnectedCarrierTail

namespace YMGap.Continuum.Z4CanonicalTwoBlockCarrierTail

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
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalTwoBlockCarrierFixedSize
open YMGap.Continuum.Z4CanonicalTwoBlockColoredCarrierGeometry
open YMGap.Continuum.Z4CanonicalTwoBlockColoredPathCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4CanonicalTwoBlockSwitchSummation
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

private def twoBlockShiftedCarrierKey {n : Nat}
    (tagged : Nat × TwoBlockRootedCarrier n) :
    Nat × (List Nat ×
      YMGap.Continuum.Z4CanonicalConnectedPathCarrier.ConnectedCarrier) :=
  (tagged.1, (tagged.2.1.val, tagged.2.2))

private theorem twoBlockShiftedCarrierKey_injective
    {n : Nat} (first second : Nat × TwoBlockRootedCarrier n)
    (heq : twoBlockShiftedCarrierKey first =
      twoBlockShiftedCarrierKey second) : first = second := by
  apply Prod.ext
  · exact congrArg (fun key => key.1) heq
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun key => key.2.1) heq
    · exact congrArg (fun key => key.2.2) heq

private instance twoBlockShiftedCarrierDecidableEqLocal {n : Nat} :
    DecidableEq (Nat × TwoBlockRootedCarrier n) :=
  fun first second =>
    if h : twoBlockShiftedCarrierKey first =
        twoBlockShiftedCarrierKey second then
      isTrue (twoBlockShiftedCarrierKey_injective first second h)
    else
      isFalse (fun heq => h (congrArg twoBlockShiftedCarrierKey heq))

def canonicalAtomFirstFace {n : Nat} (root : CanonicalAtom n) : Nat :=
  (canonicalSurfacePolymers_allNonempty n root.val root.property).1

theorem canonicalAtomFirstFace_mem {n : Nat} (root : CanonicalAtom n) :
    canonicalAtomFirstFace root ∈ root.val :=
  (canonicalSurfacePolymers_allNonempty n root.val root.property).2

theorem twoBlockConnectedColoredSupport_length_le_ambient
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    (twoBlockConnectedColoredSupport entry).length ≤
      (physicalFaceEdges n).length := by
  have hsupport : twoBlockConnectedColoredSupport entry ∈
      cutoffOneFaceSupports n := by
    unfold twoBlockConnectedColoredSupport
    exact familyUnionSupport_mem_cutoffOneFaceSupports n _
  have hnodup := nodup_of_mem_sublists
    (physicalFaceEdges n) (twoBlockConnectedColoredSupport entry)
    (physicalFaceEdges_nodup n) hsupport
  exact length_le_of_unique_representation
    (fun source target : Nat => source = target)
    (twoBlockConnectedColoredSupport entry) (physicalFaceEdges n)
    hnodup
    (fun face hface =>
      ⟨face, mem_of_mem_sublists (physicalFaceEdges n)
        (twoBlockConnectedColoredSupport entry) hsupport face hface, rfl⟩)
    (fun left _ right _ target hleft hright => hleft.trans hright.symm)

def twoBlockShiftedCarrierTargetList
    (n : Nat) (rootStart : CanonicalAtom n → Nat)
    (roots : List (CanonicalAtom n)) (floor : Nat) :
    Nat → List (Nat × TwoBlockRootedCarrier n)
  | 0 => []
  | depth + 1 =>
      twoBlockShiftedCarrierTargetList n rootStart roots floor depth ++
        (twoBlockRootCarrierTargetList n rootStart roots
          (floor + depth)).map (fun carrier => (depth, carrier))

def twoBlockShiftedCarrierTargetWeight
    (n floor : Nat) (tagged : Nat × TwoBlockRootedCarrier n) : Q' :=
  twoBlockRootCarrierTargetWeight n (floor + tagged.1) tagged.2

theorem mem_twoBlockShiftedCarrierTargetList_of_lt
    (n : Nat) (rootStart : CanonicalAtom n → Nat)
    (roots : List (CanonicalAtom n)) (floor depth : Nat)
    {offset : Nat} {carrier : TwoBlockRootedCarrier n}
    (hoffset : offset < depth)
    (hcarrier : carrier ∈ twoBlockRootCarrierTargetList
      n rootStart roots (floor + offset)) :
    (offset, carrier) ∈ twoBlockShiftedCarrierTargetList
      n rootStart roots floor depth := by
  induction depth generalizing offset carrier with
  | zero => omega
  | succ previous ih =>
      unfold twoBlockShiftedCarrierTargetList
      apply List.mem_append.mpr
      by_cases hlast : offset = previous
      · subst offset
        exact Or.inr (List.mem_map.mpr ⟨carrier, hcarrier, rfl⟩)
      · exact Or.inl (ih (by omega) hcarrier)

theorem twoBlockShiftedCarrierTargetSum_eqv_finSum
    (n : Nat) (rootStart : CanonicalAtom n → Nat)
    (roots : List (CanonicalAtom n)) (floor : Nat) : ∀ depth : Nat,
    listQSum (twoBlockShiftedCarrierTargetWeight n floor)
        (twoBlockShiftedCarrierTargetList
          n rootStart roots floor depth) ≈
      finSum (fun offset =>
        listQSum (twoBlockRootCarrierTargetWeight n (floor + offset))
          (twoBlockRootCarrierTargetList
            n rootStart roots (floor + offset))) depth
  | 0 => Q'.eqv_refl 0
  | depth + 1 => by
      rw [finSum_succ]
      unfold twoBlockShiftedCarrierTargetList
      refine Q'.eqv_trans _ _ _
        (listQSum_append (twoBlockShiftedCarrierTargetWeight n floor)
          (twoBlockShiftedCarrierTargetList
            n rootStart roots floor depth)
          ((twoBlockRootCarrierTargetList n rootStart roots
            (floor + depth)).map (fun carrier => (depth, carrier)))) ?_
      refine Q'.add_eqv_congr'
        (twoBlockShiftedCarrierTargetSum_eqv_finSum
          n rootStart roots floor depth) ?_
      rw [listQSum_map]
      exact Q'.eqv_refl _

def twoBlockConnectedCarrierShiftEncode
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (floor : Nat)
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate) :
    Nat × TwoBlockRootedCarrier n :=
  ((twoBlockConnectedColoredSupport entry).length - floor,
    twoBlockConnectedRootCarrierEncode entry)

theorem twoBlockConnectedRootCarrierEncode_mem_target
    {n : Nat} {firstRoots secondRoots : List (CanonicalAtom n)}
    {firstPredicate secondPredicate : List Bool → Bool}
    (rootStart : CanonicalAtom n → Nat)
    (hstartMem : ∀ root, root ∈ firstRoots → rootStart root ∈ root.val)
    (entry : TwoBlockConnectedEntry firstRoots secondRoots
      firstPredicate secondPredicate)
    (hne : twoBlockConnectedFirst entry ≠
      twoBlockConnectedSecond entry)
    {size : Nat}
    (hsize : (twoBlockConnectedColoredSupport entry).length = size) :
    twoBlockConnectedRootCarrierEncode entry ∈
      twoBlockRootCarrierTargetList n rootStart firstRoots size := by
  unfold twoBlockRootCarrierTargetList
    twoBlockConnectedRootCarrierEncode
  apply List.mem_flatMap.mpr
  refine ⟨twoBlockConnectedFirst entry,
    twoBlockConnectedFirst_mem entry, ?_⟩
  apply List.mem_map.mpr
  refine ⟨twoBlockConnectedColoredCarrier entry, ?_, rfl⟩
  exact twoBlockConnectedColoredCarrier_mem_target entry hne
    (hstartMem _ (twoBlockConnectedFirst_mem entry)) hsize

theorem twoBlockConnectedSourcePairSum_le_shiftedTarget
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
    listQSum (twoBlockSourcePairWeight anchorCoupling)
        (connectedTwoBlockSourcePairs
          (firstRoots := firstRoots) (secondRoots := secondRoots)
          (firstPredicate := firstPredicate)
          (secondPredicate := secondPredicate)) ≤
      listQSum (twoBlockShiftedCarrierTargetWeight n floor)
        (twoBlockShiftedCarrierTargetList n rootStart firstRoots floor
          ((physicalFaceEdges n).length + 1)) := by
  have hinjection :
      listQSum
          (fun entry : TwoBlockConnectedEntry firstRoots secondRoots
            firstPredicate secondPredicate =>
            twoBlockSourcePairWeight anchorCoupling entry.val)
          (connectedTwoBlockSourcePairs
            (firstRoots := firstRoots) (secondRoots := secondRoots)
            (firstPredicate := firstPredicate)
            (secondPredicate := secondPredicate)).attach ≤
        listQSum (twoBlockShiftedCarrierTargetWeight n floor)
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
      (fun entry => twoBlockSourcePairWeight anchorCoupling entry.val)
      (twoBlockShiftedCarrierTargetWeight n floor)
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
        twoBlockConnectedSourcePairWeight_le_support_background entry
      unfold twoBlockConnectedBackgroundPairWeight at hbound
      unfold twoBlockConnectedCarrierShiftEncode
        twoBlockShiftedCarrierTargetWeight
        twoBlockRootCarrierTargetWeight
        twoBlockConnectedCarrierTargetWeight
        twoBlockConnectedRootCarrierEncode
        twoBlockConnectedColoredCarrier
      rw [hsize]
      simpa using hbound
    · intro tagged _
      unfold twoBlockShiftedCarrierTargetWeight
        twoBlockRootCarrierTargetWeight
        twoBlockConnectedCarrierTargetWeight
      exact Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorPerFaceEnvelope (by decide) _)
        (Q'.mul_nonneg _ _
          (canonicalSurfaceFamilyActivity_nonnegative n tagged.2.2.2.1)
          (canonicalSurfaceFamilyActivity_nonnegative n tagged.2.2.2.2))
  rw [listQSum_attach] at hinjection
  exact hinjection

theorem twoBlockShiftedCarrierTargetSum_le_tail
    (n : Nat) (rootStart : CanonicalAtom n → Nat)
    (roots : List (CanonicalAtom n)) (floor depth : Nat) :
    listQSum (twoBlockShiftedCarrierTargetWeight n floor)
        (twoBlockShiftedCarrierTargetList
          n rootStart roots floor depth) ≤
      (Q'.ofNat roots.length *
          (anchorCanonicalPartition n * anchorCanonicalPartition n)) *
        (anchorEffectiveRatio ^ floor * Q'.ofNat 2) := by
  let partitionProduct :=
    anchorCanonicalPartition n * anchorCanonicalPartition n
  let scale := Q'.ofNat roots.length * partitionProduct
  have htargets := twoBlockShiftedCarrierTargetSum_eqv_finSum
    n rootStart roots floor depth
  have hterms :
      finSum (fun offset =>
          listQSum
            (twoBlockRootCarrierTargetWeight n (floor + offset))
            (twoBlockRootCarrierTargetList
              n rootStart roots (floor + offset))) depth ≤
        finSum (fun offset =>
          Q'.ofNat roots.length *
            (anchorEffectiveRatio ^ (floor + offset) *
              partitionProduct)) depth :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (fun offset =>
        twoBlockRootCarrierTargetSum_le_geom
          n (floor + offset) rootStart roots) depth
  have hreorder :
      finSum (fun offset =>
          Q'.ofNat roots.length *
            (anchorEffectiveRatio ^ (floor + offset) *
              partitionProduct)) depth ≈
        finSum (fun offset =>
          (scale * anchorEffectiveRatio ^ floor) *
            anchorEffectiveRatio ^ offset) depth := by
    apply RationalTail.finSum_eqv_congr
    intro offset
    have hpow := Q'.pow_add_eqv anchorEffectiveRatio floor offset
    refine Q'.eqv_trans _
      (Q'.ofNat roots.length *
        ((anchorEffectiveRatio ^ floor *
          anchorEffectiveRatio ^ offset) * partitionProduct)) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_right _ _ _ hpow)) ?_
    unfold scale
    ring_qeqv
  have hpull :
      finSum (fun offset =>
          (scale * anchorEffectiveRatio ^ floor) *
            anchorEffectiveRatio ^ offset) depth ≈
        (scale * anchorEffectiveRatio ^ floor) *
          finSum (fun offset => anchorEffectiveRatio ^ offset) depth :=
    Q'.eqv_symm (RationalTail.const_mul_finSum
      (fun offset => anchorEffectiveRatio ^ offset)
      (scale * anchorEffectiveRatio ^ floor) depth)
  have hgeo :
      finSum (fun offset => anchorEffectiveRatio ^ offset) depth ≤
        Q'.ofNat 2 :=
    geom_partial_le_two anchorEffectiveRatio_nonnegative
      anchorEffectiveRatio_le_half depth
  have hrootCount0 : (0 : Q') ≤ Q'.ofNat roots.length := by
    rw [Q'.zero_le_iff_num_nonneg]
    exact Int.natCast_nonneg roots.length
  have hpartition0 : (0 : Q') ≤ partitionProduct :=
    Q'.mul_nonneg _ _
      (anchorCanonicalPartition_nonnegative n)
      (anchorCanonicalPartition_nonnegative n)
  have hscale0 : (0 : Q') ≤
      scale * anchorEffectiveRatio ^ floor :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ hrootCount0 hpartition0)
      (Q'.pow_nonneg anchorEffectiveRatio
        anchorEffectiveRatio_nonnegative floor)
  have hscaled :
      (scale * anchorEffectiveRatio ^ floor) *
          finSum (fun offset => anchorEffectiveRatio ^ offset) depth ≤
        (scale * anchorEffectiveRatio ^ floor) * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgeo hscale0
  have hfinal :
      (scale * anchorEffectiveRatio ^ floor) * Q'.ofNat 2 ≈
        scale * (anchorEffectiveRatio ^ floor * Q'.ofNat 2) :=
    Q'.mul_assoc_eqv scale
      (anchorEffectiveRatio ^ floor) (Q'.ofNat 2)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htargets)
    (Q'.le_trans' _ _ _ hterms
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpull)
          (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hfinal)))))

/-- The connected residue for the strict doubled-time blocks has an explicit
uniform temporal tail.  The finite root-count prefactor is observable data;
the ambient volume occurs only in the two partition functions. -/
theorem strictDoubledTimeConnectedPairSum_le_tail
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :
    listQSum (twoBlockSourcePairWeight anchorCoupling)
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
        (anchorCanonicalPartition (centralAmbient radius) *
          anchorCanonicalPartition (centralAmbient radius))) *
        (anchorEffectiveRatio ^ (shift + shift + 6) * Q'.ofNat 2) := by
  exact Q'.le_trans' _ _ _
    (twoBlockConnectedSourcePairSum_le_shiftedTarget
      canonicalAtomFirstFace
      (fun root _ => canonicalAtomFirstFace_mem root)
      (shift + shift + 6)
      (fun entry =>
        strictDoubledTimeConnectedColoredSupport_size_floor entry)
      (fun entry => strictDoubledTimeConnectedEndpoints_ne entry))
    (twoBlockShiftedCarrierTargetSum_le_tail
      (centralAmbient radius) canonicalAtomFirstFace
      (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
      (shift + shift + 6)
      ((physicalFaceEdges (centralAmbient radius)).length + 1))

/-- Exact four-cell cancellation followed by the uniform temporal carrier
tail.  This is an observable-dependent finite-volume covariance-cell bound,
not yet a reflection-norm-relative operator contraction. -/
theorem strictDoubledTimeFourCellCrossDifference_le_tail
    {radius base shift : Nat}
    (hadmissible : strictQueryBase (base + (shift + shift)) ≤ radius)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (firstPredicate secondPredicate : List Bool → Bool) :
    listQSum (canonicalSurfaceFamilyActivity anchorCoupling
          (centralAmbient radius))
          (twoBlockTTFamilyList
            (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
            (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
            firstPredicate secondPredicate) *
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling
          (centralAmbient radius))
          (twoBlockFFFamilyList
            (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
            (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
            firstPredicate secondPredicate) -
      listQSum (canonicalSurfaceFamilyActivity anchorCoupling
          (centralAmbient radius))
          (twoBlockFTFamilyList
            (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
            (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
            firstPredicate secondPredicate) *
        listQSum (canonicalSurfaceFamilyActivity anchorCoupling
          (centralAmbient radius))
          (twoBlockTFFamilyList
            (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
            (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
            firstPredicate secondPredicate) ≤
      (Q'.ofNat
          (strictJointDoubledTimeLowerRootAtoms
            hadmissible hroots).length *
        (anchorCanonicalPartition (centralAmbient radius) *
          anchorCanonicalPartition (centralAmbient radius))) *
        (anchorEffectiveRatio ^ (shift + shift + 6) * Q'.ofNat 2) := by
  exact Q'.le_trans' _ _ _
    (twoBlockFourCellCrossDifference_le_connected
      (by decide)
      (strictJointDoubledTimeLowerRootAtoms hadmissible hroots)
      (strictJointDoubledTimeUpperRootAtoms hadmissible hroots)
      firstPredicate secondPredicate)
    (strictDoubledTimeConnectedPairSum_le_tail
      hadmissible hroots firstPredicate secondPredicate)

#print axioms twoBlockConnectedSourcePairSum_le_shiftedTarget
#print axioms twoBlockShiftedCarrierTargetSum_le_tail
#print axioms strictDoubledTimeConnectedPairSum_le_tail
#print axioms strictDoubledTimeFourCellCrossDifference_le_tail

end YMGap.Continuum.Z4CanonicalTwoBlockCarrierTail
