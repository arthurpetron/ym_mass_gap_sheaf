/-
# Geometric tail for the slab connected residue

The fixed-size rooted carrier shells are summed from any proved support-size
floor.  Their background factor remains the literal full-partition times
slab-support product throughout.  A final specialization to the two central
reflected cube roots obtains the time-directed floor `half + 1`.
-/

import YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierFixedSize
import YMGap.Continuum.Z4HalfTimeReflectionSlabConditionalStabilityAlgebra

namespace YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierTail

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitch
open YMGap.Continuum.Z4HalfTimeReflectionSlabBoundarySwitchSummation
open YMGap.Continuum.Z4HalfTimeReflectionSlabCanonicalEvent
open YMGap.Continuum.Z4HalfTimeReflectionSlabConditionalStabilityAlgebra
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierAnimal
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierFixedSize
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierWeight
open YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedPathCarrier
open YMGap.Continuum.Z4HalfTimeReflectionTopBoundaryTail
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition

local infix:50 " ≈ " => Q'.eqv

private instance canonicalAtomDecidableEqLocal {n : Nat} :
    DecidableEq (CanonicalAtom n) := fun first second =>
  if h : first.val = second.val then
    isTrue (Subtype.ext h)
  else
    isFalse (fun heq => h (congrArg Subtype.val heq))

private def slabShiftedCarrierKey {extent : Nat}
    (tagged : Nat × SlabRootedConnectedCarrier extent) :
    Nat × (List Nat × SlabConnectedCarrier) :=
  (tagged.1, (tagged.2.1.val, tagged.2.2))

private theorem slabShiftedCarrierKey_injective
    {extent : Nat}
    (first second : Nat × SlabRootedConnectedCarrier extent)
    (heq : slabShiftedCarrierKey first = slabShiftedCarrierKey second) :
    first = second := by
  apply Prod.ext
  · exact congrArg (fun key => key.1) heq
  · apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun key => key.2.1) heq
    · exact congrArg (fun key => key.2.2) heq

private instance slabShiftedCarrierDecidableEqLocal {extent : Nat} :
    DecidableEq (Nat × SlabRootedConnectedCarrier extent) :=
  fun first second =>
    if h : slabShiftedCarrierKey first = slabShiftedCarrierKey second then
      isTrue (slabShiftedCarrierKey_injective first second h)
    else
      isFalse (fun heq => h (congrArg slabShiftedCarrierKey heq))

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## 1. Uniform finite upper cutoff -/

theorem slabConnectedCarrierSupport_length_le_ambient
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    (slabConnectedCarrierSupport defaultRoot entry).length ≤
      (physicalFaceEdges (extent + 1)).length := by
  have hsupport :=
    slabConnectedCarrierSupport_mem_faceSupports defaultRoot entry
  have hnodup := nodup_of_mem_sublists
    (physicalFaceEdges (extent + 1))
    (slabConnectedCarrierSupport defaultRoot entry)
    (physicalFaceEdges_nodup (extent + 1)) hsupport
  exact length_le_of_unique_representation
    (fun source target : Nat => source = target)
    (slabConnectedCarrierSupport defaultRoot entry)
    (physicalFaceEdges (extent + 1)) hnodup
    (fun face hface =>
      ⟨face, mem_of_mem_sublists (physicalFaceEdges (extent + 1))
        (slabConnectedCarrierSupport defaultRoot entry)
        hsupport face hface, rfl⟩)
    (fun left _ right _ target hleft hright =>
      hleft.trans hright.symm)

/-! ## 2. Shifted rooted carrier shells -/

def slabShiftedCarrierTargetList
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (floor : Nat) : Nat →
      List (Nat × SlabRootedConnectedCarrier extent)
  | 0 => []
  | depth + 1 =>
      slabShiftedCarrierTargetList extent roots floor depth ++
        (slabConnectedCarrierTargetList extent roots
          (floor + depth)).map (fun carrier => (depth, carrier))

def slabShiftedCarrierTargetWeight
    (extent floor : Nat)
    (tagged : Nat × SlabRootedConnectedCarrier extent) : Q' :=
  slabRootedConnectedCarrierTargetWeight extent
    (floor + tagged.1) tagged.2

theorem mem_slabShiftedCarrierTargetList_of_lt
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (floor depth : Nat)
    {offset : Nat} {carrier : SlabRootedConnectedCarrier extent}
    (hoffset : offset < depth)
    (hcarrier : carrier ∈
      slabConnectedCarrierTargetList extent roots (floor + offset)) :
    (offset, carrier) ∈
      slabShiftedCarrierTargetList extent roots floor depth := by
  induction depth generalizing offset carrier with
  | zero => omega
  | succ previous ih =>
      unfold slabShiftedCarrierTargetList
      apply List.mem_append.mpr
      by_cases hlast : offset = previous
      · subst offset
        exact Or.inr (List.mem_map.mpr ⟨carrier, hcarrier, rfl⟩)
      · exact Or.inl (ih (by omega) hcarrier)

theorem slabShiftedCarrierTargetSum_eqv_finSum
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (floor : Nat) : ∀ depth : Nat,
    listQSum (slabShiftedCarrierTargetWeight extent floor)
        (slabShiftedCarrierTargetList extent roots floor depth) ≈
      finSum (fun offset =>
        listQSum
          (slabRootedConnectedCarrierTargetWeight extent
            (floor + offset))
          (slabConnectedCarrierTargetList extent roots
            (floor + offset))) depth
  | 0 => Q'.eqv_refl 0
  | depth + 1 => by
      rw [finSum_succ]
      unfold slabShiftedCarrierTargetList
      refine Q'.eqv_trans _ _ _
        (listQSum_append (slabShiftedCarrierTargetWeight extent floor)
          (slabShiftedCarrierTargetList extent roots floor depth)
          ((slabConnectedCarrierTargetList extent roots
              (floor + depth)).map (fun carrier => (depth, carrier)))) ?_
      refine Q'.add_eqv_congr'
        (slabShiftedCarrierTargetSum_eqv_finSum
          extent roots floor depth) ?_
      rw [listQSum_map]
      exact Q'.eqv_refl _

/-! ## 3. Direct injection of the complete connected residue -/

def slabConnectedCarrierShiftEncode
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1)) (floor : Nat)
    (entry : SlabConnectedSourceEntry extent roots predicate) :
    Nat × SlabRootedConnectedCarrier extent :=
  ((slabConnectedCarrierSupport defaultRoot entry).length - floor,
    slabRootedConnectedCarrier defaultRoot entry)

theorem connectedSlabCylinderSourcePairs_nodup
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (predicate : List Bool → Bool) :
    (connectedSlabCylinderSourcePairs
      (extent := extent) (roots := roots)
      (predicate := predicate)).Nodup :=
  List.filter_sublist.nodup
    (slabCylinderSourcePairList_nodup extent roots predicate)

theorem slabConnectedSourcePairSum_le_shiftedTarget
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (floor : Nat)
    (hfloor : ∀ entry : SlabConnectedSourceEntry extent roots predicate,
      floor ≤ (slabConnectedCarrierSupport defaultRoot entry).length) :
    listQSum slabCylinderSourcePairWeight
        (connectedSlabCylinderSourcePairs
          (extent := extent) (roots := roots)
          (predicate := predicate)) ≤
      listQSum (slabShiftedCarrierTargetWeight extent floor)
        (slabShiftedCarrierTargetList extent roots floor
          ((physicalFaceEdges (extent + 1)).length + 1)) := by
  have hinjection := listQSum_le_of_injective
    (connectedSlabCylinderSourcePairs
      (extent := extent) (roots := roots)
      (predicate := predicate)).attach
    (slabShiftedCarrierTargetList extent roots floor
      ((physicalFaceEdges (extent + 1)).length + 1))
    (fun entry : SlabConnectedSourceEntry extent roots predicate =>
      slabCylinderSourcePairWeight entry.val)
    (slabShiftedCarrierTargetWeight extent floor)
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
      have hbound := slabConnectedSourcePairWeight_le_support_background
        defaultRoot entry
      unfold slabConnectedCarrierShiftEncode
        slabShiftedCarrierTargetWeight
        slabRootedConnectedCarrierTargetWeight
        slabConnectedCarrierTargetWeight slabRootedConnectedCarrier
        slabConnectedCarrier
      rw [hsize]
      simpa using hbound)
    (fun tagged _ => by
      unfold slabShiftedCarrierTargetWeight
        slabRootedConnectedCarrierTargetWeight
        slabConnectedCarrierTargetWeight
      exact Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorPerFaceEnvelope (by decide) _)
        (Q'.mul_nonneg _ _
          (canonicalSurfaceFamilyActivity_nonnegative
            (extent + 1) tagged.2.2.2.1)
          (canonicalSurfaceFamilyActivity_nonnegative
            (extent + 1) tagged.2.2.2.2)))
  rw [listQSum_attach] at hinjection
  exact hinjection

/-! ## 4. Summing the geometric shells without losing `Z * S` -/

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

theorem slabShiftedCarrierTargetSum_le_tail
    (extent : Nat) (roots : List (CanonicalAtom (extent + 1)))
    (floor depth : Nat) :
    listQSum (slabShiftedCarrierTargetWeight extent floor)
        (slabShiftedCarrierTargetList extent roots floor depth) ≤
      (Q'.ofNat roots.length *
          (anchorCanonicalPartition (extent + 1) *
            anchorEventNumerator (extent + 1)
              (canonicalFamilySlabSupportedB extent))) *
        (anchorEffectiveRatio ^ floor * Q'.ofNat 2) := by
  let partitionProduct := anchorCanonicalPartition (extent + 1) *
    anchorEventNumerator (extent + 1)
      (canonicalFamilySlabSupportedB extent)
  let scale := Q'.ofNat roots.length * partitionProduct
  have htargets := slabShiftedCarrierTargetSum_eqv_finSum
    extent roots floor depth
  have hterms :
      finSum (fun offset =>
          listQSum
            (slabRootedConnectedCarrierTargetWeight extent
              (floor + offset))
            (slabConnectedCarrierTargetList extent roots
              (floor + offset))) depth ≤
        finSum (fun offset =>
          Q'.ofNat roots.length *
            (anchorEffectiveRatio ^ (floor + offset) *
              partitionProduct)) depth :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (fun offset =>
        slabConnectedCarrierTargetSum_le_geom_partition
          extent roots (floor + offset)) depth
  have hreorder :
      (finSum (fun offset =>
          Q'.ofNat roots.length *
            (anchorEffectiveRatio ^ (floor + offset) *
              partitionProduct)) depth) ≈
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
        (mul_eqv_both hpow (Q'.eqv_refl partitionProduct))) ?_
    unfold scale
    ring_qeqv
  have hpull :
      (finSum (fun offset =>
          (scale * anchorEffectiveRatio ^ floor) *
            anchorEffectiveRatio ^ offset) depth) ≈
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
  have hpartition0 : (0 : Q') ≤ partitionProduct :=
    Q'.mul_nonneg _ _
      (anchorCanonicalPartition_nonnegative (extent + 1))
      (anchorEventNumerator_nonnegative (extent + 1)
        (canonicalFamilySlabSupportedB extent))
  have hrootCount0 : (0 : Q') ≤ Q'.ofNat roots.length := by
    rw [Q'.zero_le_iff_num_nonneg]
    exact Int.natCast_nonneg roots.length
  have hscale0 : (0 : Q') ≤ scale * anchorEffectiveRatio ^ floor :=
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

theorem slabConnectedCylinderResidue_le_tail_of_floor
    {extent : Nat} {roots : List (CanonicalAtom (extent + 1))}
    {predicate : List Bool → Bool}
    (defaultRoot : CanonicalAtom (extent + 1))
    (hrootsSupported : ∀ root, root ∈ roots →
      canonicalPolymerSlabSupportedB extent root.val = true)
    (floor : Nat)
    (hfloor : ∀ entry : SlabConnectedSourceEntry extent roots predicate,
      floor ≤ (slabConnectedCarrierSupport defaultRoot entry).length) :
    slabConnectedCylinderResidue extent roots predicate ≤
      (Q'.ofNat roots.length *
          (anchorEffectiveRatio ^ floor * Q'.ofNat 2)) *
        (anchorEventNumerator (extent + 1)
            (canonicalFamilySlabSupportedB extent) *
          anchorCanonicalPartition (extent + 1)) := by
  have hinject := slabConnectedSourcePairSum_le_shiftedTarget
    defaultRoot hrootsSupported floor hfloor
  have htail := slabShiftedCarrierTargetSum_le_tail
    extent roots floor ((physicalFaceEdges (extent + 1)).length + 1)
  have hbound := Q'.le_trans' _ _ _ hinject htail
  unfold slabConnectedCylinderResidue
  exact Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv (by ring_qeqv))

/-! ## 5. Central reflected roots and the time-directed floor -/

def centralLowerCanonicalAtom
    (half : Nat) (hhalf : 1 ≤ half) :
    CanonicalAtom (centralExtent half + 1) :=
  ⟨centralLowerCubeRoot half, by
    simpa [centralAmbient] using centralLowerCubeRoot_canonical hhalf⟩

def centralUpperCanonicalAtom
    (half : Nat) (hhalf : 1 ≤ half) :
    CanonicalAtom (centralExtent half + 1) :=
  ⟨centralUpperCubeRoot half, by
    simpa [centralAmbient] using centralUpperCubeRoot_canonical hhalf⟩

def centralSlabCanonicalRoots
    (half : Nat) (hhalf : 1 ≤ half) :
    List (CanonicalAtom (centralExtent half + 1)) :=
  [centralLowerCanonicalAtom half hhalf,
    centralUpperCanonicalAtom half hhalf]

theorem centralLowerCanonicalAtom_supported
    (half : Nat) (hhalf : 1 ≤ half) :
    canonicalPolymerSlabSupportedB (centralExtent half)
      (centralLowerCanonicalAtom half hhalf).val = true := by
  unfold canonicalPolymerSlabSupportedB
  apply List.all_eq_true.mpr
  intro face hface
  apply decide_eq_true
  apply centralLowerCubeSurface_subset_slab hhalf
  apply (centralLowerCubeRoot_sameSupport hhalf).1
  unfold geometricPolymer
  exact List.mem_map.mpr ⟨face, hface, rfl⟩

theorem centralUpperCanonicalAtom_supported
    (half : Nat) (hhalf : 1 ≤ half) :
    canonicalPolymerSlabSupportedB (centralExtent half)
      (centralUpperCanonicalAtom half hhalf).val = true := by
  unfold canonicalPolymerSlabSupportedB
  apply List.all_eq_true.mpr
  intro face hface
  apply decide_eq_true
  apply centralUpperCubeSurface_subset_slab hhalf
  apply (centralUpperCubeRoot_sameSupport hhalf).1
  unfold geometricPolymer
  exact List.mem_map.mpr ⟨face, hface, rfl⟩

theorem centralSlabCanonicalRoots_supported
    (half : Nat) (hhalf : 1 ≤ half) :
    ∀ root, root ∈ centralSlabCanonicalRoots half hhalf →
      canonicalPolymerSlabSupportedB (centralExtent half) root.val = true := by
  intro root hroot
  simp only [centralSlabCanonicalRoots, List.mem_cons,
    List.not_mem_nil, or_false] at hroot
  rcases hroot with hroot | hroot
  · subst root
    exact centralLowerCanonicalAtom_supported half hhalf
  · subst root
    exact centralUpperCanonicalAtom_supported half hhalf

theorem centralSlabConnectedCarrierSupport_floor
    {half : Nat} (hhalf : 1 ≤ half)
    {predicate : List Bool → Bool}
    (entry : SlabConnectedSourceEntry (centralExtent half)
      (centralSlabCanonicalRoots half hhalf) predicate) :
    half + 1 ≤
      (slabConnectedCarrierSupport
        (centralLowerCanonicalAtom half hhalf) entry).length := by
  let selected := slabSourceRootAtom
    (centralLowerCanonicalAtom half hhalf) entry.val
  have hselected :=
    (slabSourceRootAtom_spec
      (centralLowerCanonicalAtom half hhalf) entry.val entry.property).2
  have hrootFace := slabCanonicalAtomFirstFace_mem selected
  apply slabConnectedCarrierSupport_linf_size_floor
    (centralLowerCanonicalAtom half hhalf)
    (centralSlabCanonicalRoots_supported half hhalf)
    entry hrootFace
  intro q hqBox hqOutside
  simp only [centralSlabCanonicalRoots, List.mem_cons,
    List.not_mem_nil, or_false] at hselected
  rcases hselected with hselected | hselected
  · have hselectedEq : selected =
        centralLowerCanonicalAtom half hhalf := hselected
    rw [hselectedEq]
    exact Nat.le_trans (Nat.le_succ half)
      (centralLowerCubeRoot_nonSlab_linf_floor
        hhalf (slabCanonicalAtomFirstFace_mem
          (centralLowerCanonicalAtom half hhalf)) hqBox hqOutside)
  · have hselectedEq : selected =
        centralUpperCanonicalAtom half hhalf := hselected
    rw [hselectedEq]
    exact centralUpperCubeRoot_nonSlab_linf_floor
      hhalf (slabCanonicalAtomFirstFace_mem
        (centralUpperCanonicalAtom half hhalf)) hqBox hqOutside

theorem centralSlabConnectedCylinderResidue_le_tail
    {half : Nat} (hhalf : 1 ≤ half)
    (predicate : List Bool → Bool) :
    slabConnectedCylinderResidue (centralExtent half)
        (centralSlabCanonicalRoots half hhalf) predicate ≤
      (Q'.ofNat 2 *
          (anchorEffectiveRatio ^ (half + 1) * Q'.ofNat 2)) *
        (anchorEventNumerator (centralAmbient half)
            (canonicalFamilySlabSupportedB (centralExtent half)) *
          anchorCanonicalPartition (centralAmbient half)) := by
  have htail := slabConnectedCylinderResidue_le_tail_of_floor
    (predicate := predicate)
    (centralLowerCanonicalAtom half hhalf)
    (centralSlabCanonicalRoots_supported half hhalf)
    (half + 1)
    (fun entry => centralSlabConnectedCarrierSupport_floor hhalf entry)
  simpa [centralSlabCanonicalRoots, centralAmbient] using htail

#print axioms slabConnectedSourcePairSum_le_shiftedTarget
#print axioms slabShiftedCarrierTargetSum_le_tail
#print axioms slabConnectedCylinderResidue_le_tail_of_floor
#print axioms centralSlabCanonicalRoots_supported
#print axioms centralSlabConnectedCarrierSupport_floor
#print axioms centralSlabConnectedCylinderResidue_le_tail

end YMGap.Continuum.Z4HalfTimeReflectionSlabConnectedCarrierTail
