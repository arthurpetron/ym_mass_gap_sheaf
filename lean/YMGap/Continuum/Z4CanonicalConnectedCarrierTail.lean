/-
# Uniform tail for the connected canonical source residue

Every connected source entry is encoded by its support size, colored carrier,
and the two exact backgrounds.  The spatial path forces the size to begin at
`distance + 2`; the finite support gives an explicit upper cutoff.  Summing
the fixed-size carrier bounds therefore produces a uniform geometric tail
with the correctly normalized background factor `Z_n * Z_small`.
-/

import YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize

namespace YMGap.Continuum.Z4CanonicalConnectedCarrierTail

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalColoredSupportWeight
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize
open YMGap.Continuum.Z4CanonicalConnectedCarrierWeight
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A finite upper cutoff for every carrier support -/

theorem connectedCarrierSupport_length_le_ambient
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (entry : ConnectedSourceEntry root hsmall) :
    (connectedCarrierSupport hsmall entry).length ≤
      (physicalFaceEdges n).length := by
  have hsupport := connectedCarrierSupport_mem_faceSupports hsmall entry
  have hnodup := nodup_of_mem_sublists
    (physicalFaceEdges n) (connectedCarrierSupport hsmall entry)
    (physicalFaceEdges_nodup n) hsupport
  exact length_le_of_unique_representation
    (fun source target : Nat => source = target)
    (connectedCarrierSupport hsmall entry) (physicalFaceEdges n)
    hnodup
    (fun face hface =>
      ⟨face, mem_of_mem_sublists (physicalFaceEdges n)
        (connectedCarrierSupport hsmall entry) hsupport face hface, rfl⟩)
    (fun left _ right _ target hleft hright =>
      hleft.trans hright.symm)

/-! ## 2. A recursive list of shifted, size-tagged carrier shells -/

def shiftedCarrierTargetList
    (small n rootFace floor : Nat) : Nat → List (Nat × ConnectedCarrier)
  | 0 => []
  | depth + 1 =>
      shiftedCarrierTargetList small n rootFace floor depth ++
        (connectedCarrierTargetList small n rootFace (floor + depth)).map
          (fun carrier => (depth, carrier))

def shiftedCarrierTargetWeight (n floor : Nat)
    (tagged : Nat × ConnectedCarrier) : Q' :=
  connectedCarrierTargetWeight n (floor + tagged.1) tagged.2

theorem mem_shiftedCarrierTargetList_of_lt
    (small n rootFace floor depth : Nat)
    {offset : Nat} {carrier : ConnectedCarrier}
    (hoffset : offset < depth)
    (hcarrier : carrier ∈
      connectedCarrierTargetList small n rootFace (floor + offset)) :
    (offset, carrier) ∈
      shiftedCarrierTargetList small n rootFace floor depth := by
  induction depth generalizing offset carrier with
  | zero => omega
  | succ previous ih =>
      unfold shiftedCarrierTargetList
      apply List.mem_append.mpr
      by_cases hlast : offset = previous
      · subst offset
        exact Or.inr (List.mem_map.mpr ⟨carrier, hcarrier, rfl⟩)
      · exact Or.inl (ih (by omega) hcarrier)

theorem shiftedCarrierTargetSum_eqv_finSum
    (small n rootFace floor : Nat) : ∀ depth : Nat,
    listQSum (shiftedCarrierTargetWeight n floor)
        (shiftedCarrierTargetList small n rootFace floor depth) ≈
      finSum (fun offset =>
        listQSum (connectedCarrierTargetWeight n (floor + offset))
          (connectedCarrierTargetList small n rootFace
            (floor + offset))) depth
  | 0 => Q'.eqv_refl 0
  | depth + 1 => by
      rw [finSum_succ]
      unfold shiftedCarrierTargetList
      refine Q'.eqv_trans _ _ _
        (listQSum_append (shiftedCarrierTargetWeight n floor)
          (shiftedCarrierTargetList small n rootFace floor depth)
          ((connectedCarrierTargetList small n rootFace
              (floor + depth)).map (fun carrier => (depth, carrier)))) ?_
      refine Q'.add_eqv_congr'
        (shiftedCarrierTargetSum_eqv_finSum small n rootFace floor depth) ?_
      rw [listQSum_map]
      exact Q'.eqv_refl _

/-! ## 3. Direct injection of all connected entries into the shifted shells -/

def connectedCarrierShiftEncode
    {small n : Nat} {root : List Nat} (hsmall : small ≤ n)
    (floor : Nat) (entry : ConnectedSourceEntry root hsmall) :
    Nat × ConnectedCarrier :=
  ((connectedCarrierSupport hsmall entry).length - floor,
    connectedCarrier hsmall entry)

theorem connectedSourcePairs_nodup
    {small n : Nat} (hsmall : small ≤ n) (root : List Nat) :
    (connectedSourcePairs (root := root) hsmall).Nodup :=
  List.filter_sublist.nodup (sourcePairList_nodup hsmall root)

theorem connectedSourcePairSum_le_shiftedTarget
    {small n inner distance start : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum sourcePairWeight
        (connectedSourcePairs (root := root) hsmall) ≤
      listQSum (shiftedCarrierTargetWeight n (distance + 2))
        (shiftedCarrierTargetList small n start (distance + 2)
          ((physicalFaceEdges n).length + 1)) := by
  have hinjection := listQSum_le_of_injective
    (connectedSourcePairs (root := root) hsmall).attach
    (shiftedCarrierTargetList small n start (distance + 2)
      ((physicalFaceEdges n).length + 1))
    (fun entry : ConnectedSourceEntry root hsmall =>
      sourcePairWeight entry.val)
    (shiftedCarrierTargetWeight n (distance + 2))
    (connectedCarrierShiftEncode hsmall (distance + 2))
    (attach_nodup_of_nodup _ (connectedSourcePairs_nodup hsmall root))
    (fun entry _ => by
      have hfloor := connectedCarrierSupport_boundary_floor
        hsmall entry hstart hstartInner hbox
      have hmax := connectedCarrierSupport_length_le_ambient hsmall entry
      let offset := (connectedCarrierSupport hsmall entry).length -
        (distance + 2)
      have hoffset : offset < (physicalFaceEdges n).length + 1 := by
        unfold offset
        omega
      have hsize :
          (connectedCarrierSupport hsmall entry).length =
            distance + 2 + offset := by
        unfold offset
        omega
      apply mem_shiftedCarrierTargetList_of_lt
        small n start (distance + 2)
        ((physicalFaceEdges n).length + 1) hoffset
      exact connectedCarrier_mem_target hsmall entry hstart hsize)
    (fun first _ second _ heq => by
      apply connectedCarrier_injective hsmall first second
      exact congrArg Prod.snd heq)
    (fun entry _ => by
      have hfloor := connectedCarrierSupport_boundary_floor
        hsmall entry hstart hstartInner hbox
      have hsize :
          distance + 2 +
              ((connectedCarrierSupport hsmall entry).length -
                (distance + 2)) =
            (connectedCarrierSupport hsmall entry).length := by
        omega
      have hbound := connectedSourcePairWeight_le_support_background
        hsmall entry
      unfold connectedBackgroundPairWeight at hbound
      unfold connectedCarrierShiftEncode shiftedCarrierTargetWeight
        connectedCarrierTargetWeight connectedCarrier
      rw [hsize]
      simpa using hbound)
    (fun tagged _ => by
      unfold shiftedCarrierTargetWeight connectedCarrierTargetWeight
      exact Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorPerFaceEnvelope (by decide) _)
        (Q'.mul_nonneg _ _
          (canonicalSurfaceFamilyActivity_nonnegative n tagged.2.2.1)
          (canonicalSurfaceFamilyActivity_nonnegative n tagged.2.2.2)))
  rw [listQSum_attach] at hinjection
  exact hinjection

/-! ## 4. Summing the geometric shells -/

theorem connectedCarrierTargetSum_le_geom_partition
    {small n : Nat} (hsmall : small ≤ n)
    (rootFace size : Nat) :
    listQSum (connectedCarrierTargetWeight n size)
        (connectedCarrierTargetList small n rootFace size) ≤
      anchorEffectiveRatio ^ size *
        (anchorCanonicalPartition n * anchorCanonicalPartition small) := by
  have hfactor := connectedCarrierTargetSum_eqv hsmall rootFace size
  have hpartition0 : (0 : Q') ≤
      anchorCanonicalPartition n * anchorCanonicalPartition small :=
    Q'.mul_nonneg _ _
      (anchorCanonicalPartition_nonnegative n)
      (anchorCanonicalPartition_nonnegative small)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (canonicalColoredPinnedSizeWeightSum_le_geom n rootFace size)
      hpartition0)

theorem shiftedCarrierTargetSum_le_tail
    {small n : Nat} (hsmall : small ≤ n)
    (rootFace floor depth : Nat) :
    listQSum (shiftedCarrierTargetWeight n floor)
        (shiftedCarrierTargetList small n rootFace floor depth) ≤
      (anchorCanonicalPartition n * anchorCanonicalPartition small) *
        (anchorEffectiveRatio ^ floor * Q'.ofNat 2) := by
  let partitionProduct :=
    anchorCanonicalPartition n * anchorCanonicalPartition small
  have htargets := shiftedCarrierTargetSum_eqv_finSum
    small n rootFace floor depth
  have hterms :
      finSum (fun offset =>
          listQSum (connectedCarrierTargetWeight n (floor + offset))
            (connectedCarrierTargetList small n rootFace
              (floor + offset))) depth ≤
        finSum (fun offset =>
          anchorEffectiveRatio ^ (floor + offset) * partitionProduct)
          depth :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (fun offset =>
        connectedCarrierTargetSum_le_geom_partition
          hsmall rootFace (floor + offset)) depth
  have hreorder :
      (finSum (fun offset =>
          anchorEffectiveRatio ^ (floor + offset) * partitionProduct)
          depth).eqv
        (finSum (fun offset =>
          (partitionProduct * anchorEffectiveRatio ^ floor) *
            anchorEffectiveRatio ^ offset) depth) := by
    apply RationalTail.finSum_eqv_congr
    intro offset
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv
        (anchorEffectiveRatio ^ (floor + offset)) partitionProduct) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left partitionProduct _ _
        (Q'.pow_add_eqv anchorEffectiveRatio floor offset)) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv partitionProduct
        (anchorEffectiveRatio ^ floor) (anchorEffectiveRatio ^ offset))
  have hpull :
      (finSum (fun offset =>
          (partitionProduct * anchorEffectiveRatio ^ floor) *
            anchorEffectiveRatio ^ offset) depth).eqv
        ((partitionProduct * anchorEffectiveRatio ^ floor) *
          finSum (fun offset => anchorEffectiveRatio ^ offset) depth) :=
    Q'.eqv_symm (RationalTail.const_mul_finSum
      (fun offset => anchorEffectiveRatio ^ offset)
      (partitionProduct * anchorEffectiveRatio ^ floor) depth)
  have hgeo :
      finSum (fun offset => anchorEffectiveRatio ^ offset) depth ≤
        Q'.ofNat 2 :=
    geom_partial_le_two anchorEffectiveRatio_nonnegative
      anchorEffectiveRatio_le_half depth
  have hproduct0 : (0 : Q') ≤ partitionProduct :=
    Q'.mul_nonneg _ _
      (anchorCanonicalPartition_nonnegative n)
      (anchorCanonicalPartition_nonnegative small)
  have hscale0 : (0 : Q') ≤
      partitionProduct * anchorEffectiveRatio ^ floor :=
    Q'.mul_nonneg _ _ hproduct0
      (Q'.pow_nonneg anchorEffectiveRatio
        anchorEffectiveRatio_nonnegative floor)
  have hscaled :
      (partitionProduct * anchorEffectiveRatio ^ floor) *
          finSum (fun offset => anchorEffectiveRatio ^ offset) depth ≤
        (partitionProduct * anchorEffectiveRatio ^ floor) * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgeo hscale0
  have hfinal :
      ((partitionProduct * anchorEffectiveRatio ^ floor) * Q'.ofNat 2).eqv
        (partitionProduct *
          (anchorEffectiveRatio ^ floor * Q'.ofNat 2)) :=
    Q'.mul_assoc_eqv partitionProduct
      (anchorEffectiveRatio ^ floor) (Q'.ofNat 2)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htargets)
    (Q'.le_trans' _ _ _ hterms
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpull)
          (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hfinal)))))

theorem connectedSourcePairSum_le_boundaryTail
    {small n inner distance start : Nat} {root : List Nat}
    (hsmall : small ≤ n)
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum sourcePairWeight
        (connectedSourcePairs (root := root) hsmall) ≤
      (anchorCanonicalPartition n * anchorCanonicalPartition small) *
        (anchorEffectiveRatio ^ (distance + 2) * Q'.ofNat 2) := by
  exact Q'.le_trans' _ _ _
    (connectedSourcePairSum_le_shiftedTarget
      hsmall hstart hstartInner hbox)
    (shiftedCarrierTargetSum_le_tail hsmall start (distance + 2)
      ((physicalFaceEdges n).length + 1))

end YMGap.Continuum.Z4CanonicalConnectedCarrierTail

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierTail.connectedCarrierSupport_length_le_ambient
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierTail.connectedSourcePairSum_le_shiftedTarget
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierTail.shiftedCarrierTargetSum_le_tail
#print axioms YMGap.Continuum.Z4CanonicalConnectedCarrierTail.connectedSourcePairSum_le_boundaryTail
