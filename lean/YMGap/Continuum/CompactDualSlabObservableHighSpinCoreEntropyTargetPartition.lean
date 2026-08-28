/-
# Accepted-target partition of entropy-paid rich representatives

The rich fiber key remembers an accepted target and the two lengths.  After
the inverse fiber has been summed and its strict effective rate proved, the
remaining representatives must be grouped by accepted target.  Within one
such target fiber, the entropy balance makes

```text
(residual, extra := paid - 15 * residual)
```

injective: the pair reconstructs `paid`, while the target is fixed.  This is
the exact finite coordinate system required for the subsequent double
geometric tail.

This module also proves that one realized representative per accepted target
has total target weight at most the physical partition.  It performs no
geometric summation yet.

Constructive contract: realized representative fibers, exact finite target
keys, and natural arithmetic only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyRate
import YMGap.Continuum.CompactDualSlabObservableRemovalPartition

namespace YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyTargetPartition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyFiber
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyRate
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropySplit
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreFarSplit
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreGeometry
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorContraction
open YMGap.Continuum.CompactDualSlabObservableHighSpinExteriorPartition
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Forget lengths only after selecting rich representatives -/

/-- Exact accepted-target key of one rich representative. -/
def slabObservableHighSpinFarCoreEntropyPaidTargetKey
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) : SlabExpandedFineTargetKey :=
  (slabObservableHighSpinCoreEntropyKey representative).targetKey

/-- One actual rich representative for every realized accepted target. -/
def slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    List (SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :=
  keyRepresentatives slabObservableHighSpinFarCoreEntropyPaidTargetKey
    (slabObservableHighSpinFarCoreEntropyPaidRepresentatives
      D faceId hface threshold radius)

/-- Rich representatives landing on the same accepted target as one target
representative. -/
def slabObservableHighSpinFarCoreEntropyPaidTargetFiber
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (targetRepresentative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    List (SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :=
  representativeFiber
    (slabObservableHighSpinFarCoreEntropyPaidRepresentatives
      D faceId hface threshold radius)
    slabObservableHighSpinFarCoreEntropyPaidTargetKey targetRepresentative

/-- Target-fiber membership gives exact equality of accepted-target keys. -/
theorem slabObservableHighSpinFarCoreEntropyPaidTargetFiber_key_eq
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (targetRepresentative representative :
      SlabObservableHighSpinCoreCertificate D faceId hface threshold)
    (hrepresentative : representative ∈
      slabObservableHighSpinFarCoreEntropyPaidTargetFiber
        (hface := hface) (radius := radius) targetRepresentative) :
    slabObservableHighSpinFarCoreEntropyPaidTargetKey targetRepresentative =
      slabObservableHighSpinFarCoreEntropyPaidTargetKey representative :=
  of_decide_eq_true (List.mem_filter.mp hrepresentative).2

/-- Equal accepted-target keys recover equal actual target pairs. -/
theorem slabObservableHighSpinCoreEntropyTarget_eq_of_targetKey_eq
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (left right : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hkey : slabObservableHighSpinFarCoreEntropyPaidTargetKey left =
      slabObservableHighSpinFarCoreEntropyPaidTargetKey right) :
    slabObservableHighSpinCoreEntropyTarget left =
      slabObservableHighSpinCoreEntropyTarget right := by
  apply slabExpandedFineTargetKey_eq_source_eq D
  · exact slabObservableHighSpinExteriorTarget_mem left.sourceEntry
  · exact slabObservableHighSpinExteriorTarget_mem right.sourceEntry
  · exact hkey

/-! ## 2. Residual and extra are injective within one target -/

/-- The two nonnegative coordinates left after entropy blocking. -/
def slabObservableHighSpinCoreEntropyEffectivePair
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) : Nat × Nat :=
  (slabObservableHighSpinCoreCertificateResidualLength representative,
    slabObservableHighSpinCoreCertificatePaidLength representative -
      15 * slabObservableHighSpinCoreCertificateResidualLength
        representative)

private theorem map_injective_on_of_map_nodup
    {A B : Type} (map : A -> B) : forall items : List A,
    (items.map map).Nodup ->
      forall left, left ∈ items -> forall right, right ∈ items ->
        map left = map right -> left = right
  | [], _, left, hleft, _, _, _ => absurd hleft List.not_mem_nil
  | head :: tail, hnodup, left, hleft, right, hright, heq => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hleft with hleftHead | hleftTail
      · subst left
        rcases List.mem_cons.mp hright with hrightHead | hrightTail
        · exact hrightHead.symm
        · exact absurd
            (heq ▸ List.mem_map.mpr ⟨right, hrightTail, rfl⟩)
            hparts.1
      · rcases List.mem_cons.mp hright with hrightHead | hrightTail
        · subst right
          exact absurd
            (heq.symm ▸ List.mem_map.mpr ⟨left, hleftTail, rfl⟩)
            hparts.1
        · exact map_injective_on_of_map_nodup map tail hparts.2
            left hleftTail right hrightTail heq

private theorem slabObservableHighSpinCoreEntropyKey_eq_of_fields
    (left right : SlabObservableHighSpinCoreEntropyKey)
    (htarget : left.targetKey = right.targetKey)
    (hpaid : left.paidLength = right.paidLength)
    (hresidual : left.residualLength = right.residualLength) :
    left = right := by
  cases left with
  | mk leftTarget leftPaid leftResidual =>
      cases right with
      | mk rightTarget rightPaid rightResidual =>
          change leftTarget = rightTarget at htarget
          change leftPaid = rightPaid at hpaid
          change leftResidual = rightResidual at hresidual
          subst rightTarget
          subst rightPaid
          subst rightResidual
          rfl

/-- Selected rich representatives retain pairwise distinct complete rich
keys. -/
theorem slabObservableHighSpinFarCoreEntropyPaidRepresentatives_keys_nodup
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    ((slabObservableHighSpinFarCoreEntropyPaidRepresentatives
        D faceId hface threshold radius).map
      slabObservableHighSpinCoreEntropyKey).Nodup := by
  unfold slabObservableHighSpinFarCoreEntropyPaidRepresentatives
  exact keyRepresentatives_keys_nodup
    slabObservableHighSpinCoreEntropyKey
    (slabObservableHighSpinFarCoreEntropyPaidCertificates
      D faceId hface threshold radius)

/-- The effective coordinate pair is injective inside one accepted-target
fiber. -/
theorem slabObservableHighSpinFarCoreEntropyPaidTargetFiber_pair_injective
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (targetRepresentative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (left : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hleft : left ∈
      slabObservableHighSpinFarCoreEntropyPaidTargetFiber
        (hface := hface) (radius := radius) targetRepresentative)
    (right : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hright : right ∈
      slabObservableHighSpinFarCoreEntropyPaidTargetFiber
        (hface := hface) (radius := radius) targetRepresentative)
    (hpair : slabObservableHighSpinCoreEntropyEffectivePair left =
      slabObservableHighSpinCoreEntropyEffectivePair right) :
    left = right := by
  have hleftTarget :=
    slabObservableHighSpinFarCoreEntropyPaidTargetFiber_key_eq
      targetRepresentative left hleft
  have hrightTarget :=
    slabObservableHighSpinFarCoreEntropyPaidTargetFiber_key_eq
      targetRepresentative right hright
  have htarget :
      slabObservableHighSpinFarCoreEntropyPaidTargetKey left =
        slabObservableHighSpinFarCoreEntropyPaidTargetKey right :=
    hleftTarget.symm.trans hrightTarget
  have hleftMem := (List.mem_filter.mp hleft).1
  have hrightMem := (List.mem_filter.mp hright).1
  have hleftPaid :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentative_mem
      left hleftMem
  have hrightPaid :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentative_mem
      right hrightMem
  have hleftBalance :=
    slabObservableHighSpinFarCoreEntropyPaid_balance left hleftPaid
  have hrightBalance :=
    slabObservableHighSpinFarCoreEntropyPaid_balance right hrightPaid
  have hresidual := congrArg Prod.fst hpair
  have hextra := congrArg Prod.snd hpair
  have hpaid :
      slabObservableHighSpinCoreCertificatePaidLength left =
        slabObservableHighSpinCoreCertificatePaidLength right := by
    change
      slabObservableHighSpinCoreCertificateResidualLength left =
        slabObservableHighSpinCoreCertificateResidualLength right at hresidual
    change
      slabObservableHighSpinCoreCertificatePaidLength left -
          15 * slabObservableHighSpinCoreCertificateResidualLength left =
        slabObservableHighSpinCoreCertificatePaidLength right -
          15 * slabObservableHighSpinCoreCertificateResidualLength right
      at hextra
    omega
  have hrich : slabObservableHighSpinCoreEntropyKey left =
      slabObservableHighSpinCoreEntropyKey right := by
    apply slabObservableHighSpinCoreEntropyKey_eq_of_fields
    · exact htarget
    · exact hpaid
    · exact hresidual
  apply map_injective_on_of_map_nodup
    slabObservableHighSpinCoreEntropyKey
    (slabObservableHighSpinFarCoreEntropyPaidRepresentatives
      D faceId hface threshold radius)
    (slabObservableHighSpinFarCoreEntropyPaidRepresentatives_keys_nodup
      D faceId hface threshold radius)
  · exact hleftMem
  · exact hrightMem
  · exact hrich

/-! ## 3. Coordinate bounds and exact nested partition -/

/-- Both effective coordinates lie below the inclusive physical component
size ceiling. -/
theorem slabObservableHighSpinFarCoreEntropyPaidRepresentative_pair_bounds
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold : Nat}
    (representative : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold) :
    (slabObservableHighSpinCoreEntropyEffectivePair representative).1 <=
        slabObservableRemovalMaxSize D ∧
      (slabObservableHighSpinCoreEntropyEffectivePair representative).2 <=
        slabObservableRemovalMaxSize D := by
  have hcomplete :=
    slabObservableHighSpinExteriorPeelSize_le_removalMaxSize
      hface representative.sourceEntry
  have hsplit :=
    slabObservableHighSpinCoreCertificate_peel_length_split representative
  change
    (SlabFusionWitnessFaceStrandSeed.peelFaces
      (representative.sourceEntry.seed D faceId hface)).length <=
        slabObservableRemovalMaxSize D at hcomplete
  change
    (SlabFusionWitnessFaceStrandSeed.peelFaces
        (representative.sourceEntry.seed D faceId hface)).length =
      slabObservableHighSpinCoreCertificatePaidLength representative +
        slabObservableHighSpinCoreCertificateResidualLength representative
    at hsplit
  change
    slabObservableHighSpinCoreCertificateResidualLength representative <=
        slabObservableRemovalMaxSize D ∧
      slabObservableHighSpinCoreCertificatePaidLength representative -
          15 *
            slabObservableHighSpinCoreCertificateResidualLength representative <=
        slabObservableRemovalMaxSize D
  constructor <;> omega

/-- Target fibers exactly regroup the already exact rich-fiber partition. -/
theorem slabObservableHighSpinFarCoreEntropyPaidTargetFibers_weight_total
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    listQSum
        (fun targetRepresentative =>
          listQSum
            (fun representative =>
              listQSum slabObservableHighSpinCoreCertificateWeight
                (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
                  (hface := hface) (radius := radius) representative))
            (slabObservableHighSpinFarCoreEntropyPaidTargetFiber
              (hface := hface) (radius := radius) targetRepresentative))
        (slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives
          D faceId hface threshold radius) ≈
      listQSum slabObservableHighSpinCoreCertificateWeight
        (slabObservableHighSpinFarCoreEntropyPaidCertificates
          D faceId hface threshold radius) := by
  have htargets := keyRepresentativeFibers_weight_total
    (slabObservableHighSpinFarCoreEntropyPaidRepresentatives
      D faceId hface threshold radius)
    (fun representative =>
      listQSum slabObservableHighSpinCoreCertificateWeight
        (slabObservableHighSpinFarCoreEntropyPaidRepresentativeFiber
          (hface := hface) (radius := radius) representative))
    slabObservableHighSpinFarCoreEntropyPaidTargetKey
  have hrich :=
    slabObservableHighSpinFarCoreEntropyPaidRepresentativeFibers_weight_total
      D faceId hface threshold radius
  exact Q'.eqv_trans _ _ _ htargets hrich

/-! ## 4. One accepted target charge lies under the physical partition -/

/-- Selected target representatives have distinct exact accepted-target
keys. -/
theorem slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives_keys_nodup
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    ((slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives
        D faceId hface threshold radius).map
      slabObservableHighSpinFarCoreEntropyPaidTargetKey).Nodup := by
  unfold slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives
  exact keyRepresentatives_keys_nodup
    slabObservableHighSpinFarCoreEntropyPaidTargetKey
    (slabObservableHighSpinFarCoreEntropyPaidRepresentatives
      D faceId hface threshold radius)

private theorem nodup_of_map_nodup {A B : Type} (map : A -> B) :
    forall items : List A, (items.map map).Nodup -> items.Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_of_map_nodup map tail hparts.2⟩
      intro hmem
      exact hparts.1 (List.mem_map.mpr ⟨head, hmem, rfl⟩)

private theorem listQSum_member_le_nonnegative_local
    {A : Type} (value : A -> Q')
    (hvalue : forall item, (0 : Q') <= value item) :
    forall (items : List A) {selected : A},
      selected ∈ items -> value selected <= listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, selected, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst selected
        exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative_on value tail (fun item _ => hvalue item))
      · have ih := listQSum_member_le_nonnegative_local
          value hvalue tail htail
        have htailLe : listQSum value tail <=
            value head + listQSum value tail := by
          have hadd := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at hadd
        exact Q'.le_trans' _ _ _ ih htailLe

/-- One representative per realized accepted target has total target weight
at most the full expanded physical partition. -/
theorem slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives_weight_le_partition
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) :
    listQSum
        (fun representative => slabExpandedFineSourceWeight D
          (slabObservableHighSpinCoreEntropyTarget representative))
        (slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives
          D faceId hface threshold radius) <=
      D.physicalPartition := by
  let representatives :=
    slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives
      D faceId hface threshold radius
  have hrepresentatives : representatives.Nodup :=
    nodup_of_map_nodup
      slabObservableHighSpinFarCoreEntropyPaidTargetKey representatives
      (slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives_keys_nodup
        D faceId hface threshold radius)
  have hsum :
      listQSum
          (fun representative => slabExpandedFineSourceWeight D
            (slabObservableHighSpinCoreEntropyTarget representative))
          representatives <=
        listQSum
          (fiberWeight (slabExpandedFineSources D)
            (slabExpandedFineSourceWeight D)
            (fun source => slabExpandedFineTargetKey D source.1 source.2))
          (slabExpandedFineTargetKeys D) := by
    apply listQSum_le_of_injective
      representatives (slabExpandedFineTargetKeys D)
      (fun representative => slabExpandedFineSourceWeight D
        (slabObservableHighSpinCoreEntropyTarget representative))
      (fiberWeight (slabExpandedFineSources D)
        (slabExpandedFineSourceWeight D)
        (fun source => slabExpandedFineTargetKey D source.1 source.2))
      slabObservableHighSpinFarCoreEntropyPaidTargetKey
    · exact hrepresentatives
    · intro representative _
      unfold slabObservableHighSpinFarCoreEntropyPaidTargetKey
        slabObservableHighSpinCoreEntropyKey
        slabObservableHighSpinCoreEntropySourceKey
        slabExpandedFineTargetKeys
      exact List.mem_map.mpr
        ⟨slabObservableHighSpinCoreEntropyTarget representative,
          slabObservableHighSpinExteriorTarget_mem
            representative.sourceEntry, rfl⟩
    · intro left hleft right hright hkey
      exact map_injective_on_of_map_nodup
        slabObservableHighSpinFarCoreEntropyPaidTargetKey representatives
        (slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives_keys_nodup
          D faceId hface threshold radius)
        left hleft right hright hkey
    · intro representative _
      apply listQSum_member_le_nonnegative_local
        (slabExpandedFineSourceWeight D)
        (slabObservableExpandedFineSourceWeight_nonnegative D)
      apply List.mem_filter.mpr
      refine ⟨slabObservableHighSpinExteriorTarget_mem
        representative.sourceEntry, ?_⟩
      apply decide_eq_true
      rfl
    · intro key _
      exact fiberWeight_nonnegative
        (slabExpandedFineSources D) (slabExpandedFineSourceWeight D)
        (fun source => slabExpandedFineTargetKey D source.1 source.2) key
        (fun source _ =>
          slabObservableExpandedFineSourceWeight_nonnegative D source)
  have hfiberTotal := fiberWeight_total
    (slabExpandedFineSources D) (slabExpandedFineSourceWeight D)
    (fun source => slabExpandedFineTargetKey D source.1 source.2)
    (slabExpandedFineTargetKeys D) (slabExpandedFineTargetKeys_nodup D)
    (fun source hsource => by
      unfold slabExpandedFineTargetKeys
      exact List.mem_map.mpr ⟨source, hsource, rfl⟩)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hfiberTotal
        (slabExpandedFineSources_weight_total D)))

#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetKey
#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives
#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetFiber
#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetFiber_key_eq
#print axioms slabObservableHighSpinCoreEntropyTarget_eq_of_targetKey_eq
#print axioms slabObservableHighSpinCoreEntropyEffectivePair
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentatives_keys_nodup
#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetFiber_pair_injective
#print axioms slabObservableHighSpinFarCoreEntropyPaidRepresentative_pair_bounds
#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetFibers_weight_total
#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives_keys_nodup
#print axioms slabObservableHighSpinFarCoreEntropyPaidTargetRepresentatives_weight_le_partition

end YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyTargetPartition
