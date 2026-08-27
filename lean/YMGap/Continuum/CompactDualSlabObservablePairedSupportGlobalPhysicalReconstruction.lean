/-
# Global support and value words reconstruct the source physical pair

Fix the terminal state of canonical target-support peeling.  The global shape
word recovers the initial target component, and the global paired value word
recovers both physical labels on every face of that component.  The locality
theorem says that outside the component the source already equals the fixed
terminal state.  These two regions therefore reconstruct the complete source
physical pair.

This is the first injectivity theorem for the aggregate code: per-peel animal
and physical words have disappeared entirely.  Auxiliary assignments remain
to be reconstructed by their own aggregate/dependent `4096^M` factor.

Constructive contract: finite list injectivity, corrected-slab inverse
indexing, and pointwise function extensionality only; no choice, `Classical`,
`sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalReconstruction

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingLocality
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalCode
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalShapeCode
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The decoded face-id order covers the complete face component -/

theorem slabObservableTwoReplicaPairTargetSupportGlobalFaceIds_cover_component
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget faceId : Nat)
    (hface : faceId ∈
      slabTwoReplicaTargetSupportComponent D.extent
        pair.1.1.1 pair.2.1.1 targetFaceId) :
    faceId ∈ slabObservableTwoReplicaPairTargetSupportGlobalFaceIds
      D rootFaceId targetFaceId htarget pair hpair massBudget := by
  have hplaquetteOriginal : slabPlaquetteAt D.extent faceId ∈
      slabObservableTwoReplicaPairTargetSupportPlaquettes
        D pair targetFaceId := by
    apply List.mem_eraseDups.mpr
    apply List.mem_map.mpr
    exact ⟨faceId, hface, rfl⟩
  have hplaquetteDecoded :=
    (slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport_sameSupport
      D rootFaceId targetFaceId htarget pair hpair massBudget).1
        (slabPlaquetteAt D.extent faceId) hplaquetteOriginal
  unfold slabObservableTwoReplicaPairTargetSupportGlobalFaceIds
  apply List.mem_map.mpr
  refine ⟨slabPlaquetteAt D.extent faceId, hplaquetteDecoded, ?_⟩
  exact slabFaceIdOfPlaquette_slabPlaquetteAt
    (slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
      D rootFaceId targetFaceId htarget pair hpair faceId hface)

/-! ## 2. A paired value table is faithful on its face-id list -/

private theorem pairValueWord_eq_at_of_mem
    (leftFirst leftSecond rightFirst rightSecond : Nat → Nat) :
    ∀ faceIds : List Nat,
      (faceIds.flatMap fun faceId =>
          [leftFirst faceId, leftSecond faceId]) =
        (faceIds.flatMap fun faceId =>
          [rightFirst faceId, rightSecond faceId]) →
      ∀ faceId, faceId ∈ faceIds →
        leftFirst faceId = rightFirst faceId ∧
          leftSecond faceId = rightSecond faceId
  | [], _, faceId, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hword, faceId, hmem => by
      change
        leftFirst head :: leftSecond head ::
            (tail.flatMap fun id =>
              [leftFirst id, leftSecond id]) =
          rightFirst head :: rightSecond head ::
            (tail.flatMap fun id =>
              [rightFirst id, rightSecond id]) at hword
      have hfirst := (List.cons.inj hword).1
      have hrest := (List.cons.inj hword).2
      have hsecond := (List.cons.inj hrest).1
      have htail := (List.cons.inj hrest).2
      rcases List.mem_cons.mp hmem with hhead | htailMem
      · subst faceId
        exact ⟨hfirst, hsecond⟩
      · exact pairValueWord_eq_at_of_mem
          leftFirst leftSecond rightFirst rightSecond
          tail htail faceId htailMem

/-! ## 3. Equal aggregate words give equal labels on the component -/

theorem slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues_eq_on_component
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (left right : SlabObservableTwoReplicaPair D rootFaceId)
    (hleft : left ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hright : right ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat)
    (hshape :
      slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget right hright massBudget)
    (hvalues :
      slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
          D rootFaceId targetFaceId htarget right hright massBudget)
    (faceId : Nat)
    (hface : faceId ∈
      slabTwoReplicaTargetSupportComponent D.extent
        left.1.1.1 left.2.1.1 targetFaceId) :
    left.1.1.1 faceId = right.1.1.1 faceId ∧
      left.2.1.1 faceId = right.2.1.1 faceId := by
  have hdecoded :
      slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport
          D rootFaceId targetFaceId htarget right hright massBudget := by
    unfold
      slabObservableTwoReplicaPairTargetSupportGlobalDecodedSupport
    rw [hshape]
  have hfaceIds :
      slabObservableTwoReplicaPairTargetSupportGlobalFaceIds
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalFaceIds
          D rootFaceId targetFaceId htarget right hright massBudget := by
    unfold slabObservableTwoReplicaPairTargetSupportGlobalFaceIds
    rw [hdecoded]
  have hfaceMem :=
    slabObservableTwoReplicaPairTargetSupportGlobalFaceIds_cover_component
      D rootFaceId targetFaceId htarget left hleft massBudget faceId hface
  unfold slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
    at hvalues
  rw [← hfaceIds] at hvalues
  exact pairValueWord_eq_at_of_mem
    left.1.1.1 left.2.1.1 right.1.1.1 right.2.1.1
    (slabObservableTwoReplicaPairTargetSupportGlobalFaceIds
      D rootFaceId targetFaceId htarget left hleft massBudget)
    hvalues faceId hfaceMem

/-! ## 4. Equal shape words identify the face component itself -/

theorem slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_eq_component_mem
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (left right : SlabObservableTwoReplicaPair D rootFaceId)
    (hleft : left ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hright : right ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat)
    (hshape :
      slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget right hright massBudget)
    (faceId : Nat) :
    faceId ∈ slabTwoReplicaTargetSupportComponent D.extent
        left.1.1.1 left.2.1.1 targetFaceId ↔
      faceId ∈ slabTwoReplicaTargetSupportComponent D.extent
        right.1.1.1 right.2.1.1 targetFaceId := by
  have hsupport :=
    slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_eq_sameSupport
      D rootFaceId targetFaceId htarget left right hleft hright
      massBudget hshape
  constructor
  · intro hface
    have hleftPhysical :=
      slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
        D rootFaceId targetFaceId htarget left hleft faceId hface
    have hleftPlaquette : slabPlaquetteAt D.extent faceId ∈
        slabObservableTwoReplicaPairTargetSupportPlaquettes
          D left targetFaceId := by
      apply List.mem_eraseDups.mpr
      exact List.mem_map.mpr ⟨faceId, hface, rfl⟩
    have hrightPlaquette := hsupport.1
      (slabPlaquetteAt D.extent faceId) hleftPlaquette
    let rightFaceId :=
      slabObservableTwoReplicaPairTargetSupportFaceValue
        D right targetFaceId (slabPlaquetteAt D.extent faceId)
    have hrightFace :=
      slabObservableTwoReplicaPairTargetSupportFaceValue_mem
        D rootFaceId targetFaceId htarget right hright
          (slabPlaquetteAt D.extent faceId)
    have hrightProjection :=
      slabObservableTwoReplicaPairTargetSupportFaceValue_projection
        D right targetFaceId (slabPlaquetteAt D.extent faceId)
          hrightPlaquette
    have hrightPhysical :=
      slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
        D rootFaceId targetFaceId htarget right hright
          rightFaceId hrightFace
    have heq : rightFaceId = faceId :=
      slabPlaquetteAt_injective_on_physical
        hrightPhysical hleftPhysical hrightProjection
    rw [← heq]
    exact hrightFace
  · intro hface
    have hrightPhysical :=
      slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
        D rootFaceId targetFaceId htarget right hright faceId hface
    have hrightPlaquette : slabPlaquetteAt D.extent faceId ∈
        slabObservableTwoReplicaPairTargetSupportPlaquettes
          D right targetFaceId := by
      apply List.mem_eraseDups.mpr
      exact List.mem_map.mpr ⟨faceId, hface, rfl⟩
    have hleftPlaquette := hsupport.2
      (slabPlaquetteAt D.extent faceId) hrightPlaquette
    let leftFaceId :=
      slabObservableTwoReplicaPairTargetSupportFaceValue
        D left targetFaceId (slabPlaquetteAt D.extent faceId)
    have hleftFace :=
      slabObservableTwoReplicaPairTargetSupportFaceValue_mem
        D rootFaceId targetFaceId htarget left hleft
          (slabPlaquetteAt D.extent faceId)
    have hleftProjection :=
      slabObservableTwoReplicaPairTargetSupportFaceValue_projection
        D left targetFaceId (slabPlaquetteAt D.extent faceId)
          hleftPlaquette
    have hleftPhysical :=
      slabObservableTwoReplicaPairTargetSupportComponent_face_mem_physical
        D rootFaceId targetFaceId htarget left hleft
          leftFaceId hleftFace
    have heq : leftFaceId = faceId :=
      slabPlaquetteAt_injective_on_physical
        hleftPhysical hrightPhysical hleftProjection
    rw [← heq]
    exact hleftFace

/-! ## 5. Complete physical reconstruction at a fixed terminal -/

theorem slabObservablePair_sourcePhysical_eq_of_terminal_eq_of_globalWords_eq
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (left right : SlabObservableTwoReplicaPair D rootFaceId)
    (hleft : left ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (hright : right ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId)
    (massBudget : Nat)
    (hterminal :
      (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget left hleft).1 =
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget right hright).1)
    (hshape :
      slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalShapeCode
          D rootFaceId targetFaceId htarget right hright massBudget)
    (hvalues :
      slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
          D rootFaceId targetFaceId htarget left hleft massBudget =
        slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues
          D rootFaceId targetFaceId htarget right hright massBudget) :
    left.1.1.1 = right.1.1.1 ∧ left.2.1.1 = right.2.1.1 := by
  have hcomponent :=
    slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_eq_component_mem
      D rootFaceId targetFaceId htarget left right hleft hright
      massBudget hshape
  constructor
  · funext faceId
    by_cases hface : faceId ∈
        slabTwoReplicaTargetSupportComponent D.extent
          left.1.1.1 left.2.1.1 targetFaceId
    · exact
        (slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues_eq_on_component
          D rootFaceId targetFaceId htarget left right hleft hright
          massBudget hshape hvalues faceId hface).1
    · have hrightOutside : faceId ∉
          slabTwoReplicaTargetSupportComponent D.extent
            right.1.1.1 right.2.1.1 targetFaceId := by
        intro hrightFace
        exact hface ((hcomponent faceId).2 hrightFace)
      have hleftLocal :=
        slabObservablePairTargetSupportCanonicalPeeling_final_physical_eq_outside
          D rootFaceId targetFaceId htarget left hleft faceId hface
      have hrightLocal :=
        slabObservablePairTargetSupportCanonicalPeeling_final_physical_eq_outside
          D rootFaceId targetFaceId htarget right hright faceId hrightOutside
      have hterminalAt := congrArg
        (fun state => state.1.1.1 faceId) hterminal
      exact hleftLocal.1.symm.trans (hterminalAt.trans hrightLocal.1)
  · funext faceId
    by_cases hface : faceId ∈
        slabTwoReplicaTargetSupportComponent D.extent
          left.1.1.1 left.2.1.1 targetFaceId
    · exact
        (slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues_eq_on_component
          D rootFaceId targetFaceId htarget left right hleft hright
          massBudget hshape hvalues faceId hface).2
    · have hrightOutside : faceId ∉
          slabTwoReplicaTargetSupportComponent D.extent
            right.1.1.1 right.2.1.1 targetFaceId := by
        intro hrightFace
        exact hface ((hcomponent faceId).2 hrightFace)
      have hleftLocal :=
        slabObservablePairTargetSupportCanonicalPeeling_final_physical_eq_outside
          D rootFaceId targetFaceId htarget left hleft faceId hface
      have hrightLocal :=
        slabObservablePairTargetSupportCanonicalPeeling_final_physical_eq_outside
          D rootFaceId targetFaceId htarget right hright faceId hrightOutside
      have hterminalAt := congrArg
        (fun state => state.2.1.1 faceId) hterminal
      exact hleftLocal.2.symm.trans (hterminalAt.trans hrightLocal.2)

end YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalReconstruction

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalReconstruction.slabObservableTwoReplicaPairTargetSupportGlobalFaceIds_cover_component
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalReconstruction.slabObservableTwoReplicaPairTargetSupportGlobalPhysicalValues_eq_on_component
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalReconstruction.slabObservableTwoReplicaPairTargetSupportGlobalShapeCode_eq_component_mem
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPhysicalReconstruction.slabObservablePair_sourcePhysical_eq_of_terminal_eq_of_globalWords_eq
