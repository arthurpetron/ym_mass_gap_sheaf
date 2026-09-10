/-
# Genuine Z4 geometry of the surviving tilted-Gibbs response

Exact component-swap cancellation leaves only active target pairs for which
the observable-rooted union-support component reaches a source-disagreement
face.  The certificate produced so far is a chain on numerical slab-face
identifiers.  This file compiles that chain to the actual four-dimensional
plaquette lattice.

The deduplicated image of the whole observable-rooted support component is a
genuine finite Z4 lattice animal.  It contains both the observable plaquette
and the selected disagreement plaquette.  Consequently its cardinality is at
least their L-infinity separation plus one.  This is the geometric activity
floor needed before a connected activity-versus-entropy estimate can be
stated.

No weight estimate, coupling-uniform contraction, completed spectral gap,
continuum construction, or mass gap is asserted here.

Constructive contract: finite Boolean graph paths, explicit slab-link
incidence, and genuine Z4 lattice animals only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedCancellation
import YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Continuum.AdjSpanningBuild
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedGeometry
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private def positiveEitherOfNatNe
    (left right : Nat) (hne : left ≠ right) :
    0 < left ∨ 0 < right := by
  cases left with
  | zero =>
      cases right with
      | zero => exact False.elim (hne rfl)
      | succ value => exact Or.inr (Nat.zero_lt_succ value)
  | succ value => exact Or.inl (Nat.zero_lt_succ value)

/-! ## 1. The geometric image of an arbitrary target-pair component -/

/-- The genuine plaquettes in the target-pair union-support component rooted
at the observable face. -/
def finePacketObservableTargetSupportPlaquettes
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat) : List Z4Plaq :=
  ((slabTwoReplicaTargetSupportComponent S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId).map
        (slabPlaquetteAt S.coarse.extent)).eraseDups

private theorem filteredEraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) :
    ∀ predicate : A → Bool, (items.filter predicate).eraseDups.Nodup := by
  induction items with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail ih =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr ⟨?_, ih _⟩
        intro hmem
        have hfiltered := List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hfiltered).2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact ih _

private theorem filterTrueLocal {A : Type} :
    ∀ items : List A, items.filter (fun _ => true) = items
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (filterTrueLocal tail)

private theorem eraseDupsNodupLocal {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) : items.eraseDups.Nodup := by
  have h := filteredEraseDupsNodupLocal items (fun _ => true)
  rw [filterTrueLocal] at h
  exact h

theorem finePacketObservableTargetSupportPlaquettes_nodup
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat) :
    (finePacketObservableTargetSupportPlaquettes
      S targetPair observableFaceId).Nodup := by
  unfold finePacketObservableTargetSupportPlaquettes
  exact eraseDupsNodupLocal _

theorem slabPlaquetteAt_mem_finePacketObservableTargetSupportPlaquettes
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId faceId : Nat)
    (hface : faceId ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId) :
    slabPlaquetteAt S.coarse.extent faceId ∈
      finePacketObservableTargetSupportPlaquettes
        S targetPair observableFaceId := by
  unfold finePacketObservableTargetSupportPlaquettes
  exact List.mem_eraseDups.mpr
    (List.mem_map.mpr ⟨faceId, hface, rfl⟩)

/-! ## 2. Compile component chains to genuine plaquette chains -/

/-- Numerical support-component chains map step-by-step to actual Z4
plaquette chains.  Every adjacency is witnessed by the same physical slab
link. -/
def finePacketTargetSupportChainToPlaquetteChain
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat) :
    {left right : Nat} →
      FiniteBoolGraphComponents.ChainIn
        (slabSupportFaceAdjacentB S.coarse.extent)
        (slabTwoReplicaTargetSupportComponent S.coarse.extent
          targetPair.1 targetPair.2 observableFaceId)
        left right →
      PolymerModel.ChainIn z4Chain.toLattice
        (finePacketObservableTargetSupportPlaquettes
          S targetPair observableFaceId)
        (slabPlaquetteAt S.coarse.extent left)
        (slabPlaquetteAt S.coarse.extent right)
  | _, _, FiniteBoolGraphComponents.ChainIn.refl face =>
      PolymerModel.ChainIn.refl _
  | _left, _right,
      FiniteBoolGraphComponents.ChainIn.step
        (b := next) hadj hnext rest =>
      PolymerModel.ChainIn.step
        (slabSupportFaceAdjacentToPlaquetteAdjacent hadj)
        (slabPlaquetteAt_mem_finePacketObservableTargetSupportPlaquettes
          S targetPair observableFaceId next hnext)
        (finePacketTargetSupportChainToPlaquetteChain
          S targetPair observableFaceId rest)

/-- The already-constructed connected response certificate therefore carries
an actual Z4 plaquette path from the observable to its selected source
disagreement. -/
def finePacketObservableConnectedDisagreementGeometricPath
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (path : FinePacketObservableConnectedDisagreementPath
      S first second observableFaceId targetPair) :
    PolymerModel.ChainIn z4Chain.toLattice
      (finePacketObservableTargetSupportPlaquettes
        S targetPair observableFaceId)
      (slabPlaquetteAt S.coarse.extent observableFaceId)
      (slabPlaquetteAt S.coarse.extent path.sourceFaceId) :=
  finePacketTargetSupportChainToPlaquetteChain
    S targetPair observableFaceId path.coarsePath

/-! ## 3. The whole component is a genuine finite lattice animal -/

/-- A computational face preimage for each plaquette in the component image,
with the observable face as total fallback. -/
def finePacketObservableTargetSupportFaceValue
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat) (plaquette : Z4Plaq) : Nat :=
  listFirstMappedPreimageOr
    (slabPlaquetteAt S.coarse.extent) observableFaceId plaquette
    (slabTwoReplicaTargetSupportComponent S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId)

theorem finePacketObservableTargetSupportFaceValue_mem
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableComponent : observableFaceId ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId)
    (plaquette : Z4Plaq) :
    finePacketObservableTargetSupportFaceValue
        S targetPair observableFaceId plaquette ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId := by
  rcases listFirstMappedPreimageOr_mem_or_eq_fallback
      (slabPlaquetteAt S.coarse.extent) observableFaceId plaquette
      (slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId) with hmem | hfallback
  · exact hmem
  · unfold finePacketObservableTargetSupportFaceValue
    rw [hfallback]
    exact hobservableComponent

theorem finePacketObservableTargetSupportFaceValue_projection
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat) (plaquette : Z4Plaq)
    (hplaquette : plaquette ∈
      finePacketObservableTargetSupportPlaquettes
        S targetPair observableFaceId) :
    slabPlaquetteAt S.coarse.extent
        (finePacketObservableTargetSupportFaceValue
          S targetPair observableFaceId plaquette) = plaquette := by
  exact listFirstMappedPreimageOr_projection
    (slabPlaquetteAt S.coarse.extent) observableFaceId plaquette
    (slabTwoReplicaTargetSupportComponent S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId)
    (List.mem_eraseDups.mp hplaquette)

/-- The deduplicated observable-rooted component is internally connected in
the genuine Z4 plaquette lattice. -/
def finePacketObservableTargetSupportPlaquettes_connected
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hobservableNe :
      targetPair.1 observableFaceId ≠ targetPair.2 observableFaceId) :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      (finePacketObservableTargetSupportPlaquettes
        S targetPair observableFaceId) := by
  intro leftPlaquette rightPlaquette hleft hright
  let left := finePacketObservableTargetSupportFaceValue
    S targetPair observableFaceId leftPlaquette
  let right := finePacketObservableTargetSupportFaceValue
    S targetPair observableFaceId rightPlaquette
  have hobservableVertex : observableFaceId ∈
      slabTwoReplicaSupportFaceVertices S.coarse.extent
        targetPair.1 targetPair.2 := by
    apply mem_slabTwoReplicaSupportFaceVertices hobservableFace
    exact positiveEitherOfNatNe _ _ hobservableNe
  have hobservableComponent : observableFaceId ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId := by
    exact root_mem_rootComponent
      (slabSupportFaceAdjacentB S.coarse.extent) hobservableVertex
  have hleftComponent : left ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId :=
    finePacketObservableTargetSupportFaceValue_mem
      S targetPair observableFaceId hobservableComponent leftPlaquette
  have hrightComponent : right ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId :=
    finePacketObservableTargetSupportFaceValue_mem
      S targetPair observableFaceId hobservableComponent rightPlaquette
  have hfaces := rootComponent_connected
    (slabSupportFaceAdjacentB S.coarse.extent)
    (slabSupportFaceAdjacentB_symmetric S.coarse.extent)
    hobservableVertex left right hleftComponent hrightComponent
  have hprojected := finePacketTargetSupportChainToPlaquetteChain
    S targetPair observableFaceId hfaces
  have hleftEq : slabPlaquetteAt S.coarse.extent left = leftPlaquette := by
    exact finePacketObservableTargetSupportFaceValue_projection
      S targetPair observableFaceId leftPlaquette hleft
  have hrightEq : slabPlaquetteAt S.coarse.extent right = rightPlaquette := by
    exact finePacketObservableTargetSupportFaceValue_projection
      S targetPair observableFaceId rightPlaquette hright
  rw [hleftEq, hrightEq] at hprojected
  exact hprojected

/-- The target-pair component is a genuine finite Z4 lattice animal rooted at
the observable plaquette. -/
theorem finePacketObservableTargetSupportAnimal
    (S : SlabScalePair) (targetPair : EdgeLabelling × EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hobservableNe :
      targetPair.1 observableFaceId ≠ targetPair.2 observableFaceId) :
    IsClusterThroughIn z4Chain
      (slabPlaquetteAt S.coarse.extent observableFaceId)
      (finePacketObservableTargetSupportPlaquettes
        S targetPair observableFaceId).length
      (finePacketObservableTargetSupportPlaquettes
        S targetPair observableFaceId) := by
  have hobservableVertex : observableFaceId ∈
      slabTwoReplicaSupportFaceVertices S.coarse.extent
        targetPair.1 targetPair.2 := by
    apply mem_slabTwoReplicaSupportFaceVertices hobservableFace
    exact positiveEitherOfNatNe _ _ hobservableNe
  have hobservableComponent : observableFaceId ∈
      slabTwoReplicaTargetSupportComponent S.coarse.extent
        targetPair.1 targetPair.2 observableFaceId := by
    exact root_mem_rootComponent
      (slabSupportFaceAdjacentB S.coarse.extent) hobservableVertex
  exact ⟨rfl,
    slabPlaquetteAt_mem_finePacketObservableTargetSupportPlaquettes
      S targetPair observableFaceId observableFaceId hobservableComponent,
    finePacketObservableTargetSupportPlaquettes_nodup
      S targetPair observableFaceId,
    ⟨finePacketObservableTargetSupportPlaquettes_connected
      S targetPair observableFaceId hobservableFace hobservableNe⟩⟩

/-! ## 4. Connected response pairs pay geometric activity -/

/-- **Geometric activity floor for the surviving response.**  The actual
target-pair support animal contains at least one distinct plaquette per unit
of observable-to-source-disagreement L-infinity distance, including the
initial plaquette. -/
theorem finePacketObservableConnectedDisagreementPath_size_floor
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (path : FinePacketObservableConnectedDisagreementPath
      S first second observableFaceId targetPair) :
    linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1 ≤
      (finePacketObservableTargetSupportPlaquettes
        S targetPair observableFaceId).length := by
  let support := finePacketObservableTargetSupportPlaquettes
    S targetPair observableFaceId
  obtain ⟨animal, hanimal, hsame⟩ :=
    (z4ClusterCountBound_animal
      (slabPlaquetteAt S.coarse.extent observableFaceId)).2
      support.length support
      (finePacketObservableTargetSupportAnimal
        S targetPair observableFaceId hobservableFace
          path.observable_targetStates_ne)
  have hsourceSupport :
      slabPlaquetteAt S.coarse.extent path.sourceFaceId ∈ support :=
    slabPlaquetteAt_mem_finePacketObservableTargetSupportPlaquettes
      S targetPair observableFaceId path.sourceFaceId
        path.source_mem_targetComponent
  have hsourceAnimal :
      slabPlaquetteAt S.coarse.extent path.sourceFaceId ∈ animal :=
    hsame.1 _ hsourceSupport
  have hfloor := enum_linf_reach_floor
    (slabPlaquetteAt S.coarse.extent observableFaceId)
    support.length animal hanimal
    (slabPlaquetteAt S.coarse.extent path.sourceFaceId) hsourceAnimal
    (linfDist
      (slabPlaquetteAt S.coarse.extent observableFaceId)
      (slabPlaquetteAt S.coarse.extent path.sourceFaceId))
    (Nat.le_refl _)
  have hsupportNodup : support.Nodup :=
    finePacketObservableTargetSupportPlaquettes_nodup
      S targetPair observableFaceId
  have hanimalNodup : animal.Nodup :=
    enumPoly_nodup z4Chain
      (slabPlaquetteAt S.coarse.extent observableFaceId)
      support.length hanimal
  have hlength : animal.length = support.length :=
    (sameSupport_length_eq_of_nodup
      hsame hsupportNodup hanimalNodup).symm
  rw [hlength] at hfloor
  exact hfloor

/-- Membership in the exact connected active-pair sum computes the geometric
path and its activity floor. -/
theorem finePacketFaceResponseConnectedActivePair_size_floor
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hpair : targetPair ∈ finePacketFaceResponseConnectedActivePairs
      S first second observableFaceId) :
    let path := finePacketFaceResponseConnectedActivePairPath
      S first second observableFaceId hobservableFace targetPair hpair
    linfDist
          (slabPlaquetteAt S.coarse.extent observableFaceId)
          (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1 ≤
      (finePacketObservableTargetSupportPlaquettes
        S targetPair observableFaceId).length := by
  exact finePacketObservableConnectedDisagreementPath_size_floor
    S first second observableFaceId hobservableFace targetPair
      (finePacketFaceResponseConnectedActivePairPath
        S first second observableFaceId hobservableFace targetPair hpair)

/-! ## 5. Axiom audit -/

#print axioms finePacketObservableTargetSupportPlaquettes
#print axioms finePacketTargetSupportChainToPlaquetteChain
#print axioms finePacketObservableConnectedDisagreementGeometricPath
#print axioms finePacketObservableTargetSupportPlaquettes_connected
#print axioms finePacketObservableTargetSupportAnimal
#print axioms finePacketObservableConnectedDisagreementPath_size_floor
#print axioms finePacketFaceResponseConnectedActivePair_size_floor

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry
