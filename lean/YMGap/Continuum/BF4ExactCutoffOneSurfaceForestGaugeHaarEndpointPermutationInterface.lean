/-
# Opaque interface to the checked BF4 Haar endpoint permutations

The executable permutation certificates are expensive to reduce but cheap to
use.  This module bundles each checked swap list with its semantic theorem
behind an opaque interface, preventing downstream elaboration from unfolding
the selection program again.

## Axiom gate

Constructive structure packaging only.  No `Classical.*`, `native_decide`,
`sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutation

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutationInterface

open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutation
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation
open YMGap.Continuum.BF4ExactSpatialTreeGaugeRawCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection

/-- Opaque downstream handle for the fixed physical-to-active block
permutation and its exact source-coordinate action. -/
structure PhysicalToActiveSwapCertificate : Type where
  steps : List (QuaternionBlockInvolution 32)
  coordinate : ∀ edgeId, edgeId < 32 →
    quaternionBlockSwapChainSource steps (surfaceActiveBlock edgeId) = edgeId

opaque physicalToActiveSwapCertificate :
    PhysicalToActiveSwapCertificate :=
  ⟨physicalToActiveSteps, physicalToActive_coordinate⟩

/-- Opaque downstream handle for every checked mask-dependent chord-prefix
permutation. -/
structure SurfaceChordCarrierSwapCertificate : Type where
  steps : ∀ mask, mask ∈ binarySurfaceMasks →
    List (QuaternionBlockInvolution 32)
  sourceOrder : ∀ mask (hmask : mask ∈ binarySurfaceMasks),
    (List.range 32).map
        (quaternionBlockSwapChainSource (steps mask hmask)) =
      surfaceChordCarrierSourceOrder mask

opaque surfaceChordCarrierSwapCertificate :
    SurfaceChordCarrierSwapCertificate :=
  ⟨surfaceChordCarrierSteps, surfaceChordCarrier_source_order⟩

private theorem getD_map_of_lt
    (map : α → β) (source : List α) (index : Nat)
    (hindex : index < source.length) (sourceFallback : α)
    (targetFallback : β) :
    (source.map map).getD index targetFallback =
      map (source.getD index sourceFallback) := by
  induction source generalizing index with
  | nil => simp at hindex
  | cons head tail induction =>
      cases index with
      | zero => simp
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hindex
          simpa using induction index hindex

private theorem getD_append_left_of_lt
    (left right : List α) (index : Nat) (fallback : α)
    (hindex : index < left.length) :
    (left ++ right).getD index fallback = left.getD index fallback := by
  induction left generalizing index with
  | nil => simp at hindex
  | cons head tail induction =>
      cases index with
      | zero => simp
      | succ index =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hindex
          simpa using induction index hindex

private theorem getD_range_of_lt
    (bound index : Nat) (hindex : index < bound) :
    (List.range bound).getD index 0 = index := by
  have hget := List.getElem_eq_getD
    (l := List.range bound) (i := index)
    (h := by simpa using hindex) 0
  rw [← hget]
  simp

private theorem getD_idxOf_of_mem
    (target fallback : Nat) (items : List Nat)
    (hmem : target ∈ items) :
    items.getD (items.idxOf target) fallback = target := by
  have hlt := List.idxOf_lt_length_of_mem hmem
  have hfound : items[items.idxOf target] == target := by
    exact List.findIdx_getElem (w := hlt)
  have heq : items[items.idxOf target] = target :=
    LawfulBEq.eq_of_beq hfound
  have hget := List.getElem_eq_getD
    (l := items) (i := items.idxOf target) (h := hlt) fallback
  rw [← hget]
  exact heq

theorem surfaceChordCarrier_length_le
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    (surfaceForestGaugeChordEdgeIds mask).length ≤ 32 := by
  have hlength := congrArg List.length
    (surfaceChordCarrierSwapCertificate.sourceOrder mask hmask)
  simp [surfaceChordCarrierSourceOrder] at hlength
  omega

/-- Coordinate form of the checked chord-prefix source order. -/
theorem surfaceChordCarrier_coordinate
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (edgeId : Nat) (hedge : edgeId ∈ surfaceForestGaugeChordEdgeIds mask) :
    let target := natListIndexOf edgeId (surfaceForestGaugeChordEdgeIds mask)
    target < 32 ∧
      quaternionBlockSwapChainSource
        (surfaceChordCarrierSwapCertificate.steps mask hmask) target = edgeId := by
  let chords := surfaceForestGaugeChordEdgeIds mask
  let target := natListIndexOf edgeId chords
  have htargetChord : target < chords.length :=
    natListIndexOf_lt_length_of_mem edgeId chords hedge
  have htarget : target < 32 :=
    Nat.lt_of_lt_of_le htargetChord
      (surfaceChordCarrier_length_le mask hmask)
  constructor
  · exact htarget
  · have horder :=
      surfaceChordCarrierSwapCertificate.sourceOrder mask hmask
    have hget :
        ((List.range 32).map
          (quaternionBlockSwapChainSource
            (surfaceChordCarrierSwapCertificate.steps mask hmask))).getD
            target 0 =
          (surfaceChordCarrierSourceOrder mask).getD target 0 :=
      congrArg (fun items => items.getD target 0) horder
    rw [getD_map_of_lt _ _ _ (by simpa using htarget) 0 0,
      getD_range_of_lt 32 target htarget,
      show surfaceChordCarrierSourceOrder mask =
          chords ++ (List.range 32).filter (fun edgeId =>
            decide (edgeId ∉ chords)) by
        rfl,
      getD_append_left_of_lt chords _ target 0 htargetChord,
      getD_natListIndexOf_of_mem edgeId 0 chords hedge] at hget
    exact hget

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeHaarEndpointPermutationInterface
