/-
# Canonical consecutive-cutoff pair recodings for the support-aware BF4 debt

The dynamic-extrema compiler accepts explicit maps in both directions between
consecutive finite vacuum-sector pair lists.  On the canonical proof path
these maps are not analytic inputs.

The current-to-next map applies the already proved physical cutoff index
embedding to both coordinates.  The later-to-current map constructively
searches the current vacuum component for a preimage of each later index and
uses the vacuum index as a total fallback on the genuinely new shell.  The
search is a left inverse on the embedded old component because the physical
cutoff index map is injective there.

This module installs those geometric maps in the load-maximum and
kernel-minimum variation interfaces.  The remaining inputs are only the
summable pointwise inequalities along these fixed maps and the independent
uniform kernel floor.  No such analytic estimate is inhabited here.

The fixed anchor is not the physical AF trajectory, and no thermodynamic,
continuum, or Clay conclusion is asserted.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. A constructive preimage search with a total fallback -/

/-- Search a finite list for the first item mapped to `target`; return the
explicit fallback when the target has no preimage. -/
def firstMappedPreimageOr
    (map : Nat -> Nat) (fallback target : Nat) : List Nat -> Nat
  | [] => fallback
  | head :: tail =>
      if map head = target then head
      else firstMappedPreimageOr map fallback target tail

theorem firstMappedPreimageOr_mem_or_eq_fallback
    (map : Nat -> Nat) (fallback target : Nat) :
    forall items : List Nat,
      firstMappedPreimageOr map fallback target items ∈ items \/
        firstMappedPreimageOr map fallback target items = fallback
  | [] => Or.inr rfl
  | head :: tail => by
      by_cases hhead : map head = target
      · simp only [firstMappedPreimageOr, hhead, if_true]
        exact Or.inl List.mem_cons_self
      · simp only [firstMappedPreimageOr, hhead, if_false]
        rcases firstMappedPreimageOr_mem_or_eq_fallback
            map fallback target tail with hmem | hfallback
        · exact Or.inl (List.mem_cons_of_mem head hmem)
        · exact Or.inr hfallback

theorem firstMappedPreimageOr_mem
    (map : Nat -> Nat) (fallback target : Nat) (items : List Nat)
    (hfallback : fallback ∈ items) :
    firstMappedPreimageOr map fallback target items ∈ items := by
  rcases firstMappedPreimageOr_mem_or_eq_fallback
      map fallback target items with hmem | heq
  · exact hmem
  · rw [heq]
    exact hfallback

theorem map_firstMappedPreimageOr_eq_of_mem_map
    (map : Nat -> Nat) (fallback target : Nat) :
    forall items : List Nat,
      target ∈ items.map map ->
        map (firstMappedPreimageOr map fallback target items) = target
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hmem => by
      by_cases hhead : map head = target
      · simp only [firstMappedPreimageOr, hhead, if_true]
      · simp only [firstMappedPreimageOr, hhead, if_false]
        apply map_firstMappedPreimageOr_eq_of_mem_map
        simp only [List.map_cons, List.mem_cons] at hmem
        rcases hmem with htargetHead | htargetTail
        · exact False.elim (hhead htargetHead.symm)
        · exact htargetTail

/-! ## 2. Canonical consecutive index and pair maps -/

def anchorCurrentIndexToNext (scale index : Nat) : Nat :=
  centralPhysicalFiniteCutoffIndexMap
    anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
    scale (scale + 1) 0 index

def anchorNextIndexToCurrent (scale index : Nat) : Nat :=
  firstMappedPreimageOr
    (anchorCurrentIndexToNext scale) 0 index
    (centralPhysicalFiniteVacuumSectorIndices
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos) scale 0)

theorem anchorCurrentIndexToNext_mem
    (scale index : Nat)
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos) scale 0) :
    anchorCurrentIndexToNext scale index ∈
      centralPhysicalFiniteVacuumSectorIndices
        anchorCoupling (Q'.le_of_lt anchorCoupling_pos) (scale + 1) 0 := by
  exact centralPhysicalFiniteVacuumSectorIndexMap_mem
    (Nat.le_succ scale) hindex

theorem anchorNextIndexToCurrent_mem
    (scale index : Nat) :
    anchorNextIndexToCurrent scale index ∈
      centralPhysicalFiniteVacuumSectorIndices
        anchorCoupling (Q'.le_of_lt anchorCoupling_pos) scale 0 := by
  unfold anchorNextIndexToCurrent
  exact firstMappedPreimageOr_mem _ 0 index _
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos) scale 0)

/-- On the embedded old component the later-to-current search is a literal
left inverse of the physical cutoff embedding. -/
theorem anchorNextIndexToCurrent_currentToNext
    (scale index : Nat)
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos) scale 0) :
    anchorNextIndexToCurrent scale
        (anchorCurrentIndexToNext scale index) = index := by
  have htargetMap : anchorCurrentIndexToNext scale index ∈
      (centralPhysicalFiniteVacuumSectorIndices
        anchorCoupling (Q'.le_of_lt anchorCoupling_pos) scale 0).map
          (anchorCurrentIndexToNext scale) :=
    List.mem_map.mpr ⟨index, hindex, rfl⟩
  have hmap := map_firstMappedPreimageOr_eq_of_mem_map
    (anchorCurrentIndexToNext scale) 0
    (anchorCurrentIndexToNext scale index)
    (centralPhysicalFiniteVacuumSectorIndices
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos) scale 0)
    htargetMap
  apply centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector
    (Nat.le_succ scale)
    (anchorNextIndexToCurrent_mem scale
      (anchorCurrentIndexToNext scale index))
    hindex
  exact hmap

def anchorCurrentPairToNext (scale : Nat) (pair : Nat × Nat) : Nat × Nat :=
  (anchorCurrentIndexToNext scale pair.1,
    anchorCurrentIndexToNext scale pair.2)

def anchorNextPairToCurrent (scale : Nat) (pair : Nat × Nat) : Nat × Nat :=
  (anchorNextIndexToCurrent scale pair.1,
    anchorNextIndexToCurrent scale pair.2)

theorem anchorCurrentPairToNext_mem
    (scale : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ anchorVacuumSectorPairs scale) :
    anchorCurrentPairToNext scale pair ∈
      anchorVacuumSectorPairs (scale + 1) := by
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  exact (mem_cartesian_iff _ _ _).mpr
    ⟨anchorCurrentIndexToNext_mem scale pair.1 hmembers.1,
      anchorCurrentIndexToNext_mem scale pair.2 hmembers.2⟩

theorem anchorNextPairToCurrent_mem
    (scale : Nat) (pair : Nat × Nat) :
    anchorNextPairToCurrent scale pair ∈ anchorVacuumSectorPairs scale := by
  exact (mem_cartesian_iff _ _ _).mpr
    ⟨anchorNextIndexToCurrent_mem scale pair.1,
      anchorNextIndexToCurrent_mem scale pair.2⟩

theorem anchorNextPairToCurrent_currentToNext
    (scale : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ anchorVacuumSectorPairs scale) :
    anchorNextPairToCurrent scale (anchorCurrentPairToNext scale pair) =
      pair := by
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  apply Prod.ext
  · exact anchorNextIndexToCurrent_currentToNext
      scale pair.1 hmembers.1
  · exact anchorNextIndexToCurrent_currentToNext
      scale pair.2 hmembers.2

/-! ## 3. The remaining canonical analytic envelopes -/

/-- With the canonical pair maps fixed, load variation reduces to two literal
pointwise inequalities and their summable budget. -/
structure AnchorCanonicalRoutedLoadEnvelope : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall scale, (0 : Q') <= variation scale
  tailControl : AntitoneTailControl variation
  current_le_next : forall scale pair,
    pair ∈ anchorVacuumSectorPairs scale ->
      anchorRoutedLoadOnPair anchorCanonicalPositiveRoutingSequence scale pair <=
        anchorRoutedLoadOnPair anchorCanonicalPositiveRoutingSequence
          (scale + 1) (anchorCurrentPairToNext scale pair) + variation scale
  next_le_current : forall scale pair,
    pair ∈ anchorVacuumSectorPairs (scale + 1) ->
      anchorRoutedLoadOnPair anchorCanonicalPositiveRoutingSequence
          (scale + 1) pair <=
        anchorRoutedLoadOnPair anchorCanonicalPositiveRoutingSequence scale
          (anchorNextPairToCurrent scale pair) + variation scale

/-- With the same canonical pair maps fixed, kernel-minimum variation reduces
to the dual two pointwise inequalities and their summable budget. -/
structure AnchorCanonicalSupportedKernelEnvelope : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall scale, (0 : Q') <= variation scale
  tailControl : AntitoneTailControl variation
  next_le_current : forall scale pair,
    pair ∈ anchorVacuumSectorPairs scale ->
      anchorSupportedKernelCandidateOnPair
          anchorCanonicalPositiveRoutingSequence
          (scale + 1) (anchorCurrentPairToNext scale pair) <=
        anchorSupportedKernelCandidateOnPair
          anchorCanonicalPositiveRoutingSequence scale pair + variation scale
  current_le_next : forall scale pair,
    pair ∈ anchorVacuumSectorPairs (scale + 1) ->
      anchorSupportedKernelCandidateOnPair
          anchorCanonicalPositiveRoutingSequence scale
          (anchorNextPairToCurrent scale pair) <=
        anchorSupportedKernelCandidateOnPair
          anchorCanonicalPositiveRoutingSequence (scale + 1) pair +
            variation scale

def AnchorCanonicalRoutedLoadEnvelope.toMaximumVariation
    (data : AnchorCanonicalRoutedLoadEnvelope) :
    AnchorAdaptiveRoutedLoadMaximumVariation
      anchorCanonicalPositiveRoutingSequence where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  value_nonnegative := fun scale pair hpair => by
    have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
    exact
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_nonnegative
        (anchorCanonicalPositiveRoutingSequence scale) hmembers.1 pair.2
  currentToNext := anchorCurrentPairToNext
  currentToNext_mem := anchorCurrentPairToNext_mem
  current_le_next := data.current_le_next
  nextToCurrent := anchorNextPairToCurrent
  nextToCurrent_mem := fun scale pair _ =>
    anchorNextPairToCurrent_mem scale pair
  next_le_current := data.next_le_current

def AnchorCanonicalSupportedKernelEnvelope.toMinimumVariation
    (data : AnchorCanonicalSupportedKernelEnvelope) :
    AnchorAdaptiveSupportedKernelMinimumVariation
      anchorCanonicalPositiveRoutingSequence where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  currentToNext := anchorCurrentPairToNext
  currentToNext_mem := anchorCurrentPairToNext_mem
  next_le_current := data.next_le_current
  nextToCurrent := anchorNextPairToCurrent
  nextToCurrent_mem := fun scale pair _ =>
    anchorNextPairToCurrent_mem scale pair
  current_le_next := data.current_le_next

/-- Canonical geometric recodings are now internal.  The remaining three
parallel analytic producers are the load envelope, kernel envelope, and
uniform pointwise kernel floor. -/
def anchorCanonicalSupportCapacityDebtVariationOfEnvelopes
    (load : AnchorCanonicalRoutedLoadEnvelope)
    (kernel : AnchorCanonicalSupportedKernelEnvelope)
    (kernelFloor : AnchorAdaptiveSupportedKernelMinimumFloor
      anchorCanonicalPositiveRoutingSequence) :
    SummableRationalStepVariation
      (anchorAdaptiveSupportCapacityDebt
        anchorCanonicalPositiveRoutingSequence) :=
  anchorCanonicalSupportCapacityDebtVariationOfPointwise
    load.toMaximumVariation kernel.toMinimumVariation kernelFloor

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding.firstMappedPreimageOr_mem
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding.map_firstMappedPreimageOr_eq_of_mem_map
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding.anchorCurrentPairToNext_mem
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding.anchorNextPairToCurrent_mem
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding.anchorNextPairToCurrent_currentToNext
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding.AnchorCanonicalRoutedLoadEnvelope.toMaximumVariation
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding.AnchorCanonicalSupportedKernelEnvelope.toMinimumVariation
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding.anchorCanonicalSupportCapacityDebtVariationOfEnvelopes
