/-
# Canonical pair recodings on the matched eventual tail

The matched pointwise variation compiler accepts maps in both directions
between consecutive finite vacuum-sector pair carriers.  On the canonical
proof path those maps are geometric data, not analytic hypotheses.

At one physical scale, the current-to-next map applies the existing physical
cutoff embedding at cutoffs `transitionStart scale + offset` and its successor.
The later-to-current map constructively searches the current finite vacuum
component for a preimage and uses the vacuum index as a total fallback on the
new shell.  The search is a left inverse on the embedded old component.

This module installs those maps in the exact matched load-maximum and
kernel-minimum interfaces.  The remaining separated-route inputs are only two
summable pointwise envelopes and the independent uniform kernel floor.  No
analytic envelope or floor is inhabited here.  No persistence, continuum
Yang--Mills theory, or Clay conclusion is asserted.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariation

/-! ## 1. Constructive matched consecutive index maps -/

/-- Embed one index from the current matched cutoff into the next cutoff. -/
def matchedEventualCanonicalCurrentIndexToNext
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset index : Nat) : Nat :=
  centralPhysicalFiniteCutoffIndexMap
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (transitionStart physicalScale + offset)
    ((transitionStart physicalScale + offset) + 1)
    0 index

/-- Search the current matched vacuum component for a preimage of a next-
cutoff index, with the vacuum index as explicit fallback on the new shell. -/
def matchedEventualCanonicalNextIndexToCurrent
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset index : Nat) : Nat :=
  firstMappedPreimageOr
    (matchedEventualCanonicalCurrentIndexToNext
      trajectory transitionStart physicalScale offset)
    0 index
    (centralPhysicalFiniteVacuumSectorIndices
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + offset) 0)

theorem matchedEventualCanonicalCurrentIndexToNext_mem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset index : Nat)
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + offset) 0) :
    matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale offset index ∈
      centralPhysicalFiniteVacuumSectorIndices
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (offset + 1)) 0 := by
  have hmem := centralPhysicalFiniteVacuumSectorIndexMap_mem
    (w := trajectory.nome physicalScale)
    (hw := Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (base := transitionStart physicalScale + offset)
    (later := (transitionStart physicalScale + offset) + 1)
    (half := 0)
    (index := index)
    (Nat.le_succ (transitionStart physicalScale + offset)) hindex
  simpa only [matchedEventualCanonicalCurrentIndexToNext, Nat.add_assoc]
    using hmem

theorem matchedEventualCanonicalNextIndexToCurrent_mem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset index : Nat) :
    matchedEventualCanonicalNextIndexToCurrent
        trajectory transitionStart physicalScale offset index ∈
      centralPhysicalFiniteVacuumSectorIndices
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + offset) 0 := by
  unfold matchedEventualCanonicalNextIndexToCurrent
  exact firstMappedPreimageOr_mem _ 0 index _
    (zero_mem_centralPhysicalFiniteVacuumSectorIndices
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + offset) 0)

/-- On the embedded old component, preimage search is a literal left inverse
of the matched physical cutoff embedding. -/
theorem matchedEventualCanonicalNextIndexToCurrent_currentToNext
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset index : Nat)
    (hindex : index ∈ centralPhysicalFiniteVacuumSectorIndices
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + offset) 0) :
    matchedEventualCanonicalNextIndexToCurrent
        trajectory transitionStart physicalScale offset
        (matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale offset index) =
      index := by
  have htargetMap :
      matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale offset index ∈
        (centralPhysicalFiniteVacuumSectorIndices
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + offset) 0).map
            (matchedEventualCanonicalCurrentIndexToNext
              trajectory transitionStart physicalScale offset) :=
    List.mem_map.mpr ⟨index, hindex, rfl⟩
  have hmap := map_firstMappedPreimageOr_eq_of_mem_map
    (matchedEventualCanonicalCurrentIndexToNext
      trajectory transitionStart physicalScale offset)
    0
    (matchedEventualCanonicalCurrentIndexToNext
      trajectory transitionStart physicalScale offset index)
    (centralPhysicalFiniteVacuumSectorIndices
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + offset) 0)
    htargetMap
  apply centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector
    (w := trajectory.nome physicalScale)
    (hw := Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (base := transitionStart physicalScale + offset)
    (later := (transitionStart physicalScale + offset) + 1)
    (half := 0)
    (left := matchedEventualCanonicalNextIndexToCurrent
      trajectory transitionStart physicalScale offset
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale offset index))
    (right := index)
    (Nat.le_succ (transitionStart physicalScale + offset))
    (matchedEventualCanonicalNextIndexToCurrent_mem
      trajectory transitionStart physicalScale offset
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale offset index))
    hindex
  exact hmap

/-! ## 2. Matched consecutive pair maps -/

def matchedEventualCanonicalCurrentPairToNext
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat) : Nat × Nat :=
  (matchedEventualCanonicalCurrentIndexToNext
      trajectory transitionStart physicalScale offset pair.1,
    matchedEventualCanonicalCurrentIndexToNext
      trajectory transitionStart physicalScale offset pair.2)

def matchedEventualCanonicalNextPairToCurrent
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat) : Nat × Nat :=
  (matchedEventualCanonicalNextIndexToCurrent
      trajectory transitionStart physicalScale offset pair.1,
    matchedEventualCanonicalNextIndexToCurrent
      trajectory transitionStart physicalScale offset pair.2)

theorem matchedEventualCanonicalCurrentPairToNext_mem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset) :
    matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale offset pair ∈
      matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale (offset + 1) := by
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  exact (mem_cartesian_iff _ _ _).mpr
    ⟨matchedEventualCanonicalCurrentIndexToNext_mem
        trajectory transitionStart physicalScale offset pair.1 hmembers.1,
      matchedEventualCanonicalCurrentIndexToNext_mem
        trajectory transitionStart physicalScale offset pair.2 hmembers.2⟩

theorem matchedEventualCanonicalNextPairToCurrent_mem
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNextPairToCurrent
        trajectory transitionStart physicalScale offset pair ∈
      matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale offset := by
  exact (mem_cartesian_iff _ _ _).mpr
    ⟨matchedEventualCanonicalNextIndexToCurrent_mem
        trajectory transitionStart physicalScale offset pair.1,
      matchedEventualCanonicalNextIndexToCurrent_mem
        trajectory transitionStart physicalScale offset pair.2⟩

theorem matchedEventualCanonicalNextPairToCurrent_currentToNext
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale offset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset) :
    matchedEventualCanonicalNextPairToCurrent
        trajectory transitionStart physicalScale offset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale offset pair) =
      pair := by
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  apply Prod.ext
  · exact matchedEventualCanonicalNextIndexToCurrent_currentToNext
      trajectory transitionStart physicalScale offset pair.1 hmembers.1
  · exact matchedEventualCanonicalNextIndexToCurrent_currentToNext
      trajectory transitionStart physicalScale offset pair.2 hmembers.2

/-! ## 3. Remaining separated-route analytic envelopes -/

/-- With canonical pair maps internal, load variation reduces to two literal
pointwise inequalities and their summable budget. -/
structure MatchedEventualCanonicalRoutedLoadEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall offset, (0 : Q') <= variation offset
  tailControl : AntitoneTailControl variation
  current_le_next : forall offset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset ->
      matchedEventualCanonicalRoutedLoadOnPair
          trajectory transitionStart physicalScale offset pair <=
        matchedEventualCanonicalRoutedLoadOnPair
            trajectory transitionStart physicalScale (offset + 1)
            (matchedEventualCanonicalCurrentPairToNext
              trajectory transitionStart physicalScale offset pair) +
          variation offset
  next_le_current : forall offset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (offset + 1) ->
      matchedEventualCanonicalRoutedLoadOnPair
          trajectory transitionStart physicalScale (offset + 1) pair <=
        matchedEventualCanonicalRoutedLoadOnPair
            trajectory transitionStart physicalScale offset
            (matchedEventualCanonicalNextPairToCurrent
              trajectory transitionStart physicalScale offset pair) +
          variation offset

/-- The dual support-aware kernel envelope on the same pair maps. -/
structure MatchedEventualCanonicalSupportedKernelEnvelope
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall offset, (0 : Q') <= variation offset
  tailControl : AntitoneTailControl variation
  next_le_current : forall offset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale offset ->
      matchedEventualCanonicalSupportedKernelCandidateOnPair
          trajectory transitionStart physicalScale (offset + 1)
          (matchedEventualCanonicalCurrentPairToNext
            trajectory transitionStart physicalScale offset pair) <=
        matchedEventualCanonicalSupportedKernelCandidateOnPair
            trajectory transitionStart physicalScale offset pair +
          variation offset
  current_le_next : forall offset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale (offset + 1) ->
      matchedEventualCanonicalSupportedKernelCandidateOnPair
          trajectory transitionStart physicalScale offset
          (matchedEventualCanonicalNextPairToCurrent
            trajectory transitionStart physicalScale offset pair) <=
        matchedEventualCanonicalSupportedKernelCandidateOnPair
            trajectory transitionStart physicalScale (offset + 1) pair +
          variation offset

def MatchedEventualCanonicalRoutedLoadEnvelope.toMaximumVariation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalRoutedLoadEnvelope
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalRoutedLoadMaximumVariation
      trajectory transitionStart physicalScale where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  value_nonnegative := fun offset pair hpair => by
    have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
    exact
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_nonnegative
        (matchedEventualCanonicalRoutingAt
          trajectory transitionStart physicalScale offset)
        hmembers.1 pair.2
  currentToNext :=
    matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale
  currentToNext_mem :=
    matchedEventualCanonicalCurrentPairToNext_mem
      trajectory transitionStart physicalScale
  current_le_next := data.current_le_next
  nextToCurrent :=
    matchedEventualCanonicalNextPairToCurrent
      trajectory transitionStart physicalScale
  nextToCurrent_mem := fun offset pair _ =>
    matchedEventualCanonicalNextPairToCurrent_mem
      trajectory transitionStart physicalScale offset pair
  next_le_current := data.next_le_current

def MatchedEventualCanonicalSupportedKernelEnvelope.toMinimumVariation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (data : MatchedEventualCanonicalSupportedKernelEnvelope
      trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalSupportedKernelMinimumVariation
      trajectory transitionStart physicalScale where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  currentToNext :=
    matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale
  currentToNext_mem :=
    matchedEventualCanonicalCurrentPairToNext_mem
      trajectory transitionStart physicalScale
  next_le_current := data.next_le_current
  nextToCurrent :=
    matchedEventualCanonicalNextPairToCurrent
      trajectory transitionStart physicalScale
  nextToCurrent_mem := fun offset pair _ =>
    matchedEventualCanonicalNextPairToCurrent_mem
      trajectory transitionStart physicalScale offset pair
  current_le_next := data.current_le_next

/-- The two analytic envelopes and the uniform pointwise kernel floor compile
to exact matched support-debt variation after the geometric recodings have
been discharged internally. -/
def matchedEventualCanonicalSupportCapacityDebtVariationOfEnvelopes
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat)
    (load : MatchedEventualCanonicalRoutedLoadEnvelope
      trajectory transitionStart physicalScale)
    (kernel : MatchedEventualCanonicalSupportedKernelEnvelope
      trajectory transitionStart physicalScale)
    (kernelFloor : MatchedEventualCanonicalSupportedKernelMinimumFloor
      trajectory transitionStart physicalScale) :
    SummableRationalStepVariation
      (matchedEventualCanonicalSupportCapacityDebt
        trajectory transitionStart physicalScale) :=
  matchedEventualCanonicalSupportCapacityDebtVariationOfPointwise
    trajectory transitionStart physicalScale
    load.toMaximumVariation kernel.toMinimumVariation kernelFloor

/-- Scale-indexed load/kernel envelopes, pointwise kernel floors, a positive
tail allowance, and the computed initial slack construct the unchanged exact
matched prefix-tail persistence producer. -/
def matchedEventualCanonicalSupportDebtPrefixTailProducerOfEnvelopes
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (load : forall physicalScale,
      MatchedEventualCanonicalRoutedLoadEnvelope
        trajectory transitionStart physicalScale)
    (kernel : forall physicalScale,
      MatchedEventualCanonicalSupportedKernelEnvelope
        trajectory transitionStart physicalScale)
    (kernelFloor : forall physicalScale,
      MatchedEventualCanonicalSupportedKernelMinimumFloor
        trajectory transitionStart physicalScale)
    (tailAllowance : Nat -> Q')
    (tailAllowance_pos : forall physicalScale,
      (0 : Q') < tailAllowance physicalScale)
    (initial_closure : forall physicalScale,
      matchedEventualCanonicalSupportCapacityDebt
            trajectory transitionStart physicalScale 0 +
          SummableRationalStepVariationPrefixTailClosure.prefixTailTotalBudget
            (matchedEventualCanonicalSupportCapacityDebtVariationOfEnvelopes
              trajectory transitionStart physicalScale
              (load physicalScale) (kernel physicalScale)
              (kernelFloor physicalScale))
            (tailAllowance physicalScale) <=
        (1 : Q')) :
    BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailCompiler.MatchedPhysicalDynamicExplicitRayEventualCanonicalSupportDebtPrefixTailProducer
      trajectory where
  transitionStart := transitionStart
  debtVariation := fun physicalScale =>
    matchedEventualCanonicalSupportCapacityDebtVariationOfEnvelopes
      trajectory transitionStart physicalScale
      (load physicalScale) (kernel physicalScale) (kernelFloor physicalScale)
  tailAllowance := tailAllowance
  tailAllowance_pos := tailAllowance_pos
  initial_closure := initial_closure

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding.matchedEventualCanonicalCurrentIndexToNext_mem
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding.matchedEventualCanonicalNextIndexToCurrent_mem
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding.matchedEventualCanonicalNextIndexToCurrent_currentToNext
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding.matchedEventualCanonicalCurrentPairToNext_mem
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding.matchedEventualCanonicalNextPairToCurrent_mem
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding.matchedEventualCanonicalNextPairToCurrent_currentToNext
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding.MatchedEventualCanonicalRoutedLoadEnvelope.toMaximumVariation
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding.MatchedEventualCanonicalSupportedKernelEnvelope.toMinimumVariation
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding.matchedEventualCanonicalSupportCapacityDebtVariationOfEnvelopes
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding.matchedEventualCanonicalSupportDebtPrefixTailProducerOfEnvelopes
