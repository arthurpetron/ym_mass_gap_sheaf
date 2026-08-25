/-
# Route-coherent bridge for matched dynamic correlated capacity debt

The transported-old deficit mixes two effects: finite data change when the
cutoff recedes, and change of the canonical loop-erased routes.  This module
constructs a bridge routing at the later cutoff.  On embedded-old endpoints
it maps the preceding canonical path through the exact cutoff embedding; on
new endpoints it uses the later canonical path.

Inserting the bridge into the exact same-edge normalized capacity debt splits
the transported deficit into data/new-traffic drift and route churn.  Together
with the three shell faces, this exposes five independent analytic estimates
which rejoin the already verified four-region and total-deficit compilers.

No inverse-square estimate, tail allowance, initial closure, continuum
theory, or Clay conclusion is supplied.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Constructive.CRealAbs
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportProxy
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private theorem add_le_add_local
    {a b c d : Q'} (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add_right a b c hab)
    (Q'.add_le_add_left b c d hcd)

private theorem reassoc_cancel_local (u middle residual : Q') :
    ((u + (-middle)) + (middle + residual)) ≈ u + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv u (-middle) (middle + residual)) ?_
  refine Q'.add_eqv_congr_left u
    ((-middle) + (middle + residual)) residual ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 residual
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

private theorem abs_sub_triangle_local (a b c : Q') :
    Q'.abs (a + -b) <=
      Q'.abs (a + -c) + Q'.abs (c + -b) := by
  have hdecompose : a + -b ≈ (a + -c) + (c + -b) := by
    exact Q'.eqv_symm (reassoc_cancel_local a c (-b))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.abs_add_le' (a + -c) (c + -b))

private theorem listQMaxZero_le_of_member_bound_local
    {State : Type} (value : State -> Q') (bound : Q') :
    forall states : List State,
      (0 : Q') <= bound ->
      (forall state, state ∈ states -> value state <= bound) ->
      listQMaxZero value states <= bound
  | [], hbound, _ => hbound
  | head :: tail, hbound, hall => by
      unfold listQMaxZero
      exact (Q'.max'_le_iff' _ _ _).mpr
        ⟨hall head List.mem_cons_self,
          listQMaxZero_le_of_member_bound_local value bound tail hbound
            (fun state hstate =>
              hall state (List.mem_cons_of_mem head hstate))⟩

/-! ## 1. Map an exact positive path through the cutoff embedding -/

private def mapPositiveKernelChainInLocal
    {State Target : Type}
    {kernel : State -> State -> Q'}
    {replacement : Target -> Target -> Q'}
    {support : List State} {targetSupport : List Target}
    (map : State -> Target)
    (map_mem : forall state,
      state ∈ support -> map state ∈ targetSupport)
    (edgePositive : forall first next,
      first ∈ support -> next ∈ support ->
      (0 : Q') < kernel first next ->
      (0 : Q') < replacement (map first) (map next)) :
    {first last : State} -> first ∈ support ->
      PositiveKernelChainIn kernel support first last ->
      PositiveKernelChainIn replacement targetSupport
        (map first) (map last)
  | _, _, _, PositiveKernelChainIn.refl state =>
      PositiveKernelChainIn.refl (map state)
  | first, _, hfirst,
      PositiveKernelChainIn.step
        (next := next) positive hnext rest =>
      PositiveKernelChainIn.step
        (edgePositive first next hfirst hnext positive)
        (map_mem next hnext)
        (mapPositiveKernelChainInLocal
          map map_mem edgePositive hnext rest)

theorem matchedEventualCanonicalCurrentIndexToNext_kernel_pos
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset first next : Nat)
    (hfirst : first ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset)
    (hnext : next ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + cutoffOffset) 0 first next) :
    (0 : Q') <
      centralPhysicalFiniteKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0
        (matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale cutoffOffset first)
        (matchedEventualCanonicalCurrentIndexToNext
          trajectory transitionStart physicalScale cutoffOffset next) := by
  have hadjacent :
      centralPhysicalFiniteSupportAdjacentB
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + cutoffOffset) 0 first next = true :=
    (centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
      hfirst hnext).mpr hpositive
  have hmappedAdjacent :=
    centralPhysicalFiniteSupportAdjacentB_cutoffIndexMap
      (w := trajectory.nome physicalScale)
      (hw := Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (base := transitionStart physicalScale + cutoffOffset)
      (later := (transitionStart physicalScale + cutoffOffset) + 1)
      (half := 0) (row := first) (column := next)
      (Nat.le_succ (transitionStart physicalScale + cutoffOffset))
      (centralPhysicalFiniteVacuumSectorIndex_lt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + cutoffOffset) 0 hfirst)
      (centralPhysicalFiniteVacuumSectorIndex_lt
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + cutoffOffset) 0 hnext)
      hadjacent
  have hresult := centralPhysicalFiniteKernel_pos_of_supportAdjacent
    (matchedEventualCanonicalCurrentIndexToNext_mem
      trajectory transitionStart physicalScale cutoffOffset first hfirst)
    (matchedEventualCanonicalCurrentIndexToNext_mem
      trajectory transitionStart physicalScale cutoffOffset next hnext)
    hmappedAdjacent
  simpa only [Nat.add_assoc] using hresult

def matchedEventualCanonicalMapPositivePathToNext
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    {first last : Nat}
    (hfirst : first ∈ matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset)
    (path : PositiveKernelChainIn
      (centralPhysicalFiniteKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + cutoffOffset) 0)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale cutoffOffset)
      first last) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (transitionStart physicalScale + (cutoffOffset + 1)) 0)
      (matchedEventualCanonicalVacuumSectorIndices
        trajectory transitionStart physicalScale (cutoffOffset + 1))
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale cutoffOffset first)
      (matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale cutoffOffset last) :=
  mapPositiveKernelChainInLocal
    (matchedEventualCanonicalCurrentIndexToNext
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalCurrentIndexToNext_mem
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalCurrentIndexToNext_kernel_pos
      trajectory transitionStart physicalScale cutoffOffset)
    hfirst path

theorem matchedEventualCanonicalCurrentIndexToNext_nextToCurrent_of_mem_embeddedOldIndex
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset index : Nat)
    (hindex : index ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
      trajectory transitionStart physicalScale cutoffOffset) :
    matchedEventualCanonicalCurrentIndexToNext
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalNextIndexToCurrent
          trajectory transitionStart physicalScale cutoffOffset index) =
      index := by
  unfold matchedEventualCanonicalEmbeddedOldIndexCarrier at hindex
  unfold matchedEventualCanonicalNextIndexToCurrent
  exact map_firstMappedPreimageOr_eq_of_mem_map
    (matchedEventualCanonicalCurrentIndexToNext
      trajectory transitionStart physicalScale cutoffOffset)
    0 index
    (matchedEventualCanonicalVacuumSectorIndices
      trajectory transitionStart physicalScale cutoffOffset)
    hindex

/-! ## 2. A total mapped-path bridge routing at the later cutoff -/

def matchedEventualCanonicalTransportedRoutingAtNext
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + (cutoffOffset + 1)) where
  path := fun left right hleft hright => by
    by_cases hleftOld : left ∈
        matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset
    · by_cases hrightOld : right ∈
          matchedEventualCanonicalEmbeddedOldIndexCarrier
            trajectory transitionStart physicalScale cutoffOffset
      · let oldLeft := matchedEventualCanonicalNextIndexToCurrent
          trajectory transitionStart physicalScale cutoffOffset left
        let oldRight := matchedEventualCanonicalNextIndexToCurrent
          trajectory transitionStart physicalScale cutoffOffset right
        have holdLeft : oldLeft ∈
            matchedEventualCanonicalVacuumSectorIndices
              trajectory transitionStart physicalScale cutoffOffset :=
          matchedEventualCanonicalNextIndexToCurrent_mem
            trajectory transitionStart physicalScale cutoffOffset left
        have holdRight : oldRight ∈
            matchedEventualCanonicalVacuumSectorIndices
              trajectory transitionStart physicalScale cutoffOffset :=
          matchedEventualCanonicalNextIndexToCurrent_mem
            trajectory transitionStart physicalScale cutoffOffset right
        let oldPath :=
          (matchedEventualCanonicalRoutingAt
            trajectory transitionStart physicalScale cutoffOffset).path
              oldLeft oldRight holdLeft holdRight
        have mapped := matchedEventualCanonicalMapPositivePathToNext
          trajectory transitionStart physicalScale cutoffOffset
          holdLeft oldPath
        have hleftMap :
            matchedEventualCanonicalCurrentIndexToNext
                trajectory transitionStart physicalScale cutoffOffset
                oldLeft = left :=
          matchedEventualCanonicalCurrentIndexToNext_nextToCurrent_of_mem_embeddedOldIndex
            trajectory transitionStart physicalScale cutoffOffset left hleftOld
        have hrightMap :
            matchedEventualCanonicalCurrentIndexToNext
                trajectory transitionStart physicalScale cutoffOffset
                oldRight = right :=
          matchedEventualCanonicalCurrentIndexToNext_nextToCurrent_of_mem_embeddedOldIndex
            trajectory transitionStart physicalScale cutoffOffset right hrightOld
        rw [hleftMap, hrightMap] at mapped
        exact mapped
      · exact
          (matchedEventualCanonicalRoutingAt
            trajectory transitionStart physicalScale
            (cutoffOffset + 1)).path left right hleft hright
    · exact
        (matchedEventualCanonicalRoutingAt
          trajectory transitionStart physicalScale
          (cutoffOffset + 1)).path left right hleft hright

/-! ## 3. The same debt evaluated on an arbitrary exact routing -/

def matchedEventualRoutedCapacityDebtOnPairForRouting
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset))
    (pair : Nat × Nat) : Q' :=
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (transitionStart physicalScale + cutoffOffset) 0 pair.1 pair.2
  if hcapacity : (0 : Q') < capacity then
    Q'.divPos
      (matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
          routing pair)
      capacity hcapacity
  else 0

theorem matchedEventualRoutedCapacityDebtOnPairForRouting_canonical
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualRoutedCapacityDebtOnPairForRouting
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalRoutingAt
          trajectory transitionStart physicalScale cutoffOffset) pair =
      matchedEventualCanonicalRoutedCapacityDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset pair :=
  rfl

/-! ## 4. Split transported-old debt into data drift and route churn -/

def matchedEventualCanonicalTransportedBridgeDataDeficitOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (pair : Nat × Nat) : Q' :=
  let current := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale cutoffOffset pair
  let bridge := matchedEventualRoutedCapacityDebtOnPairForRouting
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    (matchedEventualCanonicalTransportedRoutingAtNext
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalCurrentPairToNext
      trajectory transitionStart physicalScale cutoffOffset pair)
  Q'.max' (Q'.abs (current + -bridge))
    (Q'.abs (bridge + -current))

def matchedEventualCanonicalTransportedBridgeRouteDeficitOnPair
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (pair : Nat × Nat) : Q' :=
  let mappedPair := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  let bridge := matchedEventualRoutedCapacityDebtOnPairForRouting
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    (matchedEventualCanonicalTransportedRoutingAtNext
      trajectory transitionStart physicalScale cutoffOffset) mappedPair
  let canonical := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale (cutoffOffset + 1) mappedPair
  Q'.max' (Q'.abs (bridge + -canonical))
    (Q'.abs (canonical + -bridge))

def matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalTransportedBridgeDataDeficitOnPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalTransportedBridgeRouteDeficitMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (matchedEventualCanonicalTransportedBridgeRouteDeficitOnPair
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeDataDeficitMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold matchedEventualCanonicalTransportedBridgeDataDeficitOnPair
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.abs_nonneg _) (Q'.le_max'_left _ _)

theorem matchedEventualCanonicalTransportedBridgeRouteDeficitMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeRouteDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalTransportedBridgeRouteDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold matchedEventualCanonicalTransportedBridgeRouteDeficitOnPair
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.abs_nonneg _) (Q'.le_max'_left _ _)

theorem matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair_le_bridge_split
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (pair : Nat × Nat) :
    matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalTransportedBridgeDataDeficitOnPair
          trajectory transitionStart physicalScale cutoffOffset pair +
        matchedEventualCanonicalTransportedBridgeRouteDeficitOnPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  let current := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale cutoffOffset pair
  let mappedPair := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  let bridge := matchedEventualRoutedCapacityDebtOnPairForRouting
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    (matchedEventualCanonicalTransportedRoutingAtNext
      trajectory transitionStart physicalScale cutoffOffset) mappedPair
  let canonical := matchedEventualCanonicalRoutedCapacityDebtOnPair
    trajectory transitionStart physicalScale (cutoffOffset + 1) mappedPair
  change Q'.max'
      (Q'.abs (current + -canonical))
      (Q'.abs (canonical + -current)) <=
    Q'.max'
        (Q'.abs (current + -bridge))
        (Q'.abs (bridge + -current)) +
      Q'.max'
        (Q'.abs (bridge + -canonical))
        (Q'.abs (canonical + -bridge))
  apply (Q'.max'_le_iff' _ _ _).mpr
  constructor
  · exact Q'.le_trans' _ _ _
      (abs_sub_triangle_local current canonical bridge)
      (add_le_add_local
        (Q'.le_max'_left _ _) (Q'.le_max'_left _ _))
  · have htriangle := abs_sub_triangle_local canonical current bridge
    have hmaxima :
        Q'.abs (canonical + -bridge) +
            Q'.abs (bridge + -current) <=
          Q'.max'
              (Q'.abs (bridge + -canonical))
              (Q'.abs (canonical + -bridge)) +
            Q'.max'
              (Q'.abs (current + -bridge))
              (Q'.abs (bridge + -current)) :=
      add_le_add_local
        (Q'.le_max'_right _ _) (Q'.le_max'_right _ _)
    exact Q'.le_trans' _ _ _ htriangle
      (Q'.le_trans' _ _ _ hmaxima
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

theorem matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_le_bridge_split
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualCanonicalTransportedBridgeRouteDeficitMaximum
          trajectory transitionStart physicalScale cutoffOffset := by
  have hexact :
      matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum
          trajectory transitionStart physicalScale cutoffOffset <=
        matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
            trajectory transitionStart physicalScale cutoffOffset +
          matchedEventualCanonicalTransportedBridgeRouteDeficitMaximum
            trajectory transitionStart physicalScale cutoffOffset := by
    unfold matchedEventualCanonicalTransportedCapacityDebtDeficitExactMaximum
    apply listQMaxZero_le_of_member_bound_local
    · exact Q'.zero_le_add _ _
        (matchedEventualCanonicalTransportedBridgeDataDeficitMaximum_nonnegative
          trajectory transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalTransportedBridgeRouteDeficitMaximum_nonnegative
          trajectory transitionStart physicalScale cutoffOffset)
    · intro pair hpair
      exact Q'.le_trans' _ _ _
        (matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair_le_bridge_split
          trajectory transitionStart physicalScale cutoffOffset pair)
        (add_le_add_local
          (le_listQMaxZero_of_mem
            (matchedEventualCanonicalTransportedBridgeDataDeficitOnPair
              trajectory transitionStart physicalScale cutoffOffset)
            (matchedEventualCanonicalVacuumSectorPairs
              trajectory transitionStart physicalScale cutoffOffset) hpair)
          (le_listQMaxZero_of_mem
            (matchedEventualCanonicalTransportedBridgeRouteDeficitOnPair
              trajectory transitionStart physicalScale cutoffOffset)
            (matchedEventualCanonicalVacuumSectorPairs
              trajectory transitionStart physicalScale cutoffOffset) hpair))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_eqv_exact
        trajectory transitionStart physicalScale cutoffOffset))
    hexact

/-! ## 5. Five inverse-square leaves rejoin the existing total control -/

structure MatchedEventualCanonicalTransportedCapacityDebtBridgeInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  dataCoefficient : Q'
  routeCoefficient : Q'
  dataCoefficient_nonnegative : (0 : Q') <= dataCoefficient
  routeCoefficient_nonnegative : (0 : Q') <= routeCoefficient
  data_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalTransportedBridgeDataDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      dataCoefficient * invSqTerm offset offset_at_least_two cutoffOffset
  route_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalTransportedBridgeRouteDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      routeCoefficient * invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalTransportedCapacityDebtBridgeInverseSquareControl.coefficient
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalTransportedCapacityDebtBridgeInverseSquareControl
        trajectory transitionStart physicalScale) : Q' :=
  control.dataCoefficient + control.routeCoefficient

theorem MatchedEventualCanonicalTransportedCapacityDebtBridgeInverseSquareControl.coefficient_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalTransportedCapacityDebtBridgeInverseSquareControl
        trajectory transitionStart physicalScale) :
    (0 : Q') <= control.coefficient :=
  Q'.zero_le_add _ _
    control.dataCoefficient_nonnegative
    control.routeCoefficient_nonnegative

theorem MatchedEventualCanonicalTransportedCapacityDebtBridgeInverseSquareControl.transported_le
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalTransportedCapacityDebtBridgeInverseSquareControl
        trajectory transitionStart physicalScale)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two cutoffOffset := by
  let term := invSqTerm
    control.offset control.offset_at_least_two cutoffOffset
  exact Q'.le_trans' _ _ _
    (matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_le_bridge_split
      trajectory transitionStart physicalScale cutoffOffset)
    (Q'.le_trans' _ _ _
      (add_le_add_local
        (control.data_le cutoffOffset) (control.route_le cutoffOffset))
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.add_mul_eqv
            control.dataCoefficient control.routeCoefficient term))))

structure MatchedEventualCanonicalCapacityDebtBridgeRegionalInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  transport :
    MatchedEventualCanonicalTransportedCapacityDebtBridgeInverseSquareControl
      trajectory transitionStart physicalScale
  oldNewCoefficient : Q'
  newOldCoefficient : Q'
  newNewCoefficient : Q'
  oldNewCoefficient_nonnegative : (0 : Q') <= oldNewCoefficient
  newOldCoefficient_nonnegative : (0 : Q') <= newOldCoefficient
  newNewCoefficient_nonnegative : (0 : Q') <= newNewCoefficient
  oldNew_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      oldNewCoefficient *
        invSqTerm transport.offset
          transport.offset_at_least_two cutoffOffset
  newOld_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      newOldCoefficient *
        invSqTerm transport.offset
          transport.offset_at_least_two cutoffOffset
  newNew_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      newNewCoefficient *
        invSqTerm transport.offset
          transport.offset_at_least_two cutoffOffset

def MatchedEventualCanonicalCapacityDebtBridgeRegionalInverseSquareControl.toRegionalControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtBridgeRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtRegionalInverseSquareControl
      trajectory transitionStart physicalScale where
  offset := control.transport.offset
  offset_at_least_two := control.transport.offset_at_least_two
  transportCoefficient := control.transport.coefficient
  oldNewCoefficient := control.oldNewCoefficient
  newOldCoefficient := control.newOldCoefficient
  newNewCoefficient := control.newNewCoefficient
  transportCoefficient_nonnegative :=
    control.transport.coefficient_nonnegative
  oldNewCoefficient_nonnegative := control.oldNewCoefficient_nonnegative
  newOldCoefficient_nonnegative := control.newOldCoefficient_nonnegative
  newNewCoefficient_nonnegative := control.newNewCoefficient_nonnegative
  transport_le := control.transport.transported_le
  oldNew_le := control.oldNew_le
  newOld_le := control.newOld_le
  newNew_le := control.newNew_le

def MatchedEventualCanonicalCapacityDebtBridgeRegionalInverseSquareControl.toTotalControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtBridgeRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtInverseSquareControl
      trajectory transitionStart physicalScale :=
  control.toRegionalControl.toTotalControl

def MatchedEventualCanonicalCapacityDebtBridgeRegionalInverseSquareControl.toTotalDeficitTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtBridgeRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale :=
  control.toTotalControl.toTotalDeficitTail

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge.matchedEventualCanonicalCurrentIndexToNext_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge.matchedEventualCanonicalMapPositivePathToNext
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge.matchedEventualCanonicalTransportedRoutingAtNext
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge.matchedEventualRoutedCapacityDebtOnPairForRouting_canonical
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge.matchedEventualCanonicalTransportedCapacityDebtDeficitOnPair_le_bridge_split
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge.matchedEventualCanonicalTransportedCapacityDebtDeficitMaximum_le_bridge_split
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge.MatchedEventualCanonicalTransportedCapacityDebtBridgeInverseSquareControl.transported_le
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge.MatchedEventualCanonicalCapacityDebtBridgeRegionalInverseSquareControl.toRegionalControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge.MatchedEventualCanonicalCapacityDebtBridgeRegionalInverseSquareControl.toTotalDeficitTail
