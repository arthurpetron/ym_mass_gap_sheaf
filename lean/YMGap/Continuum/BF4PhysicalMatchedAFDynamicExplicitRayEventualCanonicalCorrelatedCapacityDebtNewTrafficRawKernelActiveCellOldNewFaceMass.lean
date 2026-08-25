/-
# Exact old--new face mass

The preceding old--new projective-amplification compiler bounded one masked
row by the stationary mass of the entire complementary endpoint list.  That
introduced a factor two and charged the old--new lane for the new--old and
new--new faces as well.

Here the endpoint carrier is filtered by the exact old--new predicate.  Its
stationary mass injects into the literal Cartesian old-block/new-block
carrier, whose mass is exactly the product of the two block masses.  Since
the old mass is at most one, the old--new face mass is at most the new-block
mass with coefficient one.  The projective-amplification row and analytic
interface are sharpened accordingly without changing the mapped edge, route,
endpoint weights, or conditional capacity.

No quantitative amplification or new-block decay estimate, continuum theory,
or Clay conclusion is supplied.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or declaration marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewProjectiveAmplification
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
import YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
import YMGap.Continuum.BF4PhysicalFiniteVacuumSector
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
import YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment
import YMGap.Continuum.FiniteWeightedCartesianInjection
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceEndpointRatio
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFacePayment
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellFaceRelativeSourceLoad
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewProjectiveAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficWeightedAmplification
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private def oldNewShellPairDecidable
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (pair : Nat × Nat) :
    Decidable
      (MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale offset pair) := by
  unfold MatchedEventualCanonicalPairInOldNewShell
    MatchedEventualCanonicalIndexInNewShell
  infer_instance

private theorem listQSum_nonnegative_on_local {A : Type}
    (value : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> (0 : Q') <= value item) ->
      (0 : Q') <= listQSum value items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hvalue =>
      Q'.zero_le_add _ _
        (hvalue head List.mem_cons_self)
        (listQSum_nonnegative_on_local value tail
          (fun item hitem => hvalue item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A -> Q') : forall items : List A,
      (forall item, item ∈ items -> left item <= right item) ->
      listQSum left items <= listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_mask_eq_filter_local {A : Type}
    (value : A -> Q') (event : A -> Bool) : forall items : List A,
      listQSum (fun item => if event item then value item else 0) items ≈
        listQSum value (items.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      cases hevent : event head
      · simp only [List.filter_cons, hevent, Bool.false_eq_true,
          if_false, listQSum]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.eqv_refl 0)
            (listQSum_mask_eq_filter_local value event tail))
          (Q'.eqv_of_eq (Q'.zero_add' _))
      · simp only [List.filter_cons, hevent, if_true, listQSum]
        exact Q'.add_eqv_congr'
          (Q'.eqv_refl (value head))
          (listQSum_mask_eq_filter_local value event tail)

/-! ## 1. The exact old--new endpoint carrier and its mass -/

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceEvent
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) : Bool :=
  @decide
    (MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset pair)
    (oldNewShellPairDecidable
      trajectory transitionStart physicalScale cutoffOffset pair)

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointPairs
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    List (Nat × Nat) :=
  (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    trajectory transitionStart physicalScale cutoffOffset).filter
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEvent
        trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  listQSum
    (matchedEventualCanonicalNewEndpointStationaryPairWeight
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointTrafficOldNewBlockStationaryMass
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) : Q' :=
  let weight := matchedEventualCanonicalLaterIndexWeight
    trajectory transitionStart physicalScale cutoffOffset
  listQSum (fun pair => weight pair.1 * weight pair.2)
    (cartesian
      (matchedEventualCanonicalLaterOldBlockIndices
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalLaterNewBlockIndices
        trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointPair_mem_oldNewBlocks
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    pair ∈ cartesian
      (matchedEventualCanonicalLaterOldBlockIndices
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalLaterNewBlockIndices
        trajectory transitionStart physicalScale cutoffOffset) := by
  have hparts := List.mem_filter.mp hpair
  have hface : MatchedEventualCanonicalPairInOldNewShell
      trajectory transitionStart physicalScale cutoffOffset pair := by
    exact @of_decide_eq_true _
      (oldNewShellPairDecidable
        trajectory transitionStart physicalScale cutoffOffset pair) hparts.2
  have hcutoff := matchedEventualCanonicalCurrentCutoff_le_laterCutoff
    transitionStart physicalScale cutoffOffset
  have hleftGeneric :=
    (mem_matchedEventualCanonicalEmbeddedOldIndexCarrier_iff_generic
      trajectory transitionStart physicalScale cutoffOffset pair.1).mp hface.1
  have hleftBlock :=
    (mem_centralPhysicalFiniteVacuumSectorOldBlockIndices_iff hcutoff).mpr
      hleftGeneric
  have hrightLater : pair.2 ∈ centralPhysicalFiniteVacuumSectorIndices
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (matchedEventualCanonicalLaterCutoff
        transitionStart physicalScale cutoffOffset) 0 := by
    simpa only [matchedEventualCanonicalVacuumSectorIndices,
      matchedEventualCanonicalLaterCutoff] using hface.2.1
  have hrightGenericNot : pair.2 ∉
      centralPhysicalFiniteEmbeddedVacuumSectorIndices
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (matchedEventualCanonicalCurrentCutoff
          transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalLaterCutoff
          transitionStart physicalScale cutoffOffset) 0 := by
    intro hgeneric
    exact hface.2.2
      ((mem_matchedEventualCanonicalEmbeddedOldIndexCarrier_iff_generic
        trajectory transitionStart physicalScale cutoffOffset pair.2).mpr
        hgeneric)
  have hrightBlock :=
    mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mpr
      ⟨hrightLater, hrightGenericNot⟩
  exact (mem_cartesian_iff _ _ pair).mpr ⟨hleftBlock, hrightBlock⟩

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass_nonnegative
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass
  apply listQSum_nonnegative_on_local
  intro pair hpair
  exact matchedEventualCanonicalNewEndpointStationaryPairWeight_nonnegative
    trajectory transitionStart physicalScale cutoffOffset pair
    (List.mem_filter.mp hpair).1

theorem matchedEventualCanonicalNewEndpointTrafficOldNewBlockStationaryMass_eqv_old_mul_new
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewBlockStationaryMass
        trajectory transitionStart physicalScale cutoffOffset ≈
      matchedEventualCanonicalLaterOldBlockMass
          trajectory transitionStart physicalScale cutoffOffset *
        matchedEventualCanonicalLaterNewBlockMass
          trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewBlockStationaryMass
    matchedEventualCanonicalLaterOldBlockMass
    matchedEventualCanonicalLaterNewBlockMass
    centralPhysicalFiniteVacuumSectorNewMass finiteWeightedMass
    matchedEventualCanonicalLaterOldBlockIndices
    matchedEventualCanonicalLaterNewBlockIndices
    matchedEventualCanonicalLaterIndexWeight
  exact listQSum_cartesian_product _ _ _ _

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass_le_old_mul_new
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalLaterOldBlockMass
          trajectory transitionStart physicalScale cutoffOffset *
        matchedEventualCanonicalLaterNewBlockMass
          trajectory transitionStart physicalScale cutoffOffset := by
  let source :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset
  let target := cartesian
    (matchedEventualCanonicalLaterOldBlockIndices
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalLaterNewBlockIndices
      trajectory transitionStart physicalScale cutoffOffset)
  let weight := matchedEventualCanonicalNewEndpointStationaryPairWeight
    trajectory transitionStart physicalScale cutoffOffset
  have hsource : source.Nodup := by
    unfold source
    apply List.filter_sublist.nodup
    unfold matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    exact List.filter_sublist.nodup
      (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs_nodup
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (matchedEventualCanonicalLaterCutoff
          transitionStart physicalScale cutoffOffset))
  have hsum : listQSum weight source <= listQSum weight target := by
    apply listQSum_le_of_injective source target weight weight
      (fun pair => pair) hsource
    · intro pair hpair
      exact
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointPair_mem_oldNewBlocks
          trajectory transitionStart physicalScale cutoffOffset pair hpair
    · intro _ _ _ _ heq
      exact heq
    · intro _ _
      exact Q'.le_refl' _
    · intro pair _
      unfold weight
        matchedEventualCanonicalNewEndpointStationaryPairWeight
        matchedEventualCanonicalLaterIndexWeight
        centralPhysicalFiniteWeight
      exact Q'.mul_nonneg _ _
        (centralPhysicalRowMarginal_nonnegative
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (matchedEventualCanonicalLaterCutoff
            transitionStart physicalScale cutoffOffset) 0 _)
        (centralPhysicalRowMarginal_nonnegative
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (matchedEventualCanonicalLaterCutoff
            transitionStart physicalScale cutoffOffset) 0 _)
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (matchedEventualCanonicalNewEndpointTrafficOldNewBlockStationaryMass_eqv_old_mul_new
        trajectory transitionStart physicalScale cutoffOffset))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass_le_newBlockMass
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalLaterNewBlockMass
        trajectory transitionStart physicalScale cutoffOffset := by
  let oldMass := matchedEventualCanonicalLaterOldBlockMass
    trajectory transitionStart physicalScale cutoffOffset
  let newMass := matchedEventualCanonicalLaterNewBlockMass
    trajectory transitionStart physicalScale cutoffOffset
  have hnew0 : (0 : Q') <= newMass :=
    matchedEventualCanonicalLaterNewBlockMass_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
  have hold1 : oldMass <= 1 :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg oldMass newMass hnew0)
      (matchedEventualCanonicalLaterOld_add_newMass_le_one
        trajectory transitionStart physicalScale cutoffOffset)
  exact Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass_le_old_mul_new
      trajectory transitionStart physicalScale cutoffOffset)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hold1 hnew0)
      (Q'.le_of_eqv (Q'.one_mul_eqv newMass)))

/-! ## 2. The exact old--new row pays only its own face mass -/

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_faceMass_mul_projectiveAmplificationMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass
          trajectory transitionStart physicalScale cutoffOffset *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  let items := matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    trajectory transitionStart physicalScale cutoffOffset
  let event := matchedEventualCanonicalNewEndpointTrafficOldNewFaceEvent
    trajectory transitionStart physicalScale cutoffOffset
  let weight := matchedEventualCanonicalNewEndpointStationaryPairWeight
    trajectory transitionStart physicalScale cutoffOffset
  let amplification := fun endpointPair =>
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationOnCell
      trajectory transitionStart physicalScale cutoffOffset
      (pair, endpointPair)
  let maximum :=
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
      trajectory transitionStart physicalScale cutoffOffset pair
  unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
  have hsum :
      listQSum
          (fun endpointPair =>
            matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
              trajectory transitionStart physicalScale cutoffOffset
              (pair, endpointPair)) items <=
        listQSum
          (fun endpointPair =>
            if event endpointPair then weight endpointPair * maximum else 0)
          items := by
    apply listQSum_le_termwise_local
    intro endpointPair hendpointPair
    letI := oldNewShellPairDecidable
      trajectory transitionStart physicalScale cutoffOffset endpointPair
    by_cases hface : MatchedEventualCanonicalPairInOldNewShell
        trajectory transitionStart physicalScale cutoffOffset endpointPair
    · have hevent : event endpointPair = true := by
        unfold event matchedEventualCanonicalNewEndpointTrafficOldNewFaceEvent
        simp [hface]
      simp only [hevent, if_true]
      have hamp : amplification endpointPair <= maximum :=
        le_listQMaxZero_of_mem amplification items hendpointPair
      have hweight0 : (0 : Q') <= weight endpointPair :=
        matchedEventualCanonicalNewEndpointStationaryPairWeight_nonnegative
          trajectory transitionStart physicalScale cutoffOffset
          endpointPair hendpointPair
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio_eqv_stationaryWeight_mul_projectiveAmplification
            trajectory transitionStart physicalScale cutoffOffset
            (pair, endpointPair) hendpointPair))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hamp hweight0)
    · have hevent : event endpointPair = false := by
        unfold event matchedEventualCanonicalNewEndpointTrafficOldNewFaceEvent
        simp [hface]
      simp only [hevent, Bool.false_eq_true, if_false]
      unfold matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatio
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceAllowance
      rw [if_neg hface]
      exact Q'.le_refl' 0
  refine Q'.le_trans' _ _ _ hsum ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _ _ _
      (listQSum_mask_eq_filter_local
        (fun endpointPair => weight endpointPair * maximum) event items)
      (Q'.eqv_trans _ _ _
        (FiniteWeightedGramSOS.listQSum_mul_right
          weight maximum (items.filter event))
        (Q'.eqv_refl _)))

theorem matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_newBlockMass_mul_projectiveAmplificationMaximum
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat) :
    matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalLaterNewBlockMass
          trajectory transitionStart physicalScale cutoffOffset *
        matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair := by
  exact Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_faceMass_mul_projectiveAmplificationMaximum
      trajectory transitionStart physicalScale cutoffOffset pair)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass_le_newBlockMass
        trajectory transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair_nonnegative
        trajectory transitionStart physicalScale cutoffOffset pair))

/-! ## 3. Coefficient-one old--new analytic interface -/

structure MatchedEventualCanonicalNewEndpointTrafficOldNewFaceSharpProjectiveAmplificationInverseSquareControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat) (physicalScale offset : Nat)
    (offset_at_least_two : 2 <= offset) : Type 1 where
  coefficient : Q'
  coefficient_nonnegative : (0 : Q') <= coefficient
  envelope_le : forall cutoffOffset pair,
    pair ∈ matchedEventualCanonicalVacuumSectorPairs
        trajectory transitionStart physicalScale cutoffOffset ->
    matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale *
        (matchedEventualCanonicalLaterNewBlockMass
            trajectory transitionStart physicalScale cutoffOffset *
          matchedEventualCanonicalNewEndpointTrafficOldNewFaceProjectiveAmplificationMaximumOnCurrentPair
            trajectory transitionStart physicalScale cutoffOffset pair) <=
      (coefficient * invSqTerm offset offset_at_least_two cutoffOffset) *
        matchedEventualCanonicalNewEndpointTrafficConditionalCapacityOnCurrentPair
          trajectory transitionStart physicalScale cutoffOffset pair

def MatchedEventualCanonicalNewEndpointTrafficOldNewFaceSharpProjectiveAmplificationInverseSquareControl.toEndpointRatioControl
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (control : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceSharpProjectiveAmplificationInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two) :
    MatchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two where
  coefficient := control.coefficient
  coefficient_nonnegative := control.coefficient_nonnegative
  endpointRatio_le := by
    intro cutoffOffset pair hpair
    have hfloor0 : (0 : Q') <=
        matchedEventualCanonicalSupportSharedFloor
          trajectory transitionStart physicalScale :=
      Q'.le_of_lt
        (matchedEventualCanonicalSupportSharedFloor_pos
          trajectory transitionStart physicalScale)
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_newBlockMass_mul_projectiveAmplificationMaximum
          trajectory transitionStart physicalScale cutoffOffset pair)
        hfloor0)
      (control.envelope_le cutoffOffset pair hpair)

theorem matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_sharpOldNewProjectiveAmplification_and_otherFaces
    {family : MatchedBlockFamily} {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory : MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat} {physicalScale offset : Nat}
    {offset_at_least_two : 2 <= offset}
    (oldNew : MatchedEventualCanonicalNewEndpointTrafficOldNewFaceSharpProjectiveAmplificationInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newOld : MatchedEventualCanonicalNewEndpointTrafficNewOldFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (newNew : MatchedEventualCanonicalNewEndpointTrafficNewNewFaceEndpointRatioCapacityBalanceInverseSquareControl
      trajectory transitionStart physicalScale offset offset_at_least_two)
    (cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      (oldNew.coefficient + (newOld.coefficient + newNew.coefficient)) *
        invSqTerm offset offset_at_least_two cutoffOffset :=
  matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_threeFaceEndpointRatioCapacityBalances
    oldNew.toEndpointRatioControl newOld newNew cutoffOffset

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass.matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointPair_mem_oldNewBlocks
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass.matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass.matchedEventualCanonicalNewEndpointTrafficOldNewBlockStationaryMass_eqv_old_mul_new
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass.matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass_le_old_mul_new
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass.matchedEventualCanonicalNewEndpointTrafficOldNewFaceStationaryMass_le_newBlockMass
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass.matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_faceMass_mul_projectiveAmplificationMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass.matchedEventualCanonicalNewEndpointTrafficOldNewFaceEndpointRatioRow_le_newBlockMass_mul_projectiveAmplificationMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass.MatchedEventualCanonicalNewEndpointTrafficOldNewFaceSharpProjectiveAmplificationInverseSquareControl.toEndpointRatioControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficRawKernelActiveCellOldNewFaceMass.matchedEventualCanonicalNewEndpointTrafficDebtMaximum_le_of_sharpOldNewProjectiveAmplification_and_otherFaces
