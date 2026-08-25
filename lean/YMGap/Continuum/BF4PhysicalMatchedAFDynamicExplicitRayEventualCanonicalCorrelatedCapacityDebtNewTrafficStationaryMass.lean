/-
# Stationary-mass control of matched dynamic new-endpoint traffic

The count-times-maximum estimator is completely explicit, but the ambient
count can grow polynomially.  The same literal new endpoint list has a sharper
weighted size: its stationary-product mass at the later cutoff.  Because every
listed pair has at least one endpoint outside the exact embedded-old vacuum
component, this pair mass is at most twice the stationary mass of the later
new index block.

The existing moving-base cutoff compiler then bounds that new-block mass by
the corrected-slab adjacent-cutoff increment plus the exact component-merger
mass.  If the executable no-merger check succeeds, only the known slab
increment remains.  These are observable-connected reductions on the same
matched nome, consecutive cutoff carriers, and endpoint list.

This module does not yet bound route amplification or the conditional-kernel
denominator, and it supplies no inverse-square estimate, continuum theory, or
Clay conclusion.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, or declaration marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficCarrierBound
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorComponentMergerDecision
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorNewMassComponentSplit
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimpleCoercivity
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficCarrierBound
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualEndpointMassBound
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphSimplePaths
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Exact consecutive matched block data -/

def matchedEventualCanonicalCurrentCutoff
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Nat :=
  transitionStart physicalScale + cutoffOffset

def matchedEventualCanonicalLaterCutoff
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Nat :=
  transitionStart physicalScale + (cutoffOffset + 1)

def matchedEventualCanonicalLaterOldBlockIndices
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : List Nat :=
  centralPhysicalFiniteVacuumSectorOldBlockIndices
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (matchedEventualCanonicalCurrentCutoff
      transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalLaterCutoff
      transitionStart physicalScale cutoffOffset) 0

def matchedEventualCanonicalLaterNewBlockIndices
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : List Nat :=
  centralPhysicalFiniteVacuumSectorNewBlockIndices
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (matchedEventualCanonicalCurrentCutoff
      transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalLaterCutoff
      transitionStart physicalScale cutoffOffset) 0

def matchedEventualCanonicalLaterIndexWeight
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset index : Nat) : Q' :=
  centralPhysicalFiniteWeight
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (matchedEventualCanonicalLaterCutoff
      transitionStart physicalScale cutoffOffset) 0 index

def matchedEventualCanonicalLaterOldBlockMass
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  listQSum
    (matchedEventualCanonicalLaterIndexWeight
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalLaterOldBlockIndices
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalLaterNewBlockMass
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorNewMass
    (trajectory.nome physicalScale)
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (matchedEventualCanonicalCurrentCutoff
      transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalLaterCutoff
      transitionStart physicalScale cutoffOffset) 0

theorem matchedEventualCanonicalCurrentCutoff_le_laterCutoff
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalCurrentCutoff
        transitionStart physicalScale cutoffOffset ≤
      matchedEventualCanonicalLaterCutoff
        transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalCurrentCutoff
    matchedEventualCanonicalLaterCutoff
  omega

theorem mem_matchedEventualCanonicalEmbeddedOldIndexCarrier_iff_generic
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset index : Nat) :
    index ∈ matchedEventualCanonicalEmbeddedOldIndexCarrier
        trajectory transitionStart physicalScale cutoffOffset ↔
      index ∈ centralPhysicalFiniteEmbeddedVacuumSectorIndices
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (matchedEventualCanonicalCurrentCutoff
          transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalLaterCutoff
          transitionStart physicalScale cutoffOffset) 0 := by
  unfold matchedEventualCanonicalEmbeddedOldIndexCarrier
    matchedEventualCanonicalVacuumSectorIndices
    matchedEventualCanonicalCurrentIndexToNext
    centralPhysicalFiniteEmbeddedVacuumSectorIndices
    matchedEventualCanonicalCurrentCutoff
    matchedEventualCanonicalLaterCutoff
  simp only [Nat.add_assoc]

/-! ## 2. New residual pairs lie in the three generic shell blocks -/

def matchedEventualCanonicalNewEndpointStationaryBlockPairs
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : List (Nat × Nat) :=
  let old := matchedEventualCanonicalLaterOldBlockIndices
    trajectory transitionStart physicalScale cutoffOffset
  let new := matchedEventualCanonicalLaterNewBlockIndices
    trajectory transitionStart physicalScale cutoffOffset
  cartesian old new ++ (cartesian new old ++ cartesian new new)

theorem matchedEventualCanonicalNewEndpointPair_mem_stationaryBlocks
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (pair : Nat × Nat)
    (hpair : pair ∈
      matchedEventualCanonicalTransportedBridgeNewEndpointPairs
        trajectory transitionStart physicalScale cutoffOffset) :
    pair ∈ matchedEventualCanonicalNewEndpointStationaryBlockPairs
      trajectory transitionStart physicalScale cutoffOffset := by
  have hparts := List.mem_filter.mp hpair
  have hsector :=
    centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hparts.1
  have hcutoff := matchedEventualCanonicalCurrentCutoff_le_laterCutoff
    transitionStart physicalScale cutoffOffset
  have hleftLater : pair.1 ∈ centralPhysicalFiniteVacuumSectorIndices
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (matchedEventualCanonicalLaterCutoff
        transitionStart physicalScale cutoffOffset) 0 := by
    simpa only [matchedEventualCanonicalLaterCutoff] using hsector.1
  have hrightLater : pair.2 ∈ centralPhysicalFiniteVacuumSectorIndices
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (matchedEventualCanonicalLaterCutoff
        transitionStart physicalScale cutoffOffset) 0 := by
    simpa only [matchedEventualCanonicalLaterCutoff] using hsector.2
  by_cases hleftOld : pair.1 ∈
      matchedEventualCanonicalEmbeddedOldIndexCarrier
        trajectory transitionStart physicalScale cutoffOffset
  · by_cases hrightOld : pair.2 ∈
        matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset
    · have holdB :
          matchedEventualCanonicalTransportedBridgeEndpointPairOldB
              trajectory transitionStart physicalScale cutoffOffset pair = true := by
        unfold matchedEventualCanonicalTransportedBridgeEndpointPairOldB
        simp [hleftOld, hrightOld]
      rw [holdB] at hparts
      cases hparts.2
    · have hleftGeneric :=
        (mem_matchedEventualCanonicalEmbeddedOldIndexCarrier_iff_generic
          trajectory transitionStart physicalScale cutoffOffset pair.1).mp
          hleftOld
      have hleftBlock :=
        (mem_centralPhysicalFiniteVacuumSectorOldBlockIndices_iff
          hcutoff).mpr hleftGeneric
      have hrightGenericNot : pair.2 ∉
          centralPhysicalFiniteEmbeddedVacuumSectorIndices
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (matchedEventualCanonicalCurrentCutoff
              transitionStart physicalScale cutoffOffset)
            (matchedEventualCanonicalLaterCutoff
              transitionStart physicalScale cutoffOffset) 0 := by
        intro hgeneric
        exact hrightOld
          ((mem_matchedEventualCanonicalEmbeddedOldIndexCarrier_iff_generic
            trajectory transitionStart physicalScale cutoffOffset pair.2).mpr
            hgeneric)
      have hrightBlock :=
        mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mpr
          ⟨hrightLater, hrightGenericNot⟩
      exact List.mem_append.mpr
        (Or.inl ((mem_cartesian_iff _ _ pair).mpr
          ⟨hleftBlock, hrightBlock⟩))
  · have hleftGenericNot : pair.1 ∉
        centralPhysicalFiniteEmbeddedVacuumSectorIndices
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (matchedEventualCanonicalCurrentCutoff
            transitionStart physicalScale cutoffOffset)
          (matchedEventualCanonicalLaterCutoff
            transitionStart physicalScale cutoffOffset) 0 := by
      intro hgeneric
      exact hleftOld
        ((mem_matchedEventualCanonicalEmbeddedOldIndexCarrier_iff_generic
          trajectory transitionStart physicalScale cutoffOffset pair.1).mpr
          hgeneric)
    have hleftBlock :=
      mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mpr
        ⟨hleftLater, hleftGenericNot⟩
    by_cases hrightOld : pair.2 ∈
        matchedEventualCanonicalEmbeddedOldIndexCarrier
          trajectory transitionStart physicalScale cutoffOffset
    · have hrightGeneric :=
        (mem_matchedEventualCanonicalEmbeddedOldIndexCarrier_iff_generic
          trajectory transitionStart physicalScale cutoffOffset pair.2).mp
          hrightOld
      have hrightBlock :=
        (mem_centralPhysicalFiniteVacuumSectorOldBlockIndices_iff
          hcutoff).mpr hrightGeneric
      exact List.mem_append.mpr
        (Or.inr (List.mem_append.mpr
          (Or.inl ((mem_cartesian_iff _ _ pair).mpr
            ⟨hleftBlock, hrightBlock⟩))))
    · have hrightGenericNot : pair.2 ∉
          centralPhysicalFiniteEmbeddedVacuumSectorIndices
            (trajectory.nome physicalScale)
            (Q'.le_of_lt (trajectory.nome_pos physicalScale))
            (matchedEventualCanonicalCurrentCutoff
              transitionStart physicalScale cutoffOffset)
            (matchedEventualCanonicalLaterCutoff
              transitionStart physicalScale cutoffOffset) 0 := by
        intro hgeneric
        exact hrightOld
          ((mem_matchedEventualCanonicalEmbeddedOldIndexCarrier_iff_generic
            trajectory transitionStart physicalScale cutoffOffset pair.2).mpr
            hgeneric)
      have hrightBlock :=
        mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mpr
          ⟨hrightLater, hrightGenericNot⟩
      exact List.mem_append.mpr
        (Or.inr (List.mem_append.mpr
          (Or.inr ((mem_cartesian_iff _ _ pair).mpr
            ⟨hleftBlock, hrightBlock⟩))))

/-! ## 3. Stationary product mass and the two-new-mass bound -/

def matchedEventualCanonicalNewEndpointStationaryMass
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  let weight := matchedEventualCanonicalLaterIndexWeight
    trajectory transitionStart physicalScale cutoffOffset
  listQSum (fun pair => weight pair.1 * weight pair.2)
    (matchedEventualCanonicalTransportedBridgeNewEndpointPairs
      trajectory transitionStart physicalScale cutoffOffset)

def matchedEventualCanonicalNewEndpointStationaryBlockMass
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  let weight := matchedEventualCanonicalLaterIndexWeight
    trajectory transitionStart physicalScale cutoffOffset
  listQSum (fun pair => weight pair.1 * weight pair.2)
    (matchedEventualCanonicalNewEndpointStationaryBlockPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalNewEndpointStationaryMass_le_blockMass
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointStationaryMass
        trajectory transitionStart physicalScale cutoffOffset ≤
      matchedEventualCanonicalNewEndpointStationaryBlockMass
        trajectory transitionStart physicalScale cutoffOffset := by
  let source := matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    trajectory transitionStart physicalScale cutoffOffset
  let target := matchedEventualCanonicalNewEndpointStationaryBlockPairs
    trajectory transitionStart physicalScale cutoffOffset
  let weight := matchedEventualCanonicalLaterIndexWeight
    trajectory transitionStart physicalScale cutoffOffset
  unfold matchedEventualCanonicalNewEndpointStationaryMass
    matchedEventualCanonicalNewEndpointStationaryBlockMass
  apply listQSum_le_of_injective source target
    (fun pair => weight pair.1 * weight pair.2)
    (fun pair => weight pair.1 * weight pair.2)
    (fun pair => pair)
  · unfold source
    unfold matchedEventualCanonicalTransportedBridgeNewEndpointPairs
    exact List.filter_sublist.nodup
      (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs_nodup
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (matchedEventualCanonicalLaterCutoff
          transitionStart physicalScale cutoffOffset))
  · intro pair hpair
    exact matchedEventualCanonicalNewEndpointPair_mem_stationaryBlocks
      trajectory transitionStart physicalScale cutoffOffset pair hpair
  · intro _ _ _ _ heq
    exact heq
  · intro _ _
    exact Q'.le_refl' _
  · intro pair _
    unfold weight matchedEventualCanonicalLaterIndexWeight
    exact Q'.mul_nonneg _ _
      (centralPhysicalRowMarginal_nonnegative
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (matchedEventualCanonicalLaterCutoff
          transitionStart physicalScale cutoffOffset) 0 _)
      (centralPhysicalRowMarginal_nonnegative
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (matchedEventualCanonicalLaterCutoff
          transitionStart physicalScale cutoffOffset) 0 _)

theorem matchedEventualCanonicalNewEndpointStationaryBlockMass_eqv_products
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointStationaryBlockMass
        trajectory transitionStart physicalScale cutoffOffset ≈
      matchedEventualCanonicalLaterOldBlockMass
          trajectory transitionStart physicalScale cutoffOffset *
        matchedEventualCanonicalLaterNewBlockMass
          trajectory transitionStart physicalScale cutoffOffset +
      (matchedEventualCanonicalLaterNewBlockMass
            trajectory transitionStart physicalScale cutoffOffset *
          matchedEventualCanonicalLaterOldBlockMass
            trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualCanonicalLaterNewBlockMass
            trajectory transitionStart physicalScale cutoffOffset *
          matchedEventualCanonicalLaterNewBlockMass
            trajectory transitionStart physicalScale cutoffOffset) := by
  let old := matchedEventualCanonicalLaterOldBlockIndices
    trajectory transitionStart physicalScale cutoffOffset
  let new := matchedEventualCanonicalLaterNewBlockIndices
    trajectory transitionStart physicalScale cutoffOffset
  let weight := matchedEventualCanonicalLaterIndexWeight
    trajectory transitionStart physicalScale cutoffOffset
  unfold matchedEventualCanonicalNewEndpointStationaryBlockMass
    matchedEventualCanonicalNewEndpointStationaryBlockPairs
  change listQSum (fun pair => weight pair.1 * weight pair.2)
      (cartesian old new ++ (cartesian new old ++ cartesian new new)) ≈
    listQSum weight old * listQSum weight new +
      (listQSum weight new * listQSum weight old +
        listQSum weight new * listQSum weight new)
  refine Q'.eqv_trans _
    (listQSum (fun pair => weight pair.1 * weight pair.2)
        (cartesian old new) +
      (listQSum (fun pair => weight pair.1 * weight pair.2)
          (cartesian new old) +
        listQSum (fun pair => weight pair.1 * weight pair.2)
          (cartesian new new))) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (listQSum_append _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (listQSum_append _ _ _))
  · exact Q'.add_eqv_congr'
      (listQSum_cartesian_product weight weight old new)
      (Q'.add_eqv_congr'
        (listQSum_cartesian_product weight weight new old)
        (listQSum_cartesian_product weight weight new new))

theorem matchedEventualCanonicalLaterOld_add_newMass_eqv_fullSectorMass
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalLaterOldBlockMass
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualCanonicalLaterNewBlockMass
          trajectory transitionStart physicalScale cutoffOffset ≈
      centralPhysicalFiniteVacuumSectorMass
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (matchedEventualCanonicalLaterCutoff
          transitionStart physicalScale cutoffOffset) 0 := by
  unfold matchedEventualCanonicalLaterOldBlockMass
    matchedEventualCanonicalLaterNewBlockMass
    matchedEventualCanonicalLaterOldBlockIndices
  unfold centralPhysicalFiniteVacuumSectorNewMass
    centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
  unfold centralPhysicalFiniteVacuumSectorOldBlockIndices
    centralPhysicalFiniteVacuumSectorNewBlockIndices
    matchedEventualCanonicalLaterIndexWeight
  exact Q'.eqv_symm
    (listQSum_filter_partition
      (matchedEventualCanonicalLaterIndexWeight
        trajectory transitionStart physicalScale cutoffOffset)
      (centralPhysicalFiniteEmbeddedVacuumSectorB
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (matchedEventualCanonicalCurrentCutoff
          transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalLaterCutoff
          transitionStart physicalScale cutoffOffset) 0)
      (centralPhysicalFiniteVacuumSectorIndices
        (trajectory.nome physicalScale)
        (Q'.le_of_lt (trajectory.nome_pos physicalScale))
        (matchedEventualCanonicalLaterCutoff
          transitionStart physicalScale cutoffOffset) 0))

theorem matchedEventualCanonicalLaterOldBlockMass_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') ≤ matchedEventualCanonicalLaterOldBlockMass
      trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalLaterOldBlockMass
  apply listQSum_nonnegative_on
  intro index _
  unfold matchedEventualCanonicalLaterIndexWeight
  exact centralPhysicalRowMarginal_nonnegative
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (matchedEventualCanonicalLaterCutoff
      transitionStart physicalScale cutoffOffset) 0 _

theorem matchedEventualCanonicalLaterNewBlockMass_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') ≤ matchedEventualCanonicalLaterNewBlockMass
      trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalLaterNewBlockMass
    centralPhysicalFiniteVacuumSectorNewMass finiteWeightedMass
  apply listQSum_nonnegative_on
  intro index _
  unfold centralPhysicalFiniteWeight
  exact centralPhysicalRowMarginal_nonnegative
    (Q'.le_of_lt (trajectory.nome_pos physicalScale))
    (matchedEventualCanonicalLaterCutoff
      transitionStart physicalScale cutoffOffset) 0 _

theorem matchedEventualCanonicalLaterOld_add_newMass_le_one
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalLaterOldBlockMass
          trajectory transitionStart physicalScale cutoffOffset +
        matchedEventualCanonicalLaterNewBlockMass
          trajectory transitionStart physicalScale cutoffOffset ≤ 1 :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (matchedEventualCanonicalLaterOld_add_newMass_eqv_fullSectorMass
        trajectory transitionStart physicalScale cutoffOffset))
    (centralPhysicalFiniteVacuumSectorMass_le_one
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (matchedEventualCanonicalLaterCutoff
        transitionStart physicalScale cutoffOffset) 0)

theorem matchedEventualCanonicalNewEndpointStationaryBlockMass_le_two_newMass
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointStationaryBlockMass
        trajectory transitionStart physicalScale cutoffOffset ≤
      Q'.ofNat 2 * matchedEventualCanonicalLaterNewBlockMass
        trajectory transitionStart physicalScale cutoffOffset := by
  let oldMass := matchedEventualCanonicalLaterOldBlockMass
    trajectory transitionStart physicalScale cutoffOffset
  let newMass := matchedEventualCanonicalLaterNewBlockMass
    trajectory transitionStart physicalScale cutoffOffset
  have hnew0 : (0 : Q') ≤ newMass :=
    matchedEventualCanonicalLaterNewBlockMass_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
  have hsum1 : oldMass + newMass ≤ 1 :=
    matchedEventualCanonicalLaterOld_add_newMass_le_one
      trajectory transitionStart physicalScale cutoffOffset
  have hold1 : oldMass ≤ 1 :=
    Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg oldMass newMass hnew0) hsum1
  have hfirstRaw : (oldMass + newMass) * newMass ≤ 1 * newMass :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hsum1 hnew0
  have hfirst : (oldMass + newMass) * newMass ≤ newMass :=
    Q'.le_trans' _ _ _ hfirstRaw
      (Q'.le_of_eqv (Q'.one_mul_eqv newMass))
  have hsecondRaw : newMass * oldMass ≤ newMass * 1 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hold1 hnew0
  have hsecond : newMass * oldMass ≤ newMass :=
    Q'.le_trans' _ _ _ hsecondRaw
      (Q'.le_of_eqv (Q'.mul_one_eqv newMass))
  have hregroup :
      matchedEventualCanonicalNewEndpointStationaryBlockMass
          trajectory transitionStart physicalScale cutoffOffset ≈
        (oldMass + newMass) * newMass + newMass * oldMass := by
    refine Q'.eqv_trans _
      (oldMass * newMass +
        (newMass * oldMass + newMass * newMass)) _ ?_ ?_
    · exact matchedEventualCanonicalNewEndpointStationaryBlockMass_eqv_products
        trajectory transitionStart physicalScale cutoffOffset
    · q_ring
  have hsum :
      (oldMass + newMass) * newMass + newMass * oldMass ≤
        newMass + newMass :=
    Q'.le_trans' _ _ _
      (Q'.add_le_add_right _ _ _ hfirst)
      (Q'.add_le_add_left _ _ _ hsecond)
  have htwo : Q'.ofNat 2 * newMass ≈ newMass + newMass := by
    refine Q'.eqv_trans _ (((1 : Q') + 1) * newMass) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    refine Q'.eqv_trans _ (1 * newMass + 1 * newMass) _
      (Q'.add_mul_eqv 1 1 newMass) ?_
    exact Q'.add_eqv_congr'
      (Q'.one_mul_eqv newMass) (Q'.one_mul_eqv newMass)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv (Q'.eqv_symm htwo)))

theorem matchedEventualCanonicalNewEndpointStationaryMass_le_two_newMass
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalNewEndpointStationaryMass
        trajectory transitionStart physicalScale cutoffOffset ≤
      Q'.ofNat 2 * matchedEventualCanonicalLaterNewBlockMass
        trajectory transitionStart physicalScale cutoffOffset :=
  Q'.le_trans' _ _ _
    (matchedEventualCanonicalNewEndpointStationaryMass_le_blockMass
      trajectory transitionStart physicalScale cutoffOffset)
    (matchedEventualCanonicalNewEndpointStationaryBlockMass_le_two_newMass
      trajectory transitionStart physicalScale cutoffOffset)

/-! ## 4. The known slab increment and honest merger residual -/

theorem matchedEventualCanonicalLaterNewBlockMass_le_increment_add_merger
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalLaterNewBlockMass
        trajectory transitionStart physicalScale cutoffOffset ≤
      slabParametricKCutoffIncrement
          (trajectory.nome physicalScale)
          (matchedEventualCanonicalCurrentCutoff
            transitionStart physicalScale cutoffOffset)
          (matchedEventualCanonicalLaterCutoff
            transitionStart physicalScale cutoffOffset)
          (centralExtent 0) +
        centralPhysicalFiniteNewComponentMergerMass
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (matchedEventualCanonicalCurrentCutoff
            transitionStart physicalScale cutoffOffset)
          (matchedEventualCanonicalLaterCutoff
            transitionStart physicalScale cutoffOffset) 0 := by
  unfold matchedEventualCanonicalLaterNewBlockMass
  exact centralPhysicalFiniteVacuumSectorNewMass_le_increment_add_merger
    (matchedEventualCanonicalCurrentCutoff_le_laterCutoff
      transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalLaterNewBlockMass_le_increment_of_noMerger
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (hcheck : centralPhysicalFiniteNoComponentMergerCheck
      (trajectory.nome physicalScale)
      (Q'.le_of_lt (trajectory.nome_pos physicalScale))
      (matchedEventualCanonicalCurrentCutoff
        transitionStart physicalScale cutoffOffset)
      (matchedEventualCanonicalLaterCutoff
        transitionStart physicalScale cutoffOffset) 0 = true) :
    matchedEventualCanonicalLaterNewBlockMass
        trajectory transitionStart physicalScale cutoffOffset ≤
      slabParametricKCutoffIncrement
        (trajectory.nome physicalScale)
        (matchedEventualCanonicalCurrentCutoff
          transitionStart physicalScale cutoffOffset)
        (matchedEventualCanonicalLaterCutoff
          transitionStart physicalScale cutoffOffset)
        (centralExtent 0) := by
  unfold matchedEventualCanonicalLaterNewBlockMass
  exact centralPhysicalFiniteVacuumSectorNewMass_le_increment_of_check
    (matchedEventualCanonicalCurrentCutoff_le_laterCutoff
      transitionStart physicalScale cutoffOffset) hcheck

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass.mem_matchedEventualCanonicalEmbeddedOldIndexCarrier_iff_generic
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass.matchedEventualCanonicalNewEndpointPair_mem_stationaryBlocks
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass.matchedEventualCanonicalNewEndpointStationaryMass_le_blockMass
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass.matchedEventualCanonicalNewEndpointStationaryBlockMass_eqv_products
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass.matchedEventualCanonicalNewEndpointStationaryMass_le_two_newMass
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass.matchedEventualCanonicalLaterNewBlockMass_le_increment_add_merger
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTrafficStationaryMass.matchedEventualCanonicalLaterNewBlockMass_le_increment_of_noMerger
