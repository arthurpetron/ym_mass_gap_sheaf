/-
# Positive retained connected mass from one explicit strand channel

After zero-weight channels are removed, the exact remaining finite coercivity
certificate is small: one support-connected physical source together with one
listed successful strand-recoupling channel.  This module names that witness
and proves that it forces the canonically thinned connected transported mass
to be strictly positive at explicitly positive coupling.

The witness channel need not belong to the first source reaching its realized
target.  Generic search completeness finds the actual selected source and a
listed channel in that row.  Every listed channel is positive, so it survives
thinning.  Positive coupling supplies the selected row's strictly positive
Gibbs prefactor, and two finite positive-sum arguments lift the surviving term
first to the row and then to the full transported mass.

No witness is constructed here.  Thus this module contracts all analytic and
selector-side positivity work into one honest finite SU(2) channel-existence
obligation.

Constructive contract: explicit dependent witnesses, Boolean finite search,
and exact `Q'` positivity only; no `Classical`, choice, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
import YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass
import YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity

namespace YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local instance retainedMassPairDecidableEq
    (D : SlabPhysicalData) (rootFaceId : Nat) :
    DecidableEq (SlabObservableTwoReplicaPair D rootFaceId) :=
  slabObservableTwoReplicaPairDecidableEq D rootFaceId

/-! ## 1. The minimal positive-channel certificate -/

/-- One listed successful channel from one literal support-connected source.
The source subtype is automatically a member of its attached enumeration. -/
structure SlabObservablePairedConnectedPositiveChannelWitness
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) where
  source : SlabObservablePairedConnectedStrandSource
    D rootFaceId targetFaceId
  choice : SlabObservablePairedConnectedStrandChoice
    D rootFaceId targetFaceId source
  choice_mem : choice ∈ slabObservablePairedConnectedStrandChoices
    D rootFaceId targetFaceId source

/-! ## 2. One witness survives first-source thinning -/

/-- **Exact finite positivity reduction.**  At positive coupling, one listed
connected successful channel forces strictly positive thinned transported
mass. -/
theorem slabObservablePairedConnectedStrandThinnedTransportedMass_pos
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (witness : SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId) :
    (0 : Q') <
      slabObservablePairedConnectedStrandThinnedTransportedMass
        D rootFaceId targetFaceId htarget := by
  let target := slabObservablePairedConnectedStrandRealize
    D rootFaceId targetFaceId htarget witness.source witness.choice
  have hseedMem : witness.source ∈
      slabObservablePairedConnectedStrandSources
        D rootFaceId targetFaceId :=
    List.mem_attach _ witness.source
  have hreach := sourceReachesTargetB_true_of_mem_realize
    (SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandChoices
      D rootFaceId targetFaceId)
    (slabObservablePairedConnectedStrandRealize
      D rootFaceId targetFaceId htarget)
    witness.source target witness.choice witness.choice_mem rfl
  obtain ⟨selected, hfirst, choice, hchoice, hrealize⟩ :=
    firstSourceForTarget_some_choice_of_reachable
      (SlabObservablePairedConnectedStrandChoice
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedStrandChoices
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedStrandRealize
        D rootFaceId targetFaceId htarget)
      (slabObservablePairedConnectedStrandSources
        D rootFaceId targetFaceId)
      witness.source target hseedMem hreach
  have hselectedMem : selected ∈
      slabObservablePairedConnectedStrandSources
        D rootFaceId targetFaceId :=
    firstSourceForTarget_mem
      (SlabObservablePairedConnectedStrandChoice
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedStrandChoices
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedStrandRealize
        D rootFaceId targetFaceId htarget)
      target hfirst
  have hlocalPos : (0 : Q') <
      slabObservablePairedConnectedStrandWeight
        D rootFaceId targetFaceId selected choice :=
    slabObservablePairedConnectedStrandWeight_pos_of_mem
      D rootFaceId targetFaceId selected choice hchoice
  have hthinPos : (0 : Q') <
      slabObservablePairedConnectedStrandThinnedWeight
        D rootFaceId targetFaceId htarget selected choice := by
    exact firstSourceThinnedWeight_pos_of_selected
      (slabObservablePairedConnectedStrandSources
        D rootFaceId targetFaceId)
      (SlabObservablePairedConnectedStrandChoice
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedStrandChoices
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedStrandWeight
        D rootFaceId targetFaceId)
      (slabObservablePairedConnectedStrandRealize
        D rootFaceId targetFaceId htarget)
      selected choice target hfirst hrealize hlocalPos
  have hrowPos : (0 : Q') <
      slabObservablePairedConnectedStrandThinnedRowMass
        D rootFaceId targetFaceId htarget selected := by
    unfold slabObservablePairedConnectedStrandThinnedRowMass
    exact listQSum_pos_of_mem
      (slabObservablePairedConnectedStrandThinnedWeight
        D rootFaceId targetFaceId htarget selected)
      (slabObservablePairedConnectedStrandThinnedWeight_nonnegative
        D rootFaceId targetFaceId htarget selected)
      (slabObservablePairedConnectedStrandChoices
        D rootFaceId targetFaceId selected)
      hchoice hthinPos
  have htermPos : (0 : Q') <
      slabObservableTwoReplicaPairWeight D selected.1 *
        slabObservablePairedConnectedStrandThinnedRowMass
          D rootFaceId targetFaceId htarget selected :=
    Q'.mul_pos
      (slabObservablePairedConnectedStrandSourceWeight_pos_of_coupling_pos
        D hcoupling rootFaceId targetFaceId selected)
      hrowPos
  unfold slabObservablePairedConnectedStrandThinnedTransportedMass
  exact listQSum_pos_of_mem
    (fun source => slabObservableTwoReplicaPairWeight D source.1 *
      slabObservablePairedConnectedStrandThinnedRowMass
        D rootFaceId targetFaceId htarget source)
    (fun source => Q'.mul_nonneg _ _
      (slabObservableTwoReplicaPairWeight_nonnegative
        D rootFaceId source.1)
      (listQSum_nonnegative_on
        (slabObservablePairedConnectedStrandThinnedWeight
          D rootFaceId targetFaceId htarget source)
        (slabObservablePairedConnectedStrandChoices
          D rootFaceId targetFaceId source)
        (fun choice _ =>
          slabObservablePairedConnectedStrandThinnedWeight_nonnegative
            D rootFaceId targetFaceId htarget source choice)))
    (slabObservablePairedConnectedStrandSources
      D rootFaceId targetFaceId)
    hselectedMem htermPos

end YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity.slabObservablePairedConnectedStrandThinnedTransportedMass_pos
