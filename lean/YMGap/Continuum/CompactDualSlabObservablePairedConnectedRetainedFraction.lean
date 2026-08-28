/-
# The explicit retained connected fraction

The connected first-source transport has row mass at most one, so its complete
transported Gibbs mass is no larger than the literal support-connected source
mass.  A positive-channel witness makes both masses strictly positive at
positive coupling.  Their constructive positive quotient is therefore an
explicit retained fraction `delta` in `(0,1]` whose product with the connected
source mass is exactly the transported mass.

This is a finite-volume, cutoff-dependent fraction.  Its type retains the full
physical datum `D`; no lower bound uniform in coupling, cutoff, separation, or
volume is asserted.

Constructive contract: finite termwise comparison and positive rational
division only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSplitPosteriorMass
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalPushforward
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The transported mass is a submass of the connected source sector -/

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A -> Q') :
    forall items : List A,
      (forall item, item ∈ items -> left item ≤ right item) ->
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm => by
      simp only [listQSum]
      exact Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hterm item (List.mem_cons_of_mem head hitem)))

private theorem connectedThinnedWeight_le_original
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedConnectedStrandChoice
      D rootFaceId targetFaceId source) :
    slabObservablePairedConnectedStrandThinnedWeight
        D rootFaceId targetFaceId htarget source choice ≤
      slabObservablePairedConnectedStrandWeight
        D rootFaceId targetFaceId source choice := by
  unfold slabObservablePairedConnectedStrandThinnedWeight
    firstSourceThinnedWeight
  split
  · exact Q'.le_refl' _
  · exact slabObservablePairedConnectedStrandWeight_nonnegative
      D rootFaceId targetFaceId source choice

theorem slabObservablePairedConnectedStrandThinnedRowMass_le_one
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (source : SlabObservablePairedConnectedStrandSource
      D rootFaceId targetFaceId) :
    slabObservablePairedConnectedStrandThinnedRowMass
        D rootFaceId targetFaceId htarget source ≤ 1 := by
  unfold slabObservablePairedConnectedStrandThinnedRowMass
  exact Q'.le_trans' _ _ _
    (listQSum_le_termwise_local
      (slabObservablePairedConnectedStrandThinnedWeight
        D rootFaceId targetFaceId htarget source)
      (slabObservablePairedConnectedStrandWeight
        D rootFaceId targetFaceId source)
      (slabObservablePairedConnectedStrandChoices
        D rootFaceId targetFaceId source)
      (fun choice _ => connectedThinnedWeight_le_original
        D rootFaceId targetFaceId htarget source choice))
    (slabObservablePairedConnectedStrandWeight_row_le_one
      D rootFaceId targetFaceId source)

/-- Literal unnormalized Gibbs mass of the support-connected source sector. -/
def slabObservablePairedConnectedSourceMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat) : Q' :=
  listQSum (slabObservableTwoReplicaPairWeight D)
    (slabObservablePairedSupportConnectedFourCellSourcePairs
      D rootFaceId targetFaceId)

theorem slabObservablePairedConnectedStrandThinnedTransportedMass_le_sourceMass
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    slabObservablePairedConnectedStrandThinnedTransportedMass
        D rootFaceId targetFaceId htarget ≤
      slabObservablePairedConnectedSourceMass
        D rootFaceId targetFaceId := by
  have hattached :
      slabObservablePairedConnectedStrandThinnedTransportedMass
          D rootFaceId targetFaceId htarget ≤
        listQSum
          (fun source : SlabObservablePairedConnectedStrandSource
              D rootFaceId targetFaceId =>
            slabObservableTwoReplicaPairWeight D source.1)
          (slabObservablePairedConnectedStrandSources
            D rootFaceId targetFaceId) := by
    unfold slabObservablePairedConnectedStrandThinnedTransportedMass
    apply listQSum_le_termwise_local
    intro source _
    have hmul := Q'.mul_le_mul_of_nonneg_left
      (slabObservablePairedConnectedStrandThinnedRowMass
        D rootFaceId targetFaceId htarget source)
      1
      (slabObservableTwoReplicaPairWeight D source.1)
      (slabObservablePairedConnectedStrandThinnedRowMass_le_one
        D rootFaceId targetFaceId htarget source)
      (slabObservableTwoReplicaPairWeight_nonnegative
        D rootFaceId source.1)
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv
        (Q'.mul_one_eqv
          (slabObservableTwoReplicaPairWeight D source.1)))
  exact Q'.le_trans' _ _ _ hattached
    (Q'.le_of_eqv (Q'.eqv_of_eq (by
      unfold slabObservablePairedConnectedStrandSources
        slabObservablePairedConnectedSourceMass
      exact listQSum_attach
        (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId))))

/-! ## 2. Positive source mass and the canonical quotient -/

theorem slabObservablePairedConnectedSourceMass_pos
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    (witness : SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId) :
    (0 : Q') < slabObservablePairedConnectedSourceMass
      D rootFaceId targetFaceId := by
  unfold slabObservablePairedConnectedSourceMass
  exact YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity.listQSum_pos_of_mem
    (slabObservableTwoReplicaPairWeight D)
    (fun pair => slabObservableTwoReplicaPairWeight_nonnegative
      D rootFaceId pair)
    (slabObservablePairedSupportConnectedFourCellSourcePairs
      D rootFaceId targetFaceId)
    witness.source.2
    (slabObservablePairedConnectedStrandSourceWeight_pos_of_coupling_pos
      D hcoupling rootFaceId targetFaceId witness.source)

/-- The finite retained fraction and its exact source-mass identity. -/
structure SlabObservablePairedConnectedRetainedFractionCertificate
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) where
  delta : Q'
  delta_pos : (0 : Q') < delta
  delta_le_one : delta ≤ 1
  delta_mul_sourceMass_eqv :
    delta * slabObservablePairedConnectedSourceMass
        D rootFaceId targetFaceId ≈
      slabObservablePairedConnectedStrandThinnedTransportedMass
        D rootFaceId targetFaceId htarget

/-- A positive-channel witness computes the exact finite retained fraction
`transportedMass / connectedSourceMass`. -/
def slabObservablePairedConnectedRetainedFractionCertificate
    (D : SlabPhysicalData) (hcoupling : (0 : Q') < D.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (witness : SlabObservablePairedConnectedPositiveChannelWitness
      D rootFaceId targetFaceId) :
    SlabObservablePairedConnectedRetainedFractionCertificate
      D rootFaceId targetFaceId htarget := by
  let sourceMass := slabObservablePairedConnectedSourceMass
    D rootFaceId targetFaceId
  let transported :=
    slabObservablePairedConnectedStrandThinnedTransportedMass
      D rootFaceId targetFaceId htarget
  have hsourcePos : (0 : Q') < sourceMass :=
    slabObservablePairedConnectedSourceMass_pos
      D hcoupling rootFaceId targetFaceId witness
  have htransportedPos : (0 : Q') < transported :=
    slabObservablePairedConnectedStrandThinnedTransportedMass_pos
      D hcoupling rootFaceId targetFaceId htarget witness
  have htransportedLe : transported ≤ sourceMass :=
    slabObservablePairedConnectedStrandThinnedTransportedMass_le_sourceMass
      D rootFaceId targetFaceId htarget
  let delta := Q'.divPos transported sourceMass hsourcePos
  exact
    { delta := delta
      delta_pos := Q'.divPos_pos transported sourceMass
        hsourcePos htransportedPos
      delta_le_one := Q'.divPos_le_of_le_mul
        transported sourceMass hsourcePos
        (Q'.le_trans' _ sourceMass _ htransportedLe
          (Q'.ge_of_eqv (Q'.one_mul_eqv sourceMass)))
      delta_mul_sourceMass_eqv :=
        Q'.divPos_mul_eqv transported sourceMass hsourcePos }

end YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction

#print axioms YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction.slabObservablePairedConnectedStrandThinnedRowMass_le_one
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction.slabObservablePairedConnectedStrandThinnedTransportedMass_le_sourceMass
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction.slabObservablePairedConnectedSourceMass_pos
#print axioms YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction.slabObservablePairedConnectedRetainedFractionCertificate
