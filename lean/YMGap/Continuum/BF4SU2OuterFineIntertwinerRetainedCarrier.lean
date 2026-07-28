/-
# Retaining the fine intertwiner carrier past the raw-row no-go

`BF4SU2OuterRawRowMassCounterexample` proves that the four-preimage face
packet forgets transverse fine flux and can turn a positive physical row
into the zero coarse row.  The universally inhabited carrier available
before that lossy projection is the literal finite list of fine link-fusion
assignments.

This module packages one checked member of that list as retained
`Type`-valued data.  Positivity of the fine physical term constructs such a
member for every cutoff and every row, so the corresponding all-row carrier
family is inhabited without a new hypothesis.  On the pinned collar source,
this retained carrier is inhabited while the old coarse joint carrier is
provably uninhabited.  This is the precise strict enlargement required for a
corrected conditional-integration kernel.

No coarse pushforward is asserted here.  The next kernel must integrate
with this fine intertwiner still present (or use an equivalent side-complete
collared packet); routing it through the old four-preimage face carrier is
impossible.

## Axiom gate

Constructive finite-list extraction only.  No `Classical.*`, `sorry`,
`native_decide`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2OuterRawRowMassCounterexample

namespace YMGap.Continuum.BF4SU2OuterFineIntertwinerRetainedCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2OuterFineWitnessRoutingReduction
open YMGap.Continuum.BF4SU2OuterJointCarrierEnumeration
open YMGap.Continuum.BF4SU2OuterPhysicalMarkovKernelFrontier
open YMGap.Continuum.BF4SU2OuterPositiveRowClosureReduction
open YMGap.Continuum.BF4SU2OuterRawRowMassCounterexample
open YMGap.Continuum.BF4SU2OuterBinaryLayerCounterexample
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- One literal fine link-intertwiner assignment, retained together with
kernel-checked membership in the complete finite fine carrier. -/
structure WholeSlabRetainedFineIntertwiner
    (S : SlabScalePair) (fineState : EdgeLabelling) : Type where
  witness : SlabFusionWitnessAssignment
  witness_mem :
    witness ∈ slabFineFusionWitnesses S.fine fineState

/-- A positive physical summand constructively supplies one member of the
retained fine-intertwiner carrier. -/
def WholeSlabRetainedFineIntertwiner.ofPositivePhysicalTerm
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    WholeSlabRetainedFineIntertwiner S fineState :=
  let selected :=
    positivePhysicalTermFineFusionWitness
      S.fine fineState hpositive
  { witness := selected.1
    witness_mem := selected.2 }

/-- The retained carrier is inhabited on every positive higher-cutoff row.
Unlike `SU2OuterRawRowMassPositive`, this family has a canonical
construction. -/
structure SU2OuterFineIntertwinerCarrier
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) : Type where
  retain :
    ∀ K source,
      K ≠ 1 →
      source ∈
        (su2OuterScalePair
          G g hg candidate hcandidate K).fine.physicalLabellings →
      (0 : Q') <
        (su2OuterScalePair
          G g hg candidate hcandidate K).fine.physicalTerm source →
      WholeSlabRetainedFineIntertwiner
        (su2OuterScalePair
          G g hg candidate hcandidate K) source

/-- Canonical all-row inhabitant: physical positivity itself performs the
finite witness extraction. -/
def canonicalSU2OuterFineIntertwinerCarrier
    (G : CutoffOneGeometry)
    (g : Q') (hg : (0 : Q') ≤ g)
    (candidate : Q') (hcandidate : (0 : Q') < candidate) :
    SU2OuterFineIntertwinerCarrier
      G g hg candidate hcandidate where
  retain := by
    intro K source _ _ hpositive
    exact
      WholeSlabRetainedFineIntertwiner.ofPositivePhysicalTerm
        hpositive

/-- The semantic target/channel/link selection required by the old carrier
is empty on the same row. -/
theorem collarState_oldJointSelection_uninhabited :
    WholeSlabJointChannelSelection
      counterScalePair collarState → False :=
  no_collarState_jointChannelSelection

/-- Exact strict-enlargement certificate: the retained fine carrier is
constructed from the positive fine term by
`WholeSlabRetainedFineIntertwiner.ofPositivePhysicalTerm`, while the
four-preimage coarse joint carrier is not.  The positive term is stored
rather than eagerly normalizing the enormous first witness. -/
structure CollarCarrierStrictEnlargement : Type where
  fineTerm_positive :
    (0 : Q') <
      counterScalePair.fine.physicalTerm collarState
  oldSelection_empty :
    WholeSlabJointChannelSelection
      counterScalePair collarState → False

def collarCarrierStrictEnlargement :
    CollarCarrierStrictEnlargement where
  fineTerm_positive := collarState_physicalTerm_pos
  oldSelection_empty := collarState_oldJointSelection_uninhabited

#print axioms WholeSlabRetainedFineIntertwiner.ofPositivePhysicalTerm
#print axioms canonicalSU2OuterFineIntertwinerCarrier
#print axioms collarState_oldJointSelection_uninhabited

end YMGap.Continuum.BF4SU2OuterFineIntertwinerRetainedCarrier
