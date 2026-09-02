/-
# Accepted vacuum completion by canonical paired peeling

The accepted paired canonical peeling may be run on an arbitrary accepted
expanded source paired with itself and on the complete physical face list.
Its first terminal replica is still an accepted expanded source.  Terminality
sets every listed physical face to zero, while bounded-carrier soundness sets
every unlisted face to zero.  The terminal physical field is therefore the
literal vacuum labelling, and its retained assignment is an accepted fusion
witness above that vacuum.

This is an existence and carrier theorem.  It does not yet compare weights
along the accepted path or identify the simultaneous threshold-truncated core
with an accepted intermediate state.

Constructive contract: deterministic well-founded peeling and explicit finite
carrier soundness only; no choice, `Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling

namespace YMGap.Continuum.CompactDualSlabAcceptedVacuumCompletion

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator

/-! ## 1. Canonical accepted completion -/

/-- The canonical accepted paired peeling of a source paired with itself over
the complete corrected-slab physical face list. -/
def slabExpandedFineSourceVacuumPeeling
    (D : SlabPhysicalData) (source : SlabExpandedFineSourceEntry D) :
    SlabAcceptedPairedCanonicalPeelingOutput D :=
  slabAcceptedPairCanonicalPeeling D D.faceEdges
    (fun faceId hface => by
      simpa only [SlabPhysicalData.faceEdges] using hface)
    (source, source)

/-- The first accepted terminal replica of the canonical self-paired peeling. -/
def slabExpandedFineSourceAcceptedVacuumCompletion
    (D : SlabPhysicalData) (source : SlabExpandedFineSourceEntry D) :
    SlabExpandedFineSourceEntry D :=
  (slabExpandedFineSourceVacuumPeeling D source).1.1

/-! ## 2. Literal vacuum target -/

/-- The terminal accepted physical field is the literal zero labelling on
every face, both inside and outside the finite physical carrier. -/
theorem slabExpandedFineSourceAcceptedVacuumCompletion_physical_eq_zero
    (D : SlabPhysicalData) (source : SlabExpandedFineSourceEntry D) :
    (slabExpandedFineSourceAcceptedVacuumCompletion D source).1.1 =
      zeroEdgeLabelling := by
  funext faceId
  by_cases hface : faceId ∈ D.faceEdges
  · have hzero :=
      (slabAcceptedPairCanonicalPeeling_final_zero
        D D.faceEdges
          (fun selectedFaceId hselected => by
            simpa only [SlabPhysicalData.faceEdges] using hselected)
          (source, source) faceId hface).1
    simpa only [slabExpandedFineSourceAcceptedVacuumCompletion,
      slabExpandedFineSourceVacuumPeeling, zeroEdgeLabelling] using hzero
  · have hphysical := acceptedExpandedSourcePhysical_mem
      (slabExpandedFineSourceAcceptedVacuumCompletion D source)
    have hzero :=
      (boundedEdgeLabellings_sound D.cutoff D.faceEdges
        (slabExpandedFineSourceAcceptedVacuumCompletion D source).1.1
        hphysical).2 faceId hface
    simpa only [zeroEdgeLabelling] using hzero

/-- The retained terminal assignment is a literal accepted fusion witness
above the zero physical field. -/
theorem slabExpandedFineSourceAcceptedVacuumCompletion_assignment_mem
    (D : SlabPhysicalData) (source : SlabExpandedFineSourceEntry D) :
    (slabExpandedFineSourceAcceptedVacuumCompletion D source).1.2 ∈
      slabFineFusionWitnesses D zeroEdgeLabelling := by
  have haccepted := acceptedExpandedSourceAssignment_mem
    (slabExpandedFineSourceAcceptedVacuumCompletion D source)
  simpa only [slabFineFusionWitnesses,
    slabExpandedFineSourceAcceptedVacuumCompletion_physical_eq_zero]
    using haccepted

/-- Pairing the literal vacuum field with the terminal assignment produces an
actual member of the expanded accepted source carrier. -/
theorem slabExpandedFineSourceAcceptedVacuumCompletion_mem
    (D : SlabPhysicalData) (source : SlabExpandedFineSourceEntry D) :
    (zeroEdgeLabelling,
      (slabExpandedFineSourceAcceptedVacuumCompletion D source).1.2) ∈
        slabExpandedFineSources D := by
  apply mem_slabExpandedFineSources_iff.mpr
  constructor
  · rw [← slabExpandedFineSourceAcceptedVacuumCompletion_physical_eq_zero
      D source]
    exact acceptedExpandedSourcePhysical_mem
      (slabExpandedFineSourceAcceptedVacuumCompletion D source)
  · exact slabExpandedFineSourceAcceptedVacuumCompletion_assignment_mem
      D source

#print axioms slabExpandedFineSourceVacuumPeeling
#print axioms slabExpandedFineSourceAcceptedVacuumCompletion
#print axioms slabExpandedFineSourceAcceptedVacuumCompletion_physical_eq_zero
#print axioms slabExpandedFineSourceAcceptedVacuumCompletion_assignment_mem
#print axioms slabExpandedFineSourceAcceptedVacuumCompletion_mem

end YMGap.Continuum.CompactDualSlabAcceptedVacuumCompletion
