/-
# Reversible physical-terminal partner on one canonical link

Write `E` for same-slot crossing of an internal edge and `M` for the local
trivalent mate.  A forward internal strand step is `A = M ∘ E`.  Since both
`E` and `M` are involutions, the reverse of one step is again a forward step:

    M (A x) = E x,       A (E x) = M x.

This module lifts that identity from one port to a retained strand path.
Starting at the local mate of a physical terminal, terminal extraction gives
its partner.  Reversing the path constructs a path back, and determinism of
the internal advance proves that the partner operation is involutive.

Constructive contract: structural recursion on retained path witnesses and
the two explicit involutions only.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CanonicalLinkStrandTerminal

namespace YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkInternalStrandContinuation
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CanonicalLinkStrandTerminal
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution

/-! ## 1. Deterministic internal-advance paths -/

/-- Reflexive transitive closure of the exact full internal advance. -/
inductive CanonicalInternalAdvancePath
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true) :
    ResolvedNetworkPort
        (canonicalLinkResolvedStrandNetwork
          degree external auxiliary hallowed) →
      ResolvedNetworkPort
        (canonicalLinkResolvedStrandNetwork
          degree external auxiliary hallowed) → Type
  | refl (port : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) :
      CanonicalInternalAdvancePath hdegree hallowed port port
  | step
      (source : ResolvedNetworkPort
        (canonicalLinkResolvedStrandNetwork
          degree external auxiliary hallowed))
      (hinternal : source.edgeId ∈ canonicalInternalFusionEdges degree)
      (finish : ResolvedNetworkPort
        (canonicalLinkResolvedStrandNetwork
          degree external auxiliary hallowed))
      (tail : CanonicalInternalAdvancePath hdegree hallowed
        (canonicalInternalAdvancePort
          hdegree hallowed source hinternal) finish) :
      CanonicalInternalAdvancePath hdegree hallowed source finish

/-- Concatenate two exact internal-advance paths. -/
def CanonicalInternalAdvancePath.append
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    {start middle finish : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)}
    (left : CanonicalInternalAdvancePath
      hdegree hallowed start middle)
    (right : CanonicalInternalAdvancePath
      hdegree hallowed middle finish) :
    CanonicalInternalAdvancePath hdegree hallowed start finish :=
  match left with
  | .refl _ => right
  | .step source hinternal _ tail =>
      .step source hinternal finish (tail.append right)

/-- Forget the physical endpoint refinement of a witnessed terminal path. -/
def canonicalStrandPathToAdvancePath
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    {start : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)}
    {terminal : CanonicalPhysicalStrandPort external auxiliary hallowed} :
    CanonicalStrandPathToPhysical hdegree hallowed start terminal →
      CanonicalInternalAdvancePath hdegree hallowed start terminal.1
  | .stop terminal => .refl terminal.1
  | .advance source hinternal terminal tail =>
      .step source hinternal terminal.1
        (canonicalStrandPathToAdvancePath tail)

/-- Refine an internal-advance path whose ordinary endpoint is physically
labelled into the terminal-path type. -/
def canonicalAdvancePathToPhysical
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    {start finish : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)}
    (path : CanonicalInternalAdvancePath
      hdegree hallowed start finish) :
    (hphysical : finish.edgeId < degree) →
      CanonicalStrandPathToPhysical hdegree hallowed start
        (⟨finish, hphysical⟩ : CanonicalPhysicalStrandPort
          external auxiliary hallowed) :=
  match path with
  | .refl port => fun hphysical => .stop ⟨port, hphysical⟩
  | .step source hinternal finish tail => fun hphysical =>
      .advance source hinternal ⟨finish, hphysical⟩
        (canonicalAdvancePathToPhysical tail hphysical)

/-! ## 2. Determinism of physical endpoints -/

/-- Two deterministic internal-advance paths from the same start cannot end
at two different physical ordinary ports. -/
theorem canonicalInternalAdvancePath_physical_finish_unique
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    {start left right : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)}
    (leftPath : CanonicalInternalAdvancePath
      hdegree hallowed start left)
    (rightPath : CanonicalInternalAdvancePath
      hdegree hallowed start right)
    (hleftPhysical : left.edgeId < degree)
    (hrightPhysical : right.edgeId < degree) :
    left = right := by
  induction leftPath with
  | refl port =>
      cases rightPath with
      | refl => rfl
      | step source hinternal finish tail =>
          exact False.elim
            ((canonicalInternalFusionEdge_not_lt hdegree hinternal)
              hleftPhysical)
  | step source hinternal left tail ih =>
      cases rightPath with
      | refl =>
          exact False.elim
            ((canonicalInternalFusionEdge_not_lt hdegree hinternal)
              hrightPhysical)
      | step source hinternal' right tail' =>
          exact ih tail' hleftPhysical

/-- Two witnessed strand paths from the same start have the same refined
physical terminal. -/
theorem canonicalStrandPath_terminal_unique
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    {start : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)}
    {left right : CanonicalPhysicalStrandPort external auxiliary hallowed}
    (leftPath : CanonicalStrandPathToPhysical
      hdegree hallowed start left)
    (rightPath : CanonicalStrandPathToPhysical
      hdegree hallowed start right) :
    left = right := by
  apply Subtype.ext
  exact canonicalInternalAdvancePath_physical_finish_unique
    (canonicalStrandPathToAdvancePath leftPath)
    (canonicalStrandPathToAdvancePath rightPath)
    left.2 right.2

/-! ## 3. Reversal of one internal step -/

/-- The raw same-slot crossing port before the following local mate. -/
def canonicalInternalCrossPort
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (source : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hinternal : source.edgeId ∈ canonicalInternalFusionEdges degree) :=
  (canonicalInternalStrandContinue hdegree hallowed hinternal
    (⟨source, rfl⟩ : CanonicalInternalStrandPort
      source.edgeId external auxiliary hallowed)).1

/-- The crossed port stays on the same internal identifier. -/
theorem canonicalInternalCrossPort_edgeId
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (source : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hinternal : source.edgeId ∈ canonicalInternalFusionEdges degree) :
    (canonicalInternalCrossPort
      hdegree hallowed source hinternal).edgeId = source.edgeId :=
  (canonicalInternalStrandContinue hdegree hallowed hinternal
    (⟨source, rfl⟩ : CanonicalInternalStrandPort
      source.edgeId external auxiliary hallowed)).2

/-- Hence the crossed port is still internal. -/
def canonicalInternalCrossPort_internal
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (source : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hinternal : source.edgeId ∈ canonicalInternalFusionEdges degree) :
    (canonicalInternalCrossPort
      hdegree hallowed source hinternal).edgeId ∈
        canonicalInternalFusionEdges degree := by
  rw [canonicalInternalCrossPort_edgeId]
  exact hinternal

/-- A fixed-edge typed internal port is internally classified at its actual
edge identifier. -/
def canonicalTypedInternalPort_internal
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (occurrence : CanonicalInternalStrandPort
      edge external auxiliary hallowed) :
    occurrence.1.edgeId ∈ canonicalInternalFusionEdges degree := by
  rw [occurrence.2]
  exact hedge

/-- The ordinary full advance agrees with continuation at a fixed typed edge. -/
theorem canonicalInternalAdvancePort_of_typed
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (occurrence : CanonicalInternalStrandPort
      edge external auxiliary hallowed) :
    canonicalInternalAdvancePort hdegree hallowed occurrence.1
        (canonicalTypedInternalPort_internal hedge occurrence) =
      (canonicalInternalStrandContinue
        hdegree hallowed hedge occurrence).1.localMate := by
  rcases occurrence with ⟨occurrence, hedgeId⟩
  cases hedgeId
  rfl

/-- Taking the local mate after a full advance recovers the raw crossing
port: `M (A x) = E x`. -/
theorem canonicalInternalAdvancePort_localMate_eq_cross
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (source : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hinternal : source.edgeId ∈ canonicalInternalFusionEdges degree) :
    (canonicalInternalAdvancePort
      hdegree hallowed source hinternal).localMate =
        canonicalInternalCrossPort hdegree hallowed source hinternal :=
  ResolvedNetworkPort.localMate_involutive
    (canonicalInternalCrossPort hdegree hallowed source hinternal)

/-- Advancing from the crossed port reaches the original local mate:
`A (E x) = M x`. -/
theorem canonicalInternalAdvancePort_cross_eq_localMate
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (source : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hinternal : source.edgeId ∈ canonicalInternalFusionEdges degree) :
    canonicalInternalAdvancePort hdegree hallowed
        (canonicalInternalCrossPort hdegree hallowed source hinternal)
        (canonicalInternalCrossPort_internal
          hdegree hallowed source hinternal) =
      source.localMate := by
  let original : CanonicalInternalStrandPort
      source.edgeId external auxiliary hallowed := ⟨source, rfl⟩
  let crossed := canonicalInternalStrandContinue
    hdegree hallowed hinternal original
  change canonicalInternalAdvancePort hdegree hallowed crossed.1
      (canonicalInternalCrossPort_internal
        hdegree hallowed source hinternal) = source.localMate
  rw [canonicalInternalAdvancePort_of_typed
    hdegree hallowed hinternal crossed]
  exact congrArg
    (fun occurrence : CanonicalInternalStrandPort
        source.edgeId external auxiliary hallowed => occurrence.1.localMate)
    (canonicalInternalStrandContinue_involutive hdegree hallowed hinternal
      original)

/-- The reverse of one full internal step is itself a forward internal step
between the local mates of the two endpoints. -/
def canonicalInternalAdvanceReverseStep
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (source : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hinternal : source.edgeId ∈ canonicalInternalFusionEdges degree) :
    CanonicalInternalAdvancePath hdegree hallowed
      (canonicalInternalAdvancePort
        hdegree hallowed source hinternal).localMate
      source.localMate := by
  rw [canonicalInternalAdvancePort_localMate_eq_cross]
  refine .step
    (canonicalInternalCrossPort hdegree hallowed source hinternal)
    (canonicalInternalCrossPort_internal
      hdegree hallowed source hinternal)
    source.localMate ?_
  rw [canonicalInternalAdvancePort_cross_eq_localMate]
  exact .refl source.localMate

/-! ## 4. Reverse whole paths and construct the physical partner -/

/-- Reverse a terminal path after applying the local mate at both ends. -/
def canonicalStrandPathReverseToMatePath
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    {start : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)}
    {terminal : CanonicalPhysicalStrandPort external auxiliary hallowed} :
    (path : CanonicalStrandPathToPhysical
      hdegree hallowed start terminal) →
    CanonicalInternalAdvancePath hdegree hallowed
      terminal.1.localMate start.localMate
  | .stop terminal => .refl terminal.1.localMate
  | .advance source hinternal terminal tail =>
      (canonicalStrandPathReverseToMatePath tail).append
        (canonicalInternalAdvanceReverseStep
          hdegree hallowed source hinternal)

/-- The physical terminal connected to `terminal`: start at its local mate
and follow the unique internal strand to the other physical end. -/
def canonicalPhysicalStrandPartner
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (terminal : CanonicalPhysicalStrandPort external auxiliary hallowed) :
    CanonicalPhysicalStrandPort external auxiliary hallowed :=
  canonicalLinkStrandTerminal hdegree hallowed terminal.1.localMate

/-- The extractor retains the forward path from a physical terminal's local
mate to its partner. -/
def canonicalPhysicalStrandPartner_path
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (terminal : CanonicalPhysicalStrandPort external auxiliary hallowed) :
    CanonicalStrandPathToPhysical hdegree hallowed terminal.1.localMate
      (canonicalPhysicalStrandPartner hdegree hallowed terminal) :=
  (canonicalLinkStrandTerminalWitness
    hdegree hallowed terminal.1.localMate).2

/-- Reversing the retained partner path gives a valid path from the partner's
local mate back to the original physical terminal. -/
def canonicalPhysicalStrandPartner_reversePath
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (terminal : CanonicalPhysicalStrandPort external auxiliary hallowed) :
    CanonicalStrandPathToPhysical hdegree hallowed
      (canonicalPhysicalStrandPartner
        hdegree hallowed terminal).1.localMate terminal := by
  have reversed :=
    canonicalStrandPathReverseToMatePath
      (canonicalPhysicalStrandPartner_path
        hdegree hallowed terminal)
  rw [ResolvedNetworkPort.localMate_involutive terminal.1] at reversed
  exact canonicalAdvancePathToPhysical reversed terminal.2

/-- The physical-terminal partner operation is an involution. -/
theorem canonicalPhysicalStrandPartner_involutive
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (terminal : CanonicalPhysicalStrandPort external auxiliary hallowed) :
    canonicalPhysicalStrandPartner hdegree hallowed
        (canonicalPhysicalStrandPartner hdegree hallowed terminal) =
      terminal :=
  canonicalStrandPath_terminal_unique
    (canonicalPhysicalStrandPartner_path hdegree hallowed
      (canonicalPhysicalStrandPartner hdegree hallowed terminal))
    (canonicalPhysicalStrandPartner_reversePath
      hdegree hallowed terminal)

#print axioms CanonicalInternalAdvancePath
#print axioms CanonicalInternalAdvancePath.append
#print axioms canonicalStrandPathToAdvancePath
#print axioms canonicalAdvancePathToPhysical
#print axioms canonicalInternalAdvancePath_physical_finish_unique
#print axioms canonicalStrandPath_terminal_unique
#print axioms canonicalInternalCrossPort
#print axioms canonicalInternalCrossPort_edgeId
#print axioms canonicalInternalCrossPort_internal
#print axioms canonicalTypedInternalPort_internal
#print axioms canonicalInternalAdvancePort_of_typed
#print axioms canonicalInternalAdvancePort_localMate_eq_cross
#print axioms canonicalInternalAdvancePort_cross_eq_localMate
#print axioms canonicalInternalAdvanceReverseStep
#print axioms canonicalStrandPathReverseToMatePath
#print axioms canonicalPhysicalStrandPartner
#print axioms canonicalPhysicalStrandPartner_path
#print axioms canonicalPhysicalStrandPartner_reversePath
#print axioms canonicalPhysicalStrandPartner_involutive

end YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
