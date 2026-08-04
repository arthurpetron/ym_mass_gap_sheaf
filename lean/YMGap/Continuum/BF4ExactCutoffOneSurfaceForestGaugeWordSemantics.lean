/-
# Finite word semantics of the BF4 surface forest gauge

The inverse orientation-aware translation ledger substitutes every old chord
by `P(tail)^-1 * U * P(head)`.  This module performs that substitution at the
free oriented-edge-word level, cancels adjacent inverse tree edges with an
executable stack reducer, cyclically removes the remaining rooted conjugacy,
and compares the result with the physical chord word obtained by deleting
the checked primal forest.  The cyclic step is exactly the basepoint
invariance of the traced face character.

The all-surface certificate is the finite geometric content of the remaining
polynomial semantic lift.  It deliberately does not identify quaternion
polynomials modulo the unit-sphere ideal; that algebraic lift remains the
next theorem.

## Axiom gate

Finite lists, booleans, and the checked forest geometry only.  No
`Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation

namespace YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordSemantics

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4CutoffOneSurfacePrimalForestCertificate
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGauge
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeTranslation
open YMGap.Continuum.BF4GeometricSpinNetworkMehler

abbrev OrientedSurfaceEdge := Nat × Bool

def inverseSurfaceWord (word : List OrientedSurfaceEdge) :
    List OrientedSurfaceEdge :=
  word.reverse.map fun entry => (entry.1, !entry.2)

/-- The old oriented chord expressed through its based-cycle coordinate. -/
def surfaceChordInverseGaugeWord
    (mask edgeId : Nat) : List OrientedSurfaceEdge :=
  let endpoints := hypercubeEdgeEndpoints.getD edgeId (0, 0)
  inverseSurfaceWord (surfaceRootPath mask endpoints.1) ++
    [(edgeId, false)] ++
    surfaceRootPath mask endpoints.2

def substituteSurfaceGaugeEntry
    (mask : Nat) (entry : OrientedSurfaceEdge) :
    List OrientedSurfaceEdge :=
  if entry.1 ∈ surfaceForestGaugeChordEdgeIds mask then
    if entry.2 then
      inverseSurfaceWord (surfaceChordInverseGaugeWord mask entry.1)
    else surfaceChordInverseGaugeWord mask entry.1
  else [entry]

def substituteSurfaceGaugeWord
    (mask : Nat) (word : List OrientedSurfaceEdge) :
    List OrientedSurfaceEdge :=
  word.flatMap (substituteSurfaceGaugeEntry mask)

/-- Stack reducer for the free involutive edge alphabet.  The stack is kept
in reverse word order so a newly adjacent inverse pair cancels immediately. -/
def freeSurfaceReduceStep
    (stack : List OrientedSurfaceEdge) (entry : OrientedSurfaceEdge) :
    List OrientedSurfaceEdge :=
  match stack with
  | [] => [entry]
  | head :: rest =>
      if head.1 = entry.1 ∧ head.2 ≠ entry.2 then rest
      else entry :: stack

def freeSurfaceReduce (word : List OrientedSurfaceEdge) :
    List OrientedSurfaceEdge :=
  (word.foldl freeSurfaceReduceStep []).reverse

/-- Remove one inverse pair at the two ends of a linearly reduced word. -/
def cancelSurfaceCyclicBoundary :
    List OrientedSurfaceEdge → Option (List OrientedSurfaceEdge)
  | [] => none
  | [_] => none
  | first :: rest =>
      match rest.reverse with
      | [] => none
      | last :: reverseMiddle =>
          if first.1 = last.1 ∧ first.2 ≠ last.2
          then some reverseMiddle.reverse
          else none

/-- Fuel-bounded cyclic reduction.  Each successful step removes two
letters, so the initial word length is more than sufficient fuel. -/
def cyclicFreeSurfaceReduceAux :
    Nat → List OrientedSurfaceEdge → List OrientedSurfaceEdge
  | 0, word => word
  | fuel + 1, word =>
      match cancelSurfaceCyclicBoundary word with
      | none => word
      | some inner => cyclicFreeSurfaceReduceAux fuel inner

/-- Free reduction modulo the conjugacy that leaves a traced face holonomy
unchanged. -/
def cyclicFreeSurfaceReduce (word : List OrientedSurfaceEdge) :
    List OrientedSurfaceEdge :=
  let reduced := freeSurfaceReduce word
  cyclicFreeSurfaceReduceAux reduced.length reduced

/-- The unrenumbered physical chord word underlying the compact forest-gauge
factor. -/
def surfaceForestGaugePhysicalWord
    (mask : Nat) (word : List OrientedSurfaceEdge) :
    List OrientedSurfaceEdge :=
  word.filter fun entry =>
    decide (entry.1 ∈ surfaceForestGaugeChordEdgeIds mask)

def surfaceForestGaugeFaceWordSemanticCheck
    (mask faceId : Nat) : Bool :=
  decide
    (cyclicFreeSurfaceReduce
        (substituteSurfaceGaugeWord mask
          (hypercubeFaceWords.getD faceId [])) =
      surfaceForestGaugePhysicalWord mask
        (hypercubeFaceWords.getD faceId []))

def binarySurfaceForestGaugeWordSemanticCheck : Bool :=
  binarySurfaceMasks.all fun mask =>
    (surfaceSelectedCompactFaceIds mask).all fun faceId =>
      surfaceForestGaugeFaceWordSemanticCheck mask faceId

/-- Every selected face of every certified surface cyclically reduces to
exactly its checked physical chord word after the inverse rooted-path
substitution. -/
theorem binarySurfaceForestGaugeWordSemanticCheck_true :
    binarySurfaceForestGaugeWordSemanticCheck = true := by
  decide

theorem surfaceForestGaugeFaceWordSemanticCheck_of_mem
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks)
    (faceId : Nat) (hface : faceId ∈ surfaceSelectedCompactFaceIds mask) :
    surfaceForestGaugeFaceWordSemanticCheck mask faceId = true :=
  List.all_eq_true.mp
    (List.all_eq_true.mp
      binarySurfaceForestGaugeWordSemanticCheck_true mask hmask)
    faceId hface

end YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordSemantics

#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordSemantics.binarySurfaceForestGaugeWordSemanticCheck_true
#print axioms YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordSemantics.surfaceForestGaugeFaceWordSemanticCheck_of_mem
