/-
# Exact cutoff-two vacuum-column sparse geometry

This file fixes the 24-variable ordering and the 48 active lower-link scopes
used by the external exact-arithmetic contraction at half-extent zero.  The
tables below are not trusted assumptions: Lean evaluates them against the
production corrected-slab face and link enumerations.

The active scope of a lower link contains only its incident lower faces;
fixed and reflected-upper vacuum labels contribute spin zero.  Every checked
scope has at most four active variables, although the production theorem only
needs the general valence-six bound.

This is finite geometry for `K = 2`, half-extent zero.  It makes no
cutoff-uniform, volume-uniform, or continuum claim.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryFactorGraph

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-- The exact production order of the 24 lower-face variables. -/
def cutoffTwoExpectedLowerFaceIds : List Nat :=
  [0, 1, 3, 9, 10, 12, 18, 19, 21, 27, 28, 30,
   36, 37, 39, 45, 46, 48, 54, 55, 57, 63, 64, 66]

/-- Active-variable scopes in the same order as `centralLowerLinks 0`.
The entries are indices into `cutoffTwoExpectedLowerFaceIds`. -/
def cutoffTwoExpectedActiveLinkVariableScopes : List (List Nat) :=
  [[0, 1], [0, 2], [0, 6, 7], [0, 12, 14],
   [1, 2], [1, 3, 4], [1, 13, 14], [2, 3, 5],
   [2, 7, 8], [3, 7, 9, 10], [3, 14, 15, 17], [4, 5],
   [4], [4, 16, 17], [5], [5, 10, 11],
   [6, 8], [6], [6, 18, 20], [7, 14, 19, 20],
   [8, 9, 11], [8], [9], [9, 20, 21, 23],
   [10], [10, 17, 22, 23], [11], [11],
   [12, 13], [12, 18, 19], [12], [13, 15, 16],
   [13], [15, 19, 21, 22], [15], [16],
   [16], [17], [18], [18], [19], [20],
   [21], [21], [22], [22], [23], [23]]

/-- The same 48 scopes expressed as production slab plaquette identifiers. -/
def cutoffTwoExpectedActiveLinkFaceIds : List (List Nat) :=
  [[0, 1], [0, 3], [0, 18, 19], [0, 36, 39],
   [1, 3], [1, 9, 10], [1, 37, 39], [3, 9, 12],
   [3, 19, 21], [9, 19, 27, 28], [9, 39, 45, 48], [10, 12],
   [10], [10, 46, 48], [12], [12, 28, 30],
   [18, 21], [18], [18, 54, 57], [19, 39, 55, 57],
   [21, 27, 30], [21], [27], [27, 57, 63, 66],
   [28], [28, 48, 64, 66], [30], [30],
   [36, 37], [36, 54, 55], [36], [37, 45, 46],
   [37], [45, 55, 63, 64], [45], [46],
   [46], [48], [54], [54], [55], [57],
   [63], [63], [64], [64], [66], [66]]

/-- Production incident faces that remain active after fixing all non-lower
faces to the vacuum label. -/
def cutoffTwoActiveIncidentFaceIds (link : Z4Link) : List Nat :=
  (slabIncidentPlaqIds 1 link).filter fun faceId =>
    decide (faceId ∈ centralLowerFaceIds 0)

/-- The active scopes calculated directly from production link geometry. -/
def cutoffTwoProductionActiveLinkFaceIds : List (List Nat) :=
  (centralLowerLinks 0).map cutoffTwoActiveIncidentFaceIds

/-- Kernel evaluation of the exact 24-variable production order. -/
theorem cutoffTwoLowerFaceIds_checked :
    centralLowerFaceIds 0 = cutoffTwoExpectedLowerFaceIds := by
  decide

/-- Kernel evaluation of all 48 production lower-link scopes. -/
theorem cutoffTwoActiveLinkFaceIds_checked :
    cutoffTwoProductionActiveLinkFaceIds =
      cutoffTwoExpectedActiveLinkFaceIds := by
  decide

/-- The index scopes map exactly to the checked production face scopes. -/
theorem cutoffTwoVariableScopes_map_to_faceIds :
    cutoffTwoExpectedActiveLinkVariableScopes.map
        (fun scope => scope.map fun index =>
          cutoffTwoExpectedLowerFaceIds.getD index 0) =
      cutoffTwoExpectedActiveLinkFaceIds := by
  decide

theorem cutoffTwoLowerFace_count :
    cutoffTwoExpectedLowerFaceIds.length = 24 := by
  decide

theorem cutoffTwoLowerLink_count :
    cutoffTwoExpectedActiveLinkVariableScopes.length = 48 := by
  decide

theorem cutoffTwoLowerFaceIds_nodup :
    cutoffTwoExpectedLowerFaceIds.Nodup := by
  decide

/-- Executable arity-four check for every active lower-link scope. -/
theorem cutoffTwoActiveLinkScopes_arity_le_four :
    cutoffTwoExpectedActiveLinkVariableScopes.all
      (fun scope => decide (scope.length ≤ 4)) = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGeometry

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGeometry.cutoffTwoLowerFaceIds_checked
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGeometry.cutoffTwoActiveLinkFaceIds_checked
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumGeometry.cutoffTwoVariableScopes_map_to_faceIds
