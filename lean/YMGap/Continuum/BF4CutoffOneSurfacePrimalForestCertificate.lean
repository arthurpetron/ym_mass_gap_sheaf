/-
# Primal maximal-forest certificates for the cutoff-one BF4 surfaces

The remaining selected-face Haar contraction is most naturally attacked by
maximal-tree gauge fixing on each connected component of the surface's
one-skeleton.  This module supplies the finite geometric input for that
argument.  It reconstructs the actual 16-vertex/32-edge unit-four-cube graph
from the already certified face-incidence rows and runs deterministic
union-find on every one of the 128 closed binary surfaces.

The resulting checker certifies that the chosen forest is a duplicate-free
subset of the selected physical edges, spans each selected component, and
leaves exactly `E - V + C` chord edges.  No Haar value is asserted here.

## Axiom gate

Finite `Nat`, `List`, bit-mask, and exact Boolean computation only.  No
Classical.*, native_decide, sorry, custom axiom, choice, or noncomputable
declaration.
-/

import YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate

namespace YMGap.Continuum.BF4CutoffOneSurfacePrimalForestCertificate

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate

/-- Endpoints of the 32 physical hypercube edges, in exactly the order of
`edgeIncidenceMasks`. -/
def hypercubeEdgeEndpoints : List (Nat × Nat) :=
  [(0, 8), (0, 4), (0, 2), (0, 1),
   (1, 9), (1, 5), (1, 3), (2, 10),
   (2, 6), (2, 3), (3, 11), (3, 7),
   (4, 12), (4, 6), (4, 5), (5, 13),
   (5, 7), (6, 14), (6, 7), (7, 15),
   (8, 12), (8, 10), (8, 9), (9, 13),
   (9, 11), (10, 14), (10, 11), (11, 15),
   (12, 14), (12, 13), (13, 15), (14, 15)]

/-- Recover the endpoints of an edge from the certified face-incidence rows:
an endpoint vertex contains all three faces incident on that edge. -/
def incidenceEndpointVertexIds (edgeId : Nat) : List Nat :=
  let edgeMask := edgeIncidenceMasks.getD edgeId 0
  (List.range 16).filter fun vertexId =>
    decide
      (maskIntersectionCount edgeMask
          (vertexIncidenceMasks.getD vertexId 0) = 3)

def hypercubeEdgeEndpointIncidenceCheck : Bool :=
  (List.range 32).all fun edgeId =>
    let endpoints := hypercubeEdgeEndpoints.getD edgeId (0, 0)
    decide
      (incidenceEndpointVertexIds edgeId = [endpoints.1, endpoints.2] ∧
        endpoints.1 < 16 ∧ endpoints.2 < 16 ∧
        endpoints.1 ≠ endpoints.2)

/-- The displayed graph is definitionally tied to the existing 32-by-24 and
16-by-24 physical incidence tables. -/
theorem hypercubeEdgeEndpointIncidenceCheck_true :
    hypercubeEdgeEndpointIncidenceCheck = true := by
  decide

def surfaceSelectedEdgeIds (mask : Nat) : List Nat :=
  (List.range 32).filter fun edgeId =>
    decide
      (0 < maskIntersectionCount (edgeIncidenceMasks.getD edgeId 0) mask)

def surfaceSelectedVertexIds (mask : Nat) : List Nat :=
  (List.range 16).filter fun vertexId =>
    decide
      (0 < maskIntersectionCount (vertexIncidenceMasks.getD vertexId 0) mask)

structure SurfaceForestState where
  labels : List Nat
  forestRev : List Nat
  deriving DecidableEq, Repr

def initialSurfaceForestState : SurfaceForestState :=
  { labels := List.range 16
    forestRev := [] }

/-- Union the two endpoint components precisely when a selected edge joins
different current components. -/
def surfaceForestStep (mask : Nat)
    (state : SurfaceForestState) (edgeId : Nat) : SurfaceForestState :=
  if edgeId ∈ surfaceSelectedEdgeIds mask then
    let endpoints := hypercubeEdgeEndpoints.getD edgeId (0, 0)
    let leftLabel := state.labels.getD endpoints.1 endpoints.1
    let rightLabel := state.labels.getD endpoints.2 endpoints.2
    if leftLabel = rightLabel then state
    else
      { labels := state.labels.map fun label =>
          if label = rightLabel then leftLabel else label
        forestRev := edgeId :: state.forestRev }
  else state

def surfaceForestState (mask : Nat) : SurfaceForestState :=
  (List.range 32).foldl (surfaceForestStep mask)
    initialSurfaceForestState

def surfacePrimalForestEdgeIds (mask : Nat) : List Nat :=
  (surfaceForestState mask).forestRev.reverse

def surfacePrimalChordEdgeIds (mask : Nat) : List Nat :=
  (surfaceSelectedEdgeIds mask).filter fun edgeId =>
    decide (edgeId ∉ surfacePrimalForestEdgeIds mask)

/-- Component representatives of precisely the selected vertices. -/
def surfacePrimalComponentLabels (mask : Nat) : List Nat :=
  ((surfaceSelectedVertexIds mask).map fun vertexId =>
    (surfaceForestState mask).labels.getD vertexId vertexId).eraseDups

def surfacePrimalComponentCount (mask : Nat) : Nat :=
  (surfacePrimalComponentLabels mask).length

/-! ## Rooted paths inside the checked forest -/

private def replaceAt (index : Nat) (value : α) : List α → List α
  | [] => []
  | head :: rest =>
      match index with
      | 0 => value :: rest
      | next + 1 => head :: replaceAt next value rest

abbrev SurfaceForestPath := List (Nat × Bool)

/-- Initially each component representative knows its empty rooted path. -/
def initialSurfaceForestPaths (mask : Nat) :
    List (Option SurfaceForestPath) :=
  (List.range 16).map fun vertexId =>
    if vertexId ∈ surfacePrimalComponentLabels mask
    then some []
    else none

/-- One relaxation across a forest edge.  `false` traverses the displayed
endpoint orientation; `true` traverses it backwards. -/
def extendSurfaceForestPaths
    (paths : List (Option SurfaceForestPath)) (edgeId : Nat) :
    List (Option SurfaceForestPath) :=
  let endpoints := hypercubeEdgeEndpoints.getD edgeId (0, 0)
  match paths.getD endpoints.1 none, paths.getD endpoints.2 none with
  | some path, none =>
      replaceAt endpoints.2 (some (path ++ [(edgeId, false)])) paths
  | none, some path =>
      replaceAt endpoints.1 (some (path ++ [(edgeId, true)])) paths
  | _, _ => paths

def relaxSurfaceForestPaths (mask : Nat)
    (paths : List (Option SurfaceForestPath)) :
    List (Option SurfaceForestPath) :=
  (surfacePrimalForestEdgeIds mask).foldl
    extendSurfaceForestPaths paths

/-- Sixteen relaxation passes suffice for every forest on sixteen vertices. -/
def surfacePrimalRootPaths (mask : Nat) :
    List (Option SurfaceForestPath) :=
  (List.range 16).foldl
    (fun paths _ => relaxSurfaceForestPaths mask paths)
    (initialSurfaceForestPaths mask)

def walkSurfaceForestPath : Nat → SurfaceForestPath → Option Nat
  | vertex, [] => some vertex
  | vertex, (edgeId, reverse) :: rest =>
      let endpoints := hypercubeEdgeEndpoints.getD edgeId (0, 0)
      if reverse then
        if vertex = endpoints.2
        then walkSurfaceForestPath endpoints.1 rest
        else none
      else if vertex = endpoints.1
        then walkSurfaceForestPath endpoints.2 rest
        else none

def surfacePrimalRootPathsCheck (mask : Nat) : Bool :=
  let paths := surfacePrimalRootPaths mask
  let forest := surfacePrimalForestEdgeIds mask
  decide (paths.length = 16) &&
    (surfaceSelectedVertexIds mask).all fun vertexId =>
      match paths.getD vertexId none with
      | none => false
      | some path =>
          let root := (surfaceForestState mask).labels.getD vertexId vertexId
          decide
            (walkSurfaceForestPath root path = some vertexId ∧
              ∀ entry, entry ∈ path → entry.1 ∈ forest)

/-- A self-contained check of the maximal-forest facts later gauge transport
may consume. -/
def surfacePrimalForestCheck (mask : Nat) : Bool :=
  let selectedEdges := surfaceSelectedEdgeIds mask
  let selectedVertices := surfaceSelectedVertexIds mask
  let forest := surfacePrimalForestEdgeIds mask
  let chords := surfacePrimalChordEdgeIds mask
  let finalLabels := (surfaceForestState mask).labels
  decide
    (selectedEdges.length = surfaceEdgeCount mask ∧
      selectedVertices.length = surfaceVertexCount mask ∧
      forest.Nodup ∧
      (∀ edgeId, edgeId ∈ forest → edgeId ∈ selectedEdges) ∧
      (∀ edgeId, edgeId ∈ selectedEdges →
        let endpoints := hypercubeEdgeEndpoints.getD edgeId (0, 0)
        finalLabels.getD endpoints.1 endpoints.1 =
          finalLabels.getD endpoints.2 endpoints.2) ∧
      forest.length + surfacePrimalComponentCount mask =
        surfaceVertexCount mask ∧
      chords.length =
        surfaceEdgeCount mask - surfaceVertexCount mask +
          surfacePrimalComponentCount mask ∧
      forest.length + chords.length = surfaceEdgeCount mask)

def binarySurfacePrimalForestCheck : Bool :=
  binarySurfaceMasks.all surfacePrimalForestCheck

def binarySurfacePrimalRootPathsCheck : Bool :=
  binarySurfaceMasks.all surfacePrimalRootPathsCheck

/-- All 128 actual closed BF4 surfaces carry a checked deterministic maximal
forest, including the empty forest on the empty surface. -/
theorem binarySurfacePrimalForestCheck_true :
    binarySurfacePrimalForestCheck = true := by
  decide

/-- The maximal forests have explicit, orientation-aware rooted paths to
every selected physical vertex. -/
theorem binarySurfacePrimalRootPathsCheck_true :
    binarySurfacePrimalRootPathsCheck = true := by
  decide

theorem surfacePrimalForestCheck_of_mem
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    surfacePrimalForestCheck mask = true :=
  List.all_eq_true.mp binarySurfacePrimalForestCheck_true mask hmask

/-- The checked forest/chord count identity in theorem form. -/
theorem surfacePrimalChordEdgeCount
    (mask : Nat) (hmask : mask ∈ binarySurfaceMasks) :
    (surfacePrimalChordEdgeIds mask).length =
      surfaceEdgeCount mask - surfaceVertexCount mask +
        surfacePrimalComponentCount mask := by
  have hcheck := of_decide_eq_true
    (surfacePrimalForestCheck_of_mem mask hmask)
  exact hcheck.2.2.2.2.2.2.1

end YMGap.Continuum.BF4CutoffOneSurfacePrimalForestCertificate

#print axioms YMGap.Continuum.BF4CutoffOneSurfacePrimalForestCertificate.hypercubeEdgeEndpointIncidenceCheck_true
#print axioms YMGap.Continuum.BF4CutoffOneSurfacePrimalForestCertificate.binarySurfacePrimalForestCheck_true
#print axioms YMGap.Continuum.BF4CutoffOneSurfacePrimalForestCertificate.binarySurfacePrimalRootPathsCheck_true
#print axioms YMGap.Continuum.BF4CutoffOneSurfacePrimalForestCertificate.surfacePrimalChordEdgeCount
