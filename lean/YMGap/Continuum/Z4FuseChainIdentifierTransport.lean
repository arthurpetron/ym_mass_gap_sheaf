/-
# Identifier transport for the production `fuseChain`

The local fusion calculation is most naturally proved on consecutive
canonical identifiers, whereas the finite box uses global plaquette numbers
and a reserved auxiliary block.  This file proves that this is only a
presentation difference.

First, `fuseChain` and `fuseLabels` are equivariant under every renaming that
is affine with unit slope on the auxiliary block.  Second, a constructive
renaming sends the canonical physical range to an arbitrary input list and
the canonical auxiliary suffix to an arbitrary reserved base.  The final
theorem identifies the canonical resolver, vertex for vertex, with the
actual `linkResolutionVertices` list.

Together with `Z4LinkIdentifierFreshness`, this supplies the structural and
non-aliasing halves of actual link-identifier transport.  It does not perform
the remaining finite Cartesian sums.
-/

import YMGap.Continuum.Z4LinkIdentifierFreshness

namespace YMGap.Continuum.Z4FuseChainIdentifierTransport

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4LinkIdentifierFreshness
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- Apply a numerical edge renaming to all three coordinates of a trivalent
vertex. -/
def mapTrivalentVertex (f : Nat → Nat) (v : TrivalentVertex) :
    TrivalentVertex :=
  (f v.1, f v.2.1, f v.2.2)

/-! ## 1. Generic equivariance of the resolver -/

/-- A fusion chain is equivariant under a renaming that preserves consecutive
successors throughout the auxiliary suffix used by the recursion. -/
theorem map_fuseChain (f : Nat → Nat) (vacuum aux left right : Nat)
    (haux : ∀ j, f (aux + j) = f aux + j) :
    ∀ tail : List Nat,
      (fuseChain vacuum aux left right tail).map (mapTrivalentVertex f) =
        fuseChain (f vacuum) (f aux) (f left) (f right) (tail.map f)
  | [] => by
      simp [fuseChain, mapTrivalentVertex]
  | [last] => by
      simp [fuseChain, mapTrivalentVertex]
  | next :: after :: rest => by
      have haux0 : f (aux + 0) = f aux + 0 := haux 0
      have haux1 : f (aux + 1) = f aux + 1 := haux 1
      have hshift : ∀ j,
          f ((aux + 1) + j) = f (aux + 1) + j := by
        intro j
        calc
          f ((aux + 1) + j) = f (aux + (j + 1)) := by
            congr 1
            omega
          _ = f aux + (j + 1) := haux (j + 1)
          _ = f (aux + 1) + j := by rw [haux1]; omega
      have ih := map_fuseChain f vacuum (aux + 1) aux next hshift
        (after :: rest)
      simp only [fuseChain, List.map_cons]
      rw [ih]
      unfold mapTrivalentVertex
      rw [haux1]
      rfl

/-- The public resolver inherits the same equivariance, including its empty
and repeated-vacuum one-leg base cases. -/
theorem map_fuseLabels (f : Nat → Nat) (vacuum aux : Nat)
    (haux : ∀ j, f (aux + j) = f aux + j) :
    ∀ labels : List Nat,
      (fuseLabels vacuum aux labels).map (mapTrivalentVertex f) =
        fuseLabels (f vacuum) (f aux) (labels.map f)
  | [] => by simp [fuseLabels]
  | [only] => by simp [fuseLabels, mapTrivalentVertex]
  | left :: right :: tail => by
      simpa only [fuseLabels] using
        map_fuseChain f vacuum aux left right haux tail

/-! ## 2. The constructive canonical-to-actual renaming -/

/-- Send positions inside `labels` to the corresponding physical identifier;
after the list ends, send consecutive canonical suffix coordinates to the
reserved block beginning at `base`. -/
def localIdentifierRename : List Nat → Nat → Nat → Nat
  | [], base, edge => base + edge
  | x :: _, _, 0 => x
  | _ :: xs, base, edge + 1 => localIdentifierRename xs base edge

theorem localIdentifierRename_length_add (labels : List Nat)
    (base j : Nat) :
    localIdentifierRename labels base (labels.length + j) = base + j := by
  induction labels with
  | nil => simp [localIdentifierRename]
  | cons x xs ih =>
      simp only [List.length_cons]
      have hindex : xs.length + 1 + j = (xs.length + j) + 1 := by omega
      rw [hindex]
      change localIdentifierRename xs base (xs.length + j) = base + j
      exact ih

/-- Canonical physical positions are sent to the supplied identifier list in
the same order. -/
theorem map_localIdentifierRename_range (labels : List Nat) (base : Nat) :
    (List.range labels.length).map (localIdentifierRename labels base) =
      labels := by
  induction labels with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.length_cons]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, localIdentifierRename, List.map_map]
      change x :: (List.range xs.length).map
          (localIdentifierRename xs base) = x :: xs
      rw [ih]

/-- On the canonical auxiliary suffix beginning at `labels.length + 1`, the
renaming has exactly the unit-slope law required by `map_fuseLabels`. -/
theorem localIdentifierRename_aux_affine (labels : List Nat) (base : Nat) :
    ∀ j,
      localIdentifierRename labels base (labels.length + 1 + j) =
        localIdentifierRename labels base (labels.length + 1) + j := by
  intro j
  rw [show labels.length + 1 + j = labels.length + (1 + j) by omega,
    localIdentifierRename_length_add,
    localIdentifierRename_length_add]
  omega

/-! ## 2a. Transport of the complete local coordinate list -/

/-- Canonical physical coordinates followed by the same eight-coordinate
reserved block used in the production geometry. -/
def canonicalLocalCoordinates (degree : Nat) : List Nat :=
  List.range degree ++ (List.range 8).map (fun j => degree + j)

/-- The constructive renaming maps the complete canonical coordinate list to
the supplied physical identifiers followed by the consecutive reserved
block. -/
theorem map_canonicalLocalCoordinates (labels : List Nat) (base : Nat) :
    (canonicalLocalCoordinates labels.length).map
        (localIdentifierRename labels base) =
      labels ++ (List.range 8).map (fun j => base + j) := by
  unfold canonicalLocalCoordinates
  rw [List.map_append, map_localIdentifierRename_range, List.map_map]
  have hfun :
      (localIdentifierRename labels base ∘ fun j => labels.length + j) =
        (fun j => base + j) := by
    funext j
    exact localIdentifierRename_length_add labels base j
  rw [hfun]

/-- On an actual link, the renamed canonical list is literally the production
physical-plus-reserved list. -/
theorem map_canonicalLocalCoordinates_actual
    (n i : Nat) (ell : Z4Link) :
    let labels := incidentPlaqIds n ell
    (canonicalLocalCoordinates labels.length).map
        (localIdentifierRename labels (linkBlockBase n i)) =
      labels ++ linkBlockEdges n i := by
  dsimp only
  exact map_canonicalLocalCoordinates
    (incidentPlaqIds n ell) (linkBlockBase n i)

/-- The actual image of the canonical coordinate list is duplicate-free; in
particular, the vertex transport above does not identify two summed graph
coordinates. -/
theorem renamed_canonicalLocalCoordinates_nodup
    (n i : Nat) (ell : Z4Link) :
    let labels := incidentPlaqIds n ell
    ((canonicalLocalCoordinates labels.length).map
      (localIdentifierRename labels (linkBlockBase n i))).Nodup := by
  dsimp only
  rw [map_canonicalLocalCoordinates_actual]
  exact incidentPlaqIds_append_linkBlockEdges_nodup n i ell

/-! ## 3. Vertex-for-vertex transport to the actual box identifiers -/

/-- Canonical consecutive identifiers and arbitrary physical identifiers
produce exactly the same resolver after the explicit renaming. -/
theorem canonical_fuseLabels_map_eq_actual (labels : List Nat) (base : Nat) :
    (fuseLabels labels.length (labels.length + 1)
        (List.range labels.length)).map
        (mapTrivalentVertex (localIdentifierRename labels base)) =
      fuseLabels base (base + 1) labels := by
  let f := localIdentifierRename labels base
  have hmap := map_fuseLabels f labels.length (labels.length + 1)
    (localIdentifierRename_aux_affine labels base)
    (List.range labels.length)
  have hvac : f labels.length = base := by
    simpa [f] using localIdentifierRename_length_add labels base 0
  have haux : f (labels.length + 1) = base + 1 := by
    simpa [f, Nat.add_assoc] using
      localIdentifierRename_length_add labels base 1
  rw [hmap, hvac, haux, map_localIdentifierRename_range]

/-- **Actual link-identifier transport.**  The canonical resolver of the same
degree maps exactly to the production `linkResolutionVertices` block. -/
theorem canonical_linkResolutionVertices_map
    (n i : Nat) (ell : Z4Link) :
    let labels := incidentPlaqIds n ell
    (fuseLabels labels.length (labels.length + 1)
        (List.range labels.length)).map
        (mapTrivalentVertex
          (localIdentifierRename labels (linkBlockBase n i))) =
      linkResolutionVertices n i ell := by
  dsimp only
  unfold linkResolutionVertices
  exact canonical_fuseLabels_map_eq_actual
    (incidentPlaqIds n ell) (linkBlockBase n i)

end YMGap.Continuum.Z4FuseChainIdentifierTransport

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4FuseChainIdentifierTransport.map_fuseChain
#print axioms YMGap.Continuum.Z4FuseChainIdentifierTransport.map_fuseLabels
#print axioms YMGap.Continuum.Z4FuseChainIdentifierTransport.localIdentifierRename_length_add
#print axioms YMGap.Continuum.Z4FuseChainIdentifierTransport.map_localIdentifierRename_range
#print axioms YMGap.Continuum.Z4FuseChainIdentifierTransport.localIdentifierRename_aux_affine
#print axioms YMGap.Continuum.Z4FuseChainIdentifierTransport.map_canonicalLocalCoordinates
#print axioms YMGap.Continuum.Z4FuseChainIdentifierTransport.map_canonicalLocalCoordinates_actual
#print axioms YMGap.Continuum.Z4FuseChainIdentifierTransport.renamed_canonicalLocalCoordinates_nodup
#print axioms YMGap.Continuum.Z4FuseChainIdentifierTransport.canonical_fuseLabels_map_eq_actual
#print axioms YMGap.Continuum.Z4FuseChainIdentifierTransport.canonical_linkResolutionVertices_map
