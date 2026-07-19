/-
# Constructive active-link coordinates for the adjacent-even fixed faces

The adjacent-even fixed-face density is a product of plaquette factors on one
common gauge field.  To pull its local sixteen-coordinate polynomials into a
single finite polynomial ring, every physical link shared by two or more
fixed faces must receive one and the same coordinate block.

The production fixed-link list already provides the required carrier.  It is
the fixed part of the deduplicated boundary-complete slab link list, is
constructively noduplicated, and contains every boundary edge of every fixed
face.  This file equips that existing list with a first-occurrence index, a
zero-padded lookup, and four scalar coordinates per link.  It also records the
round trips needed to transport each of the four literal `edgesOf` slots of a
fixed face into the global carrier.

The carrier may contain fixed slab links not used by the selected fixed-face
density.  This is intentional: it keeps the polynomial variables aligned with
the existing fixed-link kernel and avoids a second deduplication convention.
Later normalized one-link Haar integration removes any unused coordinate
blocks.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceDensitySOS
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceDensitySOS
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. The existing production fixed-link carrier -/

/-- The finite global link carrier for the adjacent-even fixed-face density.
It is exactly the existing fixed component of the boundary-complete slab link
partition. -/
abbrev adjacentEvenActiveLinks (radius : Nat) : List Z4Link :=
  adjacentEvenFixedSlabLinks radius

/-- The production active-link carrier has no duplicate link variables. -/
theorem adjacentEvenActiveLinks_nodup (radius : Nat) :
    (adjacentEvenActiveLinks radius).Nodup := by
  simpa only [adjacentEvenActiveLinks, adjacentEvenFixedSlabLinks,
    adjacentEvenFixedLinks] using
    (adjacentEvenFixedLinks_nodup radius)

/-- Geometric membership in the active carrier: a link is an actual
boundary-complete slab link on the adjacent-even fixed slice. -/
theorem mem_adjacentEvenActiveLinks
    {radius : Nat} {link : Z4Link} :
    link ∈ adjacentEvenActiveLinks radius ↔
      link ∈ boundaryCompleteSlabLinks (adjacentEvenExtent radius) ∧
      adjacentEvenLinkSide radius link = .fixed := by
  simpa only [adjacentEvenActiveLinks] using
    (mem_adjacentEvenFixedSlabLinks
      (radius := radius) (link := link))

/-! ## 2. Every fixed-face edge is carried globally -/

/-- Every literal edge of a fixed face identifier belongs to the global
active-link carrier. -/
theorem adjacentEvenFixedFaceLink_mem_activeLinks
    {radius id : Nat}
    (hid : id ∈ adjacentEvenFixedFaceIds radius)
    {link : Z4Link}
    (hlink : link ∈ adjacentEvenFixedFaceLinks radius id) :
    link ∈ adjacentEvenActiveLinks radius := by
  simpa only [adjacentEvenActiveLinks] using
    (adjacentEvenFixedFaceLink_mem_fixedSlabLinks hid hlink)

/-- The same support theorem stated for membership in the mapped physical
fixed-face list used by the density SOS. -/
theorem adjacentEvenFixedFacePlaquette_edge_mem_activeLinks
    {radius : Nat} {plaquette : Z4Plaq}
    (hplaquette :
      plaquette ∈ adjacentEvenFixedFacePlaquettes radius)
    {link : Z4Link} (hlink : link ∈ edgesOf plaquette) :
    link ∈ adjacentEvenActiveLinks radius := by
  obtain ⟨id, hid, heq⟩ := List.mem_map.mp hplaquette
  subst plaquette
  apply adjacentEvenFixedFaceLink_mem_activeLinks hid
  simpa only [adjacentEvenFixedFaceLinks] using hlink

/-! ## 3. Constructive global link indices -/

/-- First-occurrence index of a link in the active carrier.  Membership
theorems below ensure that this index is used only on carried links. -/
def adjacentEvenActiveLinkIndex
    (radius : Nat) (link : Z4Link) : Nat :=
  listIndexOf link (adjacentEvenActiveLinks radius)

/-- Zero-padded lookup in the active carrier. -/
def adjacentEvenActiveLinkAt
    (radius index : Nat) : Z4Link :=
  (adjacentEvenActiveLinks radius).getD index defaultZ4Link

/-- A carried link has a genuine in-range global index. -/
theorem adjacentEvenActiveLinkIndex_lt
    {radius : Nat} {link : Z4Link}
    (hlink : link ∈ adjacentEvenActiveLinks radius) :
    adjacentEvenActiveLinkIndex radius link <
      (adjacentEvenActiveLinks radius).length := by
  exact listIndexOf_lt_of_mem link
    (adjacentEvenActiveLinks radius) hlink

/-- Looking up the canonical index of a carried link returns that link. -/
theorem adjacentEvenActiveLinkAt_index
    {radius : Nat} {link : Z4Link}
    (hlink : link ∈ adjacentEvenActiveLinks radius) :
    adjacentEvenActiveLinkAt radius
        (adjacentEvenActiveLinkIndex radius link) = link := by
  exact getD_listIndexOf_of_mem defaultZ4Link link
    (adjacentEvenActiveLinks radius) hlink

/-- Canonical global indices are injective on carried links. -/
theorem adjacentEvenActiveLinkIndex_injective_on
    {radius : Nat} {left right : Z4Link}
    (hleft : left ∈ adjacentEvenActiveLinks radius)
    (hright : right ∈ adjacentEvenActiveLinks radius)
    (hindex : adjacentEvenActiveLinkIndex radius left =
      adjacentEvenActiveLinkIndex radius right) :
    left = right := by
  rw [← adjacentEvenActiveLinkAt_index hleft,
    ← adjacentEvenActiveLinkAt_index hright, hindex]

/-! ## 4. Four scalar coordinates per active link -/

/-- Total number of scalar-first rational quaternion coordinates on the
active carrier. -/
def adjacentEvenActiveCoordinateCount (radius : Nat) : Nat :=
  4 * (adjacentEvenActiveLinks radius).length

/-- The scalar coordinate of one component of one carried quaternion link.
Components `0,1,2,3` correspond respectively to `r,i,j,k`. -/
def adjacentEvenActiveLinkCoordinate
    (radius : Nat) (link : Z4Link) (component : Nat) : Nat :=
  4 * adjacentEvenActiveLinkIndex radius link + component

/-- Every genuine component of every carried link lies in the global scalar
coordinate range. -/
theorem adjacentEvenActiveLinkCoordinate_lt
    {radius : Nat} {link : Z4Link} {component : Nat}
    (hlink : link ∈ adjacentEvenActiveLinks radius)
    (hcomponent : component < 4) :
    adjacentEvenActiveLinkCoordinate radius link component <
      adjacentEvenActiveCoordinateCount radius := by
  have hindex := adjacentEvenActiveLinkIndex_lt hlink
  unfold adjacentEvenActiveLinkCoordinate
    adjacentEvenActiveCoordinateCount
  omega

/-! ## 5. Literal fixed-face slots and their global round trip -/

private theorem listGetD_mem_of_lt
    {A : Type} (fallback : A) : ∀ (items : List A) (index : Nat),
    index < items.length → items.getD index fallback ∈ items
  | [], _, hindex => by simp at hindex
  | head :: tail, 0, _ => List.mem_cons_self
  | head :: tail, index + 1, hindex => by
      simp only [List.getD_cons_succ]
      exact List.mem_cons_of_mem head
        (listGetD_mem_of_lt fallback tail index (by
          simp only [List.length_cons] at hindex
          omega))

/-- The link occupying one of the four literal production `edgesOf` slots of
a fixed face. -/
def adjacentEvenFixedFaceLinkAt
    (radius id slot : Nat) : Z4Link :=
  (adjacentEvenFixedFaceLinks radius id).getD slot defaultZ4Link

/-- Every slot below four is a genuine member of the face's edge list. -/
theorem adjacentEvenFixedFaceLinkAt_mem_faceLinks
    {radius id slot : Nat} (hslot : slot < 4) :
    adjacentEvenFixedFaceLinkAt radius id slot ∈
      adjacentEvenFixedFaceLinks radius id := by
  apply listGetD_mem_of_lt defaultZ4Link
  rw [adjacentEvenFixedFaceLinks_length]
  exact hslot

/-- Every genuine slot of a fixed face is carried by the global link list. -/
theorem adjacentEvenFixedFaceLinkAt_mem_activeLinks
    {radius id slot : Nat}
    (hid : id ∈ adjacentEvenFixedFaceIds radius)
    (hslot : slot < 4) :
    adjacentEvenFixedFaceLinkAt radius id slot ∈
      adjacentEvenActiveLinks radius := by
  exact adjacentEvenFixedFaceLink_mem_activeLinks hid
    (adjacentEvenFixedFaceLinkAt_mem_faceLinks hslot)

/-- Local face slots survive the local-to-global index/lookup round trip.
Consequently two face occurrences of the same physical link select the same
global quaternion coordinate block. -/
theorem adjacentEvenActiveLinkAt_index_fixedFaceLinkAt
    {radius id slot : Nat}
    (hid : id ∈ adjacentEvenFixedFaceIds radius)
    (hslot : slot < 4) :
    adjacentEvenActiveLinkAt radius
        (adjacentEvenActiveLinkIndex radius
          (adjacentEvenFixedFaceLinkAt radius id slot)) =
      adjacentEvenFixedFaceLinkAt radius id slot := by
  exact adjacentEvenActiveLinkAt_index
    (adjacentEvenFixedFaceLinkAt_mem_activeLinks hid hslot)

/-- Every scalar component of a genuine fixed-face slot lies in the global
active-coordinate range. -/
theorem adjacentEvenFixedFaceLinkAt_coordinate_lt
    {radius id slot component : Nat}
    (hid : id ∈ adjacentEvenFixedFaceIds radius)
    (hslot : slot < 4) (hcomponent : component < 4) :
    adjacentEvenActiveLinkCoordinate radius
        (adjacentEvenFixedFaceLinkAt radius id slot) component <
      adjacentEvenActiveCoordinateCount radius := by
  exact adjacentEvenActiveLinkCoordinate_lt
    (adjacentEvenFixedFaceLinkAt_mem_activeLinks hid hslot)
    hcomponent

#print axioms adjacentEvenActiveLinks_nodup
#print axioms mem_adjacentEvenActiveLinks
#print axioms adjacentEvenFixedFaceLink_mem_activeLinks
#print axioms adjacentEvenFixedFacePlaquette_edge_mem_activeLinks
#print axioms adjacentEvenActiveLinkIndex_lt
#print axioms adjacentEvenActiveLinkAt_index
#print axioms adjacentEvenActiveLinkIndex_injective_on
#print axioms adjacentEvenActiveLinkCoordinate_lt
#print axioms adjacentEvenFixedFaceLinkAt_mem_faceLinks
#print axioms adjacentEvenFixedFaceLinkAt_mem_activeLinks
#print axioms adjacentEvenActiveLinkAt_index_fixedFaceLinkAt
#print axioms adjacentEvenFixedFaceLinkAt_coordinate_lt

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
