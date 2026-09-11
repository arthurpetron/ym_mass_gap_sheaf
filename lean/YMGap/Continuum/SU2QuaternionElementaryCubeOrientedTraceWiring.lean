/-
# Outward-oriented elementary-cube trace wiring

The production plaquette convention orients every coordinate plane by its
increasing direction pair.  Those six canonical orientations are not the
orientation of the boundary of a three-dimensional cube: for example, the
`p01` and `p02` faces based at the origin traverse their common `x0` link in
the same direction.  Therefore the one-link forward/reverse Schur theorem
must not be applied directly to the six raw production words.

This leaf records the missing finite orientation data.  In the audited face
order

    p01(z=0), p02(y=0), p12(x=0),
    p01(z=1), p02(y=1), p12(x=1),

the outward boundary orientation is

    reversed, standard, reversed, standard, reversed, standard.

Each standard plaquette contributes the cyclic coefficient word with slots
`0,3` forward and slots `2,1` reverse.  Reversing a face reverses that cycle
and every link direction.  The resulting twenty-four occurrences pair the
twelve geometric cube links exactly once forward and once reverse.  The
twelve physical links are also mapped injectively into the production
active-link quaternion blocks, with every block in range.

Finally, this file evaluates only the *post-Schur, delta-resolved* scalar
network: twelve resolved fundamental contractions contribute `(1/2)^12`
and the eight deduplicated boundary vertices contribute `2^8`, hence the
factor is `1/16`.

This does **not** yet identify the production cube polynomial with that
resolved network.  In particular, a later leaf must prove that the
fundamental plaquette character is unchanged when a selected canonical face
word is inverted (`trace(U^-1) = trace(U)`), expand the six traces with the
matrix-semantics API, and transport the twelve local contractions through
the finite-product Haar/Fubini carrier.  No such physical identification is
claimed here.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFundamentalMatrixSemantics
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenRadiusZeroClosedGeometryFence

namespace YMGap.Continuum.SU2QuaternionElementaryCubeOrientedTraceWiring

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenRadiusZeroClosedGeometryFence
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Cyclic oriented boundary occurrences -/

/-- Whether a selected face uses the production increasing-plane
orientation or the oppositely oriented boundary word. -/
inductive FundamentalFaceOrientation
  | standard
  | reversed
  deriving DecidableEq

/-- One matrix-coefficient occurrence in a cyclic plaquette trace.
`positive = true` means traversal in the stored positive-coordinate link
direction.  The source and target are the matrix row and column vertices for
that traversal. -/
structure OrientedFundamentalLinkOccurrence where
  physicalLink : Z4Link
  sourceVertex : Z4Vertex
  targetVertex : Z4Vertex
  positive : Bool
  deriving DecidableEq

/-- The stored endpoints agree with the occurrence's physical link and
traversal flag. -/
def OrientedFundamentalLinkOccurrence.Coherent
    (occurrence : OrientedFundamentalLinkOccurrence) : Prop :=
  if occurrence.positive then
    occurrence.sourceVertex = occurrence.physicalLink.1 ∧
      occurrence.targetVertex =
        addE occurrence.physicalLink.1 occurrence.physicalLink.2
  else
    occurrence.sourceVertex =
        addE occurrence.physicalLink.1 occurrence.physicalLink.2 ∧
      occurrence.targetVertex = occurrence.physicalLink.1

/-- The standard positive plaquette cycle.  In `edgesOf` slot language this
is `0, 3, 2^-1, 1^-1`. -/
def standardPlaquetteBoundaryOccurrences
    (plaquette : Z4Plaq) : List OrientedFundamentalLinkOccurrence :=
  let vertex := plaquette.1
  let firstDirection := (dirsOf plaquette.2).1
  let secondDirection := (dirsOf plaquette.2).2
  [⟨(vertex, firstDirection),
      vertex, addE vertex firstDirection, true⟩,
   ⟨(addE vertex firstDirection, secondDirection),
      addE vertex firstDirection,
      addE (addE vertex firstDirection) secondDirection, true⟩,
   ⟨(addE vertex secondDirection, firstDirection),
      addE (addE vertex secondDirection) firstDirection,
      addE vertex secondDirection, false⟩,
   ⟨(vertex, secondDirection),
      addE vertex secondDirection, vertex, false⟩]

/-- The inverse cyclic plaquette word.  It reverses both the order and the
direction of every standard occurrence, giving slots
`1, 2, 3^-1, 0^-1`. -/
def reversedPlaquetteBoundaryOccurrences
    (plaquette : Z4Plaq) : List OrientedFundamentalLinkOccurrence :=
  let vertex := plaquette.1
  let firstDirection := (dirsOf plaquette.2).1
  let secondDirection := (dirsOf plaquette.2).2
  [⟨(vertex, secondDirection),
      vertex, addE vertex secondDirection, true⟩,
   ⟨(addE vertex secondDirection, firstDirection),
      addE vertex secondDirection,
      addE (addE vertex secondDirection) firstDirection, true⟩,
   ⟨(addE vertex firstDirection, secondDirection),
      addE (addE vertex firstDirection) secondDirection,
      addE vertex firstDirection, false⟩,
   ⟨(vertex, firstDirection),
      addE vertex firstDirection, vertex, false⟩]

theorem standardPlaquetteBoundaryOccurrence_coherent
    (plaquette : Z4Plaq)
    {occurrence : OrientedFundamentalLinkOccurrence}
    (hoccurrence : occurrence ∈
      standardPlaquetteBoundaryOccurrences plaquette) :
    occurrence.Coherent := by
  simp only [standardPlaquetteBoundaryOccurrences, List.mem_cons,
    List.not_mem_nil, or_false] at hoccurrence
  rcases hoccurrence with rfl | rfl | rfl | rfl <;>
    simp [OrientedFundamentalLinkOccurrence.Coherent]

theorem reversedPlaquetteBoundaryOccurrence_coherent
    (plaquette : Z4Plaq)
    {occurrence : OrientedFundamentalLinkOccurrence}
    (hoccurrence : occurrence ∈
      reversedPlaquetteBoundaryOccurrences plaquette) :
    occurrence.Coherent := by
  simp only [reversedPlaquetteBoundaryOccurrences, List.mem_cons,
    List.not_mem_nil, or_false] at hoccurrence
  rcases hoccurrence with rfl | rfl | rfl | rfl <;>
    simp [OrientedFundamentalLinkOccurrence.Coherent]

/-- Select the cyclic word prescribed by a face orientation. -/
def plaquetteBoundaryOccurrences
    (orientation : FundamentalFaceOrientation)
    (plaquette : Z4Plaq) : List OrientedFundamentalLinkOccurrence :=
  match orientation with
  | .standard => standardPlaquetteBoundaryOccurrences plaquette
  | .reversed => reversedPlaquetteBoundaryOccurrences plaquette

/-! ## 2. Exact outward orientation of the audited six faces -/

/-- The alternating outward-orientation mask in the exact order of
`radiusZeroElementaryCubeFaces`. -/
def radiusZeroElementaryCubeOutwardOrientationMask :
    List FundamentalFaceOrientation :=
  [.reversed, .standard, .reversed,
   .standard, .reversed, .standard]

theorem radiusZeroElementaryCubeOutwardOrientationMask_length :
    radiusZeroElementaryCubeOutwardOrientationMask.length = 6 := by
  decide

/-- Pair every decoded production face with its outward orientation. -/
def radiusZeroElementaryCubeOutwardFaces :
    List (Z4Plaq × FundamentalFaceOrientation) :=
  radiusZeroElementaryCubeFaces.zip
    radiusZeroElementaryCubeOutwardOrientationMask

theorem radiusZeroElementaryCubeOutwardFaces_length :
    radiusZeroElementaryCubeOutwardFaces.length = 6 := by
  decide

/-- Forgetting orientation returns exactly the decoded six-face production
carrier, in its original order. -/
theorem radiusZeroElementaryCubeOutwardFaces_map_fst :
    radiusZeroElementaryCubeOutwardFaces.map Prod.fst =
      radiusZeroElementaryCubeFaces := by
  decide

/-- Thus the oriented face carrier is attached to the six audited production
identifiers, not merely to an isomorphic abstract cube. -/
theorem radiusZeroElementaryCubeOutwardFaces_map_fst_eq_decodeIds :
    radiusZeroElementaryCubeOutwardFaces.map Prod.fst =
      radiusZeroElementaryCubeFaceIds.map
        (slabPlaquetteAt (adjacentEvenExtent 0)) := by
  rw [radiusZeroElementaryCubeOutwardFaces_map_fst]
  exact radiusZeroElementaryCubeFaces_eq_decodeIds

/-- Reading only orientations returns the exact alternating outward mask. -/
theorem radiusZeroElementaryCubeOutwardFaces_map_snd :
    radiusZeroElementaryCubeOutwardFaces.map Prod.snd =
      radiusZeroElementaryCubeOutwardOrientationMask := by
  decide

/-- The twenty-four cyclic matrix-coefficient occurrences on the outward
oriented cube boundary. -/
def radiusZeroElementaryCubeBoundaryOccurrences :
    List OrientedFundamentalLinkOccurrence :=
  radiusZeroElementaryCubeOutwardFaces.flatMap (fun orientedFace =>
    plaquetteBoundaryOccurrences orientedFace.2 orientedFace.1)

theorem radiusZeroElementaryCubeBoundaryOccurrences_length :
    radiusZeroElementaryCubeBoundaryOccurrences.length = 24 := by
  decide

/-- Every displayed cube occurrence carries the correct positive-link
endpoints for its traversal direction. -/
theorem radiusZeroElementaryCubeBoundaryOccurrence_coherent
    {occurrence : OrientedFundamentalLinkOccurrence}
    (hoccurrence : occurrence ∈
      radiusZeroElementaryCubeBoundaryOccurrences) :
    occurrence.Coherent := by
  unfold radiusZeroElementaryCubeBoundaryOccurrences at hoccurrence
  obtain ⟨orientedFace, _, hlocal⟩ := List.mem_flatMap.mp hoccurrence
  obtain ⟨plaquette, orientation⟩ := orientedFace
  cases orientation with
  | standard =>
      exact standardPlaquetteBoundaryOccurrence_coherent plaquette hlocal
  | reversed =>
      exact reversedPlaquetteBoundaryOccurrence_coherent plaquette hlocal

/-- All occurrences of one physical link in the outward-oriented cube
boundary. -/
def radiusZeroElementaryCubeLinkOccurrences (link : Z4Link) :
    List OrientedFundamentalLinkOccurrence :=
  radiusZeroElementaryCubeBoundaryOccurrences.filter (fun occurrence =>
    decide (occurrence.physicalLink = link))

/-- The positive-direction occurrences of one physical cube link. -/
def radiusZeroElementaryCubePositiveLinkOccurrences (link : Z4Link) :
    List OrientedFundamentalLinkOccurrence :=
  (radiusZeroElementaryCubeLinkOccurrences link).filter
    (fun occurrence => occurrence.positive)

/-- The reverse-direction occurrences of one physical cube link. -/
def radiusZeroElementaryCubeReverseLinkOccurrences (link : Z4Link) :
    List OrientedFundamentalLinkOccurrence :=
  (radiusZeroElementaryCubeLinkOccurrences link).filter
    (fun occurrence => !occurrence.positive)

/-- **Exact outward pairing audit.**  Every one of the twelve touched links
has exactly two boundary occurrences, exactly one in each direction. -/
theorem radiusZeroElementaryCube_link_occurrences_paired_oppositely
    {link : Z4Link}
    (hlink : link ∈ radiusZeroElementaryCubeTouchedLinks) :
    (radiusZeroElementaryCubeLinkOccurrences link).length = 2 ∧
      (radiusZeroElementaryCubePositiveLinkOccurrences link).length = 1 ∧
      (radiusZeroElementaryCubeReverseLinkOccurrences link).length = 1 := by
  unfold radiusZeroElementaryCubeTouchedLinks at hlink
  rw [mem_geometricTouchedLinks] at hlink
  obtain ⟨plaquette, hplaquette, hedge⟩ := hlink
  simp only [radiusZeroElementaryCubeFaces, List.mem_cons,
    List.not_mem_nil, or_false] at hplaquette
  rcases hplaquette with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [edgesOf, dirsOf, addE, List.mem_cons,
      List.not_mem_nil, or_false] at hedge
    rcases hedge with rfl | rfl | rfl | rfl <;> decide

theorem radiusZeroElementaryCube_link_occurrences_two
    {link : Z4Link}
    (hlink : link ∈ radiusZeroElementaryCubeTouchedLinks) :
    (radiusZeroElementaryCubeLinkOccurrences link).length = 2 :=
  (radiusZeroElementaryCube_link_occurrences_paired_oppositely hlink).1

theorem radiusZeroElementaryCube_link_occurrences_one_each_direction
    {link : Z4Link}
    (hlink : link ∈ radiusZeroElementaryCubeTouchedLinks) :
    (radiusZeroElementaryCubePositiveLinkOccurrences link).length = 1 ∧
      (radiusZeroElementaryCubeReverseLinkOccurrences link).length = 1 :=
  (radiusZeroElementaryCube_link_occurrences_paired_oppositely hlink).2

/-! ## 3. The eight resolved vertex indices -/

/-- Deduplicate all sources and targets of the outward-oriented boundary
occurrences.  This is the geometric vertex carrier used by the explicitly
post-Schur resolved network below. -/
def radiusZeroElementaryCubeBoundaryVertices : List Z4Vertex :=
  (radiusZeroElementaryCubeBoundaryOccurrences.flatMap (fun occurrence =>
    [occurrence.sourceVertex, occurrence.targetVertex])).eraseDups

theorem radiusZeroElementaryCubeBoundaryVertices_length :
    radiusZeroElementaryCubeBoundaryVertices.length = 8 := by
  decide

theorem radiusZeroElementaryCubeBoundaryVertices_nodup :
    radiusZeroElementaryCubeBoundaryVertices.Nodup := by
  decide

theorem radiusZeroElementaryCubeOccurrence_source_mem_vertices
    {occurrence : OrientedFundamentalLinkOccurrence}
    (hoccurrence : occurrence ∈
      radiusZeroElementaryCubeBoundaryOccurrences) :
    occurrence.sourceVertex ∈
      radiusZeroElementaryCubeBoundaryVertices := by
  unfold radiusZeroElementaryCubeBoundaryVertices
  rw [List.mem_eraseDups, List.mem_flatMap]
  exact ⟨occurrence, hoccurrence, List.mem_cons_self⟩

theorem radiusZeroElementaryCubeOccurrence_target_mem_vertices
    {occurrence : OrientedFundamentalLinkOccurrence}
    (hoccurrence : occurrence ∈
      radiusZeroElementaryCubeBoundaryOccurrences) :
    occurrence.targetVertex ∈
      radiusZeroElementaryCubeBoundaryVertices := by
  unfold radiusZeroElementaryCubeBoundaryVertices
  rw [List.mem_eraseDups, List.mem_flatMap]
  exact ⟨occurrence, hoccurrence,
    List.mem_cons_of_mem occurrence.sourceVertex List.mem_cons_self⟩

/-! ## 4. Injection into the production active-link blocks -/

/-- The canonical production quaternion-block indices of the twelve cube
links, in the duplicate-free geometric touched-link order. -/
def radiusZeroElementaryCubeActiveLinkBlocks : List Nat :=
  radiusZeroElementaryCubeTouchedLinks.map
    (adjacentEvenActiveLinkIndex 0)

theorem radiusZeroElementaryCubeActiveLinkBlocks_length :
    radiusZeroElementaryCubeActiveLinkBlocks.length = 12 := by
  simpa only [radiusZeroElementaryCubeActiveLinkBlocks, List.length_map] using
    radiusZeroElementaryCubeTouchedLinks_length

/-- Distinct physical cube links select distinct production quaternion
blocks. -/
theorem radiusZeroElementaryCubeActiveLinkBlocks_nodup :
    radiusZeroElementaryCubeActiveLinkBlocks.Nodup := by
  unfold radiusZeroElementaryCubeActiveLinkBlocks
  apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
  · exact radiusZeroElementaryCubeTouchedLinks_nodup
  · intro left hleft right hright hindex
    exact adjacentEvenActiveLinkIndex_injective_on
      (radiusZeroElementaryCubeTouchedLink_active hleft)
      (radiusZeroElementaryCubeTouchedLink_active hright)
      hindex

/-- Every selected cube block is in range for the production active-link
carrier. -/
theorem radiusZeroElementaryCubeActiveLinkBlock_lt
    {block : Nat}
    (hblock : block ∈ radiusZeroElementaryCubeActiveLinkBlocks) :
    block < (adjacentEvenActiveLinks 0).length := by
  obtain ⟨link, hlink, rfl⟩ := List.mem_map.mp hblock
  exact adjacentEvenActiveLinkIndex_lt
    (radiusZeroElementaryCubeTouchedLink_active hlink)

/-- Looking up a selected block returns a touched elementary-cube link. -/
theorem radiusZeroElementaryCubeActiveLinkAt_mem_touched
    {block : Nat}
    (hblock : block ∈ radiusZeroElementaryCubeActiveLinkBlocks) :
    adjacentEvenActiveLinkAt 0 block ∈
      radiusZeroElementaryCubeTouchedLinks := by
  obtain ⟨link, hlink, rfl⟩ := List.mem_map.mp hblock
  rw [adjacentEvenActiveLinkAt_index
    (radiusZeroElementaryCubeTouchedLink_active hlink)]
  exact hlink

/-! ## 5. Post-Schur, delta-resolved scalar normalization -/

/-- The scalar of the already-resolved elementary-cube trace network.

This definition starts *after* the twelve one-link integrals have been
replaced by their fundamental Schur deltas and those deltas have been
resolved to one free Boolean index at each boundary vertex.  It is not a
definition of the production Haar integral. -/
def radiusZeroElementaryCubePostSchurResolvedFactor : Q' :=
  qpow (Q'.ofNat 2) radiusZeroElementaryCubeBoundaryVertices.length *
    qpow (Q'.invSucc 1) radiusZeroElementaryCubeActiveLinkBlocks.length

/-- The geometry-derived post-Schur factor is exactly the previously audited
Euler/Schur bookkeeping expression. -/
theorem radiusZeroElementaryCubePostSchurResolvedFactor_eq_euler :
    radiusZeroElementaryCubePostSchurResolvedFactor =
      elementaryCubeEulerSchurFactor := by
  unfold radiusZeroElementaryCubePostSchurResolvedFactor
    elementaryCubeEulerSchurFactor
  rw [radiusZeroElementaryCubeBoundaryVertices_length,
    radiusZeroElementaryCubeActiveLinkBlocks_length]

/-- Exact normalization of the post-Schur, delta-resolved cube network. -/
theorem radiusZeroElementaryCubePostSchurResolvedFactor_exact :
    radiusZeroElementaryCubePostSchurResolvedFactor ≈
      Q'.mkPos 1 16 (by decide) := by
  rw [radiusZeroElementaryCubePostSchurResolvedFactor_eq_euler]
  exact elementaryCubeEulerSchurFactor_exact

#print axioms radiusZeroElementaryCubeOutwardFaces_map_fst
#print axioms radiusZeroElementaryCubeOutwardFaces_map_fst_eq_decodeIds
#print axioms radiusZeroElementaryCubeOutwardFaces_map_snd
#print axioms radiusZeroElementaryCubeBoundaryOccurrences_length
#print axioms radiusZeroElementaryCubeBoundaryOccurrence_coherent
#print axioms radiusZeroElementaryCube_link_occurrences_paired_oppositely
#print axioms radiusZeroElementaryCubeBoundaryVertices_length
#print axioms radiusZeroElementaryCubeActiveLinkBlocks_nodup
#print axioms radiusZeroElementaryCubeActiveLinkBlock_lt
#print axioms radiusZeroElementaryCubeActiveLinkAt_mem_touched
#print axioms radiusZeroElementaryCubePostSchurResolvedFactor_exact

end YMGap.Continuum.SU2QuaternionElementaryCubeOrientedTraceWiring
