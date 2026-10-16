/-
# Actual open-cube incidence and its gauge null direction

The retained spatial faces and spatial links are the literal width-only
original-slab lists already used by the fixed-spatial transfer construction.
This leaf turns their standard oriented cubical boundary coefficient into the
rational face-by-edge curl matrix consumed by the finite Gaussian precision
API.  Guarded lookups are proved to recover every in-range face and link, and
every boundary edge of a retained face lies in the same edge carrier.

The same exact incidence annihilates every vertex gradient.  An explicit
coordinate potential has a nonzero gradient on a link present at every width.
Thus the ambient full-edge curl has a genuine gauge null direction: the next
covariance certificate must first provide transverse/gauge-reduced coordinates
(or a separately justified positive completion), rather than attempt a
two-sided inverse of the full-edge precision.

Consumer: the coordinate-space FREE-reference branch in the adaptive-score
audit.  This file constructs no transverse basis, inverse, LDL table, Gaussian
density or pushforward law, compact-Haar/ORIGINAL comparison, uniform response
estimate, continuum theory, or physical mass gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry
import YMGap.Continuum.BF4U1SameCarrierPushforward
import YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeIncidence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeFaceGeometry
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision

local infix:50 " ≈ " => Q'.eqv

/-- Number of literal retained spatial edge coordinates. -/
def openCubeEdgeCount (width : Nat) : Nat :=
  (baseLinks width).length

/-- Number of literal retained spatial plaquettes. -/
def openCubeFaceCount (width : Nat) : Nat :=
  (spatialFaces width).length

/-- Total lookup of a retained spatial face.  The fallback is never used at an
index below `openCubeFaceCount`; the next two theorems expose that fact. -/
def selectedSpatialFace (width faceIndex : Nat) : Z4Plaq :=
  (spatialFaces width).getD faceIndex ((0, 0, 0, 0), .p01)

/-- Total lookup of a retained spatial link.  The fallback is never used at an
index below `openCubeEdgeCount`; the next two theorems expose that fact. -/
def selectedSpatialLink (width edgeIndex : Nat) : Z4Link :=
  (baseLinks width).getD edgeIndex ((0, 0, 0, 0), .x0)

theorem selectedSpatialFace_eq (width faceIndex : Nat)
    (hface : faceIndex < openCubeFaceCount width) :
    selectedSpatialFace width faceIndex = (spatialFaces width)[faceIndex] :=
  (List.getElem_eq_getD
    (l := spatialFaces width) (i := faceIndex) (h := hface)
    ((0, 0, 0, 0), Z4Plane.p01)).symm

theorem selectedSpatialLink_eq (width edgeIndex : Nat)
    (hedge : edgeIndex < openCubeEdgeCount width) :
    selectedSpatialLink width edgeIndex = (baseLinks width)[edgeIndex] :=
  (List.getElem_eq_getD
    (l := baseLinks width) (i := edgeIndex) (h := hedge)
    ((0, 0, 0, 0), Dir4.x0)).symm

theorem selectedSpatialFace_mem (width faceIndex : Nat)
    (hface : faceIndex < openCubeFaceCount width) :
    selectedSpatialFace width faceIndex ∈ spatialFaces width := by
  rw [selectedSpatialFace_eq width faceIndex hface]
  exact List.getElem_mem hface

theorem selectedSpatialLink_mem (width edgeIndex : Nat)
    (hedge : edgeIndex < openCubeEdgeCount width) :
    selectedSpatialLink width edgeIndex ∈ baseLinks width := by
  rw [selectedSpatialLink_eq width edgeIndex hedge]
  exact List.getElem_mem hedge

theorem selectedSpatialFace_idxOf {width : Nat} {face : Z4Plaq}
    (hface : face ∈ spatialFaces width) :
    selectedSpatialFace width ((spatialFaces width).idxOf face) = face := by
  have hindex := List.idxOf_lt_length_of_mem hface
  rw [selectedSpatialFace_eq width _ hindex]
  exact LawfulBEq.eq_of_beq (List.findIdx_getElem (w := hindex))

theorem selectedSpatialLink_idxOf {width : Nat} {link : Z4Link}
    (hlink : link ∈ baseLinks width) :
    selectedSpatialLink width ((baseLinks width).idxOf link) = link := by
  have hindex := List.idxOf_lt_length_of_mem hlink
  rw [selectedSpatialLink_eq width _ hindex]
  exact LawfulBEq.eq_of_beq (List.findIdx_getElem (w := hindex))

/-- The standard oriented cubical coefficient, embedded exactly into the
project's constructive rationals.  In `edgesOf` order its values are
`+1,-1,-1,+1`; equivalently the plaquette word has signs `+A,+B,-C,-D`. -/
def rationalBoundaryCoefficient (face : Z4Plaq) (link : Z4Link) : Q' :=
  Q'.ofInt (orientedBoundaryCoefficient face link)

theorem rationalBoundaryCoefficient_faceLinkA (face : Z4Plaq) :
    rationalBoundaryCoefficient face (faceLinkA face) = 1 := by
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  cases plane <;>
    simp [rationalBoundaryCoefficient, orientedBoundaryCoefficient,
      faceLinkA, dirsOf]
  all_goals decide

theorem rationalBoundaryCoefficient_faceLinkB (face : Z4Plaq) :
    rationalBoundaryCoefficient face (faceLinkB face) = 1 := by
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  cases plane <;>
    simp [rationalBoundaryCoefficient, orientedBoundaryCoefficient,
      faceLinkB, dirsOf, addE]
  all_goals decide

theorem rationalBoundaryCoefficient_faceLinkC (face : Z4Plaq) :
    rationalBoundaryCoefficient face (faceLinkC face) = -1 := by
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  cases plane <;>
    simp [rationalBoundaryCoefficient, orientedBoundaryCoefficient,
      faceLinkC, dirsOf, addE]
  all_goals decide

theorem rationalBoundaryCoefficient_faceLinkD (face : Z4Plaq) :
    rationalBoundaryCoefficient face (faceLinkD face) = -1 := by
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  cases plane <;>
    simp [rationalBoundaryCoefficient, orientedBoundaryCoefficient,
      faceLinkD, dirsOf]
  all_goals decide

theorem rationalBoundaryCoefficient_zero_of_not_mem
    {face : Z4Plaq} {link : Z4Link} (hlink : link ∉ edgesOf face) :
    rationalBoundaryCoefficient face link = 0 := by
  have hfirst : link ≠ (face.1, (dirsOf face.2).1) := by
    intro heq
    apply hlink
    rw [heq]
    simp [edgesOf]
  have hsecond : link ≠ (face.1, (dirsOf face.2).2) := by
    intro heq
    apply hlink
    rw [heq]
    simp [edgesOf]
  have hthird :
      link ≠ (addE face.1 (dirsOf face.2).2, (dirsOf face.2).1) := by
    intro heq
    apply hlink
    rw [heq]
    simp [edgesOf]
  have hfourth :
      link ≠ (addE face.1 (dirsOf face.2).1, (dirsOf face.2).2) := by
    intro heq
    apply hlink
    rw [heq]
    simp [edgesOf]
  simp [rationalBoundaryCoefficient, orientedBoundaryCoefficient,
    hfirst, hsecond, hthird, hfourth]
  exact RingNormaliser.ofInt_zero

/-- Actual retained-face by retained-edge curl incidence.  Entries outside the
two finite carriers are explicitly zero. -/
def openCubeCurl (width faceIndex edgeIndex : Nat) : Q' :=
  if faceIndex < openCubeFaceCount width ∧ edgeIndex < openCubeEdgeCount width then
    rationalBoundaryCoefficient
      (selectedSpatialFace width faceIndex)
      (selectedSpatialLink width edgeIndex)
  else 0

theorem openCubeCurl_in_range {width faceIndex edgeIndex : Nat}
    (hface : faceIndex < openCubeFaceCount width)
    (hedge : edgeIndex < openCubeEdgeCount width) :
    openCubeCurl width faceIndex edgeIndex =
      rationalBoundaryCoefficient
        (selectedSpatialFace width faceIndex)
        (selectedSpatialLink width edgeIndex) := by
  rw [openCubeCurl, if_pos ⟨hface, hedge⟩]

theorem openCubeCurl_out_of_range {width faceIndex edgeIndex : Nat}
    (hout : openCubeFaceCount width ≤ faceIndex ∨
      openCubeEdgeCount width ≤ edgeIndex) :
    openCubeCurl width faceIndex edgeIndex = 0 := by
  rw [openCubeCurl, if_neg]
  intro hin
  exact hout.elim (fun h => Nat.not_lt_of_ge h hin.1)
    (fun h => Nat.not_lt_of_ge h hin.2)

/-- Indexing by literal face and link recovers their exact oriented incidence
coefficient; neither total-lookup fallback participates. -/
theorem openCubeCurl_idxOf {width : Nat} {face : Z4Plaq} {link : Z4Link}
    (hface : face ∈ spatialFaces width) (hlink : link ∈ baseLinks width) :
    openCubeCurl width
        ((spatialFaces width).idxOf face)
        ((baseLinks width).idxOf link) =
      rationalBoundaryCoefficient face link := by
  rw [openCubeCurl_in_range
      (List.idxOf_lt_length_of_mem hface)
      (List.idxOf_lt_length_of_mem hlink),
    selectedSpatialFace_idxOf hface, selectedSpatialLink_idxOf hlink]

/-- No plaquette boundary coordinate is omitted by the retained edge list. -/
theorem selectedSpatialFace_edge_mem {width faceIndex : Nat}
    (hface : faceIndex < openCubeFaceCount width) {link : Z4Link}
    (hlink : link ∈ edgesOf (selectedSpatialFace width faceIndex)) :
    link ∈ baseLinks width :=
  spatial_face_link_mem (selectedSpatialFace_mem width faceIndex hface) hlink

theorem selectedSpatialFace_edge_index_lt {width faceIndex : Nat}
    (hface : faceIndex < openCubeFaceCount width) {link : Z4Link}
    (hlink : link ∈ edgesOf (selectedSpatialFace width faceIndex)) :
    (baseLinks width).idxOf link < openCubeEdgeCount width :=
  List.idxOf_lt_length_of_mem (selectedSpatialFace_edge_mem hface hlink)

/-- Positive-link discrete gradient of a rational vertex potential. -/
def edgeGradient (potential : Z4Vertex → Q') (link : Z4Link) : Q' :=
  potential (addE link.1 link.2) + -potential link.1

/-- Literal oriented curl around one plaquette, in its word order. -/
def faceCurlValue (field : Z4Link → Q') (face : Z4Plaq) : Q' :=
  field (faceLinkA face) +
    (field (faceLinkB face) +
      (-field (faceLinkC face) + -field (faceLinkD face)))

private theorem addE_dirs_comm (face : Z4Plaq) :
    addE (addE face.1 (dirsOf face.2).1) (dirsOf face.2).2 =
      addE (addE face.1 (dirsOf face.2).2) (dirsOf face.2).1 := by
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  cases plane <;> rfl

/-- Exact gauge identity `curl (gradient potential) = 0` on every retained
plaquette geometry, proved before any covariance or inverse is introduced. -/
theorem faceCurlValue_edgeGradient (potential : Z4Vertex → Q')
    (face : Z4Plaq) :
    faceCurlValue (edgeGradient potential) face ≈ 0 := by
  unfold faceCurlValue edgeGradient faceLinkA faceLinkB faceLinkC faceLinkD
  rw [← addE_dirs_comm face]
  exact poly_identity_of_normal_eq
    (.add (.add (.var 1) (.neg (.var 0)))
      (.add (.add (.var 2) (.neg (.var 1)))
        (.add (.neg (.add (.var 2) (.neg (.var 3))))
          (.neg (.add (.var 3) (.neg (.var 0)))))))
    (.const 0) (by decide) (fun
      | 0 => potential face.1
      | 1 => potential (addE face.1 (dirsOf face.2).1)
      | 2 => potential
          (addE (addE face.1 (dirsOf face.2).1) (dirsOf face.2).2)
      | _ => potential (addE face.1 (dirsOf face.2).2))

/-- A concrete rational potential whose first coordinate is the lattice's
first vertex coordinate. -/
def firstCoordinatePotential (vertex : Z4Vertex) : Q' :=
  Q'.ofNat vertex.1

def originFirstLink : Z4Link :=
  ((0, 0, 0, 0), .x0)

theorem originFirstLink_mem (width : Nat) :
    originFirstLink ∈ baseLinks width := by
  apply (baseLinks_mem_iff width originFirstLink).mpr
  exact ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩

/-- The preceding gauge-null gradient is not the zero field. -/
theorem firstCoordinateGradient_origin_nonzero :
    ¬ edgeGradient firstCoordinatePotential originFirstLink ≈ 0 := by
  decide

/-- Ambient spatial precision on the literal full edge carrier.  The checked
gradient identity above is why this object is not fed directly to an inverse
certificate. -/
def openCubeSpatialPrecision (width : Nat) : Nat → Nat → Q' :=
  finiteCurlPrecision (openCubeFaceCount width) (openCubeCurl width)

/-- Ambient free-history precision before a transverse/gauge-reduced
coordinate map is supplied. -/
def openCubeFreeHistoryPrecision (timeBonds width : Nat) : Nat → Nat → Q' :=
  freeHistoryCurlPrecision timeBonds
    (openCubeEdgeCount width) (openCubeFaceCount width) (openCubeCurl width)

theorem openCubeFreeHistoryPrecision_symm (timeBonds width left right : Nat) :
    openCubeFreeHistoryPrecision timeBonds width left right ≈
      openCubeFreeHistoryPrecision timeBonds width right left :=
  freeHistoryCurlPrecision_symm timeBonds
    (openCubeEdgeCount width) (openCubeFaceCount width)
    (openCubeCurl width) left right

end YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeIncidence

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeIncidence.openCubeCurl_idxOf
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeIncidence.selectedSpatialFace_edge_mem
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeIncidence.rationalBoundaryCoefficient_zero_of_not_mem
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeIncidence.faceCurlValue_edgeGradient
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeIncidence.originFirstLink_mem
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeIncidence.firstCoordinateGradient_origin_nonzero
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianOpenCubeIncidence.openCubeFreeHistoryPrecision_symm
