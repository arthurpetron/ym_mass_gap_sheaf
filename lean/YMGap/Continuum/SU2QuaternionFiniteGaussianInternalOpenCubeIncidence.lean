/-
# Formula-level internal open-cube incidence

The free Gaussian benchmark uses the open cubical graph on vertices with
coordinates `0, ..., width-1`.  Its internal positive links have both
endpoints in that vertex box, and its faces are exactly the three spatial
orientations whose four vertices remain in the box.  This leaf enumerates
those links and faces directly from their coordinate formulas, proves that
the lists are duplicate-free, and proves that every listed face edge belongs
to the listed internal-link carrier.

The wider fixed-spatial transfer carrier also contains transmitted links that
point through the positive boundary.  Their formula-level list is constructed
here and proved disjoint from every internal face.  This matches the PAPER
split used by the finite open-cube Gaussian benchmark.  A checked equality
between these formula lists and the existing original-transfer filters remains
a separate bridge; it is not asserted here.

Consumer: a rational tree-gauge or transverse-coordinate construction for the
finite free reference.  This file does not construct that coordinate map, an
inverse, an LDL certificate, a Gaussian law, an ORIGINAL-law comparison, a
continuum theory, or a physical mass gap.
-/

import YMGap.Continuum.BF4U1SameCarrierPushforward
import YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision

namespace YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4U1SameCarrierPushforward
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision

local infix:50 " ≈ " => Q'.eqv

/-- A spatial link based strictly inside the width box and transmitted to the
next time slice.  Its positive endpoint may lie on the outward fringe. -/
def TransmittedOpenCubeLink (width : Nat) (link : Z4Link) : Prop :=
  link.2 ≠ .x3 ∧ link.1.1 < width ∧ link.1.2.1 < width ∧
    link.1.2.2.1 < width ∧ link.1.2.2.2 = 0

instance (width : Nat) (link : Z4Link) : Decidable (TransmittedOpenCubeLink width link) := by
  unfold TransmittedOpenCubeLink
  infer_instance

/-- A transmitted spatial link whose positive endpoint also remains in the
strict vertex box. -/
def InternalOpenCubeLink (width : Nat) (link : Z4Link) : Prop :=
  TransmittedOpenCubeLink width link ∧
    match link.2 with
    | .x0 => link.1.1 + 1 < width
    | .x1 => link.1.2.1 + 1 < width
    | .x2 => link.1.2.2.1 + 1 < width
    | .x3 => False

instance (width : Nat) (link : Z4Link) : Decidable (InternalOpenCubeLink width link) := by
  rcases link with ⟨vertex, dir⟩
  cases dir <;> unfold InternalOpenCubeLink TransmittedOpenCubeLink <;> infer_instance

/-- A spatial plaquette whose complete boundary remains in the strict vertex
box. -/
def InternalOpenCubeFace (width : Nat) (face : Z4Plaq) : Prop :=
  face.1.2.2.2 = 0 ∧
    match face.2 with
    | .p01 => face.1.1 + 1 < width ∧ face.1.2.1 + 1 < width ∧
        face.1.2.2.1 < width
    | .p02 => face.1.1 + 1 < width ∧ face.1.2.1 < width ∧
        face.1.2.2.1 + 1 < width
    | .p12 => face.1.1 < width ∧ face.1.2.1 + 1 < width ∧
        face.1.2.2.1 + 1 < width
    | .p03 | .p13 | .p23 => False

instance (width : Nat) (face : Z4Plaq) : Decidable (InternalOpenCubeFace width face) := by
  rcases face with ⟨vertex, plane⟩
  cases plane <;> unfold InternalOpenCubeFace <;> infer_instance

private def rawOpenCubeLinks (width : Nat) : List Z4Link :=
  (List.range width).flatMap fun x =>
    (List.range width).flatMap fun y =>
      (List.range width).flatMap fun z =>
        [((x, y, z, 0), .x0), ((x, y, z, 0), .x1), ((x, y, z, 0), .x2)]

private def rawOpenCubeFaces (width : Nat) : List Z4Plaq :=
  (List.range width).flatMap fun x =>
    (List.range width).flatMap fun y =>
      (List.range width).flatMap fun z =>
        [((x, y, z, 0), .p01), ((x, y, z, 0), .p02), ((x, y, z, 0), .p12)]

/-- Internal positive links, in lexicographic vertex/direction order. -/
def internalOpenCubeLinks (width : Nat) : List Z4Link :=
  ((rawOpenCubeLinks width).filter
    (fun link => decide (InternalOpenCubeLink width link))).eraseDups

/-- Internal spatial faces, in lexicographic vertex/plane order. -/
def internalOpenCubeFaces (width : Nat) : List Z4Plaq :=
  ((rawOpenCubeFaces width).filter
    (fun face => decide (InternalOpenCubeFace width face))).eraseDups

private theorem rawOpenCubeLinks_mem_iff (width : Nat) (link : Z4Link) :
    link ∈ rawOpenCubeLinks width ↔ TransmittedOpenCubeLink width link := by
  rcases link with ⟨⟨x, y, z, t⟩, dir⟩
  cases dir <;> simp only [rawOpenCubeLinks, TransmittedOpenCubeLink,
    List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq, reduceCtorEq, and_false, and_true, false_or]
  case x0 | x1 | x2 =>
    constructor
    · rintro ⟨a, ha, b, hb, c, hc, hxa, hyb, hzc, ht⟩
      subst a
      subst b
      subst c
      exact ⟨by decide, ha, hb, hc, ht⟩
    · rintro ⟨_, hx, hy, hz, ht⟩
      exact ⟨x, hx, y, hy, z, hz, rfl, rfl, rfl, ht⟩
  case x3 => simp

private theorem rawOpenCubeFaces_contains {width : Nat} {face : Z4Plaq}
    (hface : InternalOpenCubeFace width face) : face ∈ rawOpenCubeFaces width := by
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  cases plane with
  | p01 =>
      rcases hface with ⟨ht, hx, hy, hz⟩
      change t = 0 at ht
      change x + 1 < width at hx
      change y + 1 < width at hy
      change z < width at hz
      subst t
      apply List.mem_flatMap.mpr
      refine ⟨x, List.mem_range.mpr (by omega), ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨y, List.mem_range.mpr (by omega), ?_⟩
      apply List.mem_flatMap.mpr
      exact ⟨z, List.mem_range.mpr hz, by simp⟩
  | p02 =>
      rcases hface with ⟨ht, hx, hy, hz⟩
      change t = 0 at ht
      change x + 1 < width at hx
      change y < width at hy
      change z + 1 < width at hz
      subst t
      apply List.mem_flatMap.mpr
      refine ⟨x, List.mem_range.mpr (by omega), ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨y, List.mem_range.mpr hy, ?_⟩
      apply List.mem_flatMap.mpr
      exact ⟨z, List.mem_range.mpr (by omega), by simp⟩
  | p12 =>
      rcases hface with ⟨ht, hx, hy, hz⟩
      change t = 0 at ht
      change x < width at hx
      change y + 1 < width at hy
      change z + 1 < width at hz
      subst t
      apply List.mem_flatMap.mpr
      refine ⟨x, List.mem_range.mpr hx, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨y, List.mem_range.mpr (by omega), ?_⟩
      apply List.mem_flatMap.mpr
      exact ⟨z, List.mem_range.mpr (by omega), by simp⟩
  | p03 | p13 | p23 => exact False.elim hface.2

private theorem filteredEraseDupsNodup {A : Type}
    [BEq A] [LawfulBEq A] (items : List A) :
    ∀ predicate : A → Bool, (items.filter predicate).eraseDups.Nodup := by
  induction items with
  | nil =>
      intro _
      exact List.nodup_nil
  | cons head tail induction =>
      intro predicate
      rw [List.filter_cons]
      split
      · rw [List.eraseDups_cons, List.filter_filter]
        refine List.nodup_cons.mpr ⟨?_, induction _⟩
        intro hmem
        have hfiltered := List.mem_eraseDups.mp hmem
        have hfalse := (List.mem_filter.mp hfiltered).2
        have hself : (head == head) = true := BEq.rfl
        rw [hself] at hfalse
        contradiction
      · exact induction _

theorem internalOpenCubeLinks_mem_iff (width : Nat) (link : Z4Link) :
    link ∈ internalOpenCubeLinks width ↔ InternalOpenCubeLink width link := by
  constructor
  · intro h
    have hf := List.mem_filter.mp (List.mem_eraseDups.mp h)
    exact of_decide_eq_true hf.2
  · intro h
    apply List.mem_eraseDups.mpr
    exact List.mem_filter.mpr
      ⟨(rawOpenCubeLinks_mem_iff width link).mpr h.1, decide_eq_true h⟩

theorem internalOpenCubeFaces_mem_iff (width : Nat) (face : Z4Plaq) :
    face ∈ internalOpenCubeFaces width ↔ InternalOpenCubeFace width face := by
  constructor
  · intro h
    have hf := List.mem_filter.mp (List.mem_eraseDups.mp h)
    exact of_decide_eq_true hf.2
  · intro h
    apply List.mem_eraseDups.mpr
    exact List.mem_filter.mpr ⟨rawOpenCubeFaces_contains h, decide_eq_true h⟩

theorem internalOpenCubeLinks_nodup (width : Nat) :
    (internalOpenCubeLinks width).Nodup :=
  filteredEraseDupsNodup _ _

theorem internalOpenCubeFaces_nodup (width : Nat) :
    (internalOpenCubeFaces width).Nodup :=
  filteredEraseDupsNodup _ _

private theorem coordinate_lt_of_add_one_lt {coordinate width : Nat}
    (hcoordinate : coordinate + 1 < width) : coordinate < width :=
  Nat.lt_of_succ_lt (by
    simpa only [Nat.succ_eq_add_one] using hcoordinate)

private theorem x0_ne_x3 : Dir4.x0 ≠ .x3 := by decide

private theorem x1_ne_x3 : Dir4.x1 ≠ .x3 := by decide

private theorem x2_ne_x3 : Dir4.x2 ≠ .x3 := by decide

/-- Every boundary edge of a coordinate-internal face satisfies the internal
link predicate. -/
theorem internalOpenCubeFace_edge_property {width : Nat} {face : Z4Plaq}
    (hface : InternalOpenCubeFace width face) {link : Z4Link}
    (hlink : link ∈ edgesOf face) : InternalOpenCubeLink width link := by
  rcases face with ⟨⟨x, y, z, t⟩, plane⟩
  cases plane with
  | p01 =>
      rcases hface with ⟨ht, hx, hy, hz⟩
      change t = 0 at ht
      change x + 1 < width at hx
      change y + 1 < width at hy
      change z < width at hz
      subst t
      simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil,
        or_false] at hlink
      rcases hlink with rfl | rfl | rfl | rfl
      · exact ⟨⟨x0_ne_x3, coordinate_lt_of_add_one_lt hx,
          coordinate_lt_of_add_one_lt hy, hz, rfl⟩, hx⟩
      · exact ⟨⟨x1_ne_x3, coordinate_lt_of_add_one_lt hx,
          coordinate_lt_of_add_one_lt hy, hz, rfl⟩, hy⟩
      · exact ⟨⟨x0_ne_x3, coordinate_lt_of_add_one_lt hx, hy, hz, rfl⟩, hx⟩
      · exact ⟨⟨x1_ne_x3, hx, coordinate_lt_of_add_one_lt hy, hz, rfl⟩, hy⟩
  | p02 =>
      rcases hface with ⟨ht, hx, hy, hz⟩
      change t = 0 at ht
      change x + 1 < width at hx
      change y < width at hy
      change z + 1 < width at hz
      subst t
      simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil,
        or_false] at hlink
      rcases hlink with rfl | rfl | rfl | rfl
      · exact ⟨⟨x0_ne_x3, coordinate_lt_of_add_one_lt hx, hy,
          coordinate_lt_of_add_one_lt hz, rfl⟩, hx⟩
      · exact ⟨⟨x2_ne_x3, coordinate_lt_of_add_one_lt hx, hy,
          coordinate_lt_of_add_one_lt hz, rfl⟩, hz⟩
      · exact ⟨⟨x0_ne_x3, coordinate_lt_of_add_one_lt hx, hy, hz, rfl⟩, hx⟩
      · exact ⟨⟨x2_ne_x3, hx, hy, coordinate_lt_of_add_one_lt hz, rfl⟩, hz⟩
  | p12 =>
      rcases hface with ⟨ht, hx, hy, hz⟩
      change t = 0 at ht
      change x < width at hx
      change y + 1 < width at hy
      change z + 1 < width at hz
      subst t
      simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil,
        or_false] at hlink
      rcases hlink with rfl | rfl | rfl | rfl
      · exact ⟨⟨x1_ne_x3, hx, coordinate_lt_of_add_one_lt hy,
          coordinate_lt_of_add_one_lt hz, rfl⟩, hy⟩
      · exact ⟨⟨x2_ne_x3, hx, coordinate_lt_of_add_one_lt hy,
          coordinate_lt_of_add_one_lt hz, rfl⟩, hz⟩
      · exact ⟨⟨x1_ne_x3, hx, coordinate_lt_of_add_one_lt hy, hz, rfl⟩, hy⟩
      · exact ⟨⟨x2_ne_x3, hx, hy, coordinate_lt_of_add_one_lt hz, rfl⟩, hz⟩
  | p03 | p13 | p23 => exact False.elim hface.2

/-- Every boundary edge of an internal face is an internal link. -/
theorem internalOpenCubeFace_edge_mem {width : Nat} {face : Z4Plaq}
    (hface : face ∈ internalOpenCubeFaces width) {link : Z4Link}
    (hlink : link ∈ edgesOf face) : link ∈ internalOpenCubeLinks width :=
  (internalOpenCubeLinks_mem_iff width link).mpr
    (internalOpenCubeFace_edge_property
      ((internalOpenCubeFaces_mem_iff width face).mp hface) hlink)

/-- Formula-level transmitted links whose positive endpoint exits the strict
vertex box. -/
def outwardOpenCubeLinks (width : Nat) : List Z4Link :=
  ((rawOpenCubeLinks width).filter (fun link =>
    decide (TransmittedOpenCubeLink width link ∧
      ¬ InternalOpenCubeLink width link))).eraseDups

theorem outwardOpenCubeLinks_mem_iff (width : Nat) (link : Z4Link) :
    link ∈ outwardOpenCubeLinks width ↔
      TransmittedOpenCubeLink width link ∧ ¬ InternalOpenCubeLink width link := by
  constructor
  · intro h
    have hf := List.mem_filter.mp (List.mem_eraseDups.mp h)
    exact of_decide_eq_true hf.2
  · intro h
    apply List.mem_eraseDups.mpr
    exact List.mem_filter.mpr
      ⟨(rawOpenCubeLinks_mem_iff width link).mpr h.1, decide_eq_true h⟩

/-- An outward transmitted link occurs in no internal spatial face. -/
theorem outwardOpenCubeLink_not_mem_edges {width : Nat} {link : Z4Link}
    (hout : link ∈ outwardOpenCubeLinks width) {face : Z4Plaq}
    (hface : face ∈ internalOpenCubeFaces width) : link ∉ edgesOf face := by
  intro hlink
  exact ((outwardOpenCubeLinks_mem_iff width link).mp hout).2
    ((internalOpenCubeLinks_mem_iff width link).mp
      (internalOpenCubeFace_edge_mem hface hlink))

/-- The standard oriented cubical coefficient, embedded in the project's
constructive rationals. -/
def internalBoundaryCoefficient (face : Z4Plaq) (link : Z4Link) : Q' :=
  Q'.ofInt (orientedBoundaryCoefficient face link)

theorem internalBoundaryCoefficient_zero_of_not_mem
    {face : Z4Plaq} {link : Z4Link} (hlink : link ∉ edgesOf face) :
    internalBoundaryCoefficient face link = 0 := by
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
  simp [internalBoundaryCoefficient, orientedBoundaryCoefficient,
    hfirst, hsecond, hthird, hfourth]
  exact RingNormaliser.ofInt_zero

theorem outwardOpenCubeLink_boundaryCoefficient_zero {width : Nat} {link : Z4Link}
    (hout : link ∈ outwardOpenCubeLinks width) {face : Z4Plaq}
    (hface : face ∈ internalOpenCubeFaces width) :
    internalBoundaryCoefficient face link = 0 :=
  internalBoundaryCoefficient_zero_of_not_mem
    (outwardOpenCubeLink_not_mem_edges hout hface)

def internalOpenCubeEdgeCount (width : Nat) : Nat :=
  (internalOpenCubeLinks width).length

def internalOpenCubeFaceCount (width : Nat) : Nat :=
  (internalOpenCubeFaces width).length

def selectedInternalOpenCubeFace (width faceIndex : Nat) : Z4Plaq :=
  (internalOpenCubeFaces width).getD faceIndex ((0, 0, 0, 0), .p01)

def selectedInternalOpenCubeLink (width edgeIndex : Nat) : Z4Link :=
  (internalOpenCubeLinks width).getD edgeIndex ((0, 0, 0, 0), .x0)

theorem selectedInternalOpenCubeFace_idxOf {width : Nat} {face : Z4Plaq}
    (hface : face ∈ internalOpenCubeFaces width) :
    selectedInternalOpenCubeFace width ((internalOpenCubeFaces width).idxOf face) = face := by
  have hindex := List.idxOf_lt_length_of_mem hface
  rw [selectedInternalOpenCubeFace, ← List.getElem_eq_getD (h := hindex)]
  exact LawfulBEq.eq_of_beq (List.findIdx_getElem (w := hindex))

theorem selectedInternalOpenCubeLink_idxOf {width : Nat} {link : Z4Link}
    (hlink : link ∈ internalOpenCubeLinks width) :
    selectedInternalOpenCubeLink width ((internalOpenCubeLinks width).idxOf link) = link := by
  have hindex := List.idxOf_lt_length_of_mem hlink
  rw [selectedInternalOpenCubeLink, ← List.getElem_eq_getD (h := hindex)]
  exact LawfulBEq.eq_of_beq (List.findIdx_getElem (w := hindex))

/-- Internal-face by internal-edge curl incidence, with zero outside both
finite coordinate ranges. -/
def internalOpenCubeCurl (width faceIndex edgeIndex : Nat) : Q' :=
  if faceIndex < internalOpenCubeFaceCount width ∧
      edgeIndex < internalOpenCubeEdgeCount width then
    internalBoundaryCoefficient
      (selectedInternalOpenCubeFace width faceIndex)
      (selectedInternalOpenCubeLink width edgeIndex)
  else 0

theorem internalOpenCubeCurl_idxOf {width : Nat} {face : Z4Plaq} {link : Z4Link}
    (hface : face ∈ internalOpenCubeFaces width)
    (hlink : link ∈ internalOpenCubeLinks width) :
    internalOpenCubeCurl width
        ((internalOpenCubeFaces width).idxOf face)
        ((internalOpenCubeLinks width).idxOf link) =
      internalBoundaryCoefficient face link := by
  rw [internalOpenCubeCurl, if_pos
      ⟨List.idxOf_lt_length_of_mem hface, List.idxOf_lt_length_of_mem hlink⟩,
    selectedInternalOpenCubeFace_idxOf hface,
    selectedInternalOpenCubeLink_idxOf hlink]

/-- No boundary coordinate of a listed internal face is omitted by the listed
internal edge carrier. -/
theorem selectedInternalOpenCubeFace_edge_mem {width faceIndex : Nat}
    (hface : faceIndex < internalOpenCubeFaceCount width) {link : Z4Link}
    (hlink : link ∈ edgesOf (selectedInternalOpenCubeFace width faceIndex)) :
    link ∈ internalOpenCubeLinks width := by
  apply internalOpenCubeFace_edge_mem _ hlink
  rw [selectedInternalOpenCubeFace, ← List.getElem_eq_getD (h := hface)]
  exact List.getElem_mem hface

def internalOpenCubeSpatialPrecision (width : Nat) : Nat → Nat → Q' :=
  finiteCurlPrecision (internalOpenCubeFaceCount width) (internalOpenCubeCurl width)

def internalOpenCubeFreeHistoryPrecision (timeBonds width : Nat) : Nat → Nat → Q' :=
  freeHistoryCurlPrecision timeBonds
    (internalOpenCubeEdgeCount width) (internalOpenCubeFaceCount width)
    (internalOpenCubeCurl width)

theorem internalOpenCubeFreeHistoryPrecision_symm
    (timeBonds width left right : Nat) :
    internalOpenCubeFreeHistoryPrecision timeBonds width left right ≈
      internalOpenCubeFreeHistoryPrecision timeBonds width right left :=
  freeHistoryCurlPrecision_symm timeBonds
    (internalOpenCubeEdgeCount width) (internalOpenCubeFaceCount width)
    (internalOpenCubeCurl width) left right

end YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence

#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence.internalOpenCubeLinks_mem_iff
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence.internalOpenCubeFaces_mem_iff
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence.internalOpenCubeFace_edge_property
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence.internalOpenCubeFace_edge_mem
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence.outwardOpenCubeLink_not_mem_edges
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence.outwardOpenCubeLink_boundaryCoefficient_zero
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence.internalOpenCubeCurl_idxOf
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence.selectedInternalOpenCubeFace_edge_mem
#print axioms YMGap.Continuum.SU2QuaternionFiniteGaussianInternalOpenCubeIncidence.internalOpenCubeFreeHistoryPrecision_symm
