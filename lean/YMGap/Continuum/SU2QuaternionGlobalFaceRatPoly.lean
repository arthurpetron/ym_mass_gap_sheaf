/-
# Shared-link rational-polynomial coordinates for finite face families

The sixteen variables of one oriented plaquette are local coordinates.  A
finite family of physical plaquettes must instead use one common coordinate
block for every physical link, so that two faces meeting at a link literally
read the same four variables.

For a supplied link list, this leaf uses the base-four code

    4 * listIndexOf link links + component,

where `component = 0,1,2,3` is the scalar-first quaternion coordinate.  The
global environment decodes the same coordinate by quotient and remainder by
four.  Missing links, invalid components, local coordinates beyond the
sixteen-variable face carrier, and global coordinates beyond the supplied
link list all have the explicit zero fallback.

The main semantic theorem pulls the existing sixteen-coordinate holonomy
polynomial into this shared carrier and evaluates it against one lattice
gauge field.  The adjacent-even specialization uses the production active
link carrier, hence every fixed face that meets the same physical link shares
the same polynomial block.

Only a symbolic list of global face factors is exposed.  No raw product of
the duplicate-preserving `RatPoly` lists is constructed or evaluated here.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
import YMGap.Continuum.RatPolySubstitution
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyRatPoly

namespace YMGap.Continuum.SU2QuaternionGlobalFaceRatPoly

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RatPolySubstitution
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyRatPoly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceWeightDecomposition
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.RepTheory.RationalQuaternion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The common link-major coordinate carrier -/

/-- Four scalar-first quaternion coordinates for every supplied physical
link. -/
def linkQuaternionCoordinateCount (links : List Z4Link) : Nat :=
  4 * links.length

/-- Read one scalar-first coordinate of a unit rational quaternion.  The
function is total, with zero beyond the four physical components. -/
def unitNormCoordinate (input : UnitNorm) : Nat → Q'
  | 0 => input.val.r
  | 1 => input.val.i
  | 2 => input.val.j
  | 3 => input.val.k
  | _ => 0

/-- Decode one global coordinate against a single gauge field.  The quotient
by four selects a physical link and the remainder selects its quaternion
component.  Coordinates beyond the supplied link carrier evaluate to zero. -/
def globalLinkEnvironment
    (links : List Z4Link) (field : RationalUnitQuaternionGaugeField)
    (coordinate : Nat) : Q' :=
  if coordinate / 4 < links.length then
    unitNormCoordinate
      (field (links.getD (coordinate / 4) defaultZ4Link))
      (coordinate % 4)
  else 0

/-- The polynomial variable for one component of one physical link.  A
missing link or invalid component is sent to the zero polynomial rather than
silently aliasing a fallback block. -/
def globalLinkCoordinatePolynomial
    (links : List Z4Link) (link : Z4Link) (component : Nat) : RatPoly :=
  if component < 4 then
    if link ∈ links then
      polyVar (4 * listIndexOf link links + component)
    else polyZero
  else polyZero

@[simp] theorem globalLinkCoordinatePolynomial_of_not_mem
    (links : List Z4Link) (link : Z4Link) (component : Nat)
    (hlink : link ∉ links) :
    globalLinkCoordinatePolynomial links link component = polyZero := by
  simp [globalLinkCoordinatePolynomial, hlink]

@[simp] theorem globalLinkCoordinatePolynomial_of_component_ge
    (links : List Z4Link) (link : Z4Link) (component : Nat)
    (hcomponent : 4 ≤ component) :
    globalLinkCoordinatePolynomial links link component = polyZero := by
  simp [globalLinkCoordinatePolynomial, Nat.not_lt.mpr hcomponent]

/-- A valid link/component code lies in the exact `4 * linkCount` carrier. -/
theorem globalLinkCoordinate_lt_count
    (links : List Z4Link) (link : Z4Link) (component : Nat)
    (hlink : link ∈ links) (hcomponent : component < 4) :
    4 * listIndexOf link links + component <
      linkQuaternionCoordinateCount links := by
  have hindex := listIndexOf_lt_of_mem link links hlink
  unfold linkQuaternionCoordinateCount
  omega

/-- Exact evaluation of one valid shared-link coordinate polynomial. -/
theorem eval_globalLinkCoordinatePolynomial
    (links : List Z4Link) (field : RationalUnitQuaternionGaugeField)
    (link : Z4Link) (component : Nat)
    (hlink : link ∈ links) (hcomponent : component < 4) :
    evalRatPoly (globalLinkEnvironment links field)
        (globalLinkCoordinatePolynomial links link component) ≈
      unitNormCoordinate (field link) component := by
  let index := listIndexOf link links
  have hindex : index < links.length :=
    listIndexOf_lt_of_mem link links hlink
  have hdiv : (4 * index + component) / 4 = index := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hcomponent]
    omega
  have hmod : (4 * index + component) % 4 = component := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hcomponent
  simp only [globalLinkCoordinatePolynomial, if_pos hcomponent, if_pos hlink]
  refine Q'.eqv_trans _ _ _
    (evalRatPoly_var (globalLinkEnvironment links field)
      (4 * index + component)) ?_
  unfold globalLinkEnvironment
  rw [hdiv, if_pos hindex, hmod]
  rw [getD_listIndexOf_of_mem defaultZ4Link link links hlink]
  exact Q'.eqv_refl _

/-! ## 2. Pulling one sixteen-coordinate face into the common carrier -/

/-- Read one of the four physical boundary links in production `edgesOf`
order, with the common lattice fallback outside the active range. -/
def plaquetteEdgeAt (plaquette : Z4Plaq) (slot : Nat) : Z4Link :=
  (edgesOf plaquette).getD slot defaultZ4Link

private theorem listGetD_mem_of_lt
    {A : Type} (fallback : A) :
    ∀ (items : List A) (index : Nat),
      index < items.length → items.getD index fallback ∈ items
  | [], _, hindex => by simp at hindex
  | head :: tail, 0, _ => List.mem_cons_self
  | head :: tail, index + 1, hindex => by
      simp only [List.getD_cons_succ]
      apply List.mem_cons_of_mem head
      apply listGetD_mem_of_lt fallback tail index
      simp only [List.length_cons] at hindex
      omega

/-- Replace each active local edge coordinate by the variable block of its
physical lattice link.  Coordinates beyond the local sixteen-coordinate
carrier are explicitly zero. -/
def faceToGlobalLinkSubstitution
    (links : List Z4Link) (plaquette : Z4Plaq) (coordinate : Nat) : RatPoly :=
  if coordinate < 16 then
    globalLinkCoordinatePolynomial links
      (plaquetteEdgeAt plaquette (coordinate / 4))
      (coordinate % 4)
  else polyZero

@[simp] theorem faceToGlobalLinkSubstitution_of_ge
    (links : List Z4Link) (plaquette : Z4Plaq) (coordinate : Nat)
    (hcoordinate : 16 ≤ coordinate) :
    faceToGlobalLinkSubstitution links plaquette coordinate = polyZero := by
  simp [faceToGlobalLinkSubstitution, Nat.not_lt.mpr hcoordinate]

/-- The list-based four-edge environment is exactly the edge-major,
component-minor quotient/remainder decoder.  This theorem also records the
zero extension beyond coordinate fifteen. -/
theorem fourEdgeEnvironment_eq_indexedCoordinates
    (field : RationalUnitQuaternionGaugeField) (plaquette : Z4Plaq) :
    ∀ coordinate : Nat,
      Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
          (plaquetteOrientedEdgeInput field plaquette) coordinate =
        if coordinate < 16 then
          unitNormCoordinate
            (field (plaquetteEdgeAt plaquette (coordinate / 4)))
            (coordinate % 4)
        else 0
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | 13 => rfl
  | 14 => rfl
  | 15 => rfl
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ
      (Nat.succ (Nat.succ (Nat.succ (Nat.succ
        (Nat.succ (Nat.succ (Nat.succ (Nat.succ
          (Nat.succ (Nat.succ (Nat.succ (Nat.succ _))))))))))))))) => rfl

/-- Evaluation of the complete local-to-global coordinate map agrees with
the official sixteen-coordinate environment of the plaquette. -/
theorem eval_faceToGlobalLinkSubstitution
    (links : List Z4Link) (field : RationalUnitQuaternionGaugeField)
    (plaquette : Z4Plaq)
    (hsupport : ∀ link, link ∈ edgesOf plaquette → link ∈ links) :
    ∀ coordinate : Nat,
      evalRatPoly (globalLinkEnvironment links field)
          (faceToGlobalLinkSubstitution links plaquette coordinate) ≈
        Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.fourEdgeEnvironment
          (plaquetteOrientedEdgeInput field plaquette) coordinate := by
  intro coordinate
  have hindexed :=
    fourEdgeEnvironment_eq_indexedCoordinates field plaquette coordinate
  by_cases hcoordinate : coordinate < 16
  · have hslot : coordinate / 4 < 4 := by omega
    have hedge : plaquetteEdgeAt plaquette (coordinate / 4) ∈
        edgesOf plaquette := by
      exact listGetD_mem_of_lt defaultZ4Link (edgesOf plaquette)
        (coordinate / 4) (by
          obtain ⟨vertex, plane⟩ := plaquette
          cases plane <;> simpa [edgesOf] using hslot)
    have hcomponent : coordinate % 4 < 4 :=
      Nat.mod_lt coordinate (by omega)
    rw [faceToGlobalLinkSubstitution, if_pos hcoordinate]
    refine Q'.eqv_trans _ _ _
      (eval_globalLinkCoordinatePolynomial links field
        (plaquetteEdgeAt plaquette (coordinate / 4))
        (coordinate % 4) (hsupport _ hedge) hcomponent) ?_
    rw [if_pos hcoordinate] at hindexed
    exact Q'.eqv_of_eq hindexed.symm
  · rw [faceToGlobalLinkSubstitution, if_neg hcoordinate]
    refine Q'.eqv_trans _ _ _
      (evalRatPoly_zero (globalLinkEnvironment links field)) ?_
    rw [if_neg hcoordinate] at hindexed
    exact Q'.eqv_of_eq hindexed.symm

/-- One complete anchor-face polynomial pulled from its sixteen local edge
coordinates into the common shared-link carrier. -/
def globalAnchorFacePolynomial
    (cutoff : Nat) (links : List Z4Link) (plaquette : Z4Plaq) : RatPoly :=
  substitute (faceToGlobalLinkSubstitution links plaquette)
    (anchorFaceHolonomyWeightedSOSPolynomial cutoff)

/-- Exact physical evaluation of one globally coordinated face polynomial
against a single gauge field. -/
theorem eval_globalAnchorFacePolynomial
    (cutoff : Nat) (links : List Z4Link)
    (field : RationalUnitQuaternionGaugeField) (plaquette : Z4Plaq)
    (hsupport : ∀ link, link ∈ edgesOf plaquette → link ∈ links) :
    evalRatPoly (globalLinkEnvironment links field)
        (globalAnchorFacePolynomial cutoff links plaquette) ≈
      anchorTruncatedFaceClassValue cutoff
        (latticePlaquetteHolonomy field plaquette).val.r := by
  change
    evalRatPoly (globalLinkEnvironment links field)
        (substitute (faceToGlobalLinkSubstitution links plaquette)
          (anchorFaceHolonomyWeightedSOSPolynomial cutoff)) ≈
      anchorTruncatedFaceClassValue cutoff
        (standardPlaquetteHolonomy
          (plaquetteOrientedEdgeInput field plaquette)).val.r
  exact Q'.eqv_trans _ _ _
    (eval_substitute
      (faceToGlobalLinkSubstitution links plaquette)
      (anchorFaceHolonomyWeightedSOSPolynomial cutoff)
      (globalLinkEnvironment links field))
    (Q'.eqv_trans _ _ _
      (evalRatPoly_environment_congr
        (eval_faceToGlobalLinkSubstitution links field plaquette hsupport)
        (anchorFaceHolonomyWeightedSOSPolynomial cutoff))
      (eval_anchorFaceHolonomyWeightedSOSPolynomial_eqv_classValue
        cutoff (plaquetteOrientedEdgeInput field plaquette)))

/-! ## 3. Production adjacent-even specialization -/

/-- The generic base-four count is literally the production active-coordinate
count on the adjacent-even carrier. -/
theorem linkQuaternionCoordinateCount_activeLinks (radius : Nat) :
    linkQuaternionCoordinateCount (adjacentEvenActiveLinks radius) =
      adjacentEvenActiveCoordinateCount radius := rfl

/-- On a carried link and a genuine component, the generic polynomial uses
the exact coordinate named by the production active-link codec. -/
theorem globalLinkCoordinatePolynomial_activeLinks
    {radius : Nat} {link : Z4Link} {component : Nat}
    (hlink : link ∈ adjacentEvenActiveLinks radius)
    (hcomponent : component < 4) :
    globalLinkCoordinatePolynomial
        (adjacentEvenActiveLinks radius) link component =
      polyVar
        (adjacentEvenActiveLinkCoordinate radius link component) := by
  simp only [globalLinkCoordinatePolynomial, if_pos hcomponent, if_pos hlink,
    adjacentEvenActiveLinkCoordinate, adjacentEvenActiveLinkIndex]

/-- The common environment on the production adjacent-even active-link
carrier. -/
def adjacentEvenActiveLinkEnvironment
    (radius : Nat) (field : RationalUnitQuaternionGaugeField) : Nat → Q' :=
  globalLinkEnvironment (adjacentEvenActiveLinks radius) field

/-- One fixed physical face, now expressed in the common production active
link carrier. -/
def adjacentEvenFixedFaceGlobalPolynomial
    (cutoff radius id : Nat) : RatPoly :=
  globalAnchorFacePolynomial cutoff (adjacentEvenActiveLinks radius)
    (slabPlaquetteAt (adjacentEvenExtent radius) id)

/-- Exact evaluation of a production fixed-face polynomial against one
lattice gauge field.  The membership hypothesis is precisely what certifies
that all four face edges belong to the common active-link carrier. -/
theorem eval_adjacentEvenFixedFaceGlobalPolynomial
    (cutoff radius id : Nat) (field : RationalUnitQuaternionGaugeField)
    (hid : id ∈ adjacentEvenFixedFaceIds radius) :
    evalRatPoly (adjacentEvenActiveLinkEnvironment radius field)
        (adjacentEvenFixedFaceGlobalPolynomial cutoff radius id) ≈
      anchorTruncatedFaceClassValue cutoff
        (latticePlaquetteHolonomy field
          (slabPlaquetteAt (adjacentEvenExtent radius) id)).val.r := by
  apply eval_globalAnchorFacePolynomial
  intro link hlink
  apply adjacentEvenFixedFaceLink_mem_activeLinks hid
  simpa only [adjacentEvenFixedFaceLinks] using hlink

/-- The finite family of globally coordinated fixed-face factors.  This is a
symbolic factor list, deliberately not a raw expanded `RatPoly` product. -/
def adjacentEvenFixedFaceGlobalPolynomialFactors
    (cutoff radius : Nat) : List RatPoly :=
  (adjacentEvenFixedFaceIds radius).map
    (adjacentEvenFixedFaceGlobalPolynomial cutoff radius)

#print axioms globalLinkCoordinate_lt_count
#print axioms eval_globalLinkCoordinatePolynomial
#print axioms fourEdgeEnvironment_eq_indexedCoordinates
#print axioms eval_faceToGlobalLinkSubstitution
#print axioms eval_globalAnchorFacePolynomial
#print axioms globalLinkCoordinatePolynomial_activeLinks
#print axioms eval_adjacentEvenFixedFaceGlobalPolynomial

end YMGap.Continuum.SU2QuaternionGlobalFaceRatPoly
