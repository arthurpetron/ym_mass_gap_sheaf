/-
# Endpoint boundary characters in the active-link polynomial carrier

For a fixed-link endpoint assignment `assignment`, the boundary character is

    B_assignment(U) = product over fixed links l of U_{assignment l}(r(U_l)).

Here `U_n` is the second-kind Chebyshev polynomial, hence the scalar-coordinate
form of the rank-`n` SU(2) character.  This leaf realizes each one-link factor
with the existing `QPoly`-to-`RatPoly` Horner lift and the shared active-link
coordinate codec.  The canonical representation remains a lazy factor list;
the raw product below is only an opaque bridge for consumers that require one
`RatPoly`.

The evaluation theorem is against one common physical gauge field, so every
occurrence of a fixed physical link reads the same quaternion coordinate.
Both the lazy factors and the opaque product stay inside the exact active-link
coordinate and quaternion-block carriers.

This file attaches neither terminal deltas nor exterior scales.  In
particular, it makes no Haar/spin, fusion, or reachable-kernel identification.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionLazyFactorProductBridge

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenEndpointBoundaryCharacterRatPoly

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPoly
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
open YMGap.Continuum.SU2QuaternionLazyFactorProductBridge
open YMGap.Continuum.SU2QuaternionLazyGlobalSOS
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceRatPolyRealization
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenLazyEndpointScaleAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Fixed-link membership and scalar-coordinate lookup -/

/-- The endpoint kernel's fixed-link list is definitionally the polynomial
carrier's active-link list.  This named bridge prevents downstream character
proofs from depending on that implementation detail. -/
theorem adjacentEvenFixedLink_mem_activeLinks
    {radius : Nat} {link : Z4Link}
    (hlink : link ∈ adjacentEvenFixedLinks radius) :
    link ∈ adjacentEvenActiveLinks radius := by
  simpa only [adjacentEvenFixedLinks, adjacentEvenActiveLinks,
    adjacentEvenFixedSlabLinks] using hlink

/-- The active environment reads the scalar component of a carried physical
link at its canonical base-four coordinate.  The conclusion is literal
equality, so polynomial evaluation may rewrite its Chebyshev argument without
an additional extensional-congruence lemma. -/
theorem adjacentEvenActiveLinkEnvironment_scalar
    {radius : Nat} {link : Z4Link}
    (field : RationalUnitQuaternionGaugeField)
    (hlink : link ∈ adjacentEvenActiveLinks radius) :
    adjacentEvenActiveLinkEnvironment radius field
        (adjacentEvenActiveLinkCoordinate radius link 0) =
      (field link).val.r := by
  let index := listIndexOf link (adjacentEvenActiveLinks radius)
  have hindex : index < (adjacentEvenActiveLinks radius).length :=
    listIndexOf_lt_of_mem link (adjacentEvenActiveLinks radius) hlink
  have hdiv : (4 * index + 0) / 4 = index := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
    omega
  have hmod : (4 * index + 0) % 4 = 0 := by
    rw [Nat.mul_add_mod]
  change
    globalLinkEnvironment (adjacentEvenActiveLinks radius) field
        (4 * index + 0) =
      (field link).val.r
  unfold globalLinkEnvironment
  rw [hdiv, if_pos hindex, hmod]
  unfold index
  rw [getD_listIndexOf_of_mem defaultZ4Link link
    (adjacentEvenActiveLinks radius) hlink]
  rfl

/-! ## 2. One-link character polynomials -/

/-- The rank-`rank` SU(2) character of one fixed physical link, embedded at
that link's scalar coordinate in the common active-link carrier. -/
def adjacentEvenEndpointLinkCharacterPolynomial
    (radius : Nat) (link : Z4Link) (rank : Nat) : RatPoly :=
  qPolyToRatPolyAt
    (adjacentEvenActiveLinkCoordinate radius link 0)
    (chebPoly rank)

/-- Exact common-field evaluation of one carried endpoint character. -/
theorem eval_adjacentEvenEndpointLinkCharacterPolynomial
    (radius : Nat) (link : Z4Link) (rank : Nat)
    (field : RationalUnitQuaternionGaugeField)
    (hlink : link ∈ adjacentEvenActiveLinks radius) :
    evalRatPoly (adjacentEvenActiveLinkEnvironment radius field)
        (adjacentEvenEndpointLinkCharacterPolynomial radius link rank) ≈
      YMGap.Continuum.Cheb.U rank (field link).val.r := by
  unfold adjacentEvenEndpointLinkCharacterPolynomial
  refine Q'.eqv_trans _ _ _
    (eval_qPolyToRatPolyAt
      (adjacentEvenActiveLinkEnvironment radius field)
      (adjacentEvenActiveLinkCoordinate radius link 0)
      (chebPoly rank)) ?_
  rw [adjacentEvenActiveLinkEnvironment_scalar field hlink]
  exact eval_chebPoly rank (field link).val.r

/-- A univariate Horner lift at an in-range coordinate remains inside the
same finite raw-polynomial coordinate carrier. -/
theorem qPolyToRatPolyAt_supportedCoordinates
    {coordinateCount coordinate : Nat}
    (hcoordinate : coordinate < coordinateCount) :
    ∀ polynomial : QPoly.Poly,
      SupportedCoordinates coordinateCount
        (qPolyToRatPolyAt coordinate polynomial)
  | [] => supportedCoordinates_polyZero coordinateCount
  | coefficient :: tail => by
      change
        SupportedCoordinates coordinateCount
          (polyAdd (polySmul coefficient polyOne)
            (polyMul (polyVar coordinate)
              (qPolyToRatPolyAt coordinate tail)))
      apply supportedCoordinates_polyAdd
      · exact supportedCoordinates_polySmul coefficient
          (supportedCoordinates_polyOne coordinateCount)
      · exact supportedCoordinates_polyMul
          (supportedCoordinates_polyVar hcoordinate)
          (qPolyToRatPolyAt_supportedCoordinates hcoordinate tail)

/-- Every carried one-link character has exact active-coordinate support. -/
theorem adjacentEvenEndpointLinkCharacterPolynomial_supported
    {radius : Nat} {link : Z4Link} {rank : Nat}
    (hlink : link ∈ adjacentEvenActiveLinks radius) :
    SupportedCoordinates (adjacentEvenActiveCoordinateCount radius)
      (adjacentEvenEndpointLinkCharacterPolynomial radius link rank) := by
  unfold adjacentEvenEndpointLinkCharacterPolynomial
  apply qPolyToRatPolyAt_supportedCoordinates
  exact adjacentEvenActiveLinkCoordinate_lt hlink (by omega)

/-! ## 3. The lazy boundary-character product -/

/-- Canonical factorized representation of the full endpoint boundary
character.  No cross-link raw polynomial product is materialized here. -/
def adjacentEvenEndpointBoundaryCharacterFactors
    (radius : Nat) (assignment : Z4Link → Nat) : List RatPoly :=
  (adjacentEvenFixedLinks radius).map (fun link =>
    adjacentEvenEndpointLinkCharacterPolynomial
      radius link (assignment link))

/-- The intended common-field value of the full endpoint character. -/
def adjacentEvenEndpointBoundaryCharacterValue
    (radius : Nat) (assignment : Z4Link → Nat)
    (field : RationalUnitQuaternionGaugeField) : Q' :=
  listQProduct (fun link =>
    YMGap.Continuum.Cheb.U (assignment link) (field link).val.r)
    (adjacentEvenFixedLinks radius)

private theorem eval_adjacentEvenEndpointBoundaryCharacterFactorsOn
    (radius : Nat) (assignment : Z4Link → Nat)
    (field : RationalUnitQuaternionGaugeField) :
    ∀ links : List Z4Link,
      (∀ link, link ∈ links → link ∈ adjacentEvenActiveLinks radius) →
      evalRatPolyFactors (adjacentEvenActiveLinkEnvironment radius field)
          (links.map (fun link =>
            adjacentEvenEndpointLinkCharacterPolynomial
              radius link (assignment link))) ≈
        listQProduct (fun link =>
          YMGap.Continuum.Cheb.U (assignment link) (field link).val.r)
          links
  | [], _ => Q'.eqv_refl 1
  | link :: links, hlinks => by
      change
        evalRatPoly (adjacentEvenActiveLinkEnvironment radius field)
              (adjacentEvenEndpointLinkCharacterPolynomial
                radius link (assignment link)) *
            evalRatPolyFactors
              (adjacentEvenActiveLinkEnvironment radius field)
              (links.map (fun source =>
                adjacentEvenEndpointLinkCharacterPolynomial
                  radius source (assignment source))) ≈
          YMGap.Continuum.Cheb.U (assignment link) (field link).val.r *
            listQProduct (fun source =>
              YMGap.Continuum.Cheb.U
                (assignment source) (field source).val.r) links
      exact q_mul_congr
        (eval_adjacentEvenEndpointLinkCharacterPolynomial
          radius link (assignment link) field
          (hlinks link List.mem_cons_self))
        (eval_adjacentEvenEndpointBoundaryCharacterFactorsOn
          radius assignment field links
          (fun source hsource =>
            hlinks source (List.mem_cons_of_mem link hsource)))

/-- Exact evaluation of the lazy boundary-character factors in the common
active-link environment. -/
theorem eval_adjacentEvenEndpointBoundaryCharacterFactors
    (radius : Nat) (assignment : Z4Link → Nat)
    (field : RationalUnitQuaternionGaugeField) :
    evalRatPolyFactors (adjacentEvenActiveLinkEnvironment radius field)
        (adjacentEvenEndpointBoundaryCharacterFactors radius assignment) ≈
      adjacentEvenEndpointBoundaryCharacterValue radius assignment field := by
  unfold adjacentEvenEndpointBoundaryCharacterFactors
    adjacentEvenEndpointBoundaryCharacterValue
  apply eval_adjacentEvenEndpointBoundaryCharacterFactorsOn
  intro link hlink
  exact adjacentEvenFixedLink_mem_activeLinks hlink

/-- Every lazy endpoint-character factor stays inside the exact common
active-coordinate carrier. -/
theorem adjacentEvenEndpointBoundaryCharacterFactors_supported
    (radius : Nat) (assignment : Z4Link → Nat) :
    SupportedRatPolyFactors (adjacentEvenActiveCoordinateCount radius)
      (adjacentEvenEndpointBoundaryCharacterFactors radius assignment) := by
  intro polynomial hpolynomial
  unfold adjacentEvenEndpointBoundaryCharacterFactors at hpolynomial
  rw [List.mem_map] at hpolynomial
  obtain ⟨link, hlink, rfl⟩ := hpolynomial
  exact adjacentEvenEndpointLinkCharacterPolynomial_supported
    (adjacentEvenFixedLink_mem_activeLinks hlink)

/-! ## 4. Opaque one-polynomial bridge -/

/-- One raw polynomial representing the boundary character.  Downstream
files should keep this definition opaque: unfolding the recursive product at
a concrete radius can expand a large duplicate-preserving term list. -/
def adjacentEvenEndpointBoundaryCharacterPolynomial
    (radius : Nat) (assignment : Z4Link → Nat) : RatPoly :=
  ratPolyFactorProduct
    (adjacentEvenEndpointBoundaryCharacterFactors radius assignment)

/-- Exact evaluation of the opaque product representative. -/
theorem eval_adjacentEvenEndpointBoundaryCharacterPolynomial
    (radius : Nat) (assignment : Z4Link → Nat)
    (field : RationalUnitQuaternionGaugeField) :
    evalRatPoly (adjacentEvenActiveLinkEnvironment radius field)
        (adjacentEvenEndpointBoundaryCharacterPolynomial radius assignment) ≈
      adjacentEvenEndpointBoundaryCharacterValue radius assignment field := by
  unfold adjacentEvenEndpointBoundaryCharacterPolynomial
  exact Q'.eqv_trans _ _ _
    (eval_ratPolyFactorProduct
      (adjacentEvenActiveLinkEnvironment radius field)
      (adjacentEvenEndpointBoundaryCharacterFactors radius assignment))
    (eval_adjacentEvenEndpointBoundaryCharacterFactors
      radius assignment field)

/-- The opaque product inherits exact active-coordinate support from its
lazy factors. -/
theorem adjacentEvenEndpointBoundaryCharacterPolynomial_supported
    (radius : Nat) (assignment : Z4Link → Nat) :
    SupportedCoordinates (adjacentEvenActiveCoordinateCount radius)
      (adjacentEvenEndpointBoundaryCharacterPolynomial
        radius assignment) := by
  unfold adjacentEvenEndpointBoundaryCharacterPolynomial
  apply ratPolyFactorProduct_supported
  exact adjacentEvenEndpointBoundaryCharacterFactors_supported
    radius assignment

/-- Native finite-product-Haar block support for the opaque endpoint
character polynomial. -/
theorem adjacentEvenEndpointBoundaryCharacterPolynomial_supportedBlocks
    (radius : Nat) (assignment : Z4Link → Nat) :
    SupportedQuaternionBlocks (adjacentEvenActiveLinks radius).length
      (adjacentEvenEndpointBoundaryCharacterPolynomial
        radius assignment) := by
  rw [← supportedCoordinates_four_mul_iff]
  exact adjacentEvenEndpointBoundaryCharacterPolynomial_supported
    radius assignment

/-! ## 5. Production physical endpoint states -/

/-- Lazy boundary-character factors for the production zero-padded physical
half-state indexed by `state`. -/
def adjacentEvenPhysicalEndpointBoundaryCharacterFactors
    (K radius state : Nat) : List RatPoly :=
  adjacentEvenEndpointBoundaryCharacterFactors radius
    (adjacentEvenPhysicalEndpointAssignment K radius state)

/-- Common-field boundary-character value for one physical endpoint state. -/
def adjacentEvenPhysicalEndpointBoundaryCharacterValue
    (K radius state : Nat)
    (field : RationalUnitQuaternionGaugeField) : Q' :=
  adjacentEvenEndpointBoundaryCharacterValue radius
    (adjacentEvenPhysicalEndpointAssignment K radius state) field

/-- Opaque one-polynomial representative for one physical endpoint state. -/
def adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial
    (K radius state : Nat) : RatPoly :=
  adjacentEvenEndpointBoundaryCharacterPolynomial radius
    (adjacentEvenPhysicalEndpointAssignment K radius state)

/-- Exact factor-list evaluation for every physical endpoint index. -/
theorem eval_adjacentEvenPhysicalEndpointBoundaryCharacterFactors
    (K radius state : Nat)
    (field : RationalUnitQuaternionGaugeField) :
    evalRatPolyFactors (adjacentEvenActiveLinkEnvironment radius field)
        (adjacentEvenPhysicalEndpointBoundaryCharacterFactors
          K radius state) ≈
      adjacentEvenPhysicalEndpointBoundaryCharacterValue
        K radius state field := by
  exact eval_adjacentEvenEndpointBoundaryCharacterFactors radius
    (adjacentEvenPhysicalEndpointAssignment K radius state) field

/-- Exact opaque-polynomial evaluation for every physical endpoint index. -/
theorem eval_adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial
    (K radius state : Nat)
    (field : RationalUnitQuaternionGaugeField) :
    evalRatPoly (adjacentEvenActiveLinkEnvironment radius field)
        (adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial
          K radius state) ≈
      adjacentEvenPhysicalEndpointBoundaryCharacterValue
        K radius state field := by
  exact eval_adjacentEvenEndpointBoundaryCharacterPolynomial radius
    (adjacentEvenPhysicalEndpointAssignment K radius state) field

/-- Exact active-coordinate support of every physical endpoint factor list. -/
theorem adjacentEvenPhysicalEndpointBoundaryCharacterFactors_supported
    (K radius state : Nat) :
    SupportedRatPolyFactors (adjacentEvenActiveCoordinateCount radius)
      (adjacentEvenPhysicalEndpointBoundaryCharacterFactors
        K radius state) := by
  exact adjacentEvenEndpointBoundaryCharacterFactors_supported radius
    (adjacentEvenPhysicalEndpointAssignment K radius state)

/-- Exact active-coordinate support of every physical endpoint polynomial. -/
theorem adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial_supported
    (K radius state : Nat) :
    SupportedCoordinates (adjacentEvenActiveCoordinateCount radius)
      (adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial
        K radius state) := by
  exact adjacentEvenEndpointBoundaryCharacterPolynomial_supported radius
    (adjacentEvenPhysicalEndpointAssignment K radius state)

/-- Native active quaternion-block support of every physical endpoint
polynomial. -/
theorem adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial_supportedBlocks
    (K radius state : Nat) :
    SupportedQuaternionBlocks (adjacentEvenActiveLinks radius).length
      (adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial
        K radius state) := by
  exact adjacentEvenEndpointBoundaryCharacterPolynomial_supportedBlocks radius
    (adjacentEvenPhysicalEndpointAssignment K radius state)

#print axioms adjacentEvenFixedLink_mem_activeLinks
#print axioms adjacentEvenActiveLinkEnvironment_scalar
#print axioms eval_adjacentEvenEndpointLinkCharacterPolynomial
#print axioms qPolyToRatPolyAt_supportedCoordinates
#print axioms adjacentEvenEndpointBoundaryCharacterFactors_supported
#print axioms eval_adjacentEvenEndpointBoundaryCharacterFactors
#print axioms eval_adjacentEvenEndpointBoundaryCharacterPolynomial
#print axioms adjacentEvenEndpointBoundaryCharacterPolynomial_supportedBlocks
#print axioms eval_adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial
#print axioms adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial_supportedBlocks

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenEndpointBoundaryCharacterRatPoly
