/-
# Mod-two cellular dyadic pushforward on finite Z4 supports

The occupancy-OR block map is positive and local but fails to preserve gauge
closure on arbitrary fine supports.  This module replaces OR aggregation by
the cellular pushforward over F2.  Coordinatewise floor-halving sends a fine
face to a coarse face only when both spanning directions survive.  Multiple
fine faces with the same nondegenerate image are combined by XOR.

The cellular boundary calculation is carried out independently of any
Yang--Mills weight.  No Gibbs-law, activity, coupling-flow, or SU(2) measure
pushforward is asserted.
-/

import YMGap.Continuum.Z4DyadicDeterministicSupportKernel

namespace YMGap.Continuum.Z4DyadicModTwoCellularKernel

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4UnitCubeEnumerationParity
open YMGap.Continuum.Z4UnitCubeIncidenceParity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Floor projection and the nondegenerate preimage fibres -/

def vertexCoord : Z4Vertex → Dir4 → Nat
  | (a, _, _, _), .x0 => a
  | (_, b, _, _), .x1 => b
  | (_, _, c, _), .x2 => c
  | (_, _, _, d), .x3 => d

/-- Coordinatewise floor-halving of a lattice vertex. -/
def dyadicVertexProjection : Z4Vertex → Z4Vertex
  | (a, b, c, d) => (a / 2, b / 2, c / 2, d / 2)

/-- The underlying coarse face of a fine face.  It contributes to the
cellular pushforward only when `dyadicPlaquetteNondegenerateB` is true. -/
def dyadicPlaquetteProjection (fine : Z4Plaq) : Z4Plaq :=
  (dyadicVertexProjection fine.1, fine.2)

def dyadicPlaquetteNondegenerateB (fine : Z4Plaq) : Bool :=
  decide (vertexCoord fine.1 (dirsOf fine.2).1 % 2 = 1) &&
    decide (vertexCoord fine.1 (dirsOf fine.2).2 % 2 = 1)

/-- The four fine faces having a fixed coarse face as a nondegenerate image.
The two transverse dyadic bits are free and the two spanning bits are one. -/
def dyadicFacePreimages : Z4Plaq → List Z4Plaq
  | ((a, b, c, d), .p01) =>
      [((2*a+1, 2*b+1, 2*c,   2*d),   .p01),
       ((2*a+1, 2*b+1, 2*c+1, 2*d),   .p01),
       ((2*a+1, 2*b+1, 2*c,   2*d+1), .p01),
       ((2*a+1, 2*b+1, 2*c+1, 2*d+1), .p01)]
  | ((a, b, c, d), .p02) =>
      [((2*a+1, 2*b,   2*c+1, 2*d),   .p02),
       ((2*a+1, 2*b+1, 2*c+1, 2*d),   .p02),
       ((2*a+1, 2*b,   2*c+1, 2*d+1), .p02),
       ((2*a+1, 2*b+1, 2*c+1, 2*d+1), .p02)]
  | ((a, b, c, d), .p03) =>
      [((2*a+1, 2*b,   2*c,   2*d+1), .p03),
       ((2*a+1, 2*b+1, 2*c,   2*d+1), .p03),
       ((2*a+1, 2*b,   2*c+1, 2*d+1), .p03),
       ((2*a+1, 2*b+1, 2*c+1, 2*d+1), .p03)]
  | ((a, b, c, d), .p12) =>
      [((2*a,   2*b+1, 2*c+1, 2*d),   .p12),
       ((2*a+1, 2*b+1, 2*c+1, 2*d),   .p12),
       ((2*a,   2*b+1, 2*c+1, 2*d+1), .p12),
       ((2*a+1, 2*b+1, 2*c+1, 2*d+1), .p12)]
  | ((a, b, c, d), .p13) =>
      [((2*a,   2*b+1, 2*c,   2*d+1), .p13),
       ((2*a+1, 2*b+1, 2*c,   2*d+1), .p13),
       ((2*a,   2*b+1, 2*c+1, 2*d+1), .p13),
       ((2*a+1, 2*b+1, 2*c+1, 2*d+1), .p13)]
  | ((a, b, c, d), .p23) =>
      [((2*a,   2*b,   2*c+1, 2*d+1), .p23),
       ((2*a+1, 2*b,   2*c+1, 2*d+1), .p23),
       ((2*a,   2*b+1, 2*c+1, 2*d+1), .p23),
       ((2*a+1, 2*b+1, 2*c+1, 2*d+1), .p23)]

/-- The eight nondegenerate fine links above one coarse link. -/
def dyadicLinkPreimages : Z4Link → List Z4Link
  | ((a, b, c, d), .x0) =>
      [((2*a+1, 2*b,   2*c,   2*d),   .x0),
       ((2*a+1, 2*b+1, 2*c,   2*d),   .x0),
       ((2*a+1, 2*b,   2*c+1, 2*d),   .x0),
       ((2*a+1, 2*b+1, 2*c+1, 2*d),   .x0),
       ((2*a+1, 2*b,   2*c,   2*d+1), .x0),
       ((2*a+1, 2*b+1, 2*c,   2*d+1), .x0),
       ((2*a+1, 2*b,   2*c+1, 2*d+1), .x0),
       ((2*a+1, 2*b+1, 2*c+1, 2*d+1), .x0)]
  | ((a, b, c, d), .x1) =>
      [((2*a,   2*b+1, 2*c,   2*d),   .x1),
       ((2*a+1, 2*b+1, 2*c,   2*d),   .x1),
       ((2*a,   2*b+1, 2*c+1, 2*d),   .x1),
       ((2*a+1, 2*b+1, 2*c+1, 2*d),   .x1),
       ((2*a,   2*b+1, 2*c,   2*d+1), .x1),
       ((2*a+1, 2*b+1, 2*c,   2*d+1), .x1),
       ((2*a,   2*b+1, 2*c+1, 2*d+1), .x1),
       ((2*a+1, 2*b+1, 2*c+1, 2*d+1), .x1)]
  | ((a, b, c, d), .x2) =>
      [((2*a,   2*b,   2*c+1, 2*d),   .x2),
       ((2*a+1, 2*b,   2*c+1, 2*d),   .x2),
       ((2*a,   2*b+1, 2*c+1, 2*d),   .x2),
       ((2*a+1, 2*b+1, 2*c+1, 2*d),   .x2),
       ((2*a,   2*b,   2*c+1, 2*d+1), .x2),
       ((2*a+1, 2*b,   2*c+1, 2*d+1), .x2),
       ((2*a,   2*b+1, 2*c+1, 2*d+1), .x2),
       ((2*a+1, 2*b+1, 2*c+1, 2*d+1), .x2)]
  | ((a, b, c, d), .x3) =>
      [((2*a,   2*b,   2*c,   2*d+1), .x3),
       ((2*a+1, 2*b,   2*c,   2*d+1), .x3),
       ((2*a,   2*b+1, 2*c,   2*d+1), .x3),
       ((2*a+1, 2*b+1, 2*c,   2*d+1), .x3),
       ((2*a,   2*b,   2*c+1, 2*d+1), .x3),
       ((2*a+1, 2*b,   2*c+1, 2*d+1), .x3),
       ((2*a,   2*b+1, 2*c+1, 2*d+1), .x3),
       ((2*a+1, 2*b+1, 2*c+1, 2*d+1), .x3)]

private theorem odd_half (coordinate : Nat) :
    (2 * coordinate + 1) / 2 = coordinate := by
  rw [Nat.mul_add_div (m := 2) (by omega) coordinate 1]
  simp

/-- Every face in the explicit four-element fibre is nondegenerate and its
coordinatewise floor-halved image is the advertised coarse face.  Thus the
enumerated fibre used below is tied to the geometric projection, rather than
being an unrelated blocking table. -/
theorem facePreimage_is_nondegenerate_projection
    {coarsePlaquette finePlaquette : Z4Plaq}
    (hpreimage : finePlaquette ∈ dyadicFacePreimages coarsePlaquette) :
    dyadicPlaquetteNondegenerateB finePlaquette = true ∧
      dyadicPlaquetteProjection finePlaquette = coarsePlaquette := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarsePlaquette
  cases plane <;>
    simp only [dyadicFacePreimages, List.mem_cons, List.not_mem_nil,
      or_false] at hpreimage <;>
    rcases hpreimage with h | h | h | h <;>
    subst finePlaquette <;>
    exact ⟨by
      simp [dyadicPlaquetteNondegenerateB, vertexCoord, dirsOf], by
      simp [dyadicPlaquetteProjection, dyadicVertexProjection, odd_half]⟩

#print axioms facePreimage_is_nondegenerate_projection

/-! ## 2. F2 chain operations and the cellular boundary identity -/

def xorList {A : Type} (coefficient : A → Bool) : List A → Bool
  | [] => false
  | head :: tail => coefficient head ^^ xorList coefficient tail

private theorem xorList_congr_on {A : Type}
    (left right : A → Bool) :
    ∀ entries : List A,
      (∀ entry, entry ∈ entries → left entry = right entry) →
      xorList left entries = xorList right entries
  | [], _ => rfl
  | head :: tail, hagree => by
      have hhead : left head = right head :=
        hagree head List.mem_cons_self
      have htail : xorList left tail = xorList right tail :=
        xorList_congr_on left right tail
          (fun entry hmem =>
            hagree entry (List.mem_cons_of_mem head hmem))
      rw [xorList, xorList, hhead, htail]

def dyadicFacePushforward
    (fineCoefficient : Z4Plaq → Bool) (coarse : Z4Plaq) : Bool :=
  xorList fineCoefficient (dyadicFacePreimages coarse)

def dyadicLinkPushforward
    (fineCoefficient : Z4Link → Bool) (coarse : Z4Link) : Bool :=
  xorList fineCoefficient (dyadicLinkPreimages coarse)

/-- Locality in its exact finite-fibre form: the pushed coefficient at one
coarse face depends only on the four nondegenerate fine faces above it. -/
theorem dyadicFacePushforward_local
    (first second : Z4Plaq → Bool) (coarsePlaquette : Z4Plaq)
    (hlocal : ∀ finePlaquette,
      finePlaquette ∈ dyadicFacePreimages coarsePlaquette →
        first finePlaquette = second finePlaquette) :
    dyadicFacePushforward first coarsePlaquette =
      dyadicFacePushforward second coarsePlaquette := by
  unfold dyadicFacePushforward
  exact xorList_congr_on first second
    (dyadicFacePreimages coarsePlaquette) hlocal

def backwardFaceCoefficient (coefficient : Z4Plaq → Bool)
    (vertex : Z4Vertex) (edgeDirection transverse : Dir4) : Bool :=
  if vertexCoord vertex transverse = 0 then false
  else coefficient (subE vertex transverse, planeOf edgeDirection transverse)

def incidentPlanePairCoefficient (coefficient : Z4Plaq → Bool)
    (vertex : Z4Vertex) (edgeDirection transverse : Dir4) : Bool :=
  coefficient (vertex, planeOf edgeDirection transverse) ^^
    backwardFaceCoefficient coefficient vertex edgeDirection transverse

/-- Mod-two coefficient of the cellular boundary at one positive-direction
link.  The zero-coordinate test removes the nonexistent negative-side face. -/
def cellularBoundaryCoefficient
    (coefficient : Z4Plaq → Bool) : Z4Link → Bool
  | (vertex, .x0) =>
      incidentPlanePairCoefficient coefficient vertex .x0 .x1 ^^
      (incidentPlanePairCoefficient coefficient vertex .x0 .x2 ^^
       incidentPlanePairCoefficient coefficient vertex .x0 .x3)
  | (vertex, .x1) =>
      incidentPlanePairCoefficient coefficient vertex .x1 .x0 ^^
      (incidentPlanePairCoefficient coefficient vertex .x1 .x2 ^^
       incidentPlanePairCoefficient coefficient vertex .x1 .x3)
  | (vertex, .x2) =>
      incidentPlanePairCoefficient coefficient vertex .x2 .x0 ^^
      (incidentPlanePairCoefficient coefficient vertex .x2 .x1 ^^
       incidentPlanePairCoefficient coefficient vertex .x2 .x3)
  | (vertex, .x3) =>
      incidentPlanePairCoefficient coefficient vertex .x3 .x0 ^^
      (incidentPlanePairCoefficient coefficient vertex .x3 .x1 ^^
       incidentPlanePairCoefficient coefficient vertex .x3 .x2)

private theorem boolToNat_xor (left right : Bool) :
    (left ^^ right).toNat = (left.toNat + right.toNat) % 2 := by
  cases left <;> cases right <;> rfl

private theorem bool_eq_of_toNat_eq {left right : Bool}
    (h : left.toNat = right.toNat) : left = right := by
  cases left <;> cases right <;> simp at h ⊢

/-- One plane-pair of the boundary commutes with the dyadic projection.  This
is the local cancellation mechanism: the two fine faces collapsed in the
transverse direction occur twice and cancel over F2. -/
theorem dyadicIncidentPlanePair_commutes
    (fineCoefficient : Z4Plaq → Bool) (coarseVertex : Z4Vertex)
    (edgeDirection transverse : Dir4) (hne : edgeDirection ≠ transverse) :
    incidentPlanePairCoefficient
        (dyadicFacePushforward fineCoefficient)
        coarseVertex edgeDirection transverse =
      xorList
        (fun fineLink =>
          incidentPlanePairCoefficient fineCoefficient fineLink.1
            edgeDirection transverse)
        (dyadicLinkPreimages (coarseVertex, edgeDirection)) := by
  obtain ⟨a, b, c, d⟩ := coarseVertex
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases edgeDirection <;> cases transverse <;>
    simp [incidentPlanePairCoefficient, backwardFaceCoefficient,
      vertexCoord, dyadicFacePushforward, dyadicFacePreimages,
      dyadicLinkPreimages, xorList, subE, planeOf, Nat.mul_succ,
      Nat.add_assoc] at hne ⊢
  all_goals
    apply bool_eq_of_toNat_eq
    simp only [boolToNat_xor]
    omega

#print axioms dyadicIncidentPlanePair_commutes

private theorem xorList_pointwise_xor {A : Type}
    (left right : A → Bool) (entries : List A) :
    xorList (fun entry => left entry ^^ right entry) entries =
      (xorList left entries ^^ xorList right entries) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      simp only [xorList, ih]
      cases left head <;> cases right head <;>
        cases xorList left tail <;> cases xorList right tail <;> rfl

private theorem xorList_pointwise_three {A : Type}
    (first second third : A → Bool) (entries : List A) :
    xorList (fun entry =>
        first entry ^^ (second entry ^^ third entry)) entries =
      (xorList first entries ^^
        (xorList second entries ^^ xorList third entries)) := by
  rw [xorList_pointwise_xor]
  rw [xorList_pointwise_xor]

/-- The F2 cellular boundary commutes with coordinatewise floor-halving.
Equivalently, the explicitly enumerated nondegenerate face fibres and link
fibres define a chain map from fine cubical 2-chains to coarse cubical
2-chains. -/
theorem dyadicCellularBoundary_commutes
    (fineCoefficient : Z4Plaq → Bool) (coarseLink : Z4Link) :
    cellularBoundaryCoefficient
        (dyadicFacePushforward fineCoefficient) coarseLink =
      dyadicLinkPushforward
        (cellularBoundaryCoefficient fineCoefficient) coarseLink := by
  obtain ⟨coarseVertex, edgeDirection⟩ := coarseLink
  cases edgeDirection with
  | x0 =>
      simp only [cellularBoundaryCoefficient]
      rw [dyadicIncidentPlanePair_commutes fineCoefficient coarseVertex .x0 .x1
          (by decide),
        dyadicIncidentPlanePair_commutes fineCoefficient coarseVertex .x0 .x2
          (by decide),
        dyadicIncidentPlanePair_commutes fineCoefficient coarseVertex .x0 .x3
          (by decide)]
      unfold dyadicLinkPushforward
      calc
        _ = xorList
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x0 .x1 ^^
                (incidentPlanePairCoefficient fineCoefficient fineLink.1 .x0 .x2 ^^
                 incidentPlanePairCoefficient fineCoefficient fineLink.1 .x0 .x3))
            (dyadicLinkPreimages (coarseVertex, .x0)) :=
          (xorList_pointwise_three
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x0 .x1)
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x0 .x2)
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x0 .x3)
            (dyadicLinkPreimages (coarseVertex, .x0))).symm
        _ = _ := by
          obtain ⟨a, b, c, d⟩ := coarseVertex
          rfl
  | x1 =>
      simp only [cellularBoundaryCoefficient]
      rw [dyadicIncidentPlanePair_commutes fineCoefficient coarseVertex .x1 .x0
          (by decide),
        dyadicIncidentPlanePair_commutes fineCoefficient coarseVertex .x1 .x2
          (by decide),
        dyadicIncidentPlanePair_commutes fineCoefficient coarseVertex .x1 .x3
          (by decide)]
      unfold dyadicLinkPushforward
      calc
        _ = xorList
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x1 .x0 ^^
                (incidentPlanePairCoefficient fineCoefficient fineLink.1 .x1 .x2 ^^
                 incidentPlanePairCoefficient fineCoefficient fineLink.1 .x1 .x3))
            (dyadicLinkPreimages (coarseVertex, .x1)) :=
          (xorList_pointwise_three
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x1 .x0)
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x1 .x2)
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x1 .x3)
            (dyadicLinkPreimages (coarseVertex, .x1))).symm
        _ = _ := by
          obtain ⟨a, b, c, d⟩ := coarseVertex
          rfl
  | x2 =>
      simp only [cellularBoundaryCoefficient]
      rw [dyadicIncidentPlanePair_commutes fineCoefficient coarseVertex .x2 .x0
          (by decide),
        dyadicIncidentPlanePair_commutes fineCoefficient coarseVertex .x2 .x1
          (by decide),
        dyadicIncidentPlanePair_commutes fineCoefficient coarseVertex .x2 .x3
          (by decide)]
      unfold dyadicLinkPushforward
      calc
        _ = xorList
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x2 .x0 ^^
                (incidentPlanePairCoefficient fineCoefficient fineLink.1 .x2 .x1 ^^
                 incidentPlanePairCoefficient fineCoefficient fineLink.1 .x2 .x3))
            (dyadicLinkPreimages (coarseVertex, .x2)) :=
          (xorList_pointwise_three
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x2 .x0)
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x2 .x1)
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x2 .x3)
            (dyadicLinkPreimages (coarseVertex, .x2))).symm
        _ = _ := by
          obtain ⟨a, b, c, d⟩ := coarseVertex
          rfl
  | x3 =>
      simp only [cellularBoundaryCoefficient]
      rw [dyadicIncidentPlanePair_commutes fineCoefficient coarseVertex .x3 .x0
          (by decide),
        dyadicIncidentPlanePair_commutes fineCoefficient coarseVertex .x3 .x1
          (by decide),
        dyadicIncidentPlanePair_commutes fineCoefficient coarseVertex .x3 .x2
          (by decide)]
      unfold dyadicLinkPushforward
      calc
        _ = xorList
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x3 .x0 ^^
                (incidentPlanePairCoefficient fineCoefficient fineLink.1 .x3 .x1 ^^
                 incidentPlanePairCoefficient fineCoefficient fineLink.1 .x3 .x2))
            (dyadicLinkPreimages (coarseVertex, .x3)) :=
          (xorList_pointwise_three
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x3 .x0)
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x3 .x1)
            (fun fineLink : Z4Link =>
              incidentPlanePairCoefficient fineCoefficient fineLink.1 .x3 .x2)
            (dyadicLinkPreimages (coarseVertex, .x3))).symm
        _ = _ := by
          obtain ⟨a, b, c, d⟩ := coarseVertex
          rfl

#print axioms dyadicCellularBoundary_commutes

/-! ## 3. Exact mod-two closure preservation -/

/-- A cubical 2-chain is closed when every link coefficient in its mod-two
boundary vanishes.  For a zero-one support coefficient this is precisely the
even face-incidence condition, stated without introducing an integer-valued
intermediate count. -/
def ModTwoClosed (coefficient : Z4Plaq → Bool) : Prop :=
  ∀ link, cellularBoundaryCoefficient coefficient link = false

private theorem xorList_false_of_coefficients_false {A : Type}
    (coefficient : A → Bool) (hzero : ∀ entry, coefficient entry = false) :
    ∀ entries : List A, xorList coefficient entries = false
  | [] => rfl
  | head :: tail => by
      rw [xorList, hzero head,
        xorList_false_of_coefficients_false coefficient hzero tail]
      rfl

/-- Closed fine F2 2-chains have closed coarse images under the cellular
dyadic pushforward. -/
theorem dyadicFacePushforward_preserves_modTwoClosed
    (fineCoefficient : Z4Plaq → Bool)
    (hclosed : ModTwoClosed fineCoefficient) :
    ModTwoClosed (dyadicFacePushforward fineCoefficient) := by
  intro coarseLink
  rw [dyadicCellularBoundary_commutes]
  unfold dyadicLinkPushforward
  exact xorList_false_of_coefficients_false
    (cellularBoundaryCoefficient fineCoefficient)
    hclosed
    (dyadicLinkPreimages coarseLink)

#print axioms dyadicFacePushforward_preserves_modTwoClosed

/-! ## 4. Canonical finite-support output -/

/-- The zero-one F2 coefficient represented by a finite support list. -/
def supportCoefficient (support : List Z4Plaq) (plaquette : Z4Plaq) : Bool :=
  decide (plaquette ∈ support)

/-- Canonical finite support for the pushed coefficient inside coarse box
`n`.  The box filter fixes both order and multiplicity. -/
def dyadicModTwoPushforwardSupport (n : Nat)
    (fineSupport : List Z4Plaq) : List Z4Plaq :=
  (boxPlaquettes n).filter
    (dyadicFacePushforward (supportCoefficient fineSupport))

theorem mem_dyadicModTwoPushforwardSupport_iff
    (n : Nat) (fineSupport : List Z4Plaq) (coarsePlaquette : Z4Plaq) :
    coarsePlaquette ∈ dyadicModTwoPushforwardSupport n fineSupport ↔
      coarsePlaquette ∈ boxPlaquettes n ∧
        dyadicFacePushforward (supportCoefficient fineSupport)
          coarsePlaquette = true := by
  simp [dyadicModTwoPushforwardSupport]

theorem dyadicModTwoPushforwardSupport_mem_stateSpace
    (n : Nat) (fineSupport : List Z4Plaq) :
    dyadicModTwoPushforwardSupport n fineSupport ∈
      sublists (boxPlaquettes n) := by
  unfold dyadicModTwoPushforwardSupport
  exact Z4CutoffOneSupportBijection.filter_mem_sublists _ _

theorem dyadicModTwoPushforwardSupport_nodup
    (n : Nat) (fineSupport : List Z4Plaq) :
    (dyadicModTwoPushforwardSupport n fineSupport).Nodup := by
  unfold dyadicModTwoPushforwardSupport
  exact List.filter_sublist.nodup (boxPlaquettes_nodup n)

private theorem xorList_true_exists {A : Type} (coefficient : A → Bool) :
    ∀ entries : List A, xorList coefficient entries = true →
      ∃ entry, entry ∈ entries ∧ coefficient entry = true
  | [], htrue => by cases htrue
  | head :: tail, htrue => by
      cases hhead : coefficient head with
      | false =>
          have htail : xorList coefficient tail = true := by
            simpa [xorList, hhead] using htrue
          obtain ⟨entry, hmem, hentry⟩ :=
            xorList_true_exists coefficient tail htail
          exact ⟨entry, List.mem_cons_of_mem head hmem, hentry⟩
      | true =>
          exact ⟨head, List.mem_cons_self, hhead⟩

/-- A nondegenerate fine face in the explicit fibre of a coarse face cannot
lie in the doubled fine box unless that coarse face lies in the original
box. -/
theorem coarse_mem_box_of_facePreimage_mem_doubled_box
    {n : Nat} {coarsePlaquette finePlaquette : Z4Plaq}
    (hpreimage : finePlaquette ∈ dyadicFacePreimages coarsePlaquette)
    (hfineBox : finePlaquette ∈ boxPlaquettes (2 * n)) :
    coarsePlaquette ∈ boxPlaquettes n := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := coarsePlaquette
  cases plane <;>
    simp only [dyadicFacePreimages, List.mem_cons, List.not_mem_nil,
      or_false] at hpreimage <;>
    rcases hpreimage with h | h | h | h <;>
    subst finePlaquette <;>
    simp only [mem_boxPlaquettes] at hfineBox ⊢ <;>
    exact ⟨by omega, by omega, by omega, by omega⟩

/-- If the fine support lies in the doubled box, every nonzero coefficient
of its global cellular image lies in the coarse box. -/
theorem dyadicFacePushforward_true_implies_mem_box
    {n : Nat} {fineSupport : List Z4Plaq}
    (hfineBox : ∀ finePlaquette, finePlaquette ∈ fineSupport →
      finePlaquette ∈ boxPlaquettes (2 * n))
    {coarsePlaquette : Z4Plaq}
    (htrue : dyadicFacePushforward (supportCoefficient fineSupport)
      coarsePlaquette = true) :
    coarsePlaquette ∈ boxPlaquettes n := by
  unfold dyadicFacePushforward at htrue
  obtain ⟨finePlaquette, hpreimage, hfineCoefficient⟩ :=
    xorList_true_exists (supportCoefficient fineSupport)
      (dyadicFacePreimages coarsePlaquette) htrue
  have hfineMem : finePlaquette ∈ fineSupport := by
    simpa [supportCoefficient] using hfineCoefficient
  exact coarse_mem_box_of_facePreimage_mem_doubled_box
    hpreimage (hfineBox finePlaquette hfineMem)

/-- Under the declared fine-box hypothesis, filtering the coarse box loses
no coefficient: the finite output list represents the global cellular
pushforward exactly. -/
theorem supportCoefficient_dyadicModTwoPushforwardSupport
    {n : Nat} {fineSupport : List Z4Plaq}
    (hfineBox : ∀ finePlaquette, finePlaquette ∈ fineSupport →
      finePlaquette ∈ boxPlaquettes (2 * n))
    (coarsePlaquette : Z4Plaq) :
    supportCoefficient
        (dyadicModTwoPushforwardSupport n fineSupport) coarsePlaquette =
      dyadicFacePushforward (supportCoefficient fineSupport)
        coarsePlaquette := by
  cases hvalue : dyadicFacePushforward (supportCoefficient fineSupport)
      coarsePlaquette with
  | false =>
      have hnotMem : coarsePlaquette ∉
          dyadicModTwoPushforwardSupport n fineSupport := by
        intro hmem
        have htrue :=
          (mem_dyadicModTwoPushforwardSupport_iff
            n fineSupport coarsePlaquette).mp hmem
        rw [hvalue] at htrue
        cases htrue.2
      simp [supportCoefficient, hnotMem]
  | true =>
      have hcoarseBox : coarsePlaquette ∈ boxPlaquettes n :=
        dyadicFacePushforward_true_implies_mem_box hfineBox hvalue
      have hmem : coarsePlaquette ∈
          dyadicModTwoPushforwardSupport n fineSupport :=
        (mem_dyadicModTwoPushforwardSupport_iff
          n fineSupport coarsePlaquette).mpr ⟨hcoarseBox, hvalue⟩
      simp [supportCoefficient, hmem]

/-- The canonical finite output of a box-supported closed fine support is
again closed in the exact mod-two cellular sense. -/
theorem dyadicModTwoPushforwardSupport_preserves_modTwoClosed
    {n : Nat} {fineSupport : List Z4Plaq}
    (hfineBox : ∀ finePlaquette, finePlaquette ∈ fineSupport →
      finePlaquette ∈ boxPlaquettes (2 * n))
    (hclosed : ModTwoClosed (supportCoefficient fineSupport)) :
    ModTwoClosed
      (supportCoefficient
        (dyadicModTwoPushforwardSupport n fineSupport)) := by
  have hcoefficient :
      supportCoefficient (dyadicModTwoPushforwardSupport n fineSupport) =
        dyadicFacePushforward (supportCoefficient fineSupport) := by
    funext coarsePlaquette
    exact supportCoefficient_dyadicModTwoPushforwardSupport
      hfineBox coarsePlaquette
  rw [hcoefficient]
  exact dyadicFacePushforward_preserves_modTwoClosed _ hclosed

/-! ## 5. Semantic bridge to the existing incidence-count predicate -/

private theorem incidentPlanePairCoefficient_pointwise_xor
    (left right : Z4Plaq → Bool)
    (vertex : Z4Vertex) (edge transverse : Dir4) :
    incidentPlanePairCoefficient (fun p => left p ^^ right p)
        vertex edge transverse =
      (incidentPlanePairCoefficient left vertex edge transverse ^^
        incidentPlanePairCoefficient right vertex edge transverse) := by
  by_cases hzero : vertexCoord vertex transverse = 0
  · simp [incidentPlanePairCoefficient, backwardFaceCoefficient, hzero]
  · simp only [incidentPlanePairCoefficient, backwardFaceCoefficient,
      hzero, if_false]
    cases left (vertex, planeOf edge transverse) <;>
      cases right (vertex, planeOf edge transverse) <;>
      cases left (subE vertex transverse, planeOf edge transverse) <;>
      cases right (subE vertex transverse, planeOf edge transverse) <;> rfl

private theorem boolXor_three_interchange
    (a₁ a₂ a₃ b₁ b₂ b₃ : Bool) :
    ((a₁ ^^ b₁) ^^ ((a₂ ^^ b₂) ^^ (a₃ ^^ b₃))) =
      ((a₁ ^^ (a₂ ^^ a₃)) ^^ (b₁ ^^ (b₂ ^^ b₃))) := by
  cases a₁ <;> cases a₂ <;> cases a₃ <;>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> rfl

/-- The direct cubical boundary is linear over pointwise F2 addition. -/
theorem cellularBoundaryCoefficient_pointwise_xor
    (left right : Z4Plaq → Bool) (link : Z4Link) :
    cellularBoundaryCoefficient (fun p => left p ^^ right p) link =
      (cellularBoundaryCoefficient left link ^^
        cellularBoundaryCoefficient right link) := by
  obtain ⟨vertex, direction⟩ := link
  cases direction <;>
    simp only [cellularBoundaryCoefficient] <;>
    rw [incidentPlanePairCoefficient_pointwise_xor,
      incidentPlanePairCoefficient_pointwise_xor,
      incidentPlanePairCoefficient_pointwise_xor] <;>
    exact boolXor_three_interchange _ _ _ _ _ _

private theorem forwardIncidentFace_sound
    (vertex : Z4Vertex) (direction transverse : Dir4)
    (hne : transverse ≠ direction) :
    (vertex, direction) ∈
      edgesOf (vertex, planeOf direction transverse) := by
  cases direction <;> cases transverse <;>
    first
    | exact absurd rfl hne
    | simp [edgesOf, dirsOf, planeOf]

private theorem subE_self_or_addE
    (vertex : Z4Vertex) (direction : Dir4) :
    subE vertex direction = vertex ∨
      addE (subE vertex direction) direction = vertex := by
  obtain ⟨a, b, c, d⟩ := vertex
  cases direction with
  | x0 =>
      cases a with
      | zero => exact Or.inl rfl
      | succ a => exact Or.inr (by simp [subE, addE])
  | x1 =>
      cases b with
      | zero => exact Or.inl rfl
      | succ b => exact Or.inr (by simp [subE, addE])
  | x2 =>
      cases c with
      | zero => exact Or.inl rfl
      | succ c => exact Or.inr (by simp [subE, addE])
  | x3 =>
      cases d with
      | zero => exact Or.inl rfl
      | succ d => exact Or.inr (by simp [subE, addE])

private theorem backwardIncidentFace_sound
    (vertex : Z4Vertex) (direction transverse : Dir4)
    (hne : transverse ≠ direction) :
    (vertex, direction) ∈
      edgesOf (subE vertex transverse, planeOf direction transverse) := by
  rcases subE_self_or_addE vertex transverse with hsame | hfar
  · rw [hsame]
    exact forwardIncidentFace_sound vertex direction transverse hne
  · cases direction <;> cases transverse <;>
      first
      | exact absurd rfl hne
      | simp [edgesOf, dirsOf, planeOf, hfar]

private theorem edgePlaqs_mem_sound (plaquette : Z4Plaq)
    (vertex : Z4Vertex) (direction : Dir4)
    (hmem : plaquette ∈ edgePlaqs vertex direction) :
    (vertex, direction) ∈ edgesOf plaquette := by
  cases direction <;>
    simp only [edgePlaqs, List.mem_cons, List.not_mem_nil,
      or_false] at hmem <;>
    rcases hmem with h | h | h | h | h | h <;>
    subst plaquette
  all_goals
    first
    | apply forwardIncidentFace_sound <;> intro hequal <;> cases hequal
    | apply backwardIncidentFace_sound <;> intro hequal <;> cases hequal

/-- The one-or-two face list in a fixed plane incident on a link.  At the
zero boundary there is no distinct backward face. -/
def incidentPlanePairFaces (vertex : Z4Vertex)
    (direction transverse : Dir4) : List Z4Plaq :=
  if vertexCoord vertex transverse = 0 then
    [(vertex, planeOf direction transverse)]
  else
    [(vertex, planeOf direction transverse),
      (subE vertex transverse, planeOf direction transverse)]

/-- The explicit duplicate-free list of all plaquettes incident on a link. -/
def cellularIncidentFaces : Z4Link → List Z4Plaq
  | (vertex, .x0) =>
      incidentPlanePairFaces vertex .x0 .x1 ++
        (incidentPlanePairFaces vertex .x0 .x2 ++
          incidentPlanePairFaces vertex .x0 .x3)
  | (vertex, .x1) =>
      incidentPlanePairFaces vertex .x1 .x0 ++
        (incidentPlanePairFaces vertex .x1 .x2 ++
          incidentPlanePairFaces vertex .x1 .x3)
  | (vertex, .x2) =>
      incidentPlanePairFaces vertex .x2 .x0 ++
        (incidentPlanePairFaces vertex .x2 .x1 ++
          incidentPlanePairFaces vertex .x2 .x3)
  | (vertex, .x3) =>
      incidentPlanePairFaces vertex .x3 .x0 ++
        (incidentPlanePairFaces vertex .x3 .x1 ++
          incidentPlanePairFaces vertex .x3 .x2)

private theorem xorList_append {A : Type} (coefficient : A → Bool) :
    ∀ left right : List A,
      xorList coefficient (left ++ right) =
        (xorList coefficient left ^^ xorList coefficient right)
  | [], right => by
      simp only [List.nil_append, xorList]
      cases xorList coefficient right <;> rfl
  | head :: tail, right => by
      simp only [List.cons_append, xorList, xorList_append]
      cases coefficient head <;> cases xorList coefficient tail <;>
        cases xorList coefficient right <;> rfl

private theorem incidentPlanePairFaces_boundary
    (coefficient : Z4Plaq → Bool)
    (vertex : Z4Vertex) (direction transverse : Dir4) :
    xorList coefficient
        (incidentPlanePairFaces vertex direction transverse) =
      incidentPlanePairCoefficient coefficient vertex direction transverse := by
  by_cases hzero : vertexCoord vertex transverse = 0
  · simp [incidentPlanePairFaces, hzero, xorList,
      incidentPlanePairCoefficient, backwardFaceCoefficient]
  · simp [incidentPlanePairFaces, hzero, xorList,
      incidentPlanePairCoefficient, backwardFaceCoefficient]

private theorem cellularBoundaryCoefficient_incidentFaces
    (coefficient : Z4Plaq → Bool) (link : Z4Link) :
    cellularBoundaryCoefficient coefficient link =
      xorList coefficient (cellularIncidentFaces link) := by
  obtain ⟨vertex, direction⟩ := link
  cases direction <;>
    simp only [cellularBoundaryCoefficient, cellularIncidentFaces,
      xorList_append, incidentPlanePairFaces_boundary]

private theorem subE_ne_of_coord_ne_zero
    (vertex : Z4Vertex) (direction : Dir4)
    (hne : vertexCoord vertex direction ≠ 0) :
    subE vertex direction ≠ vertex := by
  obtain ⟨a, b, c, d⟩ := vertex
  cases direction with
  | x0 =>
      cases a with
      | zero => exact absurd rfl hne
      | succ a =>
          intro hequal
          have hcoord := congrArg (fun v : Z4Vertex => v.1) hequal
          simp only [subE] at hcoord
          omega
  | x1 =>
      cases b with
      | zero => exact absurd rfl hne
      | succ b =>
          intro hequal
          have hcoord := congrArg (fun v : Z4Vertex => v.2.1) hequal
          simp only [subE] at hcoord
          omega
  | x2 =>
      cases c with
      | zero => exact absurd rfl hne
      | succ c =>
          intro hequal
          have hcoord := congrArg (fun v : Z4Vertex => v.2.2.1) hequal
          simp only [subE] at hcoord
          omega
  | x3 =>
      cases d with
      | zero => exact absurd rfl hne
      | succ d =>
          intro hequal
          have hcoord := congrArg (fun v : Z4Vertex => v.2.2.2) hequal
          simp only [subE] at hcoord
          omega

private theorem incidentPlanePairFaces_nodup
    (vertex : Z4Vertex) (direction transverse : Dir4) :
    (incidentPlanePairFaces vertex direction transverse).Nodup := by
  by_cases hzero : vertexCoord vertex transverse = 0
  · simp [incidentPlanePairFaces, hzero]
  · have hne : vertex ≠ subE vertex transverse :=
      (subE_ne_of_coord_ne_zero vertex transverse hzero).symm
    simp [incidentPlanePairFaces, hzero, hne]

private theorem incidentPlanePairFaces_plane
    {vertex : Z4Vertex} {direction transverse : Dir4}
    {plaquette : Z4Plaq}
    (hmem : plaquette ∈
      incidentPlanePairFaces vertex direction transverse) :
    plaquette.2 = planeOf direction transverse := by
  by_cases hzero : vertexCoord vertex transverse = 0
  · simp [incidentPlanePairFaces, hzero] at hmem
    subst plaquette
    rfl
  · simp [incidentPlanePairFaces, hzero] at hmem
    rcases hmem with hmem | hmem
    · subst plaquette
      rfl
    · subst plaquette
      rfl

private theorem planeOf_injective_away
    (direction first second : Dir4)
    (hfirst : first ≠ direction) (hsecond : second ≠ direction)
    (hplane : planeOf direction first = planeOf direction second) :
    first = second := by
  cases direction <;> cases first <;> cases second <;>
    simp [planeOf] at hfirst hsecond hplane ⊢

private theorem incidentPlanePairFaces_disjoint
    (vertex : Z4Vertex) (direction first second : Dir4)
    (hfirst : first ≠ direction) (hsecond : second ≠ direction)
    (hdifferent : first ≠ second) :
    ∀ firstFace,
      firstFace ∈ incidentPlanePairFaces vertex direction first →
      ∀ secondFace,
        secondFace ∈ incidentPlanePairFaces vertex direction second →
        firstFace ≠ secondFace := by
  intro firstFace hfirstMem secondFace hsecondMem hequal
  have hfirstPlane := incidentPlanePairFaces_plane hfirstMem
  have hsecondPlane := incidentPlanePairFaces_plane hsecondMem
  have hplanes : planeOf direction first = planeOf direction second := by
    rw [← hfirstPlane, ← hsecondPlane, hequal]
  exact hdifferent
    (planeOf_injective_away direction first second
      hfirst hsecond hplanes)

private theorem subE_eq_self_of_coord_zero
    (vertex : Z4Vertex) (direction : Dir4)
    (hzero : vertexCoord vertex direction = 0) :
    subE vertex direction = vertex := by
  obtain ⟨a, b, c, d⟩ := vertex
  cases direction with
  | x0 =>
      simp only [vertexCoord] at hzero
      subst a
      rfl
  | x1 =>
      simp only [vertexCoord] at hzero
      subst b
      rfl
  | x2 =>
      simp only [vertexCoord] at hzero
      subst c
      rfl
  | x3 =>
      simp only [vertexCoord] at hzero
      subst d
      rfl

private theorem mem_incidentPlanePairFaces_iff
    (plaquette : Z4Plaq) (vertex : Z4Vertex)
    (direction transverse : Dir4) :
    plaquette ∈ incidentPlanePairFaces vertex direction transverse ↔
      plaquette = (vertex, planeOf direction transverse) ∨
        plaquette = (subE vertex transverse,
          planeOf direction transverse) := by
  by_cases hzero : vertexCoord vertex transverse = 0
  · have hsub := subE_eq_self_of_coord_zero vertex transverse hzero
    simp [incidentPlanePairFaces, hzero, hsub]
  · simp [incidentPlanePairFaces, hzero]

private theorem mem_cellularIncidentFaces_iff_edgePlaqs
    (plaquette : Z4Plaq) (vertex : Z4Vertex) (direction : Dir4) :
    plaquette ∈ cellularIncidentFaces (vertex, direction) ↔
      plaquette ∈ edgePlaqs vertex direction := by
  cases direction <;>
    simp only [cellularIncidentFaces, List.mem_append,
      mem_incidentPlanePairFaces_iff, edgePlaqs, List.mem_cons,
      List.not_mem_nil, or_false] <;>
    simp only [or_assoc]

/-- The explicit incident-face list has exactly the geometric incidence
semantics used by `faceIncidenceCount`. -/
theorem mem_cellularIncidentFaces_iff
    (plaquette : Z4Plaq) (link : Z4Link) :
    plaquette ∈ cellularIncidentFaces link ↔
      link ∈ edgesOf plaquette := by
  obtain ⟨vertex, direction⟩ := link
  rw [mem_cellularIncidentFaces_iff_edgePlaqs]
  constructor
  · exact edgePlaqs_mem_sound plaquette vertex direction
  · exact edge_complete plaquette vertex direction

private theorem cellularIncidentFaces_nodup (link : Z4Link) :
    (cellularIncidentFaces link).Nodup := by
  obtain ⟨vertex, direction⟩ := link
  cases direction <;>
    simp only [cellularIncidentFaces] <;>
    apply List.nodup_append.mpr <;>
    refine ⟨incidentPlanePairFaces_nodup _ _ _, ?_, ?_⟩
  all_goals
    first
    | exact List.nodup_append.mpr
        ⟨incidentPlanePairFaces_nodup _ _ _,
          incidentPlanePairFaces_nodup _ _ _,
          incidentPlanePairFaces_disjoint _ _ _ _
            (by intro h; cases h) (by intro h; cases h)
            (by intro h; cases h)⟩
    | intro firstFace hfirst secondFace hsecond
      rcases List.mem_append.mp hsecond with hsecond | hsecond
      · exact incidentPlanePairFaces_disjoint _ _ _ _
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h)
          firstFace hfirst secondFace hsecond
      · exact incidentPlanePairFaces_disjoint _ _ _ _
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h)
          firstFace hfirst secondFace hsecond

private def diracFaceCoefficient (source query : Z4Plaq) : Bool :=
  decide (query = source)

private theorem xorList_diracFaceCoefficient (source : Z4Plaq) :
    ∀ entries : List Z4Plaq, entries.Nodup →
      xorList (diracFaceCoefficient source) entries =
        decide (source ∈ entries)
  | [], _ => rfl
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      have ih := xorList_diracFaceCoefficient source tail hparts.2
      by_cases hhead : head = source
      · subst head
        simp [xorList, diracFaceCoefficient, hparts.1, ih]
      · have hsource : source ≠ head := by
          intro hequal
          exact hhead hequal.symm
        simp [xorList, diracFaceCoefficient, hhead, hsource, ih]

/-- The cellular boundary of a one-face Dirac coefficient is exactly the
geometric incidence indicator. -/
theorem cellularBoundaryCoefficient_dirac
    (source : Z4Plaq) (link : Z4Link) :
    cellularBoundaryCoefficient (diracFaceCoefficient source) link =
      z4Boundary source link := by
  rw [cellularBoundaryCoefficient_incidentFaces]
  rw [xorList_diracFaceCoefficient source (cellularIncidentFaces link)
    (cellularIncidentFaces_nodup link)]
  simp [z4Boundary, mem_cellularIncidentFaces_iff]

private theorem supportCoefficient_cons_xor
    {head : Z4Plaq} {tail : List Z4Plaq} (hnot : head ∉ tail) :
    supportCoefficient (head :: tail) =
      fun query => diracFaceCoefficient head query ^^
        supportCoefficient tail query := by
  funext query
  by_cases hequal : query = head
  · subst query
    simp [supportCoefficient, diracFaceCoefficient, hnot]
  · simp [supportCoefficient, diracFaceCoefficient, hequal]

private theorem cellularBoundaryCoefficient_support_cons
    {head : Z4Plaq} {tail : List Z4Plaq} (hnot : head ∉ tail)
    (link : Z4Link) :
    cellularBoundaryCoefficient (supportCoefficient (head :: tail)) link =
      (z4Boundary head link ^^
        cellularBoundaryCoefficient (supportCoefficient tail) link) := by
  rw [supportCoefficient_cons_xor hnot]
  rw [cellularBoundaryCoefficient_pointwise_xor]
  rw [cellularBoundaryCoefficient_dirac]

private theorem boolXor_decide_odd (bit : Bool) (n : Nat) :
    (bit ^^ decide (n % 2 = 1)) =
      decide ((bit.toNat + n) % 2 = 1) := by
  cases bit <;> simp
  have hlt : n % 2 < 2 := Nat.mod_lt n (by omega)
  by_cases hzero : n % 2 = 0
  · have hnext : (1 + n) % 2 = 1 := by omega
    simp [hzero, hnext]
  · have hone : n % 2 = 1 := by omega
    have hnext : (1 + n) % 2 = 0 := by omega
    simp [hone, hnext]

/-- For a duplicate-free finite support, the direct F2 cellular boundary is
the parity of the original geometric face-incidence count. -/
theorem cellularBoundaryCoefficient_supportParity :
    ∀ support : List Z4Plaq, support.Nodup → ∀ link : Z4Link,
      cellularBoundaryCoefficient (supportCoefficient support) link =
        decide (faceIncidenceCount link support % 2 = 1)
  | [], _, link => by
      obtain ⟨vertex, direction⟩ := link
      cases direction <;>
        simp [cellularBoundaryCoefficient, incidentPlanePairCoefficient,
          backwardFaceCoefficient, supportCoefficient, faceIncidenceCount]
  | head :: tail, hnodup, link => by
      have hparts := List.nodup_cons.mp hnodup
      rw [cellularBoundaryCoefficient_support_cons hparts.1 link]
      rw [cellularBoundaryCoefficient_supportParity tail hparts.2 link]
      by_cases hinc : link ∈ edgesOf head
      · simp only [faceIncidenceCount, if_pos hinc]
        simpa [z4Boundary, hinc] using
          boolXor_decide_odd true (faceIncidenceCount link tail)
      · simp only [faceIncidenceCount, if_neg hinc]
        simpa [z4Boundary, hinc] using
          boolXor_decide_odd false (faceIncidenceCount link tail)

/-- On canonical (duplicate-free) supports, `ModTwoClosed` is not a new or
weakened closure notion: it is equivalent to the pre-existing geometric
`EvenFaceIncidence` predicate. -/
theorem modTwoClosed_supportCoefficient_iff_evenFaceIncidence
    (support : List Z4Plaq) (hnodup : support.Nodup) :
    ModTwoClosed (supportCoefficient support) ↔
      Z4DyadicDeterministicSupportKernel.EvenFaceIncidence support := by
  constructor
  · intro hclosed link
    have hboundary := hclosed link
    rw [cellularBoundaryCoefficient_supportParity support hnodup link]
      at hboundary
    have hnotone : faceIncidenceCount link support % 2 ≠ 1 := by
      intro hone
      simp [hone] at hboundary
    have hlt : faceIncidenceCount link support % 2 < 2 :=
      Nat.mod_lt _ (by omega)
    omega
  · intro heven link
    rw [cellularBoundaryCoefficient_supportParity support hnodup link]
    have hzero := heven link
    simp [hzero]

/-- The canonical XOR image preserves the development's original geometric
even-incidence condition, not merely an auxiliary Boolean restatement. -/
theorem dyadicModTwoPushforwardSupport_preserves_evenFaceIncidence
    {n : Nat} {fineSupport : List Z4Plaq}
    (hfineBox : ∀ finePlaquette, finePlaquette ∈ fineSupport →
      finePlaquette ∈ boxPlaquettes (2 * n))
    (hfineNodup : fineSupport.Nodup)
    (hclosed :
      Z4DyadicDeterministicSupportKernel.EvenFaceIncidence fineSupport) :
    Z4DyadicDeterministicSupportKernel.EvenFaceIncidence
      (dyadicModTwoPushforwardSupport n fineSupport) := by
  have hfineClosed : ModTwoClosed (supportCoefficient fineSupport) :=
    (modTwoClosed_supportCoefficient_iff_evenFaceIncidence
      fineSupport hfineNodup).2 hclosed
  have houtClosed : ModTwoClosed
      (supportCoefficient
        (dyadicModTwoPushforwardSupport n fineSupport)) :=
    dyadicModTwoPushforwardSupport_preserves_modTwoClosed
      hfineBox hfineClosed
  exact (modTwoClosed_supportCoefficient_iff_evenFaceIncidence
    (dyadicModTwoPushforwardSupport n fineSupport)
    (dyadicModTwoPushforwardSupport_nodup n fineSupport)).1 houtClosed

/-! ## 6. Explicit source dependence -/

def sourceWitnessCoarsePlaquette : Z4Plaq :=
  ((0, 0, 0, 0), .p01)

def sourceWitnessFinePlaquette : Z4Plaq :=
  ((1, 1, 0, 0), .p01)

theorem sourceWitnessCoarsePlaquette_mem_singleton_image :
    sourceWitnessCoarsePlaquette ∈
      dyadicModTwoPushforwardSupport 2 [sourceWitnessFinePlaquette] := by
  apply (mem_dyadicModTwoPushforwardSupport_iff
    2 [sourceWitnessFinePlaquette] sourceWitnessCoarsePlaquette).mpr
  constructor
  · unfold sourceWitnessCoarsePlaquette
    simp only [mem_boxPlaquettes]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · rfl

/-- The mod-two carrier is genuinely source-dependent: changing the empty
fine support to one nondegenerate fine face changes its canonical output. -/
theorem dyadicModTwoPushforwardSupport_source_dependent :
    dyadicModTwoPushforwardSupport 2 [] ≠
      dyadicModTwoPushforwardSupport 2 [sourceWitnessFinePlaquette] := by
  intro hequal
  have hmem : sourceWitnessCoarsePlaquette ∈
      dyadicModTwoPushforwardSupport 2 [] := by
    rw [hequal]
    exact sourceWitnessCoarsePlaquette_mem_singleton_image
  have htrue :=
    (mem_dyadicModTwoPushforwardSupport_iff
      2 [] sourceWitnessCoarsePlaquette).mp hmem
  simp [dyadicFacePushforward, supportCoefficient, dyadicFacePreimages,
    xorList, sourceWitnessCoarsePlaquette] at htrue

/-! ## 7. Positive normalized deterministic kernel -/

def modTwoSupportStateSpace (n : Nat) : List (List Z4Plaq) :=
  sublists (boxPlaquettes n)

theorem modTwoSupportStateSpace_nodup (n : Nat) :
    (modTwoSupportStateSpace n).Nodup := by
  unfold modTwoSupportStateSpace
  exact CayleyPruferInjection.sublists_nodup
    (boxPlaquettes n) (boxPlaquettes_nodup n)

/-- Exact-rational Dirac mass at the canonical cellular image. -/
def dyadicModTwoSupportKernel (n : Nat)
    (fineSupport coarseSupport : List Z4Plaq) : Q' :=
  if coarseSupport = dyadicModTwoPushforwardSupport n fineSupport then
    1 else 0

theorem dyadicModTwoSupportKernel_nonnegative
    (n : Nat) (fineSupport coarseSupport : List Z4Plaq) :
    (0 : Q') ≤ dyadicModTwoSupportKernel n fineSupport coarseSupport := by
  unfold dyadicModTwoSupportKernel
  by_cases himage :
      coarseSupport = dyadicModTwoPushforwardSupport n fineSupport
  · rw [if_pos himage]
    exact Q'.zero_le_one
  · rw [if_neg himage]
    exact Q'.le_refl' 0

theorem dyadicModTwoSupportKernel_on_image
    (n : Nat) (fineSupport : List Z4Plaq) :
    dyadicModTwoSupportKernel n fineSupport
      (dyadicModTwoPushforwardSupport n fineSupport) = 1 := by
  simp [dyadicModTwoSupportKernel]

theorem dyadicModTwoSupportKernel_off_image
    {n : Nat} {fineSupport coarseSupport : List Z4Plaq}
    (hne : coarseSupport ≠
      dyadicModTwoPushforwardSupport n fineSupport) :
    dyadicModTwoSupportKernel n fineSupport coarseSupport = 0 := by
  simp [dyadicModTwoSupportKernel, hne]

private theorem listQSum_modTwoDirac_zero_of_not_mem
    {A : Type} [DecidableEq A] (target : A) :
    ∀ states : List A, target ∉ states →
      listQSum (fun state => if state = target then (1 : Q') else 0)
        states ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hnot => by
      have hhead : head ≠ target := by
        intro hequal
        subst head
        exact hnot List.mem_cons_self
      have htail : target ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      simp only [listQSum, if_neg hhead]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl 0)
          (listQSum_modTwoDirac_zero_of_not_mem target tail htail))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_modTwoDirac_one_of_mem_nodup
    {A : Type} [DecidableEq A] (target : A) :
    ∀ states : List A, states.Nodup → target ∈ states →
      listQSum (fun state => if state = target then (1 : Q') else 0)
        states ≈ 1
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum, if_true]
        have hzero := listQSum_modTwoDirac_zero_of_not_mem
          target tail hparts.1
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl 1) hzero)
          (Q'.eqv_of_eq (Q'.add_zero' 1))
      · have hheadNe : head ≠ target := by
          intro hequal
          subst head
          exact hparts.1 htail
        simp only [listQSum, if_neg hheadNe]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.eqv_refl 0)
            (listQSum_modTwoDirac_one_of_mem_nodup
              target tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' 1))

/-- Every row has exact total mass one on the finite canonical support state
space. -/
theorem dyadicModTwoSupportKernel_row_normalized
    (n : Nat) (fineSupport : List Z4Plaq) :
    listQSum (dyadicModTwoSupportKernel n fineSupport)
      (modTwoSupportStateSpace n) ≈ 1 := by
  change listQSum
    (fun coarseSupport =>
      if coarseSupport = dyadicModTwoPushforwardSupport n fineSupport then
        (1 : Q') else 0)
    (modTwoSupportStateSpace n) ≈ 1
  exact listQSum_modTwoDirac_one_of_mem_nodup
    (dyadicModTwoPushforwardSupport n fineSupport)
    (modTwoSupportStateSpace n)
    (modTwoSupportStateSpace_nodup n)
    (dyadicModTwoPushforwardSupport_mem_stateSpace n fineSupport)

/-- On a box-supported closed input, every target carrying nonzero Dirac
mass is itself closed. -/
theorem dyadicModTwoSupportKernel_nonzero_target_closed
    {n : Nat} {fineSupport coarseSupport : List Z4Plaq}
    (hfineBox : ∀ finePlaquette, finePlaquette ∈ fineSupport →
      finePlaquette ∈ boxPlaquettes (2 * n))
    (hclosed : ModTwoClosed (supportCoefficient fineSupport))
    (hnonzero : dyadicModTwoSupportKernel n fineSupport coarseSupport ≠ 0) :
    ModTwoClosed (supportCoefficient coarseSupport) := by
  have himage : coarseSupport =
      dyadicModTwoPushforwardSupport n fineSupport := by
    by_cases himage : coarseSupport =
        dyadicModTwoPushforwardSupport n fineSupport
    · exact himage
    · exact absurd
        (dyadicModTwoSupportKernel_off_image himage) hnonzero
  subst coarseSupport
  exact dyadicModTwoPushforwardSupport_preserves_modTwoClosed
    hfineBox hclosed

#print axioms coarse_mem_box_of_facePreimage_mem_doubled_box
#print axioms dyadicFacePushforward_true_implies_mem_box
#print axioms supportCoefficient_dyadicModTwoPushforwardSupport
#print axioms dyadicModTwoPushforwardSupport_preserves_modTwoClosed
#print axioms mem_cellularIncidentFaces_iff
#print axioms cellularBoundaryCoefficient_pointwise_xor
#print axioms cellularBoundaryCoefficient_dirac
#print axioms cellularBoundaryCoefficient_supportParity
#print axioms modTwoClosed_supportCoefficient_iff_evenFaceIncidence
#print axioms dyadicModTwoPushforwardSupport_preserves_evenFaceIncidence
#print axioms dyadicFacePushforward_local
#print axioms dyadicModTwoPushforwardSupport_source_dependent
#print axioms modTwoSupportStateSpace_nodup
#print axioms dyadicModTwoSupportKernel_nonnegative
#print axioms dyadicModTwoSupportKernel_on_image
#print axioms dyadicModTwoSupportKernel_off_image
#print axioms dyadicModTwoSupportKernel_row_normalized
#print axioms dyadicModTwoSupportKernel_nonzero_target_closed

end YMGap.Continuum.Z4DyadicModTwoCellularKernel
