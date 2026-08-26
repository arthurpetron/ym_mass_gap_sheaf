/-
# Canonical endpoint swap on an internal link edge

A duplicate-free finite fiber of cardinality two is not merely a count: it
canonically carries the transposition of its two points.  This module states
that elementary fact once as a constructive compiler and applies it to the
two half-edges over every genuine internal edge of an accepted canonical
link-resolution network.

The result is the position-level continuation needed before transporting a
bounded strand slot.  It is an explicit fixed-point-free involution, not a
finite-choice existence statement.

Constructive contract: pattern matching on an explicit two-element list and
decidable equality only.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.ResolvedTrivalentNetworkHalfEdges

namespace YMGap.Continuum.CanonicalLinkInternalHalfEdgeSwap

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkHalfEdges
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState

/-! ## 1. The constructive two-point-fiber compiler -/

/-- An explicit ordered presentation of a duplicate-free two-point list. -/
structure TwoPointFiber {A : Type} (entries : List A) : Type where
  first : A
  second : A
  exact : entries = [first, second]
  distinct : first ≠ second

/-- Length two plus duplicate-freeness computes the two distinct points. -/
def TwoPointFiber.ofLengthNodup {A : Type} (entries : List A)
    (hlength : entries.length = 2) (hnodup : entries.Nodup) :
    TwoPointFiber entries := by
  cases entries with
  | nil => simp at hlength
  | cons first rest =>
      cases rest with
      | nil => simp at hlength
      | cons second tail =>
          cases tail with
          | nil =>
              refine ⟨first, second, rfl, ?_⟩
              have hhead := (List.nodup_cons.mp hnodup).1
              simpa using hhead
          | cons third tail => simp at hlength

/-- Membership in a compiled two-point fiber is the displayed disjunction. -/
theorem TwoPointFiber.mem_iff {A : Type} {entries : List A}
    (fiber : TwoPointFiber entries) (item : A) :
    item ∈ entries ↔ item = fiber.first ∨ item = fiber.second := by
  cases fiber with
  | mk first second hexact hdistinct =>
      subst entries
      simp

/-- Exchange the two displayed points.  Values outside the fiber are sent to
the first point, but all load-bearing laws below are stated on members. -/
def TwoPointFiber.swap {A : Type} [DecidableEq A] {entries : List A}
    (fiber : TwoPointFiber entries) (item : A) : A :=
  if item = fiber.first then fiber.second else fiber.first

/-- The exchange preserves the two-point fiber. -/
theorem TwoPointFiber.swap_mem {A : Type} [DecidableEq A]
    {entries : List A} (fiber : TwoPointFiber entries) {item : A}
    (_hmem : item ∈ entries) : fiber.swap item ∈ entries := by
  rw [fiber.mem_iff]
  unfold TwoPointFiber.swap
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The exchange has no fixed point on the fiber. -/
theorem TwoPointFiber.swap_ne_self {A : Type} [DecidableEq A]
    {entries : List A} (fiber : TwoPointFiber entries) {item : A}
    (hmem : item ∈ entries) : fiber.swap item ≠ item := by
  rw [fiber.mem_iff] at hmem
  rcases hmem with hfirst | hsecond
  · subst item
    have hsecondFirst : fiber.second ≠ fiber.first := Ne.symm fiber.distinct
    simp [TwoPointFiber.swap, hsecondFirst]
  · subst item
    have hsecondFirst : fiber.second ≠ fiber.first := Ne.symm fiber.distinct
    simp [TwoPointFiber.swap, hsecondFirst, fiber.distinct]

/-- Exchanging twice returns the original member. -/
theorem TwoPointFiber.swap_involutive {A : Type} [DecidableEq A]
    {entries : List A} (fiber : TwoPointFiber entries) {item : A}
    (hmem : item ∈ entries) : fiber.swap (fiber.swap item) = item := by
  rw [fiber.mem_iff] at hmem
  rcases hmem with hfirst | hsecond
  · subst item
    have hsecondFirst : fiber.second ≠ fiber.first := Ne.symm fiber.distinct
    simp [TwoPointFiber.swap, hsecondFirst]
  · subst item
    have hsecondFirst : fiber.second ≠ fiber.first := Ne.symm fiber.distinct
    simp [TwoPointFiber.swap, hsecondFirst]

/-- Any two members of a two-point fiber are either identical or related by
the canonical exchange.  This is the finite orbit principle used to descend
same-edge data without choosing an orientation of the edge. -/
theorem TwoPointFiber.eq_or_eq_swap {A : Type} [DecidableEq A]
    {entries : List A} (fiber : TwoPointFiber entries)
    {left right : A} (hleft : left ∈ entries) (hright : right ∈ entries) :
    right = left ∨ right = fiber.swap left := by
  rw [fiber.mem_iff] at hleft hright
  rcases hleft with hleft | hleft <;>
    rcases hright with hright | hright
  · exact Or.inl (hright.trans hleft.symm)
  · subst left
    subst right
    exact Or.inr (by simp [TwoPointFiber.swap])
  · subst left
    subst right
    have hsecondFirst : fiber.second ≠ fiber.first := Ne.symm fiber.distinct
    exact Or.inr (by simp [TwoPointFiber.swap, hsecondFirst])
  · exact Or.inl (hright.trans hleft.symm)

/-- The member type of an explicit finite fiber. -/
abbrev FiberMember {A : Type} (entries : List A) :=
  { item : A // item ∈ entries }

/-- The two-point exchange as a self-map of the actual member type. -/
def TwoPointFiber.swapMember {A : Type} [DecidableEq A]
    {entries : List A} (fiber : TwoPointFiber entries) :
    FiberMember entries -> FiberMember entries :=
  fun item => ⟨fiber.swap item.1, fiber.swap_mem item.2⟩

/-- The member exchange is fixed-point-free. -/
theorem TwoPointFiber.swapMember_ne_self {A : Type} [DecidableEq A]
    {entries : List A} (fiber : TwoPointFiber entries)
    (item : FiberMember entries) :
    fiber.swapMember item ≠ item := by
  intro heq
  exact fiber.swap_ne_self item.2 (congrArg Subtype.val heq)

/-- The member exchange is an involution. -/
theorem TwoPointFiber.swapMember_involutive
    {A : Type} [DecidableEq A] {entries : List A}
    (fiber : TwoPointFiber entries) (item : FiberMember entries) :
    fiber.swapMember (fiber.swapMember item) = item := by
  apply Subtype.ext
  exact fiber.swap_involutive item.2

/-! ## 2. Membership in a resolved edge fiber -/

/-- A half-edge belongs to the fiber of `edge` exactly when it carries that
identifier. -/
theorem mem_halfEdgesOnEdge_iff
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (halfEdge : ResolvedNetworkHalfEdge network) (edge : Nat) :
    halfEdge ∈ halfEdgesOnEdge network edge ↔ halfEdge.edgeId = edge := by
  simp [halfEdgesOnEdge, ResolvedNetworkHalfEdge.mem_all]

/-! ## 3. Canonical internal-edge specialization -/

/-- The two distinct half-edges over a genuine internal edge, retained as
explicit data. -/
def canonicalInternalHalfEdgeFiber
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree) :
    TwoPointFiber
      (halfEdgesOnEdge
        (canonicalLinkResolvedStrandNetwork
          degree external auxiliary hallowed) edge) :=
  TwoPointFiber.ofLengthNodup _
    (canonicalLinkResolved_halfEdgesOnEdge_length_internal
      hdegree hallowed hedge)
    (halfEdgesOnEdge_nodup
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed) edge)

/-- The actual member type of the internal half-edge fiber. -/
abbrev CanonicalInternalHalfEdge
    {degree : Nat} (edge : Nat) (external auxiliary : EdgeLabelling)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true) :=
  FiberMember
    (halfEdgesOnEdge
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed) edge)

/-- Continue across a genuine internal fusion edge by exchanging its two
half-edge endpoints. -/
def canonicalInternalHalfEdgeSwap
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree) :
    CanonicalInternalHalfEdge edge external auxiliary hallowed ->
      CanonicalInternalHalfEdge edge external auxiliary hallowed :=
  (canonicalInternalHalfEdgeFiber hdegree hallowed hedge).swapMember

/-- Internal continuation stays over the same graph-edge identifier. -/
theorem canonicalInternalHalfEdgeSwap_edgeId
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (halfEdge : CanonicalInternalHalfEdge edge external auxiliary hallowed) :
    (canonicalInternalHalfEdgeSwap hdegree hallowed hedge halfEdge).1.edgeId =
      edge :=
  (mem_halfEdgesOnEdge_iff _ _).mp
    (canonicalInternalHalfEdgeSwap hdegree hallowed hedge halfEdge).2

/-- Internal endpoint continuation never remains at the same half-edge. -/
theorem canonicalInternalHalfEdgeSwap_ne_self
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (halfEdge : CanonicalInternalHalfEdge edge external auxiliary hallowed) :
    canonicalInternalHalfEdgeSwap hdegree hallowed hedge halfEdge ≠ halfEdge :=
  (canonicalInternalHalfEdgeFiber hdegree hallowed hedge).swapMember_ne_self
    halfEdge

/-- Internal endpoint continuation is an involution. -/
theorem canonicalInternalHalfEdgeSwap_involutive
    {degree edge : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (hedge : edge ∈ canonicalInternalFusionEdges degree)
    (halfEdge : CanonicalInternalHalfEdge edge external auxiliary hallowed) :
    canonicalInternalHalfEdgeSwap hdegree hallowed hedge
        (canonicalInternalHalfEdgeSwap hdegree hallowed hedge halfEdge) =
      halfEdge :=
  (canonicalInternalHalfEdgeFiber hdegree hallowed hedge).swapMember_involutive
    halfEdge

#print axioms TwoPointFiber
#print axioms TwoPointFiber.ofLengthNodup
#print axioms TwoPointFiber.mem_iff
#print axioms TwoPointFiber.swap
#print axioms TwoPointFiber.swap_mem
#print axioms TwoPointFiber.swap_ne_self
#print axioms TwoPointFiber.swap_involutive
#print axioms TwoPointFiber.eq_or_eq_swap
#print axioms FiberMember
#print axioms TwoPointFiber.swapMember
#print axioms TwoPointFiber.swapMember_ne_self
#print axioms TwoPointFiber.swapMember_involutive
#print axioms mem_halfEdgesOnEdge_iff
#print axioms canonicalInternalHalfEdgeFiber
#print axioms CanonicalInternalHalfEdge
#print axioms canonicalInternalHalfEdgeSwap
#print axioms canonicalInternalHalfEdgeSwap_edgeId
#print axioms canonicalInternalHalfEdgeSwap_ne_self
#print axioms canonicalInternalHalfEdgeSwap_involutive

end YMGap.Continuum.CanonicalLinkInternalHalfEdgeSwap
