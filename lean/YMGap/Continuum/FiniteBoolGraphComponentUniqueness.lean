/-
# Uniqueness of finite Boolean-graph components up to support

Component lists have two irrelevant orderings: the order of vertices inside a
component and the order of components inside the family.  Literal list
equality is therefore not the canonical uniqueness statement.  This module
proves the precise invariant statement: any two nonempty, internally
connected, pairwise-separated covers of the same finite vertex support have
the same component supports in both directions.

The key lemma says that a chain cannot leave a member of a separated cover.
At the first putative crossing, coverage supplies the destination component
and pairwise separation contradicts the crossing adjacency.
-/

import YMGap.Continuum.FiniteBoolGraphComponents

namespace YMGap.Continuum.FiniteBoolGraphComponentUniqueness

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.FiniteBoolGraphComponents

def SameSupport {α : Type} (left right : List α) : Prop :=
  ∀ point, point ∈ left ↔ point ∈ right

def FamiliesSupportEquivalent {α : Type}
    (left right : List (List α)) : Prop :=
  (∀ component, component ∈ left →
      ∃ matching, matching ∈ right ∧ SameSupport component matching) ∧
    (∀ component, component ∈ right →
      ∃ matching, matching ∈ left ∧ SameSupport component matching)

theorem chain_stays_in_separated_component
    {α : Type} [DecidableEq α] {adj : α → α → Bool}
    {vertices : List α} {partition : List (List α)}
    (hcover : Covers vertices partition)
    (hseparated : DistinctSeparated adj partition)
    {target walkSupport : List α}
    (htarget : target ∈ partition)
    (hwalkSubset : ∀ point, point ∈ walkSupport → point ∈ vertices) :
    ∀ {source destination : α}, ChainIn adj walkSupport source destination →
      source ∈ target → destination ∈ target := by
  intro source destination chain
  induction chain with
  | refl point =>
      intro hsource
      exact hsource
  | @step source next destination hadj hnext rest ih =>
      intro hsource
      have hnextVertex : next ∈ vertices := hwalkSubset next hnext
      obtain ⟨container, hcontainer, hnextContainer⟩ :=
        (hcover next).1 hnextVertex
      have hnextTarget : next ∈ target := by
        by_cases heq : container = target
        · rw [← heq]
          exact hnextContainer
        · have htargetNe : target ≠ container := fun h => heq h.symm
          have hfalse := hseparated target htarget container hcontainer
            htargetNe source hsource _ hnextContainer
          rw [hadj] at hfalse
          cases hfalse
      exact ih hnextTarget

theorem connected_separated_covers_unique_up_to_support
    {α : Type} [DecidableEq α] {adj : α → α → Bool} {vertices : List α}
    {left right : List (List α)}
    (hleftCover : Covers vertices left)
    (hrightCover : Covers vertices right)
    (hleftConnected : AllConnected adj left)
    (hrightConnected : AllConnected adj right)
    (hleftNonempty : AllNonempty left)
    (hrightNonempty : AllNonempty right)
    (hleftSeparated : DistinctSeparated adj left)
    (hrightSeparated : DistinctSeparated adj right) :
    FamiliesSupportEquivalent left right := by
  constructor
  · intro component hcomponent
    obtain ⟨seed, hseed⟩ := hleftNonempty component hcomponent
    have hseedVertex : seed ∈ vertices :=
      (hleftCover seed).2 ⟨component, hcomponent, hseed⟩
    obtain ⟨matching, hmatching, hseedMatching⟩ :=
      (hrightCover seed).1 hseedVertex
    refine ⟨matching, hmatching, ?_⟩
    intro point
    constructor
    · intro hpoint
      have hchain := hleftConnected component hcomponent
        seed point hseed hpoint
      exact chain_stays_in_separated_component hrightCover
        hrightSeparated hmatching
        (fun x hx => (hleftCover x).2 ⟨component, hcomponent, hx⟩)
        hchain hseedMatching
    · intro hpoint
      have hchain := hrightConnected matching hmatching
        seed point hseedMatching hpoint
      exact chain_stays_in_separated_component hleftCover
        hleftSeparated hcomponent
        (fun x hx => (hrightCover x).2 ⟨matching, hmatching, hx⟩)
        hchain hseed
  · intro component hcomponent
    obtain ⟨seed, hseed⟩ := hrightNonempty component hcomponent
    have hseedVertex : seed ∈ vertices :=
      (hrightCover seed).2 ⟨component, hcomponent, hseed⟩
    obtain ⟨matching, hmatching, hseedMatching⟩ :=
      (hleftCover seed).1 hseedVertex
    refine ⟨matching, hmatching, ?_⟩
    intro point
    constructor
    · intro hpoint
      have hchain := hrightConnected component hcomponent
        seed point hseed hpoint
      exact chain_stays_in_separated_component hleftCover
        hleftSeparated hmatching
        (fun x hx => (hrightCover x).2 ⟨component, hcomponent, hx⟩)
        hchain hseedMatching
    · intro hpoint
      have hchain := hleftConnected matching hmatching
        seed point hseedMatching hpoint
      exact chain_stays_in_separated_component hrightCover
        hrightSeparated hcomponent
        (fun x hx => (hleftCover x).2 ⟨matching, hmatching, hx⟩)
        hchain hseed

theorem graphComponents_unique_up_to_support
    {α : Type} [DecidableEq α] (adj : α → α → Bool)
    (hsym : SymmetricAdj adj) (vertices : List α)
    {candidate : List (List α)}
    (hcandidateCover : Covers vertices candidate)
    (hcandidateConnected : AllConnected adj candidate)
    (hcandidateNonempty : AllNonempty candidate)
    (hcandidateSeparated : DistinctSeparated adj candidate) :
    FamiliesSupportEquivalent (graphComponents adj vertices) candidate :=
  connected_separated_covers_unique_up_to_support
    (graphComponents_covers adj vertices)
    hcandidateCover
    (graphComponents_allConnected adj hsym vertices)
    hcandidateConnected
    (graphComponents_allNonempty adj vertices)
    hcandidateNonempty
    (graphComponents_distinctSeparated adj hsym vertices)
    hcandidateSeparated

end YMGap.Continuum.FiniteBoolGraphComponentUniqueness

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.FiniteBoolGraphComponentUniqueness.chain_stays_in_separated_component
#print axioms YMGap.Continuum.FiniteBoolGraphComponentUniqueness.connected_separated_covers_unique_up_to_support
#print axioms YMGap.Continuum.FiniteBoolGraphComponentUniqueness.graphComponents_unique_up_to_support
