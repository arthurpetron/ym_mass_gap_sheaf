/-
# Factorization of the conditional auxiliary multiplicity over links

The global physical plaquette labelling remains fixed throughout this file.
Only the private, pairwise-disjoint auxiliary channel blocks are separated.
The exact Boolean constraint factors over enumerated links, constructive
finite Fubini turns the corresponding finite sum into a product, and every
factor is the literal local zero-one sum for one resolved lattice link.

This closes the global-overlap bookkeeping problem: shared face labels are
not duplicated, while private auxiliary labels are genuinely independent
conditional on those shared labels.  Identifying the resulting local factors
with closed SU(2) fixed-external-label fusion formulas is the next layer.
-/

import YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

namespace YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ConditionalAuxiliaryMultiplicity
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4LinkIdentifierFreshness

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Local and family multiplicity sums -/

def linkFamilyConditionalAllowedB (n : Nat)
    (physical : EdgeLabelling) (links : List (Nat × Z4Link))
    (auxiliary : EdgeLabelling) : Bool :=
  links.all (linkConditionalAuxiliaryAllowedB n physical auxiliary)

/-- Literal fixed-external-label auxiliary sum for one enumerated link. -/
def linkAuxiliaryMultiplicity (K n : Nat)
    (physical : EdgeLabelling) (indexed : Nat × Z4Link) : Q' :=
  listQSum
    (fun auxiliary =>
      if linkConditionalAuxiliaryAllowedB n physical auxiliary indexed
        then 1 else 0)
    (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (actualLinkAuxiliaryCoordinates n indexed.1 indexed.2))

/-- The fusion-basis invariant multiplicity: the exact number of bounded
private-channel labellings satisfying the trivalent link constraint at fixed
external plaquette spins.  Geometry guarantees valence at most six. -/
def linkInvariantMultiplicityCount (K n : Nat)
    (physical : EdgeLabelling) (indexed : Nat × Z4Link) : Nat :=
  ((boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (actualLinkAuxiliaryCoordinates n indexed.1 indexed.2)).filter
    (fun auxiliary =>
      linkConditionalAuxiliaryAllowedB n physical auxiliary indexed)).length

theorem linkAuxiliaryMultiplicity_eq_invariantCount
    (K n : Nat) (physical : EdgeLabelling)
    (indexed : Nat × Z4Link) :
    linkAuxiliaryMultiplicity K n physical indexed ≈
      Q'.ofNat (linkInvariantMultiplicityCount K n physical indexed) := by
  unfold linkAuxiliaryMultiplicity linkInvariantMultiplicityCount
  exact listQSum_boolIndicator_eq_count
    (linkConditionalAuxiliaryAllowedB n physical · indexed)
    (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (actualLinkAuxiliaryCoordinates n indexed.1 indexed.2))

/-- Conditional auxiliary sum for an arbitrary displayed family of private
link blocks. -/
def linkFamilyAuxiliaryMultiplicity (K n : Nat)
    (physical : EdgeLabelling) (links : List (Nat × Z4Link)) : Q' :=
  listQSum
    (fun auxiliary =>
      if linkFamilyConditionalAllowedB n physical links auxiliary
        then 1 else 0)
    (boundedEdgeLabellings (linkAuxiliaryCutoff K)
      (links.flatMap fun indexed =>
        actualLinkAuxiliaryCoordinates n indexed.1 indexed.2))

def linkAuxiliaryMultiplicityProduct (K n : Nat)
    (physical : EdgeLabelling) : List (Nat × Z4Link) → Q'
  | [] => 1
  | indexed :: rest =>
      linkAuxiliaryMultiplicity K n physical indexed *
        linkAuxiliaryMultiplicityProduct K n physical rest

/-! ## 2. Locality under a block overlay -/

/-- Overlaying the head block changes its local constraint exactly according
to the outer labelling and leaves every disjoint tail constraint exactly
according to the inner labelling. -/
theorem linkFamilyConditionalAllowedB_overlay_cons
    (n : Nat) (physical outer inner : EdgeLabelling)
    (head : Nat × Z4Link) (tail : List (Nat × Z4Link))
    (hdisjoint : ∀ indexed, indexed ∈ tail → ∀ edge,
      edge ∈ actualLinkAuxiliaryCoordinates n indexed.1 indexed.2 →
      edge ∉ actualLinkAuxiliaryCoordinates n head.1 head.2) :
    linkFamilyConditionalAllowedB n physical (head :: tail)
        (overlayOn
          (actualLinkAuxiliaryCoordinates n head.1 head.2)
          outer inner) =
      (linkConditionalAuxiliaryAllowedB n physical outer head &&
        linkFamilyConditionalAllowedB n physical tail inner) := by
  unfold linkFamilyConditionalAllowedB
  simp only [List.all_cons]
  have hhead := linkConditionalAuxiliaryAllowedB_congr_on
    n physical
    (overlayOn (actualLinkAuxiliaryCoordinates n head.1 head.2)
      outer inner)
    outer head
    (fun edge hedge => overlayOn_apply_of_mem hedge)
  have htail :
      tail.all
          (linkConditionalAuxiliaryAllowedB n physical
            (overlayOn
              (actualLinkAuxiliaryCoordinates n head.1 head.2)
              outer inner)) =
        tail.all (linkConditionalAuxiliaryAllowedB n physical inner) := by
    apply list_all_congr_on
    intro indexed hindexed
    apply linkConditionalAuxiliaryAllowedB_congr_on
    intro edge hedge
    exact overlayOn_apply_of_not_mem
      (hdisjoint indexed hindexed edge hedge)
  rw [hhead, htail]

/-! ## 3. Finite-sum algebra -/

theorem boolIndicator_and_factor (left right : Bool) :
    (if left && right then (1 : Q') else 0) ≈
      (if left then 1 else 0) * (if right then 1 else 0) := by
  cases left <;> cases right
  · exact Q'.eqv_symm (Q'.zero_mul_eqv 0)
  · exact Q'.eqv_symm (Q'.zero_mul_eqv 1)
  · exact Q'.eqv_symm (Q'.mul_zero_eqv 1)
  · exact Q'.eqv_symm (Q'.one_mul_eqv 1)

theorem listQSum_mul_const {A : Type} (f : A → Q')
    (constant : Q') : ∀ xs : List A,
    listQSum (fun x => f x * constant) xs ≈
      listQSum f xs * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv _)
  | x :: xs => by
      simp only [listQSum]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_mul_const f constant xs))
        (Q'.eqv_symm
          (Q'.add_mul_eqv (f x) (listQSum f xs) constant))

/-- One exact Fubini step: a disjoint head block factors from the tail family. -/
theorem linkFamilyAuxiliaryMultiplicity_cons_factor
    (K n : Nat) (physical : EdgeLabelling)
    (head : Nat × Z4Link) (tail : List (Nat × Z4Link))
    (hdisjoint : ∀ indexed, indexed ∈ tail → ∀ edge,
      edge ∈ actualLinkAuxiliaryCoordinates n indexed.1 indexed.2 →
      edge ∉ actualLinkAuxiliaryCoordinates n head.1 head.2) :
    linkFamilyAuxiliaryMultiplicity K n physical (head :: tail) ≈
      linkAuxiliaryMultiplicity K n physical head *
        linkFamilyAuxiliaryMultiplicity K n physical tail := by
  let headEdges := actualLinkAuxiliaryCoordinates n head.1 head.2
  let tailEdges := tail.flatMap fun indexed =>
    actualLinkAuxiliaryCoordinates n indexed.1 indexed.2
  let headAllowed : EdgeLabelling → Bool := fun auxiliary =>
    linkConditionalAuxiliaryAllowedB n physical auxiliary head
  let tailAllowed : EdgeLabelling → Bool := fun auxiliary =>
    linkFamilyConditionalAllowedB n physical tail auxiliary
  unfold linkFamilyAuxiliaryMultiplicity
  refine Q'.eqv_trans _
    (listQSum
      (fun outer =>
        listQSum
          (fun inner =>
            if linkFamilyConditionalAllowedB n physical (head :: tail)
                (overlayOn headEdges outer inner)
              then (1 : Q') else 0)
          (boundedEdgeLabellings (linkAuxiliaryCutoff K) tailEdges))
      (boundedEdgeLabellings (linkAuxiliaryCutoff K) headEdges)) _ ?_ ?_
  · exact listQSum_bounded_append_fubini (linkAuxiliaryCutoff K)
      headEdges tailEdges
      (fun auxiliary =>
        if linkFamilyConditionalAllowedB n physical (head :: tail)
          auxiliary then (1 : Q') else 0)
  · refine Q'.eqv_trans _
      (listQSum
        (fun outer =>
          (if headAllowed outer then (1 : Q') else 0) *
            linkFamilyAuxiliaryMultiplicity K n physical tail)
        (boundedEdgeLabellings (linkAuxiliaryCutoff K) headEdges)) _ ?_ ?_
    · apply listQSum_congr
      intro outer
      unfold linkFamilyAuxiliaryMultiplicity
      refine Q'.eqv_trans _
        (listQSum
          (fun inner =>
            (if headAllowed outer then (1 : Q') else 0) *
              (if tailAllowed inner then (1 : Q') else 0))
          (boundedEdgeLabellings (linkAuxiliaryCutoff K) tailEdges)) _ ?_ ?_
      · apply listQSum_congr
        intro inner
        have hsplit := linkFamilyConditionalAllowedB_overlay_cons
          n physical outer inner head tail hdisjoint
        dsimp [headEdges]
        rw [hsplit]
        exact boolIndicator_and_factor
          (headAllowed outer) (tailAllowed inner)
      · exact listQSum_const_mul
          (if headAllowed outer then (1 : Q') else 0)
          (fun inner => if tailAllowed inner then (1 : Q') else 0)
          (boundedEdgeLabellings (linkAuxiliaryCutoff K) tailEdges)
    · unfold linkAuxiliaryMultiplicity
      exact listQSum_mul_const
        (fun outer => if headAllowed outer then (1 : Q') else 0)
        (linkFamilyAuxiliaryMultiplicity K n physical tail)
        (boundedEdgeLabellings (linkAuxiliaryCutoff K) headEdges)

/-! ## 4. Product over the enumerated links -/

theorem linkFamilyAuxiliaryMultiplicity_enumerateFrom_factor
    (K n : Nat) (physical : EdgeLabelling) :
    ∀ (start : Nat) (links : List Z4Link),
    linkFamilyAuxiliaryMultiplicity K n physical
        (enumerateFrom start links) ≈
      linkAuxiliaryMultiplicityProduct K n physical
        (enumerateFrom start links)
  | _, [] => by
      unfold linkFamilyAuxiliaryMultiplicity
        linkFamilyConditionalAllowedB linkAuxiliaryMultiplicityProduct
      change (1 : Q') + 0 ≈ 1
      exact Q'.eqv_of_eq (Q'.add_zero' 1)
  | start, ell :: rest => by
      let head : Nat × Z4Link := (start, ell)
      let tail := enumerateFrom (start + 1) rest
      have hdisjoint : ∀ indexed, indexed ∈ tail → ∀ edge,
          edge ∈ actualLinkAuxiliaryCoordinates n indexed.1 indexed.2 →
          edge ∉ actualLinkAuxiliaryCoordinates n head.1 head.2 := by
        intro indexed hindexed edge hedge
        have hindexGe : start + 1 ≤ indexed.1 :=
          YMGap.Continuum.Z4LinkIdentifierFreshness.enumerateFrom_index_ge
            hindexed
        intro hhead
        dsimp [head] at hhead ⊢
        exact actualLinkAuxiliaryCoordinates_disjoint_of_index_lt
          (n := n) (leftLink := ell) (rightLink := indexed.2)
          (by omega) edge hhead hedge
      change linkFamilyAuxiliaryMultiplicity K n physical (head :: tail) ≈
        linkAuxiliaryMultiplicity K n physical head *
          linkAuxiliaryMultiplicityProduct K n physical tail
      exact Q'.eqv_trans _
        (linkAuxiliaryMultiplicity K n physical head *
          linkFamilyAuxiliaryMultiplicity K n physical tail) _
        (linkFamilyAuxiliaryMultiplicity_cons_factor
          K n physical head tail hdisjoint)
        (Q'.mul_eqv_congr_left _ _ _
          (linkFamilyAuxiliaryMultiplicity_enumerateFrom_factor
            K n physical (start + 1) rest))

/-- The block-ordered global multiplicity is the exact product of the local
fixed-external-label link multiplicities. -/
theorem conditionalAuxiliaryMultiplicityByLinkBlocks_eq_product
    (K n : Nat) (physical : EdgeLabelling) :
    conditionalAuxiliaryMultiplicityByLinkBlocks K n physical ≈
      linkAuxiliaryMultiplicityProduct K n physical
        (enumerate (distinctBoxLinks n)) := by
  refine Q'.eqv_trans _
    (linkFamilyAuxiliaryMultiplicity K n physical
      (enumerate (distinctBoxLinks n))) _ ?_ ?_
  · unfold conditionalAuxiliaryMultiplicityByLinkBlocks
      linkFamilyAuxiliaryMultiplicity productionLinkAuxiliaryEdges
    apply listQSum_congr
    intro auxiliary
    unfold conditionalAuxiliaryMultiplicityTerm
      linkFamilyConditionalAllowedB
    rw [conditionalAuxiliaryAllowedB_eq_link_all]
    exact Q'.eqv_refl _
  · unfold enumerate
    exact linkFamilyAuxiliaryMultiplicity_enumerateFrom_factor
      K n physical 0 (distinctBoxLinks n)

/-- **Global conditional link factorization.** -/
theorem conditionalAuxiliaryMultiplicity_eq_link_product
    (K n : Nat) (physical : EdgeLabelling) :
    conditionalAuxiliaryMultiplicity K n physical ≈
      linkAuxiliaryMultiplicityProduct K n physical
        (enumerate (distinctBoxLinks n)) :=
  Q'.eqv_trans _ _ _
    (conditionalAuxiliaryMultiplicity_eq_byLinkBlocks K n physical)
    (conditionalAuxiliaryMultiplicityByLinkBlocks_eq_product
      K n physical)

theorem conditionalBoxAuxiliarySum_eq_link_product
    (K n : Nat) (physical : EdgeLabelling) :
    conditionalBoxAuxiliarySum K n physical ≈
      linkAuxiliaryMultiplicityProduct K n physical
        (enumerate (distinctBoxLinks n)) :=
  Q'.eqv_trans _ _ _
    (conditionalBoxAuxiliarySum_eq_multiplicity K n physical)
    (conditionalAuxiliaryMultiplicity_eq_link_product K n physical)

/-- **Exact finite-box link-factorized spin-foam formula.**  Every physical
plaquette character coefficient occurs once, and the remaining factor is
the product of exact fixed-external-label SU(2) fusion-basis multiplicities
over the enumerated physical links. -/
theorem fusionCompleteBoxVertexCartesianSum_eq_linkSpinFoam
    (K n : Nat) :
    fusionCompleteBoxVertexCartesianSum K n ≈
      listQSum
        (fun physical =>
          physicalBoxPacketFactor K n physical *
            linkAuxiliaryMultiplicityProduct K n physical
              (enumerate (distinctBoxLinks n)))
        (boundedEdgeLabellings (linkAuxiliaryCutoff K)
          (List.range (plaquetteEdgeCount n))) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun physical =>
        physicalBoxPacketFactor K n physical *
          conditionalBoxAuxiliarySum K n physical)
      (boundedEdgeLabellings (linkAuxiliaryCutoff K)
        (List.range (plaquetteEdgeCount n)))) _
    (fusionCompleteBoxVertexCartesianSum_eq_conditional K n) ?_
  apply listQSum_congr
  intro physical
  exact Q'.mul_eqv_congr_left _ _ _
    (conditionalBoxAuxiliarySum_eq_link_product K n physical)

end YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization.linkFamilyConditionalAllowedB_overlay_cons
#print axioms YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization.linkAuxiliaryMultiplicity_eq_invariantCount
#print axioms YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization.linkFamilyAuxiliaryMultiplicity_cons_factor
#print axioms YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization.linkFamilyAuxiliaryMultiplicity_enumerateFrom_factor
#print axioms YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization.conditionalAuxiliaryMultiplicityByLinkBlocks_eq_product
#print axioms YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization.conditionalAuxiliaryMultiplicity_eq_link_product
#print axioms YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization.conditionalBoxAuxiliarySum_eq_link_product
#print axioms YMGap.Continuum.Z4ConditionalLinkMultiplicityFactorization.fusionCompleteBoxVertexCartesianSum_eq_linkSpinFoam
