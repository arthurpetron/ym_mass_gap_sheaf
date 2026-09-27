/-
# Literal link locality of free-block fluctuations and detached spectators

The raw Haar block fluctuation of a link-local polynomial remains local on
the SAME physical links. Outside that set it is coefficientwise zero. The
detached original-action background is independent of every supplied local
link. These are raw-carrier identities, not an interacting Dirichlet bound.
-/

import YMGap.Continuum.BF4ExactSlabLocalSupportComparison
import YMGap.Continuum.BF4ExactSlabStarIndependentProbe
import YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
import YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal

namespace YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabStarIndependentProbe
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabStarNormalizer
open YMGap.Continuum.BF4ExactSlabStarInverseApproximation
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockProjection
open YMGap.Continuum.SU2QuaternionOriginalHaarBlockMarginal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

/-- Clearing a quaternion block never creates dependence outside a fixed
literal link support, even when the selected block is outside that support. -/
theorem project_linkLocal {extent : Nat} {S : List Z4Link} {p : RatPoly}
    (hp : LinkLocal extent S p) (selected : Nat) :
    LinkLocal extent S (project selected p) := by
  intro t ht block hb hn component hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  change exponentAt (clearQuaternionBlock selected s.1) (4*block+component) = 0
  rw [exponentAt_clearQuaternionBlock]
  by_cases h : coordinateInQuaternionBlock selected (4*block+component)
  · rw [if_pos h]
  · rw [if_neg h]
    exact hp s hs block hb hn component hc

theorem fluctuation_linkLocal {extent : Nat} {S : List Z4Link} {p : RatPoly}
    (hp : LinkLocal extent S p) (selected : Nat) :
    LinkLocal extent S (fluctuation selected p) :=
  hp.add ((project_linkLocal hp selected).neg)

theorem fluctuation_supported_local {extent : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks (blocks extent) p) (selected : Nat) :
    SupportedQuaternionBlocks (blocks extent) (fluctuation selected p) :=
  fluctuation_supported selected hp

/-- A physical link omitted by the literal support has no free Haar-block
fluctuation: the entire polynomial cancels in the coefficient quotient. -/
theorem fluctuation_zero_outside {extent : Nat} {S : List Z4Link} {p : RatPoly}
    (hp : LinkLocal extent S p) {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hnot : link ∉ S) :
    RatPolyCoeffEqv
      (fluctuation ((boundaryCompleteSlabLinks extent).idxOf link) p) polyZero := by
  let block := (boundaryCompleteSlabLinks extent).idxOf link
  have hind : QuaternionBlockIndependent block p :=
    independent_of_local hp (List.idxOf_lt_length_of_mem hl) (by
      intro hm
      apply hnot
      rw [correctedSlabLinkAt_idxOf hl] at hm
      exact hm)
  have hf := project_fixed block p hind
  unfold fluctuation
  exact (((RatPolyCoeffEqv.refl p).add (RatPolyCoeffEqv.neg hf)).trans
    ((coeffEvalExpr_eqv_of_normalize_eq
      (.add (.var 0) (.neg (.var 0))) (.const 0)
      (by decide) (fun _ => p)).trans (RatPolyCoeffEqv.zero_smul polyOne)))

/-- Every original detached heat factor is retained, but none touches a
link in the supplied support. This is syntactic block independence. -/
theorem background_independent_on_support (w : Q') (K extent : Nat)
    (S : List Z4Link) {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) (hS : link ∈ S) :
    QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf link)
      (background w K extent S) :=
  independent_of_local
    (heatProduct_local w K extent (detached extent S))
    (List.idxOf_lt_length_of_mem hl) (by
      intro hm
      have hm' : link ∈ faceLinks extent (detached extent S) := by
        rw [correctedSlabLinkAt_idxOf hl] at hm
        exact hm
      exact links_detached_disjoint extent S link hS hm')

/-- The already-constructed exterior probe really omits its selected
physical block on the same original full carrier. -/
theorem probeMap_independent_selected {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    (r : (exteriorData hw0 hw1 K extent hK link hl).V) :
    QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf link)
      (probeMap hw0 hw1 K extent hK link hl r).val := by
  have hp := probeMap_local hw0 hw1 K extent hK link hl r
  apply independent_of_local hp (List.idxOf_lt_length_of_mem hl)
  intro hm
  have hmem : link ∈ independentLinks extent link := by
    rw [correctedSlabLinkAt_idxOf hl] at hm
    exact hm
  have hd := (List.mem_filter.mp hmem).2
  have hn : link ≠ link := by simpa only [decide_eq_true_eq] using hd
  exact hn rfl

end YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation

#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation.project_linkLocal
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation.fluctuation_linkLocal
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation.fluctuation_supported_local
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation.fluctuation_zero_outside
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation.background_independent_on_support
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation.probeMap_independent_selected
