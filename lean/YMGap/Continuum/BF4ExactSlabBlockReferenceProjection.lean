/-
# Finite-family Haar reference on one actual detached background

The reference integrates a selected subfamily of physical links on the
background obtained by detaching a possibly larger family. Both completion
comparison maps retain the same original polynomial coordinates. The actual
interacting block conditional and this auxiliary reference fix each other's
ranges. They are not asserted equal or orthogonal in the original form.
-/

import YMGap.Continuum.BF4ExactSlabBlockCompletionComparison
import YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
import YMGap.Continuum.SU2QuaternionWeightedHaarFamilyCompletion
import YMGap.Continuum.GNSDenseFixedPoint

namespace YMGap.Continuum.BF4ExactSlabBlockReferenceProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockCompletionComparison
open YMGap.Continuum.BF4ExactSlabBlockOriginalConditional
open YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionWeightedHaarFamilyCompletion
open YMGap.Continuum.SU2QuaternionWeightedHaarProjectionCompletion
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K)
  (S A : List Z4Link)
  (hS : ∀ link, link ∈ S → link ∈ boundaryCompleteSlabLinks extent)
  (hAS : ∀ link, link ∈ A → link ∈ S)

local notation "blocks" => List.length (boundaryCompleteSlabLinks extent)
local notation "F" => fullData hw0 hw1 K extent hK
local notation "W" => background w K extent S
local notation "H" => background_certificate hw0 hw1 K extent hK S
local notation "G" => backgroundData hw0 hw1 K extent hK S
local notation "ids" => slots extent A
local notation "J" => toBackground hw0 hw1 K extent hK S hS
local notation "I" => toFull hw0 hw1 K extent hK S hS

include hS hAS in
private theorem selected_valid :
    ∀ link, link ∈ A → link ∈ boundaryCompleteSlabLinks extent := by
  intro link hA
  exact hS link (hAS link hA)

include hS hAS in
private theorem selected_slots_valid :
    ∀ i, i ∈ ids → i < blocks :=
  slots_valid extent A (selected_valid extent S A hS hAS)

include hS hAS in
private theorem background_selected_independent :
    ∀ i, i ∈ ids → QuaternionBlockIndependent i W := by
  intro i hi
  obtain ⟨link, hA, rfl⟩ := List.mem_map.mp hi
  exact background_independent_on_support w K extent S
    (hS link (hAS link hA)) (hAS link hA)

local notation "M" => familyProjection blocks W H ids
  (selected_slots_valid extent S A hS hAS)
  (background_selected_independent (w := w) K extent S A hS hAS)
local notation "P" => conditionalProjection hw0 hw1 K extent hK A
  (selected_valid extent S A hS hAS)

/-- Literal reference representative, with the supplied completion moduli. -/
def referenceCauchy (X : CauchyGNS F) : CauchyGNS F :=
  BF4ExactSlabBlockOriginalConditional.toFullCauchy hw0 hw1 K extent hK S hS
    ((familyMap blocks W H ids
      (selected_slots_valid extent S A hS hAS)
      (background_selected_independent (w := w) K extent S A hS hAS)).mapCauchy
      (toBackgroundCauchy hw0 hw1 K extent hK S hS X))

/-- The reference is orthogonal in G, not asserted orthogonal in F. -/
def reference (x : GNSCompletionSpace F) : GNSCompletionSpace F :=
  I (M (J x))

local notation "Q" => reference hw0 hw1 K extent hK S A hS hAS

theorem reference_mk (X : CauchyGNS F) :
    Q (Quotient.mk (cauchySetoid F) X) =
      Quotient.mk (cauchySetoid F)
        (referenceCauchy hw0 hw1 K extent hK S A hS hAS X) := rfl

theorem reference_embed (p : (F).V) :
    Q (embedV F p) =
      embedV F ⟨familyProject ids p.val, familyProject_supported ids p.property⟩ := by
  unfold reference
  rw [toBackground_embed]
  exact (congrArg I (familyProjection_embed blocks W H ids
    (selected_slots_valid extent S A hS hAS)
    (background_selected_independent (w := w) K extent S A hS hAS) p)).trans
    (toFull_embed hw0 hw1 K extent hK S hS _)

/-- The background image of the reference is the SAME family Haar map. -/
theorem background_reference (x : GNSCompletionSpace F) :
    J (Q x) = M (J x) :=
  toBackground_toFull hw0 hw1 K extent hK S hS _

private theorem singleton_subset (link : Z4Link) (hlink : link ∈ S) :
    ∀ j, j ∈ [link] → j ∈ S := by
  intro j hj
  exact (List.mem_singleton.mp hj) ▸ hlink

/-- With the SAME detached background, a singleton reference is precisely
the completed weighted coordinate Haar map in background coordinates. -/
theorem background_reference_singleton (link : Z4Link) (hlink : link ∈ S)
    (x : GNSCompletionSpace F) :
    J (reference hw0 hw1 K extent hK S [link] hS
      (singleton_subset S link hlink) x) =
      projection blocks W H
        ((boundaryCompleteSlabLinks extent).idxOf link)
        (List.idxOf_lt_length_of_mem (hS link hlink))
        (background_independent_on_support w K extent S
          (hS link hlink) hlink) (J x) := by
  rw [background_reference hw0 hw1 K extent hK S [link] hS
    (singleton_subset S link hlink) x]
  change familyProjection blocks W H [((boundaryCompleteSlabLinks extent).idxOf link)]
      _ _ (J x) = _
  exact familyProjection_singleton blocks W H _
    (List.idxOf_lt_length_of_mem (hS link hlink))
    (background_independent_on_support w K extent S
      (hS link hlink) hlink) (J x)

/-- The original block conditional fixes every reference image. -/
theorem conditional_reference (x : GNSCompletionSpace F) : P (Q x) = Q x := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [reference_mk]
  apply GNSDenseFixedPoint.fixed_of_cauchy_terms P
    (conditionalProjection_selfAdjoint hw0 hw1 K extent hK A
      (selected_valid extent S A hS hAS))
  intro n
  change P (embedV F
      ⟨familyProject ids (X.seq n).val,
        familyProject_supported ids (X.seq n).property⟩) = _
  apply conditionalProjection_fix_exterior_polynomial hw0 hw1 K extent hK A
    (selected_valid extent S A hS hAS)
  intro i hi
  exact familyProject_independent ids (X.seq n).val i hi

/-- The raw reference fixes every actual block-conditional output. Its
explicit representative is independent of each selected original slot. -/
theorem reference_conditional (x : GNSCompletionSpace F) : Q (P x) = P x := by
  refine Quotient.inductionOn x ?_
  intro X
  let T := conditionalDenseMap hw0 hw1 K extent hK A
    (selected_valid extent S A hS hAS)
  let Y := T.mapRep X
  let Z := toBackgroundCauchy hw0 hw1 K extent hK S hS Y
  have hy (n : Nat) : ∀ i, i ∈ ids → QuaternionBlockIndependent i (Y.seq n).val := by
    intro i hi
    let m := (T.mapOuter X).phi n
    let j := (T.mapOuter X).reindex.Jidx n
    change QuaternionBlockIndependent i
      ((T.toRep (X.seq m)).seq j).val
    exact inverseCauchy_independent hw0 hw1 K extent hK A
      (selected_valid extent S A hS hAS) (X.seq m) j i hi
  have hfix : M (Quotient.mk (cauchySetoid G) Z) =
      Quotient.mk (cauchySetoid G) Z :=
    familyProjection_fixed_cauchy blocks W H ids
      (selected_slots_valid extent S A hS hAS)
      (background_selected_independent (w := w) K extent S A hS hAS) Z hy
  change I (M (Quotient.mk (cauchySetoid G) Z)) =
    Quotient.mk (cauchySetoid F) Y
  rw [hfix]
  exact toFull_toBackground hw0 hw1 K extent hK S hS
    (Quotient.mk (cauchySetoid F) Y)

#print axioms referenceCauchy
#print axioms reference
#print axioms reference_mk
#print axioms reference_embed
#print axioms background_reference
#print axioms background_reference_singleton
#print axioms conditional_reference
#print axioms reference_conditional

end YMGap.Continuum.BF4ExactSlabBlockReferenceProjection
