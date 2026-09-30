/-
# The singleton block map is the original star conditional projection

The two constructions use different exterior polynomial carriers: the block
construction keeps the original coordinates, while the star construction
removes and reindexes the selected head.  Their completed operators are
identified by their common fixed polynomial range and original full-action
pairing, not by definitional equality of their inverse iterations.

This is an exact non-strict projection identity, not a mixing estimate.
-/

import YMGap.Continuum.BF4ExactSlabBlockConditionalProjection
import YMGap.Continuum.BF4ExactSlabStarIndependentProbe
import YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation
import YMGap.Continuum.GNSDenseFixedPoint

namespace YMGap.Continuum.BF4ExactSlabBlockSingletonProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.GNSDenseFixedPoint
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabStarIndependentProbe
open YMGap.Continuum.BF4ExactSlabLocalSupportFluctuation
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockCompletedInverse
open YMGap.Continuum.BF4ExactSlabBlockOriginalConditional
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (link : Z4Link)
  (hl : link ∈ boundaryCompleteSlabLinks extent)

local notation "F" => fullData hw0 hw1 K extent hK
include hl in
private theorem singleton_valid :
    ∀ j, j ∈ [link] → j ∈ boundaryCompleteSlabLinks extent := by
  intro j hj
  simp only [List.mem_singleton] at hj
  subst j
  exact hl

local notation "B" => BF4ExactSlabBlockConditionalProjection.conditionalProjection
  hw0 hw1 K extent hK [link] (singleton_valid extent link hl)
local notation "S" => BF4ExactSlabStarConditionalProjection.conditionalProjection
  hw0 hw1 K extent hK link hl

include hl in
/-- A supported polynomial independent of the selected original coordinate
has literal link support away from that coordinate. -/
private theorem local_of_selected_independent (p : (F).V)
    (hp : QuaternionBlockIndependent
      ((boundaryCompleteSlabLinks extent).idxOf link) p.val) :
    LinkLocal extent (independentLinks extent link) p.val := by
  intro t ht b hb hnot c hc
  have hphys := correctedSlabLinkAt_mem (List.mem_range.mpr hb)
  have hselected : correctedSlabLinkAt extent b = link := by
    by_cases he : correctedSlabLinkAt extent b = link
    · exact he
    · have hm : correctedSlabLinkAt extent b ∈ independentLinks extent link := by
        apply List.mem_filter.mpr
        refine ⟨hphys, ?_⟩
        simp [he]
      exact False.elim (hnot hm)
  have hbi : b = (boundaryCompleteSlabLinks extent).idxOf link :=
    correctedSlabLinkAt_injective_on_physical
      (List.mem_range.mpr hb)
      (List.mem_range.mpr (List.idxOf_lt_length_of_mem hl))
      (hselected.trans (correctedSlabLinkAt_idxOf hl).symm)
  subst b
  have hind := hp t ht
  have hz := exponentAt_clearQuaternionBlock_self t.1
    ((boundaryCompleteSlabLinks extent).idxOf link) c hc
  rw [hind] at hz
  exact hz

/-- STAR fixes the actual singleton block output, using the existing block
Cauchy representative and no comparison of the two inverse iterations. -/
theorem star_fixes_block_dense (p : (F).V) :
    S (B (embedV F p)) = B (embedV F p) := by
  rw [BF4ExactSlabBlockConditionalProjection.conditionalProjection_embed]
  let X := BF4ExactSlabBlockOriginalConditional.conditionalRep hw0 hw1 K extent hK
    [link] (singleton_valid extent link hl) p
  exact fixed_of_cauchy_terms S
    (BF4ExactSlabStarConditionalProjection.conditionalProjection_selfAdjoint
      hw0 hw1 K extent hK link hl) X (fun n => by
      apply BF4ExactSlabStarIndependentProbe.conditionalProjection_fix_local
        hw0 hw1 K extent hK link hl (independentLinks extent link) (X.seq n)
      · apply local_of_selected_independent hw0 hw1 K extent hK link hl
        have hi : (boundaryCompleteSlabLinks extent).idxOf link ∈ slots extent [link] := by
          simp [slots]
        exact BF4ExactSlabBlockOriginalConditional.inverseCauchy_independent
          hw0 hw1 K extent hK [link] (singleton_valid extent link hl) p n _ hi
      · simp [independentLinks])

/-- BLOCK fixes the actual star output, whose lifted exterior approximants
are independent of the selected original coordinate. -/
theorem block_fixes_star_dense (p : (F).V) :
    B (S (embedV F p)) = S (embedV F p) := by
  rw [BF4ExactSlabStarConditionalProjection.conditionalProjection_embed]
  let X := (BF4ExactSlabStarConditionalProjection.conditionalDenseMap
    hw0 hw1 K extent hK link hl).toRep p
  have hfix := fixed_of_cauchy_terms B
    (BF4ExactSlabBlockConditionalProjection.conditionalProjection_selfAdjoint
      hw0 hw1 K extent hK [link] (singleton_valid extent link hl)) X (fun n => by
      apply BF4ExactSlabBlockConditionalProjection.conditionalProjection_fix_exterior_polynomial
        hw0 hw1 K extent hK [link] (singleton_valid extent link hl) (X.seq n)
      intro i hi
      have hselected : i = (boundaryCompleteSlabLinks extent).idxOf link := by
        simpa [slots] using hi
      subst i
      change QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf link)
        (BF4ExactSlabStarFullActionProbe.probeMap hw0 hw1 K extent hK link hl
          ((BF4ExactSlabStarCompletedInverse.inverseCauchy hw0 hw1 K extent hK link hl
            (BF4ExactSlabStarFullActionProbe.numeratorMap
              hw0 hw1 K extent hK link hl p)).seq n)).val
      exact probeMap_independent_selected hw0 hw1 K extent hK link hl _)
  change B (Quotient.mk (cauchySetoid F) X) = Quotient.mk (cauchySetoid F) X at hfix
  exact hfix

/-- The star projection fixes the entire singleton block range. -/
theorem star_fixes_block (x : GNSCompletionSpace F) : S (B x) = B x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact fixed_of_cauchy_images S B
    (BF4ExactSlabStarConditionalProjection.conditionalProjection_selfAdjoint
      hw0 hw1 K extent hK link hl)
    (BF4ExactSlabBlockConditionalProjection.conditionalProjection_selfAdjoint
      hw0 hw1 K extent hK [link] (singleton_valid extent link hl)) X
    (fun n => star_fixes_block_dense hw0 hw1 K extent hK link hl (X.seq n))

/-- The singleton block projection fixes the entire star range. -/
theorem block_fixes_star (x : GNSCompletionSpace F) : B (S x) = S x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact fixed_of_cauchy_images B S
    (BF4ExactSlabBlockConditionalProjection.conditionalProjection_selfAdjoint
      hw0 hw1 K extent hK [link] (singleton_valid extent link hl))
    (BF4ExactSlabStarConditionalProjection.conditionalProjection_selfAdjoint
      hw0 hw1 K extent hK link hl) X
    (fun n => block_fixes_star_dense hw0 hw1 K extent hK link hl (X.seq n))

/-- The singleton BLOCK operator is exactly the STAR operator used by the
conditional sweep and its Chebyshev recurrence, on every vector of the same
original full-action completion. -/
theorem conditionalProjection_singleton (x : GNSCompletionSpace F) :
    B x = S x := by
  apply eq_of_pairings_equal
  intro y
  calc
    (F).cinnerCompl (B x) y = (F).cinnerCompl (S (B x)) y := by
      rw [star_fixes_block hw0 hw1 K extent hK link hl x]
    _ = (F).cinnerCompl (B x) (S y) :=
      BF4ExactSlabStarConditionalProjection.conditionalProjection_selfAdjoint
        hw0 hw1 K extent hK link hl _ _
    _ = (F).cinnerCompl x (B (S y)) :=
      BF4ExactSlabBlockConditionalProjection.conditionalProjection_selfAdjoint
        hw0 hw1 K extent hK [link] (singleton_valid extent link hl) _ _
    _ = (F).cinnerCompl x (S y) := by
      rw [block_fixes_star hw0 hw1 K extent hK link hl y]
    _ = (F).cinnerCompl (S x) y :=
      (BF4ExactSlabStarConditionalProjection.conditionalProjection_selfAdjoint
        hw0 hw1 K extent hK link hl _ _).symm

end YMGap.Continuum.BF4ExactSlabBlockSingletonProjection

#print axioms YMGap.Continuum.BF4ExactSlabBlockSingletonProjection.star_fixes_block_dense
#print axioms YMGap.Continuum.BF4ExactSlabBlockSingletonProjection.block_fixes_star_dense
#print axioms YMGap.Continuum.BF4ExactSlabBlockSingletonProjection.star_fixes_block
#print axioms YMGap.Continuum.BF4ExactSlabBlockSingletonProjection.block_fixes_star
#print axioms YMGap.Continuum.BF4ExactSlabBlockSingletonProjection.conditionalProjection_singleton
