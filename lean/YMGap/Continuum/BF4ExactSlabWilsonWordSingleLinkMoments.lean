/-
# One-link moments of an actual ORIGINAL slab Wilson word

An ordered word whose literal head is a selected forward physical link and
whose tail omits that link has the exact free one-link first and second
moments against any spectator independent of the selected block.  This file
only connects the original slab word to the generic independent-tail Haar
calculation; it makes no variance or scaling claim.
-/

import YMGap.Continuum.SU2QuaternionIndependentTailMoments
import YMGap.Continuum.BF4ExactSlabWilsonWordLinkLocality
import YMGap.Continuum.BF4ExactSlabSpatialWilsonControl
import YMGap.Continuum.BF4ExactSlabLinkStarGeometry

namespace YMGap.Continuum.BF4ExactSlabWilsonWordSingleLinkMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabWilsonWordLinkLocality
open YMGap.Continuum.BF4ExactSlabSpatialWilsonControl (word_unit)
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
  (complementHeat complementHeat_degree_zero)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
  (degree_zero_independent)
open YMGap.Continuum.SU2QuaternionIndependentTailMoments

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

/-- The actual original ordered word with the selected forward link exposed
as its literal head has zero first moment against an independent spectator. -/
theorem original_word_first_moment
    (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    (tail : List OrientedBF4Link)
    (habsent : ∀ entry, entry ∈ tail → entry.link ≠ link)
    (r : RatPoly)
    (hr : QuaternionBlockIndependent
      ((boundaryCompleteSlabLinks extent).idxOf link) r) :
    quaternionHaar (B extent)
      (polyMul (character extent (⟨link, false⟩ :: tail) 1) r) ≈ 0 := by
  let block := (boundaryCompleteSlabLinks extent).idxOf link
  have hb : block < B extent := List.idxOf_lt_length_of_mem hl
  have hp := word_blockDegree_zero_of_link_absent extent link hl tail habsent
  have h := fundamental_first_moment (B extent) block hb (word extent tail) r hp hr
  simpa only [character, word, wordWith, orientedCorrectedSlabLinkPolynomial,
    Bool.false_eq_true, if_false, correctedSlabLinkPolynomial_of_mem hl, block] using h

/-- Under the existing ordered-word Haar-unit certificate, the same literal
head word has second moment equal to the untouched independent spectator. -/
theorem original_word_second_moment
    (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    (tail : List OrientedBF4Link)
    (hphysical : ∀ entry, entry ∈ tail →
      entry.link ∈ boundaryCompleteSlabLinks extent)
    (habsent : ∀ entry, entry ∈ tail → entry.link ≠ link)
    (r : RatPoly)
    (hr : QuaternionBlockIndependent
      ((boundaryCompleteSlabLinks extent).idxOf link) r) :
    quaternionHaar (B extent)
      (polyMul
        (polyMul (character extent (⟨link, false⟩ :: tail) 1)
          (character extent (⟨link, false⟩ :: tail) 1)) r) ≈
      quaternionHaar (B extent) r := by
  let block := (boundaryCompleteSlabLinks extent).idxOf link
  have hb : block < B extent := List.idxOf_lt_length_of_mem hl
  have hp := word_blockDegree_zero_of_link_absent extent link hl tail habsent
  have hnorm := word_unit extent tail hphysical
  have h := fundamental_second_moment
    (B extent) block hb (word extent tail) r hp hr hnorm
  simpa only [character, word, wordWith, orientedCorrectedSlabLinkPolynomial,
    Bool.false_eq_true, if_false, correctedSlabLinkPolynomial_of_mem hl, block] using h

/-- The selected-rest action is retained in full.  Its independence is the
existing link-star degree-zero theorem, not a newly assumed factorization. -/
theorem original_word_complement_first_moment
    (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    (tail : List OrientedBF4Link)
    (habsent : ∀ entry, entry ∈ tail → entry.link ≠ link) :
    quaternionHaar (B extent)
      (polyMul (character extent (⟨link, false⟩ :: tail) 1)
        (complementHeat w K extent link)) ≈ 0 := by
  exact original_word_first_moment extent link hl tail habsent _
    (degree_zero_independent (complementHeat_degree_zero w K extent link hl))

/-- Exact second moment against the unchanged selected-rest action product. -/
theorem original_word_complement_second_moment
    (w : Q') (K extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent)
    (tail : List OrientedBF4Link)
    (hphysical : ∀ entry, entry ∈ tail →
      entry.link ∈ boundaryCompleteSlabLinks extent)
    (habsent : ∀ entry, entry ∈ tail → entry.link ≠ link) :
    quaternionHaar (B extent)
      (polyMul
        (polyMul (character extent (⟨link, false⟩ :: tail) 1)
          (character extent (⟨link, false⟩ :: tail) 1))
        (complementHeat w K extent link)) ≈
      quaternionHaar (B extent) (complementHeat w K extent link) := by
  exact original_word_second_moment extent link hl tail hphysical habsent _
    (degree_zero_independent (complementHeat_degree_zero w K extent link hl))

#print axioms original_word_first_moment
#print axioms original_word_second_moment
#print axioms original_word_complement_first_moment
#print axioms original_word_complement_second_moment

end YMGap.Continuum.BF4ExactSlabWilsonWordSingleLinkMoments
