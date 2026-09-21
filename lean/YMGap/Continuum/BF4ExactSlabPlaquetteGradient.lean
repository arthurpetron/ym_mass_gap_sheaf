/-
# Star-local gradients of a whole signed plaquette observable

The observable is the literal signed sum of all original physical-face
fundamental characters.  For a selected physical link, its incident part
contains exactly the faces meeting that link.  Conjugating the head angular
derivative back to original coordinates gives an actual star-local test.

The derivative of the whole signed observable is coefficient-equivalent to
the derivative of this incident part: every nonincident face is killed by
the selected-link angular derivative.  All signed coefficients are retained.
These are finite polynomial support identities only; no action, response,
positivity, or analytic estimate is asserted.
-/

import YMGap.Continuum.BF4ExactSlabSelectedStarVariance
import YMGap.Continuum.BF4ExactSlabWardStarGeometry
import YMGap.Continuum.SU2QuaternionAngularLocality
import YMGap.Continuum.SU2QuaternionHaarCertificateReindex
import YMGap.Continuum.SU2QuaternionHaarAngularIBP
import YMGap.Continuum.SU2QuaternionAngularSupport
import YMGap.Continuum.SU2QuaternionHaarHeadFubini
import YMGap.Continuum.QuaternionHaarSquareCertificate

namespace YMGap.Continuum.BF4ExactSlabPlaquetteGradient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.BF4ExactSlabSelectedFaceFold
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
open YMGap.Continuum.BF4ExactSlabWardStarGeometry
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionHaarCertificateReindex
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionAngularLocality
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

private abbrev blocks (extent : Nat) : Nat :=
  (boundaryCompleteSlabLinks extent).length

/-- One signed fundamental-character summand, with its coefficient unchanged. -/
def term (extent : Nat) (c : Nat → Q') (id : Nat) : RatPoly :=
  polySmul (c id) (faceCharacter extent (slabPlaquetteAt extent id))

/-- The whole signed physical-plaquette observable. -/
def observable (extent : Nat) (c : Nat → Q') : RatPoly :=
  finitePolySum (term extent c) (slabPhysicalFaceEdges extent)

/-- Exactly the summands incident to one selected link. -/
def incidentObservable (extent : Nat) (link : Z4Link) (c : Nat → Q') : RatPoly :=
  finitePolySum (term extent c) (incidentIds extent link)

/-- Pull the incident gradient back to the original link coordinates. -/
def test (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (i j : Nat)
    (c : Nat → Q') : RatPoly :=
  let swap := linkHeadSwap extent link hl
  reindexQuaternionPolynomial swap
    (angularDerivative i j
      (reindexQuaternionPolynomial swap (incidentObservable extent link c)))

private theorem term_supported (extent : Nat) (c : Nat → Q') (id : Nat) :
    SupportedQuaternionBlocks (blocks extent) (term extent c id) := by
  unfold term
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact faceCharacter_supported extent (slabPlaquetteAt extent id) s hs

private theorem sum_supported {A : Type} {extent : Nat} (f : A → RatPoly)
    (hf : ∀ a, SupportedQuaternionBlocks (blocks extent) (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks (blocks extent) (finitePolySum f xs)
  | [] => fun _ h => False.elim (List.not_mem_nil h)
  | a :: xs => supported_add (hf a) (sum_supported f hf xs)

/-- The entire signed observable is supported on the original slab carrier. -/
theorem observable_supported (extent : Nat) (c : Nat → Q') :
    SupportedQuaternionBlocks (blocks extent) (observable extent c) :=
  sum_supported (term extent c) (term_supported extent c) _

/-- The incident signed sub-observable is supported on the same carrier. -/
theorem incidentObservable_supported (extent : Nat) (link : Z4Link) (c : Nat → Q') :
    SupportedQuaternionBlocks (blocks extent) (incidentObservable extent link c) :=
  sum_supported (term extent c) (term_supported extent c) _

private theorem term_local (extent : Nat) (c : Nat → Q') (id : Nat) :
    LinkLocal extent (edgesOf (slabPlaquetteAt extent id)) (term extent c id) := by
  unfold term faceCharacter
  exact ((face_scalar_local extent (slabPlaquetteAt extent id)).character 1).smul (c id)

/-- The incident signed sum uses no link outside the selected link's faces. -/
theorem incidentObservable_local (extent : Nat) (link : Z4Link) (c : Nat → Q') :
    LinkLocal extent (starLinks extent link) (incidentObservable extent link c) := by
  have hlocal : LinkLocal extent (faceLinks extent (incidentIds extent link))
      (incidentObservable extent link c) := by
    apply BlockLocal.finiteSum
    intro id hid
    exact (term_local extent c id).mono (fun other hother =>
      List.mem_flatMap.mpr ⟨id, hid, hother⟩)
  exact hlocal.mono (fun other hother => List.mem_cons_of_mem link hother)

/-- The pulled-back incident gradient stays on the same complete link star. -/
theorem test_local (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) {i j : Nat}
    (hi : i < 4) (hj : j < 4) (c : Nat → Q') :
    LinkLocal extent (starLinks extent link) (test extent link hl i j c) := by
  unfold test
  apply conjugatedHead_angularDerivative_local (linkHeadSwap extent link hl)
    (incidentObservable_local extent link c)
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl))
  · rw [show (linkHeadSwap extent link hl).map 0 =
        (boundaryCompleteSlabLinks extent).idxOf link from
        headSwapBlockInvolution_map_zero _ _ (List.idxOf_lt_length_of_mem hl),
      correctedSlabLinkAt_idxOf hl]
    exact near_refl extent link
  · exact hi
  · exact hj

/-- The pulled-back incident gradient is supported on the original carrier. -/
theorem test_supported (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) (i j : Nat) (c : Nat → Q') :
    SupportedQuaternionBlocks (blocks extent) (test extent link hl i j c) := by
  unfold test
  exact reindex_supported (linkHeadSwap extent link hl) _

private theorem finitePolySum_append {A : Type} (f : A → RatPoly) :
    ∀ xs ys : List A,
      finitePolySum f (xs ++ ys) =
        polyAdd (finitePolySum f xs) (finitePolySum f ys)
  | [], _ => rfl
  | _ :: xs, ys => by
      simp only [List.cons_append, finitePolySum, finitePolySum_append f xs ys,
        polyAdd, List.append_assoc]

private theorem finitePolySum_perm {A : Type} (f : A → RatPoly)
    {xs ys : List A} (h : xs.Perm ys) :
    RatPolyCoeffEqv (finitePolySum f xs) (finitePolySum f ys) := by
  induction h with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons a h ih => exact (RatPolyCoeffEqv.refl (f a)).add ih
  | swap a b xs =>
      exact (RatPolyCoeffEqv.add_assoc (f b) (f a) (finitePolySum f xs)).symm.trans
        (((RatPolyCoeffEqv.add_comm (f b) (f a)).add
          (RatPolyCoeffEqv.refl (finitePolySum f xs))).trans
          (RatPolyCoeffEqv.add_assoc (f a) (f b) (finitePolySum f xs)))
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

private def complementObservable (extent : Nat) (link : Z4Link)
    (c : Nat → Q') : RatPoly :=
  finitePolySum (term extent c) (complementIds extent link)

private theorem complementObservable_local (extent : Nat) (link : Z4Link)
    (c : Nat → Q') :
    LinkLocal extent (faceLinks extent (complementIds extent link))
      (complementObservable extent link c) := by
  apply BlockLocal.finiteSum
  intro id hid
  exact (term_local extent c id).mono (fun other hother =>
    List.mem_flatMap.mpr ⟨id, hid, hother⟩)

/-- The selected-link angular derivative of the whole signed observable is
exactly its incident derivative. No coefficient is absolutized or discarded. -/
theorem observable_derivative_incident (extent : Nat) (link : Z4Link)
    (hl : link ∈ boundaryCompleteSlabLinks extent) {i j : Nat}
    (hi : i < 4) (hj : j < 4) (c : Nat → Q') :
    let swap := linkHeadSwap extent link hl
    RatPolyCoeffEqv
      (angularDerivative i j
        (reindexQuaternionPolynomial swap (observable extent c)))
      (angularDerivative i j
        (reindexQuaternionPolynomial swap (incidentObservable extent link c))) := by
  dsimp only
  let swap := linkHeadSwap extent link hl
  have hpartition : RatPolyCoeffEqv (observable extent c)
      (polyAdd (incidentObservable extent link c)
        (complementObservable extent link c)) := by
    refine (finitePolySum_perm (term extent c)
      (face_partition extent link).symm).trans ?_
    rw [finitePolySum_append]
    exact RatPolyCoeffEqv.refl _
  have hzero : RatPolyCoeffEqv
      (angularDerivative i j
        (reindexQuaternionPolynomial swap (complementObservable extent link c)))
      polyZero := by
    apply angularDerivative_independent_zero hi hj
    apply blockDegree_reindex swap
      (Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem hl))
      (headSwapBlockInvolution_map_zero _ _ (List.idxOf_lt_length_of_mem hl))
    exact linkLocal_degree_zero (complementObservable_local extent link c)
      link hl (link_not_mem_complement extent link)
  refine (angularDerivative_congr i j (RatPolyCoeffEqv.reindex swap hpartition)).trans ?_
  rw [reindexQuaternionPolynomial_add]
  exact (angularDerivative_add i j
    (reindexQuaternionPolynomial swap (incidentObservable extent link c))
    (reindexQuaternionPolynomial swap (complementObservable extent link c))).trans
      (((RatPolyCoeffEqv.refl _).add hzero).trans (RatPolyCoeffEqv.add_zero _))

end YMGap.Continuum.BF4ExactSlabPlaquetteGradient

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGradient.observable_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGradient.incidentObservable_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGradient.incidentObservable_local
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGradient.test_local
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGradient.test_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteGradient.observable_derivative_incident
