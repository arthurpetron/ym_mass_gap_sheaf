/-
# The original full-action image of the completed block conditional state

The identity on supported polynomials is bounded from the detached original
background form into the complete original action. The constructed inverse
state is then tested through the actual family marginal identities. This is
an ordinary weighted L2 construction, not an OS-time or scaling estimate.
-/

import YMGap.Continuum.BF4ExactSlabBlockCompletedInverse
import YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation
import YMGap.Continuum.BF4ExactSlabBlockExteriorPairing
import YMGap.Continuum.GNSDenseCompletionLaws

namespace YMGap.Continuum.BF4ExactSlabBlockOriginalConditional

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.GNSDenseCompletionExtension
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabBlockComparisonConstants
open YMGap.Continuum.BF4ExactSlabBlockNormalizer
open YMGap.Continuum.BF4ExactSlabBlockNormalizerMap
open YMGap.Continuum.BF4ExactSlabBlockInverseApproximation
open YMGap.Continuum.BF4ExactSlabBlockCompletedInverse
open YMGap.Continuum.BF4ExactSlabBlockConditionalApproximation
open YMGap.Continuum.BF4ExactSlabBlockExteriorPairing
open YMGap.Continuum.BF4ExactSlabBlockInsertedNorm
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K extent : Nat) (hK : headCutoff w ≤ K) (links : List Z4Link)
  (hl : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)

local notation "G" => backgroundData hw0 hw1 K extent hK links
local notation "F" => fullData hw0 hw1 K extent hK
local notation "M" => normalizerMap hw0 hw1 K extent hK links
local notation "U" => blockUpper w links.length

/-- Both weighted data have the identical supported polynomial carrier. -/
private def toFullVector
    (_hphysical : ∀ link, link ∈ links → link ∈ boundaryCompleteSlabLinks extent)
    (a : (G).V) : (F).V := a

/-- The entire original action costs only the selected-link collar ceiling
relative to the retained detached background; no locality of `a` is assumed. -/
theorem toFull_norm_bound (a : (G).V) :
    (F).B (toFullVector hw0 hw1 K extent hK links hl a)
      (toFullVector hw0 hw1 K extent hK links hl a) ≤ U * (G).B a a := by
  exact (collar_weighted_bounds hw0 hw1 K extent hK links links.length
    (Nat.le_refl _) (Certificate.square a.val a.property)).2

theorem toFull_distance_bound (a b : (G).V) :
    (F).distSqQ (toFullVector hw0 hw1 K extent hK links hl a)
      (toFullVector hw0 hw1 K extent hK links hl b) ≤
      U * (G).distSqQ a b := by
  change (F).B ((F).sub a b) ((F).sub a b) ≤
    U * (G).B ((G).sub a b) ((G).sub a b)
  exact toFull_norm_bound hw0 hw1 K extent hK links hl ((G).sub a b)

private def toFullTolerance (w : Q') (size : Nat) (epsilon : Q') : Q' :=
  epsilon * ExpUBInstance.oneOver1p (blockUpper w size)

private theorem toFullTolerance_pos {epsilon : Q'} (h : (0 : Q') < epsilon) :
    (0 : Q') < toFullTolerance w links.length epsilon :=
  Q'.mul_pos h (oneOver1p_pos _)

include hw0 in
private theorem toFull_budget {epsilon : Q'} (h : (0 : Q') < epsilon) :
    U * toFullTolerance w links.length epsilon ≤ epsilon :=
  key_bound U epsilon (Q'.le_of_lt (blockUpper_positive hw0 links.length))
    (Q'.le_of_lt h)

/-- Identity-sequence map into the existing original full-action completion. -/
def toFullCauchy (X : CauchyGNS G) : CauchyGNS F where
  seq := fun n => toFullVector hw0 hw1 K extent hK links hl (X.seq n)
  modulus := fun epsilon => X.modulus (toFullTolerance w links.length epsilon)
  isCauchy := by
    intro epsilon hepsilon p q hp hq
    exact Q'.le_trans' _ _ _ (toFull_distance_bound hw0 hw1 K extent hK links hl _ _)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
        (X.isCauchy _ (toFullTolerance_pos (w := w) links hepsilon) p q hp hq)
        (Q'.le_of_lt (blockUpper_positive hw0 links.length)))
        (toFull_budget hw0 links hepsilon))

/-- Explicit transport of null moduli into the original full-action form. -/
def toFullNullModulus {X Y : CauchyGNS G} (h : CauchyNullModulus G X Y) :
    CauchyNullModulus F
      (toFullCauchy hw0 hw1 K extent hK links hl X)
      (toFullCauchy hw0 hw1 K extent hK links hl Y) where
  modulus := fun epsilon => h.modulus (toFullTolerance w links.length epsilon)
  close := by
    intro epsilon hepsilon n hn
    exact Q'.le_trans' _ _ _ (toFull_distance_bound hw0 hw1 K extent hK links hl _ _)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
        (h.close _ (toFullTolerance_pos (w := w) links hepsilon) n hn)
        (Q'.le_of_lt (blockUpper_positive hw0 links.length)))
        (toFull_budget hw0 links hepsilon))

private theorem toFullCauchy_null {X Y : CauchyGNS G} (h : CauchyNull G X Y) :
    CauchyNull F (toFullCauchy hw0 hw1 K extent hK links hl X)
      (toFullCauchy hw0 hw1 K extent hK links hl Y) := by
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := h (toFullTolerance w links.length epsilon)
    (toFullTolerance_pos (w := w) links hepsilon)
  refine ⟨N, fun n hn => ?_⟩
  exact Q'.le_trans' _ _ _ (toFull_distance_bound hw0 hw1 K extent hK links hl _ _)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _
      (hN n hn) (Q'.le_of_lt (blockUpper_positive hw0 links.length)))
      (toFull_budget hw0 links hepsilon))

def toFullCompletion : GNSCompletionSpace G → GNSCompletionSpace F :=
  Quotient.lift
    (fun X => Quotient.mk (cauchySetoid F)
      (toFullCauchy hw0 hw1 K extent hK links hl X))
    (fun _ _ h => Quotient.sound (toFullCauchy_null hw0 hw1 K extent hK links hl h))

theorem toFullCompletion_embed (r : (G).V) :
    toFullCompletion hw0 hw1 K extent hK links hl (embedV G r) =
      embedV F (toFullVector hw0 hw1 K extent hK links hl r) := by
  apply Quotient.sound
  intro epsilon hepsilon
  exact ⟨0, fun _ _ => Q'.le_trans' _ _ _
    (Q'.le_of_eqv ((F).rad_refl r)) (Q'.le_of_lt hepsilon)⟩

/-- Cauchy representative of the actual family-conditional output. -/
def conditionalRep (p : (F).V) : CauchyGNS F :=
  toFullCauchy hw0 hw1 K extent hK links hl
    (inverseCauchy hw0 hw1 K extent hK links hl
      (numeratorVector hw0 hw1 K extent hK links p.val p.property))

def conditionalUpdate (p : (F).V) : GNSCompletionSpace F :=
  Quotient.mk (cauchySetoid F)
    (conditionalRep hw0 hw1 K extent hK links hl p)

/-- The exact exterior-pairing identity extends only for representatives
whose every term is independent of the integrated block family. No such
claim is made for arbitrary vectors of the detached background completion. -/
theorem toFull_pair_of_independent (X Y : CauchyGNS G)
    (hX : ∀ n i, i ∈ slots extent links →
      QuaternionBlockIndependent i (X.seq n).val)
    (hY : ∀ n i, i ∈ slots extent links →
      QuaternionBlockIndependent i (Y.seq n).val) :
    (F).cinnerCompl
      (toFullCompletion hw0 hw1 K extent hK links hl (Quotient.mk (cauchySetoid G) X))
      (toFullCompletion hw0 hw1 K extent hK links hl (Quotient.mk (cauchySetoid G) Y)) =
      (G).cinnerCompl (Quotient.mk (cauchySetoid G) X)
        (normalizerCompletion hw0 hw1 K extent hK links hl
          (Quotient.mk (cauchySetoid G) Y)) := by
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal ?_
    (CReal.convergesTo_ofQ'CauchySeq _ _) (CReal.convergesTo_ofQ'CauchySeq _ _)
  intro n
  exact CReal.ofQ'_equiv_of_eqv
    (original_exterior_pair hw0 hw1 K extent hK links hl
      (X.seq n) (Y.seq n) (hX n) (hY n))

/-- Finite block-numerator testing extends to any explicitly independent
Cauchy representative, with arbitrary supported original observable. -/
theorem toFull_test_of_independent (X : CauchyGNS G)
    (hX : ∀ n i, i ∈ slots extent links →
      QuaternionBlockIndependent i (X.seq n).val)
    (p : (F).V) :
    (F).cinnerCompl
      (toFullCompletion hw0 hw1 K extent hK links hl (Quotient.mk (cauchySetoid G) X))
      (embedV F p) =
      (G).cinnerCompl (Quotient.mk (cauchySetoid G) X)
        (embedV G (numeratorVector hw0 hw1 K extent hK links p.val p.property)) := by
  apply Quotient.sound
  refine CReal.Equiv_of_limit_of_equal ?_
    (CReal.convergesTo_ofQ'CauchySeq _ _) (CReal.convergesTo_ofQ'CauchySeq _ _)
  intro n
  exact CReal.ofQ'_equiv_of_eqv
    (insertedNormalizer_pair_pin w K extent links hl (X.seq n).val p.val (hX n))

theorem inverseCauchy_independent (p : (F).V) :
    ∀ n i, i ∈ slots extent links →
      QuaternionBlockIndependent i
        ((inverseCauchy hw0 hw1 K extent hK links hl
          (numeratorVector hw0 hw1 K extent hK links p.val p.property)).seq n).val := by
  intro n i hi
  exact approximateInverse_independent hw0 hw1 K extent hK links
    (numeratorVector hw0 hw1 K extent hK links p.val p.property)
    (insertedNormalizer_independent w K extent links p.val) n i hi

/-- Reproduction against every explicitly family-independent completed
representative, not merely against the constructed conditional output. -/
theorem conditionalUpdate_pairing_exterior (X : CauchyGNS G)
    (hX : ∀ n i, i ∈ slots extent links →
      QuaternionBlockIndependent i (X.seq n).val)
    (p : (F).V) :
    (F).cinnerCompl
      (toFullCompletion hw0 hw1 K extent hK links hl (Quotient.mk (cauchySetoid G) X))
      (conditionalUpdate hw0 hw1 K extent hK links hl p) =
    (F).cinnerCompl
      (toFullCompletion hw0 hw1 K extent hK links hl (Quotient.mk (cauchySetoid G) X))
      (embedV F p) := by
  let Y := inverseCauchy hw0 hw1 K extent hK links hl
    (numeratorVector hw0 hw1 K extent hK links p.val p.property)
  change (F).cinnerCompl
      (toFullCompletion hw0 hw1 K extent hK links hl (Quotient.mk (cauchySetoid G) X))
      (toFullCompletion hw0 hw1 K extent hK links hl (Quotient.mk (cauchySetoid G) Y)) = _
  have himage : normalizerCompletion hw0 hw1 K extent hK links hl
      (Quotient.mk (cauchySetoid G) Y) =
      embedV G (numeratorVector hw0 hw1 K extent hK links p.val p.property) :=
    normalizer_inverseState hw0 hw1 K extent hK links hl _
  rw [toFull_pair_of_independent hw0 hw1 K extent hK links hl X Y hX
    (inverseCauchy_independent hw0 hw1 K extent hK links hl p), himage]
  exact (toFull_test_of_independent hw0 hw1 K extent hK links hl X hX p).symm

/-- The actual block output reproduces its pairing with every second block
output against the ORIGINAL observable. This is the sharp projection seed. -/
theorem conditionalUpdate_pairing (p q : (F).V) :
    (F).cinnerCompl (conditionalUpdate hw0 hw1 K extent hK links hl p)
      (conditionalUpdate hw0 hw1 K extent hK links hl q) =
    (F).cinnerCompl (conditionalUpdate hw0 hw1 K extent hK links hl p)
      (embedV F q) :=
  conditionalUpdate_pairing_exterior hw0 hw1 K extent hK links hl
    (inverseCauchy hw0 hw1 K extent hK links hl
      (numeratorVector hw0 hw1 K extent hK links p.val p.property))
    (inverseCauchy_independent hw0 hw1 K extent hK links hl p) q

#print axioms toFull_norm_bound
#print axioms toFull_distance_bound
#print axioms toFullCauchy
#print axioms toFullNullModulus
#print axioms toFullCompletion
#print axioms toFullCompletion_embed
#print axioms conditionalRep
#print axioms conditionalUpdate
#print axioms toFull_pair_of_independent
#print axioms toFull_test_of_independent
#print axioms inverseCauchy_independent
#print axioms conditionalUpdate_pairing_exterior
#print axioms conditionalUpdate_pairing

end YMGap.Continuum.BF4ExactSlabBlockOriginalConditional
