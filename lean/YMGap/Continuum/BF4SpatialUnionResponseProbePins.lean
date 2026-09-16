/-
# Actual lag-three probe pins between the two finite-action exhaustions

The current union probe is literally the existing centralStage.value.
Its lower and upper chart insertions have the same ordered plaquette words
as the translated old response probes. Prefix equivalence retains rational
coefficients, term order and all actual quaternion coordinates; only trailing
zero padding and singleton presentation bookkeeping are removed.

The current joint chart is UPPER times LOWER. That order is retained in the
source joint pin; swapping to the old connected numerator's LOWER times UPPER
requires polynomial/Haar commutativity, not a termwise-prefix claim.
These are observable identities, not equality of the selected-chain and full
slab actions, a response lower bound, or a continuum assertion.
-/

import YMGap.Continuum.BF4SpatialUnionResponseGeometry
import YMGap.Continuum.BF4SpatialUnionExcitation
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedProbeControl
import YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix

namespace YMGap.Continuum.BF4SpatialUnionResponseProbePins

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal (originFace)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra (lower upper)
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit (unitSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
  (physicalTime unit physicalTime_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (placedSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlacedProbeControl
  (chartProbe chartProbe_local chartLinks spanCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedProbeControl
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionBlockLocality (BlockLocal)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (LinkLocal)
open YMGap.Continuum.QuaternionHaarPolynomialInterval (Interval)
open YMGap.Continuum.SU2QuaternionHeadSubstitutionPrefix
  (prefix_symm prefix_mul_one prefix_one_mul)
open YMGap.Continuum.BF4SpatialUnionResponseGeometry

/-- The existing excitation's uncentered original observable, not a new probe. -/
def centralProbe : PhysicalSpan 1 := BF4SpatialUnionExcitation.centralStage.value

theorem centralProbe_radius : radius centralProbe.val = 0 := rfl

def currentLower (s : Nat) : RatPoly := lowerProbe 1 (s+1) 0 3 (s+1) centralProbe

def currentUpper (s : Nat) : RatPoly := upperProbe 1 (s+1) 0 3 (s+1) centralProbe

/-- The actual single-observable cap; the generic unit-presentation cap is not paid. -/
def singleCap : Q' := spanCap centralProbe.val

def currentLower_interval (s : Nat) :
    Interval (boundaryCompleteSlabLinks (targetExtent s)).length (currentLower s) singleCap :=
  lowerProbe_interval 1 (s+1) 0 3 (s+1) centralProbe (by decide)

def currentUpper_interval (s : Nat) :
    Interval (boundaryCompleteSlabLinks (targetExtent s)).length (currentUpper s) singleCap :=
  upperProbe_interval 1 (s+1) 0 3 (s+1) centralProbe (by decide)

private theorem prefix_one_smul (blocks : Nat) : ∀ p : RatPoly,
    QuaternionPrefixPolynomialEqv blocks (polySmul 1 p) p
  | [] => .nil
  | term::rest => .cons ⟨Q'.one_mul_eqv term.2, fun _ _ => rfl⟩
      (prefix_one_smul blocks rest)

private theorem singleton_sum (blocks : Nat) (p : RatPoly) :
    QuaternionPrefixPolynomialEqv blocks (polyAdd (polySmul 1 p) polyZero) p := by
  simpa only [polyAdd, polyZero, List.append_nil] using prefix_one_smul blocks p

private theorem singleton_ledger (blocks : Nat) (p : RatPoly) :
    QuaternionPrefixPolynomialEqv blocks
      (polyAdd (polySmul 1
        (polyMul (polyAdd (polySmul 1 p) polyZero) polyOne)) polyZero) p :=
  (singleton_sum blocks _).trans
    (((singleton_sum blocks p).mul (.refl blocks polyOne)).trans
      (prefix_mul_one blocks p))

attribute [local irreducible] correctedSlabPlaquettePolynomial

/-- Stronger term-order-preserving version of the existing coefficient pin. -/
theorem placedSpan_face_prefix (extent time : Nat) (p : Z4Plaq) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks extent).length
      (placedSpan extent time (facePresentation p))
      (faceCharacter extent (timeShiftPlaquette time p)) := by
  change QuaternionPrefixPolynomialEqv _
    (polyAdd (polySmul 1
      (polyMul (polyAdd (polySmul 1
        (sweptCharacter extent 0 (timeShiftPlaquette time p) 1)) polyZero) polyOne)) polyZero) _
  have hc : sweptCharacter extent 0 (timeShiftPlaquette time p) 1 =
      faceCharacter extent (timeShiftPlaquette time p) := by
    simp only [sweptCharacter, if_neg (not_swept_zero _), faceCharacter]
  rw [hc]
  exact singleton_ledger _ _

private theorem placedSpan_unit_prefix (extent time : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks extent).length
      (placedSpan extent time unitSpan) polyOne := by
  change QuaternionPrefixPolynomialEqv _ (polyAdd (polySmul 1 polyOne) polyZero) polyOne
  exact singleton_sum _ _

/-- Exact current lower endpoint equals the translated OLD lower endpoint. -/
theorem lower_face_pin (s : Nat) :
    timeShiftPlaquette (paddedWidth 1 (s+1)+1+(s+1))
      (shiftFace (s+2) 0 originFace) = shiftFace 1 (2*s+7) (sliceFace s 0) := by
  simp only [timeShiftPlaquette, timeShiftVertex, shiftFace, shiftVertex,
    originFace, sliceFace, Prod.mk.injEq, Nat.zero_add, Nat.add_zero]
  unfold paddedWidth
  repeat' constructor
  all_goals omega

/-- The upper endpoint is THREE physical time steps above the lower one. -/
theorem upper_face_pin (s : Nat) :
    timeShiftPlaquette (paddedWidth 1 (s+1)+1+(s+1)+3)
      (shiftFace (s+2) 0 originFace) = shiftFace 1 (2*s+7) (sliceFace s 3) := by
  simp only [timeShiftPlaquette, timeShiftVertex, shiftFace, shiftVertex,
    originFace, sliceFace, Prod.mk.injEq, Nat.zero_add, Nat.add_zero]
  unfold paddedWidth
  repeat' constructor
  all_goals omega

theorem currentLower_character_prefix (s : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (targetExtent s)).length
      (currentLower s)
      (faceCharacter (targetExtent s) (shiftFace 1 (2*s+7) (sliceFace s 0))) := by
  change QuaternionPrefixPolynomialEqv _
    (placedSpan (targetExtent s) (paddedWidth 1 (s+1)+1+(s+1))
      (facePresentation (shiftFace (s+2) 0 originFace))) _
  have h := placedSpan_face_prefix (targetExtent s)
    (paddedWidth 1 (s+1)+1+(s+1)) (shiftFace (s+2) 0 originFace)
  rw [lower_face_pin] at h
  exact h

theorem currentUpper_character_prefix (s : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (targetExtent s)).length
      (currentUpper s)
      (faceCharacter (targetExtent s) (shiftFace 1 (2*s+7) (sliceFace s 3))) := by
  change QuaternionPrefixPolynomialEqv _
    (placedSpan (targetExtent s) (paddedWidth 1 (s+1)+1+(s+1)+3)
      (facePresentation (shiftFace (s+2) 0 originFace))) _
  have h := placedSpan_face_prefix (targetExtent s)
    (paddedWidth 1 (s+1)+1+(s+1)+3) (shiftFace (s+2) 0 originFace)
  rw [upper_face_pin] at h
  exact h

/-- The complete old lower polynomial is transported to the actual current one. -/
theorem lower_translation_prefix (s : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (targetExtent s)).length
      ((responsePlacement s).embedding.polynomial (lower (enlarge s shiftedProbe)))
      (currentLower s) := by
  have h := (responsePlacement s).character_pin (slice_physical s ⟨0, by decide⟩) 1
  rw [lower_shifted_probe_pin]
  exact h.trans (prefix_symm (currentLower_character_prefix s))

/-- The old REFLECTED upper polynomial is transported, not independently replaced. -/
theorem upper_translation_prefix (s : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (targetExtent s)).length
      ((responsePlacement s).embedding.polynomial (upper (enlarge s shiftedProbe)))
      (currentUpper s) := by
  have h := (responsePlacement s).character_pin (slice_physical s ⟨3, by decide⟩) 1
  rw [upper_shifted_probe_pin]
  exact h.trans (prefix_symm (currentUpper_character_prefix s))

/-- The source product retains the actual chart's UPPER-then-LOWER order. -/
theorem joint_translation_prefix (s : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (targetExtent s)).length
      ((responsePlacement s).embedding.polynomial
        (polyMul (upper (enlarge s shiftedProbe)) (lower (enlarge s shiftedProbe))))
      (chartProbe 1 (s+1) 3 (s+1) centralProbe (physicalTime 3 centralProbe)) := by
  rw [(responsePlacement s).embedding.polynomial_mul]
  change QuaternionPrefixPolynomialEqv _ _
    (chartProbe 1 (s+1) (0+3) (s+1) centralProbe (physicalTime 3 centralProbe))
  rw [chartProbe_separated 1 (s+1) 0 3 (s+1) centralProbe centralProbe (by decide)]
  exact (upper_translation_prefix s).mul (lower_translation_prefix s)

private theorem currentLower_unit_prefix (s : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (targetExtent s)).length
      (lowerProbe 1 (s+1) 0 3 (s+1) (unit 1)) polyOne := by
  change QuaternionPrefixPolynomialEqv _
    (placedSpan (targetExtent s) (paddedWidth 1 (s+1)+1+(s+1)) unitSpan) polyOne
  exact placedSpan_unit_prefix _ _

private theorem currentUpper_unit_prefix (s : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (targetExtent s)).length
      (upperProbe 1 (s+1) 0 3 (s+1) (unit 1)) polyOne := by
  change QuaternionPrefixPolynomialEqv _
    (placedSpan (targetExtent s) (paddedWidth 1 (s+1)+1+(s+1)+3) unitSpan) polyOne
  exact placedSpan_unit_prefix _ _

/-- The actual first unit-marginal chart has precisely the upper probe insertion. -/
theorem upper_marginal_prefix (s : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (targetExtent s)).length
      (chartProbe 1 (s+1) 3 (s+1) centralProbe (unit 1)) (currentUpper s) := by
  rw [← physicalTime_unit 1 3]
  change QuaternionPrefixPolynomialEqv _
    (chartProbe 1 (s+1) (0+3) (s+1) centralProbe (physicalTime 3 (unit 1))) _
  rw [chartProbe_separated 1 (s+1) 0 3 (s+1) centralProbe (unit 1) (by decide)]
  exact ((QuaternionPrefixPolynomialEqv.refl _ _).mul
    (currentLower_unit_prefix s)).trans (prefix_mul_one _ _)

/-- The second unit-marginal chart has precisely the lower probe insertion. -/
theorem lower_marginal_prefix (s : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (targetExtent s)).length
      (chartProbe 1 (s+1) 3 (s+1) (unit 1) (physicalTime 3 centralProbe))
      (currentLower s) := by
  change QuaternionPrefixPolynomialEqv _
    (chartProbe 1 (s+1) (0+3) (s+1) (unit 1) (physicalTime 3 centralProbe)) _
  rw [chartProbe_separated 1 (s+1) 0 3 (s+1) (unit 1) centralProbe (by decide)]
  exact ((currentUpper_unit_prefix s).mul
    (QuaternionPrefixPolynomialEqv.refl _ _)).trans (prefix_one_mul _ _)

private theorem blockLocal_of_prefix {blocks : Nat} {allowed : Nat → Prop}
    {p q : RatPoly} (h : QuaternionPrefixPolynomialEqv blocks p q)
    (hp : BlockLocal blocks allowed p) : BlockLocal blocks allowed q := by
  revert hp
  induction h with
  | nil =>
      intro _ term ht
      exact False.elim (List.not_mem_nil ht)
  | cons ht _ ih =>
      intro hp term hm block hb hn component hc
      rcases List.mem_cons.mp hm with rfl | hm
      · rw [← ht.exponent (4*block+component) (by omega)]
        exact hp _ List.mem_cons_self block hb hn component hc
      · exact ih (fun t ht => hp t (List.mem_cons_of_mem _ ht))
          term hm block hb hn component hc

/-- Exact exponent transport from the original unit-marginal chart locality. -/
theorem currentUpper_local (s : Nat) :
    LinkLocal (targetExtent s) (chartLinks 1 (s+1) 3 (s+1)) (currentUpper s) :=
  blockLocal_of_prefix (upper_marginal_prefix s)
    (chartProbe_local 1 (s+1) 3 (s+1) centralProbe (unit 1) (by decide) (by decide))

theorem currentLower_local (s : Nat) :
    LinkLocal (targetExtent s) (chartLinks 1 (s+1) 3 (s+1)) (currentLower s) :=
  blockLocal_of_prefix (lower_marginal_prefix s)
    (chartProbe_local 1 (s+1) 3 (s+1) (unit 1) (physicalTime 3 centralProbe)
      (by decide) (by decide))

/-- Product cap c*c, retaining the same single-probe cap on both factors. -/
def joint_interval (s : Nat) :
    Interval (boundaryCompleteSlabLinks (targetExtent s)).length
      (chartProbe 1 (s+1) 3 (s+1) centralProbe (physicalTime 3 centralProbe))
      (singleCap*singleCap) := by
  change Interval _ (chartProbe 1 (s+1) (0+3) (s+1) centralProbe
    (physicalTime 3 centralProbe)) _
  rw [chartProbe_separated 1 (s+1) 0 3 (s+1) centralProbe centralProbe (by decide)]
  exact (currentUpper_interval s).mul (currentLower_interval s)

theorem joint_local (s : Nat) :
    LinkLocal (targetExtent s) (chartLinks 1 (s+1) 3 (s+1))
      (chartProbe 1 (s+1) 3 (s+1) centralProbe (physicalTime 3 centralProbe)) :=
  chartProbe_local 1 (s+1) 3 (s+1) centralProbe (physicalTime 3 centralProbe)
    (by decide) (by decide)

end YMGap.Continuum.BF4SpatialUnionResponseProbePins

#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.centralProbe
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.centralProbe_radius
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.currentLower
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.currentUpper
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.singleCap
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.currentLower_interval
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.currentUpper_interval
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.placedSpan_face_prefix
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.lower_face_pin
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.upper_face_pin
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.currentLower_character_prefix
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.currentUpper_character_prefix
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.lower_translation_prefix
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.upper_translation_prefix
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.joint_translation_prefix
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.upper_marginal_prefix
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.lower_marginal_prefix
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.currentUpper_local
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.currentLower_local
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.joint_interval
#print axioms YMGap.Continuum.BF4SpatialUnionResponseProbePins.joint_local
