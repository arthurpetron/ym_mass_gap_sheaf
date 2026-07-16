/-
# A derived uniform cap for translated strict reflection quadratics

Every literal strict Gram entry is dyadically close to a centered cylinder
probability.  Probability normalization and the explicit comparison
coefficient therefore give a stage-independent entry bound.  Finite
quadratic stability turns that into an exact coefficient-dependent cap for
every rational approximation of every Euclidean time translate.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSRecurrence

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSUniformCap

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.HalfPow
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSRecurrence
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem finiteJointQuadratic_zeroLaw_eqv
    {State : Type} (states : List State)
    (coefficient : State → Q') :
    finiteJointQuadratic states coefficient (fun _ _ => (0 : Q')) ≈ 0 := by
  unfold finiteJointQuadratic
  refine Q'.eqv_trans _
    (listQSum (fun _ : State => (0 : Q')) states) _ ?_
    (listQSum_zero states)
  apply listQSum_congr_on
  intro left _
  refine Q'.eqv_trans _
    (listQSum (fun _ : State => (0 : Q')) states) _ ?_
    (listQSum_zero states)
  apply listQSum_congr_on
  intro right _
  exact Q'.mul_zero_eqv (coefficient left * coefficient right)

private theorem add_neg_zero_eqv (value : Q') :
    value + (-(0 : Q')) ≈ value := by
  refine Q'.eqv_trans _ (value + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl value)
      (by decide : (-(0 : Q')) ≈ 0)
  · exact Q'.eqv_of_eq (Q'.add_zero' value)

private theorem finiteJointQuadratic_abs_le_of_entry_abs_le
    {State : Type} (states : List State)
    (coefficient : State → Q') (joint : State → State → Q')
    (bound : Q') (hbound : (0 : Q') ≤ bound)
    (hentry : ∀ left right, left ∈ states → right ∈ states →
      Q'.abs (joint left right) ≤ bound) :
    Q'.abs (finiteJointQuadratic states coefficient joint) ≤
      (coefficientL1 states coefficient * coefficientL1 states coefficient) *
        bound := by
  let zeroLaw : State → State → Q' := fun _ _ => 0
  have hfinite := finiteJointQuadratic_abs_sub_le_square
    states coefficient joint zeroLaw bound hbound
    (fun left right hleft hright => by
      have hdifference : joint left right + (-zeroLaw left right) ≈
          joint left right := add_neg_zero_eqv (joint left right)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.abs_eqv_congr hdifference))
        (hentry left right hleft hright))
  have hzero : finiteJointQuadratic states coefficient zeroLaw ≈ 0 := by
    exact finiteJointQuadratic_zeroLaw_eqv states coefficient
  have hdifference :
      finiteJointQuadratic states coefficient joint +
          (-finiteJointQuadratic states coefficient zeroLaw) ≈
        finiteJointQuadratic states coefficient joint := by
    refine Q'.eqv_trans _
      (finiteJointQuadratic states coefficient joint + (-(0 : Q'))) _ ?_ ?_
    · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.neg_eqv_congr _ _ hzero)
    · exact add_neg_zero_eqv _
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr (Q'.eqv_symm hdifference))) hfinite

/-- Uniform bound for one normalized strict Gram entry. -/
def strictJointGramUniformBound (rootCount : Nat) : Q' :=
  (1 : Q') + strictJointConditionalCenteredCoefficient
    (rootCount + rootCount)

theorem strictJointGramUniformBound_nonnegative (rootCount : Nat) :
    (0 : Q') ≤ strictJointGramUniformBound rootCount := by
  unfold strictJointGramUniformBound
  exact Q'.zero_le_add _ _ (by decide)
    (strictJointConditionalCenteredCoefficient_nonnegative _)

/-- Literal strict Gram entries are bounded uniformly in the common cutoff,
box size, and stage. -/
theorem centralNormalizedStrictJointGramSequence_le_uniformBound
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    centralNormalizedStrictJointGramSequence
        coupling hcoupling base roots left right stage ≤
      strictJointGramUniformBound roots.length := by
  let centered := couplingParametricStrictJointCenteredSequence
    coupling hcoupling base roots
    (centralStrictJointPairPredicate roots.length left right) stage
  let conditional := strictJointConditionalCenteredCoefficient
    (roots.length + roots.length)
  have hclose := centralNormalizedStrictJointGramSequence_to_centered_abs_le
    hcoupling hle hroots left right (stage := stage)
  have hentryToCentered :
      centralNormalizedStrictJointGramSequence
          coupling hcoupling base roots left right stage ≤
        centered + conditional * HalfPow.half ^ stage :=
    ExpNeg.le_add_of_abs_sub_le hclose
  have hcentered : centered ≤ (1 : Q') :=
    couplingParametricStrictJointCenteredSequence_le_one
      hcoupling base roots
      (centralStrictJointPairPredicate roots.length left right) stage
  have hhalf : HalfPow.half ^ stage ≤ (1 : Q') := by
    have h := ExpNeg.pow_half_antitone 0 stage
    simpa only [Nat.zero_add, Q'.pow_zero] using h
  have hconditional : (0 : Q') ≤ conditional :=
    strictJointConditionalCenteredCoefficient_nonnegative _
  have herror : conditional * HalfPow.half ^ stage ≤ conditional := by
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ conditional
      hhalf hconditional
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (Q'.mul_one_eqv conditional))
  exact Q'.le_trans' _ _ _ hentryToCentered
    (Q'.add_le_add hcentered herror)

/-- Coefficient-dependent uniform cap for a strict finite quadratic. -/
def strictJointQuadraticUniformBound
    (rootCount : Nat) (coefficient : List Bool → Q') : Q' :=
  (coefficientL1 (strictJointFingerprintSpace rootCount) coefficient *
      coefficientL1 (strictJointFingerprintSpace rootCount) coefficient) *
    strictJointGramUniformBound rootCount

theorem strictJointQuadraticUniformBound_nonnegative
    (rootCount : Nat) (coefficient : List Bool → Q') :
    (0 : Q') ≤ strictJointQuadraticUniformBound rootCount coefficient := by
  unfold strictJointQuadraticUniformBound
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (coefficientL1_nonnegative_local _ coefficient)
      (coefficientL1_nonnegative_local _ coefficient))
    (strictJointGramUniformBound_nonnegative rootCount)

theorem centralNormalizedStrictJointFixedQuadraticSequence_abs_le_uniformBound
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base stage : Nat} {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool → Q') :
    Q'.abs (centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling base roots coefficient stage) ≤
      strictJointQuadraticUniformBound roots.length coefficient := by
  unfold centralNormalizedStrictJointFixedQuadraticSequence
  exact finiteJointQuadratic_abs_le_of_entry_abs_le
    (strictJointFingerprintSpace roots.length) coefficient
    (fun left right => centralNormalizedStrictJointGramSequence
      coupling hcoupling base roots left right stage)
    (strictJointGramUniformBound roots.length)
    (strictJointGramUniformBound_nonnegative roots.length)
    (fun left right _ _ => by
      have hnonnegative := centralNormalizedStrictJointGramSequence_nonnegative
        hcoupling hroots left right stage
      rw [ExpNeg.abs_of_nonneg hnonnegative]
      exact centralNormalizedStrictJointGramSequence_le_uniformBound
        hcoupling hle hroots left right)

/-- Every rational approximation of every translated quadratic has the same
cap determined by the untranslated coefficient table and root count. -/
theorem timeTranslatedStrictJointReflectionQuadratic_approx_le_uniformBound
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (shift stage : Nat) :
    ((timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
        hcoupling hle).approx stage ≤
      strictJointQuadraticUniformBound
        vector.roots.length vector.coefficient := by
  have habs :=
    centralNormalizedStrictJointFixedQuadraticSequence_abs_le_uniformBound
      hcoupling hle
      (timeTranslateStrictJointCylinderVector shift vector).rootsCanonical
      (timeTranslateStrictJointCylinderVector shift vector).coefficient
      (stage := stage)
  have hvalue := Q'.le_trans' _ _ _
    (Q'.le_abs_self
      (((timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
        hcoupling hle).approx stage)) habs
  simpa only [StrictJointCylinderVector.reflectionQuadratic_approx,
    timeTranslateStrictJointCylinderVector_roots,
    timeTranslateStrictJointCylinderVector_coefficient,
    strictJointQuadraticUniformBound, List.length_map] using hvalue

/-- Constructive-real presentation of the same cap. -/
theorem timeTranslatedStrictJointReflectionQuadratic_leEv_uniformBound
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (shift : Nat) :
    CReal.leEv
      ((timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
        hcoupling hle)
      (CReal.ofQ'
        (strictJointQuadraticUniformBound
          vector.roots.length vector.coefficient)) :=
  CReal.leEv_le_ofQ'_of_approx_le
    (timeTranslatedStrictJointReflectionQuadratic_approx_le_uniformBound
      hcoupling hle vector shift)

#print axioms centralNormalizedStrictJointGramSequence_le_uniformBound
#print axioms centralNormalizedStrictJointFixedQuadraticSequence_abs_le_uniformBound
#print axioms timeTranslatedStrictJointReflectionQuadratic_approx_le_uniformBound
#print axioms timeTranslatedStrictJointReflectionQuadratic_leEv_uniformBound

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSUniformCap
