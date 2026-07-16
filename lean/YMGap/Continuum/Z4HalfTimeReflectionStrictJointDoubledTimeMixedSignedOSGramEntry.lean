/-
# Signed recoding of translated strict OS Gram entries

The cofinal signed/strict comparison is now specialized to the pair
predicates which define literal entries of the strict Osterwalder--Schrader
Gram kernel.  Signed spatial descent then identifies every translated
diagonal entry with the corresponding oriented doubled-time mixed signed
entry.

This file performs only entrywise constructive-real composition.  It does not
assume or restate a covariance frontier, and it does not yet identify the
mixed signed entry with the finite polarized OS bilinear sum.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSRecoding

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSGramEntry

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

/-- A literal Gram entry of the time-translated strict cylinder is the
matching target signed-presentation entry. -/
theorem centralNormalizedTranslatedStrictJointGramLimit_equiv_signedTarget
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    CReal.Equiv
      (centralNormalizedStrictJointGramLimit
        coupling hcoupling hle
        (timeShiftCanonicalRoots_canonical
          (base := base) (shift := shift) (roots := roots) hroots)
        left right)
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (timeTranslatedStrictJointSignedPresentation
          base shift fixedStage roots
          (centralStrictJointPairPredicate roots.length left right)
          hroots)) := by
  have htranslated := timeShiftCanonicalRoots_canonical
    (base := base) (shift := shift) (roots := roots) hroots
  have hgram := centralNormalizedStrictJointGramLimit_equiv_centered
    hcoupling hle htranslated left right
  simp only [List.length_map] at hgram
  have hsigned :=
    couplingParametricTranslatedStrictJointCenteredLimit_equiv_signedTarget
      hcoupling hle hroots
      (centralStrictJointPairPredicate roots.length left right)
      (fixedStage := fixedStage) (shift := shift)
  exact CReal.Equiv.trans hgram hsigned

/-- Entrywise doubled-time descent: the translated Gram entry and the
oriented mixed signed entry are the same constructive real. -/
theorem centralNormalizedTranslatedStrictJointGramLimit_equiv_signedMixed
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (left right : List Bool) :
    CReal.Equiv
      (centralNormalizedStrictJointGramLimit
        coupling hcoupling hle
        (timeShiftCanonicalRoots_canonical
          (base := base) (shift := shift) (roots := roots) hroots)
        left right)
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (strictJointDoubledTimeMixedSignedPresentation
          base shift fixedStage roots
          (centralStrictJointPairPredicate roots.length left right)
          hstage hroots)) := by
  have htarget :=
    centralNormalizedTranslatedStrictJointGramLimit_equiv_signedTarget
      hcoupling hle hroots left right
      (fixedStage := fixedStage) (shift := shift)
  have hmixed := strictJointDoubledTime_signedSpatialValue_equiv
    hcoupling hle hstage hroots
    (centralStrictJointPairPredicate roots.length left right)
  exact CReal.Equiv.trans htarget hmixed

#print axioms centralNormalizedTranslatedStrictJointGramLimit_equiv_signedTarget
#print axioms centralNormalizedTranslatedStrictJointGramLimit_equiv_signedMixed

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSGramEntry
