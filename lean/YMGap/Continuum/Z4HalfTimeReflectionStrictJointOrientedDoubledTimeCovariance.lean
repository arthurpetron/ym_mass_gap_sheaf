/-
# Oriented doubled-time covariance for two strict presentations

The heterogeneous signed entry descent identifies the common-box mixed form
with its oriented source signed chart.  The signed-spatial comparison
identifies that source chart with the simultaneously translated target chart.
Finally, the target chart is the zero-shift oriented chart of the two literal
time-translated presentations.  Combining the three exact identities proves
the full oriented doubled-time relation

  B(T_s x,T_s y) = B(S_(2s)x,T_(2s)y).

Symmetry of the left side then discharges the antisymmetric residual for all
even one-sided shifts.  No covariance or self-adjointness hypothesis is used.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeSignedEntry
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationSemanticDescent
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointPolarizedDoubledTimeIdentity

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCovariance

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionCenteredCRealBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCenteredAssembly
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeJointRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeSignedEntry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedSignedSpatialComparison
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointPolarizedDoubledTimeIdentity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationSemanticDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4SignedCenteredCylinderRecedingBoundary
open YMGap.Continuum.Z4SignedCenteredCornerBridge
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

/-! ## 1. The target chart is the zero-shift chart after translation -/

theorem orientedShiftZeroMixedCenteredRoots_eq_translated
    {base shift stage : Nat}
    {leftRoots rightRoots : List (List Nat)}
    (hright : ∀ root, root ∈ rightRoots →
      root ∈ canonicalSurfacePolymers base) :
    orientedDoubledTimeMixedCenteredRoots
        (base + shift) 0 stage
        (leftRoots.map (timeShiftCanonicalRoot shift base))
        (rightRoots.map (timeShiftCanonicalRoot shift base)) =
      orientedTimeTranslatedCenteredRoots
        base shift stage leftRoots rightRoots := by
  unfold orientedDoubledTimeMixedCenteredRoots
    orientedTimeTranslatedCenteredRoots
    strictJointDoubledTimeMixedCenteredLowerRoot
    strictJointDoubledTimeMixedCenteredUpperRoot
  simp only [List.map_map, Nat.add_zero, Nat.sub_zero]
  have hlower :
      List.map
          ((fun root => centralStrictLowerCenteredStageRoot
              (base + shift) stage root) ∘
            timeShiftCanonicalRoot shift base)
          leftRoots =
        List.map
          (fun root => centralStrictLowerCenteredStageRoot
            (base + shift) stage (timeShiftCanonicalRoot shift base root))
          leftRoots := by
    apply List.map_congr_left
    intro root hroot
    rfl
  have hupper :
      List.map
          ((fun root => centralStrictUpperCenteredStageRoot
              (base + shift) stage
              (timeShiftCanonicalRoot 0 (base + shift) root)) ∘
            timeShiftCanonicalRoot shift base)
          rightRoots =
        List.map
          (fun root => centralStrictUpperCenteredStageRoot
            (base + shift) stage (timeShiftCanonicalRoot shift base root))
          rightRoots := by
    apply List.map_congr_left
    intro root hroot
    simp only [Function.comp_apply]
    rw [timeShiftCanonicalRoot_zero
      (timeShiftCanonicalRoot_canonical (hright root hroot))]
  rw [hlower, hupper]

private theorem signedCenteredCylinderChart_ext_local
    {left right : SignedCenteredCylinderChart}
    (hcenter : left.center = right.center)
    (hradius : left.radius = right.radius)
    (hroots : left.roots = right.roots) : left = right := by
  obtain ⟨leftCenter, leftRadius, leftRoots, leftCanonical⟩ := left
  obtain ⟨rightCenter, rightRadius, rightRoots, rightCanonical⟩ := right
  simp only at hcenter hradius hroots
  subst rightCenter
  subst rightRadius
  subst rightRoots
  rfl

private theorem signedCenteredCylinderPresentation_ext_local
    {left right : SignedCenteredCylinderPresentation}
    (hchart : left.chart = right.chart)
    (hpredicate : left.predicate = right.predicate) : left = right := by
  obtain ⟨leftChart, leftPredicate⟩ := left
  obtain ⟨rightChart, rightPredicate⟩ := right
  simp only at hchart hpredicate
  subst rightChart
  subst rightPredicate
  rfl

theorem orientedShiftZeroMixedSignedPresentation_eq_translated
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (left right : StrictJointCylinderVector base)
    (predicate : List Bool → Bool) :
    orientedDoubledTimeMixedSignedPresentation
        (base + shift) 0 fixedStage
        (timeTranslateStrictJointCylinderVector shift left).roots
        (timeTranslateStrictJointCylinderVector shift right).roots
        predicate (Nat.zero_le fixedStage)
        (timeTranslateStrictJointCylinderVector shift left).rootsCanonical
        (timeTranslateStrictJointCylinderVector shift right).rootsCanonical =
      orientedTimeTranslatedSignedPresentation
        base shift fixedStage left.roots right.roots predicate
        hstage left.rootsCanonical right.rootsCanonical := by
  apply signedCenteredCylinderPresentation_ext_local
  · apply signedCenteredCylinderChart_ext_local
    · change signedNaturalCornerCenter
          (strictQueryBase (base + shift) + fixedStage) =
        signedNaturalCornerCenter
          ((strictQueryBase base + fixedStage) + shift)
      apply congrArg signedNaturalCornerCenter
      rw [strictQueryBase_add_shift]
      omega
    · change strictQueryBase (base + shift) + fixedStage =
        (strictQueryBase base + fixedStage) + shift
      rw [strictQueryBase_add_shift]
      omega
    · simp only [orientedDoubledTimeMixedSignedPresentation,
        orientedTimeTranslatedSignedPresentation,
        orientedDoubledTimeMixedSignedChart,
        orientedTimeTranslatedSignedChart,
        timeTranslateStrictJointCylinderVector_roots]
      exact orientedShiftZeroMixedCenteredRoots_eq_translated
        right.rootsCanonical
  · rfl

/-! ## 2. Finite target signed assembly -/

def orientedTimeTranslatedSignedBilinear
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (left right : StrictJointCylinderVector base) : CReal :=
  listCRealSum
    (fun leftBits => listCRealSum
      (fun rightBits => CReal.mul
        (CReal.ofQ' (left.coefficient leftBits * right.coefficient rightBits))
        (couplingParametricSignedCenteredPresentationValueAtAnchor
          coupling hcoupling hle
          (orientedTimeTranslatedSignedPresentation
            base shift fixedStage left.roots right.roots
            (centralStrictJointPairPredicate
              left.roots.length leftBits rightBits)
            hstage left.rootsCanonical right.rootsCanonical)))
      (strictJointFingerprintSpace right.roots.length))
    (strictJointFingerprintSpace left.roots.length)

private theorem creal_equiv_refl_local (value : CReal) :
    CReal.Equiv value value := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have hnonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  exact ⟨Q'.add_le_self_of_nonneg _ _ hnonnegative,
    Q'.add_le_self_of_nonneg _ _ hnonnegative⟩

private theorem creal_mul_congr_right_local
    {scalar left right : CReal} (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.mul scalar left) (CReal.mul scalar right) :=
  (CRealAlg.cmul_comm scalar left).trans
    ((CReal.mul_congr_left h).trans (CRealAlg.cmul_comm right scalar))

private theorem listCRealSum_congr_on_local
    {State : Type} {left right : State → CReal} :
    ∀ states : List State,
      (∀ state, state ∈ states → CReal.Equiv (left state) (right state)) →
      CReal.Equiv (listCRealSum left states) (listCRealSum right states)
  | [], _ => creal_equiv_refl_local CReal.czero
  | head :: tail, h => by
      have hhead : CReal.Equiv (left head) (right head) :=
        h head List.mem_cons_self
      have htail : CReal.Equiv
          (listCRealSum left tail) (listCRealSum right tail) :=
        listCRealSum_congr_on_local tail
          (fun state hstate => h state (List.mem_cons_of_mem head hstate))
      exact CReal.Equiv.trans
        (CReal.add_congr_left hhead)
        (CReal.add_congr_right htail)

/-- The simultaneously translated target signed assembly equals the oriented
mixed source signed assembly by the derived signed-spatial comparison. -/
theorem orientedTimeTranslatedSignedBilinear_equiv_mixedSigned
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (orientedTimeTranslatedSignedBilinear
        coupling hcoupling hle hstage left right)
      (orientedDoubledTimeMixedSignedBilinear
        coupling hcoupling hle hstage left right) := by
  unfold orientedTimeTranslatedSignedBilinear
    orientedDoubledTimeMixedSignedBilinear
  apply listCRealSum_congr_on_local
  intro leftBits hleftBits
  apply listCRealSum_congr_on_local
  intro rightBits hrightBits
  apply creal_mul_congr_right_local
  exact orientedSignedSpatialValue_equiv
    hcoupling hle hstage left.rootsCanonical right.rootsCanonical
    (centralStrictJointPairPredicate
      left.roots.length leftBits rightBits)

/-- After translating both inputs, the zero-shift mixed signed assembly is
literally the target signed assembly, up to constructive-real reflexivity. -/
theorem orientedShiftZeroMixedSignedBilinear_equiv_translated
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (hzero : 0 + 0 ≤ fixedStage)
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (orientedDoubledTimeMixedSignedBilinear
        coupling hcoupling hle hzero
        (timeTranslateStrictJointCylinderVector shift left)
        (timeTranslateStrictJointCylinderVector shift right))
      (orientedTimeTranslatedSignedBilinear
        coupling hcoupling hle hstage left right) := by
  unfold orientedDoubledTimeMixedSignedBilinear
    orientedTimeTranslatedSignedBilinear
  simp only [timeTranslateStrictJointCylinderVector_coefficient,
    timeTranslateStrictJointCylinderVector_roots_length]
  apply listCRealSum_congr_on_local
  intro leftBits hleftBits
  apply listCRealSum_congr_on_local
  intro rightBits hrightBits
  apply creal_mul_congr_right_local
  rw [orientedShiftZeroMixedSignedPresentation_eq_translated
    hstage left right
    (centralStrictJointPairPredicate
      left.roots.length leftBits rightBits)]
  exact creal_equiv_refl_local _

/-! ## 3. Terminal oriented covariance and the even-shift residual -/

/-- Full oriented doubled-time identity for two unrelated strict cylinder
presentations. -/
theorem orientedDoubledTimeCovariance
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (timeTranslateStrictJointCylinderVector shift left)
        (timeTranslateStrictJointCylinderVector shift right))
      (orientedDoubledTimeReflectionBilinear
        hcoupling hle shift left right) := by
  let translatedLeft := timeTranslateStrictJointCylinderVector shift left
  let translatedRight := timeTranslateStrictJointCylinderVector shift right
  have hzero : 0 + 0 ≤ shift + shift := by omega
  have hraw := orientedDoubledTimeReflectionBilinear_equiv_mixedSigned
    hcoupling hle hzero translatedLeft translatedRight
  have hsource : orientedDoubledTimeSource 0 translatedLeft =
      translatedLeft := by
    simpa only [orientedDoubledTimeSource, Nat.add_zero] using
      (boxTransportStrictJointCylinderVector_refl translatedLeft)
  have htarget : orientedDoubledTimeTarget 0 translatedRight =
      translatedRight := by
    simpa only [orientedDoubledTimeTarget, Nat.add_zero] using
      (timeTranslateStrictJointCylinderVector_zero translatedRight)
  unfold orientedDoubledTimeReflectionBilinear at hraw
  rw [hsource, htarget] at hraw
  exact CReal.Equiv.trans hraw
    (CReal.Equiv.trans
      (orientedShiftZeroMixedSignedBilinear_equiv_translated
        hcoupling hle (Nat.le_refl (shift + shift)) hzero left right)
      (CReal.Equiv.trans
        (orientedTimeTranslatedSignedBilinear_equiv_mixedSigned
          hcoupling hle (Nat.le_refl (shift + shift)) left right)
        (CReal.Equiv.symm
          (orientedDoubledTimeReflectionBilinear_equiv_mixedSigned
            hcoupling hle (Nat.le_refl (shift + shift)) left right))))

/-- The antisymmetric one-sided covariance residual is discharged for every
even shift. -/
theorem strictJointEvenOneSidedTimeCovariance_derived
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) :
    StrictJointOneSidedTimeCovariance
      hcoupling hle (shift + shift) left right := by
  have hleft : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (timeTranslateStrictJointCylinderVector shift left)
        (timeTranslateStrictJointCylinderVector shift right))
      (strictJointOneSidedTimeCross hcoupling hle
        (shift + shift) left right) := by
    simpa only [strictJointOneSidedTimeCross,
      orientedDoubledTimeReflectionBilinear,
      orientedDoubledTimeSource, orientedDoubledTimeTarget] using
      (orientedDoubledTimeCovariance
        hcoupling hle shift left right)
  have hright : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (timeTranslateStrictJointCylinderVector shift right)
        (timeTranslateStrictJointCylinderVector shift left))
      (strictJointOneSidedTimeCross hcoupling hle
        (shift + shift) right left) := by
    simpa only [strictJointOneSidedTimeCross,
      orientedDoubledTimeReflectionBilinear,
      orientedDoubledTimeSource, orientedDoubledTimeTarget] using
      (orientedDoubledTimeCovariance
        hcoupling hle shift right left)
  have hsymm := StrictJointCylinderVector.reflectionBilinear_symm
    hcoupling hle
    (timeTranslateStrictJointCylinderVector shift left)
    (timeTranslateStrictJointCylinderVector shift right)
  exact CReal.Equiv.trans (CReal.Equiv.symm hleft)
    (CReal.Equiv.trans hsymm hright)

#print axioms orientedShiftZeroMixedCenteredRoots_eq_translated
#print axioms orientedShiftZeroMixedSignedPresentation_eq_translated
#print axioms orientedTimeTranslatedSignedBilinear_equiv_mixedSigned
#print axioms orientedShiftZeroMixedSignedBilinear_equiv_translated
#print axioms orientedDoubledTimeCovariance
#print axioms strictJointEvenOneSidedTimeCovariance_derived

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointOrientedDoubledTimeCovariance
