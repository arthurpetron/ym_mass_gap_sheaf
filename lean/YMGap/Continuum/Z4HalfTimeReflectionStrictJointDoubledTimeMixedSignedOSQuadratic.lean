/-
# Finite quadratic assembly of the doubled-time signed descent

The entrywise signed descent is assembled over the fixed Boolean fingerprint
space.  This gives a concrete constructive-real mixed signed quadratic and
identifies it with the translated strict reflection quadratic.  The only
remaining OS interface after this file is to identify the same mixed signed
quadratic with the direct polarized doubled-time OS bilinear.
-/

import YMGap.Continuum.Z4HalfTimeReflectionCenteredCRealBridge
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSGramEntry

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSQuadratic

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionCenteredCRealBridge
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSGramEntry
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

local infix:50 " ≈ " => Q'.eqv

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

/-- Finite CReal quadratic assembled from literal Gram-entry limits of the
time-translated strict cylinder. -/
def centralNormalizedTranslatedStrictJointGramQuadratic
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) : CReal :=
  listCRealSum
    (fun left => listCRealSum
      (fun right => CReal.mul
        (CReal.ofQ'
          (vector.coefficient left * vector.coefficient right))
        (centralNormalizedStrictJointGramLimit
          coupling hcoupling hle
          (timeShiftCanonicalRoots_canonical
            (base := base) (shift := shift) (roots := vector.roots)
            vector.rootsCanonical)
          left right))
      (strictJointFingerprintSpace vector.roots.length))
    (strictJointFingerprintSpace vector.roots.length)

/-- The oriented mixed signed quadratic, with the exact same fixed coefficient
table and state list as the translated strict Gram quadratic. -/
def strictJointDoubledTimeMixedSignedQuadratic
    (coupling : Q') (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift fixedStage : Nat)
    (hstage : shift + shift ≤ fixedStage)
    (vector : StrictJointCylinderVector base) : CReal :=
  listCRealSum
    (fun left => listCRealSum
      (fun right => CReal.mul
        (CReal.ofQ'
          (vector.coefficient left * vector.coefficient right))
        (couplingParametricSignedCenteredPresentationValueAtAnchor
          coupling hcoupling hle
          (strictJointDoubledTimeMixedSignedPresentation
            base shift fixedStage vector.roots
            (centralStrictJointPairPredicate
              vector.roots.length left right)
            hstage vector.rootsCanonical)))
      (strictJointFingerprintSpace vector.roots.length))
    (strictJointFingerprintSpace vector.roots.length)

/-- Every approximation of the translated Gram quadratic is the existing
fixed finite Gram quadratic for the translated cylinder. -/
theorem centralNormalizedTranslatedStrictJointGramQuadratic_approx_eqv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift stage : Nat}
    (vector : StrictJointCylinderVector base) :
    (centralNormalizedTranslatedStrictJointGramQuadratic
        coupling hcoupling hle shift vector).approx stage ≈
      centralNormalizedStrictJointFixedQuadraticSequence
        coupling hcoupling (base + shift)
        (timeTranslateStrictJointCylinderVector shift vector).roots
        (timeTranslateStrictJointCylinderVector shift vector).coefficient
        stage := by
  unfold centralNormalizedTranslatedStrictJointGramQuadratic
    centralNormalizedStrictJointFixedQuadraticSequence
    finiteJointQuadratic
  rw [listCRealSum_approx]
  simp only [timeTranslateStrictJointCylinderVector_roots,
    timeTranslateStrictJointCylinderVector_coefficient, List.length_map]
  apply listQSum_congr
  intro left
  rw [listCRealSum_approx]
  apply listQSum_congr
  intro right
  exact Q'.eqv_refl _

/-- The reflection quadratic of the translated cylinder is its finite CReal
Gram-entry assembly. -/
theorem timeTranslatedStrictJointReflectionQuadratic_equiv_gramQuadratic
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      ((timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
        hcoupling hle)
      (centralNormalizedTranslatedStrictJointGramQuadratic
        coupling hcoupling hle shift vector) := by
  apply CReal.Equiv_of_lifted_approx_equal
  intro stage
  apply YMGap.Constructive.TrigAdd.equiv_ofQ'_of_eqv
  exact Q'.eqv_symm
    (centralNormalizedTranslatedStrictJointGramQuadratic_approx_eqv
      hcoupling hle vector (shift := shift) (stage := stage))

/-- Finite entrywise descent assembles to equality of the translated Gram
quadratic and the oriented mixed signed quadratic. -/
theorem centralNormalizedTranslatedStrictJointGramQuadratic_equiv_mixedSigned
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      (centralNormalizedTranslatedStrictJointGramQuadratic
        coupling hcoupling hle shift vector)
      (strictJointDoubledTimeMixedSignedQuadratic
        coupling hcoupling hle shift fixedStage hstage vector) := by
  unfold centralNormalizedTranslatedStrictJointGramQuadratic
    strictJointDoubledTimeMixedSignedQuadratic
  apply listCRealSum_congr_on_local
  intro left hleft
  apply listCRealSum_congr_on_local
  intro right hright
  apply creal_mul_congr_right_local
  exact centralNormalizedTranslatedStrictJointGramLimit_equiv_signedMixed
    hcoupling hle hstage vector.rootsCanonical left right

/-- The translated reflection quadratic is exactly the assembled oriented
doubled-time mixed signed quadratic. -/
theorem timeTranslatedStrictJointReflectionQuadratic_equiv_mixedSigned
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift fixedStage : Nat}
    (hstage : shift + shift ≤ fixedStage)
    (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      ((timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
        hcoupling hle)
      (strictJointDoubledTimeMixedSignedQuadratic
        coupling hcoupling hle shift fixedStage hstage vector) :=
  CReal.Equiv.trans
    (timeTranslatedStrictJointReflectionQuadratic_equiv_gramQuadratic
      hcoupling hle shift vector)
    (centralNormalizedTranslatedStrictJointGramQuadratic_equiv_mixedSigned
      hcoupling hle hstage vector)

#print axioms centralNormalizedTranslatedStrictJointGramQuadratic_approx_eqv
#print axioms timeTranslatedStrictJointReflectionQuadratic_equiv_gramQuadratic
#print axioms centralNormalizedTranslatedStrictJointGramQuadratic_equiv_mixedSigned
#print axioms timeTranslatedStrictJointReflectionQuadratic_equiv_mixedSigned

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSQuadratic
