/-
# Spatial covariance of the SAME chronological Wilson operators

Translate the actual ordered loop in every multiplication instruction and
leave coefficients and discrete times unchanged. The literal multiplier pin,
linearity and time commutation prove intertwining on EVERY vector of the
existing completed Wilson carrier, not just on the vacuum. The reversed
adjoint action and the original mixed/connected scalars obey the same law.

The original signed-window compiler is a consumer: its translated program
still realizes the literally translated source window. Its squared cap and
input tolerance are unchanged. This is positive diagonal lattice covariance
at the fixed small nome, not a full signed spatial action, continuum covariance,
canonical OS reconstruction, changing-spacing bound or physical mass theorem.
Equality on the vacuum is not used to identify arbitrary operator presentations.
-/

import YMGap.Continuum.BF4WilsonDiagonalTranslationMultiplierSyntax
import YMGap.Continuum.BF4WilsonDiagonalTranslationLinear
import YMGap.Continuum.BF4WilsonChronologicalOperator

namespace YMGap.Continuum.BF4WilsonChronologicalSpatialCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonDiagonalTranslationSyntax
open YMGap.Continuum.BF4WilsonDiagonalTranslationMultiplierSyntax
open YMGap.Continuum.BF4WilsonDiagonalTranslationLinear
open YMGap.Continuum.BF4WilsonSpatialUnionDiagonalTranslation
open YMGap.Continuum.BF4WilsonChronologicalProgram
open YMGap.Continuum.BF4WilsonChronologicalOperator
open YMGap.Continuum.BF4WilsonWindowRealization
open YMGap.Continuum.BF4WilsonWindowOperatorPins (embedWindow)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow (WindowExpression Within)
open YMGap.Continuum.BF4WilsonSpatialUnion (distSq)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap (completedCenteredScalar)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Computed syntax transformation; no new program representation is selected. -/
def translateProgram {base : Nat} (s : Nat) : Program base → Program (base+2*s)
  | .vacuum => .vacuum
  | .zero => .zero
  | .add p q => .add (translateProgram s p) (translateProgram s q)
  | .smul c p => .smul c (translateProgram s p)
  | .time n p => .time n (translateProgram s p)
  | .multiply L spin p => .multiply (translatedLoop s L) spin (translateProgram s p)

theorem squaredCap_translate {base : Nat} (s : Nat) (p : Program base) :
    squaredCap (translateProgram s p) = squaredCap p := by
  induction p <;> simp only [translateProgram, squaredCap, *]

theorem inputTolerance_translate {base : Nat} (s : Nat) (p : Program base) (epsilon : Q') :
    inputTolerance (translateProgram s p) epsilon = inputTolerance p epsilon := by
  unfold inputTolerance
  simp only [squaredCap_translate]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "R" => completedTranslation hw0 hw1 hsmall hd hs
local notation "M" => completedMultiply hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs

/-- Intertwining of actual bounded observables on arbitrary completed inputs. -/
theorem completedTranslation_multiply {base : Nat} (s : Nat) (L : SourceLoop base)
    (spin : Nat) (x : V) : R s (M L spin x) = M (translatedLoop s L) spin (R s x) := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  refine ⟨CRealSeminormCompletion.SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun k => ?_)⟩
  change Equiv (distSq hw0 hw1 hsmall hd hs (stageTranslate s (multiplyStage L spin (X.seq k)))
    (multiplyStage (translatedLoop s L) spin (stageTranslate s (X.seq k)))) czero
  rw [stageTranslate_multiplyStage]
  exact distance_refl hw0 hw1 hsmall hd hs _

theorem act_translate {base : Nat} (s : Nat) (p : Program base) (x : V) :
    R s (act hw0 hw1 hsmall hd hs p x) =
      act hw0 hw1 hsmall hd hs (translateProgram s p) (R s x) := by
  induction p with
  | vacuum => rfl
  | zero => exact completedTranslation_zero_vector hw0 hw1 hsmall hd hs s
  | add p q hp hq =>
      simp only [act, translateProgram, completedTranslation_add_vectors, hp, hq]
  | smul c p hp => simp only [act, translateProgram, completedTranslation_smul, hp]
  | time n p hp => simp only [act, translateProgram, completedTranslation_time, hp]
  | multiply L spin p hp => simp only [act, translateProgram, completedTranslation_multiply, hp]

theorem adjointAct_translate {base : Nat} (s : Nat) (p : Program base) (x : V) :
    R s (adjointAct hw0 hw1 hsmall hd hs p x) =
      adjointAct hw0 hw1 hsmall hd hs (translateProgram s p) (R s x) := by
  induction p generalizing x with
  | vacuum => rfl
  | zero => exact completedTranslation_zero_vector hw0 hw1 hsmall hd hs s
  | add p q hp hq =>
      simp only [adjointAct, translateProgram, completedTranslation_add_vectors, hp, hq]
  | smul c p hp => simp only [adjointAct, translateProgram, completedTranslation_smul, hp]
  | time n p hp => simp only [adjointAct, translateProgram, hp, completedTranslation_time]
  | multiply L spin p hp =>
      simp only [adjointAct, translateProgram, hp, completedTranslation_multiply]

theorem evaluate_translate {base : Nat} (s : Nat) (p : Program base) :
    R s (evaluate hw0 hw1 hsmall hd hs p) =
      evaluate hw0 hw1 hsmall hd hs (translateProgram s p) := by
  rw [← act_unit, act_translate, completedTranslation_unit, act_unit]

/-- The original mixed matrix element, not an unrelated model scalar. -/
theorem matrixElement_translate {base : Nat} (s : Nat) (p : Program base) (x y : V) :
    B (act hw0 hw1 hsmall hd hs (translateProgram s p) (R s x)) (R s y) =
      B (act hw0 hw1 hsmall hd hs p x) y := by
  rw [← act_translate, completedInner_translate]

theorem connectedPrograms_translate {left right : Nat} (s n : Nat)
    (p : Program left) (q : Program right) :
    completedCenteredScalar hw0 hw1 hsmall hd hs n
      (evaluate hw0 hw1 hsmall hd hs (translateProgram s p))
      (evaluate hw0 hw1 hsmall hd hs (translateProgram s q)) =
      completedCenteredScalar hw0 hw1 hsmall hd hs n
        (evaluate hw0 hw1 hsmall hd hs p) (evaluate hw0 hw1 hsmall hd hs q) := by
  rw [← evaluate_translate, ← evaluate_translate, completedCenteredScalar_translate]

/-- The SAME original embedded source window, with its actual spatial edges shifted. -/
theorem completedTranslation_embedWindow {base : Nat} (hb : 0 < base) (s H : Nat)
    (e : WindowExpression base) (he : Within H e) :
    R s (embedWindow hw0 hw1 hsmall hd hs hb H e he) =
      embedWindow hw0 hw1 hsmall hd hs (by omega) H (translateExpression s e)
        ((translate_within s H e).mpr he) := rfl

/-- Translation of compiled code realizes the literal translated original window. -/
theorem translatedCompileWindow_pin {base : Nat} (hb : 0 < base) (s H : Nat)
    (e : WindowExpression base) (he : Within H e) :
    evaluate hw0 hw1 hsmall hd hs (translateProgram s (compileWindow H e)) =
      embedWindow hw0 hw1 hsmall hd hs (by omega) H (translateExpression s e)
        ((translate_within s H e).mpr he) := by
  rw [← evaluate_translate, compileWindow_pin hw0 hw1 hsmall hd hs hb H e he,
    completedTranslation_embedWindow]

#print axioms translateProgram
#print axioms squaredCap_translate
#print axioms inputTolerance_translate
#print axioms completedTranslation_multiply
#print axioms act_translate
#print axioms adjointAct_translate
#print axioms evaluate_translate
#print axioms matrixElement_translate
#print axioms connectedPrograms_translate
#print axioms completedTranslation_embedWindow
#print axioms translatedCompileWindow_pin

end YMGap.Continuum.BF4WilsonChronologicalSpatialCovariance
