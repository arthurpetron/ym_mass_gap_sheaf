/-
# Finite chronological programs in the SAME completed Wilson operators

A program is explicit data built from the existing vacuum, zero, addition,
rational scaling, discrete time and bounded time-zero loop multiplication.
A decreasing-offset word has an exact program: insert its latest character
after realizing the earlier factors, then advance by the remaining distance
to the supplied reflection center. All time advances are natural numbers.

Sorting preserves the original scalar source polynomial. Its already proved
descent identifies the output with the original embedded word, with no new
operator assumption and no multiplication of arbitrary positive-time states.
General finite signed windows are the next consumer, not an asserted full
gauge-observable or continuum-QFT completeness theorem.
-/

import YMGap.Continuum.BF4WilsonTimedWordOrder
import YMGap.Continuum.BF4WilsonWindowOperatorPins

namespace YMGap.Continuum.BF4WilsonChronologicalProgram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4WilsonTimedWord
open YMGap.Continuum.BF4WilsonTimedWordOrder
open YMGap.Continuum.BF4WilsonWindowOperatorPins
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionLinear (completedAdd completedSmul)
open YMGap.Continuum.BF4WilsonSpatialUnionPosdef (completedZero)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier (completedMultiply)
open YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity (embedWindow_eq_of_source_identity)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- A finite witness, not an existentially selected observable representation. -/
inductive Program (base : Nat) : Type where
  | vacuum : Program base
  | zero : Program base
  | add : Program base → Program base → Program base
  | smul : Q' → Program base → Program base
  | time : Nat → Program base → Program base
  | multiply : SourceLoop base → Nat → Program base → Program base

def orderedProgram {base : Nat} (H : Nat) : List (TimedLoop base) → Program base
  | [] => .vacuum
  | a :: rest => .time (H-a.offset)
      (.multiply a.loop a.spin (orderedProgram a.offset rest))

def wordProgram {base : Nat} (H : Nat) (word : List (TimedLoop base)) : Program base :=
  orderedProgram H (orderWord word)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs

/-- Every constructor acts by the SAME already constructed completed operation. -/
def evaluate {base : Nat} : Program base → V
  | .vacuum => completedUnit hw0 hw1 hsmall hd hs
  | .zero => completedZero hw0 hw1 hsmall hd hs
  | .add p q => completedAdd hw0 hw1 hsmall hd hs
      (evaluate p) (evaluate q)
  | .smul c p => completedSmul hw0 hw1 hsmall hd hs c (evaluate p)
  | .time n p => completedTime hw0 hw1 hsmall hd hs n (evaluate p)
  | .multiply L spin p => completedMultiply hw0 hw1 hsmall hd hs L spin
      (evaluate p)

/-- Decreasing offsets supply every recursive room guard; no truncated-time alias is used. -/
theorem orderedProgram_pin {base : Nat} (hb : 0 < base)
    (word : List (TimedLoop base)) (hdsc : Descending word) (H : Nat) (hword : WordWithin H word) :
    evaluate hw0 hw1 hsmall hd hs (orderedProgram H word) =
      embedWindow hw0 hw1 hsmall hd hs hb H (wordExpression word)
        ((wordExpression_within H word).mpr hword) := by
  induction word generalizing H with
  | nil => exact (embedWindow_one hw0 hw1 hsmall hd hs hb H).symm
  | cons a rest ih =>
      have ha : a.offset ≤ H := ((wordWithin_cons H a rest).mp hword).1
      have hrest : WordWithin a.offset rest := hdsc.1
      simp only [orderedProgram, evaluate]
      rw [ih hdsc.2 a.offset hrest, completedMultiply_embedWindow]
      have htime := completedTime_embedWindow hw0 hw1 hsmall hd hs hb
        a.offset (H-a.offset) (.mul (.loop a.offset a.loop a.spin) (wordExpression rest))
        ⟨Nat.le_refl _, (wordExpression_within a.offset rest).mpr hrest⟩
      simpa only [show a.offset+(H-a.offset)=H by omega, wordExpression] using htime

/-- Any bounded word, not an assumed time-ordered input, has an exact original-state program. -/
theorem wordProgram_pin {base : Nat} (hb : 0 < base) (H : Nat)
    (word : List (TimedLoop base)) (hword : WordWithin H word) :
    evaluate hw0 hw1 hsmall hd hs (wordProgram H word) =
      embedWindow hw0 hw1 hsmall hd hs hb H (wordExpression word)
        ((wordExpression_within H word).mpr hword) := by
  refine (orderedProgram_pin hw0 hw1 hsmall hd hs hb (orderWord word)
    (orderWord_descending word) H (orderWord_within H word hword)).trans ?_
  exact embedWindow_eq_of_source_identity hw0 hw1 hsmall hd hs hb H
    (wordExpression (orderWord word)) (wordExpression word)
    ((wordExpression_within H (orderWord word)).mpr (orderWord_within H word hword))
    ((wordExpression_within H word).mpr hword)
    (PaddedPolynomialCoeffEqv.of_coeff (orderWord_source word))

#print axioms Program
#print axioms orderedProgram
#print axioms wordProgram
#print axioms evaluate
#print axioms orderedProgram_pin
#print axioms wordProgram_pin

end YMGap.Continuum.BF4WilsonChronologicalProgram
