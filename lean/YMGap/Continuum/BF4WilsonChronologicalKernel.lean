/-
# Duration-preserving chronological kernels for original Wilson windows

The existing compiler generates vacuum vectors. Its empty word is the identity,
so it can omit time before the first insertion because time fixes the vacuum.
That convention is not an observable-presentation-independent kernel on arbitrary
inputs. Here the empty word propagates for the WHOLE supplied duration H.

Every compiled kernel acts on an original input window by adjoining the shifted
original observable and advancing the reflection center by H. This exact graft
identity keeps the input expression, action, carrier and discrete duration.
The old vacuum output and squared cap are retained. Nothing identifies the old
and new operators away from the vacuum or constructs a continuum OS root.
-/

import YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra

namespace YMGap.Continuum.BF4WilsonChronologicalKernel

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4WilsonTimedWord
open YMGap.Continuum.BF4WilsonTimedWordOrder
open YMGap.Continuum.BF4WilsonExpressionExpansion
open YMGap.Continuum.BF4WilsonChronologicalProgram
open YMGap.Continuum.BF4WilsonChronologicalOperator
open YMGap.Continuum.BF4WilsonWindowOperatorPins
open YMGap.Continuum.BF4WilsonWindowRealization
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws
open YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity (embedWindow_eq_of_source_identity)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_coeff)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Empty intervals still propagate arbitrary inputs through their duration. -/
def orderedKernel {base : Nat} (H : Nat) : List (TimedLoop base) → Program base
  | [] => .time H .vacuum
  | a :: rest => .time (H-a.offset)
      (.multiply a.loop a.spin (orderedKernel a.offset rest))

def wordKernel {base : Nat} (H : Nat) (word : List (TimedLoop base)) : Program base :=
  orderedKernel H (orderWord word)

def termsKernel {base : Nat} (H : Nat) : List (Q' × List (TimedLoop base)) → Program base
  | [] => .zero
  | a :: rest => .add (.smul a.1 (wordKernel H a.2)) (termsKernel H rest)

def compileKernel {base : Nat} (H : Nat) (e : WindowExpression base) : Program base :=
  termsKernel H (expand e)

/-- Attach the new interval AFTER the input window, retaining both factors. -/
def graft {base : Nat} (K : Nat) (e f : WindowExpression base) : WindowExpression base :=
  .mul (shift K e) f

theorem graft_within {base H K : Nat} (e f : WindowExpression base)
    (he : Within H e) (hf : Within K f) : Within (H+K) (graft K e f) :=
  ⟨shift_within H K e he, within_mono (Nat.le_add_left _ _) f hf⟩

theorem graft_source_congr {base : Nat} (blocks K : Nat)
    (e e' f : WindowExpression base)
    (h : RatPolyCoeffEqv (sourcePolynomial e) (sourcePolynomial e')) :
    PaddedPolynomialCoeffEqv blocks (sourcePolynomial (graft K e f))
      (sourcePolynomial (graft K e' f)) :=
  ((source_shift blocks K e).trans
    ((PaddedPolynomialCoeffEqv.of_coeff (lift_coeff (K*(baseLinks base).length) h)).trans
      (source_shift blocks K e').symm)).mul (.refl _ _)

theorem orderedKernel_cap {base : Nat} (H : Nat) (word : List (TimedLoop base)) :
    squaredCap (orderedKernel H word) = squaredCap (orderedProgram H word) := by
  induction word generalizing H with
  | nil => rfl
  | cons a rest ih => simp only [orderedKernel, orderedProgram, squaredCap, ih]

theorem compileKernel_cap {base : Nat} (H : Nat) (e : WindowExpression base) :
    squaredCap (compileKernel H e) = squaredCap (compileWindow H e) := by
  suffices h : ∀ terms : List (Q' × List (TimedLoop base)),
      squaredCap (termsKernel H terms) = squaredCap (termsProgram H terms) from h (expand e)
  intro terms
  induction terms with
  | nil => rfl
  | cons a rest ih =>
      simp only [termsKernel, termsProgram, squaredCap, wordKernel, wordProgram, orderedKernel_cap, ih]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "Op" => act hw0 hw1 hsmall hd hs
local notation "Eval" => evaluate hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs

theorem orderedKernel_vacuum {base : Nat} (H : Nat) (word : List (TimedLoop base)) :
    Eval (orderedKernel H word) = Eval (orderedProgram H word) := by
  induction word generalizing H with
  | nil => exact completedUnit_fixed hw0 hw1 hsmall hd hs H
  | cons a rest ih => simp only [orderedKernel, orderedProgram, evaluate, ih]

theorem compileKernel_vacuum {base : Nat} (H : Nat) (e : WindowExpression base) :
    Op (compileKernel H e) U = Eval (compileWindow H e) := by
  rw [act_unit]
  suffices h : ∀ terms : List (Q' × List (TimedLoop base)),
      Eval (termsKernel H terms) = Eval (termsProgram H terms) from h (expand e)
  intro terms
  induction terms with
  | nil => rfl
  | cons a rest ih =>
      simp only [termsKernel, termsProgram, evaluate, wordKernel, wordProgram, orderedKernel_vacuum, ih]

/-- This is an all-input time operator, not merely its vacuum value. -/
theorem compileKernel_one {base : Nat} (H : Nat) (x : V) :
    Op (compileKernel H (.one : WindowExpression base)) x =
      completedTime hw0 hw1 hsmall hd hs H x := by
  simp only [compileKernel, expand, termsKernel, wordKernel, orderWord, orderedKernel, act,
    completedSmul_one, completedAdd_zero]

/-- Exact original-window action for a supplied finite input, including its past. -/
theorem orderedKernel_graft {base : Nat} (hb : 0 < base)
    (word : List (TimedLoop base)) (hdsc : Descending word)
    (H K : Nat) (hword : WordWithin H word) (f : WindowExpression base) (hf : Within K f) :
    Op (orderedKernel H word) (embedWindow hw0 hw1 hsmall hd hs hb K f hf) =
      embedWindow hw0 hw1 hsmall hd hs hb (H+K) (graft K (wordExpression word) f)
        (graft_within _ _ ((wordExpression_within H word).mpr hword) hf) := by
  induction word generalizing H with
  | nil =>
      simp only [orderedKernel, act]
      have ht := completedTime_embedWindow hw0 hw1 hsmall hd hs hb K H f hf
      simp only [Nat.add_comm K H] at ht
      refine ht.trans ?_
      apply embedWindow_eq_of_source_identity hw0 hw1 hsmall hd hs hb (H+K)
      exact PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.one_mul (sourcePolynomial f)).symm
  | cons a rest ih =>
      have ha : a.offset ≤ H := ((wordWithin_cons H a rest).mp hword).1
      have hr := (wordExpression_within a.offset rest).mpr hdsc.1
      simp only [orderedKernel, act]
      rw [ih hdsc.2 a.offset hdsc.1, completedMultiply_embedWindow]
      have ht := completedTime_embedWindow hw0 hw1 hsmall hd hs hb
        (a.offset+K) (H-a.offset)
        (.mul (.loop (a.offset+K) a.loop a.spin) (graft K (wordExpression rest) f))
        ⟨Nat.le_refl _, graft_within _ _ hr hf⟩
      simp only [show a.offset+K+(H-a.offset)=H+K by omega] at ht
      refine ht.trans ?_
      apply embedWindow_eq_of_source_identity hw0 hw1 hsmall hd hs hb (H+K)
      exact PaddedPolynomialCoeffEqv.of_coeff
        (RatPolyCoeffEqv.mul_assoc (sourcePolynomial (.loop (a.offset+K) a.loop a.spin))
          (sourcePolynomial (shift K (wordExpression rest))) (sourcePolynomial f)).symm

theorem wordKernel_graft {base : Nat} (hb : 0 < base) (H K : Nat)
    (word : List (TimedLoop base)) (hword : WordWithin H word)
    (f : WindowExpression base) (hf : Within K f) :
    Op (wordKernel H word) (embedWindow hw0 hw1 hsmall hd hs hb K f hf) =
      embedWindow hw0 hw1 hsmall hd hs hb (H+K) (graft K (wordExpression word) f)
        (graft_within _ _ ((wordExpression_within H word).mpr hword) hf) := by
  refine (orderedKernel_graft hw0 hw1 hsmall hd hs hb (orderWord word)
    (orderWord_descending word) H K (orderWord_within H word hword) f hf).trans ?_
  apply embedWindow_eq_of_source_identity hw0 hw1 hsmall hd hs hb (H+K)
  exact graft_source_congr _ K _ _ f (orderWord_source word)

theorem termsKernel_graft {base : Nat} (hb : 0 < base) (H K : Nat)
    (terms : List (Q' × List (TimedLoop base)))
    (hterms : ∀ term, term ∈ terms → WordWithin H term.2)
    (f : WindowExpression base) (hf : Within K f) :
    Op (termsKernel H terms) (embedWindow hw0 hw1 hsmall hd hs hb K f hf) =
      embedWindow hw0 hw1 hsmall hd hs hb (H+K) (graft K (termsExpression terms) f)
        (graft_within _ _ (termsExpression_within H terms hterms) hf) := by
  induction terms with
  | nil =>
      change BF4WilsonSpatialUnionPosdef.completedZero hw0 hw1 hsmall hd hs = _
      rw [← embedWindow_zero hw0 hw1 hsmall hd hs hb (H+K)]
      apply embedWindow_eq_of_source_identity hw0 hw1 hsmall hd hs hb (H+K)
      exact PaddedPolynomialCoeffEqv.of_coeff
        ((RatPolyCoeffEqv.zero_smul polyOne).trans
          (((RatPolyCoeffEqv.zero_smul polyOne).mul_right (sourcePolynomial f)).trans
            (RatPolyCoeffEqv.mul_zero_left (sourcePolynomial f))).symm)
  | cons a rest ih =>
      have ha := hterms a List.mem_cons_self
      have hr : ∀ term, term ∈ rest → WordWithin H term.2 :=
        fun term ht => hterms term (List.mem_cons_of_mem a ht)
      simp only [termsKernel, act]
      rw [wordKernel_graft hw0 hw1 hsmall hd hs hb H K a.2 ha f hf, ih hr,
        completedSmul_embedWindow, completedAdd_embedWindow]
      apply embedWindow_eq_of_source_identity hw0 hw1 hsmall hd hs hb (H+K)
      change PaddedPolynomialCoeffEqv _
        (polyAdd (polySmul a.1 (polyMul (sourcePolynomial (shift K (wordExpression a.2)))
          (sourcePolynomial f)))
          (polyMul (sourcePolynomial (shift K (termsExpression rest))) (sourcePolynomial f)))
        (polyMul (polyAdd (polySmul a.1 (sourcePolynomial (shift K (wordExpression a.2))))
          (sourcePolynomial (shift K (termsExpression rest)))) (sourcePolynomial f))
      rw [polyMul_add_left_exact]
      exact PaddedPolynomialCoeffEqv.of_coeff
        ((RatPolyCoeffEqv.polyMul_smul_left a.1
          (sourcePolynomial (shift K (wordExpression a.2))) (sourcePolynomial f)).symm.add
          (.refl _))

/-- The new compiler is pinned on original finite inputs, not only on U. -/
theorem compileKernel_graft {base : Nat} (hb : 0 < base) (H K : Nat)
    (e f : WindowExpression base) (he : Within H e) (hf : Within K f) :
    Op (compileKernel H e) (embedWindow hw0 hw1 hsmall hd hs hb K f hf) =
      embedWindow hw0 hw1 hsmall hd hs hb (H+K) (graft K e f) (graft_within e f he hf) := by
  refine (termsKernel_graft hw0 hw1 hsmall hd hs hb H K (expand e)
    (expand_within H e he) f hf).trans ?_
  apply embedWindow_eq_of_source_identity hw0 hw1 hsmall hd hs hb (H+K)
  exact graft_source_congr _ K _ _ f (expand_source e)

end YMGap.Continuum.BF4WilsonChronologicalKernel

#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.orderedKernel
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.wordKernel
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.termsKernel
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.compileKernel
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.graft
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.graft_within
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.graft_source_congr
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.orderedKernel_cap
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.compileKernel_cap
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.orderedKernel_vacuum
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.compileKernel_vacuum
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.compileKernel_one
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.orderedKernel_graft
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.wordKernel_graft
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.termsKernel_graft
#print axioms YMGap.Continuum.BF4WilsonChronologicalKernel.compileKernel_graft
