/-
# Constructive vacuum generation on the SAME all-nome Wilson completion

The existing finite chronological code now evaluates using the actual
literal-width all-nome operators. Every bounded signed Wilson expression
has an explicit program with exactly its original embedded state. A supplied
Cauchy representative then computes a program within any positive squared-
distance tolerance, using that representative's own modulus.

Only the parameter-free word sorting, signed expansion and compiler are
reused from the older spatial-union construction. No small-nome conclusion,
carrier identification or extra analytic premise is imported into the proof.
This covers the existing fixed-width Wilson syntax, not all continuum gauge
observables. Scaling, full OS/QFT reconstruction and a physical gap remain open.
-/

import YMGap.Continuum.BF4WilsonAllNomeWindowPins
import YMGap.Continuum.BF4WilsonWindowRealization

namespace YMGap.Continuum.BF4WilsonAllNomeWindowRealization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression)
open YMGap.Continuum.BF4WilsonTimedWord
open YMGap.Continuum.BF4WilsonTimedWordOrder
open YMGap.Continuum.BF4WilsonExpressionExpansion
open YMGap.Continuum.BF4WilsonChronologicalProgram (Program orderedProgram wordProgram)
open YMGap.Continuum.BF4WilsonWindowRealization (termsProgram compileWindow)
open YMGap.Continuum.BF4WilsonAllNomeWindowPins
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion embed unitState)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedZero completedAdd completedSmul)
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator (completedMultiply)
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist distanceData)
open YMGap.Continuum.CRealSeminormCompletedApproximation (constantApproximation_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width

/-- Every constructor uses the pre-existing operations on the SAME completion. -/
def evaluate : Program width → V
  | .vacuum => unitState hw0 hw1 width
  | .zero => completedZero hw0 hw1 width
  | .add p q => completedAdd hw0 hw1 (evaluate p) (evaluate q)
  | .smul c p => completedSmul hw0 hw1 c (evaluate p)
  | .time n p => completedTime hw0 hw1 n (evaluate p)
  | .multiply L spin p => completedMultiply hw0 hw1 L spin (evaluate p)

theorem orderedProgram_pin (word : List (TimedLoop width)) (hdsc : Descending word)
    (H : Nat) (hword : WordWithin H word) :
    evaluate hw0 hw1 (orderedProgram H word) =
      embedWindow hw0 hw1 H (wordExpression word)
        ((wordExpression_within H word).mpr hword) := by
  induction word generalizing H with
  | nil => exact (embedWindow_one hw0 hw1 H).symm
  | cons a rest ih =>
      have ha : a.offset ≤ H := ((wordWithin_cons H a rest).mp hword).1
      have hrest : WordWithin a.offset rest := hdsc.1
      simp only [orderedProgram, evaluate]
      rw [ih hdsc.2 a.offset hrest, completedMultiply_embedWindow]
      have htime := completedTime_embedWindow hw0 hw1 a.offset (H-a.offset)
        (.mul (.loop a.offset a.loop a.spin) (wordExpression rest))
        ⟨Nat.le_refl _, (wordExpression_within a.offset rest).mpr hrest⟩
      simpa only [show a.offset+(H-a.offset)=H by omega, wordExpression] using htime

/-- Sorting changes no original state, by literal-width source-identity descent. -/
theorem wordProgram_pin (H : Nat) (word : List (TimedLoop width))
    (hword : WordWithin H word) :
    evaluate hw0 hw1 (wordProgram H word) =
      embedWindow hw0 hw1 H (wordExpression word)
        ((wordExpression_within H word).mpr hword) := by
  refine (orderedProgram_pin hw0 hw1 (orderWord word)
    (orderWord_descending word) H (orderWord_within H word hword)).trans ?_
  exact embedWindow_eq_of_source_identity hw0 hw1 H
    (wordExpression (orderWord word)) (wordExpression word)
    ((wordExpression_within H (orderWord word)).mpr (orderWord_within H word hword))
    ((wordExpression_within H word).mpr hword) (orderWord_source word)

theorem termsProgram_pin (H : Nat) (terms : List (Q' × List (TimedLoop width)))
    (hterms : ∀ term, term ∈ terms → WordWithin H term.2) :
    evaluate hw0 hw1 (termsProgram H terms) =
      embedWindow hw0 hw1 H (termsExpression terms)
        (termsExpression_within H terms hterms) := by
  induction terms with
  | nil => exact (embedWindow_zero hw0 hw1 H).symm
  | cons a rest ih =>
      have ha := hterms a List.mem_cons_self
      have hr : ∀ term, term ∈ rest → WordWithin H term.2 :=
        fun term ht => hterms term (List.mem_cons_of_mem a ht)
      simp only [termsProgram, evaluate]
      rw [wordProgram_pin hw0 hw1 H a.2 ha, ih hr,
        completedSmul_embedWindow, completedAdd_embedWindow]
      rfl

/-- Every bounded signed multi-time Wilson expression is exactly generated. -/
theorem compileWindow_pin (H : Nat) (e : WindowExpression width) (he : Within H e) :
    evaluate hw0 hw1 (compileWindow H e) = embedWindow hw0 hw1 H e he := by
  refine (termsProgram_pin hw0 hw1 H (expand e) (expand_within H e he)).trans ?_
  exact embedWindow_eq_of_source_identity hw0 hw1 H
    (termsExpression (expand e)) e
    (termsExpression_within H (expand e) (expand_within H e he)) he (expand_source e)

/-- The finite program is computable Type-level data, not a selected preimage. -/
def windowCertificate (H : Nat) (e : WindowExpression width) (he : Within H e) :
    {p : Program width // evaluate hw0 hw1 p = embedWindow hw0 hw1 H e he} :=
  ⟨compileWindow H e, compileWindow_pin hw0 hw1 H e he⟩

def intrinsicProgram (x : IntrinsicExpression width) : Program width :=
  compileWindow x.radius x.expression

theorem intrinsicProgram_pin (x : IntrinsicExpression width) :
    evaluate hw0 hw1 (intrinsicProgram x) = embed hw0 hw1 x :=
  compileWindow_pin hw0 hw1 x.radius x.expression x.within

/-- The existing representative supplies both the sampling index and the state. -/
def approximationProgram (X : (D).Cauchy) (epsilon : Q') : Program width :=
  intrinsicProgram (X.seq (X.modulus epsilon))

theorem approximationProgram_bound (X : (D).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) :
    RCle (completedDist hw0 hw1
      (evaluate hw0 hw1 (approximationProgram hw0 hw1 X epsilon))
      (Quotient.mk (D).completionSetoid X)) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  unfold approximationProgram
  rw [intrinsicProgram_pin]
  exact constantApproximation_bound (distanceData hw0 hw1) X epsilon he
    (X.modulus epsilon) (Nat.le_refl _)

/-- Quantitative vacuum generation for every SUPPLIED original representative;
no representative of an arbitrary quotient state is chosen. -/
def approximationCertificate (X : (D).Cauchy) (epsilon : Q')
    (he : (0 : Q') < epsilon) :
    {p : Program width // RCle (completedDist hw0 hw1 (evaluate hw0 hw1 p)
      (Quotient.mk (D).completionSetoid X)) (Quotient.mk crealSetoid (ofQ' epsilon))} :=
  ⟨approximationProgram hw0 hw1 X epsilon,
    approximationProgram_bound hw0 hw1 X epsilon he⟩

#print axioms evaluate
#print axioms orderedProgram_pin
#print axioms wordProgram_pin
#print axioms termsProgram_pin
#print axioms compileWindow_pin
#print axioms windowCertificate
#print axioms intrinsicProgram
#print axioms intrinsicProgram_pin
#print axioms approximationProgram
#print axioms approximationProgram_bound
#print axioms approximationCertificate

end YMGap.Continuum.BF4WilsonAllNomeWindowRealization
