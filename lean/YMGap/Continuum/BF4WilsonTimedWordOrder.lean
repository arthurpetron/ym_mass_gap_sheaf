/-
# Constructive chronological ordering of scalar Wilson-character words

Insertion sort compares only the natural-number time offsets. The output
has decreasing offsets and retains any supplied finite time bound. Its
original source polynomial is coefficient-equivalent to the input by
associativity and commutativity of scalar character multiplication.

No comparison on SourceLoop is used. In particular, no ordered link within
a nonabelian Wilson holonomy is moved. This is a finite syntax identity for
the original source polynomials, not an assumed OS-state identification.
-/

import YMGap.Continuum.BF4WilsonTimedWord

namespace YMGap.Continuum.BF4WilsonTimedWordOrder

set_option autoImplicit false

open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4WilsonTimedWord
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

/-- Insert before the first offset no greater than the supplied offset. -/
def insertWord {base : Nat} (a : TimedLoop base) :
    List (TimedLoop base) → List (TimedLoop base)
  | [] => [a]
  | b :: rest =>
      if b.offset ≤ a.offset then a :: b :: rest else b :: insertWord a rest

def orderWord {base : Nat} : List (TimedLoop base) → List (TimedLoop base)
  | [] => []
  | a :: rest => insertWord a (orderWord rest)

theorem insertWord_within {base : Nat} (H : Nat) (a : TimedLoop base)
    (xs : List (TimedLoop base)) (ha : a.offset ≤ H) :
    WordWithin H xs → WordWithin H (insertWord a xs) := by
  induction xs with
  | nil =>
      intro _
      exact (wordWithin_cons H a []).mpr ⟨ha, wordWithin_nil H⟩
  | cons b rest ih =>
      intro h
      have hb := (wordWithin_cons H b rest).mp h
      by_cases hab : b.offset ≤ a.offset
      · simpa only [insertWord, if_pos hab] using
          (wordWithin_cons H a (b :: rest)).mpr ⟨ha, h⟩
      · simpa only [insertWord, if_neg hab] using
          (wordWithin_cons H b (insertWord a rest)).mpr ⟨hb.1, ih hb.2⟩

theorem insertWord_descending {base : Nat} (a : TimedLoop base)
    (xs : List (TimedLoop base)) : Descending xs → Descending (insertWord a xs) := by
  induction xs with
  | nil =>
      intro _
      exact ⟨wordWithin_nil a.offset, True.intro⟩
  | cons b rest ih =>
      intro h
      have hb : WordWithin b.offset rest ∧ Descending rest := h
      by_cases hab : b.offset ≤ a.offset
      · rw [insertWord, if_pos hab]
        exact ⟨(wordWithin_cons a.offset b rest).mpr
          ⟨hab, fun c hc => Nat.le_trans (hb.1 c hc) hab⟩, h⟩
      · rw [insertWord, if_neg hab]
        exact ⟨insertWord_within b.offset a rest (by omega) hb.1, ih hb.2⟩

theorem orderWord_descending {base : Nat} (xs : List (TimedLoop base)) :
    Descending (orderWord xs) := by
  induction xs with
  | nil => exact True.intro
  | cons a rest ih => exact insertWord_descending a (orderWord rest) ih

theorem orderWord_within {base : Nat} (H : Nat) (xs : List (TimedLoop base)) :
    WordWithin H xs → WordWithin H (orderWord xs) := by
  induction xs with
  | nil => exact fun h => h
  | cons a rest ih =>
      intro h
      have ha := (wordWithin_cons H a rest).mp h
      exact insertWord_within H a (orderWord rest) ha.1 (ih ha.2)

private theorem swap_scalar_factors (a b c : RatPoly) :
    RatPolyCoeffEqv (polyMul b (polyMul a c)) (polyMul a (polyMul b c)) :=
  (RatPolyCoeffEqv.mul_assoc b a c).symm.trans
    (((RatPolyCoeffEqv.mul_comm b a).mul_right c).trans
      (RatPolyCoeffEqv.mul_assoc a b c))

/-- The unchanged inserted character multiplies the original word polynomial. -/
theorem insertWord_source {base : Nat} (a : TimedLoop base)
    (xs : List (TimedLoop base)) :
    RatPolyCoeffEqv (sourcePolynomial (wordExpression (insertWord a xs)))
      (polyMul (sourcePolynomial (.loop a.offset a.loop a.spin))
        (sourcePolynomial (wordExpression xs))) := by
  induction xs with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons b rest ih =>
      by_cases hab : b.offset ≤ a.offset
      · rw [insertWord, if_pos hab]
        exact RatPolyCoeffEqv.refl _
      · rw [insertWord, if_neg hab]
        exact (RatPolyCoeffEqv.mul_left
          (sourcePolynomial (.loop b.offset b.loop b.spin)) ih).trans
          (swap_scalar_factors
            (sourcePolynomial (.loop a.offset a.loop a.spin))
            (sourcePolynomial (.loop b.offset b.loop b.spin))
            (sourcePolynomial (wordExpression rest)))

/-- Chronological ordering preserves the actual source polynomial, without
reordering any internal holonomy word or comparing source-loop data. -/
theorem orderWord_source {base : Nat} (xs : List (TimedLoop base)) :
    RatPolyCoeffEqv (sourcePolynomial (wordExpression (orderWord xs)))
      (sourcePolynomial (wordExpression xs)) := by
  induction xs with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons a rest ih =>
      exact (insertWord_source a (orderWord rest)).trans
        (RatPolyCoeffEqv.mul_left (sourcePolynomial (.loop a.offset a.loop a.spin)) ih)

#print axioms insertWord
#print axioms orderWord
#print axioms insertWord_within
#print axioms insertWord_descending
#print axioms orderWord_descending
#print axioms orderWord_within
#print axioms insertWord_source
#print axioms orderWord_source

end YMGap.Continuum.BF4WilsonTimedWordOrder
