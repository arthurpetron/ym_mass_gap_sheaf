/-
# Exact finite signed-word expansion of ORIGINAL Wilson expressions

Every original window expression is expanded constructively into a finite
list of rationally weighted timed words. Products use the Cartesian product
of the two lists and concatenate words; no loop holonomy is reordered.
The signed sum of these words has the same free source polynomial and the
same window bound as the original expression.

This is finite coefficient algebra on the existing syntax, with no analytic
hypothesis or new state space. Chronological sorting, operator realization
and descent into the original OS completion are separate consumers.
-/

import YMGap.Continuum.BF4WilsonTimedWord

namespace YMGap.Continuum.BF4WilsonExpressionExpansion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4WilsonTimedWord
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

/-- Explicit Cartesian multiplication, retaining coefficient products and word order. -/
def multiplyTerms {base : Nat} : List (Q' × List (TimedLoop base)) →
    List (Q' × List (TimedLoop base)) → List (Q' × List (TimedLoop base))
  | [], _ => []
  | a :: rest, right =>
      right.map (fun b => (a.1*b.1, a.2++b.2)) ++ multiplyTerms rest right

/-- A finite signed list, without collecting, sorting or cancelling terms. -/
def expand {base : Nat} : WindowExpression base → List (Q' × List (TimedLoop base))
  | .one => [(1, [])]
  | .loop offset loop spin => [(1, [⟨offset, loop, spin⟩])]
  | .add e f => expand e ++ expand f
  | .mul e f => multiplyTerms (expand e) (expand f)
  | .smul c e => (expand e).map (fun term => (c*term.1, term.2))

/-- The empty list denotes the original zero expression, not an added constructor. -/
def termsExpression {base : Nat} : List (Q' × List (TimedLoop base)) → WindowExpression base
  | [] => .smul 0 .one
  | term :: rest => .add (.smul term.1 (wordExpression term.2)) (termsExpression rest)

private theorem word_source_append {base : Nat} (left right : List (TimedLoop base)) :
    RatPolyCoeffEqv (sourcePolynomial (wordExpression (left++right)))
      (polyMul (sourcePolynomial (wordExpression left)) (sourcePolynomial (wordExpression right))) := by
  induction left with
  | nil => exact (RatPolyCoeffEqv.one_mul _).symm
  | cons a rest ih =>
      exact (RatPolyCoeffEqv.mul_left (sourcePolynomial (.loop a.offset a.loop a.spin)) ih).trans
        (RatPolyCoeffEqv.mul_assoc (sourcePolynomial (.loop a.offset a.loop a.spin))
          (sourcePolynomial (wordExpression rest)) (sourcePolynomial (wordExpression right))).symm

private theorem terms_source_singleton {base : Nat} (c : Q') (word : List (TimedLoop base)) :
    RatPolyCoeffEqv (sourcePolynomial (termsExpression [(c, word)]))
      (polySmul c (sourcePolynomial (wordExpression word))) :=
  ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.zero_smul polyOne)).trans
    (RatPolyCoeffEqv.add_zero _)

private theorem terms_source_append {base : Nat}
    (left right : List (Q' × List (TimedLoop base))) :
    RatPolyCoeffEqv (sourcePolynomial (termsExpression (left++right)))
      (polyAdd (sourcePolynomial (termsExpression left)) (sourcePolynomial (termsExpression right))) := by
  induction left with
  | nil =>
      exact (((RatPolyCoeffEqv.zero_smul polyOne).add (RatPolyCoeffEqv.refl _)).trans
        (RatPolyCoeffEqv.zero_add _)).symm
  | cons a rest ih =>
      exact ((RatPolyCoeffEqv.refl _).add ih).trans
        (RatPolyCoeffEqv.add_assoc
          (polySmul a.1 (sourcePolynomial (wordExpression a.2)))
          (sourcePolynomial (termsExpression rest)) (sourcePolynomial (termsExpression right))).symm

private theorem terms_source_smul {base : Nat} (c : Q')
    (terms : List (Q' × List (TimedLoop base))) :
    RatPolyCoeffEqv
      (sourcePolynomial (termsExpression (terms.map (fun term => (c*term.1, term.2)))))
      (polySmul c (sourcePolynomial (termsExpression terms))) := by
  induction terms with
  | nil =>
      exact (RatPolyCoeffEqv.zero_smul polyOne).trans
        (((RatPolyCoeffEqv.zero_smul polyOne).smul c).trans (RatPolyCoeffEqv.smul_zero c)).symm
  | cons a rest ih =>
      exact ((RatPolyCoeffEqv.smul_assoc c a.1 (sourcePolynomial (wordExpression a.2))).symm.add ih).trans
        (RatPolyCoeffEqv.smul_add c (polySmul a.1 (sourcePolynomial (wordExpression a.2)))
          (sourcePolynomial (termsExpression rest))).symm

private theorem weighted_word_product {base : Nat}
    (a b : Q' × List (TimedLoop base)) :
    RatPolyCoeffEqv (polySmul (a.1*b.1) (sourcePolynomial (wordExpression (a.2++b.2))))
      (polyMul (polySmul a.1 (sourcePolynomial (wordExpression a.2)))
        (polySmul b.1 (sourcePolynomial (wordExpression b.2)))) :=
  ((word_source_append a.2 b.2).smul (a.1*b.1)).trans
    ((RatPolyCoeffEqv.smul_assoc a.1 b.1
      (polyMul (sourcePolynomial (wordExpression a.2)) (sourcePolynomial (wordExpression b.2)))).symm.trans
      (((RatPolyCoeffEqv.polyMul_smul_right b.1 (sourcePolynomial (wordExpression a.2))
        (sourcePolynomial (wordExpression b.2))).smul a.1).symm.trans
          (RatPolyCoeffEqv.polyMul_smul_left a.1 (sourcePolynomial (wordExpression a.2))
            (polySmul b.1 (sourcePolynomial (wordExpression b.2)))).symm))

private theorem terms_source_row {base : Nat} (a : Q' × List (TimedLoop base))
    (right : List (Q' × List (TimedLoop base))) :
    RatPolyCoeffEqv
      (sourcePolynomial (termsExpression (right.map (fun b => (a.1*b.1, a.2++b.2)))))
      (polyMul (polySmul a.1 (sourcePolynomial (wordExpression a.2)))
        (sourcePolynomial (termsExpression right))) := by
  induction right with
  | nil =>
      exact (RatPolyCoeffEqv.zero_smul polyOne).trans
        ((RatPolyCoeffEqv.mul_left _ (RatPolyCoeffEqv.zero_smul polyOne)).trans
          (RatPolyCoeffEqv.mul_zero_right _)).symm
  | cons b rest ih =>
      exact ((weighted_word_product a b).add ih).trans
        (RatPolyCoeffEqv.mul_add_right
          (polySmul a.1 (sourcePolynomial (wordExpression a.2)))
          (polySmul b.1 (sourcePolynomial (wordExpression b.2)))
          (sourcePolynomial (termsExpression rest))).symm

private theorem terms_source_product {base : Nat}
    (left right : List (Q' × List (TimedLoop base))) :
    RatPolyCoeffEqv (sourcePolynomial (termsExpression (multiplyTerms left right)))
      (polyMul (sourcePolynomial (termsExpression left)) (sourcePolynomial (termsExpression right))) := by
  induction left with
  | nil =>
      exact (RatPolyCoeffEqv.zero_smul polyOne).trans
        (((RatPolyCoeffEqv.zero_smul polyOne).mul_right _).trans
          (RatPolyCoeffEqv.mul_zero_left _)).symm
  | cons a rest ih =>
      refine ((terms_source_append
        (right.map (fun b => (a.1*b.1, a.2++b.2))) (multiplyTerms rest right)).trans
          ((terms_source_row a right).add ih)).trans ?_
      change RatPolyCoeffEqv _
        (polyMul (polyAdd (polySmul a.1 (sourcePolynomial (wordExpression a.2)))
          (sourcePolynomial (termsExpression rest))) (sourcePolynomial (termsExpression right)))
      rw [polyMul_add_left_exact]
      exact RatPolyCoeffEqv.refl _

/-- Exact FREE source-polynomial equality, before any regulator or state quotient. -/
theorem expand_source {base : Nat} (e : WindowExpression base) :
    RatPolyCoeffEqv (sourcePolynomial (termsExpression (expand e))) (sourcePolynomial e) := by
  induction e with
  | one =>
      exact (terms_source_singleton (base := base) 1 []).trans (RatPolyCoeffEqv.one_smul polyOne)
  | loop offset loop spin =>
      exact (terms_source_singleton 1 [⟨offset, loop, spin⟩]).trans
        ((RatPolyCoeffEqv.one_smul _).trans (RatPolyCoeffEqv.mul_one _))
  | add e f ihe ihf => exact (terms_source_append (expand e) (expand f)).trans (ihe.add ihf)
  | mul e f ihe ihf => exact (terms_source_product (expand e) (expand f)).trans (ihe.mul ihf)
  | smul c e ih => exact (terms_source_smul c (expand e)).trans (ih.smul c)

private theorem wordWithin_append {base H : Nat} {left right : List (TimedLoop base)}
    (hl : WordWithin H left) (hr : WordWithin H right) : WordWithin H (left++right) := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact hl a h
  · exact hr a h

private theorem multiplyTerms_within {base : Nat} (H : Nat)
    (left right : List (Q' × List (TimedLoop base)))
    (hl : ∀ term, term ∈ left → WordWithin H term.2)
    (hr : ∀ term, term ∈ right → WordWithin H term.2) :
    ∀ term, term ∈ multiplyTerms left right → WordWithin H term.2 := by
  revert hl
  induction left with
  | nil => intro _ term h; cases h
  | cons a rest ih =>
      intro hl term h
      rcases List.mem_append.mp h with hrow | hrest
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hrow
        exact wordWithin_append (hl a List.mem_cons_self) (hr b hb)
      · exact ih (fun b hb => hl b (List.mem_cons_of_mem a hb)) term hrest

/-- Every generated word retains the original window bound. -/
theorem expand_within {base : Nat} (H : Nat) :
    ∀ e : WindowExpression base, Within H e →
      ∀ term, term ∈ expand e → WordWithin H term.2
  | .one, _, term, ht => by
      have h : term = (1, []) := List.mem_singleton.mp ht
      subst term
      exact wordWithin_nil H
  | .loop offset loop spin, he, term, ht => by
      have h : term = (1, [⟨offset, loop, spin⟩]) := List.mem_singleton.mp ht
      subst term
      exact (wordWithin_cons H ⟨offset, loop, spin⟩ []).mpr ⟨he, wordWithin_nil H⟩
  | .add e f, he, term, ht => by
      rcases List.mem_append.mp ht with h | h
      · exact expand_within H e he.1 term h
      · exact expand_within H f he.2 term h
  | .mul e f, he, term, ht =>
      multiplyTerms_within H (expand e) (expand f)
        (expand_within H e he.1) (expand_within H f he.2) term ht
  | .smul c e, he, term, ht => by
      obtain ⟨original, ho, rfl⟩ := List.mem_map.mp ht
      exact expand_within H e he original ho

/-- Any finite signed sum of bounded words remains an original bounded expression. -/
theorem termsExpression_within {base : Nat} (H : Nat)
    (terms : List (Q' × List (TimedLoop base)))
    (hterms : ∀ term, term ∈ terms → WordWithin H term.2) :
    Within H (termsExpression terms) := by
  revert hterms
  induction terms with
  | nil => intro _; exact True.intro
  | cons a rest ih =>
      intro hterms
      exact ⟨(wordExpression_within H a.2).mpr (hterms a List.mem_cons_self),
        ih (fun b hb => hterms b (List.mem_cons_of_mem a hb))⟩

#print axioms multiplyTerms
#print axioms expand
#print axioms termsExpression
#print axioms expand_source
#print axioms expand_within
#print axioms termsExpression_within

end YMGap.Continuum.BF4WilsonExpressionExpansion
