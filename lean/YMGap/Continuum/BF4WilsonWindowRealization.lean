/-
# Every original signed Wilson window has an exact finite operator program

Expand the supplied expression, order each scalar character word by time,
and assemble its actual chronological operator program with the original
signed coefficients. The finite source identities and original state descent
prove equality to the existing embedded window. All original finite windows
are covered, not just a selected family of loop products.

The certificate returns the finite program as Type-level data. Every dense
union stage has such a certificate, with its OWN supplied base and radius;
no common support bound is selected for Cauchy streams. A supplied Cauchy
representative and positive tolerance compute a finite program within that
actual completed squared-distance tolerance, using the original modulus.
This is coverage of
the existing Wilson-window syntax, not a theorem that it contains every
gauge observable, a canonical reflected OS root, or continuum QFT.
-/

import YMGap.Continuum.BF4WilsonExpressionExpansion
import YMGap.Continuum.BF4WilsonChronologicalProgram

namespace YMGap.Continuum.BF4WilsonWindowRealization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4WilsonTimedWord
open YMGap.Continuum.BF4WilsonExpressionExpansion
open YMGap.Continuum.BF4WilsonChronologicalProgram
open YMGap.Continuum.BF4WilsonWindowOperatorPins
open YMGap.Continuum.BF4WilsonSpatialUnion (Stage)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedDistance (completedDist distanceData)
open YMGap.Continuum.CRealSeminormCompletedApproximation (constantApproximation_bound)
open YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity (embedWindow_eq_of_source_identity)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

def termsProgram {base : Nat} (H : Nat) : List (Q' × List (TimedLoop base)) → Program base
  | [] => .zero
  | term :: rest => .add (.smul term.1 (wordProgram H term.2)) (termsProgram H rest)

/-- Computable finite code, retaining every signed term rather than selecting a representation. -/
def compileWindow {base : Nat} (H : Nat) (e : WindowExpression base) : Program base :=
  termsProgram H (expand e)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs

theorem termsProgram_pin {base : Nat} (hb : 0 < base) (H : Nat)
    (terms : List (Q' × List (TimedLoop base)))
    (hterms : ∀ term, term ∈ terms → WordWithin H term.2) :
    evaluate hw0 hw1 hsmall hd hs (termsProgram H terms) =
      embedWindow hw0 hw1 hsmall hd hs hb H (termsExpression terms)
        (termsExpression_within H terms hterms) := by
  induction terms with
  | nil => exact (embedWindow_zero hw0 hw1 hsmall hd hs hb H).symm
  | cons a rest ih =>
      have ha := hterms a List.mem_cons_self
      have hr : ∀ term, term ∈ rest → WordWithin H term.2 :=
        fun term ht => hterms term (List.mem_cons_of_mem a ht)
      simp only [termsProgram, evaluate]
      rw [wordProgram_pin hw0 hw1 hsmall hd hs hb H a.2 ha, ih hr,
        completedSmul_embedWindow, completedAdd_embedWindow]
      rfl

/-- Exact realization of EVERY original bounded signed multi-time expression. -/
theorem compileWindow_pin {base : Nat} (hb : 0 < base) (H : Nat)
    (e : WindowExpression base) (he : Within H e) :
    evaluate hw0 hw1 hsmall hd hs (compileWindow H e) =
      embedWindow hw0 hw1 hsmall hd hs hb H e he := by
  refine (termsProgram_pin hw0 hw1 hsmall hd hs hb H (expand e)
    (expand_within H e he)).trans ?_
  exact embedWindow_eq_of_source_identity hw0 hw1 hsmall hd hs hb H
    (termsExpression (expand e)) e
    (termsExpression_within H (expand e) (expand_within H e he)) he
    (PaddedPolynomialCoeffEqv.of_coeff (expand_source e))

/-- The witness is the explicit finite code, not a Prop-level existence claim. -/
def windowCertificate {base : Nat} (hb : 0 < base) (H : Nat)
    (e : WindowExpression base) (he : Within H e) :
    {p : Program base // evaluate hw0 hw1 hsmall hd hs p =
      embedWindow hw0 hw1 hsmall hd hs hb H e he} :=
  ⟨compileWindow H e, compileWindow_pin hw0 hw1 hsmall hd hs hb H e he⟩

def stageProgram (x : Stage) : Program x.base := compileWindow x.value.radius x.value.expression

/-- Every dense stage of the existing UNION, without a fixed global support base. -/
theorem stageProgram_pin (x : Stage) :
    evaluate hw0 hw1 hsmall hd hs (stageProgram x) = embedStage hw0 hw1 hsmall hd hs x := by
  have h := compileWindow_pin hw0 hw1 hsmall hd hs x.positive x.value.radius
    x.value.expression x.value.within
  exact h

def stageCertificate (x : Stage) :
    {p : Program x.base // evaluate hw0 hw1 hsmall hd hs p = embedStage hw0 hw1 hsmall hd hs x} :=
  ⟨stageProgram x, stageProgram_pin hw0 hw1 hsmall hd hs x⟩

/-- The support base is computed from the actual sampled stage, not chosen for the stream. -/
def approximationProgram (X : (D).Cauchy) (epsilon : Q') :
    Program (X.seq (X.modulus epsilon)).base :=
  stageProgram (X.seq (X.modulus epsilon))

theorem approximationProgram_bound (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    RCle (completedDist hw0 hw1 hsmall hd hs
      (evaluate hw0 hw1 hsmall hd hs (approximationProgram hw0 hw1 hsmall hd hs X epsilon))
      (Quotient.mk (D).completionSetoid X)) (Quotient.mk crealSetoid (ofQ' epsilon)) := by
  unfold approximationProgram
  rw [stageProgram_pin]
  exact constantApproximation_bound (distanceData hw0 hw1 hsmall hd hs) X epsilon he
    (X.modulus epsilon) (Nat.le_refl _)

/-- Quantitative vacuum-program generation for every SUPPLIED original Cauchy representative. -/
def approximationCertificate (X : (D).Cauchy) (epsilon : Q') (he : (0 : Q') < epsilon) :
    Σ' base : Nat, {p : Program base // RCle
      (completedDist hw0 hw1 hsmall hd hs (evaluate hw0 hw1 hsmall hd hs p)
        (Quotient.mk (D).completionSetoid X)) (Quotient.mk crealSetoid (ofQ' epsilon))} :=
  ⟨(X.seq (X.modulus epsilon)).base,
    approximationProgram hw0 hw1 hsmall hd hs X epsilon,
    approximationProgram_bound hw0 hw1 hsmall hd hs X epsilon he⟩

#print axioms termsProgram
#print axioms compileWindow
#print axioms termsProgram_pin
#print axioms compileWindow_pin
#print axioms windowCertificate
#print axioms stageProgram
#print axioms stageProgram_pin
#print axioms stageCertificate
#print axioms approximationProgram
#print axioms approximationProgram_bound
#print axioms approximationCertificate

end YMGap.Continuum.BF4WilsonWindowRealization
