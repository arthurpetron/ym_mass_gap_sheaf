/-
# Coefficient-setoid uniqueness for the canonical Chebyshev-U extractor

`SU2ClassPolynomialChebExtraction` constructs a finite Chebyshev-U expansion
for every bare `QPoly.Poly`.  This module proves that the construction respects
the semantic polynomial setoid.  The coefficient setoid is the kernel-decidable
predicate `QPoly.allZero (psub a b)`; the preceding extensional-reflection
theorem identifies it exactly with extensional rational evaluation.

The main result says extensionally equal bare polynomials have coefficientwise
equivalent canonical Chebyshev extractions.  Consequently the extracted vacuum
coefficient defines a functional directly on bare polynomials and respects
`PolyEqv`.  This is the uniqueness/well-definedness half of the Haar descent.

Honest scope: linearity and fusion-square positivity of the descended
functional, and conversion to `CharacterPacket`, are successor results.

# Axiom gate

All declarations are MLTT/HoTT-clean up to `propext` / `Quot.sound`.  There is
no `Classical.*`, `Real`, `native_decide`, `sorry`, `admit`, or custom axiom.
-/

import YMGap.Continuum.SU2ClassPolynomialChebExtraction

namespace YMGap.Continuum.SU2ClassPolynomialChebUniqueness

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2ClassPolynomialExtensionalReflection
open YMGap.Continuum.SU2ClassPolynomialChebExtraction

/-- Semantic equality of finite coefficient lists, including arbitrary
trailing and unnormalized zero representatives. -/
def CoeffEqv (a b : List Q') : Prop := allZero (psub a b)

local infix:50 " ≈c " => CoeffEqv

theorem coeffEqv_iff_polyEqv (a b : List Q') :
    (a ≈c b) <-> PolyEqv a b := by
  exact (polyEqv_iff_allZero_psub a b).symm

theorem coeffEqv_refl (a : List Q') : a ≈c a :=
  (coeffEqv_iff_polyEqv a a).2 (peqv_refl a)

theorem coeffEqv_symm {a b : List Q'} (h : a ≈c b) : b ≈c a :=
  (coeffEqv_iff_polyEqv b a).2
    (peqv_symm ((coeffEqv_iff_polyEqv a b).1 h))

theorem coeffEqv_trans {a b c : List Q'} (hab : a ≈c b) (hbc : b ≈c c) :
    a ≈c c :=
  (coeffEqv_iff_polyEqv a c).2
    (peqv_trans ((coeffEqv_iff_polyEqv a b).1 hab)
      ((coeffEqv_iff_polyEqv b c).1 hbc))

theorem coeffEqv_padd {a a' b b' : List Q'}
    (ha : a ≈c a') (hb : b ≈c b') : padd a b ≈c padd a' b' :=
  (coeffEqv_iff_polyEqv _ _).2
    (padd_congr ((coeffEqv_iff_polyEqv _ _).1 ha)
      ((coeffEqv_iff_polyEqv _ _).1 hb))

theorem coeffEqv_pscale (c : Q') {a b : List Q'} (h : a ≈c b) :
    pscale c a ≈c pscale c b := by
  apply (coeffEqv_iff_polyEqv _ _).2
  intro x
  refine Q'.eqv_trans _ (c * eval a x) _ (eval_pscale c a x) ?_
  exact Q'.eqv_trans _ (c * eval b x) _
    (Q'.mul_eqv_congr_left c _ _ (((coeffEqv_iff_polyEqv a b).1 h) x))
    (Q'.eqv_symm (eval_pscale c b x))

theorem coeffEqv_zeroCons {a b : List Q'} (h : a ≈c b) :
    (0 :: a) ≈c (0 :: b) := by
  apply (coeffEqv_iff_polyEqv _ _).2
  intro x
  show ((0 : Q') + x * eval a x).eqv (0 + x * eval b x)
  exact q_add_congr (Q'.eqv_refl 0)
    (Q'.mul_eqv_congr_left x _ _ (((coeffEqv_iff_polyEqv a b).1 h) x))

/-- Removing the lowest coefficient preserves coefficient equivalence.  This
is where the reflective `allZero` representation is essential: ordinary
extensional equality alone does not expose the tail computationally. -/
theorem coeffEqv_tail {a b : List Q'} (h : a ≈c b) : a.tail ≈c b.tail := by
  cases a with
  | nil =>
      cases b with
      | nil => exact coeffEqv_refl []
      | cons d ds =>
          unfold CoeffEqv at h ⊢
          simp only [List.tail, psub, pneg, padd, pscale, allZero, allZeroB,
            Bool.and_eq_true] at h ⊢
          exact h.2
  | cons c cs =>
      cases b with
      | nil =>
          cases cs with
          | nil => exact coeffEqv_refl []
          | cons e es =>
              unfold CoeffEqv at h ⊢
              simp only [List.tail, psub, pneg, padd, pscale, allZero, allZeroB,
                Bool.and_eq_true] at h ⊢
              exact h.2
      | cons d ds =>
          unfold CoeffEqv at h ⊢
          simp only [List.tail, psub, pneg, padd, pscale, allZero, allZeroB,
            Bool.and_eq_true] at h ⊢
          exact h.2

theorem coeffEqv_xLift {a b : List Q'} (h : a ≈c b) :
    xLift a ≈c xLift b := by
  unfold xLift
  exact coeffEqv_padd
    (coeffEqv_zeroCons (coeffEqv_pscale HalfPow.half h))
    (coeffEqv_pscale HalfPow.half (coeffEqv_tail h))

def headCoeff : List Q' -> Q'
  | [] => 0
  | a :: _ => a

theorem eval_zero_eqv_headCoeff : forall a : List Q',
    (eval a 0).eqv (headCoeff a)
  | [] => Q'.eqv_refl 0
  | a :: as => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (q_zero_mul (eval as 0)))
        (q_add_zero_eqv a)

theorem headCoeff_congr {a b : List Q'} (h : a ≈c b) :
    (headCoeff a).eqv (headCoeff b) := by
  exact Q'.eqv_trans _ (eval a 0) _
    (Q'.eqv_symm (eval_zero_eqv_headCoeff a))
    (Q'.eqv_trans _ (eval b 0) _
      (((coeffEqv_iff_polyEqv a b).1 h) 0)
      (eval_zero_eqv_headCoeff b))

theorem singleton_headCoeff_congr {a b : List Q'} (h : a ≈c b) :
    [headCoeff a] ≈c [headCoeff b] := by
  apply (coeffEqv_iff_polyEqv _ _).2
  intro x
  show (headCoeff a + x * 0).eqv (headCoeff b + x * 0)
  exact q_add_congr (headCoeff_congr h) (Q'.eqv_refl _)

def chebStep (c : Q') (a : List Q') : List Q' := padd [c] (xLift a)

theorem coeffEqv_chebStep {c d : Q'} {a b : List Q'}
    (hc : [c] ≈c [d]) (hab : a ≈c b) :
    chebStep c a ≈c chebStep d b :=
  coeffEqv_padd hc (coeffEqv_xLift hab)

private theorem zeroStep : ([] : List Q') ≈c chebStep 0 [] := by
  unfold CoeffEqv chebStep xLift
  decide

/-- The canonical Horner Chebyshev extractor respects semantic equality of
ordinary coefficient lists. -/
theorem chebExtract_coeffEqv : forall a b : List Q',
    a ≈c b -> chebExtract a ≈c chebExtract b
  | [], [], _ => coeffEqv_refl []
  | [], d :: ds, h => by
      have ht : ([] : List Q') ≈c ds := coeffEqv_tail h
      have hi : chebExtract ([] : List Q') ≈c chebExtract ds :=
        chebExtract_coeffEqv [] ds ht
      have hs : chebStep 0 (chebExtract []) ≈c
          chebStep d (chebExtract ds) :=
        coeffEqv_chebStep (singleton_headCoeff_congr h) hi
      exact coeffEqv_trans zeroStep hs
  | c :: cs, [], h => by
      have ht : cs ≈c ([] : List Q') := coeffEqv_tail h
      have hi : chebExtract cs ≈c chebExtract ([] : List Q') :=
        chebExtract_coeffEqv cs [] ht
      have hs : chebStep c (chebExtract cs) ≈c
          chebStep 0 (chebExtract []) :=
        coeffEqv_chebStep (singleton_headCoeff_congr h) hi
      exact coeffEqv_trans hs (coeffEqv_symm zeroStep)
  | c :: cs, d :: ds, h => by
      exact coeffEqv_chebStep (singleton_headCoeff_congr h)
        (chebExtract_coeffEqv cs ds (coeffEqv_tail h))

/-- **Canonical Chebyshev coefficient uniqueness on bare `QPoly`.**
Extensionally equal bare polynomials have coefficientwise-equivalent extracted
Chebyshev-U lists, including trailing-zero normalization. -/
theorem chebExtract_unique {p q : Poly} (h : PolyEqv p q) :
    chebExtract p ≈c chebExtract q :=
  chebExtract_coeffEqv p q (allZero_psub_of_polyEqv h)

/-- The vacuum coefficient extracted directly from a bare polynomial. -/
def bareVacuumHaar (p : Poly) : Q' := headCoeff (chebExtract p)

/-- The extracted vacuum coefficient is well-defined on the extensional
polynomial setoid. -/
theorem bareVacuumHaar_congr {p q : Poly} (h : PolyEqv p q) :
    (bareVacuumHaar p).eqv (bareVacuumHaar q) :=
  headCoeff_congr (chebExtract_unique h)

end YMGap.Continuum.SU2ClassPolynomialChebUniqueness

#print axioms YMGap.Continuum.SU2ClassPolynomialChebUniqueness.coeffEqv_tail
#print axioms YMGap.Continuum.SU2ClassPolynomialChebUniqueness.coeffEqv_xLift
#print axioms YMGap.Continuum.SU2ClassPolynomialChebUniqueness.chebExtract_coeffEqv
#print axioms YMGap.Continuum.SU2ClassPolynomialChebUniqueness.chebExtract_unique
#print axioms YMGap.Continuum.SU2ClassPolynomialChebUniqueness.bareVacuumHaar_congr
