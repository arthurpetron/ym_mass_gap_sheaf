/-
# ORIGINAL symbol vectors depend only on the symbol on [0,1]

The comparison uses the two uniform Bernstein approximation rates, not
equality of sample presentations or a supplied diagonal resolution. It
therefore permits different bounds, continuity data and values outside
[0,1]. If a symbol agrees with a polynomial there, its constructed vector
is exactly that polynomial of the SAME original two-step transfer applied
to the original normalized probe. Nome and spacing remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing

namespace YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedApproximation
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference (probe_distance_two_sided)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit
  (squareTolerance squareTolerance_pos squareTolerance_budget)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing (bernsteinRow_pin)

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

theorem rowLimits_eq_of_close (R S : CauchyRows) (rate : Q' → Nat)
    (h : ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
      RCle (completedDist (rowPoint R n) (rowPoint S n)) (rat epsilon)) : rowLimit R=rowLimit S := by
  apply completed_eq_of_small
  intro epsilon he
  let d := quarter (quarter epsilon)
  have hd : (0 : Q')<d := quarter_pos (quarter_pos he)
  let n := max (max (rowLimitRate R d) (rowLimitRate S d)) (rate d)
  have hR := rowLimit_bound R d hd n (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have hS := rowLimit_bound S d hd n (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
  rw [completedDist_symm] at hR
  exact completedDist_three_segment _ _ _ _ epsilon he hR (h d hd n (Nat.le_max_right _ _)) hS

theorem bernstein_symbol_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat)
    (hn : (symbolErrorModulus F V).stage epsilon≤n) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (bernsteinPoly F n) t≤F.f t+epsilon ∧
    F.f t≤QPoly.eval (bernsteinPoly F n) t+epsilon := by
  have h := (symbolErrorModulus F V).twobound epsilon he n hn t ht h1
  have e := eval_bernsteinPoly F n t
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv e) h.1,
    Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv e))⟩

theorem half_error_trans (a b c epsilon : Q')
    (h1 : a≤b+HalfPow.half*epsilon) (h2 : b≤c+HalfPow.half*epsilon) : a≤c+epsilon :=
  Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ h2)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon)))))

def comparisonModulus (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (epsilon : Q') : Nat :=
  max ((symbolErrorModulus F V).stage (HalfPow.half*epsilon))
    ((symbolErrorModulus G W).stage (HalfPow.half*epsilon))

theorem same_symbol_bernstein_close (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G)
    (hfg : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (F.f t) (G.f t))
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat)
    (hn : comparisonModulus F V G W epsilon≤n) (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (bernsteinPoly F n) t≤QPoly.eval (bernsteinPoly G n) t+epsilon ∧
    QPoly.eval (bernsteinPoly G n) t≤QPoly.eval (bernsteinPoly F n) t+epsilon := by
  have hd := ExpNeg.half_mul_pos epsilon he
  have hF := bernstein_symbol_bound F V _ hd n (Nat.le_trans (Nat.le_max_left _ _) hn) t ht h1
  have hG := bernstein_symbol_bound G W _ hd n (Nat.le_trans (Nat.le_max_right _ _) hn) t ht h1
  exact ⟨half_error_trans _ _ _ epsilon hF.1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv (hfg t ht h1)) hG.2),
    half_error_trans _ _ _ epsilon hG.1 (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hfg t ht h1)) hF.2)⟩

/-- Equivalent only on the spectral interval; bounds/moduli/outside values may differ. -/
theorem continuousProbe_congr (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G)
    (hfg : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (F.f t) (G.f t)) :
    continuousProbe F V=continuousProbe G W := by
  apply rowLimits_eq_of_close (bernsteinRows F V) (bernsteinRows G W)
    (fun epsilon => comparisonModulus F V G W (squareTolerance epsilon))
  intro epsilon he n hn
  rw [bernsteinRow_pin,bernsteinRow_pin]
  have hd := squareTolerance_pos epsilon he
  exact RCle_trans (probe_distance_two_sided _ _ _ (Q'.le_of_lt hd)
    (same_symbol_bernstein_close F V G W hfg _ hd n hn))
    (leEv_le_ofQ'_of_approx_le (fun _ => squareTolerance_budget epsilon he))

/-- Agreement with a polynomial on [0,1] recovers its ACTUAL original probe vector. -/
theorem continuousProbe_eq_polynomial (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (p : QPoly.Poly) (hp : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (F.f t) (QPoly.eval p t)) :
    continuousProbe F V=polynomialVector unitProbe.val p 0 := by
  apply continuousProbe_unique F V _ (fun epsilon => (symbolErrorModulus F V).stage (squareTolerance epsilon))
  intro epsilon he n hn
  have hd := squareTolerance_pos epsilon he
  have hpoly : ∀ t : Q',(0 : Q')≤t → t≤1 →
      QPoly.eval (bernsteinPoly F n) t≤QPoly.eval p t+squareTolerance epsilon ∧
      QPoly.eval p t≤QPoly.eval (bernsteinPoly F n) t+squareTolerance epsilon := by
    intro t ht h1
    have h := bernstein_symbol_bound F V _ hd n hn t ht h1
    exact ⟨Q'.le_trans' _ _ _ h.1 (Q'.add_le_add_right _ _ _ (Q'.le_of_eqv (hp t ht h1))),
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hp t ht h1)) h.2⟩
  exact RCle_trans (probe_distance_two_sided _ _ _ (Q'.le_of_lt hd) hpoly)
    (leEv_le_ofQ'_of_approx_le (fun _ => squareTolerance_budget epsilon he))

end YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility.rowLimits_eq_of_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility.bernstein_symbol_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility.half_error_trans
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility.comparisonModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility.same_symbol_bernstein_close
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility.continuousProbe_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility.continuousProbe_eq_polynomial
