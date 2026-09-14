/-
# Original continuous-symbol action respects state and symbol equivalence

The action depends only on the represented ORIGINAL state and on the
symbol's rational values on [0,1], not on representation or modulus data.
Agreement with a polynomial recovers the pre-existing polynomial operator.
Acting on the original normalized probe recovers its existing symbol vector.
A fully supplied cusp-on-cusp action certificate is constructed as an
instance; no nonzeroness conclusion is inferred from symbol nonconstancy.

Represented-sector closure and the full continuous operator algebra remain
subsequent obligations. These fixed-nome/spacing results do not close the
full-carrier, physical spectral, canonical or continuum Yang--Mills bridges.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction
import YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility

namespace YMGap.Continuum.BF4ExactSlabThermodynamicContinuousActionCompatibility

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialOperator
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing (bernsteinRow_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicSymbolCompatibility
open YMGap.Continuum.BF4ExactSlabThermodynamicCyclicPresentation
open YMGap.Continuum.BF4ExactSlabThermodynamicContinuousAction
open YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe (cuspSymbol cuspVanishing)

/-- Independence of all input row/representative/polynomial data for the SAME original state. -/
theorem symbolAction_input_congr (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (X Y : CyclicPresentation) (h : state X=state Y) : symbolAction F V X=symbolAction F V Y := by
  apply rowLimit_independent
  intro n
  rw [symbolRows_pin,symbolRows_pin,h]

/-- Only rational [0,1] values are relevant; symbol bounds and continuity data may differ. -/
theorem symbolAction_symbol_congr (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X : CyclicPresentation)
    (hfg : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (F.f t) (G.f t)) :
    symbolAction F V X=symbolAction G W X := by
  apply rowLimits_eq_of_close (symbolRows F V X) (symbolRows G W X)
    (fun epsilon => comparisonModulus F V G W (approximationTolerance X epsilon))
  intro epsilon he n hn
  rw [symbolRows_pin,symbolRows_pin]
  exact polynomial_close X _ _ epsilon he
    (same_symbol_bernstein_close F V G W hfg _ (approximationTolerance_pos X he) n hn)

theorem symbolAction_congr (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) (X Y : CyclicPresentation)
    (hxy : state X=state Y)
    (hfg : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (F.f t) (G.f t)) :
    symbolAction F V X=symbolAction G W Y :=
  (symbolAction_symbol_congr F V G W X hfg).trans (symbolAction_input_congr G W X Y hxy)

theorem symbolAction_modulus_independent (F : CtsMod) (V W : MonotoneOmegaVanishing F)
    (X : CyclicPresentation) : symbolAction F V X=symbolAction F W X :=
  symbolAction_symbol_congr F V F W X (fun t _ _ => Q'.eqv_refl (F.f t))

/-- Polynomial recovery is an equality with the SAME already-defined original operator. -/
theorem symbolAction_eq_polynomial (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (X : CyclicPresentation) (p : QPoly.Poly)
    (hp : ∀ t : Q',(0 : Q')≤t → t≤1 → Q'.eqv (F.f t) (QPoly.eval p t)) :
    symbolAction F V X=polynomialOperator p (state X) := by
  apply rowLimit_eq_of_bound _ _
    (fun epsilon => (symbolErrorModulus F V).stage (approximationTolerance X epsilon))
  intro epsilon he n hn
  rw [symbolRows_pin]
  apply polynomial_close X _ _ epsilon he
  intro t ht h1
  have h := bernstein_symbol_bound F V _ (approximationTolerance_pos X he) n hn t ht h1
  exact ⟨Q'.le_trans' _ _ _ h.1 (Q'.add_le_add_right _ _ _ (Q'.le_of_eqv (hp t ht h1))),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (hp t ht h1)) h.2⟩

/-- The continuous action extends the ORIGINAL symbol-vector constructor on the norm-one probe. -/
theorem symbolAction_probe (F : CtsMod) (V : MonotoneOmegaVanishing F) :
    symbolAction F V (ofPolynomial [1])=continuousProbe F V := by
  apply rowLimit_independent
  intro n
  rw [symbolRows_pin,bernsteinRow_pin,state_ofPolynomial,operator_one]
  rfl

/-- All function and input representation data are supplied; the result need not be nonzero. -/
def cuspActionCertificate := symbolActionCertificate cuspSymbol cuspVanishing (ofSymbol cuspSymbol cuspVanishing)

end YMGap.Continuum.BF4ExactSlabThermodynamicContinuousActionCompatibility

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousActionCompatibility.symbolAction_input_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousActionCompatibility.symbolAction_symbol_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousActionCompatibility.symbolAction_congr
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousActionCompatibility.symbolAction_modulus_independent
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousActionCompatibility.symbolAction_eq_polynomial
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousActionCompatibility.symbolAction_probe
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicContinuousActionCompatibility.cuspActionCertificate
