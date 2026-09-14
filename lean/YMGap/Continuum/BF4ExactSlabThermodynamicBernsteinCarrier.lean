/-
# Bernstein symbols produce ACTUAL ORIGINAL completed probe vectors

The existing constructive bounded continuous symbol and its monotone
vanishing modulus generate Bernstein polynomials with a single rate
UNIFORM over [0,1]. Their actual original probe vectors have constructed
Cauchy rows and a completed limit with explicit rate. The limit is unique
and independent of the chosen modulus for the same symbol.

Only pure rational approximation is reused. No diagonal resolution or
operator image-Cauchy input is supplied. This constructs symbol vectors
on the original cyclic sector, not a full operator calculus, spectral
measure, continuous-time generator or continuum Yang--Mills theory.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit
import YMGap.Continuum.BernsteinStageData

namespace YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinModulusClose
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

def symbolErrorModulus (F : CtsMod) (V : MonotoneOmegaVanishing F) : ErrorModulus F :=
  bernsteinErrorModulus F (bernsteinStageData F V)

def bernsteinModulus (F : CtsMod) (V : MonotoneOmegaVanishing F) (epsilon : Q') : Nat :=
  (symbolErrorModulus F V).stage (HalfPow.half*epsilon)

/-- One computed rate controls ALL rational spectral points, not just one. -/
theorem bernstein_uniformCauchy (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (epsilon : Q') (he : (0 : Q')<epsilon) (m n : Nat)
    (hm : bernsteinModulus F V epsilon≤m) (hn : bernsteinModulus F V epsilon≤n)
    (t : Q') (ht : (0 : Q')≤t) (h1 : t≤1) :
    QPoly.eval (bernsteinPoly F m) t≤QPoly.eval (bernsteinPoly F n) t+epsilon ∧
    QPoly.eval (bernsteinPoly F n) t≤QPoly.eval (bernsteinPoly F m) t+epsilon :=
  (bernsteinPolySpectralCauchy F (symbolErrorModulus F V) t ht h1).cauchy epsilon he m n hm hn

def bernsteinRows (F : CtsMod) (V : MonotoneOmegaVanishing F) : CauchyRows :=
  polynomialRows (bernsteinPoly F) (bernsteinModulus F V) (bernstein_uniformCauchy F V)

def continuousProbeRepresentative (F : CtsMod) (V : MonotoneOmegaVanishing F) : seminorm.Cauchy :=
  diagonalCauchy (bernsteinRows F V)

def continuousProbe (F : CtsMod) (V : MonotoneOmegaVanishing F) : Completion := rowLimit (bernsteinRows F V)

def continuousProbeModulus (F : CtsMod) (V : MonotoneOmegaVanishing F) : Q' → Nat := rowLimitRate (bernsteinRows F V)

theorem continuousProbe_pin (F : CtsMod) (V : MonotoneOmegaVanishing F) :
    Quotient.mk seminorm.completionSetoid (continuousProbeRepresentative F V)=continuousProbe F V := rfl

theorem continuousProbe_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat) (hn : continuousProbeModulus F V epsilon≤n) :
    RCle (completedDist (polynomialVector unitProbe.val (bernsteinPoly F n) 0) (continuousProbe F V)) (rat epsilon) :=
  polynomialLimit_bound (bernsteinPoly F) (bernsteinModulus F V) (bernstein_uniformCauchy F V) epsilon he n hn

def continuousProbeCertificate (F : CtsMod) (V : MonotoneOmegaVanishing F) :
    Σ' X : seminorm.Cauchy,
      {rate : Q' → Nat // ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
        RCle (completedDist (polynomialVector unitProbe.val (bernsteinPoly F n) 0)
          (Quotient.mk seminorm.completionSetoid X)) (rat epsilon)} :=
  ⟨continuousProbeRepresentative F V,⟨continuousProbeModulus F V,continuousProbe_bound F V⟩⟩

theorem continuousProbe_unique (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (L : Completion) (rate : Q' → Nat)
    (hL : ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
      RCle (completedDist (polynomialVector unitProbe.val (bernsteinPoly F n) 0) L) (rat epsilon)) :
    continuousProbe F V=L :=
  polynomialLimit_unique (bernsteinPoly F) (bernsteinModulus F V) (bernstein_uniformCauchy F V) L rate hL

theorem continuousProbe_modulus_independent (F : CtsMod) (V W : MonotoneOmegaVanishing F) :
    continuousProbe F V=continuousProbe F W := rowLimit_independent _ _ (fun _ => rfl)

end YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier.symbolErrorModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier.bernsteinModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier.bernstein_uniformCauchy
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier.bernsteinRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier.continuousProbeRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier.continuousProbe
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier.continuousProbeModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier.continuousProbe_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier.continuousProbe_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier.continuousProbeCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier.continuousProbe_unique
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier.continuousProbe_modulus_independent
