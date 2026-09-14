/-
# Norm and SAME moment-pairing limits for ORIGINAL Bernstein symbol vectors

Positive binomial weights and their partition of unity bound every
Bernstein polynomial by the supplied symbol bound. The original polynomial
probe norm estimate passes to the constructed original carrier limit.
Pairings of two symbol vectors are limits, with a computed two-slot rate,
of the SAME original moment functional on products of Bernstein polynomials.
The scalar representative and its Cauchy modulus are retained as data.

This supplies norm and pairing laws for symbol vectors at fixed SU(2) nome
and spacing. Symbol-equivalence compatibility, full operator calculus,
physical-scale spectral control and continuum Yang--Mills remain open.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit
import YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe

namespace YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BernsteinVariance (bmono)
open YMGap.Continuum.BinomialTheorem (partition_of_unity)
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialFunctional (momentFunctional)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialProbeNorm (probe_inner_product probe_norm_bound)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference (probeRepresentative_pin)
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier
open YMGap.Continuum.BF4ExactSlabThermodynamicRowPairingLimit

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

/-- Uniform in degree and rational spectral point, at the symbol's declared bound. -/
theorem bernstein_abs_bound (F : CtsMod) (n : Nat) (t : Q')
    (ht : (0 : Q')≤t) (h1 : t≤1) : Q'.abs (bernstein F n t)≤F.bound := by
  have hterm : ∀ k,Q'.abs (F.f (smp n k)*bmono n t (1-t) k)≤F.bound*bmono n t (1-t) k := by
    intro k
    have hb := bmono_nonneg n t ht h1 k
    have h := ExpNeg.abs_mul_le (F.f (smp n k)) (bmono n t (1-t) k)
    rw [abs_of_nonneg hb] at h
    exact Q'.le_trans' _ _ _ h (Q'.mul_le_mul_of_nonneg_right _ _ _ (F.f_le _) hb)
  apply Q'.le_trans' _ _ _ (abs_finSum_le _ (n+1))
  apply Q'.le_trans' _ _ _ (ExpNeg.finSum_le_finSum_of_termwise _ _ hterm (n+1))
  apply Q'.le_of_eqv
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (const_mul_finSum _ F.bound (n+1)))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (partition_of_unity n t))
      (Q'.mul_one_eqv F.bound))

theorem bernsteinPoly_abs_bound (F : CtsMod) (n : Nat) (t : Q')
    (ht : (0 : Q')≤t) (h1 : t≤1) : Q'.abs (QPoly.eval (bernsteinPoly F n) t)≤F.bound :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (eval_bernsteinPoly F n t)))
    (bernstein_abs_bound F n t ht h1)

theorem bernsteinRow_pin (F : CtsMod) (V : MonotoneOmegaVanishing F) (n : Nat) :
    rowPoint (bernsteinRows F V) n=polynomialVector unitProbe.val (bernsteinPoly F n) 0 :=
  probeRepresentative_pin _

/-- The constructed original symbol vector, not a supplied diagonal model. -/
theorem continuousProbe_norm_bound (F : CtsMod) (V : MonotoneOmegaVanishing F) :
    RCle (completedInner (continuousProbe F V) (continuousProbe F V)) (rat (F.bound*F.bound)) := by
  apply rowLimit_norm_bound (bernsteinRows F V)
  intro n
  rw [bernsteinRow_pin]
  exact probe_norm_bound _ _ (bound_nonneg F) (bernsteinPoly_abs_bound F n)

def momentPairingModulus (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) : Q' → Nat :=
  pairingModulus (bernsteinRows F V) (bernsteinRows G W)

/-- The approximating scalars use the SAME original polynomial moment functional. -/
theorem momentPairing_bound (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G)
    (epsilon : Q') (he : (0 : Q')<epsilon) (n : Nat)
    (hn : momentPairingModulus F V G W epsilon≤n) :
    RCle (momentFunctional (QPoly.pmul (bernsteinPoly F n) (bernsteinPoly G n)))
      (RCadd (completedInner (continuousProbe F V) (continuousProbe G W)) (rat epsilon)) ∧
    RCle (completedInner (continuousProbe F V) (continuousProbe G W))
      (RCadd (momentFunctional (QPoly.pmul (bernsteinPoly F n) (bernsteinPoly G n))) (rat epsilon)) := by
  have h := row_pairing_bound (bernsteinRows F V) (bernsteinRows G W) epsilon he n hn
  rw [bernsteinRow_pin,bernsteinRow_pin,probe_inner_product] at h
  exact h

def momentPairingRepresentative (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) : CReal :=
  pairingRepresentative (bernsteinRows F V) (bernsteinRows G W)

theorem momentPairingRepresentative_pin (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) :
    Quotient.mk crealSetoid (momentPairingRepresentative F V G W)=
      completedInner (continuousProbe F V) (continuousProbe G W) := rfl

def momentPairingCertificate (F : CtsMod) (V : MonotoneOmegaVanishing F)
    (G : CtsMod) (W : MonotoneOmegaVanishing G) :
    Σ' s : CReal, Σ' _cs : QCauchy s.approx,
      {rate : Q' → Nat // Quotient.mk crealSetoid s=completedInner (continuousProbe F V) (continuousProbe G W) ∧
        ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
          RCle (momentFunctional (QPoly.pmul (bernsteinPoly F n) (bernsteinPoly G n)))
            (RCadd (Quotient.mk crealSetoid s) (rat epsilon)) ∧
          RCle (Quotient.mk crealSetoid s)
            (RCadd (momentFunctional (QPoly.pmul (bernsteinPoly F n) (bernsteinPoly G n))) (rat epsilon))} :=
  ⟨momentPairingRepresentative F V G W,
    pairingRepresentativeCauchy (bernsteinRows F V) (bernsteinRows G W),
    ⟨momentPairingModulus F V G W,⟨rfl,momentPairing_bound F V G W⟩⟩⟩

/-- A fully supplied instance; nonzeroness of this particular vector is not asserted. -/
theorem cuspVector_norm_bound :
    RCle (completedInner BF4ExactSlabThermodynamicCuspProbe.cuspVector
      BF4ExactSlabThermodynamicCuspProbe.cuspVector) (rat 1) :=
  RCle_trans (continuousProbe_norm_bound BF4ExactSlabThermodynamicCuspProbe.cuspSymbol
    BF4ExactSlabThermodynamicCuspProbe.cuspVanishing)
    (leEv_le_ofQ'_of_approx_le (fun _ => by change (1 : Q')*1≤1; decide))

end YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing.bernstein_abs_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing.bernsteinPoly_abs_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing.bernsteinRow_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing.continuousProbe_norm_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing.momentPairingModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing.momentPairing_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing.momentPairingRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing.momentPairingRepresentative_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing.momentPairingCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinLimitPairing.cuspVector_norm_bound
