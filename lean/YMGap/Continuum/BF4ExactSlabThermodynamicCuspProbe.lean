/-
# A concrete nonconstant bounded symbol in the ORIGINAL carrier construction

The rational cusp f(t)=min(|t-1/2|,1) is globally bounded and 1-Lipschitz.
Its continuity modulus and monotone vanishing selector are constructed,
not supplied. The original Bernstein carrier construction therefore gives
an actual completed symbol vector and a representative/rate certificate.

The symbol is proved nonconstant. This does not assert that its original
symbol vector is nonzero, nor give full spectral calculus or continuum YM.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier

namespace YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BernsteinUniformConvergence
open YMGap.Continuum.BernsteinSequenceWrap
open YMGap.Continuum.BernsteinStageData
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinCarrier
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)

theorem cap_step (a b e : Q') (he : (0 : Q')≤e) (h : a≤b+e) :
    Q'.min' a 1≤Q'.min' b 1+e := by
  unfold Q'.min'
  by_cases ha : a≤1 <;> by_cases hb : b≤1
  · rw [if_pos ha,if_pos hb]; exact h
  · rw [if_pos ha,if_neg hb]
    exact Q'.le_trans' _ _ _ ha (Q'.add_le_self_of_nonneg _ _ he)
  · rw [if_neg ha,if_pos hb]
    exact Q'.le_trans' _ _ _ (Q'.le_of_not_le ha) h
  · rw [if_neg ha,if_neg hb]; exact Q'.add_le_self_of_nonneg _ _ he

theorem shifted_difference (s t c : Q') : Q'.eqv ((s + -c) + -(t + -c)) (s + -t) :=
  poly_identity_of_normal_eq
    (.add (.add (.var 0) (.neg (.var 2))) (.neg (.add (.var 1) (.neg (.var 2)))))
    (.add (.var 0) (.neg (.var 1))) (by decide)
    (fun | 0 => s | 1 => t | _ => c)

theorem shifted_abs_step (s t c : Q') :
    Q'.abs (s + -c)≤Q'.abs (t + -c)+Q'.abs (s + -t) :=
  Q'.le_trans' _ _ _ (Q'.abs_le_abs_add_abs_sub _ _)
    (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ (Q'.abs_eqv_congr (shifted_difference s t c))))

def cusp (t : Q') : Q' := Q'.min' (Q'.abs (t + -HalfPow.half)) 1

theorem cusp_nonnegative (t : Q') : (0 : Q')≤cusp t :=
  Q'.zero_le_min _ _ (Q'.abs_nonneg _) Q'.zero_le_one

theorem cusp_bound (t : Q') : Q'.abs (cusp t)≤1 := by
  rw [abs_of_nonneg (cusp_nonnegative t)]
  exact Q'.min_le_right

theorem cusp_lipschitz (s t : Q') : Q'.abs (cusp s + -cusp t)≤Q'.abs (s + -t) := by
  have h1 := cap_step _ _ _ (Q'.abs_nonneg _) (shifted_abs_step s t HalfPow.half)
  have hrev := Q'.le_trans' _ _ _ (shifted_abs_step t s HalfPow.half)
    (Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ (ExpNeg.abs_sub_comm t s)))
  exact abs_sub_le_of_bounds h1 (cap_step _ _ _ (Q'.abs_nonneg _) hrev)

def cuspSymbol : CtsMod where
  f := cusp
  bound := 1
  ω := Q'.abs
  f_le := cusp_bound
  ω_nn := Q'.abs_nonneg
  mod := fun s t delta h => Q'.le_trans' _ _ _ (cusp_lipschitz s t)
    (Q'.le_trans' _ _ _ h (Q'.le_abs_self delta))

def cuspVanishing : MonotoneOmegaVanishing cuspSymbol where
  delta := fun epsilon => epsilon
  mono := fun _ _ h => h
  pos := fun _ h => h
  small := by
    intro epsilon he
    change Q'.abs epsilon≤epsilon
    rw [abs_of_nonneg (Q'.le_of_lt he)]
    exact Q'.le_refl' _

theorem cusp_at_zero : Q'.eqv (cusp 0) HalfPow.half := by decide

theorem cusp_at_midpoint : Q'.eqv (cusp HalfPow.half) 0 := by decide

theorem cusp_nonconstant : ¬Q'.eqv (cusp 0) (cusp HalfPow.half) := by decide

def cuspVector : Completion := continuousProbe cuspSymbol cuspVanishing

def cuspVectorRepresentative : seminorm.Cauchy := continuousProbeRepresentative cuspSymbol cuspVanishing

def cuspVectorModulus : Q' → Nat := continuousProbeModulus cuspSymbol cuspVanishing

theorem cuspVector_bound (epsilon : Q') (he : (0 : Q')<epsilon)
    (n : Nat) (hn : cuspVectorModulus epsilon≤n) :
    RCle (completedDist (polynomialVector unitProbe.val (bernsteinPoly cuspSymbol n) 0) cuspVector)
      (Quotient.mk crealSetoid (ofQ' epsilon)) := continuousProbe_bound cuspSymbol cuspVanishing epsilon he n hn

def cuspVectorCertificate :
    Σ' X : seminorm.Cauchy,
      {rate : Q' → Nat // ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
        RCle (completedDist (polynomialVector unitProbe.val (bernsteinPoly cuspSymbol n) 0)
          (Quotient.mk seminorm.completionSetoid X)) (Quotient.mk crealSetoid (ofQ' epsilon))} :=
  continuousProbeCertificate cuspSymbol cuspVanishing

end YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cap_step
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.shifted_difference
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.shifted_abs_step
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cusp
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cusp_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cusp_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cusp_lipschitz
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cuspSymbol
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cuspVanishing
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cusp_at_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cusp_at_midpoint
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cusp_nonconstant
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cuspVector
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cuspVectorRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cuspVectorModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cuspVector_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicCuspProbe.cuspVectorCertificate
