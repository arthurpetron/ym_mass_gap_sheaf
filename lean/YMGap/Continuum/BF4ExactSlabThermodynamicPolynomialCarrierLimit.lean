/-
# Constructed ORIGINAL carrier limits of uniformly Cauchy polynomials

A supplied polynomial sequence with an explicit UNIFORM [0,1] modulus
produces actual original Cauchy representatives and an outer squared-
distance modulus. The existing represented-row completeness constructs
the limit, its representative and rate. No representative choice, supplied
diagonal resolution or arbitrary-quotient completeness is assumed.

The next module supplies these inputs from proved Bernstein approximation.
All physical nome/spacing parameters remain fixed.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference
import YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows

namespace YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedGeometry
open YMGap.Continuum.BF4ExactSlabThermodynamicNormalizedProbe
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinMomentConvergence (rat_mono)
open YMGap.Continuum.BF4ExactSlabThermodynamicBernsteinPolynomialMoments (polynomialVector)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialDifference
open YMGap.Continuum.BF4ExactSlabThermodynamicCauchyRows

local notation "rat" q => Quotient.mk crealSetoid (ofQ' q)

/-- Square-root-free conversion from squared-distance to scalar tolerance. -/
def squareTolerance (epsilon : Q') : Q' := Q'.min' epsilon 1

theorem squareTolerance_pos (epsilon : Q') (he : (0 : Q')<epsilon) :
    (0 : Q')<squareTolerance epsilon := by
  unfold squareTolerance Q'.min'
  split
  · exact he
  · decide

theorem squareTolerance_budget (epsilon : Q') (he : (0 : Q')<epsilon) :
    squareTolerance epsilon*squareTolerance epsilon≤epsilon :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ Q'.min_le_right (Q'.le_of_lt (squareTolerance_pos epsilon he)))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) Q'.min_le_left)

section UniformSequence

variable (p : Nat → QPoly.Poly) (M : Q' → Nat)
  (h : ∀ epsilon : Q',(0 : Q')<epsilon → ∀ m n,M epsilon≤m → M epsilon≤n →
    ∀ t : Q',(0 : Q')≤t → t≤1 →
      QPoly.eval (p m) t≤QPoly.eval (p n) t+epsilon ∧
      QPoly.eval (p n) t≤QPoly.eval (p m) t+epsilon)

def polynomialRows : CauchyRows where
  row := fun n => probeRepresentative (p n)
  modulus := fun epsilon => M (squareTolerance epsilon)
  isCauchy := by
    intro epsilon he m n hm hn
    simp only [probeRepresentative_pin]
    have hd := squareTolerance_pos epsilon he
    exact RCle_trans (probe_distance_two_sided (p m) (p n) _ (Q'.le_of_lt hd)
      (h _ hd m n hm hn)) (rat_mono (squareTolerance_budget epsilon he))

theorem polynomialRows_pin (n : Nat) :
    rowPoint (polynomialRows p M h) n=polynomialVector unitProbe.val (p n) 0 := probeRepresentative_pin (p n)

def polynomialLimitRepresentative : seminorm.Cauchy := diagonalCauchy (polynomialRows p M h)

def polynomialLimit : Completion := rowLimit (polynomialRows p M h)

def polynomialLimitModulus : Q' → Nat := rowLimitRate (polynomialRows p M h)

theorem polynomialLimit_pin :
    Quotient.mk seminorm.completionSetoid (polynomialLimitRepresentative p M h)=polynomialLimit p M h := rfl

theorem polynomialLimit_bound (epsilon : Q') (he : (0 : Q')<epsilon)
    (n : Nat) (hn : polynomialLimitModulus p M h epsilon≤n) :
    RCle (completedDist (polynomialVector unitProbe.val (p n) 0) (polynomialLimit p M h)) (rat epsilon) := by
  have hb := rowLimit_bound (polynomialRows p M h) epsilon he n hn
  rw [polynomialRows_pin] at hb
  exact hb

/-- The original representative AND outer convergence rate are returned. -/
def polynomialLimitCertificate :
    Σ' X : seminorm.Cauchy,
      {rate : Q' → Nat // ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
        RCle (completedDist (polynomialVector unitProbe.val (p n) 0)
          (Quotient.mk seminorm.completionSetoid X)) (rat epsilon)} :=
  ⟨polynomialLimitRepresentative p M h,⟨polynomialLimitModulus p M h,polynomialLimit_bound p M h⟩⟩

theorem polynomialLimit_unique (L : Completion) (rate : Q' → Nat)
    (hL : ∀ epsilon : Q',(0 : Q')<epsilon → ∀ n,rate epsilon≤n →
      RCle (completedDist (polynomialVector unitProbe.val (p n) 0) L) (rat epsilon)) :
    polynomialLimit p M h=L := by
  apply rowLimit_eq_of_bound (polynomialRows p M h) L rate
  intro epsilon he n hn
  rw [polynomialRows_pin]
  exact hL epsilon he n hn

end UniformSequence

theorem constant_uniform (q : QPoly.Poly) (epsilon : Q') (he : (0 : Q')<epsilon)
    (_m _n : Nat) (_hm : 0≤_m) (_hn : 0≤_n) (t : Q') (_ht : (0 : Q')≤t) (_h1 : t≤1) :
    QPoly.eval q t≤QPoly.eval q t+epsilon ∧ QPoly.eval q t≤QPoly.eval q t+epsilon :=
  ⟨Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he),Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)⟩

theorem polynomialLimit_constant (q : QPoly.Poly) :
    polynomialLimit (fun _ => q) (fun _ => 0) (constant_uniform q)=polynomialVector unitProbe.val q 0 := by
  apply polynomialLimit_unique _ _ _ _ (fun _ => 0)
  intro epsilon he n _
  have hz := (completedDist_zero_iff _ _).mpr (Eq.refl (polynomialVector unitProbe.val q 0))
  rw [hz]
  exact rat_mono (Q'.le_of_lt he)

end YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.squareTolerance
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.squareTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.squareTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.polynomialRows
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.polynomialRows_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.polynomialLimitRepresentative
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.polynomialLimit
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.polynomialLimitModulus
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.polynomialLimit_pin
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.polynomialLimit_bound
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.polynomialLimitCertificate
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.polynomialLimit_unique
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.constant_uniform
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialCarrierLimit.polynomialLimit_constant
