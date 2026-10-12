/-
# Coordinate and rational-row Stein identities for the finite Gaussian evaluator

This file uses the EXISTING `finiteProductGaussian N` on `RatPoly`. It
integrates the first N independent standard Gaussian coordinates. Exponents
at indices >=N are ignored, equivalently those formal variables are evaluated
at one. This scalar functional does NOT preserve unevaluated tail coefficients.
Coordinate IBP is asserted only for i<N, but for every finite polynomial p,
with no degree restriction, support assumption, or assumed moment law.

Consumer: explicit rational curvature/observation rows in the finite Gaussian
reference trace-source comparison. The computed linear-row Stein identity is
the contraction producer needed before the general degree-four/six Wick join.
The next proof applies row Stein twice to the literal radial quartic, then
contracts its second directional derivative with the computed row Gram data;
that covariance identity is not asserted by the IBP statements alone.
That correlated three-color quartic/quadratic covariance join, the actual
transverse mode coefficients and their approximation moduli, and the original
compact-Haar/section/source/OLD-center comparison remain separate obligations.

No new Gaussian functional, classical axiom, `sorry`, `native_decide`, or
assumption bundle is introduced.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity
import YMGap.Continuum.SU2QuaternionRatPolyDifferential

namespace YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarRationalCanonicalizer
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP
open YMGap.Continuum.SU2QuaternionFiniteProductGaussianPositivity

local infix:50 " ≈ " => Q'.eqv

/-- The existing evaluator is exactly its coefficient-times-moment probe. -/
theorem finiteProductGaussian_probe (N : Nat) : ∀ p : RatPoly,
    finiteProductGaussian N p = ratWeightedSum (finiteGaussianMono N) p
  | [] => rfl
  | term :: p => by
      change term.2*finiteGaussianMono N term.1 + finiteProductGaussian N p =
        term.2*finiteGaussianMono N term.1 + ratWeightedSum (finiteGaussianMono N) p
      rw [finiteProductGaussian_probe N p]

/-- Coefficient equality transports the SAME finite Gaussian evaluation. -/
theorem finiteProductGaussian_coeffEqv (N : Nat) {p q : RatPoly}
    (h : RatPolyCoeffEqv p q) : finiteProductGaussian N p ≈ finiteProductGaussian N q := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact h (finiteGaussianMono N)

private theorem finiteGaussianMono_ext (N : Nat) (a b : List Nat)
    (h : ∀ i, i<N → exponentAt a i = exponentAt b i) :
    finiteGaussianMono N a = finiteGaussianMono N b := by
  induction N generalizing a b with
  | zero => rfl
  | succ N ih =>
      change gaussianMoment1 (exponentAt a N)*finiteGaussianMono N a =
        gaussianMoment1 (exponentAt b N)*finiteGaussianMono N b
      rw [h N (by omega), ih a b (fun i hi => h i (by omega))]

private theorem exponentAt_lower (i k : Nat) (m : List Nat) :
    exponentAt (lowerExponentAt i m) k =
      if k=i then exponentAt m k-1 else exponentAt m k := by
  induction i generalizing k m with
  | zero =>
      cases m with
      | nil =>
          change (0 : Nat) = if k=0 then 0-1 else 0
          cases Nat.decEq k 0 with
          | isTrue h => rw [if_pos h]
          | isFalse h => rw [if_neg h]
      | cons a m =>
          cases k with
          | zero => rfl
          | succ k => rfl
  | succ i ih =>
      cases m with
      | nil =>
          change (0 : Nat) = if k=Nat.succ i then 0-1 else 0
          cases Nat.decEq k (Nat.succ i) with
          | isTrue h => rw [if_pos h]
          | isFalse h => rw [if_neg h]
      | cons a m =>
          cases k with
          | zero => rfl
          | succ k =>
              change exponentAt (lowerExponentAt i m) k =
                if Nat.succ k=Nat.succ i then exponentAt m k-1 else exponentAt m k
              cases Nat.decEq k i with
              | isTrue h =>
                  subst k
                  rw [if_pos rfl]
                  have htail := ih i m
                  rw [if_pos rfl] at htail
                  exact htail
              | isFalse h =>
                  have hsucc : Nat.succ k ≠ Nat.succ i := fun heq => h (Nat.succ.inj heq)
                  rw [if_neg hsucc]
                  have htail := ih k m
                  rw [if_neg h] at htail
                  exact htail

private theorem moment1_stein (e : Nat) :
    gaussianMoment1 (e+1) ≈ Q'.ofNat e * gaussianMoment1 (e-1) := by
  cases e with
  | zero =>
      exact Q'.eqv_trans _ _ _ gaussianMoment1_one (Q'.eqv_symm (Q'.zero_mul_eqv _))
  | succ e =>
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_sub_cancel] using
        gaussianMoment1_shift e

private theorem swap_scalar (a b c : Q') : a*(b*c) ≈ b*(a*c) :=
  poly_identity_of_normal_eq
    (.mul (.var 0) (.mul (.var 1) (.var 2)))
    (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
    (fun | 0 => a | 1 => b | _ => c)

/-- Dimension-uniform monomial Stein recurrence, including short exponent
lists and arbitrary exponents outside the integrated coordinate prefix. -/
theorem finiteGaussianMono_coordinate_stein (N i : Nat) (hi : i<N) (m : List Nat) :
    finiteGaussianMono N (monoMul (varMono i) m) ≈
      derivativeProbe i (finiteGaussianMono N) m := by
  induction N generalizing i m with
  | zero => omega
  | succ N ih =>
      change gaussianMoment1 (exponentAt (monoMul (varMono i) m) N)*
          finiteGaussianMono N (monoMul (varMono i) m) ≈
        Q'.ofNat (exponentAt m i)*
          (gaussianMoment1 (exponentAt (lowerExponentAt i m) N)*
            finiteGaussianMono N (lowerExponentAt i m))
      cases Nat.decEq i N with
      | isTrue hlast =>
        subst i
        have hvar : exponentAt (monoMul (varMono N) m) N = exponentAt m N+1 := by
          rw [exponentAt_monoMul, exponentAt_varMono, if_pos rfl]
          omega
        have hlower : exponentAt (lowerExponentAt N m) N = exponentAt m N-1 := by
          rw [exponentAt_lower, if_pos rfl]
        have hvarTail : finiteGaussianMono N (monoMul (varMono N) m) = finiteGaussianMono N m :=
          finiteGaussianMono_ext N _ _ (fun k hk => by
            rw [exponentAt_monoMul, exponentAt_varMono, if_neg (by omega : k≠N)]
            exact Nat.zero_add _)
        have hlowerTail : finiteGaussianMono N (lowerExponentAt N m) = finiteGaussianMono N m :=
          finiteGaussianMono_ext N _ _ (fun k hk => by
            rw [exponentAt_lower, if_neg (by omega : k≠N)])
        rw [hvar, hlower, hvarTail, hlowerTail]
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (moment1_stein (exponentAt m N)))
          (Q'.mul_assoc_eqv _ _ _)
      | isFalse hlast =>
        have hsmall : i<N := by omega
        have hvar : exponentAt (monoMul (varMono i) m) N = exponentAt m N := by
          rw [exponentAt_monoMul, exponentAt_varMono, if_neg (by omega : N≠i)]
          exact Nat.zero_add _
        have hlower : exponentAt (lowerExponentAt i m) N = exponentAt m N := by
          rw [exponentAt_lower, if_neg (by omega : N≠i)]
        have hstep : finiteGaussianMono N (monoMul (varMono i) m) ≈
            Q'.ofNat (exponentAt m i)*finiteGaussianMono N (lowerExponentAt i m) :=
          ih (i := i) (m := m) (hi := hsmall)
        rw [hvar, hlower]
        exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hstep)
          (swap_scalar _ _ _)

private theorem weighted_var (weight : List Nat → Q') (i : Nat) : ∀ p : RatPoly,
    ratWeightedSum weight (polyMul (polyVar i) p) ≈
      ratWeightedSum (fun m => weight (monoMul (varMono i) m)) p
  | [] => Q'.eqv_refl _
  | term :: p => by
      have ih := weighted_var weight i p
      rcases term with ⟨m,c⟩
      simp only [polyMul, polyVar, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.map_cons]
      simp only [polyMul, polyVar, List.flatMap_cons, List.flatMap_nil,
        List.append_nil] at ih
      exact Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv c)) ih

private theorem weighted_congr (w v : List Nat → Q') (h : ∀ m, w m ≈ v m) :
    ∀ p : RatPoly, ratWeightedSum w p ≈ ratWeightedSum v p
  | [] => Q'.eqv_refl _
  | term :: p => Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (h term.1)) (weighted_congr w v h p)

/-- Actual coordinate IBP on the existing finite evaluator, for EVERY p.
Variables outside N are evaluated at one, not retained as coefficients. -/
theorem finiteProductGaussian_coordinate_stein (N i : Nat) (hi : i<N) (p : RatPoly) :
    finiteProductGaussian N (polyMul (polyVar i) p) ≈
      finiteProductGaussian N (ratDerivative i p) := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact Q'.eqv_trans _ _ _ (weighted_var (finiteGaussianMono N) i p)
    (Q'.eqv_trans _ _ _
      (weighted_congr _ _ (finiteGaussianMono_coordinate_stein N i hi) p)
      (Q'.eqv_symm (ratWeightedSum_derivative i (finiteGaussianMono N) p)))

private theorem gaussian_add (N : Nat) (p q : RatPoly) :
    finiteProductGaussian N (polyAdd p q) ≈
      finiteProductGaussian N p + finiteProductGaussian N q := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_add (finiteGaussianMono N) p q

private theorem gaussian_smul (N : Nat) (c : Q') (p : RatPoly) :
    finiteProductGaussian N (polySmul c p) ≈ c*finiteProductGaussian N p := by
  rw [finiteProductGaussian_probe, finiteProductGaussian_probe]
  exact ratWeightedSum_smul (finiteGaussianMono N) c p

private def linearRowOn (coefficient : Nat → Q') : List Nat → RatPoly
  | [] => polyZero
  | i :: indices => polyAdd (polySmul (coefficient i) (polyVar i))
      (linearRowOn coefficient indices)

private def rowDerivativeOn (coefficient : Nat → Q') (p : RatPoly) : List Nat → RatPoly
  | [] => polyZero
  | i :: indices => polyAdd (polySmul (coefficient i) (ratDerivative i p))
      (rowDerivativeOn coefficient p indices)

/-- Literal finite rational linear row sum_i coefficient_i*x_i, i<N. -/
def finiteLinearRow (N : Nat) (coefficient : Nat → Q') : RatPoly :=
  linearRowOn coefficient (List.range N)

/-- The computed directional derivative for the SAME explicit row. -/
def finiteRowDerivative (N : Nat) (coefficient : Nat → Q') (p : RatPoly) : RatPoly :=
  rowDerivativeOn coefficient p (List.range N)

private theorem linearRowOn_stein (N : Nat) (coefficient : Nat → Q') (p : RatPoly) :
    ∀ indices : List Nat, (∀ i, i ∈ indices → i<N) →
      finiteProductGaussian N (polyMul (linearRowOn coefficient indices) p) ≈
        finiteProductGaussian N (rowDerivativeOn coefficient p indices)
  | [], _ => Q'.eqv_refl _
  | i :: indices, hindices => by
      have hcoord := finiteProductGaussian_coordinate_stein N i
        (hindices i List.mem_cons_self) p
      have hscaled :
          finiteProductGaussian N (polyMul (polySmul (coefficient i) (polyVar i)) p) ≈
            finiteProductGaussian N (polySmul (coefficient i) (ratDerivative i p)) :=
        Q'.eqv_trans _ _ _
          (finiteProductGaussian_coeffEqv N
            (RatPolyCoeffEqv.polyMul_smul_left (coefficient i) (polyVar i) p))
          (Q'.eqv_trans _ _ _ (gaussian_smul N (coefficient i) (polyMul (polyVar i) p))
            (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hcoord)
              (Q'.eqv_symm (gaussian_smul N (coefficient i) (ratDerivative i p)))))
      have ih := linearRowOn_stein N coefficient p indices
        (fun j hj => hindices j (List.mem_cons_of_mem i hj))
      change finiteProductGaussian N
          (polyMul (polyAdd (polySmul (coefficient i) (polyVar i))
            (linearRowOn coefficient indices)) p) ≈
        finiteProductGaussian N
          (polyAdd (polySmul (coefficient i) (ratDerivative i p))
            (rowDerivativeOn coefficient p indices))
      rw [polyMul_add_left_exact]
      exact Q'.eqv_trans _ _ _ (gaussian_add N _ _)
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hscaled ih)
          (Q'.eqv_symm (gaussian_add N _ _)))

/-- Finite rational linear-row Stein contraction with computed coefficients.
No covariance/moment identity is a premise; zero rows and N=0 are included. -/
theorem finiteProductGaussian_linearRow_stein (N : Nat) (coefficient : Nat → Q') (p : RatPoly) :
    finiteProductGaussian N (polyMul (finiteLinearRow N coefficient) p) ≈
      finiteProductGaussian N (finiteRowDerivative N coefficient p) :=
  linearRowOn_stein N coefficient p (List.range N)
    (fun _ hi => List.mem_range.mp hi)

end YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP

#print axioms YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP.finiteProductGaussian_probe
#print axioms YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP.finiteProductGaussian_coeffEqv
#print axioms YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP.finiteGaussianMono_coordinate_stein
#print axioms YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP.finiteProductGaussian_coordinate_stein
#print axioms YMGap.Continuum.SU2QuaternionFiniteProductGaussianIBP.finiteProductGaussian_linearRow_stein
