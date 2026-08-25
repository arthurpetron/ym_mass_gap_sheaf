/-
# Coefficient compiler for the finite positive-artanh Euler anchor

This module reflects the remaining finite Euler-versus-geometric comparison
into the existing constructive `QPoly` carrier.  Exact evaluation semantics
are proved for the artanh polynomial, its finite exponential composition, and
the geometric comparison polynomial.  The pointwise window estimate is then
compiled from one weighted coefficient-L1 inequality.

The coefficient certificate is still an honest uninhabited input.  Its value
is causal: evaluation at the variable `z` has disappeared from the inequality
being checked; only the rational radius `|z|` and the already-computed natural
Euler pivot remain.
-/

import YMGap.Constructive.CRealArtanhEulerGeometricAnchor
import YMGap.Constructive.QPolyWeightedL1
import YMGap.Constructive.QPolyJetOne
import YMGap.Constructive.QPolyCoefficient
import YMGap.Constructive.QPolyValuation
import YMGap.Constructive.QPolyFormalDerivative

namespace YMGap.Constructive.CRealArtanhEulerPolynomialAnchor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.CRealArtanhEulerRatio
open YMGap.Constructive.CRealArtanhEulerGeometricAnchor
open YMGap.Constructive.QPolyWeightedL1
open YMGap.Constructive.QPolyJetOne
open YMGap.Constructive.QPolyCoefficient
open YMGap.Constructive.QPolyValuation
open YMGap.Constructive.QPolyFormalDerivative

local infix:50 " ~q " => Q'.eqv

/-- Constant polynomial. -/
def pconst (c : Q') : Poly := [c]

/-- The polynomial variable. -/
def pvar : Poly := [0, 1]

/-- Closed rational representative `-2`. -/
def negativeTwo : Q' := (-1 : Q') + (-1 : Q')

/-- Natural power in the coefficient-list polynomial algebra. -/
def ppow (p : Poly) : Nat -> Poly
  | 0 => pconst 1
  | n + 1 => pmul p (ppow p n)

/-- Multiplication by `z` has zero constant coefficient. -/
theorem coeff_pmul_pvar_zero (q : Poly) :
    (coeff (pmul pvar q) 0).eqv 0 := by
  unfold pvar
  refine Q'.eqv_trans _ ((0 : Q') * coeff q 0) _
    (coeff_pmul_pair_left_zero 0 1 q) ?_
  exact q_zero_mul _

/-- Multiplication by `z` shifts the previous coefficient without changing
its value. -/
theorem coeff_pmul_pvar_succ (q : Poly) (index : Nat) :
    (coeff (pmul pvar q) (index + 1)).eqv (coeff q index) := by
  unfold pvar
  refine Q'.eqv_trans _
    ((0 : Q') * coeff q (index + 1) +
      (1 : Q') * coeff q index) _
    (coeff_pmul_pair_left_succ 0 1 q index) ?_
  exact Q'.eqv_trans _
    ((0 : Q') + coeff q index) _
    (q_add_congr (q_zero_mul _) (Q'.one_mul_eqv _))
    (q_zero_add_eqv _)

/-- Exact coefficient formula for the pure monomial `z^power`. -/
theorem coeff_ppow_pvar : forall (power index : Nat),
    (coeff (ppow pvar power) index).eqv
      (if index = power then (1 : Q') else 0)
  | 0, 0 => Q'.eqv_refl 1
  | 0, index + 1 => Q'.eqv_refl 0
  | power + 1, 0 => by
      rw [if_neg (by omega : 0 ≠ power + 1)]
      exact coeff_pmul_pvar_zero _
  | power + 1, index + 1 => by
      by_cases heq : index = power
      · subst index
        rw [if_pos rfl]
        exact Q'.eqv_trans _ (coeff (ppow pvar power) power) _
          (coeff_pmul_pvar_succ _ power)
          (Q'.eqv_trans _
            (if power = power then (1 : Q') else 0) _
            (coeff_ppow_pvar power power)
            (by rw [if_pos rfl]; exact Q'.eqv_refl 1))
      · have hsucc : index + 1 ≠ power + 1 := by omega
        rw [if_neg hsucc]
        exact Q'.eqv_trans _ (coeff (ppow pvar power) index) _
          (coeff_pmul_pvar_succ _ index)
          (Q'.eqv_trans _
            (if index = power then (1 : Q') else 0) _
            (coeff_ppow_pvar power index)
            (by rw [if_neg heq]; exact Q'.eqv_refl 0))

/-- Formal differentiation of a positive monomial. -/
theorem pderiv_ppow_pvar_succ (power : Nat) :
    CoeffEqv (pderiv (ppow pvar (power + 1)))
      (pscale (Q'.ofNat (power + 1)) (ppow pvar power)) := by
  intro index
  by_cases heq : index = power
  · subst index
    exact Q'.eqv_trans _
      (Q'.ofNat (power + 1) *
        coeff (ppow pvar (power + 1)) (power + 1)) _
      (coeff_pderiv _ power)
      (Q'.eqv_trans _
        (Q'.ofNat (power + 1) * 1) _
        (Q'.mul_eqv_congr_left _ _ 1
          (Q'.eqv_trans _
            (if power + 1 = power + 1 then (1 : Q') else 0) _
            (coeff_ppow_pvar (power + 1) (power + 1))
            (by rw [if_pos rfl]; exact Q'.eqv_refl 1)))
        (Q'.eqv_trans _
          (Q'.ofNat (power + 1) *
            coeff (ppow pvar power) power) _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.eqv_symm
              (Q'.eqv_trans _
                (if power = power then (1 : Q') else 0) _
                (coeff_ppow_pvar power power)
                (by rw [if_pos rfl]; exact Q'.eqv_refl 1))))
          (Q'.eqv_symm
            (coeff_pscale (Q'.ofNat (power + 1))
              (ppow pvar power) power))))
  · have hsucc : index + 1 ≠ power + 1 := by omega
    exact Q'.eqv_trans _
      (Q'.ofNat (index + 1) *
        coeff (ppow pvar (power + 1)) (index + 1)) _
      (coeff_pderiv _ index)
      (Q'.eqv_trans _
        (Q'.ofNat (index + 1) * 0) _
        (Q'.mul_eqv_congr_left _ _ 0
          (Q'.eqv_trans _
            (if index + 1 = power + 1 then (1 : Q') else 0) _
            (coeff_ppow_pvar (power + 1) (index + 1))
            (by rw [if_neg hsucc]; exact Q'.eqv_refl 0)))
        (Q'.eqv_trans _
          (0 : Q') _
          (q_mul_zero _)
          (Q'.eqv_symm
            (Q'.eqv_trans _
              (Q'.ofNat (power + 1) *
                coeff (ppow pvar power) index) _
              (coeff_pscale (Q'.ofNat (power + 1))
                (ppow pvar power) index)
              (Q'.eqv_trans _
                (Q'.ofNat (power + 1) * 0) _
                (Q'.mul_eqv_congr_left _ _ 0
                  (Q'.eqv_trans _
                    (if index = power then (1 : Q') else 0) _
                    (coeff_ppow_pvar power index)
                    (by rw [if_neg heq]; exact Q'.eqv_refl 0)))
                (q_mul_zero _))))))

/-- Products of pure monomials add their exponents coefficientwise. -/
theorem coeffEqv_ppow_pvar_add : forall (left right : Nat),
    CoeffEqv (pmul (ppow pvar left) (ppow pvar right))
      (ppow pvar (left + right))
  | 0, right => by
      simpa only [ppow, pconst, Nat.zero_add] using
        (coeffEqv_pmul_one_left (ppow pvar right))
  | left + 1, right => by
      have hsum : (left + 1) + right = (left + right) + 1 := by omega
      rw [hsum]
      exact CoeffEqv.trans
        (coeffEqv_pmul_assoc pvar (ppow pvar left) (ppow pvar right))
        (CoeffEqv.pmul (CoeffEqv.refl pvar)
          (coeffEqv_ppow_pvar_add left right))

/-- Multiplication by `z^power` shifts padded coefficients by exactly
`power`. -/
theorem coeff_pmul_ppow_pvar : forall (power : Nat) (p : Poly) (index : Nat),
    (coeff (pmul (ppow pvar power) p) index).eqv
      (if power <= index then coeff p (index - power) else 0)
  | 0, p, index => by
      rw [if_pos (Nat.zero_le index), Nat.sub_zero]
      exact coeffEqv_pmul_one_left p index
  | power + 1, p, 0 => by
      have hfalse : Not (power + 1 <= 0) := by omega
      rw [if_neg hfalse]
      exact Q'.eqv_trans _
        (coeff (pmul pvar (pmul (ppow pvar power) p)) 0) _
        (coeffEqv_pmul_assoc pvar (ppow pvar power) p 0)
        (coeff_pmul_pvar_zero _)
  | power + 1, p, index + 1 => by
      have hassoc := coeffEqv_pmul_assoc
        pvar (ppow pvar power) p (index + 1)
      refine Q'.eqv_trans _
        (coeff (pmul pvar (pmul (ppow pvar power) p)) (index + 1)) _
        hassoc ?_
      refine Q'.eqv_trans _
        (coeff (pmul (ppow pvar power) p) index) _
        (coeff_pmul_pvar_succ _ index) ?_
      refine Q'.eqv_trans _
        (if power <= index then coeff p (index - power) else 0) _
        (coeff_pmul_ppow_pvar power p index) ?_
      by_cases hle : power <= index
      · have hsucc : power + 1 <= index + 1 := by omega
        rw [if_pos hle, if_pos hsucc]
        have hsub : index + 1 - (power + 1) = index - power := by omega
        rw [hsub]
        exact Q'.eqv_refl _
      · have hsucc : Not (power + 1 <= index + 1) := by omega
        rw [if_neg hle, if_neg hsucc]
        exact Q'.eqv_refl 0

/-- Multiplication by `-z` has zero constant coefficient. -/
theorem coeff_pmul_neg_pvar_zero (q : Poly) :
    (coeff (pmul (pneg pvar) q) 0).eqv 0 := by
  unfold pneg pvar
  refine Q'.eqv_trans _ (((-1 : Q') * 0) * coeff q 0) _
    (coeff_pmul_pair_left_zero _ _ q) ?_
  exact Q'.eqv_trans _ (0 * coeff q 0) _
    (Q'.mul_eqv_congr_right _ 0 _ (q_mul_zero (-1)))
    (q_zero_mul (coeff q 0))

/-- Multiplication by `-z` shifts the previous coefficient and scales it by
`-1`. -/
theorem coeff_pmul_neg_pvar_succ (q : Poly) (n : Nat) :
    (coeff (pmul (pneg pvar) q) (n + 1)).eqv
      ((-1 : Q') * coeff q n) := by
  unfold pneg pvar
  refine Q'.eqv_trans _
    (((-1 : Q') * 0) * coeff q (n + 1) +
      ((-1 : Q') * 1) * coeff q n) _
    (coeff_pmul_pair_left_succ _ _ q n) ?_
  refine Q'.eqv_trans _
    (0 * coeff q (n + 1) + (-1 : Q') * coeff q n) _
    (q_add_congr
      (Q'.mul_eqv_congr_right _ 0 _ (q_mul_zero (-1)))
      (Q'.mul_eqv_congr_right _ (-1) _ (Q'.mul_one_eqv (-1)))) ?_
  exact Q'.eqv_trans _ (0 + (-1 : Q') * coeff q n) _
    (q_add_congr (q_zero_mul _) (Q'.eqv_refl _))
    (q_zero_add_eqv _)

/-- Exact coefficient formula for the pure monomial `(-z)^power`. -/
theorem coeff_ppow_neg_pvar : forall (power index : Nat),
    (coeff (ppow (pneg pvar) power) index).eqv
      (if index = power then ((-1 : Q') ^ power) else 0)
  | 0, 0 => Q'.eqv_refl 1
  | 0, index + 1 => Q'.eqv_refl 0
  | power + 1, 0 => by
      rw [if_neg (by omega : 0 ≠ power + 1)]
      exact coeff_pmul_neg_pvar_zero _
  | power + 1, index + 1 => by
      by_cases heq : index = power
      · subst index
        rw [if_pos rfl]
        exact Q'.eqv_trans _
          ((-1 : Q') * coeff (ppow (pneg pvar) power) power) _
          (coeff_pmul_neg_pvar_succ _ power)
          (Q'.mul_eqv_congr_left (-1) _ _
            (Q'.eqv_trans _
              (if power = power then ((-1 : Q') ^ power) else 0) _
              (coeff_ppow_neg_pvar power power)
              (by rw [if_pos rfl]; exact Q'.eqv_refl _)))
      · have hsucc : index + 1 ≠ power + 1 := by omega
        rw [if_neg hsucc]
        exact Q'.eqv_trans _
          ((-1 : Q') * coeff (ppow (pneg pvar) power) index) _
          (coeff_pmul_neg_pvar_succ _ index)
          (Q'.eqv_trans _ ((-1 : Q') * 0) _
            (Q'.mul_eqv_congr_left (-1) _ 0
              (Q'.eqv_trans _
                (if index = power then ((-1 : Q') ^ power) else 0) _
                (coeff_ppow_neg_pvar power index)
                (by rw [if_neg heq]; exact Q'.eqv_refl 0)))
            (q_mul_zero (-1)))

theorem eval_pconst (c x : Q') : (eval (pconst c) x).eqv c := by
  show (c + x * 0).eqv c
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left c (x * 0) 0 (q_mul_zero x))
    (q_add_zero_eqv c)

theorem eval_pvar (x : Q') : (eval pvar x).eqv x := by
  show ((0 : Q') + x * (1 + x * 0)).eqv x
  refine Q'.eqv_trans _ (x * (1 + x * 0)) _ (q_zero_add_eqv _) ?_
  refine Q'.eqv_trans _ (x * 1) _
    (Q'.mul_eqv_congr_left x _ _
      (Q'.eqv_trans _ (1 + 0) _
        (Q'.add_eqv_congr_left 1 _ 0 (q_mul_zero x))
        (q_add_zero_eqv 1))) ?_
  exact Q'.mul_one_eqv x

/-- Rational equivalence is preserved by natural powers. -/
theorem pow_eqv_congr {a b : Q'} (h : a.eqv b) :
    forall n : Nat, (a ^ n).eqv (b ^ n)
  | 0 => Q'.eqv_refl 1
  | n + 1 =>
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right a b (a ^ n) h)
        (Q'.mul_eqv_congr_left b (a ^ n) (b ^ n)
          (pow_eqv_congr h n))

/-- Polynomial powers evaluate to rational powers. -/
theorem eval_ppow (p : Poly) (x : Q') :
    forall n : Nat, (eval (ppow p n) x).eqv ((eval p x) ^ n)
  | 0 => Q'.eqv_trans _ _ _ (eval_pconst 1 x) (Q'.eqv_refl 1)
  | n + 1 =>
      Q'.eqv_trans _ _ _ (eval_pmul p (ppow p n) x)
        (Q'.mul_eqv_congr_left (eval p x)
          (eval (ppow p n) x) ((eval p x) ^ n)
          (eval_ppow p x n))

theorem eval_ppow_pvar (x : Q') (n : Nat) :
    (eval (ppow pvar n) x).eqv (x ^ n) :=
  Q'.eqv_trans _ _ _ (eval_ppow pvar x n)
    (pow_eqv_congr (eval_pvar x) n)

/-- Weighted norm of a constant polynomial. -/
theorem weightedL1_pconst_eqv (rho c : Q') :
    (weightedL1 rho (pconst c)).eqv (Q'.abs c) := by
  change (Q'.abs c + rho * 0).eqv (Q'.abs c)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Q'.abs c) _ 0 (q_mul_zero rho))
    (q_add_zero_eqv (Q'.abs c))

/-- At radius `rho`, the polynomial variable has weighted norm `rho`. -/
theorem weightedL1_pvar_eqv (rho : Q') :
    (weightedL1 rho pvar).eqv rho := by
  change (Q'.abs (0 : Q') +
      rho * (Q'.abs (1 : Q') + rho * 0)).eqv rho
  have hzero : (Q'.abs (0 : Q')).eqv 0 := by decide
  have hone : (Q'.abs (1 : Q')).eqv 1 := by decide
  have hinner : (Q'.abs (1 : Q') + rho * 0).eqv 1 := by
    refine Q'.eqv_trans _ (1 + 0) _
      (q_add_congr hone (q_mul_zero rho)) ?_
    exact q_add_zero_eqv 1
  refine Q'.eqv_trans _ (0 + rho * 1) _
    (q_add_congr hzero
      (Q'.mul_eqv_congr_left rho _ 1 hinner)) ?_
  refine Q'.eqv_trans _ (rho * 1) _ (q_zero_add_eqv _) ?_
  exact Q'.mul_one_eqv rho

/-- Polynomial powers inherit submultiplicativity of the weighted norm. -/
theorem weightedL1_ppow_le
    (rho : Q') (hrho : (0 : Q') <= rho) (p : Poly) :
    forall n : Nat,
      weightedL1 rho (ppow p n) <= (weightedL1 rho p) ^ n
  | 0 => Q'.le_of_eqv (weightedL1_pconst_eqv rho 1)
  | n + 1 => by
      have hmul := weightedL1_pmul_le rho hrho p (ppow p n)
      have htail := Q'.mul_le_mul_of_nonneg_left
        (weightedL1 rho (ppow p n)) ((weightedL1 rho p) ^ n)
        (weightedL1 rho p) (weightedL1_ppow_le rho hrho p n)
        (weightedL1_nonnegative rho hrho p)
      exact Q'.le_trans' _ _ _ hmul htail

/-- Polynomial for the `k`th odd-power artanh term. -/
def artanhTermPoly (k : Nat) : Poly :=
  pscale (CRealLog.recipOdd k) (ppow pvar (2 * k + 1))

/-- Polynomial for the first `stage` artanh terms. -/
def artanhPartialPoly : Nat -> Poly
  | 0 => []
  | stage + 1 => padd (artanhPartialPoly stage) (artanhTermPoly stage)

theorem eval_artanhTermPoly (z : Q') (k : Nat) :
    (eval (artanhTermPoly k) z).eqv (CRealLog.term z k) := by
  refine Q'.eqv_trans _ _ _
    (eval_pscale (CRealLog.recipOdd k) (ppow pvar (2 * k + 1)) z) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (CRealLog.recipOdd k)
      (eval (ppow pvar (2 * k + 1)) z) (z ^ (2 * k + 1))
      (eval_ppow_pvar z (2 * k + 1))) ?_
  exact Q'.mul_comm_eqv (CRealLog.recipOdd k) (z ^ (2 * k + 1))

/-- The weighted norm of each reflected artanh term is bounded by its usual
magnitude term at the same rational input. -/
theorem weightedL1_artanhTermPoly_le (z : Q') (k : Nat) :
    weightedL1 (Q'.abs z) (artanhTermPoly k) <=
      CRealLog.termAbs z k := by
  let rho : Q' := Q'.abs z
  let odd : Nat := 2 * k + 1
  have hrho : (0 : Q') <= rho := Q'.abs_nonneg z
  have hscale := weightedL1_pscale_le rho hrho
    (CRealLog.recipOdd k) (ppow pvar odd)
  have hpower := weightedL1_ppow_le rho hrho pvar odd
  have hvarPower : (weightedL1 rho pvar ^ odd).eqv (rho ^ odd) :=
    pow_eqv_congr (weightedL1_pvar_eqv rho) odd
  have hpower' : weightedL1 rho (ppow pvar odd) <= rho ^ odd :=
    Q'.le_trans' _ _ _ hpower (Q'.le_of_eqv hvarPower)
  have hcoefficient :
      (Q'.abs (CRealLog.recipOdd k)).eqv
        (CRealLog.recipOdd k) := by
    exact Q'.eqv_of_eq
      (ExpNeg.abs_of_nonneg (CRealLog.recipOdd_nonneg k))
  have hscaledPower :
      Q'.abs (CRealLog.recipOdd k) *
          weightedL1 rho (ppow pvar odd) <=
        Q'.abs (CRealLog.recipOdd k) * rho ^ odd :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpower'
      (Q'.abs_nonneg (CRealLog.recipOdd k))
  refine Q'.le_trans' _ _ _ hscale
    (Q'.le_trans' _ _ _ hscaledPower ?_)
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _
    (CRealLog.recipOdd k * rho ^ odd) _
    (Q'.mul_eqv_congr_right _ _ _ hcoefficient) ?_
  exact Q'.mul_comm_eqv (CRealLog.recipOdd k) (rho ^ odd)

theorem eval_artanhPartialPoly (z : Q') :
    forall stage : Nat,
      (eval (artanhPartialPoly stage) z).eqv
        (CRealLog.partialSum z stage)
  | 0 => Q'.eqv_refl 0
  | stage + 1 =>
      Q'.eqv_trans _ _ _
        (eval_padd (artanhPartialPoly stage) (artanhTermPoly stage) z)
        (Q'.eqv_trans _ _ _
          (q_add_congr
            (eval_artanhPartialPoly z stage)
            (eval_artanhTermPoly z stage))
          (Q'.eqv_refl _))

/-- The reflected artanh partial polynomial is controlled by the exact
magnitude block beginning at zero. -/
theorem weightedL1_artanhPartialPoly_le (z : Q') :
    forall stage : Nat,
      weightedL1 (Q'.abs z) (artanhPartialPoly stage) <=
        CRealLog.blockAbs z 0 stage
  | 0 => Q'.le_refl' 0
  | stage + 1 => by
      rw [artanhPartialPoly, CRealLog.blockAbs_succ, Nat.zero_add]
      have hadd := weightedL1_padd_le (Q'.abs z) (Q'.abs_nonneg z)
        (artanhPartialPoly stage) (artanhTermPoly stage)
      exact Q'.le_trans' _ _ _ hadd
        (Q'.add_le_add
          (weightedL1_artanhPartialPoly_le z stage)
          (weightedL1_artanhTermPoly_le z stage))

/-- Polynomial for twice the finite artanh partial sum. -/
def positiveArtanhExponentPoly (stage : Nat) : Poly :=
  padd (artanhPartialPoly stage) (artanhPartialPoly stage)

/-- Polynomial for the first `stage` even powers
`1 + z^2 + ... + z^(2(stage-1))`.  This is the exact formal derivative of
the finite artanh polynomial. -/
def evenPowerPartialPoly : Nat -> Poly
  | 0 => []
  | stage + 1 => padd (evenPowerPartialPoly stage) (ppow pvar (2 * stage))

/-- The polynomial `1 - z^2` used to contract the finite even-power
derivative into its two boundary monomials. -/
def oneSubSquarePoly : Poly :=
  padd (pconst 1) (pneg (ppow pvar 2))

/-- Multiplying one even monomial by `1-z^2` produces adjacent boundary
monomials. -/
theorem coeffEqv_oneSubSquarePoly_mul_evenPower (stage : Nat) :
    CoeffEqv
      (pmul oneSubSquarePoly (ppow pvar (2 * stage)))
      (padd (ppow pvar (2 * stage))
        (pneg (ppow pvar (2 * (stage + 1))))) := by
  let monomial : Poly := ppow pvar (2 * stage)
  have hpower := coeffEqv_ppow_pvar_add 2 (2 * stage)
  have hdegree : 2 + 2 * stage = 2 * (stage + 1) := by omega
  rw [hdegree] at hpower
  have hnegative :
      CoeffEqv
        (pmul (pneg (ppow pvar 2)) monomial)
        (pneg (ppow pvar (2 * (stage + 1)))) :=
    CoeffEqv.trans
      (coeffEqv_pscale_pmul (-1) (ppow pvar 2) monomial)
      (CoeffEqv.pneg hpower)
  unfold oneSubSquarePoly
  exact CoeffEqv.trans
    (coeffEqv_padd_pmul_left
      (pconst 1) (pneg (ppow pvar 2)) monomial)
    (CoeffEqv.padd
      (coeffEqv_pmul_one_left monomial) hnegative)

/-- Exact finite geometric telescoping:
`(1-z^2)(1+z^2+...+z^(2(stage-1))) = 1-z^(2stage)`. -/
theorem coeffEqv_oneSubSquarePoly_mul_evenPowerPartial :
    forall stage : Nat,
      CoeffEqv (pmul oneSubSquarePoly (evenPowerPartialPoly stage))
        (padd (pconst 1) (pneg (ppow pvar (2 * stage))))
  | 0 => by
      have hleft : CoeffEqv (pmul oneSubSquarePoly []) [] := by
        simpa only [pmul] using
          (coeffEqv_pmul_comm oneSubSquarePoly [])
      have hright :
          CoeffEqv (padd (pconst 1) (pneg (ppow pvar 0))) [] := by
        simpa only [ppow] using
          (coeffEqv_padd_pneg_self (pconst 1))
      exact CoeffEqv.trans hleft (CoeffEqv.symm hright)
  | stage + 1 => by
      refine CoeffEqv.trans
        (coeffEqv_pmul_padd_right oneSubSquarePoly
          (evenPowerPartialPoly stage) (ppow pvar (2 * stage))) ?_
      refine CoeffEqv.trans
        (CoeffEqv.padd
          (coeffEqv_oneSubSquarePoly_mul_evenPowerPartial stage)
          (coeffEqv_oneSubSquarePoly_mul_evenPower stage)) ?_
      exact coeffEqv_padd_pneg_cancel
        (pconst 1) (ppow pvar (2 * stage))
        (pneg (ppow pvar (2 * (stage + 1))))

/-- The odd denominator in the `k`th artanh term cancels its derivative
coefficient. -/
theorem recipOdd_mul_ofNat_odd_eqv_one (k : Nat) :
    (CRealLog.recipOdd k * Q'.ofNat (2 * k + 1)).eqv (1 : Q') := by
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv (CRealLog.recipOdd k) (Q'.ofNat (2 * k + 1)))
    (by
      unfold CRealLog.recipOdd
      exact Q'.ofNat_succ_mul_invSucc (2 * k))

/-- Cancellation of the odd artanh denominator remains exact after
multiplying an arbitrary coefficient. -/
theorem recipOdd_mul_ofNat_odd_mul (k : Nat) (c : Q') :
    (CRealLog.recipOdd k * (Q'.ofNat (2 * k + 1) * c)).eqv c := by
  exact Q'.eqv_trans _
    ((CRealLog.recipOdd k * Q'.ofNat (2 * k + 1)) * c) _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv (CRealLog.recipOdd k)
        (Q'.ofNat (2 * k + 1)) c))
    (Q'.eqv_trans _ ((1 : Q') * c) _
      (Q'.mul_eqv_congr_right _ _ c
        (recipOdd_mul_ofNat_odd_eqv_one k))
      (Q'.one_mul_eqv c))

/-- Exact formal derivative of one reflected artanh term. -/
theorem pderiv_artanhTermPoly (k : Nat) :
    CoeffEqv (pderiv (artanhTermPoly k)) (ppow pvar (2 * k)) := by
  refine CoeffEqv.trans
    (pderiv_pscale (CRealLog.recipOdd k)
      (ppow pvar (2 * k + 1))) ?_
  refine CoeffEqv.trans
    (CoeffEqv.pscale (CRealLog.recipOdd k)
      (pderiv_ppow_pvar_succ (2 * k))) ?_
  intro index
  refine Q'.eqv_trans _
    (CRealLog.recipOdd k *
      coeff (pscale (Q'.ofNat (2 * k + 1))
        (ppow pvar (2 * k))) index) _
    (coeff_pscale (CRealLog.recipOdd k)
      (pscale (Q'.ofNat (2 * k + 1))
        (ppow pvar (2 * k))) index) ?_
  refine Q'.eqv_trans _
    (CRealLog.recipOdd k *
      (Q'.ofNat (2 * k + 1) *
        coeff (ppow pvar (2 * k)) index)) _
    (Q'.mul_eqv_congr_left (CRealLog.recipOdd k) _ _
      (coeff_pscale (Q'.ofNat (2 * k + 1))
        (ppow pvar (2 * k)) index)) ?_
  exact recipOdd_mul_ofNat_odd_mul k _

/-- Formal differentiation of the finite artanh partial polynomial produces
the matching finite even-power sum. -/
theorem pderiv_artanhPartialPoly : forall stage : Nat,
    CoeffEqv (pderiv (artanhPartialPoly stage))
      (evenPowerPartialPoly stage)
  | 0 => CoeffEqv.refl []
  | stage + 1 => by
      refine CoeffEqv.trans
        (pderiv_padd (artanhPartialPoly stage) (artanhTermPoly stage)) ?_
      exact CoeffEqv.padd
        (pderiv_artanhPartialPoly stage)
        (pderiv_artanhTermPoly stage)

/-- The finite positive-artanh exponent has derivative twice the finite
even-power sum. -/
theorem pderiv_positiveArtanhExponentPoly (stage : Nat) :
    CoeffEqv (pderiv (positiveArtanhExponentPoly stage))
      (padd (evenPowerPartialPoly stage) (evenPowerPartialPoly stage)) := by
  refine CoeffEqv.trans
    (pderiv_padd (artanhPartialPoly stage) (artanhPartialPoly stage)) ?_
  exact CoeffEqv.padd
    (pderiv_artanhPartialPoly stage)
    (pderiv_artanhPartialPoly stage)

/-- Multiplication by `1-z^2` contracts the negative derivative of the
finite positive-artanh exponent to its constant and truncation-boundary
terms. -/
theorem coeffEqv_oneSubSquare_mul_negativeExponentDerivative
    (stage : Nat) :
    CoeffEqv
      (pmul oneSubSquarePoly
        (pneg (pderiv (positiveArtanhExponentPoly stage))))
      (pneg
        (padd
          (padd (pconst 1) (pneg (ppow pvar (2 * stage))))
          (padd (pconst 1) (pneg (ppow pvar (2 * stage)))))) := by
  let evenSum : Poly := evenPowerPartialPoly stage
  let boundary : Poly :=
    padd (pconst 1) (pneg (ppow pvar (2 * stage)))
  have hnegativeDerivative :
      CoeffEqv
        (pneg (pderiv (positiveArtanhExponentPoly stage)))
        (pneg (padd evenSum evenSum)) :=
    CoeffEqv.pneg (pderiv_positiveArtanhExponentPoly stage)
  have hdistributed :
      CoeffEqv
        (pmul oneSubSquarePoly (padd evenSum evenSum))
        (padd boundary boundary) :=
    CoeffEqv.trans
      (coeffEqv_pmul_padd_right oneSubSquarePoly evenSum evenSum)
      (CoeffEqv.padd
        (coeffEqv_oneSubSquarePoly_mul_evenPowerPartial stage)
        (coeffEqv_oneSubSquarePoly_mul_evenPowerPartial stage))
  exact CoeffEqv.trans
    (CoeffEqv.pmul (CoeffEqv.refl oneSubSquarePoly)
      hnegativeDerivative)
    (CoeffEqv.trans
      (coeffEqv_pmul_pscale (-1) oneSubSquarePoly
        (padd evenSum evenSum))
      (CoeffEqv.pneg hdistributed))

theorem eval_positiveArtanhExponentPoly (z : Q') (stage : Nat) :
    (eval (positiveArtanhExponentPoly stage) z).eqv
      (positiveArtanhExponent z stage) := by
  exact Q'.eqv_trans _ _ _
    (eval_padd (artanhPartialPoly stage) (artanhPartialPoly stage) z)
    (q_add_congr
      (eval_artanhPartialPoly z stage)
      (eval_artanhPartialPoly z stage))

/-- Coefficient-norm majorant for the reflected positive-artanh exponent. -/
theorem weightedL1_positiveArtanhExponentPoly_le
    (z : Q') (stage : Nat) :
    weightedL1 (Q'.abs z) (positiveArtanhExponentPoly stage) <=
      CRealLog.blockAbs z 0 stage + CRealLog.blockAbs z 0 stage := by
  have hadd := weightedL1_padd_le (Q'.abs z) (Q'.abs_nonneg z)
    (artanhPartialPoly stage) (artanhPartialPoly stage)
  exact Q'.le_trans' _ _ _ hadd
    (Q'.add_le_add
      (weightedL1_artanhPartialPoly_le z stage)
      (weightedL1_artanhPartialPoly_le z stage))

/-- Polynomial factor representing `(-x)/(k+1)` when `x` is itself a
polynomial. -/
def expStepPoly (exponent : Poly) (k : Nat) : Poly :=
  pscale (Q'.invSucc k) (pneg exponent)

theorem eval_expStepPoly
    (exponent : Poly) (z value : Q')
    (hvalue : (eval exponent z).eqv value) (k : Nat) :
    (eval (expStepPoly exponent k) z).eqv
      ((-value) * Q'.invSucc k) := by
  refine Q'.eqv_trans _ _ _
    (eval_pscale (Q'.invSucc k) (pneg exponent) z) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.invSucc k)
      (eval (pneg exponent) z) (-(eval exponent z))
      (eval_pneg exponent z)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.invSucc k)
      (-(eval exponent z)) (-value)
      (Q'.neg_eqv_congr _ _ hvalue)) ?_
  exact Q'.mul_comm_eqv (Q'.invSucc k) (-value)

/-- Polynomial form of one finite exponential-series term. -/
def expTermPoly (exponent : Poly) : Nat -> Poly
  | 0 => pconst 1
  | k + 1 => pmul (expTermPoly exponent k) (expStepPoly exponent k)

/-- Polynomial form of the finite exponential partial sum. -/
def expPartialPoly (exponent : Poly) : Nat -> Poly
  | 0 => []
  | inner + 1 => padd (expPartialPoly exponent inner)
      (expTermPoly exponent inner)

/-- Formal differentiation commutes with coefficientwise negation. -/
theorem pderiv_pneg (p : Poly) :
    CoeffEqv (pderiv (pneg p)) (pneg (pderiv p)) := by
  unfold pneg
  exact pderiv_pscale (-1) p

/-- Formal derivative of one exponential recursion step. -/
theorem pderiv_expStepPoly (exponent : Poly) (k : Nat) :
    CoeffEqv (pderiv (expStepPoly exponent k))
      (pscale (Q'.invSucc k) (pneg (pderiv exponent))) := by
  unfold expStepPoly
  exact CoeffEqv.trans
    (pderiv_pscale (Q'.invSucc k) (pneg exponent))
    (CoeffEqv.pscale (Q'.invSucc k) (pderiv_pneg exponent))

/-- The two Leibniz summands in the exponential-term induction combine by
the exact adjacent reciprocal cancellation. -/
theorem expTermDerivativeStepAlgebra
    (term factor differential : Poly) (k : Nat) :
    CoeffEqv
      (padd
        (pmul (pmul term differential)
          (pscale (Q'.invSucc (k + 1)) factor))
        (pmul (pmul term (pscale (Q'.invSucc k) factor))
          (pscale (Q'.invSucc (k + 1)) differential)))
      (pmul (pmul term (pscale (Q'.invSucc k) factor))
        differential) := by
  let a : Q' := Q'.invSucc k
  let b : Q' := Q'.invSucc (k + 1)
  let base : Poly := pmul (pmul term factor) differential
  have hswap :
      CoeffEqv (pmul (pmul term differential) factor) base := by
    exact CoeffEqv.trans
      (coeffEqv_pmul_assoc term differential factor)
      (CoeffEqv.trans
        (CoeffEqv.pmul (CoeffEqv.refl term)
          (coeffEqv_pmul_comm differential factor))
        (CoeffEqv.symm
          (coeffEqv_pmul_assoc term factor differential)))
  have hfirst :
      CoeffEqv
        (pmul (pmul term differential) (pscale b factor))
        (pscale b base) :=
    CoeffEqv.trans
      (coeffEqv_pmul_pscale b (pmul term differential) factor)
      (CoeffEqv.pscale b hswap)
  have hinner :
      CoeffEqv
        (pmul (pmul term (pscale a factor)) differential)
        (pscale a base) :=
    CoeffEqv.trans
      (CoeffEqv.pmul
        (coeffEqv_pmul_pscale a term factor)
        (CoeffEqv.refl differential))
      (coeffEqv_pscale_pmul a (pmul term factor) differential)
  have hsecond :
      CoeffEqv
        (pmul (pmul term (pscale a factor))
          (pscale b differential))
        (pscale (b * a) base) :=
    CoeffEqv.trans
      (coeffEqv_pmul_pscale b
        (pmul term (pscale a factor)) differential)
      (CoeffEqv.trans
        (CoeffEqv.pscale b hinner)
        (coeffEqv_pscale_comp b a base))
  have hscalar : (b + b * a).eqv a := by
    exact Q'.eqv_trans _
      (b * 1 + b * a) _
      (q_add_congr
        (Q'.eqv_symm (Q'.mul_one_eqv b)) (Q'.eqv_refl _))
      (Q'.eqv_trans _
        (b * (1 + a)) _
        (Q'.eqv_symm (Q'.mul_add_eqv b 1 a))
        (Q'.eqv_trans _
          (b * (a + 1)) _
          (Q'.mul_eqv_congr_left b _ _ (Q'.add_comm_eqv 1 a))
          (by
            unfold a b
            exact ExpNeg.invSucc_cancel k)))
  have hleft :
      CoeffEqv
        (padd
          (pmul (pmul term differential) (pscale b factor))
          (pmul (pmul term (pscale a factor))
            (pscale b differential)))
        (pscale a base) :=
    CoeffEqv.trans
      (CoeffEqv.padd hfirst hsecond)
      (CoeffEqv.trans
        (coeffEqv_padd_pscale b (b * a) base)
        (coeffEqv_pscale_scalar hscalar base))
  exact CoeffEqv.trans hleft (CoeffEqv.symm hinner)

/-- Exact formal derivative of a positive-index finite exponential term.
The proof stays in finite coefficient lists; the only division is discharged
by `ExpNeg.invSucc_cancel`. -/
theorem pderiv_expTermPoly_succ (exponent : Poly) : forall k : Nat,
    CoeffEqv (pderiv (expTermPoly exponent (k + 1)))
      (pmul (expTermPoly exponent k) (pneg (pderiv exponent)))
  | 0 => by
      refine CoeffEqv.trans
        (pderiv_pmul (pconst 1) (expStepPoly exponent 0)) ?_
      change
        CoeffEqv
          (pmul [(1 : Q')] (pderiv (expStepPoly exponent 0)))
          (pmul [(1 : Q')] (pneg (pderiv exponent)))
      refine CoeffEqv.pmul (CoeffEqv.refl [(1 : Q')]) ?_
      refine CoeffEqv.trans (pderiv_expStepPoly exponent 0) ?_
      exact CoeffEqv.trans
        (coeffEqv_pscale_scalar
          (by decide : (Q'.invSucc 0).eqv (1 : Q'))
          (pneg (pderiv exponent)))
        (coeffEqv_pscale_one (pneg (pderiv exponent)))
  | k + 1 => by
      refine CoeffEqv.trans
        (pderiv_pmul
          (expTermPoly exponent (k + 1))
          (expStepPoly exponent (k + 1))) ?_
      refine CoeffEqv.trans
        (CoeffEqv.padd
          (CoeffEqv.pmul
            (pderiv_expTermPoly_succ exponent k)
            (CoeffEqv.refl (expStepPoly exponent (k + 1))))
          (CoeffEqv.pmul
            (CoeffEqv.refl (expTermPoly exponent (k + 1)))
            (pderiv_expStepPoly exponent (k + 1)))) ?_
      change
        CoeffEqv
          (padd
            (pmul
              (pmul (expTermPoly exponent k) (pneg (pderiv exponent)))
              (pscale (Q'.invSucc (k + 1)) (pneg exponent)))
            (pmul
              (pmul (expTermPoly exponent k)
                (pscale (Q'.invSucc k) (pneg exponent)))
              (pscale (Q'.invSucc (k + 1))
                (pneg (pderiv exponent)))))
          (pmul
            (pmul (expTermPoly exponent k)
              (pscale (Q'.invSucc k) (pneg exponent)))
            (pneg (pderiv exponent)))
      exact expTermDerivativeStepAlgebra
        (expTermPoly exponent k) (pneg exponent)
        (pneg (pderiv exponent)) k

/-- The derivative of an exponential partial polynomial with `inner+1`
terms is the previous partial polynomial times the negative exponent
derivative. -/
theorem pderiv_expPartialPoly_succ (exponent : Poly) : forall inner : Nat,
    CoeffEqv (pderiv (expPartialPoly exponent (inner + 1)))
      (pmul (expPartialPoly exponent inner) (pneg (pderiv exponent)))
  | 0 => CoeffEqv.refl []
  | inner + 1 => by
      refine CoeffEqv.trans
        (pderiv_padd
          (expPartialPoly exponent (inner + 1))
          (expTermPoly exponent (inner + 1))) ?_
      refine CoeffEqv.trans
        (CoeffEqv.padd
          (pderiv_expPartialPoly_succ exponent inner)
          (pderiv_expTermPoly_succ exponent inner)) ?_
      exact CoeffEqv.symm
        (coeffEqv_padd_pmul_left
          (expPartialPoly exponent inner)
          (expTermPoly exponent inner)
          (pneg (pderiv exponent)))

/-- Exact finite differential equation for the reflected positive-artanh
Euler polynomial.  It includes the explicit degree-`2*stage` boundary term;
no infinite-series identity is used. -/
theorem positiveArtanhExpPartialPoly_finiteDifferentialEquation
    (stage inner : Nat) :
    CoeffEqv
      (pmul oneSubSquarePoly
        (pderiv
          (expPartialPoly (positiveArtanhExponentPoly stage) (inner + 1))))
      (pmul
        (expPartialPoly (positiveArtanhExponentPoly stage) inner)
        (pneg
          (padd
            (padd (pconst 1) (pneg (ppow pvar (2 * stage))))
            (padd (pconst 1) (pneg (ppow pvar (2 * stage))))))) := by
  let exponent : Poly := positiveArtanhExponentPoly stage
  let truncated : Poly := expPartialPoly exponent inner
  let differential : Poly := pneg (pderiv exponent)
  have hderivative := pderiv_expPartialPoly_succ exponent inner
  have hreorder :
      CoeffEqv
        (pmul oneSubSquarePoly (pmul truncated differential))
        (pmul truncated (pmul oneSubSquarePoly differential)) :=
    CoeffEqv.trans
      (CoeffEqv.symm
        (coeffEqv_pmul_assoc oneSubSquarePoly truncated differential))
      (CoeffEqv.trans
        (CoeffEqv.pmul
          (coeffEqv_pmul_comm oneSubSquarePoly truncated)
          (CoeffEqv.refl differential))
        (coeffEqv_pmul_assoc truncated oneSubSquarePoly differential))
  exact CoeffEqv.trans
    (CoeffEqv.pmul (CoeffEqv.refl oneSubSquarePoly) hderivative)
    (CoeffEqv.trans hreorder
      (CoeffEqv.pmul (CoeffEqv.refl truncated)
        (coeffEqv_oneSubSquare_mul_negativeExponentDerivative stage)))

/-- Normalize the doubled boundary polynomial into two negative constants
and two positive degree-`2*stage` monomials. -/
theorem coeffEqv_negativeDoubledArtanhBoundary (stage : Nat) :
    CoeffEqv
      (pneg
        (padd
          (padd (pconst 1) (pneg (ppow pvar (2 * stage))))
          (padd (pconst 1) (pneg (ppow pvar (2 * stage))))))
      (padd
        (padd (pneg (pconst 1)) (pneg (pconst 1)))
        (padd (ppow pvar (2 * stage))
          (ppow pvar (2 * stage)))) := by
  let one : Poly := pconst 1
  let boundary : Poly := ppow pvar (2 * stage)
  have hsingle :
      CoeffEqv (pneg (padd one (pneg boundary)))
        (padd (pneg one) boundary) :=
    CoeffEqv.trans (coeffEqv_pneg_padd one (pneg boundary))
      (CoeffEqv.padd (CoeffEqv.refl (pneg one))
        (coeffEqv_pneg_pneg boundary))
  exact CoeffEqv.trans
    (coeffEqv_pneg_padd
      (padd one (pneg boundary)) (padd one (pneg boundary)))
    (CoeffEqv.trans (CoeffEqv.padd hsingle hsingle)
      (coeffEqv_padd_interchange
        (pneg one) boundary (pneg one) boundary))

/-- Right multiplication by the negative constant-one polynomial negates
each coefficient. -/
theorem coeff_pmul_pneg_pconst_one (p : Poly) (index : Nat) :
    (coeff (pmul p (pneg (pconst 1))) index).eqv
      (-(coeff p index)) := by
  have hrightIdentity : CoeffEqv (pmul p (pconst 1)) p :=
    CoeffEqv.trans (coeffEqv_pmul_comm p (pconst 1))
      (coeffEqv_pmul_one_left p)
  have hpoly :
      CoeffEqv (pmul p (pneg (pconst 1))) (pneg p) :=
    CoeffEqv.trans
      (coeffEqv_pmul_pscale (-1) p (pconst 1))
      (CoeffEqv.pscale (-1) hrightIdentity)
  exact Q'.eqv_trans _ (coeff (pneg p) index) _
    (hpoly index) (coeff_pneg_eqv p index)

/-- A monomial on the right contributes no coefficient below its degree. -/
theorem coeff_pmul_ppow_pvar_right_eqv_zero_of_lt
    (p : Poly) (power index : Nat) (hindex : index < power) :
    (coeff (pmul p (ppow pvar power)) index).eqv 0 := by
  exact Q'.eqv_trans _
    (coeff (pmul (ppow pvar power) p) index) _
    (coeffEqv_pmul_comm p (ppow pvar power) index)
    (Q'.eqv_trans _
      (if power <= index then coeff p (index - power) else 0) _
      (coeff_pmul_ppow_pvar power p index)
      (by
        rw [if_neg (by omega : Not (power <= index))]
        exact Q'.eqv_refl 0))

/-- `-2` times a coefficient is the sum of two copies of its negation. -/
theorem negativeTwo_mul_eqv_neg_add_neg (a : Q') :
    (negativeTwo * a).eqv ((-a) + (-a)) := by
  unfold negativeTwo
  refine Q'.eqv_trans _
    ((-1 : Q') * a + (-1 : Q') * a) _
    (q_add_mul (-1) (-1) a) ?_
  exact q_add_congr
    (Q'.eqv_trans _ (-(1 * a)) _
      (Q'.neg_mul_eqv 1 a)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a)))
    (Q'.eqv_trans _ (-(1 * a)) _
      (Q'.neg_mul_eqv 1 a)
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a)))

/-- Below the explicit artanh boundary, multiplying by the contracted
boundary polynomial is exactly scalar multiplication by `-2`. -/
theorem coeff_pmul_negativeDoubledArtanhBoundary_of_lt
    (p : Poly) (stage index : Nat) (hindex : index < 2 * stage) :
    (coeff
      (pmul p
        (pneg
          (padd
            (padd (pconst 1) (pneg (ppow pvar (2 * stage))))
            (padd (pconst 1) (pneg (ppow pvar (2 * stage)))))))
      index).eqv (negativeTwo * coeff p index) := by
  let negativeOne : Poly := pneg (pconst 1)
  let boundary : Poly := ppow pvar (2 * stage)
  let expanded : Poly :=
    padd
      (padd (pmul p negativeOne) (pmul p negativeOne))
      (padd (pmul p boundary) (pmul p boundary))
  have hexpanded :
      CoeffEqv
        (pmul p
          (pneg
            (padd
              (padd (pconst 1) (pneg (ppow pvar (2 * stage))))
              (padd (pconst 1) (pneg (ppow pvar (2 * stage)))))))
        expanded :=
    CoeffEqv.trans
      (CoeffEqv.pmul (CoeffEqv.refl p)
        (coeffEqv_negativeDoubledArtanhBoundary stage))
      (CoeffEqv.trans
        (coeffEqv_pmul_padd_right p
          (padd negativeOne negativeOne) (padd boundary boundary))
        (CoeffEqv.padd
          (coeffEqv_pmul_padd_right p negativeOne negativeOne)
          (coeffEqv_pmul_padd_right p boundary boundary)))
  refine Q'.eqv_trans _ (coeff expanded index) _
    (hexpanded index) ?_
  refine Q'.eqv_trans _
    ((coeff (pmul p negativeOne) index +
        coeff (pmul p negativeOne) index) +
      (coeff (pmul p boundary) index +
        coeff (pmul p boundary) index)) _
    (Q'.eqv_trans _
      (coeff (padd (pmul p negativeOne) (pmul p negativeOne)) index +
        coeff (padd (pmul p boundary) (pmul p boundary)) index) _
      (coeff_padd index
        (padd (pmul p negativeOne) (pmul p negativeOne))
        (padd (pmul p boundary) (pmul p boundary)))
      (q_add_congr
        (coeff_padd index (pmul p negativeOne) (pmul p negativeOne))
        (coeff_padd index (pmul p boundary) (pmul p boundary)))) ?_
  refine Q'.eqv_trans _
    (((-(coeff p index)) + (-(coeff p index))) + (0 + 0)) _
    (q_add_congr
      (q_add_congr
        (coeff_pmul_pneg_pconst_one p index)
        (coeff_pmul_pneg_pconst_one p index))
      (q_add_congr
        (coeff_pmul_ppow_pvar_right_eqv_zero_of_lt
          p (2 * stage) index hindex)
        (coeff_pmul_ppow_pvar_right_eqv_zero_of_lt
          p (2 * stage) index hindex))) ?_
  refine Q'.eqv_trans _
    ((-(coeff p index)) + (-(coeff p index))) _
    (Q'.eqv_trans _
      (((-(coeff p index)) + (-(coeff p index))) + 0) _
      (Q'.add_eqv_congr_left _ _ 0 (q_zero_add_eqv 0))
      (q_add_zero_eqv _)) ?_
  exact Q'.eqv_symm (negativeTwo_mul_eqv_neg_add_neg (coeff p index))

/-- Coefficients of `(1-z^2)p` are the local two-step difference of the
coefficients of `p`. -/
theorem coeff_oneSubSquarePoly_pmul (p : Poly) (index : Nat) :
    (coeff (pmul oneSubSquarePoly p) index).eqv
      (coeff p index +
        (if 2 <= index then -(coeff p (index - 2)) else 0)) := by
  have hexpanded :
      CoeffEqv (pmul oneSubSquarePoly p)
        (padd p (pneg (pmul (ppow pvar 2) p))) := by
    unfold oneSubSquarePoly
    exact CoeffEqv.trans
      (coeffEqv_padd_pmul_left
        (pconst 1) (pneg (ppow pvar 2)) p)
      (CoeffEqv.padd
        (coeffEqv_pmul_one_left p)
        (coeffEqv_pscale_pmul (-1) (ppow pvar 2) p))
  refine Q'.eqv_trans _
    (coeff (padd p (pneg (pmul (ppow pvar 2) p))) index) _
    (hexpanded index) ?_
  refine Q'.eqv_trans _
    (coeff p index + coeff (pneg (pmul (ppow pvar 2) p)) index) _
    (coeff_padd index p (pneg (pmul (ppow pvar 2) p))) ?_
  refine Q'.eqv_trans _
    (coeff p index + -(coeff (pmul (ppow pvar 2) p) index)) _
    (Q'.add_eqv_congr_left _ _ _
      (coeff_pneg_eqv (pmul (ppow pvar 2) p) index)) ?_
  by_cases htwo : 2 <= index
  · rw [if_pos htwo]
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_trans _
          (if 2 <= index then coeff p (index - 2) else 0) _
          (coeff_pmul_ppow_pvar 2 p index)
          (by rw [if_pos htwo]; exact Q'.eqv_refl _)))
  · rw [if_neg htwo]
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_trans _ (-(0 : Q')) _
        (Q'.neg_eqv_congr _ 0
          (Q'.eqv_trans _
            (if 2 <= index then coeff p (index - 2) else 0) _
            (coeff_pmul_ppow_pvar 2 p index)
            (by rw [if_neg htwo]; exact Q'.eqv_refl 0)))
        (by decide))

/-- A zero-constant exponent makes its `k`-th Euler term start in degree
`k`.  This is the formal reason a finite Euler sum with `inner` terms already
has all coefficients below `inner` stabilized. -/
theorem zeroPrefix_expTermPoly
    (exponent : Poly) (hexponent : zeroPrefix 1 exponent) :
    forall k : Nat, zeroPrefix k (expTermPoly exponent k)
  | 0 => by rfl
  | k + 1 => by
      have hstep : zeroPrefix 1 (expStepPoly exponent k) := by
        unfold expStepPoly pneg
        exact zeroPrefix_pscale 1 (Q'.invSucc k) _
          (zeroPrefix_pscale 1 (-1) exponent hexponent)
      exact zeroPrefix_pmul_add k 1
        (expTermPoly exponent k) (expStepPoly exponent k)
        (zeroPrefix_expTermPoly exponent hexponent k) hstep

/-- Adding the next Euler term cannot change any coefficient below the
current truncation length. -/
theorem coeff_expPartialPoly_succ_stable
    (exponent : Poly) (hexponent : zeroPrefix 1 exponent)
    (inner index : Nat) (hindex : index < inner) :
    (coeff (expPartialPoly exponent (inner + 1)) index).eqv
      (coeff (expPartialPoly exponent inner) index) := by
  refine Q'.eqv_trans _
    (coeff (expPartialPoly exponent inner) index +
      coeff (expTermPoly exponent inner) index) _
    (coeff_padd index _ _) ?_
  exact Q'.eqv_trans _
    (coeff (expPartialPoly exponent inner) index + 0) _
    (q_add_congr (Q'.eqv_refl _)
      (coeff_eqv_zero_of_zeroPrefix inner _
        (zeroPrefix_expTermPoly exponent hexponent inner) index hindex))
    (q_add_zero_eqv _)

/-- Once an Euler coefficient is present, every later finite partial sum has
exactly the same coefficient. -/
theorem coeff_expPartialPoly_add_stable
    (exponent : Poly) (hexponent : zeroPrefix 1 exponent)
    (inner extra index : Nat) (hindex : index < inner) :
    (coeff (expPartialPoly exponent (inner + extra)) index).eqv
      (coeff (expPartialPoly exponent inner) index) := by
  induction extra with
  | zero => exact Q'.eqv_refl _
  | succ extra ih =>
      have hlt : index < inner + extra :=
        Nat.lt_of_lt_of_le hindex (Nat.le_add_right inner extra)
      rw [Nat.add_succ]
      exact Q'.eqv_trans _ _ _
        (coeff_expPartialPoly_succ_stable exponent hexponent
          (inner + extra) index hlt)
        ih

theorem eval_expTermPoly
    (exponent : Poly) (z value : Q')
    (hvalue : (eval exponent z).eqv value) :
    forall k : Nat,
      (eval (expTermPoly exponent k) z).eqv (ExpNeg.term value k)
  | 0 => Q'.eqv_trans _ _ _ (eval_pconst 1 z) (Q'.eqv_refl 1)
  | k + 1 =>
      Q'.eqv_trans _ _ _
        (eval_pmul (expTermPoly exponent k) (expStepPoly exponent k) z)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right
            (eval (expTermPoly exponent k) z) (ExpNeg.term value k)
            (eval (expStepPoly exponent k) z)
            (eval_expTermPoly exponent z value hvalue k))
          (Q'.mul_eqv_congr_left (ExpNeg.term value k)
            (eval (expStepPoly exponent k) z)
            ((-value) * Q'.invSucc k)
            (eval_expStepPoly exponent z value hvalue k)))

/-- Generic coefficient-norm majorant for a reflected finite exponential
term. -/
theorem weightedL1_expTermPoly_le
    (rho : Q') (hrho : (0 : Q') <= rho) (exponent : Poly) :
    forall k : Nat,
      weightedL1 rho (expTermPoly exponent k) <=
        ExpNeg.termAbs (weightedL1 rho exponent) k
  | 0 => Q'.le_of_eqv (weightedL1_pconst_eqv rho 1)
  | k + 1 => by
      let normExponent : Q' := weightedL1 rho exponent
      let normTerm : Q' := weightedL1 rho (expTermPoly exponent k)
      let normStep : Q' := weightedL1 rho (expStepPoly exponent k)
      have hmul := weightedL1_pmul_le rho hrho
        (expTermPoly exponent k) (expStepPoly exponent k)
      have hterm : normTerm <= ExpNeg.termAbs normExponent k :=
        weightedL1_expTermPoly_le rho hrho exponent k
      have hscale := weightedL1_pscale_le rho hrho (Q'.invSucc k)
        (pneg exponent)
      have hinvAbs : (Q'.abs (Q'.invSucc k)).eqv (Q'.invSucc k) :=
        Q'.eqv_of_eq (ExpNeg.abs_of_nonneg (Q'.invSucc_nonneg k))
      have hneg := weightedL1_pneg_le rho hrho exponent
      have hstep : normStep <= normExponent * Q'.invSucc k := by
        refine Q'.le_trans' _ _ _ hscale ?_
        have hscaledNeg :
            Q'.abs (Q'.invSucc k) * weightedL1 rho (pneg exponent) <=
              Q'.abs (Q'.invSucc k) * normExponent :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ hneg
            (Q'.abs_nonneg (Q'.invSucc k))
        refine Q'.le_trans' _ _ _ hscaledNeg (Q'.le_of_eqv ?_)
        refine Q'.eqv_trans _ (Q'.invSucc k * normExponent) _
          (Q'.mul_eqv_congr_right _ _ _ hinvAbs) ?_
        exact Q'.mul_comm_eqv (Q'.invSucc k) normExponent
      have hfirst : normTerm * normStep <=
          ExpNeg.termAbs normExponent k * normStep :=
        Q'.mul_le_mul_of_nonneg_right _ _ normStep hterm
          (weightedL1_nonnegative rho hrho (expStepPoly exponent k))
      have hsecond : ExpNeg.termAbs normExponent k * normStep <=
          ExpNeg.termAbs normExponent k *
            (normExponent * Q'.invSucc k) :=
        Q'.mul_le_mul_of_nonneg_left _ _
          (ExpNeg.termAbs normExponent k) hstep
          (ExpNeg.termAbs_nonneg normExponent
            (weightedL1_nonnegative rho hrho exponent) k)
      exact Q'.le_trans' _ _ _ hmul
        (Q'.le_trans' _ _ _ hfirst hsecond)

theorem eval_expPartialPoly
    (exponent : Poly) (z value : Q')
    (hvalue : (eval exponent z).eqv value) :
    forall inner : Nat,
      (eval (expPartialPoly exponent inner) z).eqv
        (ExpNeg.partialSum value inner)
  | 0 => Q'.eqv_refl 0
  | inner + 1 =>
      Q'.eqv_trans _ _ _
        (eval_padd (expPartialPoly exponent inner)
          (expTermPoly exponent inner) z)
        (q_add_congr
          (eval_expPartialPoly exponent z value hvalue inner)
          (eval_expTermPoly exponent z value hvalue inner))

/-- Generic coefficient-norm majorant for the reflected finite exponential
partial sum. -/
theorem weightedL1_expPartialPoly_le
    (rho : Q') (hrho : (0 : Q') <= rho) (exponent : Poly) :
    forall inner : Nat,
      weightedL1 rho (expPartialPoly exponent inner) <=
        ExpNeg.partialSumAbs (weightedL1 rho exponent) inner
  | 0 => Q'.le_refl' 0
  | inner + 1 => by
      have hadd := weightedL1_padd_le rho hrho
        (expPartialPoly exponent inner) (expTermPoly exponent inner)
      exact Q'.le_trans' _ _ _ hadd
        (Q'.add_le_add
          (weightedL1_expPartialPoly_le rho hrho exponent inner)
          (weightedL1_expTermPoly_le rho hrho exponent inner))

theorem eval_positiveArtanhExpPartialPoly
    (z : Q') (stage inner : Nat) :
    (eval (expPartialPoly (positiveArtanhExponentPoly stage) inner) z).eqv
      (ExpNeg.partialSum (positiveArtanhExponent z stage) inner) :=
  eval_expPartialPoly (positiveArtanhExponentPoly stage) z
    (positiveArtanhExponent z stage)
    (eval_positiveArtanhExponentPoly z stage) inner

/-- Polynomial for `sum_{k=0}^{degree} (-z)^k`. -/
def geometricSumPoly : Nat -> Poly
  | 0 => pconst 1
  | degree + 1 => padd (geometricSumPoly degree)
      (ppow (pneg pvar) (degree + 1))

/-- Exact coefficients of the finite geometric sum.  Inside its truncation
window they are `(-1)^index`; all higher coefficients vanish. -/
theorem coeff_geometricSumPoly : forall (degree index : Nat),
    (coeff (geometricSumPoly degree) index).eqv
      (if index <= degree then ((-1 : Q') ^ index) else 0)
  | 0, 0 => Q'.eqv_refl 1
  | 0, index + 1 => by
      rw [if_neg (by omega : ¬ index + 1 <= 0)]
      exact Q'.eqv_refl 0
  | degree + 1, index => by
      refine Q'.eqv_trans _
        (coeff (geometricSumPoly degree) index +
          coeff (ppow (pneg pvar) (degree + 1)) index) _
        (coeff_padd index _ _) ?_
      by_cases hle : index <= degree
      · rw [if_pos (by omega : index <= degree + 1)]
        have hne : index ≠ degree + 1 := by omega
        exact Q'.eqv_trans _ (((-1 : Q') ^ index) + 0) _
          (q_add_congr
            (Q'.eqv_trans _
              (if index <= degree then ((-1 : Q') ^ index) else 0) _
              (coeff_geometricSumPoly degree index)
              (by rw [if_pos hle]; exact Q'.eqv_refl _))
            (Q'.eqv_trans _
              (if index = degree + 1 then
                ((-1 : Q') ^ (degree + 1)) else 0) _
              (coeff_ppow_neg_pvar (degree + 1) index)
              (by rw [if_neg hne]; exact Q'.eqv_refl 0)))
          (q_add_zero_eqv _)
      · by_cases heq : index = degree + 1
        · subst index
          rw [if_pos (by omega : degree + 1 <= degree + 1)]
          exact Q'.eqv_trans _ (0 + ((-1 : Q') ^ (degree + 1))) _
            (q_add_congr
              (Q'.eqv_trans _
                (if degree + 1 <= degree then
                  ((-1 : Q') ^ (degree + 1)) else 0) _
                (coeff_geometricSumPoly degree (degree + 1))
                (by rw [if_neg (by omega)]; exact Q'.eqv_refl 0))
              (Q'.eqv_trans _
                (if degree + 1 = degree + 1 then
                  ((-1 : Q') ^ (degree + 1)) else 0) _
                (coeff_ppow_neg_pvar (degree + 1) (degree + 1))
                (by rw [if_pos rfl]; exact Q'.eqv_refl _)))
            (q_zero_add_eqv _)
        · rw [if_neg (by omega : ¬ index <= degree + 1)]
          exact Q'.eqv_trans _ (0 + 0) _
            (q_add_congr
              (Q'.eqv_trans _
                (if index <= degree then ((-1 : Q') ^ index) else 0) _
                (coeff_geometricSumPoly degree index)
                (by rw [if_neg hle]; exact Q'.eqv_refl 0))
              (Q'.eqv_trans _
                (if index = degree + 1 then
                  ((-1 : Q') ^ (degree + 1)) else 0) _
                (coeff_ppow_neg_pvar (degree + 1) index)
                (by rw [if_neg heq]; exact Q'.eqv_refl 0)))
            (q_add_zero_eqv 0)

theorem eval_neg_pvar (z : Q') :
    (eval (pneg pvar) z).eqv (-z) :=
  Q'.eqv_trans _ _ _ (eval_pneg pvar z)
    (Q'.neg_eqv_congr _ _ (eval_pvar z))

theorem eval_geometricSumPoly (z : Q') :
    forall degree : Nat,
      (eval (geometricSumPoly degree) z).eqv
        (QGeometricSum.geomSum (-z) degree)
  | 0 => Q'.eqv_trans _ _ _ (eval_pconst 1 z) (Q'.eqv_refl 1)
  | degree + 1 => by
      refine Q'.eqv_trans _ _ _
        (eval_padd (geometricSumPoly degree)
          (ppow (pneg pvar) (degree + 1)) z) ?_
      refine q_add_congr (eval_geometricSumPoly z degree) ?_
      exact Q'.eqv_trans _ _ _
        (eval_ppow (pneg pvar) z (degree + 1))
        (pow_eqv_congr (eval_neg_pvar z) (degree + 1))

/-- Polynomial for `(1-z)`. -/
def positiveArtanhNumeratorPoly : Poly :=
  padd (pconst 1) (pneg pvar)

theorem eval_positiveArtanhNumeratorPoly (z : Q') :
    (eval positiveArtanhNumeratorPoly z).eqv ((1 : Q') + -z) := by
  refine Q'.eqv_trans _ _ _
    (eval_padd (pconst 1) (pneg pvar) z) ?_
  exact q_add_congr (eval_pconst 1 z) (eval_neg_pvar z)

/-- Coefficient polynomial for the finite geometric approximation. -/
def positiveArtanhGeometricApproxPoly (degree : Nat) : Poly :=
  pmul (geometricSumPoly degree) positiveArtanhNumeratorPoly

/-- Closed coefficient target for `(1-z)/(1+z)`: constant coefficient one,
then twice the alternating sign. -/
def positiveArtanhFormalTargetCoeff : Nat -> Q'
  | 0 => 1
  | index + 1 =>
      ((-1 : Q') ^ (index + 1)) + ((-1 : Q') ^ (index + 1))

/-- Below its truncation boundary, the finite geometric comparison already
has the closed target coefficient. -/
theorem coeff_positiveArtanhGeometricApproxPoly_eq_target :
    forall (degree index : Nat), index < degree + 1 ->
      (coeff (positiveArtanhGeometricApproxPoly degree) index).eqv
        (positiveArtanhFormalTargetCoeff index)
  | degree, 0, hindex => by
      unfold positiveArtanhGeometricApproxPoly
        positiveArtanhNumeratorPoly pconst pneg pvar
      change (coeff
        (pmul (geometricSumPoly degree)
          [(1 : Q') + (-1 : Q') * 0, (-1 : Q') * 1]) 0).eqv 1
      refine Q'.eqv_trans _
        (coeff (geometricSumPoly degree) 0 *
          ((1 : Q') + (-1 : Q') * 0)) _
        (coeff_pmul_pair_zero _ _ _) ?_
      have hgeom := coeff_geometricSumPoly degree 0
      rw [if_pos (by omega : 0 <= degree)] at hgeom
      have hb0 : ((1 : Q') + (-1 : Q') * 0).eqv 1 :=
        Q'.eqv_trans _ (1 + 0) _
          (Q'.add_eqv_congr_left 1 _ 0 (q_mul_zero (-1)))
          (q_add_zero_eqv 1)
      exact Q'.eqv_trans _ (1 * 1) _
        (q_mul_congr hgeom hb0)
        (Q'.one_mul_eqv 1)
  | degree, index + 1, hindex => by
      unfold positiveArtanhGeometricApproxPoly
        positiveArtanhNumeratorPoly pconst pneg pvar
      change (coeff
        (pmul (geometricSumPoly degree)
          [(1 : Q') + (-1 : Q') * 0, (-1 : Q') * 1])
        (index + 1)).eqv
          (((-1 : Q') ^ (index + 1)) +
            ((-1 : Q') ^ (index + 1)))
      refine Q'.eqv_trans _
        (coeff (geometricSumPoly degree) (index + 1) *
            ((1 : Q') + (-1 : Q') * 0) +
          coeff (geometricSumPoly degree) index * ((-1 : Q') * 1)) _
        (coeff_pmul_pair_succ _ _ _ index) ?_
      have hnext := coeff_geometricSumPoly degree (index + 1)
      have hprev := coeff_geometricSumPoly degree index
      rw [if_pos (by omega : index + 1 <= degree)] at hnext
      rw [if_pos (by omega : index <= degree)] at hprev
      have hb0 : ((1 : Q') + (-1 : Q') * 0).eqv 1 :=
        Q'.eqv_trans _ (1 + 0) _
          (Q'.add_eqv_congr_left 1 _ 0 (q_mul_zero (-1)))
          (q_add_zero_eqv 1)
      have hb1 : ((-1 : Q') * 1).eqv (-1 : Q') :=
        Q'.mul_one_eqv (-1)
      refine Q'.eqv_trans _
        (((-1 : Q') ^ (index + 1)) * 1 +
          ((-1 : Q') ^ index) * (-1 : Q')) _
        (q_add_congr
          (q_mul_congr hnext hb0)
          (q_mul_congr hprev hb1)) ?_
      exact q_add_congr
        (Q'.mul_one_eqv ((-1 : Q') ^ (index + 1)))
        (Q'.mul_comm_eqv ((-1 : Q') ^ index) (-1))

theorem eval_positiveArtanhGeometricApproxPoly
    (z : Q') (degree : Nat) :
    (eval (positiveArtanhGeometricApproxPoly degree) z).eqv
      (positiveArtanhGeometricApprox z degree) := by
  refine Q'.eqv_trans _ _ _
    (eval_pmul (geometricSumPoly degree)
      positiveArtanhNumeratorPoly z) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right
      (eval (geometricSumPoly degree) z)
      (QGeometricSum.geomSum (-z) degree)
      (eval positiveArtanhNumeratorPoly z)
      (eval_geometricSumPoly z degree)) ?_
  exact Q'.mul_eqv_congr_left
    (QGeometricSum.geomSum (-z) degree)
    (eval positiveArtanhNumeratorPoly z) ((1 : Q') + -z)
    (eval_positiveArtanhNumeratorPoly z)

/-- The exact coefficient polynomial for the current finite difference. -/
def positiveArtanhEulerGeometricDifferencePoly
    (stage inner degree : Nat) : Poly :=
  psub
    (expPartialPoly (positiveArtanhExponentPoly stage) inner)
    (positiveArtanhGeometricApproxPoly degree)

theorem eval_positiveArtanhEulerGeometricDifferencePoly
    (z : Q') (stage inner degree : Nat) :
    (eval (positiveArtanhEulerGeometricDifferencePoly
      stage inner degree) z).eqv
      (ExpNeg.partialSum (positiveArtanhExponent z stage) inner +
        -(positiveArtanhGeometricApprox z degree)) := by
  refine Q'.eqv_trans _ _ _
    (eval_psub
      (expPartialPoly (positiveArtanhExponentPoly stage) inner)
      (positiveArtanhGeometricApproxPoly degree) z) ?_
  exact q_add_congr
    (eval_positiveArtanhExpPartialPoly z stage inner)
    (Q'.neg_eqv_congr _ _
      (eval_positiveArtanhGeometricApproxPoly z degree))

/-! ## Constant and linear formal jets -/

theorem constantCoeff_pconst (c : Q') :
    (constantCoeff (pconst c)).eqv c := Q'.eqv_refl c

theorem linearCoeff_pconst (c : Q') :
    (linearCoeff (pconst c)).eqv 0 := Q'.eqv_refl 0

theorem constantCoeff_pvar : (constantCoeff pvar).eqv 0 :=
  Q'.eqv_refl 0

theorem linearCoeff_pvar : (linearCoeff pvar).eqv 1 :=
  Q'.eqv_refl 1

/-- A positive power of a zero-constant polynomial again has zero constant
coefficient. -/
theorem constantCoeff_ppow_succ_eqv_zero
    (p : Poly) (hconstant : (constantCoeff p).eqv 0) (n : Nat) :
    (constantCoeff (ppow p (n + 1))).eqv 0 := by
  refine Q'.eqv_trans _
    (constantCoeff p * constantCoeff (ppow p n)) _
    (constantCoeff_pmul p (ppow p n)) ?_
  exact Q'.eqv_trans _ (0 * constantCoeff (ppow p n)) _
    (Q'.mul_eqv_congr_right _ 0 _ hconstant)
    (q_zero_mul _)

/-- The linear jet of the first power is the original linear jet when the
constant coefficient vanishes. -/
theorem linearCoeff_ppow_one
    (p : Poly) (hconstant : (constantCoeff p).eqv 0) :
    (linearCoeff (ppow p 1)).eqv (linearCoeff p) := by
  refine Q'.eqv_trans _
    (constantCoeff p * linearCoeff (pconst 1) +
      linearCoeff p * constantCoeff (pconst 1)) _
    (linearCoeff_pmul p (pconst 1)) ?_
  refine Q'.eqv_trans _
    (0 * 0 + linearCoeff p * 1) _
    (q_add_congr
      (Q'.eqv_trans _ (0 * linearCoeff (pconst 1)) _
        (Q'.mul_eqv_congr_right _ 0 _ hconstant)
        (q_zero_mul _))
      (Q'.mul_eqv_congr_left (linearCoeff p) _ 1
        (constantCoeff_pconst 1))) ?_
  exact Q'.eqv_trans _ (0 + linearCoeff p) _
    (q_add_congr (q_zero_mul 0) (Q'.mul_one_eqv _))
    (q_zero_add_eqv _)

/-- Every power of degree at least two has zero linear coefficient when its
base has zero constant coefficient. -/
theorem linearCoeff_ppow_add_two_eqv_zero
    (p : Poly) (hconstant : (constantCoeff p).eqv 0) (n : Nat) :
    (linearCoeff (ppow p (n + 2))).eqv 0 := by
  have htail := constantCoeff_ppow_succ_eqv_zero p hconstant n
  refine Q'.eqv_trans _
    (constantCoeff p * linearCoeff (ppow p (n + 1)) +
      linearCoeff p * constantCoeff (ppow p (n + 1))) _
    (linearCoeff_pmul p (ppow p (n + 1))) ?_
  refine Q'.eqv_trans _ (0 * linearCoeff (ppow p (n + 1)) +
      linearCoeff p * 0) _
    (q_add_congr
      (Q'.mul_eqv_congr_right _ 0 _ hconstant)
      (Q'.mul_eqv_congr_left (linearCoeff p) _ 0 htail)) ?_
  exact Q'.eqv_trans _ (0 + 0) _
    (q_add_congr (q_zero_mul _) (q_mul_zero _))
    (q_add_zero_eqv 0)

theorem constantCoeff_artanhTermPoly_eqv_zero (k : Nat) :
    (constantCoeff (artanhTermPoly k)).eqv 0 := by
  refine Q'.eqv_trans _
    (CRealLog.recipOdd k *
      constantCoeff (ppow pvar (2 * k + 1))) _
    (constantCoeff_pscale _ _) ?_
  exact Q'.eqv_trans _ (CRealLog.recipOdd k * 0) _
    (Q'.mul_eqv_congr_left _ _ 0
      (constantCoeff_ppow_succ_eqv_zero pvar constantCoeff_pvar (2 * k)))
    (q_mul_zero _)

theorem linearCoeff_artanhTermPoly_zero_eqv_one :
    (linearCoeff (artanhTermPoly 0)).eqv 1 := by
  refine Q'.eqv_trans _
    (CRealLog.recipOdd 0 * linearCoeff (ppow pvar 1)) _
    (linearCoeff_pscale _ _) ?_
  refine Q'.eqv_trans _
    (CRealLog.recipOdd 0 * linearCoeff pvar) _
    (Q'.mul_eqv_congr_left _ _ _
      (linearCoeff_ppow_one pvar constantCoeff_pvar)) ?_
  exact Q'.eqv_trans _ (CRealLog.recipOdd 0 * 1) _
    (Q'.mul_eqv_congr_left _ _ 1 linearCoeff_pvar)
    (by decide)

theorem linearCoeff_artanhTermPoly_succ_eqv_zero (k : Nat) :
    (linearCoeff (artanhTermPoly (k + 1))).eqv 0 := by
  have hexponent : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
  unfold artanhTermPoly
  rw [hexponent]
  refine Q'.eqv_trans _
    (CRealLog.recipOdd (k + 1) *
      linearCoeff (ppow pvar ((2 * k + 1) + 2))) _
    (linearCoeff_pscale _ _) ?_
  exact Q'.eqv_trans _ (CRealLog.recipOdd (k + 1) * 0) _
    (Q'.mul_eqv_congr_left _ _ 0
      (linearCoeff_ppow_add_two_eqv_zero
        pvar constantCoeff_pvar (2 * k + 1)))
    (q_mul_zero _)

theorem constantCoeff_artanhPartialPoly_eqv_zero :
    forall stage : Nat,
      (constantCoeff (artanhPartialPoly stage)).eqv 0
  | 0 => Q'.eqv_refl 0
  | stage + 1 => by
      refine Q'.eqv_trans _
        (constantCoeff (artanhPartialPoly stage) +
          constantCoeff (artanhTermPoly stage)) _
        (constantCoeff_padd _ _) ?_
      exact Q'.eqv_trans _ (0 + 0) _
        (q_add_congr
          (constantCoeff_artanhPartialPoly_eqv_zero stage)
          (constantCoeff_artanhTermPoly_eqv_zero stage))
        (q_add_zero_eqv 0)

theorem linearCoeff_artanhPartialPoly_succ_eqv_one :
    forall stage : Nat,
      (linearCoeff (artanhPartialPoly (stage + 1))).eqv 1
  | 0 => by
      refine Q'.eqv_trans _
        (linearCoeff (artanhPartialPoly 0) +
          linearCoeff (artanhTermPoly 0)) _
        (linearCoeff_padd _ _) ?_
      exact Q'.eqv_trans _ (0 + 1) _
        (q_add_congr (Q'.eqv_refl 0)
          linearCoeff_artanhTermPoly_zero_eqv_one)
        (q_zero_add_eqv 1)
  | stage + 1 => by
      refine Q'.eqv_trans _
        (linearCoeff (artanhPartialPoly (stage + 1)) +
          linearCoeff (artanhTermPoly (stage + 1))) _
        (linearCoeff_padd _ _) ?_
      exact Q'.eqv_trans _ (1 + 0) _
        (q_add_congr
          (linearCoeff_artanhPartialPoly_succ_eqv_one stage)
          (linearCoeff_artanhTermPoly_succ_eqv_zero stage))
        (q_add_zero_eqv 1)

theorem constantCoeff_positiveArtanhExponentPoly_eqv_zero (stage : Nat) :
    (constantCoeff (positiveArtanhExponentPoly stage)).eqv 0 := by
  refine Q'.eqv_trans _
    (constantCoeff (artanhPartialPoly stage) +
      constantCoeff (artanhPartialPoly stage)) _
    (constantCoeff_padd _ _) ?_
  exact Q'.eqv_trans _ (0 + 0) _
    (q_add_congr
      (constantCoeff_artanhPartialPoly_eqv_zero stage)
      (constantCoeff_artanhPartialPoly_eqv_zero stage))
    (q_add_zero_eqv 0)

/-- The reflected finite artanh exponent has constructive valuation at least
one at every outer stage. -/
theorem zeroPrefix_one_positiveArtanhExponentPoly (stage : Nat) :
    zeroPrefix 1 (positiveArtanhExponentPoly stage) :=
  zeroPrefix_of_coeff_eqv_zero 1 _ (fun index hindex => by
    have hzero : index = 0 := by omega
    subst index
    exact Q'.eqv_trans _ _ _
      (coeff_zero_eq_constantCoeff _)
      (constantCoeff_positiveArtanhExponentPoly_eqv_zero stage))

/-- The `k`-th reflected Euler term starts in degree `k`, uniformly in the
finite artanh stage. -/
theorem zeroPrefix_positiveArtanhExpTermPoly
    (stage k : Nat) :
    zeroPrefix k
      (expTermPoly (positiveArtanhExponentPoly stage) k) :=
  zeroPrefix_expTermPoly _
    (zeroPrefix_one_positiveArtanhExponentPoly stage) k

theorem linearCoeff_positiveArtanhExponentPoly_succ_eqv_two
    (stage : Nat) :
    (linearCoeff (positiveArtanhExponentPoly (stage + 1))).eqv
      ((1 : Q') + 1) := by
  refine Q'.eqv_trans _
    (linearCoeff (artanhPartialPoly (stage + 1)) +
      linearCoeff (artanhPartialPoly (stage + 1))) _
    (linearCoeff_padd _ _) ?_
  exact q_add_congr
    (linearCoeff_artanhPartialPoly_succ_eqv_one stage)
    (linearCoeff_artanhPartialPoly_succ_eqv_one stage)

theorem constantCoeff_expStepPoly_eqv_zero
    (exponent : Poly) (hconstant : (constantCoeff exponent).eqv 0)
    (k : Nat) :
    (constantCoeff (expStepPoly exponent k)).eqv 0 := by
  refine Q'.eqv_trans _
    (Q'.invSucc k * constantCoeff (pneg exponent)) _
    (constantCoeff_pscale _ _) ?_
  refine Q'.eqv_trans _
    (Q'.invSucc k * ((-1 : Q') * constantCoeff exponent)) _
    (Q'.mul_eqv_congr_left _ _ _ (constantCoeff_pneg exponent)) ?_
  refine Q'.eqv_trans _
    (Q'.invSucc k * ((-1 : Q') * 0)) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left (-1) _ 0 hconstant)) ?_
  exact Q'.eqv_trans _ (Q'.invSucc k * 0) _
    (Q'.mul_eqv_congr_left _ _ 0 (q_mul_zero (-1)))
    (q_mul_zero _)

theorem linearCoeff_expStepPoly_eqv
    (exponent : Poly) (k : Nat) :
    (linearCoeff (expStepPoly exponent k)).eqv
      (Q'.invSucc k * ((-1 : Q') * linearCoeff exponent)) := by
  exact Q'.eqv_trans _ _ _ (linearCoeff_pscale _ _)
    (Q'.mul_eqv_congr_left _ _ _ (linearCoeff_pneg exponent))

theorem constantCoeff_expTermPoly_zero (exponent : Poly) :
    (constantCoeff (expTermPoly exponent 0)).eqv 1 :=
  constantCoeff_pconst 1

theorem constantCoeff_expTermPoly_succ_eqv_zero
    (exponent : Poly) (hconstant : (constantCoeff exponent).eqv 0) :
    forall k : Nat,
      (constantCoeff (expTermPoly exponent (k + 1))).eqv 0
  | k => by
      refine Q'.eqv_trans _
        (constantCoeff (expTermPoly exponent k) *
          constantCoeff (expStepPoly exponent k)) _
        (constantCoeff_pmul _ _) ?_
      exact Q'.eqv_trans _
        (constantCoeff (expTermPoly exponent k) * 0) _
        (Q'.mul_eqv_congr_left _ _ 0
          (constantCoeff_expStepPoly_eqv_zero exponent hconstant k))
        (q_mul_zero _)

theorem linearCoeff_expTermPoly_zero (exponent : Poly) :
    (linearCoeff (expTermPoly exponent 0)).eqv 0 :=
  linearCoeff_pconst 1

theorem linearCoeff_expTermPoly_one_eqv_negativeTwo
    (stage : Nat) :
    (linearCoeff
      (expTermPoly (positiveArtanhExponentPoly (stage + 1)) 1)).eqv
      negativeTwo := by
  let exponent := positiveArtanhExponentPoly (stage + 1)
  have hconstant :=
    constantCoeff_positiveArtanhExponentPoly_eqv_zero (stage + 1)
  refine Q'.eqv_trans _
    (constantCoeff (expTermPoly exponent 0) *
        linearCoeff (expStepPoly exponent 0) +
      linearCoeff (expTermPoly exponent 0) *
        constantCoeff (expStepPoly exponent 0)) _
    (linearCoeff_pmul _ _) ?_
  refine Q'.eqv_trans _
    (1 * (Q'.invSucc 0 * ((-1 : Q') * ((1 : Q') + 1))) +
      0 * 0) _
    (q_add_congr
      (Q'.eqv_trans _
        (1 * linearCoeff (expStepPoly exponent 0)) _
        (Q'.mul_eqv_congr_right _ 1 _
          (constantCoeff_expTermPoly_zero exponent))
        (Q'.mul_eqv_congr_left 1 _ _
          (Q'.eqv_trans _ _ _
            (linearCoeff_expStepPoly_eqv exponent 0)
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.mul_eqv_congr_left (-1) _ _
                (linearCoeff_positiveArtanhExponentPoly_succ_eqv_two stage))))))
      (Q'.eqv_trans _
        (0 * constantCoeff (expStepPoly exponent 0)) _
        (Q'.mul_eqv_congr_right _ 0 _
          (linearCoeff_expTermPoly_zero exponent))
        (Q'.mul_eqv_congr_left 0 _ 0
          (constantCoeff_expStepPoly_eqv_zero exponent hconstant 0)))) ?_
  exact Q'.eqv_trans _
    (Q'.invSucc 0 * ((-1 : Q') * ((1 : Q') + 1))) _
    (Q'.eqv_trans _ _ _
      (q_add_congr (Q'.one_mul_eqv _) (q_mul_zero 0))
      (q_add_zero_eqv _))
    (by decide)

theorem linearCoeff_expTermPoly_add_two_eqv_zero
    (stage k : Nat) :
    (linearCoeff
      (expTermPoly (positiveArtanhExponentPoly (stage + 1)) (k + 2))).eqv
      0 := by
  let exponent := positiveArtanhExponentPoly (stage + 1)
  have hconstant :=
    constantCoeff_positiveArtanhExponentPoly_eqv_zero (stage + 1)
  refine Q'.eqv_trans _
    (constantCoeff (expTermPoly exponent (k + 1)) *
        linearCoeff (expStepPoly exponent (k + 1)) +
      linearCoeff (expTermPoly exponent (k + 1)) *
        constantCoeff (expStepPoly exponent (k + 1))) _
    (linearCoeff_pmul _ _) ?_
  refine Q'.eqv_trans _
    (0 * linearCoeff (expStepPoly exponent (k + 1)) +
      linearCoeff (expTermPoly exponent (k + 1)) * 0) _
    (q_add_congr
      (Q'.mul_eqv_congr_right _ 0 _
        (constantCoeff_expTermPoly_succ_eqv_zero exponent hconstant k))
      (Q'.mul_eqv_congr_left _ _ 0
        (constantCoeff_expStepPoly_eqv_zero exponent hconstant (k + 1)))) ?_
  exact Q'.eqv_trans _ (0 + 0) _
    (q_add_congr (q_zero_mul _) (q_mul_zero _))
    (q_add_zero_eqv 0)

theorem constantCoeff_expPartialPoly_succ_eqv_one
    (exponent : Poly) (hconstant : (constantCoeff exponent).eqv 0) :
    forall inner : Nat,
      (constantCoeff (expPartialPoly exponent (inner + 1))).eqv 1
  | 0 => by
      refine Q'.eqv_trans _
        (constantCoeff (expPartialPoly exponent 0) +
          constantCoeff (expTermPoly exponent 0)) _
        (constantCoeff_padd _ _) ?_
      exact Q'.eqv_trans _ (0 + 1) _
        (q_add_congr (Q'.eqv_refl 0)
          (constantCoeff_expTermPoly_zero exponent))
        (q_zero_add_eqv 1)
  | inner + 1 => by
      refine Q'.eqv_trans _
        (constantCoeff (expPartialPoly exponent (inner + 1)) +
          constantCoeff (expTermPoly exponent (inner + 1))) _
        (constantCoeff_padd _ _) ?_
      exact Q'.eqv_trans _ (1 + 0) _
        (q_add_congr
          (constantCoeff_expPartialPoly_succ_eqv_one exponent hconstant inner)
          (constantCoeff_expTermPoly_succ_eqv_zero
            exponent hconstant inner))
        (q_add_zero_eqv 1)

theorem linearCoeff_expPartialPoly_add_two_eqv_negativeTwo :
    forall stage inner : Nat,
      (linearCoeff
        (expPartialPoly (positiveArtanhExponentPoly (stage + 1))
          (inner + 2))).eqv negativeTwo
  | stage, 0 => by
      let exponent := positiveArtanhExponentPoly (stage + 1)
      refine Q'.eqv_trans _
        (linearCoeff (expPartialPoly exponent 1) +
          linearCoeff (expTermPoly exponent 1)) _
        (linearCoeff_padd _ _) ?_
      have hpartialOne :
          (linearCoeff (expPartialPoly exponent 1)).eqv 0 := by
        refine Q'.eqv_trans _
          (linearCoeff (expPartialPoly exponent 0) +
            linearCoeff (expTermPoly exponent 0)) _
          (linearCoeff_padd _ _) ?_
        exact Q'.eqv_trans _ (0 + 0) _
          (q_add_congr (Q'.eqv_refl 0)
            (linearCoeff_expTermPoly_zero exponent))
          (q_add_zero_eqv 0)
      exact Q'.eqv_trans _ (0 + negativeTwo) _
        (q_add_congr hpartialOne
          (linearCoeff_expTermPoly_one_eqv_negativeTwo stage))
        (q_zero_add_eqv negativeTwo)
  | stage, inner + 1 => by
      let exponent := positiveArtanhExponentPoly (stage + 1)
      refine Q'.eqv_trans _
        (linearCoeff (expPartialPoly exponent (inner + 2)) +
          linearCoeff (expTermPoly exponent (inner + 2))) _
        (linearCoeff_padd _ _) ?_
      exact Q'.eqv_trans _ (negativeTwo + 0) _
        (q_add_congr
          (linearCoeff_expPartialPoly_add_two_eqv_negativeTwo stage inner)
          (linearCoeff_expTermPoly_add_two_eqv_zero stage inner))
        (q_add_zero_eqv negativeTwo)

theorem constantCoeff_neg_pvar_eqv_zero :
    (constantCoeff (pneg pvar)).eqv 0 := by
  exact Q'.eqv_trans _ ((-1 : Q') * 0) _
    (Q'.eqv_trans _ _ _ (constantCoeff_pneg pvar)
      (Q'.mul_eqv_congr_left (-1) _ 0 constantCoeff_pvar))
    (q_mul_zero (-1))

theorem linearCoeff_neg_pvar_eqv_neg_one :
    (linearCoeff (pneg pvar)).eqv (-1 : Q') := by
  exact Q'.eqv_trans _ ((-1 : Q') * 1) _
    (Q'.eqv_trans _ _ _ (linearCoeff_pneg pvar)
      (Q'.mul_eqv_congr_left (-1) _ 1 linearCoeff_pvar))
    (Q'.mul_one_eqv (-1))

theorem constantCoeff_geometricSumPoly_eqv_one :
    forall degree : Nat,
      (constantCoeff (geometricSumPoly degree)).eqv 1
  | 0 => constantCoeff_pconst 1
  | degree + 1 => by
      refine Q'.eqv_trans _
        (constantCoeff (geometricSumPoly degree) +
          constantCoeff (ppow (pneg pvar) (degree + 1))) _
        (constantCoeff_padd _ _) ?_
      exact Q'.eqv_trans _ (1 + 0) _
        (q_add_congr
          (constantCoeff_geometricSumPoly_eqv_one degree)
          (constantCoeff_ppow_succ_eqv_zero
            (pneg pvar) constantCoeff_neg_pvar_eqv_zero degree))
        (q_add_zero_eqv 1)

theorem linearCoeff_geometricSumPoly_succ_eqv_neg_one :
    forall degree : Nat,
      (linearCoeff (geometricSumPoly (degree + 1))).eqv (-1 : Q')
  | 0 => by
      refine Q'.eqv_trans _
        (linearCoeff (geometricSumPoly 0) +
          linearCoeff (ppow (pneg pvar) 1)) _
        (linearCoeff_padd _ _) ?_
      exact Q'.eqv_trans _ (0 + (-1 : Q')) _
        (q_add_congr
          (linearCoeff_pconst 1)
          (Q'.eqv_trans _ _ _
            (linearCoeff_ppow_one
              (pneg pvar) constantCoeff_neg_pvar_eqv_zero)
            linearCoeff_neg_pvar_eqv_neg_one))
        (q_zero_add_eqv (-1))
  | degree + 1 => by
      refine Q'.eqv_trans _
        (linearCoeff (geometricSumPoly (degree + 1)) +
          linearCoeff (ppow (pneg pvar) (degree + 2))) _
        (linearCoeff_padd _ _) ?_
      exact Q'.eqv_trans _ ((-1 : Q') + 0) _
        (q_add_congr
          (linearCoeff_geometricSumPoly_succ_eqv_neg_one degree)
          (linearCoeff_ppow_add_two_eqv_zero
            (pneg pvar) constantCoeff_neg_pvar_eqv_zero degree))
        (q_add_zero_eqv (-1))

theorem constantCoeff_positiveArtanhNumeratorPoly_eqv_one :
    (constantCoeff positiveArtanhNumeratorPoly).eqv 1 := by
  refine Q'.eqv_trans _
    (constantCoeff (pconst 1) + constantCoeff (pneg pvar)) _
    (constantCoeff_padd _ _) ?_
  exact Q'.eqv_trans _ (1 + 0) _
    (q_add_congr (constantCoeff_pconst 1)
      constantCoeff_neg_pvar_eqv_zero)
    (q_add_zero_eqv 1)

theorem linearCoeff_positiveArtanhNumeratorPoly_eqv_neg_one :
    (linearCoeff positiveArtanhNumeratorPoly).eqv (-1 : Q') := by
  refine Q'.eqv_trans _
    (linearCoeff (pconst 1) + linearCoeff (pneg pvar)) _
    (linearCoeff_padd _ _) ?_
  exact Q'.eqv_trans _ (0 + (-1 : Q')) _
    (q_add_congr (linearCoeff_pconst 1)
      linearCoeff_neg_pvar_eqv_neg_one)
    (q_zero_add_eqv (-1))

theorem constantCoeff_positiveArtanhGeometricApproxPoly_eqv_one
    (degree : Nat) :
    (constantCoeff (positiveArtanhGeometricApproxPoly degree)).eqv 1 := by
  refine Q'.eqv_trans _
    (constantCoeff (geometricSumPoly degree) *
      constantCoeff positiveArtanhNumeratorPoly) _
    (constantCoeff_pmul _ _) ?_
  exact Q'.eqv_trans _ (1 * 1) _
    (Q'.eqv_trans _
      (1 * constantCoeff positiveArtanhNumeratorPoly) _
      (Q'.mul_eqv_congr_right _ 1 _
        (constantCoeff_geometricSumPoly_eqv_one degree))
      (Q'.mul_eqv_congr_left 1 _ 1
        constantCoeff_positiveArtanhNumeratorPoly_eqv_one))
    (Q'.one_mul_eqv 1)

theorem linearCoeff_positiveArtanhGeometricApproxPoly_succ_eqv_negativeTwo
    (degree : Nat) :
    (linearCoeff
      (positiveArtanhGeometricApproxPoly (degree + 1))).eqv negativeTwo := by
  refine Q'.eqv_trans _
    (constantCoeff (geometricSumPoly (degree + 1)) *
        linearCoeff positiveArtanhNumeratorPoly +
      linearCoeff (geometricSumPoly (degree + 1)) *
        constantCoeff positiveArtanhNumeratorPoly) _
    (linearCoeff_pmul _ _) ?_
  refine Q'.eqv_trans _
    (1 * (-1 : Q') + (-1 : Q') * 1) _
    (q_add_congr
      (Q'.eqv_trans _
        (1 * linearCoeff positiveArtanhNumeratorPoly) _
        (Q'.mul_eqv_congr_right _ 1 _
          (constantCoeff_geometricSumPoly_eqv_one (degree + 1)))
        (Q'.mul_eqv_congr_left 1 _ (-1)
          linearCoeff_positiveArtanhNumeratorPoly_eqv_neg_one))
      (Q'.eqv_trans _
        ((-1 : Q') * constantCoeff positiveArtanhNumeratorPoly) _
        (Q'.mul_eqv_congr_right _ (-1) _
          (linearCoeff_geometricSumPoly_succ_eqv_neg_one degree))
        (Q'.mul_eqv_congr_left (-1) _ 1
          constantCoeff_positiveArtanhNumeratorPoly_eqv_one))) ?_
  decide

theorem constantCoeff_positiveArtanhEulerGeometricDifferencePoly_eqv_zero
    (stage inner degree : Nat) (hstage : 1 <= stage)
    (hinner : 1 <= inner) :
    (constantCoeff (positiveArtanhEulerGeometricDifferencePoly
      stage inner degree)).eqv 0 := by
  cases stage with
  | zero => omega
  | succ stage =>
      cases inner with
      | zero => omega
      | succ inner =>
          let exponent := positiveArtanhExponentPoly (stage + 1)
          refine Q'.eqv_trans _
            (constantCoeff (expPartialPoly exponent (inner + 1)) +
              ((-1 : Q') *
                constantCoeff (positiveArtanhGeometricApproxPoly degree))) _
            (constantCoeff_psub _ _) ?_
          refine Q'.eqv_trans _ (1 + ((-1 : Q') * 1)) _
            (q_add_congr
              (constantCoeff_expPartialPoly_succ_eqv_one exponent
                (constantCoeff_positiveArtanhExponentPoly_eqv_zero
                  (stage + 1)) inner)
              (Q'.mul_eqv_congr_left (-1) _ 1
                (constantCoeff_positiveArtanhGeometricApproxPoly_eqv_one
                  degree))) ?_
          decide

theorem linearCoeff_positiveArtanhEulerGeometricDifferencePoly_eqv_zero
    (stage inner degree : Nat)
    (hstage : 1 <= stage) (hinner : 2 <= inner)
    (hdegree : 1 <= degree) :
    (linearCoeff (positiveArtanhEulerGeometricDifferencePoly
      stage inner degree)).eqv 0 := by
  cases stage with
  | zero => omega
  | succ stage =>
      cases inner with
      | zero => omega
      | succ inner =>
          cases inner with
          | zero => omega
          | succ inner =>
              cases degree with
              | zero => omega
              | succ degree =>
                  let exponent := positiveArtanhExponentPoly (stage + 1)
                  refine Q'.eqv_trans _
                    (linearCoeff (expPartialPoly exponent (inner + 2)) +
                      ((-1 : Q') *
                        linearCoeff
                          (positiveArtanhGeometricApproxPoly (degree + 1)))) _
                    (linearCoeff_psub _ _) ?_
                  refine Q'.eqv_trans _
                    (negativeTwo + ((-1 : Q') * negativeTwo)) _
                    (q_add_congr
                      (linearCoeff_expPartialPoly_add_two_eqv_negativeTwo
                        stage inner)
                      (Q'.mul_eqv_congr_left (-1) _ _
                        (linearCoeff_positiveArtanhGeometricApproxPoly_succ_eqv_negativeTwo
                          degree))) ?_
                  decide

/-- The constant and linear coefficients cancel whenever all three finite
truncations have reached the orders at which those jets stabilize. -/
theorem zeroPrefix_two_positiveArtanhEulerGeometricDifferencePoly
    (stage inner degree : Nat)
    (hstage : 1 <= stage) (hinner : 2 <= inner)
    (hdegree : 1 <= degree) :
    zeroPrefix 2
      (positiveArtanhEulerGeometricDifferencePoly stage inner degree) :=
  zeroPrefix_two_of_coefficients_zero _
    (constantCoeff_positiveArtanhEulerGeometricDifferencePoly_eqv_zero
      stage inner degree hstage (Nat.le_trans (by decide) hinner))
    (linearCoeff_positiveArtanhEulerGeometricDifferencePoly_eqv_zero
      stage inner degree hstage hinner hdegree)

/-! ## The first exact cancellation -/

/-- Every nonconstant Euler term vanishes when its exponent is zero. -/
theorem expTerm_zero_succ_eqv (k : Nat) :
    (ExpNeg.term (0 : Q') (k + 1)).eqv 0 := by
  rw [ExpNeg.term_succ]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (ExpNeg.term 0 k) _ 0 ?_) ?_
  · refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ 0 _
        (by decide : (-(0 : Q')).eqv 0)) ?_
    exact q_zero_mul _
  · exact q_mul_zero _

/-- Every positive-length Euler partial sum at exponent zero is exactly one
up to rational equivalence. -/
theorem expPartialSum_zero_succ_eqv :
    forall n : Nat,
      (ExpNeg.partialSum (0 : Q') (n + 1)).eqv 1
  | 0 => by
      rw [ExpNeg.partialSum_one]
      exact Q'.eqv_refl 1
  | n + 1 => by
      rw [ExpNeg.partialSum_succ]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ 0 (expTerm_zero_succ_eqv n)) ?_
      exact Q'.eqv_trans _ _ _ (q_add_zero_eqv _) (expPartialSum_zero_succ_eqv n)

/-- The finite geometric sum at the rational representative `-0` is one. -/
theorem geometricSum_neg_zero_eqv_one :
    forall degree : Nat,
      (QGeometricSum.geomSum (-(0 : Q')) degree).eqv 1
  | 0 => by
      rw [QGeometricSum.geomSum_zero]
      exact Q'.eqv_refl 1
  | degree + 1 => by
      rw [QGeometricSum.geomSum_succ]
      have hnegZero : (-(0 : Q')).eqv 0 := by decide
      have hpower : ((-(0 : Q')) ^ (degree + 1)).eqv 0 :=
        Q'.eqv_trans _ _ _
          (pow_eqv_congr hnegZero (degree + 1))
          (CRealLog.zero_pow_succ_eqv degree)
      exact Q'.eqv_trans _ (1 + 0) _
        (q_add_congr (geometricSum_neg_zero_eqv_one degree) hpower)
        (q_add_zero_eqv 1)

/-- The reflected positive-artanh exponent vanishes at zero. -/
theorem positiveArtanhExponent_zero_eqv_zero (stage : Nat) :
    (positiveArtanhExponent (0 : Q') stage).eqv 0 := by
  unfold positiveArtanhExponent
  exact Q'.eqv_trans _ (0 + 0) _
    (q_add_congr
      (CRealLog.partialSum_zero_eqv stage)
      (CRealLog.partialSum_zero_eqv stage))
    (q_add_zero_eqv 0)

/-- The finite geometric comparison has constant value one. -/
theorem positiveArtanhGeometricApprox_zero_eqv_one (degree : Nat) :
    (positiveArtanhGeometricApprox (0 : Q') degree).eqv 1 := by
  unfold positiveArtanhGeometricApprox
  have hnegZero : (-(0 : Q')).eqv 0 := by decide
  have hfactor : ((1 : Q') + -(0 : Q')).eqv 1 :=
    Q'.eqv_trans _ (1 + 0) _
      (q_add_congr (Q'.eqv_refl 1) hnegZero)
      (q_add_zero_eqv 1)
  exact Q'.eqv_trans _ (1 * 1) _
    (Q'.eqv_trans _ (1 * ((1 : Q') + -(0 : Q'))) _
      (Q'.mul_eqv_congr_right _ 1 _
        (geometricSum_neg_zero_eqv_one degree))
      (Q'.mul_eqv_congr_left 1 _ 1 hfactor))
    (Q'.one_mul_eqv 1)

/-- With at least one Euler term, the constant coefficient of the reflected
Euler-versus-geometric difference vanishes semantically. -/
theorem eval_positiveArtanhEulerGeometricDifferencePoly_zero
    (stage n degree : Nat) :
    (eval (positiveArtanhEulerGeometricDifferencePoly
      stage (n + 1) degree) 0).eqv 0 := by
  have hexponent := positiveArtanhExponent_zero_eqv_zero stage
  have heuler :
      (ExpNeg.partialSum (positiveArtanhExponent 0 stage) (n + 1)).eqv 1 :=
    Q'.eqv_trans _ _ _
      (YMGap.Constructive.partialSum_eqv hexponent (n + 1))
      (expPartialSum_zero_succ_eqv n)
  have hgeometric := positiveArtanhGeometricApprox_zero_eqv_one degree
  have hdifference :
      (ExpNeg.partialSum (positiveArtanhExponent 0 stage) (n + 1) +
        -(positiveArtanhGeometricApprox 0 degree)).eqv 0 :=
    Q'.eqv_trans _ (1 + -1) _
      (q_add_congr heuler (Q'.neg_eqv_congr _ _ hgeometric))
      (Q'.add_neg_self_eqv 1)
  exact Q'.eqv_trans _ _ _
    (eval_positiveArtanhEulerGeometricDifferencePoly 0 stage (n + 1) degree)
    hdifference

/-- The explicit exponential term modulus is never zero: its denominator
summand is a positive natural. -/
theorem one_le_expNegTermAbsModulus (x epsilon : Q') :
    1 <= ExpNeg.termAbsModulus x epsilon := by
  unfold ExpNeg.termAbsModulus
  have hden : 1 <=
      (epsilon *
        Q'.invSucc
          (ExpNeg.termAbs x (RatNat.halfRatioCutoff x)).num.toNat).den := by
    exact (epsilon *
      Q'.invSucc
        (ExpNeg.termAbs x (RatNat.halfRatioCutoff x)).num.toNat).den_pos
  omega

/-- Consequently the explicit Euler Cauchy pivot always contains at least its
constant term. -/
theorem one_le_expNegMexp (x epsilon : Q') :
    1 <= ExpNeg.Mexp x epsilon := by
  unfold ExpNeg.Mexp
  exact Nat.le_trans
    (one_le_expNegTermAbsModulus x (HalfPow.half * epsilon))
    (Nat.le_max_right _ _)

theorem one_le_positiveArtanhEulerAnchorPivot (z epsilon : Q') :
    1 <= positiveArtanhEulerAnchorPivot z epsilon := by
  unfold positiveArtanhEulerAnchorPivot
  exact one_le_expNegMexp _ _

/-- Positive rational powers remain positive. -/
theorem qpow_pos (z : Q') (hz : (0 : Q') < z) :
    forall n : Nat, (0 : Q') < z ^ n
  | 0 => by
      rw [Q'.pow_zero]
      decide
  | n + 1 => Q'.mul_pos hz (qpow_pos z hz n)

theorem artanhTerm_pos (z : Q') (hz : (0 : Q') < z) (k : Nat) :
    (0 : Q') < CRealLog.term z k :=
  Q'.mul_pos (qpow_pos z hz (2 * k + 1)) (CRealLog.recipOdd_pos k)

theorem artanhPartialSum_succ_pos (z : Q') (hz : (0 : Q') < z) :
    forall stage : Nat,
      (0 : Q') < CRealLog.partialSum z (stage + 1)
  | 0 => by
      rw [CRealLog.partialSum_succ, CRealLog.partialSum_zero, Q'.zero_add']
      exact artanhTerm_pos z hz 0
  | stage + 1 => by
      rw [CRealLog.partialSum_succ]
      exact Q'.add_pos
        (artanhPartialSum_succ_pos z hz stage)
        (artanhTerm_pos z hz (stage + 1))

theorem one_le_positiveArtanhEulerAnchorStage (epsilon : Q') :
    1 <= positiveArtanhEulerAnchorStage epsilon := by
  unfold positiveArtanhEulerAnchorStage positiveArtanhExponentModulus
    CRealLog.Martanh
  have hden :=
    (Q'.mkPos 8 9 (by decide) *
      (HalfPow.half * positiveArtanhAnchorOuterTolerance epsilon)).den_pos
  omega

theorem positiveArtanhExponent_pos_of_one_le
    (z : Q') (hz : (0 : Q') < z) (stage : Nat)
    (hstage : 1 <= stage) :
    (0 : Q') < positiveArtanhExponent z stage := by
  cases stage with
  | zero => omega
  | succ stage =>
      unfold positiveArtanhExponent
      exact Q'.add_pos
        (artanhPartialSum_succ_pos z hz stage)
        (artanhPartialSum_succ_pos z hz stage)

theorem two_le_halfRatioCutoff_of_pos
    (x : Q') (hx : (0 : Q') < x) :
    2 <= RatNat.halfRatioCutoff x := by
  have hnum : 0 < x.num := Q'.num_pos_of_pos hx
  have hcast : (x.num.toNat : Int) = x.num :=
    Int.toNat_of_nonneg (Int.le_of_lt hnum)
  have hnat : 0 < x.num.toNat := by omega
  unfold RatNat.halfRatioCutoff
  omega

theorem two_le_expNegMexp_of_pos
    (x epsilon : Q') (hx : (0 : Q') < x) :
    2 <= ExpNeg.Mexp x epsilon := by
  unfold ExpNeg.Mexp
  exact Nat.le_trans (two_le_halfRatioCutoff_of_pos x hx)
    (Nat.le_max_left _ _)

theorem two_le_positiveArtanhEulerAnchorPivot
    (z : Q') (hz : (0 : Q') < z) (epsilon : Q') :
    2 <= positiveArtanhEulerAnchorPivot z epsilon := by
  unfold positiveArtanhEulerAnchorPivot
  exact two_le_expNegMexp_of_pos _ _
    (positiveArtanhExponent_pos_of_one_le z hz _
      (one_le_positiveArtanhEulerAnchorStage epsilon))

theorem one_le_positiveArtanhGeometricAnchorDegree (epsilon : Q') :
    1 <= positiveArtanhGeometricAnchorDegree epsilon := by
  unfold positiveArtanhGeometricAnchorDegree
  have hden := (positiveArtanhGeometricComparisonTolerance epsilon).den_pos
  omega

/-- The first coefficient cancels for every positive-length Euler truncation.
This is the first proved segment of the expected full formal prefix. -/
theorem zeroPrefix_one_positiveArtanhEulerGeometricDifferencePoly
    (stage inner degree : Nat) (hinner : 1 <= inner) :
    zeroPrefix 1
      (positiveArtanhEulerGeometricDifferencePoly stage inner degree) := by
  cases inner with
  | zero => omega
  | succ n =>
      exact zeroPrefix_one_of_eval_zero _
        (eval_positiveArtanhEulerGeometricDifferencePoly_zero stage n degree)

/-- Number of low coefficients expected to agree before any of the three
finite truncations can affect the formal identity. -/
def positiveArtanhEulerPolynomialCancellationCount
    (stage inner degree : Nat) : Nat :=
  min inner (min (2 * stage + 1) (degree + 1))

/-- Canonical stabilized Euler coefficient.  Exactly `index + 1` Euler terms
are sufficient to determine coefficient `index`; later terms have valuation
strictly above it. -/
def positiveArtanhEulerStableCoeff (stage index : Nat) : Q' :=
  coeff
    (expPartialPoly (positiveArtanhExponentPoly stage) (index + 1))
    index

/-- The canonical stabilized Euler coefficient starts at one, independently
of the artanh stage. -/
theorem positiveArtanhEulerStableCoeff_zero_eqv_one (stage : Nat) :
    (positiveArtanhEulerStableCoeff stage 0).eqv 1 := by
  unfold positiveArtanhEulerStableCoeff
  exact Q'.eqv_trans _ _ _
    (coeff_zero_eq_constantCoeff _)
    (constantCoeff_expPartialPoly_succ_eqv_one
      (positiveArtanhExponentPoly stage)
      (constantCoeff_positiveArtanhExponentPoly_eqv_zero stage) 0)

/-- At every positive artanh stage, the stabilized linear Euler coefficient
is the closed value `-2`. -/
theorem positiveArtanhEulerStableCoeff_one_eqv_negativeTwo
    (stage : Nat) :
    (positiveArtanhEulerStableCoeff (stage + 1) 1).eqv negativeTwo := by
  unfold positiveArtanhEulerStableCoeff
  exact Q'.eqv_trans _ _ _
    (coeff_one_eq_linearCoeff _)
    (linearCoeff_expPartialPoly_add_two_eqv_negativeTwo stage 0)

/-- Every finite Euler truncation containing coefficient `index` agrees with
the canonical stabilized coefficient.  This removes the moving inner Euler
pivot from the remaining formal coefficient identity. -/
theorem coeff_positiveArtanhExpPartialPoly_eq_stable_of_lt :
    forall (stage inner index : Nat), index < inner ->
      (coeff
        (expPartialPoly (positiveArtanhExponentPoly stage) inner)
        index).eqv
        (positiveArtanhEulerStableCoeff stage index)
  | stage, 0, index, hindex => by omega
  | stage, inner + 1, index, hindex => by
      by_cases hlt : index < inner
      · exact Q'.eqv_trans _ _ _
          (coeff_expPartialPoly_succ_stable
            (positiveArtanhExponentPoly stage)
            (zeroPrefix_one_positiveArtanhExponentPoly stage)
            inner index hlt)
          (coeff_positiveArtanhExpPartialPoly_eq_stable_of_lt
            stage inner index hlt)
      · have heq : index = inner := by omega
        subst index
        exact Q'.eqv_refl _

/-- Solve `x+y ≃ z` for `x` using only constructive rational ring laws. -/
theorem q_left_eqv_add_neg_of_add_eqv {x y z : Q'}
    (h : (x + y).eqv z) : x.eqv (z + -y) := by
  exact Q'.eqv_trans _ (x + 0) _
    (Q'.eqv_symm (q_add_zero_eqv x))
    (Q'.eqv_trans _ (x + (y + -y)) _
      (Q'.add_eqv_congr_left x 0 _
        (Q'.eqv_symm (Q'.add_neg_self_eqv y)))
      (Q'.eqv_trans _ ((x + y) + -y) _
        (Q'.eqv_symm (Q'.add_assoc_eqv x y (-y)))
        (Q'.add_eqv_congr_right _ z (-y) h)))

/-- Multiplication by the rational representative `-1` is negation. -/
theorem negOne_mul_eqv_neg (a : Q') : ((-1 : Q') * a).eqv (-a) :=
  Q'.eqv_trans _ (-(1 * a)) _
    (Q'.neg_mul_eqv 1 a)
    (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv a))

/-- Multiplication by natural two is duplication. -/
theorem ofNat_two_mul_eqv_add_self (a : Q') :
    (Q'.ofNat 2 * a).eqv (a + a) := by
  have htwo : (Q'.ofNat 2).eqv ((1 : Q') + 1) :=
    Q'.eqv_trans _ (Q'.ofNat 1 + Q'.ofNat 1) _
      (Q'.ofNat_add_eqv 1 1)
      (q_add_congr (by decide) (by decide))
  exact Q'.eqv_trans _ (((1 : Q') + 1) * a) _
    (Q'.mul_eqv_congr_right _ _ a htwo)
    (Q'.eqv_trans _ (1 * a + 1 * a) _
      (q_add_mul 1 1 a)
      (q_add_congr (Q'.one_mul_eqv a) (Q'.one_mul_eqv a)))

/-- The closed `-2` scalar is natural two acting on the negated input. -/
theorem negativeTwo_mul_eqv_ofNat_two_mul_neg (a : Q') :
    (negativeTwo * a).eqv (Q'.ofNat 2 * (-a)) :=
  Q'.eqv_trans _ ((-a) + (-a)) _
    (negativeTwo_mul_eqv_neg_add_neg a)
    (Q'.eqv_symm (ofNat_two_mul_eqv_add_self (-a)))

/-- Combine the `-2` term and a natural multiple of the negated coefficient
into one successor natural multiple. -/
theorem negativeTwo_add_ofNat_mul_neg (a : Q') (count : Nat) :
    (negativeTwo * a + Q'.ofNat count * (-a)).eqv
      (Q'.ofNat (count + 2) * (-a)) := by
  refine Q'.eqv_trans _
    (Q'.ofNat 2 * (-a) + Q'.ofNat count * (-a)) _
    (q_add_congr (negativeTwo_mul_eqv_ofNat_two_mul_neg a)
      (Q'.eqv_refl _)) ?_
  refine Q'.eqv_trans _
    ((Q'.ofNat 2 + Q'.ofNat count) * (-a)) _
    (Q'.eqv_symm (q_add_mul (Q'.ofNat 2) (Q'.ofNat count) (-a))) ?_
  have hscalar : (Q'.ofNat 2 + Q'.ofNat count).eqv
      (Q'.ofNat (count + 2)) :=
    Q'.eqv_trans _ (Q'.ofNat count + Q'.ofNat 2) _
      (Q'.add_comm_eqv _ _)
      (Q'.eqv_symm (Q'.ofNat_add_eqv count 2))
  exact Q'.mul_eqv_congr_right _ _ (-a) hscalar

/-- Local coefficient form of the finite differential equation.  All Euler
coefficients have already been moved to their canonical stabilized
representatives, and the explicit artanh boundary is absent below
`2*stage`. -/
theorem positiveArtanhEulerStableCoeff_differentialRecurrence
    (stage index : Nat) (hbound : index < 2 * stage) :
    (Q'.ofNat (index + 1) *
          positiveArtanhEulerStableCoeff stage (index + 1) +
        (if 2 <= index then
          -(Q'.ofNat (index - 1) *
            positiveArtanhEulerStableCoeff stage (index - 1))
        else 0)).eqv
      (negativeTwo * positiveArtanhEulerStableCoeff stage index) := by
  let exponent : Poly := positiveArtanhExponentPoly stage
  let nextPartial : Poly := expPartialPoly exponent (index + 2)
  let currentPartial : Poly := expPartialPoly exponent (index + 1)
  have hstableMain :
      (coeff nextPartial (index + 1)).eqv
        (positiveArtanhEulerStableCoeff stage (index + 1)) :=
    coeff_positiveArtanhExpPartialPoly_eq_stable_of_lt
      stage (index + 2) (index + 1) (by omega)
  have hderivMain :
      (coeff (pderiv nextPartial) index).eqv
        (Q'.ofNat (index + 1) *
          positiveArtanhEulerStableCoeff stage (index + 1)) :=
    Q'.eqv_trans _
      (Q'.ofNat (index + 1) * coeff nextPartial (index + 1)) _
      (coeff_pderiv nextPartial index)
      (Q'.mul_eqv_congr_left _ _ _ hstableMain)
  have hleft :
      (coeff (pmul oneSubSquarePoly (pderiv nextPartial)) index).eqv
        (Q'.ofNat (index + 1) *
            positiveArtanhEulerStableCoeff stage (index + 1) +
          (if 2 <= index then
            -(Q'.ofNat (index - 1) *
              positiveArtanhEulerStableCoeff stage (index - 1))
          else 0)) := by
    refine Q'.eqv_trans _
      (coeff (pderiv nextPartial) index +
        (if 2 <= index then
          -(coeff (pderiv nextPartial) (index - 2)) else 0)) _
      (coeff_oneSubSquarePoly_pmul (pderiv nextPartial) index) ?_
    by_cases htwo : 2 <= index
    · simp only [if_pos htwo]
      have hminus : index - 2 + 1 = index - 1 := by omega
      have hstableBack :
          (coeff nextPartial (index - 1)).eqv
            (positiveArtanhEulerStableCoeff stage (index - 1)) :=
        coeff_positiveArtanhExpPartialPoly_eq_stable_of_lt
          stage (index + 2) (index - 1) (by omega)
      have hderivBack := coeff_pderiv nextPartial (index - 2)
      rw [hminus] at hderivBack
      exact q_add_congr hderivMain
        (Q'.neg_eqv_congr _ _
          (Q'.eqv_trans _
            (Q'.ofNat (index - 1) *
              coeff nextPartial (index - 1)) _
            hderivBack
            (Q'.mul_eqv_congr_left _ _ _ hstableBack)))
    · simp only [if_neg htwo]
      exact q_add_congr hderivMain (Q'.eqv_refl 0)
  have hdifferential :=
    positiveArtanhExpPartialPoly_finiteDifferentialEquation
      stage (index + 1) index
  have hcurrent :
      (coeff currentPartial index).eqv
        (positiveArtanhEulerStableCoeff stage index) :=
    coeff_positiveArtanhExpPartialPoly_eq_stable_of_lt
      stage (index + 1) index (by omega)
  have hright :
      (coeff
        (pmul currentPartial
          (pneg
            (padd
              (padd (pconst 1) (pneg (ppow pvar (2 * stage))))
              (padd (pconst 1) (pneg (ppow pvar (2 * stage)))))))
        index).eqv
        (negativeTwo * positiveArtanhEulerStableCoeff stage index) :=
    Q'.eqv_trans _
      (negativeTwo * coeff currentPartial index) _
      (coeff_pmul_negativeDoubledArtanhBoundary_of_lt
        currentPartial stage index hbound)
      (Q'.mul_eqv_congr_left negativeTwo _ _ hcurrent)
  exact Q'.eqv_trans _
    (coeff (pmul oneSubSquarePoly (pderiv nextPartial)) index) _
    (Q'.eqv_symm hleft)
    (Q'.eqv_trans _
      (coeff
        (pmul currentPartial
          (pneg
            (padd
              (padd (pconst 1) (pneg (ppow pvar (2 * stage))))
              (padd (pconst 1) (pneg (ppow pvar (2 * stage)))))))
        index) _
      hdifferential hright)

/-- The closed comparison target starts at the same constant coefficient. -/
theorem positiveArtanhFormalTargetCoeff_zero_eqv_one :
    (positiveArtanhFormalTargetCoeff 0).eqv 1 :=
  Q'.eqv_refl 1

/-- The first positive comparison coefficient is `-2`. -/
theorem positiveArtanhFormalTargetCoeff_one_eqv_negativeTwo :
    (positiveArtanhFormalTargetCoeff 1).eqv negativeTwo := by
  decide

/-- After the exceptional constant-to-linear step, the closed target
coefficients alternate by multiplication with `-1`. -/
theorem positiveArtanhFormalTargetCoeff_succ_eqv_neg
    (index : Nat) (hindex : 1 <= index) :
    (positiveArtanhFormalTargetCoeff (index + 1)).eqv
      ((-1 : Q') * positiveArtanhFormalTargetCoeff index) := by
  cases index with
  | zero => omega
  | succ index =>
      change
        (((-1 : Q') ^ ((index + 1) + 1)) +
            ((-1 : Q') ^ ((index + 1) + 1))).eqv
          ((-1 : Q') *
            (((-1 : Q') ^ (index + 1)) +
              ((-1 : Q') ^ (index + 1))))
      rw [Q'.pow_succ]
      exact Q'.eqv_symm
        (Q'.mul_add_eqv (-1)
          ((-1 : Q') ^ (index + 1))
          ((-1 : Q') ^ (index + 1)))

/-- The stabilized Euler coefficients alternate after the exceptional
constant-to-linear step.  This discharges the former recurrence certificate
field directly from the finite differential equation. -/
theorem positiveArtanhEulerStableCoeff_succ_eqv_neg
    (stage : Nat) : forall index : Nat, 1 <= index ->
      index + 1 < 2 * stage + 1 ->
      (positiveArtanhEulerStableCoeff stage (index + 1)).eqv
        ((-1 : Q') * positiveArtanhEulerStableCoeff stage index) := by
  intro index
  induction index using Nat.strongRecOn with
  | ind index ih =>
      intro hone hwindow
      have hboundary : index < 2 * stage := by omega
      by_cases hbase : index = 1
      · subst index
        have htwoFalse : Not (2 <= 1) := by omega
        have hrec :
            (Q'.ofNat 2 * positiveArtanhEulerStableCoeff stage 2 + 0).eqv
              (negativeTwo * positiveArtanhEulerStableCoeff stage 1) := by
          simpa only [if_neg htwoFalse] using
            (positiveArtanhEulerStableCoeff_differentialRecurrence
              stage 1 hboundary)
        have hfactor :
            (Q'.ofNat 2 * positiveArtanhEulerStableCoeff stage 2).eqv
              (Q'.ofNat 2 *
                (-(positiveArtanhEulerStableCoeff stage 1))) :=
          Q'.eqv_trans _
            (Q'.ofNat 2 * positiveArtanhEulerStableCoeff stage 2 + 0) _
            (Q'.eqv_symm
              (q_add_zero_eqv
                (Q'.ofNat 2 * positiveArtanhEulerStableCoeff stage 2)))
            (Q'.eqv_trans _
              (negativeTwo * positiveArtanhEulerStableCoeff stage 1) _
              hrec
              (negativeTwo_mul_eqv_ofNat_two_mul_neg
                (positiveArtanhEulerStableCoeff stage 1)))
        have hcancel :
            (positiveArtanhEulerStableCoeff stage 2).eqv
              (-(positiveArtanhEulerStableCoeff stage 1)) :=
          Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos 1) hfactor
        exact Q'.eqv_trans _ _ _ hcancel
          (Q'.eqv_symm
            (negOne_mul_eqv_neg
              (positiveArtanhEulerStableCoeff stage 1)))
      · have htwo : 2 <= index := by omega
        have hprevious : 1 <= index - 1 := by omega
        have hpreviousWindow : index - 1 + 1 < 2 * stage + 1 := by omega
        have hinduction := ih (index - 1) (by omega)
          hprevious hpreviousWindow
        have hpreviousSucc : index - 1 + 1 = index := by omega
        rw [hpreviousSucc] at hinduction
        have hcurrentEqNegPrevious :
            (positiveArtanhEulerStableCoeff stage index).eqv
              (-(positiveArtanhEulerStableCoeff stage (index - 1))) :=
          Q'.eqv_trans _ _ _ hinduction
            (negOne_mul_eqv_neg
              (positiveArtanhEulerStableCoeff stage (index - 1)))
        have hpreviousEqNegCurrent :
            (positiveArtanhEulerStableCoeff stage (index - 1)).eqv
              (-(positiveArtanhEulerStableCoeff stage index)) :=
          Q'.eqv_symm
            (Q'.eqv_trans _
              (-(-(positiveArtanhEulerStableCoeff stage (index - 1)))) _
              (Q'.neg_eqv_congr _ _ hcurrentEqNegPrevious)
              (Q'.neg_neg_eqv
                (positiveArtanhEulerStableCoeff stage (index - 1))))
        have hrec :
            (Q'.ofNat (index + 1) *
                  positiveArtanhEulerStableCoeff stage (index + 1) +
                -(Q'.ofNat (index - 1) *
                  positiveArtanhEulerStableCoeff stage (index - 1))).eqv
              (negativeTwo * positiveArtanhEulerStableCoeff stage index) := by
          simpa only [if_pos htwo] using
            (positiveArtanhEulerStableCoeff_differentialRecurrence
              stage index hboundary)
        have hsolved := q_left_eqv_add_neg_of_add_eqv hrec
        have hrest :
            (negativeTwo * positiveArtanhEulerStableCoeff stage index +
                -(-(Q'.ofNat (index - 1) *
                  positiveArtanhEulerStableCoeff stage (index - 1)))).eqv
              (negativeTwo * positiveArtanhEulerStableCoeff stage index +
                Q'.ofNat (index - 1) *
                  (-(positiveArtanhEulerStableCoeff stage index))) := by
          exact Q'.add_eqv_congr_left _ _ _
            (Q'.eqv_trans _
              (Q'.ofNat (index - 1) *
                positiveArtanhEulerStableCoeff stage (index - 1)) _
              (Q'.neg_neg_eqv _)
              (Q'.mul_eqv_congr_left _ _ _ hpreviousEqNegCurrent))
        have hcombine := negativeTwo_add_ofNat_mul_neg
          (positiveArtanhEulerStableCoeff stage index) (index - 1)
        have hcount : index - 1 + 2 = index + 1 := by omega
        rw [hcount] at hcombine
        have hfactor :
            (Q'.ofNat (index + 1) *
                positiveArtanhEulerStableCoeff stage (index + 1)).eqv
              (Q'.ofNat (index + 1) *
                (-(positiveArtanhEulerStableCoeff stage index))) :=
          Q'.eqv_trans _ _ _ hsolved
            (Q'.eqv_trans _ _ _ hrest hcombine)
        have hcancel :
            (positiveArtanhEulerStableCoeff stage (index + 1)).eqv
              (-(positiveArtanhEulerStableCoeff stage index)) :=
          Q'.mul_left_cancel_of_pos (Q'.ofNat_succ_pos index) hfactor
        exact Q'.eqv_trans _ _ _ hcancel
          (Q'.eqv_symm
            (negOne_mul_eqv_neg
              (positiveArtanhEulerStableCoeff stage index)))

/-- Every stabilized Euler coefficient strictly below the artanh truncation
boundary is the closed two-copy alternating target. -/
theorem positiveArtanhEulerStableCoeff_eq_target_of_lt
    (stage index : Nat) (hindex : index < 2 * stage + 1) :
    (positiveArtanhEulerStableCoeff stage index).eqv
      (positiveArtanhFormalTargetCoeff index) := by
  induction index generalizing stage with
  | zero =>
      exact Q'.eqv_trans _ 1 _
        (positiveArtanhEulerStableCoeff_zero_eqv_one stage)
        (Q'.eqv_symm positiveArtanhFormalTargetCoeff_zero_eqv_one)
  | succ index ih =>
      cases index with
      | zero =>
          cases stage with
          | zero => omega
          | succ stage =>
              exact Q'.eqv_trans _ negativeTwo _
                (positiveArtanhEulerStableCoeff_one_eqv_negativeTwo stage)
                (Q'.eqv_symm
                  positiveArtanhFormalTargetCoeff_one_eqv_negativeTwo)
      | succ index =>
          have hprevious : index + 1 < 2 * stage + 1 := by omega
          exact Q'.eqv_trans _
            ((-1 : Q') *
              positiveArtanhEulerStableCoeff stage (index + 1)) _
            (positiveArtanhEulerStableCoeff_succ_eqv_neg
              stage (index + 1) (by omega) hindex)
            (Q'.eqv_trans _
              ((-1 : Q') *
                positiveArtanhFormalTargetCoeff (index + 1)) _
              (Q'.mul_eqv_congr_left (-1) _ _
                (ih stage hprevious))
              (Q'.eqv_symm
                (positiveArtanhFormalTargetCoeff_succ_eqv_neg
                  (index + 1) (by omega))))

/-- The fully computed anchor difference polynomial. -/
def positiveArtanhEulerAnchorDifferencePoly
    (z epsilon : Q') : Poly :=
  positiveArtanhEulerGeometricDifferencePoly
    (positiveArtanhEulerAnchorStage epsilon)
    (positiveArtanhEulerAnchorPivot z epsilon)
    (positiveArtanhGeometricAnchorDegree epsilon)

/-- The fully computed anchor therefore has one exact zero coefficient with
no certificate input. -/
theorem zeroPrefix_one_positiveArtanhEulerAnchorDifferencePoly
    (z epsilon : Q') :
    zeroPrefix 1 (positiveArtanhEulerAnchorDifferencePoly z epsilon) := by
  unfold positiveArtanhEulerAnchorDifferencePoly
  exact zeroPrefix_one_positiveArtanhEulerGeometricDifferencePoly _ _ _
    (one_le_positiveArtanhEulerAnchorPivot z epsilon)

/-- At every positive input, the fully computed anchor cancels both its
constant and linear coefficients. -/
theorem zeroPrefix_two_positiveArtanhEulerAnchorDifferencePoly
    (z : Q') (hz : (0 : Q') < z) (epsilon : Q') :
    zeroPrefix 2 (positiveArtanhEulerAnchorDifferencePoly z epsilon) := by
  unfold positiveArtanhEulerAnchorDifferencePoly
  exact zeroPrefix_two_positiveArtanhEulerGeometricDifferencePoly _ _ _
    (one_le_positiveArtanhEulerAnchorStage epsilon)
    (two_le_positiveArtanhEulerAnchorPivot z hz epsilon)
    (one_le_positiveArtanhGeometricAnchorDegree epsilon)

/-- The fully computed cancellation-prefix length. -/
def positiveArtanhEulerAnchorCancellationCount
    (z epsilon : Q') : Nat :=
  positiveArtanhEulerPolynomialCancellationCount
    (positiveArtanhEulerAnchorStage epsilon)
    (positiveArtanhEulerAnchorPivot z epsilon)
    (positiveArtanhGeometricAnchorDegree epsilon)

/-! ## The computed cancellation count pays the geometric radius factor -/

/-- The stored denominator of a rational product is the product of the
stored positive denominators.  `Q'.mul_den_cast` already proves the integer
version; this is the natural-number form needed by the explicit cutoffs. -/
theorem qmul_den_eq_nat (a b : Q') :
    (a * b).den = a.den * b.den := by
  exact_mod_cast Q'.mul_den_cast a b

/-- The reserved geometric comparison tolerance is exactly
`epsilon / 16` at the level of stored denominators. -/
theorem positiveArtanhGeometricComparisonTolerance_den (epsilon : Q') :
    (positiveArtanhGeometricComparisonTolerance epsilon).den =
      16 * epsilon.den := by
  unfold positiveArtanhGeometricComparisonTolerance
    positiveArtanhAnchorInnerTolerance HalfPow.half
  repeat rw [qmul_den_eq_nat]
  repeat rw [Q'.mkPos_den]
  omega

/-- The explicit outer Euler stage is much larger than the geometric
tolerance denominator: its exact value is `432 * epsilon.den`. -/
theorem positiveArtanhEulerAnchorStage_eq (epsilon : Q') :
    positiveArtanhEulerAnchorStage epsilon = 432 * epsilon.den := by
  unfold positiveArtanhEulerAnchorStage positiveArtanhExponentModulus
    CRealLog.Martanh positiveArtanhAnchorOuterTolerance HalfPow.half
  repeat rw [qmul_den_eq_nat]
  repeat rw [Q'.mkPos_den]
  omega

/-- Multiplying by a positive-denominator rational cannot decrease the
stored denominator. -/
theorem den_le_mul_den (a b : Q') :
    a.den <= (a * b).den := by
  rw [qmul_den_eq_nat]
  have hb : 1 <= b.den := by
    have := b.den_pos
    omega
  simpa using Nat.mul_le_mul_left a.den hb

/-- The exponential pivot exceeds the comparison-tolerance denominator by
two.  One part comes from the positive exponent's ratio cutoff, and the
other from the explicit term-modulus denominator. -/
theorem positiveArtanhEulerAnchorPivot_ge_comparisonDen_add_two
    (z : Q') (hz : (0 : Q') < z) (epsilon : Q') :
    (positiveArtanhGeometricComparisonTolerance epsilon).den + 2 <=
      positiveArtanhEulerAnchorPivot z epsilon := by
  let x : Q' := positiveArtanhExponent z
    (positiveArtanhEulerAnchorStage epsilon)
  let tolerance : Q' := positiveArtanhGeometricComparisonTolerance epsilon
  have hx : (0 : Q') < x :=
    positiveArtanhExponent_pos_of_one_le z hz _
      (one_le_positiveArtanhEulerAnchorStage epsilon)
  have hcut : 2 <= RatNat.halfRatioCutoff x :=
    two_le_halfRatioCutoff_of_pos x hx
  have hden : tolerance.den <=
      (tolerance * Q'.invSucc
        (ExpNeg.termAbs x (RatNat.halfRatioCutoff x)).num.toNat).den :=
    den_le_mul_den _ _
  change tolerance.den + 2 <= ExpNeg.Mexp x
    (positiveArtanhAnchorInnerTolerance epsilon)
  unfold ExpNeg.Mexp
  refine Nat.le_trans ?_ (Nat.le_max_right _ _)
  change tolerance.den + 2 <= RatNat.halfRatioCutoff x +
    (tolerance * Q'.invSucc
      (ExpNeg.termAbs x (RatNat.halfRatioCutoff x)).num.toNat).den
  omega

/-- All three finite truncations lie beyond one successor of the comparison
tolerance denominator.  This is the exact common cutoff needed to extract
one additional factor `1/2`. -/
theorem positiveArtanhEulerAnchorCancellationCount_ge_comparisonDen_succ
    (z : Q') (hz : (0 : Q') < z) (epsilon : Q') :
    (positiveArtanhGeometricComparisonTolerance epsilon).den + 1 <=
      positiveArtanhEulerAnchorCancellationCount z epsilon := by
  let tolerance : Q' := positiveArtanhGeometricComparisonTolerance epsilon
  have hpivot : tolerance.den + 1 <=
      positiveArtanhEulerAnchorPivot z epsilon := by
    have hpivotBase :=
      positiveArtanhEulerAnchorPivot_ge_comparisonDen_add_two z hz epsilon
    change tolerance.den + 2 <=
      positiveArtanhEulerAnchorPivot z epsilon at hpivotBase
    omega
  have hstage : tolerance.den + 1 <=
      2 * positiveArtanhEulerAnchorStage epsilon + 1 := by
    rw [positiveArtanhGeometricComparisonTolerance_den,
      positiveArtanhEulerAnchorStage_eq]
    omega
  have hdegree : tolerance.den + 1 <=
      positiveArtanhGeometricAnchorDegree epsilon + 1 := by
    unfold positiveArtanhGeometricAnchorDegree
    exact Nat.le_refl _
  unfold positiveArtanhEulerAnchorCancellationCount
    positiveArtanhEulerPolynomialCancellationCount
  exact Nat.le_min.mpr ⟨hpivot, Nat.le_min.mpr ⟨hstage, hdegree⟩⟩

/-- The geometric truncation is always the first of the three computed
cutoffs.  Thus the common cancellation count is exactly one past the
geometric degree; neither the input-dependent Euler pivot nor the outer
artanh stage controls the residual interface. -/
theorem positiveArtanhEulerAnchorCancellationCount_eq_geometricDegree_succ
    (z : Q') (hz : (0 : Q') < z) (epsilon : Q') :
    positiveArtanhEulerAnchorCancellationCount z epsilon =
      positiveArtanhGeometricAnchorDegree epsilon + 1 := by
  apply Nat.le_antisymm
  · unfold positiveArtanhEulerAnchorCancellationCount
      positiveArtanhEulerPolynomialCancellationCount
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
  · have hcount :=
      positiveArtanhEulerAnchorCancellationCount_ge_comparisonDen_succ
        z hz epsilon
    unfold positiveArtanhGeometricAnchorDegree
    exact hcount

/-- One extra dyadic power pays a factor of two exactly. -/
theorem half_pow_succ_mul_two_eqv (n : Nat) :
    ((HalfPow.half ^ (n + 1)) * Q'.ofNat 2).eqv
      (HalfPow.half ^ n) := by
  show ((HalfPow.half * HalfPow.half ^ n) * Q'.ofNat 2).eqv
    (HalfPow.half ^ n)
  refine Q'.eqv_trans _
    (HalfPow.half * ((HalfPow.half ^ n) * Q'.ofNat 2)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (HalfPow.half * (Q'.ofNat 2 * (HalfPow.half ^ n))) _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv (HalfPow.half ^ n) (Q'.ofNat 2))) ?_
  refine Q'.eqv_trans _
    ((HalfPow.half * Q'.ofNat 2) * (HalfPow.half ^ n)) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ ((1 : Q') * (HalfPow.half ^ n)) _
    (Q'.mul_eqv_congr_right _ _ _ (by decide)) ?_
  exact Q'.one_mul_eqv _

/-- On the direct artanh window, the computed cancellation radius alone
pays the full comparison tolerance against any residual tail of weighted
size at most two. -/
theorem positiveArtanhEulerAnchorRadiusPow_mul_two_le_comparisonTolerance
    (z : Q') (hz : (0 : Q') < z)
    (hzb : Q'.abs z <= CRealLog.recipOdd 1)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (Q'.abs z) ^ (positiveArtanhEulerAnchorCancellationCount z epsilon) *
        Q'.ofNat 2 <= positiveArtanhGeometricComparisonTolerance epsilon := by
  let tolerance : Q' := positiveArtanhGeometricComparisonTolerance epsilon
  let count : Nat := positiveArtanhEulerAnchorCancellationCount z epsilon
  have htolerance : (0 : Q') < tolerance :=
    positiveArtanhGeometricComparisonTolerance_pos epsilon hepsilon
  have hcount :=
    positiveArtanhEulerAnchorCancellationCount_ge_comparisonDen_succ
      z hz epsilon
  change tolerance.den + 1 <= count at hcount
  obtain ⟨extra, hcountEq⟩ := Nat.exists_eq_add_of_le hcount
  have hradius : Q'.abs z <= HalfPow.half :=
    Q'.le_trans' _ _ _ hzb (by decide)
  have hbase : (Q'.abs z) ^ count <= HalfPow.half ^ count :=
    CRealLog.pow_le_pow_base _ _ (Q'.abs_nonneg z) hradius count
  have hanti : HalfPow.half ^ count <=
      HalfPow.half ^ (tolerance.den + 1) := by
    rw [hcountEq]
    exact ExpNeg.pow_half_antitone (tolerance.den + 1) extra
  have hpower : (Q'.abs z) ^ count <=
      HalfPow.half ^ (tolerance.den + 1) :=
    Q'.le_trans' _ _ _ hbase hanti
  have htwice : (Q'.abs z) ^ count * Q'.ofNat 2 <=
      HalfPow.half ^ (tolerance.den + 1) * Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpower (by decide)
  exact Q'.le_trans' _ _ _ htwice
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (half_pow_succ_mul_two_eqv tolerance.den))
      (HalfPow.pow_half_le tolerance htolerance))

/-! ## The first active geometric-boundary coefficient -/

/-- At its first coefficient outside the formal comparison window, the
finite geometric polynomial carries one copy of the alternating sign rather
than the two copies in the infinite target. -/
theorem coeff_positiveArtanhGeometricApproxPoly_boundary (degree : Nat) :
    (coeff (positiveArtanhGeometricApproxPoly degree) (degree + 1)).eqv
      ((-1 : Q') ^ (degree + 1)) := by
  unfold positiveArtanhGeometricApproxPoly
    positiveArtanhNumeratorPoly pconst pneg pvar
  change (coeff
    (pmul (geometricSumPoly degree)
      [(1 : Q') + (-1 : Q') * 0, (-1 : Q') * 1])
    (degree + 1)).eqv ((-1 : Q') ^ (degree + 1))
  refine Q'.eqv_trans _
    (coeff (geometricSumPoly degree) (degree + 1) *
        ((1 : Q') + (-1 : Q') * 0) +
      coeff (geometricSumPoly degree) degree * ((-1 : Q') * 1)) _
    (coeff_pmul_pair_succ _ _ _ degree) ?_
  have hnext := coeff_geometricSumPoly degree (degree + 1)
  rw [if_neg (by omega : ¬ degree + 1 <= degree)] at hnext
  have hprev := coeff_geometricSumPoly degree degree
  rw [if_pos (by omega : degree <= degree)] at hprev
  have hb0 : ((1 : Q') + (-1 : Q') * 0).eqv 1 :=
    Q'.eqv_trans _ (1 + 0) _
      (Q'.add_eqv_congr_left 1 _ 0 (q_mul_zero (-1)))
      (q_add_zero_eqv 1)
  have hb1 : ((-1 : Q') * 1).eqv (-1 : Q') :=
    Q'.mul_one_eqv (-1)
  refine Q'.eqv_trans _
    ((0 : Q') * 1 + ((-1 : Q') ^ degree) * (-1 : Q')) _
    (q_add_congr (q_mul_congr hnext hb0) (q_mul_congr hprev hb1)) ?_
  refine Q'.eqv_trans _ (((-1 : Q') ^ degree) * (-1 : Q')) _
    (Q'.eqv_trans _ (0 + (((-1 : Q') ^ degree) * (-1 : Q'))) _
      (q_add_congr (q_zero_mul 1) (Q'.eqv_refl _))
      (q_zero_add_eqv _)) ?_
  exact Q'.mul_comm_eqv ((-1 : Q') ^ degree) (-1)

/-- The first geometric-boundary index remains strictly inside the much
later outer artanh truncation. -/
theorem positiveArtanhGeometricAnchorDegree_succ_lt_stageBoundary
    (epsilon : Q') :
    positiveArtanhGeometricAnchorDegree epsilon + 1 <
      2 * positiveArtanhEulerAnchorStage epsilon + 1 := by
  unfold positiveArtanhGeometricAnchorDegree
  rw [positiveArtanhGeometricComparisonTolerance_den,
    positiveArtanhEulerAnchorStage_eq]
  have hden := epsilon.den_pos
  omega

/-- The first geometric-boundary index also remains strictly inside the
input-dependent Euler pivot. -/
theorem positiveArtanhGeometricAnchorDegree_succ_lt_pivot
    (z : Q') (hz : (0 : Q') < z) (epsilon : Q') :
    positiveArtanhGeometricAnchorDegree epsilon + 1 <
      positiveArtanhEulerAnchorPivot z epsilon := by
  have hpivot :=
    positiveArtanhEulerAnchorPivot_ge_comparisonDen_add_two z hz epsilon
  unfold positiveArtanhGeometricAnchorDegree
  omega

/-- The Euler polynomial still has its stabilized infinite-target
coefficient at the first geometric boundary. -/
theorem coeff_positiveArtanhEulerAnchorExpPoly_boundary_eq_target
    (z : Q') (hz : (0 : Q') < z) (epsilon : Q') :
    let stage := positiveArtanhEulerAnchorStage epsilon
    let inner := positiveArtanhEulerAnchorPivot z epsilon
    let degree := positiveArtanhGeometricAnchorDegree epsilon
    (coeff
      (expPartialPoly (positiveArtanhExponentPoly stage) inner)
      (degree + 1)).eqv
        (positiveArtanhFormalTargetCoeff (degree + 1)) := by
  let stage := positiveArtanhEulerAnchorStage epsilon
  let inner := positiveArtanhEulerAnchorPivot z epsilon
  let degree := positiveArtanhGeometricAnchorDegree epsilon
  have hinner : degree + 1 < inner :=
    positiveArtanhGeometricAnchorDegree_succ_lt_pivot z hz epsilon
  have hstage : degree + 1 < 2 * stage + 1 :=
    positiveArtanhGeometricAnchorDegree_succ_lt_stageBoundary epsilon
  exact Q'.eqv_trans _ _ _
    (coeff_positiveArtanhExpPartialPoly_eq_stable_of_lt
      stage inner (degree + 1) hinner)
    (positiveArtanhEulerStableCoeff_eq_target_of_lt
      stage (degree + 1) hstage)

/-- Subtracting the one-copy geometric boundary from the two-copy Euler
target leaves exactly one alternating-sign coefficient. -/
theorem coeff_positiveArtanhEulerAnchorDifferencePoly_boundary
    (z : Q') (hz : (0 : Q') < z) (epsilon : Q') :
    let degree := positiveArtanhGeometricAnchorDegree epsilon
    (coeff (positiveArtanhEulerAnchorDifferencePoly z epsilon)
      (degree + 1)).eqv ((-1 : Q') ^ (degree + 1)) := by
  let stage := positiveArtanhEulerAnchorStage epsilon
  let inner := positiveArtanhEulerAnchorPivot z epsilon
  let degree := positiveArtanhGeometricAnchorDegree epsilon
  let sign : Q' := (-1 : Q') ^ (degree + 1)
  have heuler :=
    coeff_positiveArtanhEulerAnchorExpPoly_boundary_eq_target z hz epsilon
  change (coeff
    (expPartialPoly (positiveArtanhExponentPoly stage) inner)
    (degree + 1)).eqv
      (positiveArtanhFormalTargetCoeff (degree + 1)) at heuler
  have heuler' :
      (coeff (expPartialPoly (positiveArtanhExponentPoly stage) inner)
        (degree + 1)).eqv (sign + sign) := by
    exact Q'.eqv_trans _ _ _ heuler (Q'.eqv_refl _)
  have hgeom :
      (coeff (positiveArtanhGeometricApproxPoly degree) (degree + 1)).eqv
        sign :=
    coeff_positiveArtanhGeometricApproxPoly_boundary degree
  unfold positiveArtanhEulerAnchorDifferencePoly
    positiveArtanhEulerGeometricDifferencePoly
  refine Q'.eqv_trans _
    (coeff (expPartialPoly (positiveArtanhExponentPoly stage) inner)
        (degree + 1) +
      (-1 : Q') *
        coeff (positiveArtanhGeometricApproxPoly degree) (degree + 1)) _
    (coeff_psub _ _ _) ?_
  have hneg :
      ((-1 : Q') *
          coeff (positiveArtanhGeometricApproxPoly degree) (degree + 1)).eqv
        (-sign) :=
    Q'.eqv_trans _ ((-1 : Q') * sign) _
      (Q'.mul_eqv_congr_left (-1) _ _ hgeom)
      (negOne_mul_eqv_neg sign)
  refine Q'.eqv_trans _ ((sign + sign) + (-sign)) _
    (q_add_congr heuler' hneg) ?_
  refine Q'.eqv_trans _ (sign + (sign + (-sign))) _
    (Q'.add_assoc_eqv sign sign (-sign)) ?_
  refine Q'.eqv_trans _ (sign + 0) _
    (Q'.add_eqv_congr_left sign _ 0 (Q'.add_neg_self_eqv sign)) ?_
  exact q_add_zero_eqv sign

/-- Every rational power of `-1` has absolute value one. -/
theorem abs_negOne_pow_eqv_one : forall n : Nat,
    (Q'.abs ((-1 : Q') ^ n)).eqv 1
  | 0 => by decide
  | n + 1 => by
      refine Q'.eqv_trans _ (Q'.abs (-(((-1 : Q') ^ n)))) _
        (Q'.abs_eqv_congr (negOne_mul_eqv_neg (((-1 : Q') ^ n)))) ?_
      exact Q'.eqv_trans _ _ _ (Q'.abs_neg' (((-1 : Q') ^ n)))
        (abs_negOne_pow_eqv_one n)

/-- The first uncancelled coefficient of the full computed difference has
absolute value exactly one. -/
theorem abs_coeff_positiveArtanhEulerAnchorDifferencePoly_boundary_eqv_one
    (z : Q') (hz : (0 : Q') < z) (epsilon : Q') :
    let degree := positiveArtanhGeometricAnchorDegree epsilon
    (Q'.abs (coeff (positiveArtanhEulerAnchorDifferencePoly z epsilon)
      (degree + 1))).eqv 1 := by
  let degree := positiveArtanhGeometricAnchorDegree epsilon
  exact Q'.eqv_trans _ _ _
    (Q'.abs_eqv_congr
      (coeff_positiveArtanhEulerAnchorDifferencePoly_boundary z hz epsilon))
    (abs_negOne_pow_eqv_one (degree + 1))

/-- Splitting a dropped weighted coefficient list exposes its boundary
coefficient and the next shifted tail, including implicit zero padding. -/
theorem weightedL1_drop_eqv_boundary_add_tail
    (rho : Q') : forall (p : Poly) (index : Nat),
    (weightedL1 rho (List.drop index p)).eqv
      (Q'.abs (coeff p index) +
        rho * weightedL1 rho (List.drop (index + 1) p))
  | [], 0 => by
      change (0 : Q').eqv (Q'.abs 0 + rho * 0)
      refine Q'.eqv_symm (Q'.eqv_trans _ ((0 : Q') + 0) _
        (q_add_congr (by decide) (q_mul_zero rho)) ?_)
      exact q_add_zero_eqv 0
  | [], index + 1 => by
      change (0 : Q').eqv (Q'.abs 0 + rho * 0)
      refine Q'.eqv_symm (Q'.eqv_trans _ ((0 : Q') + 0) _
        (q_add_congr (by decide) (q_mul_zero rho)) ?_)
      exact q_add_zero_eqv 0
  | _ :: _, 0 => Q'.eqv_refl _
  | _ :: cs, index + 1 =>
      weightedL1_drop_eqv_boundary_add_tail rho cs index

/-- After spending one unit on the exact first boundary coefficient, a
shifted post-boundary tail of size at most three fits the former residual
size-two budget because `|z| <= 1/3`. -/
theorem positiveArtanhEulerResidualTailSize_two_of_postBoundary_three
    (z : Q') (hz : (0 : Q') < z)
    (hzb : Q'.abs z <= CRealLog.recipOdd 1)
    (epsilon : Q')
    (htail :
      let degree := positiveArtanhGeometricAnchorDegree epsilon
      let polynomial := positiveArtanhEulerAnchorDifferencePoly z epsilon
      weightedL1 (Q'.abs z) (List.drop (degree + 2) polynomial) <=
        Q'.ofNat 3) :
    let degree := positiveArtanhGeometricAnchorDegree epsilon
    let polynomial := positiveArtanhEulerAnchorDifferencePoly z epsilon
    weightedL1 (Q'.abs z) (List.drop (degree + 1) polynomial) <=
      Q'.ofNat 2 := by
  let degree := positiveArtanhGeometricAnchorDegree epsilon
  let polynomial := positiveArtanhEulerAnchorDifferencePoly z epsilon
  let rho := Q'.abs z
  have hrho : (0 : Q') <= rho := Q'.abs_nonneg z
  have hscaleTail :
      rho * weightedL1 rho (List.drop (degree + 2) polynomial) <=
        rho * Q'.ofNat 3 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ htail hrho
  have hscaleRadius : rho * Q'.ofNat 3 <=
      CRealLog.recipOdd 1 * Q'.ofNat 3 :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hzb (by decide)
  have htailOne :
      rho * weightedL1 rho (List.drop (degree + 2) polynomial) <= 1 :=
    Q'.le_trans' _ _ _ hscaleTail
      (Q'.le_trans' _ _ _ hscaleRadius (Q'.le_of_eqv (by decide)))
  have hboundary : (Q'.abs (coeff polynomial (degree + 1))).eqv 1 :=
    abs_coeff_positiveArtanhEulerAnchorDifferencePoly_boundary_eqv_one
      z hz epsilon
  have hsplit := weightedL1_drop_eqv_boundary_add_tail
    rho polynomial (degree + 1)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit)
    (Q'.le_trans' _ _ _
      (Q'.add_le_add (Q'.le_of_eqv hboundary) htailOne)
      (Q'.le_of_eqv (by decide)))

/-- The executable coefficient inequality at one rational input and
tolerance. -/
def positiveArtanhEulerPolynomialCoefficientBound
    (z epsilon : Q') : Prop :=
  weightedL1 (Q'.abs z)
      (positiveArtanhEulerAnchorDifferencePoly z epsilon) <=
    positiveArtanhGeometricComparisonTolerance epsilon

instance coefficientBoundDecidable (z epsilon : Q') :
    Decidable (positiveArtanhEulerPolynomialCoefficientBound z epsilon) :=
  inferInstanceAs (Decidable
    (weightedL1 (Q'.abs z)
        (positiveArtanhEulerGeometricDifferencePoly
          (positiveArtanhEulerAnchorStage epsilon)
          (positiveArtanhEulerAnchorPivot z epsilon)
          (positiveArtanhGeometricAnchorDegree epsilon)) <=
      positiveArtanhGeometricComparisonTolerance epsilon))

/-- Boolean form of the coefficient inequality. -/
def positiveArtanhEulerPolynomialCoefficientCheck
    (z epsilon : Q') : Bool :=
  decide (positiveArtanhEulerPolynomialCoefficientBound z epsilon)

/-- A total diagnostic result: every finite coefficient check either returns
its proof or a proof that the proposed bound fails. -/
inductive PositiveArtanhEulerPolynomialCoefficientAudit
    (z epsilon : Q') : Type where
  | pass : positiveArtanhEulerPolynomialCoefficientBound z epsilon ->
      PositiveArtanhEulerPolynomialCoefficientAudit z epsilon
  | fail : (positiveArtanhEulerPolynomialCoefficientBound z epsilon -> False) ->
      PositiveArtanhEulerPolynomialCoefficientAudit z epsilon

/-- Execute the finite coefficient audit. -/
def auditPositiveArtanhEulerPolynomialCoefficientBound
    (z epsilon : Q') :
    PositiveArtanhEulerPolynomialCoefficientAudit z epsilon :=
  if h : positiveArtanhEulerPolynomialCoefficientBound z epsilon then
    .pass h
  else
    .fail h

/-- A coefficient-only certificate for the remaining finite scalar anchor.
The polynomial has no evaluation variable.  The actual radius `|z|` is used,
rather than the whole `1/3` window, so the coefficient norm remains matched to
the input-dependent Euler pivot. -/
structure PositiveWindowArtanhEulerPolynomialCoefficientCertificate
    (z : Q') (_hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  coefficientBound : forall epsilon : Q', (0 : Q') < epsilon ->
    positiveArtanhEulerPolynomialCoefficientBound z epsilon

/-- Uniform producer of coefficient-only anchor certificates. -/
structure PositiveWindowArtanhEulerPolynomialCoefficientCompiler : Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerPolynomialCoefficientCertificate z hz hzb

/-- Prefix/tail presentation of the coefficient bound.  The prefix is an
executable exact-zero check; the tail is multiplied by the corresponding
power of the actual input radius. -/
structure PositiveWindowArtanhEulerPolynomialPrefixTailCertificate
    (z : Q') (_hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  prefixZero : forall epsilon : Q', (0 : Q') < epsilon ->
    zeroPrefix (positiveArtanhEulerAnchorCancellationCount z epsilon)
      (positiveArtanhEulerAnchorDifferencePoly z epsilon)
  tailBound : forall epsilon : Q', (0 : Q') < epsilon ->
    let count := positiveArtanhEulerAnchorCancellationCount z epsilon
    let polynomial := positiveArtanhEulerAnchorDifferencePoly z epsilon
    (Q'.abs z) ^ count *
        weightedL1 (Q'.abs z) (List.drop count polynomial) <=
      positiveArtanhGeometricComparisonTolerance epsilon

/-- Uniform producer of prefix/tail coefficient certificates. -/
structure PositiveWindowArtanhEulerPolynomialPrefixTailCompiler : Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerPolynomialPrefixTailCertificate z hz hzb

/-- Reduced algebraic frontier after Euler-truncation stability has been
proved internally.  The remaining identity compares one canonical stabilized
Euler coefficient with the finite geometric coefficient, only below the
artanh and geometric truncation orders. -/
structure PositiveArtanhEulerPolynomialStableCoefficientCertificate : Type 1 where
  coefficientAgreement :
    forall (stage degree index : Nat),
      index < 2 * stage + 1 -> index < degree + 1 ->
      (positiveArtanhEulerStableCoeff stage index).eqv
        (coeff (positiveArtanhGeometricApproxPoly degree) index)

/-- Further-reduced algebraic frontier after the finite geometric coefficient
has been computed internally.  Only the artanh stage and coefficient index
remain. -/
structure PositiveArtanhEulerPolynomialTargetCoefficientCertificate : Type 1 where
  coefficientTarget :
    forall (stage index : Nat), index < 2 * stage + 1 ->
      (positiveArtanhEulerStableCoeff stage index).eqv
        (positiveArtanhFormalTargetCoeff index)

/-- Strictly smaller algebraic frontier: the constant and linear seeds are
proved internally, so only the local alternating successor recurrence remains
for the stabilized Euler coefficients. -/
structure PositiveArtanhEulerPolynomialStableRecurrenceCertificate : Type 1 where
  coefficientSucc :
    forall (stage index : Nat), 1 <= index ->
      index + 1 < 2 * stage + 1 ->
      (positiveArtanhEulerStableCoeff stage (index + 1)).eqv
        ((-1 : Q') * positiveArtanhEulerStableCoeff stage index)

/-- Canonical internally proved inhabitant of the stabilized recurrence
certificate. -/
def canonicalPositiveArtanhEulerPolynomialStableRecurrenceCertificate :
    PositiveArtanhEulerPolynomialStableRecurrenceCertificate where
  coefficientSucc := positiveArtanhEulerStableCoeff_succ_eqv_neg

/-- The algebraic rib of the scalable cancellation proof.  This statement is
independent of the evaluation point and tolerance: every coefficient below the
first possible truncation error agrees in the finite Euler and geometric
polynomials. -/
structure PositiveArtanhEulerPolynomialFormalCoefficientCertificate : Type 1 where
  coefficientZero :
    forall (stage inner degree index : Nat),
      index < positiveArtanhEulerPolynomialCancellationCount
        stage inner degree ->
      (coeff
        (positiveArtanhEulerGeometricDifferencePoly stage inner degree)
        index).eqv 0

namespace PositiveArtanhEulerPolynomialFormalCoefficientCertificate

/-- Pointwise formal coefficient cancellation compiles exactly to the
executable zero-prefix predicate used by weighted coefficient factoring. -/
def prefixZero
    (certificate : PositiveArtanhEulerPolynomialFormalCoefficientCertificate)
    (stage inner degree : Nat) :
    zeroPrefix
      (positiveArtanhEulerPolynomialCancellationCount stage inner degree)
      (positiveArtanhEulerGeometricDifferencePoly stage inner degree) :=
  zeroPrefix_of_coeff_eqv_zero _ _
    (certificate.coefficientZero stage inner degree)

end PositiveArtanhEulerPolynomialFormalCoefficientCertificate

namespace PositiveArtanhEulerPolynomialStableCoefficientCertificate

/-- Euler valuation removes the `inner` truncation from the formal
certificate.  A proof of the stabilized artanh/geometric identity therefore
inhabits the original four-index coefficient certificate. -/
def toFormal
    (certificate :
      PositiveArtanhEulerPolynomialStableCoefficientCertificate) :
    PositiveArtanhEulerPolynomialFormalCoefficientCertificate where
  coefficientZero stage inner degree index hindex := by
    have hinner : index < inner :=
      Nat.lt_of_lt_of_le hindex (Nat.min_le_left _ _)
    have hrest : index < min (2 * stage + 1) (degree + 1) :=
      Nat.lt_of_lt_of_le hindex (Nat.min_le_right _ _)
    have hstage : index < 2 * stage + 1 :=
      Nat.lt_of_lt_of_le hrest (Nat.min_le_left _ _)
    have hdegree : index < degree + 1 :=
      Nat.lt_of_lt_of_le hrest (Nat.min_le_right _ _)
    have heuler := coeff_positiveArtanhExpPartialPoly_eq_stable_of_lt
      stage inner index hinner
    have hagreement := certificate.coefficientAgreement
      stage degree index hstage hdegree
    exact coeff_psub_eqv_zero_of_eqv _ _ index
      (Q'.eqv_trans _ _ _ heuler hagreement)

end PositiveArtanhEulerPolynomialStableCoefficientCertificate

namespace PositiveArtanhEulerPolynomialTargetCoefficientCertificate

/-- The closed finite-geometric coefficient formula removes `degree` from the
caller-supplied algebraic frontier. -/
def toStable
    (certificate :
      PositiveArtanhEulerPolynomialTargetCoefficientCertificate) :
    PositiveArtanhEulerPolynomialStableCoefficientCertificate where
  coefficientAgreement stage degree index hstage hdegree :=
    Q'.eqv_trans _ _ _
      (certificate.coefficientTarget stage index hstage)
      (Q'.eqv_symm
        (coeff_positiveArtanhGeometricApproxPoly_eq_target
          degree index hdegree))

end PositiveArtanhEulerPolynomialTargetCoefficientCertificate

namespace PositiveArtanhEulerPolynomialStableRecurrenceCertificate

/-- The proved two coefficient seeds plus the local successor recurrence
generate every closed target coefficient below the artanh truncation order. -/
def toTarget
    (certificate :
      PositiveArtanhEulerPolynomialStableRecurrenceCertificate) :
    PositiveArtanhEulerPolynomialTargetCoefficientCertificate where
  coefficientTarget := by
    intro stage index hindex
    induction index generalizing stage with
    | zero =>
        exact Q'.eqv_trans _ 1 _
          (positiveArtanhEulerStableCoeff_zero_eqv_one stage)
          (Q'.eqv_symm positiveArtanhFormalTargetCoeff_zero_eqv_one)
    | succ index ih =>
        cases index with
        | zero =>
            cases stage with
            | zero => omega
            | succ stage =>
                exact Q'.eqv_trans _ negativeTwo _
                  (positiveArtanhEulerStableCoeff_one_eqv_negativeTwo stage)
                  (Q'.eqv_symm
                    positiveArtanhFormalTargetCoeff_one_eqv_negativeTwo)
        | succ index =>
            have hprevious : index + 1 < 2 * stage + 1 := by omega
            exact Q'.eqv_trans _
              ((-1 : Q') *
                positiveArtanhEulerStableCoeff stage (index + 1)) _
              (certificate.coefficientSucc stage (index + 1)
                (by omega) hindex)
              (Q'.eqv_trans _
                ((-1 : Q') *
                  positiveArtanhFormalTargetCoeff (index + 1)) _
                (Q'.mul_eqv_congr_left (-1) _ _
                  (ih stage hprevious))
                (Q'.eqv_symm
                  (positiveArtanhFormalTargetCoeff_succ_eqv_neg
                    (index + 1) (by omega))))

end PositiveArtanhEulerPolynomialStableRecurrenceCertificate

/-- Canonical target-coefficient certificate generated from the internally
proved recurrence. -/
def canonicalPositiveArtanhEulerPolynomialTargetCoefficientCertificate :
    PositiveArtanhEulerPolynomialTargetCoefficientCertificate :=
  canonicalPositiveArtanhEulerPolynomialStableRecurrenceCertificate.toTarget

/-- Canonical stabilized coefficient agreement with every finite geometric
truncation in range. -/
def canonicalPositiveArtanhEulerPolynomialStableCoefficientCertificate :
    PositiveArtanhEulerPolynomialStableCoefficientCertificate :=
  canonicalPositiveArtanhEulerPolynomialTargetCoefficientCertificate.toStable

/-- Canonical exact formal cancellation certificate for the entire common
finite Euler/geometric prefix. -/
def canonicalPositiveArtanhEulerPolynomialFormalCoefficientCertificate :
    PositiveArtanhEulerPolynomialFormalCoefficientCertificate :=
  canonicalPositiveArtanhEulerPolynomialStableCoefficientCertificate.toFormal

/-- The analytic rib after the entire formally cancelling prefix has been
removed.  It contains no algebraic cancellation field and can therefore be
developed independently of the formal coefficient proof. -/
structure PositiveWindowArtanhEulerPolynomialFullTailCertificate
    (z : Q') (_hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  tailBound : forall epsilon : Q', (0 : Q') < epsilon ->
    let count := positiveArtanhEulerAnchorCancellationCount z epsilon
    let polynomial := positiveArtanhEulerAnchorDifferencePoly z epsilon
    (Q'.abs z) ^ count *
        weightedL1 (Q'.abs z) (List.drop count polynomial) <=
      positiveArtanhGeometricComparisonTolerance epsilon

/-- Uniform producer of the analytic full-tail certificates. -/
structure PositiveWindowArtanhEulerPolynomialFullTailCompiler : Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerPolynomialFullTailCertificate z hz hzb

/-- Strictly smaller analytic residue after the computed cancellation radius
has been proved to pay the tolerance.  The caller need only bound the shifted
weighted coefficient tail by the fixed rational constant two; no
epsilon-dependent radius estimate remains in the interface. -/
structure PositiveWindowArtanhEulerPolynomialResidualTailSizeCertificate
    (z : Q') (_hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  tailSizeBound : forall epsilon : Q', (0 : Q') < epsilon ->
    let degree := positiveArtanhGeometricAnchorDegree epsilon
    let polynomial := positiveArtanhEulerAnchorDifferencePoly z epsilon
    weightedL1 (Q'.abs z) (List.drop (degree + 1) polynomial) <=
      Q'.ofNat 2

/-- Uniform producer of the residual shifted-tail-size certificates. -/
structure PositiveWindowArtanhEulerPolynomialResidualTailSizeCompiler : Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerPolynomialResidualTailSizeCertificate z hz hzb

/-- Smaller analytic frontier after computing the first uncancelled
coefficient exactly.  Only the tail strictly beyond that boundary remains,
with the fixed size-three budget paid down to size two by `|z| <= 1/3`. -/
structure PositiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCertificate
    (z : Q') (_hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  tailSizeBound : forall epsilon : Q', (0 : Q') < epsilon ->
    let degree := positiveArtanhGeometricAnchorDegree epsilon
    let polynomial := positiveArtanhEulerAnchorDifferencePoly z epsilon
    weightedL1 (Q'.abs z) (List.drop (degree + 2) polynomial) <=
      Q'.ofNat 3

/-- Uniform producer of the post-boundary shifted-tail-size certificates. -/
structure PositiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCompiler :
    Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCertificate
      z hz hzb

namespace PositiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCertificate

/-- The exact unit boundary coefficient and direct-window radius compile the
post-boundary size-three certificate to the former residual size-two one. -/
def toResidualTailSize
    {z : Q'} {hz : (0 : Q') < z}
    {hzb : Q'.abs z <= CRealLog.recipOdd 1}
    (certificate :
      PositiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCertificate
        z hz hzb) :
    PositiveWindowArtanhEulerPolynomialResidualTailSizeCertificate
      z hz hzb where
  tailSizeBound epsilon hepsilon :=
    positiveArtanhEulerResidualTailSize_two_of_postBoundary_three
      z hz hzb epsilon (certificate.tailSizeBound epsilon hepsilon)

end PositiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCertificate

/-- A post-boundary tail compiler supplies the residual shifted-tail
compiler while retaining the same rational input. -/
def positiveWindowArtanhEulerPolynomialResidualTailSizeCompilerOfPostBoundary
    (compiler :
      PositiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCompiler) :
    PositiveWindowArtanhEulerPolynomialResidualTailSizeCompiler where
  evaluate z hz hzb :=
    (compiler.evaluate z hz hzb).toResidualTailSize

namespace PositiveWindowArtanhEulerPolynomialResidualTailSizeCertificate

/-- The proved cutoff/radius decay compiles a fixed tail-size bound into the
previous full analytic tail certificate. -/
def toFullTail
    {z : Q'} {hz : (0 : Q') < z}
    {hzb : Q'.abs z <= CRealLog.recipOdd 1}
    (certificate :
      PositiveWindowArtanhEulerPolynomialResidualTailSizeCertificate
        z hz hzb) :
    PositiveWindowArtanhEulerPolynomialFullTailCertificate z hz hzb where
  tailBound epsilon hepsilon := by
    let count := positiveArtanhEulerAnchorCancellationCount z epsilon
    let degree := positiveArtanhGeometricAnchorDegree epsilon
    let polynomial := positiveArtanhEulerAnchorDifferencePoly z epsilon
    have hcount : count = degree + 1 :=
      positiveArtanhEulerAnchorCancellationCount_eq_geometricDegree_succ
        z hz epsilon
    have hsize :
        weightedL1 (Q'.abs z) (List.drop count polynomial) <= Q'.ofNat 2 := by
      rw [hcount]
      exact certificate.tailSizeBound epsilon hepsilon
    have hscaled :
        (Q'.abs z) ^ count *
            weightedL1 (Q'.abs z) (List.drop count polynomial) <=
          (Q'.abs z) ^ count * Q'.ofNat 2 :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hsize
        (Q'.pow_nonneg _ (Q'.abs_nonneg z) count)
    exact Q'.le_trans' _ _ _ hscaled
      (positiveArtanhEulerAnchorRadiusPow_mul_two_le_comparisonTolerance
        z hz hzb epsilon hepsilon)

end PositiveWindowArtanhEulerPolynomialResidualTailSizeCertificate

/-- A fixed residual tail-size compiler supplies the former full analytic
tail compiler. -/
def positiveWindowArtanhEulerPolynomialFullTailCompilerOfResidualTailSize
    (compiler :
      PositiveWindowArtanhEulerPolynomialResidualTailSizeCompiler) :
    PositiveWindowArtanhEulerPolynomialFullTailCompiler where
  evaluate z hz hzb := (compiler.evaluate z hz hzb).toFullTail

/-- Tail-only presentation after the constant-coefficient cancellation has
been proved internally.  Unlike `PositiveWindowArtanhEulerPolynomialPrefixTailCertificate`,
there is no exact-prefix field left for callers to inhabit. -/
structure PositiveWindowArtanhEulerPolynomialOneTailCertificate
    (z : Q') (_hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  tailBound : forall epsilon : Q', (0 : Q') < epsilon ->
    (Q'.abs z) ^ 1 *
        weightedL1 (Q'.abs z)
          (List.drop 1 (positiveArtanhEulerAnchorDifferencePoly z epsilon)) <=
      positiveArtanhGeometricComparisonTolerance epsilon

/-- Uniform producer of the reduced, tail-only certificates. -/
structure PositiveWindowArtanhEulerPolynomialOneTailCompiler : Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerPolynomialOneTailCertificate z hz hzb

/-- Tail-only presentation after both the constant and linear coefficients
have been proved to cancel. -/
structure PositiveWindowArtanhEulerPolynomialTwoTailCertificate
    (z : Q') (_hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  tailBound : forall epsilon : Q', (0 : Q') < epsilon ->
    (Q'.abs z) ^ 2 *
        weightedL1 (Q'.abs z)
          (List.drop 2 (positiveArtanhEulerAnchorDifferencePoly z epsilon)) <=
      positiveArtanhGeometricComparisonTolerance epsilon

/-- Uniform producer of the quadratic-radius tail certificate. -/
structure PositiveWindowArtanhEulerPolynomialTwoTailCompiler : Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerPolynomialTwoTailCertificate z hz hzb

namespace PositiveWindowArtanhEulerPolynomialOneTailCertificate

/-- The proved constant cancellation contracts the sole remaining tail field
to the original full coefficient inequality. -/
def toCoefficient
    {z : Q'} {hz : (0 : Q') < z}
    {hzb : Q'.abs z <= CRealLog.recipOdd 1}
    (certificate : PositiveWindowArtanhEulerPolynomialOneTailCertificate
      z hz hzb) :
    PositiveWindowArtanhEulerPolynomialCoefficientCertificate z hz hzb where
  coefficientBound epsilon hepsilon := by
    have hfactor := weightedL1_eqv_pow_mul_drop_of_zeroPrefix
      (Q'.abs z) 1 (positiveArtanhEulerAnchorDifferencePoly z epsilon)
      (zeroPrefix_one_positiveArtanhEulerAnchorDifferencePoly z epsilon)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (certificate.tailBound epsilon hepsilon)

end PositiveWindowArtanhEulerPolynomialOneTailCertificate

/-- A tail-only compiler produces the full coefficient compiler. -/
def positiveWindowArtanhEulerPolynomialCoefficientCompilerOfOneTail
    (compiler : PositiveWindowArtanhEulerPolynomialOneTailCompiler) :
    PositiveWindowArtanhEulerPolynomialCoefficientCompiler where
  evaluate z hz hzb := (compiler.evaluate z hz hzb).toCoefficient

namespace PositiveWindowArtanhEulerPolynomialTwoTailCertificate

/-- The proved constant and linear cancellations contract the quadratic tail
to the full coefficient inequality. -/
def toCoefficient
    {z : Q'} {hz : (0 : Q') < z}
    {hzb : Q'.abs z <= CRealLog.recipOdd 1}
    (certificate : PositiveWindowArtanhEulerPolynomialTwoTailCertificate
      z hz hzb) :
    PositiveWindowArtanhEulerPolynomialCoefficientCertificate z hz hzb where
  coefficientBound epsilon hepsilon := by
    have hfactor := weightedL1_eqv_pow_mul_drop_of_zeroPrefix
      (Q'.abs z) 2 (positiveArtanhEulerAnchorDifferencePoly z epsilon)
      (zeroPrefix_two_positiveArtanhEulerAnchorDifferencePoly z hz epsilon)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (certificate.tailBound epsilon hepsilon)

end PositiveWindowArtanhEulerPolynomialTwoTailCertificate

/-- A quadratic-tail compiler produces the full coefficient compiler. -/
def positiveWindowArtanhEulerPolynomialCoefficientCompilerOfTwoTail
    (compiler : PositiveWindowArtanhEulerPolynomialTwoTailCompiler) :
    PositiveWindowArtanhEulerPolynomialCoefficientCompiler where
  evaluate z hz hzb := (compiler.evaluate z hz hzb).toCoefficient

namespace PositiveWindowArtanhEulerPolynomialPrefixTailCertificate

/-- Exact zero-prefix factoring contracts the two prefix/tail fields to the
single full coefficient inequality. -/
def toCoefficient
    {z : Q'} {hz : (0 : Q') < z}
    {hzb : Q'.abs z <= CRealLog.recipOdd 1}
    (certificate : PositiveWindowArtanhEulerPolynomialPrefixTailCertificate
      z hz hzb) :
    PositiveWindowArtanhEulerPolynomialCoefficientCertificate z hz hzb where
  coefficientBound epsilon hepsilon := by
    let count := positiveArtanhEulerAnchorCancellationCount z epsilon
    let polynomial := positiveArtanhEulerAnchorDifferencePoly z epsilon
    have hfactor := weightedL1_eqv_pow_mul_drop_of_zeroPrefix
      (Q'.abs z) count polynomial
      (certificate.prefixZero epsilon hepsilon)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (certificate.tailBound epsilon hepsilon)

end PositiveWindowArtanhEulerPolynomialPrefixTailCertificate

/-- Uniform prefix/tail certificates compile to the full coefficient
compiler. -/
def positiveWindowArtanhEulerPolynomialCoefficientCompilerOfPrefixTail
    (compiler : PositiveWindowArtanhEulerPolynomialPrefixTailCompiler) :
    PositiveWindowArtanhEulerPolynomialCoefficientCompiler where
  evaluate z hz hzb := (compiler.evaluate z hz hzb).toCoefficient

/-- The independently proved algebraic and analytic ribs rejoin at the
prefix/tail interface.  From this point onward there is one scalar compiler
path: no evaluation point or observable is changed by the join. -/
def positiveWindowArtanhEulerPolynomialPrefixTailCompilerOfFormalAndTail
    (formal : PositiveArtanhEulerPolynomialFormalCoefficientCertificate)
    (tail : PositiveWindowArtanhEulerPolynomialFullTailCompiler) :
    PositiveWindowArtanhEulerPolynomialPrefixTailCompiler where
  evaluate z hz hzb :=
    { prefixZero := fun epsilon hepsilon => by
        unfold positiveArtanhEulerAnchorCancellationCount
          positiveArtanhEulerAnchorDifferencePoly
        exact formal.prefixZero _ _ _
      tailBound := fun epsilon hepsilon =>
        (tail.evaluate z hz hzb).tailBound epsilon hepsilon }

/-- The algebraic/analytic join contracts directly to the original weighted
coefficient compiler. -/
def positiveWindowArtanhEulerPolynomialCoefficientCompilerOfFormalAndTail
    (formal : PositiveArtanhEulerPolynomialFormalCoefficientCertificate)
    (tail : PositiveWindowArtanhEulerPolynomialFullTailCompiler) :
    PositiveWindowArtanhEulerPolynomialCoefficientCompiler :=
  positiveWindowArtanhEulerPolynomialCoefficientCompilerOfPrefixTail
    (positiveWindowArtanhEulerPolynomialPrefixTailCompilerOfFormalAndTail
      formal tail)

/-- The reduced stabilized-coefficient certificate and the independent
analytic tail compiler rejoin at the same coefficient interface. -/
def positiveWindowArtanhEulerPolynomialCoefficientCompilerOfStableAndTail
    (stable : PositiveArtanhEulerPolynomialStableCoefficientCertificate)
    (tail : PositiveWindowArtanhEulerPolynomialFullTailCompiler) :
    PositiveWindowArtanhEulerPolynomialCoefficientCompiler :=
  positiveWindowArtanhEulerPolynomialCoefficientCompilerOfFormalAndTail
    stable.toFormal tail

/-- The stage/index target certificate and analytic tail contract to the same
weighted coefficient compiler. -/
def positiveWindowArtanhEulerPolynomialCoefficientCompilerOfTargetAndTail
    (target : PositiveArtanhEulerPolynomialTargetCoefficientCertificate)
    (tail : PositiveWindowArtanhEulerPolynomialFullTailCompiler) :
    PositiveWindowArtanhEulerPolynomialCoefficientCompiler :=
  positiveWindowArtanhEulerPolynomialCoefficientCompilerOfStableAndTail
    target.toStable tail

/-- The local stabilized-coefficient recurrence and analytic tail contract to
the same weighted coefficient compiler. -/
def positiveWindowArtanhEulerPolynomialCoefficientCompilerOfRecurrenceAndTail
    (recurrence :
      PositiveArtanhEulerPolynomialStableRecurrenceCertificate)
    (tail : PositiveWindowArtanhEulerPolynomialFullTailCompiler) :
    PositiveWindowArtanhEulerPolynomialCoefficientCompiler :=
  positiveWindowArtanhEulerPolynomialCoefficientCompilerOfTargetAndTail
    recurrence.toTarget tail

/-- With the algebraic recurrence now proved internally, the full analytic
tail is the sole remaining input to the scalable coefficient compiler. -/
def positiveWindowArtanhEulerPolynomialCoefficientCompilerOfFullTail
    (tail : PositiveWindowArtanhEulerPolynomialFullTailCompiler) :
    PositiveWindowArtanhEulerPolynomialCoefficientCompiler :=
  positiveWindowArtanhEulerPolynomialCoefficientCompilerOfFormalAndTail
    canonicalPositiveArtanhEulerPolynomialFormalCoefficientCertificate tail

/-- Boolean-check presentation of the coefficient certificate.  It is useful
for generated finite certificates because each field reduces to an executable
kernel computation. -/
structure PositiveWindowArtanhEulerPolynomialCheckedCertificate
    (z : Q') (_hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  checkPasses : forall epsilon : Q', (0 : Q') < epsilon ->
    positiveArtanhEulerPolynomialCoefficientCheck z epsilon = true

/-- Uniform producer of Boolean-check coefficient certificates. -/
structure PositiveWindowArtanhEulerPolynomialCheckedCompiler : Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerPolynomialCheckedCertificate z hz hzb

namespace PositiveWindowArtanhEulerPolynomialCheckedCertificate

/-- A successful executable check is the proposition-level coefficient
certificate consumed by the analytic path. -/
def toCoefficient
    {z : Q'} {hz : (0 : Q') < z}
    {hzb : Q'.abs z <= CRealLog.recipOdd 1}
    (certificate : PositiveWindowArtanhEulerPolynomialCheckedCertificate
      z hz hzb) :
    PositiveWindowArtanhEulerPolynomialCoefficientCertificate z hz hzb where
  coefficientBound epsilon hepsilon := by
    have hcheck := certificate.checkPasses epsilon hepsilon
    unfold positiveArtanhEulerPolynomialCoefficientCheck at hcheck
    exact of_decide_eq_true hcheck

end PositiveWindowArtanhEulerPolynomialCheckedCertificate

/-- Uniform successful Boolean checks compile to coefficient certificates. -/
def positiveWindowArtanhEulerPolynomialCoefficientCompilerOfChecked
    (compiler : PositiveWindowArtanhEulerPolynomialCheckedCompiler) :
    PositiveWindowArtanhEulerPolynomialCoefficientCompiler where
  evaluate z hz hzb := (compiler.evaluate z hz hzb).toCoefficient

namespace PositiveWindowArtanhEulerPolynomialCoefficientCertificate

/-- Weighted coefficient control compiles to the direct finite value
comparison on the positive-artanh window. -/
def toGeometricValueAnchor
    {z : Q'} {hz : (0 : Q') < z}
    {hzb : Q'.abs z <= CRealLog.recipOdd 1}
    (certificate :
      PositiveWindowArtanhEulerPolynomialCoefficientCertificate z hz hzb) :
    PositiveWindowArtanhEulerGeometricValueAnchorCertificate z hz hzb where
  anchorValueComparison epsilon hepsilon := by
    let stage : Nat := positiveArtanhEulerAnchorStage epsilon
    let inner : Nat := positiveArtanhEulerAnchorPivot z epsilon
    let degree : Nat := positiveArtanhGeometricAnchorDegree epsilon
    let polynomial : Poly :=
      positiveArtanhEulerGeometricDifferencePoly stage inner degree
    have hpoly : Q'.abs (eval polynomial z) <=
        weightedL1 (Q'.abs z) polynomial :=
      abs_eval_le_weightedL1 (Q'.abs_nonneg z)
        (Q'.le_refl' (Q'.abs z)) polynomial
    have heqv := eval_positiveArtanhEulerGeometricDifferencePoly
      z stage inner degree
    have habsEqv :
        (Q'.abs (eval polynomial z)).eqv
          (Q'.abs
            (ExpNeg.partialSum (positiveArtanhExponent z stage) inner +
              -(positiveArtanhGeometricApprox z degree))) :=
      Q'.abs_eqv_congr heqv
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm habsEqv))
      (Q'.le_trans' _ _ _ hpoly
        (certificate.coefficientBound epsilon hepsilon))

end PositiveWindowArtanhEulerPolynomialCoefficientCertificate

/-- Uniform coefficient compilers produce the direct geometric-value
compiler and therefore the full scalar inverse. -/
def positiveWindowArtanhEulerGeometricValueAnchorCompilerOfPolynomial
    (compiler : PositiveWindowArtanhEulerPolynomialCoefficientCompiler) :
    PositiveWindowArtanhEulerGeometricValueAnchorCompiler where
  evaluate z hz hzb :=
    (compiler.evaluate z hz hzb).toGeometricValueAnchor

def positiveWindowArtanhEulerCompilerOfPolynomial
    (compiler : PositiveWindowArtanhEulerPolynomialCoefficientCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfGeometricValueAnchor
    (positiveWindowArtanhEulerGeometricValueAnchorCompilerOfPolynomial compiler)

/-- Uniform prefix/tail coefficient certificates compile all the way to the
scalar inverse. -/
def positiveWindowArtanhEulerCompilerOfPolynomialPrefixTail
    (compiler : PositiveWindowArtanhEulerPolynomialPrefixTailCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfPolynomial
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfPrefixTail compiler)

/-- Independent formal-cancellation and analytic-tail compilers rejoin and
compile all the way to the same scalar inverse. -/
def positiveWindowArtanhEulerCompilerOfPolynomialFormalAndTail
    (formal : PositiveArtanhEulerPolynomialFormalCoefficientCertificate)
    (tail : PositiveWindowArtanhEulerPolynomialFullTailCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfPolynomial
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfFormalAndTail
      formal tail)

/-- The stabilized-coefficient frontier plus the full analytic tail compiles
to the same scalar inverse. -/
def positiveWindowArtanhEulerCompilerOfPolynomialStableAndTail
    (stable : PositiveArtanhEulerPolynomialStableCoefficientCertificate)
    (tail : PositiveWindowArtanhEulerPolynomialFullTailCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfPolynomial
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfStableAndTail
      stable tail)

/-- The reduced stage/index target certificate plus the analytic tail compiles
to the same scalar inverse. -/
def positiveWindowArtanhEulerCompilerOfPolynomialTargetAndTail
    (target : PositiveArtanhEulerPolynomialTargetCoefficientCertificate)
    (tail : PositiveWindowArtanhEulerPolynomialFullTailCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfPolynomial
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfTargetAndTail
      target tail)

/-- The reduced local recurrence plus the independent analytic tail compiles
to the same scalar inverse. -/
def positiveWindowArtanhEulerCompilerOfPolynomialRecurrenceAndTail
    (recurrence :
      PositiveArtanhEulerPolynomialStableRecurrenceCertificate)
    (tail : PositiveWindowArtanhEulerPolynomialFullTailCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfPolynomial
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfRecurrenceAndTail
      recurrence tail)

/-- The internally proved algebraic prefix leaves only the full analytic
tail compiler as an input to the scalar inverse path. -/
def positiveWindowArtanhEulerCompilerOfPolynomialFullTail
    (tail : PositiveWindowArtanhEulerPolynomialFullTailCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfPolynomial
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfFullTail tail)

/-- The residual shifted-tail-size compiler now reaches the scalar inverse:
the cancellation-count and radius-decay factors are internal theorems. -/
def positiveWindowArtanhEulerCompilerOfPolynomialResidualTailSize
    (tail : PositiveWindowArtanhEulerPolynomialResidualTailSizeCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfPolynomialFullTail
    (positiveWindowArtanhEulerPolynomialFullTailCompilerOfResidualTailSize tail)

/-- The exact first boundary coefficient is internal, so a post-boundary
size-three compiler reaches the same scalar inverse. -/
def positiveWindowArtanhEulerCompilerOfPolynomialPostBoundaryTailSize
    (tail :
      PositiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfPolynomialResidualTailSize
    (positiveWindowArtanhEulerPolynomialResidualTailSizeCompilerOfPostBoundary
      tail)

/-- The reduced tail-only compiler also compiles all the way to the scalar
inverse; its constant cancellation is a theorem, not a caller-supplied
field. -/
def positiveWindowArtanhEulerCompilerOfPolynomialOneTail
    (compiler : PositiveWindowArtanhEulerPolynomialOneTailCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfPolynomial
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfOneTail compiler)

/-- The quadratic-radius tail compiler compiles to the same scalar inverse. -/
def positiveWindowArtanhEulerCompilerOfPolynomialTwoTail
    (compiler : PositiveWindowArtanhEulerPolynomialTwoTailCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfPolynomial
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfTwoTail compiler)

/-- Uniform executable coefficient checks compile all the way to the scalar
inverse. -/
def positiveWindowArtanhEulerCompilerOfPolynomialChecked
    (compiler : PositiveWindowArtanhEulerPolynomialCheckedCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfPolynomial
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfChecked compiler)

end YMGap.Constructive.CRealArtanhEulerPolynomialAnchor

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.eval_positiveArtanhEulerGeometricDifferencePoly
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.weightedL1_positiveArtanhExponentPoly_le
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.weightedL1_expPartialPoly_le
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.auditPositiveArtanhEulerPolynomialCoefficientBound
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialCheckedCertificate.toCoefficient
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialPrefixTailCertificate.toCoefficient
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveArtanhEulerPolynomialFormalCoefficientCertificate.prefixZero
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.zeroPrefix_expTermPoly
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.coeff_expPartialPoly_add_stable
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.coeff_positiveArtanhExpPartialPoly_eq_stable_of_lt
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveArtanhEulerPolynomialStableCoefficientCertificate.toFormal
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.coeff_ppow_neg_pvar
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.coeff_geometricSumPoly
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.coeff_positiveArtanhGeometricApproxPoly_eq_target
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveArtanhEulerPolynomialTargetCoefficientCertificate.toStable
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveArtanhEulerPolynomialStableRecurrenceCertificate.toTarget
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.pderiv_positiveArtanhExponentPoly
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.pderiv_expPartialPoly_succ
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveArtanhExpPartialPoly_finiteDifferentialEquation
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerStableCoeff_differentialRecurrence
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerStableCoeff_succ_eqv_neg
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.canonicalPositiveArtanhEulerPolynomialFormalCoefficientCertificate
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerPolynomialPrefixTailCompilerOfFormalAndTail
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialFormalAndTail
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialStableAndTail
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialTargetAndTail
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialRecurrenceAndTail
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialFullTail
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerAnchorCancellationCount_ge_comparisonDen_succ
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerAnchorCancellationCount_eq_geometricDegree_succ
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerAnchorRadiusPow_mul_two_le_comparisonTolerance
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.coeff_positiveArtanhEulerAnchorDifferencePoly_boundary
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.abs_coeff_positiveArtanhEulerAnchorDifferencePoly_boundary_eqv_one
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveArtanhEulerResidualTailSize_two_of_postBoundary_three
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCertificate.toResidualTailSize
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialResidualTailSizeCertificate.toFullTail
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialResidualTailSize
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomialPostBoundaryTailSize
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.zeroPrefix_one_positiveArtanhEulerAnchorDifferencePoly
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.zeroPrefix_two_positiveArtanhEulerAnchorDifferencePoly
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialOneTailCertificate.toCoefficient
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialTwoTailCertificate.toCoefficient
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialCoefficientCertificate.toGeometricValueAnchor
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomial
