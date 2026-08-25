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

namespace YMGap.Constructive.CRealArtanhEulerPolynomialAnchor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.CRealArtanhEulerRatio
open YMGap.Constructive.CRealArtanhEulerGeometricAnchor
open YMGap.Constructive.QPolyWeightedL1

local infix:50 " ~q " => Q'.eqv

/-- Constant polynomial. -/
def pconst (c : Q') : Poly := [c]

/-- The polynomial variable. -/
def pvar : Poly := [0, 1]

/-- Natural power in the coefficient-list polynomial algebra. -/
def ppow (p : Poly) : Nat -> Poly
  | 0 => pconst 1
  | n + 1 => pmul p (ppow p n)

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

/-- The fully computed cancellation-prefix length. -/
def positiveArtanhEulerAnchorCancellationCount
    (z epsilon : Q') : Nat :=
  positiveArtanhEulerPolynomialCancellationCount
    (positiveArtanhEulerAnchorStage epsilon)
    (positiveArtanhEulerAnchorPivot z epsilon)
    (positiveArtanhGeometricAnchorDegree epsilon)

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

/-- The reduced tail-only compiler also compiles all the way to the scalar
inverse; its constant cancellation is a theorem, not a caller-supplied
field. -/
def positiveWindowArtanhEulerCompilerOfPolynomialOneTail
    (compiler : PositiveWindowArtanhEulerPolynomialOneTailCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfPolynomial
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfOneTail compiler)

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
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.zeroPrefix_one_positiveArtanhEulerAnchorDifferencePoly
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialOneTailCertificate.toCoefficient
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialCoefficientCertificate.toGeometricValueAnchor
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomial
