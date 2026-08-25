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

/-- The executable coefficient inequality at one rational input and
tolerance. -/
def positiveArtanhEulerPolynomialCoefficientBound
    (z epsilon : Q') : Prop :=
  weightedL1 (Q'.abs z)
      (positiveArtanhEulerGeometricDifferencePoly
        (positiveArtanhEulerAnchorStage epsilon)
        (positiveArtanhEulerAnchorPivot z epsilon)
        (positiveArtanhGeometricAnchorDegree epsilon)) <=
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
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.auditPositiveArtanhEulerPolynomialCoefficientBound
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialCheckedCertificate.toCoefficient
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.PositiveWindowArtanhEulerPolynomialCoefficientCertificate.toGeometricValueAnchor
#print axioms
  YMGap.Constructive.CRealArtanhEulerPolynomialAnchor.positiveWindowArtanhEulerCompilerOfPolynomial
