/-
# Geometric-polynomial anchor for the positive artanh Euler inverse

The previous frontier asks for one finite denominator-cleared comparison
between an Euler exponential partial sum and `(1-z)/(1+z)`.  This module
inserts an explicit finite polynomial between them.  Its rational residual is
proved geometrically; the remaining certificate will compare only two finite
rational computations at fully computed indices.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Constructive.CRealArtanhEulerRatio
import YMGap.Constructive.QGeometricSum

namespace YMGap.Constructive.CRealArtanhEulerGeometricAnchor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CRealArtanhEulerRatio

/-- The explicit polynomial
`(1-z) * sum_{k=0}^{degree} (-z)^k`, written with the finite sum first so
the denominator-cleared telescope applies directly. -/
def positiveArtanhGeometricApprox (z : Q') (degree : Nat) : Q' :=
  QGeometricSum.geomSum (-z) degree * ((1 : Q') + -z)

/-- The denominator-cleared residual of the geometric polynomial. -/
def positiveArtanhGeometricDefect (z : Q') (degree : Nat) : Q' :=
  (((1 : Q') + z) * positiveArtanhGeometricApprox z degree) +
    -((1 : Q') + -z)

/-- The denominator times the geometric sum is exactly
`1 - (-z)^(degree+1)`. -/
theorem denominator_mul_geomSum_eqv
    (z : Q') (degree : Nat) :
    (((1 : Q') + z) * QGeometricSum.geomSum (-z) degree).eqv
      ((1 : Q') + -((-z) ^ (degree + 1))) := by
  have hfactor : ((1 : Q') + z).eqv ((1 : Q') + -(-z)) :=
    Q'.add_eqv_congr_left 1 _ _ (Q'.eqv_symm (Q'.neg_neg_eqv z))
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hfactor)
    (QGeometricSum.one_sub_mul_geomSum (-z) degree)

/-- Exact residual of the finite polynomial: one final geometric power and
no division. -/
theorem positiveArtanhGeometricDefect_eqv
    (z : Q') (degree : Nat) :
    (positiveArtanhGeometricDefect z degree).eqv
      (-(((1 : Q') + -z) * ((-z) ^ (degree + 1)))) := by
  let numerator : Q' := (1 : Q') + -z
  let power : Q' := (-z) ^ (degree + 1)
  unfold positiveArtanhGeometricDefect positiveArtanhGeometricApprox
  change ((((1 : Q') + z) *
      (QGeometricSum.geomSum (-z) degree * numerator)) +
        -numerator).eqv (-(numerator * power))
  refine Q'.eqv_trans _
    (((((1 : Q') + z) * QGeometricSum.geomSum (-z) degree) *
      numerator) + -numerator) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv ((1 : Q') + z)
          (QGeometricSum.geomSum (-z) degree) numerator))) ?_
  refine Q'.eqv_trans _
    ((((1 : Q') + -power) * numerator) + -numerator) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ numerator
        (denominator_mul_geomSum_eqv z degree))) ?_
  refine Q'.eqv_trans _
    (((1 : Q') * numerator + (-power) * numerator) + -numerator) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_mul_eqv 1 (-power) numerator)) ?_
  refine Q'.eqv_trans _
    ((numerator + (-(power * numerator))) + -numerator) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _
        (numerator + (-power) * numerator) _
        (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv numerator))
        (Q'.add_eqv_congr_left numerator _ _
          (Q'.neg_mul_eqv power numerator)))) ?_
  refine Q'.eqv_trans _
    (((-(power * numerator)) + numerator) + -numerator) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_comm_eqv numerator (-(power * numerator)))) ?_
  refine Q'.eqv_trans _
    ((-(power * numerator)) + (numerator + -numerator)) _
    (Q'.add_assoc_eqv (-(power * numerator)) numerator (-numerator)) ?_
  refine Q'.eqv_trans _ ((-(power * numerator)) + 0) _
    (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv numerator)) ?_
  refine Q'.eqv_trans _ (-(power * numerator)) _
    (Q'.eqv_of_eq (Q'.add_zero' (-(power * numerator)))) ?_
  exact Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv power numerator)

/-- The direct positive artanh window is contained in the dyadic half
window, including after negation. -/
theorem abs_neg_z_le_half
    (z : Q') (hzb : Q'.abs z <= CRealLog.recipOdd 1) :
    Q'.abs (-z) <= HalfPow.half :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' z))
    (Q'.le_trans' _ _ _ hzb (by decide))

/-- Every power of `-z` is dominated by the matching half-power. -/
theorem abs_neg_z_pow_le_half
    (z : Q') (hzb : Q'.abs z <= CRealLog.recipOdd 1) :
    forall n : Nat, Q'.abs ((-z) ^ n) <= HalfPow.half ^ n
  | 0 => by
      rw [Q'.pow_zero, Q'.pow_zero]
      exact Q'.abs_le (by decide) (by decide)
  | n + 1 => by
      show Q'.abs ((-z) * (-z) ^ n) <=
        HalfPow.half * HalfPow.half ^ n
      refine Q'.le_trans' _ _ _
        (ExpNeg.abs_mul_le (-z) ((-z) ^ n)) ?_
      exact Q'.mul_le_mul_of_nonneg
        (abs_neg_z_le_half z hzb)
        (abs_neg_z_pow_le_half z hzb n)
        HalfPow.half_nonneg (Q'.abs_nonneg _)

/-- The numerator `1-z` is nonnegative on the direct positive window. -/
theorem positiveArtanhNumerator_nonnegative
    (z : Q') (hzb : Q'.abs z <= CRealLog.recipOdd 1) :
    (0 : Q') <= (1 : Q') + -z := by
  have hzleOne : z <= (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self z)
      (Q'.le_trans' _ _ _ hzb (by decide))
  exact Q'.sub_nonneg_of_le hzleOne

/-- The numerator `1-z` has absolute value at most one when `z` is
nonnegative. -/
theorem abs_positiveArtanhNumerator_le_one
    (z : Q') (hz : (0 : Q') < z)
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) :
    Q'.abs ((1 : Q') + -z) <= (1 : Q') := by
  have hnonneg := positiveArtanhNumerator_nonnegative z hzb
  rw [ExpNeg.abs_of_nonneg hnonneg]
  have hneg : -z <= (0 : Q') :=
    Q'.nonpos_neg_of_nonneg (Q'.le_of_lt hz)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 (-z) 0 hneg)
    (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1)))

/-- The exact rational defect of the degree-`degree` polynomial is bounded by
one dyadic power beyond its degree. -/
theorem positiveArtanhGeometricDefect_abs_le_halfPow
    (z : Q') (hz : (0 : Q') < z)
    (hzb : Q'.abs z <= CRealLog.recipOdd 1)
    (degree : Nat) :
    Q'.abs (positiveArtanhGeometricDefect z degree) <=
      HalfPow.half ^ (degree + 1) := by
  let numerator : Q' := (1 : Q') + -z
  let power : Q' := (-z) ^ (degree + 1)
  have heqv := positiveArtanhGeometricDefect_eqv z degree
  have habsEqv :
      (Q'.abs (positiveArtanhGeometricDefect z degree)).eqv
        (Q'.abs (-(numerator * power))) :=
    Q'.abs_eqv_congr heqv
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv habsEqv) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_neg' (numerator * power))) ?_
  refine Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le numerator power) ?_
  refine Q'.le_trans' _
    ((1 : Q') * (HalfPow.half ^ (degree + 1))) _ ?_ ?_
  · exact Q'.mul_le_mul_of_nonneg
      (abs_positiveArtanhNumerator_le_one z hz hzb)
      (abs_neg_z_pow_le_half z hzb (degree + 1))
      (by decide) (Q'.abs_nonneg _)
  · exact Q'.le_of_eqv (Q'.one_mul_eqv _)

/-- Half of the single-anchor defect budget is reserved for comparing the
Euler partial sum with the explicit polynomial. -/
def positiveArtanhGeometricComparisonTolerance (epsilon : Q') : Q' :=
  HalfPow.half * positiveArtanhAnchorInnerTolerance epsilon

theorem positiveArtanhGeometricComparisonTolerance_pos
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    (0 : Q') < positiveArtanhGeometricComparisonTolerance epsilon :=
  ExpNeg.half_mul_pos _
    (positiveArtanhAnchorInnerTolerance_pos epsilon hepsilon)

/-- The fully computed polynomial degree at tolerance `epsilon`. -/
def positiveArtanhGeometricAnchorDegree (epsilon : Q') : Nat :=
  (positiveArtanhGeometricComparisonTolerance epsilon).den

/-- At the computed degree, the exact geometric residual fits inside its
reserved half-budget. -/
theorem positiveArtanhGeometricAnchorDefect_abs_le
    (z : Q') (hz : (0 : Q') < z)
    (hzb : Q'.abs z <= CRealLog.recipOdd 1)
    (epsilon : Q') (hepsilon : (0 : Q') < epsilon) :
    Q'.abs
        (positiveArtanhGeometricDefect z
          (positiveArtanhGeometricAnchorDegree epsilon)) <=
      positiveArtanhGeometricComparisonTolerance epsilon := by
  let tolerance : Q' := positiveArtanhGeometricComparisonTolerance epsilon
  let degree : Nat := positiveArtanhGeometricAnchorDegree epsilon
  have htolerance : (0 : Q') < tolerance :=
    positiveArtanhGeometricComparisonTolerance_pos epsilon hepsilon
  have hdefect := positiveArtanhGeometricDefect_abs_le_halfPow
    z hz hzb degree
  have hdrop : HalfPow.half ^ (degree + 1) <= HalfPow.half ^ degree :=
    ExpNeg.pow_half_antitone degree 1
  have hdegree : HalfPow.half ^ degree <= tolerance := by
    exact HalfPow.pow_half_le tolerance htolerance
  exact Q'.le_trans' _ _ _ hdefect
    (Q'.le_trans' _ _ _ hdrop hdegree)

/-- Subtracting the two cleared defects cancels the common numerator exactly;
what remains is the positive denominator times the Euler-value minus the
polynomial-value. -/
theorem clearedDefect_sub_geometricDefect_eqv
    (z : Q') (stage inner degree : Nat) :
    (positiveArtanhEulerClearedDefect z stage inner +
        -(positiveArtanhGeometricDefect z degree)).eqv
      (((1 : Q') + z) *
        (ExpNeg.partialSum (positiveArtanhExponent z stage) inner +
          -(positiveArtanhGeometricApprox z degree))) := by
  let denominator : Q' := (1 : Q') + z
  let numerator : Q' := (1 : Q') + -z
  let value : Q' :=
    ExpNeg.partialSum (positiveArtanhExponent z stage) inner
  let polynomial : Q' := positiveArtanhGeometricApprox z degree
  unfold positiveArtanhEulerClearedDefect positiveArtanhGeometricDefect
  change ((denominator * value + -numerator) +
      -(denominator * polynomial + -numerator)).eqv
    (denominator * (value + -polynomial))
  refine Q'.eqv_trans _
    ((denominator * value + -numerator) +
      (-(denominator * polynomial) + -(-numerator))) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_eqv (denominator * polynomial) (-numerator))) ?_
  refine Q'.eqv_trans _
    ((denominator * value + -numerator) +
      (-(denominator * polynomial) + numerator)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv numerator))) ?_
  refine Q'.eqv_trans _
    (denominator * value +
      (-numerator + (-(denominator * polynomial) + numerator))) _
    (Q'.add_assoc_eqv (denominator * value) (-numerator)
      (-(denominator * polynomial) + numerator)) ?_
  refine Q'.eqv_trans _
    (denominator * value +
      (-numerator + (numerator + -(denominator * polynomial)))) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_left _ _ _
        (Q'.add_comm_eqv (-(denominator * polynomial)) numerator))) ?_
  refine Q'.eqv_trans _
    (denominator * value +
      ((-numerator + numerator) + -(denominator * polynomial))) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (Q'.add_assoc_eqv (-numerator) numerator
          (-(denominator * polynomial))))) ?_
  refine Q'.eqv_trans _
    (denominator * value +
      ((0 : Q') + -(denominator * polynomial))) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.neg_add_self_eqv numerator))) ?_
  refine Q'.eqv_trans _
    (denominator * value + -(denominator * polynomial)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_of_eq (Q'.zero_add' (-(denominator * polynomial))))) ?_
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _
    (denominator * value + denominator * (-polynomial)) _
    (Q'.mul_add_eqv denominator value (-polynomial)) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_neg_eqv denominator polynomial)

/-- The remaining finite certificate compares two explicitly computed
cleared defects at one artanh stage, one Euler pivot, and one polynomial
degree.  It stores no modulus and quantifies over no late stages. -/
structure PositiveWindowArtanhEulerGeometricAnchorCertificate
    (z : Q') (_hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  anchorComparison : forall epsilon : Q', (0 : Q') < epsilon ->
    Q'.abs
        (positiveArtanhEulerClearedDefect z
            (positiveArtanhEulerAnchorStage epsilon)
            (positiveArtanhEulerAnchorPivot z epsilon) +
          -(positiveArtanhGeometricDefect z
            (positiveArtanhGeometricAnchorDegree epsilon))) <=
      positiveArtanhGeometricComparisonTolerance epsilon *
        ((1 : Q') + z)

/-- A uniform producer of the finite geometric-anchor certificates. -/
structure PositiveWindowArtanhEulerGeometricAnchorCompiler : Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerGeometricAnchorCertificate z hz hzb

/-- The narrowest current scalar certificate: at fully computed artanh,
Euler, and polynomial indices, the finite Euler partial sum is close to the
explicit finite geometric polynomial. -/
structure PositiveWindowArtanhEulerGeometricValueAnchorCertificate
    (z : Q') (_hz : (0 : Q') < z)
    (_hzb : Q'.abs z <= CRealLog.recipOdd 1) : Type 1 where
  anchorValueComparison : forall epsilon : Q', (0 : Q') < epsilon ->
    Q'.abs
        (ExpNeg.partialSum
            (positiveArtanhExponent z
              (positiveArtanhEulerAnchorStage epsilon))
            (positiveArtanhEulerAnchorPivot z epsilon) +
          -(positiveArtanhGeometricApprox z
            (positiveArtanhGeometricAnchorDegree epsilon))) <=
      positiveArtanhGeometricComparisonTolerance epsilon

/-- A uniform producer of direct finite value-comparison certificates. -/
structure PositiveWindowArtanhEulerGeometricValueAnchorCompiler : Type 2 where
  evaluate :
    (z : Q') -> (hz : (0 : Q') < z) ->
    (hzb : Q'.abs z <= CRealLog.recipOdd 1) ->
    PositiveWindowArtanhEulerGeometricValueAnchorCertificate z hz hzb

namespace PositiveWindowArtanhEulerGeometricValueAnchorCertificate

/-- A direct finite value comparison compiles to the cleared
geometric-defect comparison by multiplying by the positive denominator. -/
def toGeometricAnchor
    {z : Q'} {hz : (0 : Q') < z}
    {hzb : Q'.abs z <= CRealLog.recipOdd 1}
    (certificate :
      PositiveWindowArtanhEulerGeometricValueAnchorCertificate z hz hzb) :
    PositiveWindowArtanhEulerGeometricAnchorCertificate z hz hzb where
  anchorComparison epsilon hepsilon := by
    let stage : Nat := positiveArtanhEulerAnchorStage epsilon
    let inner : Nat := positiveArtanhEulerAnchorPivot z epsilon
    let degree : Nat := positiveArtanhGeometricAnchorDegree epsilon
    let denominator : Q' := (1 : Q') + z
    let difference : Q' :=
      ExpNeg.partialSum (positiveArtanhExponent z stage) inner +
        -(positiveArtanhGeometricApprox z degree)
    have hvalue : Q'.abs difference <=
        positiveArtanhGeometricComparisonTolerance epsilon :=
      certificate.anchorValueComparison epsilon hepsilon
    have hdenominator : (0 : Q') <= denominator :=
      Q'.zero_le_add 1 z (by decide) (Q'.le_of_lt hz)
    have heqv := clearedDefect_sub_geometricDefect_eqv
      z stage inner degree
    have habsEqv :
        (Q'.abs
          (positiveArtanhEulerClearedDefect z stage inner +
            -(positiveArtanhGeometricDefect z degree))).eqv
          (Q'.abs (denominator * difference)) :=
      Q'.abs_eqv_congr heqv
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv habsEqv) ?_
    refine Q'.le_trans' _ _ _
      (ExpNeg.abs_mul_le denominator difference) ?_
    rw [ExpNeg.abs_of_nonneg hdenominator]
    refine Q'.le_trans' _
      (denominator * positiveArtanhGeometricComparisonTolerance epsilon) _
      (Q'.mul_le_mul_of_nonneg_left _ _ denominator
        hvalue hdenominator) ?_
    exact Q'.le_of_eqv
      (Q'.mul_comm_eqv denominator
        (positiveArtanhGeometricComparisonTolerance epsilon))

end PositiveWindowArtanhEulerGeometricValueAnchorCertificate

/-- Uniform direct value certificates compile to uniform geometric-defect
certificates. -/
def positiveWindowArtanhEulerGeometricAnchorCompilerOfValueAnchor
    (compiler : PositiveWindowArtanhEulerGeometricValueAnchorCompiler) :
    PositiveWindowArtanhEulerGeometricAnchorCompiler where
  evaluate z hz hzb := (compiler.evaluate z hz hzb).toGeometricAnchor

namespace PositiveWindowArtanhEulerGeometricAnchorCertificate

/-- The finite Euler-versus-polynomial comparison compiles to the previous
single-anchor defect certificate.  The polynomial residual consumes one half
of the budget; the finite comparison consumes the other half after multiplying
by the positive denominator. -/
def toSingleAnchor
    {z : Q'} {hz : (0 : Q') < z}
    {hzb : Q'.abs z <= CRealLog.recipOdd 1}
    (certificate :
      PositiveWindowArtanhEulerGeometricAnchorCertificate z hz hzb) :
    PositiveWindowArtanhEulerSingleAnchorCertificate z hz hzb where
  anchorDefect epsilon hepsilon := by
    let tolerance : Q' :=
      positiveArtanhGeometricComparisonTolerance epsilon
    let fullTolerance : Q' :=
      positiveArtanhAnchorInnerTolerance epsilon
    let denominator : Q' := (1 : Q') + z
    let eulerDefect : Q' :=
      positiveArtanhEulerClearedDefect z
        (positiveArtanhEulerAnchorStage epsilon)
        (positiveArtanhEulerAnchorPivot z epsilon)
    let geometricDefect : Q' :=
      positiveArtanhGeometricDefect z
        (positiveArtanhGeometricAnchorDegree epsilon)
    have htolerance : (0 : Q') <= tolerance :=
      Q'.le_of_lt
        (positiveArtanhGeometricComparisonTolerance_pos epsilon hepsilon)
    have hdenominator : (1 : Q') <= denominator :=
      Q'.add_le_self_of_nonneg 1 z (Q'.le_of_lt hz)
    have hgeometric : Q'.abs geometricDefect <= tolerance :=
      positiveArtanhGeometricAnchorDefect_abs_le
        z hz hzb epsilon hepsilon
    have hcomparison :
        Q'.abs (eulerDefect + -geometricDefect) <=
          tolerance * denominator :=
      certificate.anchorComparison epsilon hepsilon
    have htriangle : Q'.abs eulerDefect <=
        Q'.abs geometricDefect +
          Q'.abs (eulerDefect + -geometricDefect) :=
      Q'.abs_le_abs_add_abs_sub eulerDefect geometricDefect
    have htolerance_le_scaled : tolerance <= tolerance * denominator := by
      have hmul : tolerance * (1 : Q') <= tolerance * denominator :=
        Q'.mul_le_mul_of_nonneg_left 1 denominator tolerance
          hdenominator htolerance
      exact Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.mul_one_eqv tolerance)) hmul
    have hsum :
        Q'.abs geometricDefect +
            Q'.abs (eulerDefect + -geometricDefect) <=
          (tolerance * denominator) +
            (tolerance * denominator) :=
      Q'.le_trans' _ _ _
        (Q'.add_le_add hgeometric hcomparison)
        (Q'.add_le_add_right tolerance
          (tolerance * denominator) (tolerance * denominator)
          htolerance_le_scaled)
    have hdoubleTolerance : (tolerance + tolerance).eqv fullTolerance := by
      change
        ((HalfPow.half * fullTolerance) +
          (HalfPow.half * fullTolerance)).eqv fullTolerance
      exact ExpNeg.two_halves fullTolerance
    have hdoubleScaled :
        ((tolerance * denominator) +
          (tolerance * denominator)).eqv
            (fullTolerance * denominator) := by
      refine Q'.eqv_trans _ ((tolerance + tolerance) * denominator) _
        (Q'.eqv_symm
          (Q'.add_mul_eqv tolerance tolerance denominator)) ?_
      exact Q'.mul_eqv_congr_right _ _ denominator hdoubleTolerance
    exact Q'.le_trans' _ _ _ htriangle
      (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hdoubleScaled))

end PositiveWindowArtanhEulerGeometricAnchorCertificate

/-- Uniform geometric-anchor certificates compile to uniform single-anchor
certificates. -/
def positiveWindowArtanhEulerSingleAnchorCompilerOfGeometricAnchor
    (compiler : PositiveWindowArtanhEulerGeometricAnchorCompiler) :
    PositiveWindowArtanhEulerSingleAnchorCompiler where
  evaluate z hz hzb := (compiler.evaluate z hz hzb).toSingleAnchor

/-- Uniform geometric-anchor certificates therefore compile all the way to
the positive-artanh Euler evaluation interface. -/
def positiveWindowArtanhEulerCompilerOfGeometricAnchor
    (compiler : PositiveWindowArtanhEulerGeometricAnchorCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfSingleAnchor
    (positiveWindowArtanhEulerSingleAnchorCompilerOfGeometricAnchor compiler)

/-- Uniform direct finite value comparisons compile all the way to the
positive-artanh Euler evaluation interface. -/
def positiveWindowArtanhEulerCompilerOfGeometricValueAnchor
    (compiler : PositiveWindowArtanhEulerGeometricValueAnchorCompiler) :
    PositiveWindowArtanhEulerCompiler :=
  positiveWindowArtanhEulerCompilerOfGeometricAnchor
    (positiveWindowArtanhEulerGeometricAnchorCompilerOfValueAnchor compiler)

end YMGap.Constructive.CRealArtanhEulerGeometricAnchor

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Constructive.CRealArtanhEulerGeometricAnchor.positiveArtanhGeometricDefect_eqv
#print axioms
  YMGap.Constructive.CRealArtanhEulerGeometricAnchor.positiveArtanhGeometricAnchorDefect_abs_le
#print axioms
  YMGap.Constructive.CRealArtanhEulerGeometricAnchor.clearedDefect_sub_geometricDefect_eqv
#print axioms
  YMGap.Constructive.CRealArtanhEulerGeometricAnchor.PositiveWindowArtanhEulerGeometricValueAnchorCertificate.toGeometricAnchor
#print axioms
  YMGap.Constructive.CRealArtanhEulerGeometricAnchor.PositiveWindowArtanhEulerGeometricAnchorCertificate.toSingleAnchor
#print axioms
  YMGap.Constructive.CRealArtanhEulerGeometricAnchor.positiveWindowArtanhEulerCompilerOfGeometricValueAnchor
