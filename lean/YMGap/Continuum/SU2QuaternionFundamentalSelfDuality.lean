/-
# Exact self-duality of the fundamental SU(2) coefficient

The fundamental representation of `SU(2)` is pseudoreal.  At the literal
quaternion-polynomial level this identifies a forward coefficient with a
reverse coefficient whose two external indices are complemented and
transposed.  The off-diagonal coefficients acquire the epsilon-tensor sign.

This leaf freezes that sign convention before arbitrary oriented link words
are normalized to the balanced projector interfaces.  It also computes the
two same-orientation second moments, including a negative entry which would
be lost by an unsigned identification.

No face family, global Boolean-index network, bounded labelling, trajectory,
or weighted SOS polynomial is materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur

namespace YMGap.Continuum.SU2QuaternionFundamentalSelfDuality

open YMGap.Constructive
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur

/-! ## 1. Literal epsilon action -/

/-- Componentwise negation in the honest complex-polynomial carrier. -/
def complexRatPolyNeg (value : ComplexRatPoly) : ComplexRatPoly :=
  (polyNeg value.1, polyNeg value.2)

/-- The epsilon-tensor action is positive on diagonal matrix coefficients and
negative on off-diagonal coefficients. -/
def fundamentalDualityAction
    (row column : Bool) (value : ComplexRatPoly) : ComplexRatPoly :=
  if row = column then value else complexRatPolyNeg value

/-- The corresponding exact rational sign. -/
def fundamentalDualitySign (row column : Bool) : Q' :=
  if row = column then 1 else -1

private theorem q_neg_neg_eq (value : Q') : -(-value) = value := by
  rcases value with ⟨numerator, denominatorPredecessor⟩
  change Q'.mk (-(-numerator)) denominatorPredecessor =
    Q'.mk numerator denominatorPredecessor
  rw [Int.neg_neg]

private theorem polyNeg_polyNeg (polynomial : RatPoly) :
    polyNeg (polyNeg polynomial) = polynomial := by
  induction polynomial with
  | nil => rfl
  | cons term polynomial ih =>
      rcases term with ⟨monomial, coefficient⟩
      change
        (monomial, -(-coefficient)) :: polyNeg (polyNeg polynomial) =
          (monomial, coefficient) :: polynomial
      rw [q_neg_neg_eq, ih]

theorem complexRatPolyNeg_neg (value : ComplexRatPoly) :
    complexRatPolyNeg (complexRatPolyNeg value) = value := by
  rcases value with ⟨realPart, imaginaryPart⟩
  simp [complexRatPolyNeg, polyNeg_polyNeg]

/-- **Forward-to-reverse fundamental self-duality.**  This is raw equality of
the duplicate-preserving polynomial representatives, not merely equality
after evaluation or Haar integration. -/
theorem forwardFundamentalCoefficient_eq_dual_reverse
    (block : Nat) (row column : Bool) :
    forwardFundamentalCoefficient block row column =
      fundamentalDualityAction row column
        (reverseFundamentalCoefficient block (!column) (!row)) := by
  cases row <;> cases column <;>
    simp [fundamentalDualityAction, complexRatPolyNeg,
      reverseFundamentalCoefficient, complexRatPolyConj,
      forwardFundamentalCoefficient, fundamentalMatrixCoefficient,
      fundamentalLinkQuaternion, variablesAt, polyNeg_polyNeg]

/-- **Reverse-to-forward fundamental self-duality.**  The same epsilon sign
appears in the converse direction. -/
theorem reverseFundamentalCoefficient_eq_dual_forward
    (block : Nat) (row column : Bool) :
    reverseFundamentalCoefficient block row column =
      fundamentalDualityAction row column
        (forwardFundamentalCoefficient block (!column) (!row)) := by
  cases row <;> cases column <;>
    simp [fundamentalDualityAction, complexRatPolyNeg,
      reverseFundamentalCoefficient, complexRatPolyConj,
      forwardFundamentalCoefficient, fundamentalMatrixCoefficient,
      fundamentalLinkQuaternion, variablesAt, polyNeg_polyNeg]

/-! ## 2. An orientation-complete occurrence carrier -/

/-- The two orientations of a fundamental coefficient on one link. -/
inductive FundamentalLinkOrientation
  | forward
  | reverse
deriving DecidableEq, Repr

/-- Reverse one link orientation. -/
def FundamentalLinkOrientation.opposite :
    FundamentalLinkOrientation → FundamentalLinkOrientation
  | .forward => .reverse
  | .reverse => .forward

theorem FundamentalLinkOrientation.opposite_opposite
    (orientation : FundamentalLinkOrientation) :
    orientation.opposite.opposite = orientation := by
  cases orientation <;> rfl

/-- Select the literal coefficient corresponding to an orientation. -/
def orientedFundamentalCoefficient
    (orientation : FundamentalLinkOrientation)
    (block : Nat) (row column : Bool) : ComplexRatPoly :=
  match orientation with
  | .forward => forwardFundamentalCoefficient block row column
  | .reverse => reverseFundamentalCoefficient block row column

/-- One ordered oriented fundamental occurrence at a link. -/
structure FundamentalOccurrence where
  orientation : FundamentalLinkOrientation
  row : Bool
  column : Bool
deriving DecidableEq, Repr

/-- Epsilon duality reverses orientation and complements the transposed
external indices. -/
def FundamentalOccurrence.dual
    (occurrence : FundamentalOccurrence) : FundamentalOccurrence :=
  ⟨occurrence.orientation.opposite, !occurrence.column, !occurrence.row⟩

theorem FundamentalOccurrence.dual_dual
    (occurrence : FundamentalOccurrence) :
    occurrence.dual.dual = occurrence := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation <;> cases row <;> cases column <;> rfl

/-- The literal polynomial carried by one occurrence. -/
def fundamentalOccurrenceCoefficient
    (block : Nat) (occurrence : FundamentalOccurrence) : ComplexRatPoly :=
  orientedFundamentalCoefficient occurrence.orientation block
    occurrence.row occurrence.column

/-- Orientation-complete raw self-duality for a packaged occurrence. -/
theorem fundamentalOccurrenceCoefficient_eq_dual
    (block : Nat) (occurrence : FundamentalOccurrence) :
    fundamentalOccurrenceCoefficient block occurrence =
      fundamentalDualityAction occurrence.row occurrence.column
        (fundamentalOccurrenceCoefficient block occurrence.dual) := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation
  · exact forwardFundamentalCoefficient_eq_dual_reverse block row column
  · exact reverseFundamentalCoefficient_eq_dual_forward block row column

/-! ## 3. Same-orientation Schur kernel -/

/-- The signed epsilon pairing for two coefficients of the same orientation.
The indices of the first coefficient must be the componentwise complements of
the second coefficient's indices. -/
def sameOrientationFundamentalSchurDelta
    (firstRow firstColumn secondRow secondColumn : Bool) : RationalComplex :=
  if firstRow = !secondRow ∧ firstColumn = !secondColumn then
    (fundamentalDualitySign secondRow secondColumn * Q'.invSucc 1, 0)
  else
    (0, 0)

/-- Two forward-oriented fundamental coefficients contract through the
signed invariant epsilon tensor. -/
theorem oneLink_twoForward_fundamental_schur
    (firstRow firstColumn secondRow secondColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (complexRatPolyMul
          (forwardFundamentalCoefficient 0 firstRow firstColumn)
          (forwardFundamentalCoefficient 0 secondRow secondColumn)))
      (sameOrientationFundamentalSchurDelta
        firstRow firstColumn secondRow secondColumn) := by
  cases firstRow <;> cases firstColumn <;>
    cases secondRow <;> cases secondColumn <;>
      constructor <;> decide

/-- Two reverse-oriented fundamental coefficients obey the same signed
epsilon contraction. -/
theorem oneLink_twoReverse_fundamental_schur
    (firstRow firstColumn secondRow secondColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (complexRatPolyMul
          (reverseFundamentalCoefficient 0 firstRow firstColumn)
          (reverseFundamentalCoefficient 0 secondRow secondColumn)))
      (sameOrientationFundamentalSchurDelta
        firstRow firstColumn secondRow secondColumn) := by
  cases firstRow <;> cases firstColumn <;>
    cases secondRow <;> cases secondColumn <;>
      constructor <;> decide

/-! ## 4. Sign regressions -/

/-- Diagonal self-dual pairing: `integral F[0,0] F[1,1] = 1/2`. -/
theorem oneLink_twoForward_diagonal_selfDual :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (complexRatPolyMul
          (forwardFundamentalCoefficient 0 false false)
          (forwardFundamentalCoefficient 0 true true)))
      (Q'.invSucc 1, 0) := by
  constructor <;> decide

/-- Off-diagonal epsilon pairing:
`integral F[0,1] F[1,0] = -1/2`. -/
theorem oneLink_twoForward_offDiagonal_selfDual :
    RationalComplexEqv
      (finiteProductHaarComplex 1
        (complexRatPolyMul
          (forwardFundamentalCoefficient 0 false true)
          (forwardFundamentalCoefficient 0 true false)))
      (-Q'.invSucc 1, 0) := by
  constructor <;> decide

#print axioms complexRatPolyNeg_neg
#print axioms forwardFundamentalCoefficient_eq_dual_reverse
#print axioms reverseFundamentalCoefficient_eq_dual_forward
#print axioms FundamentalOccurrence.dual_dual
#print axioms fundamentalOccurrenceCoefficient_eq_dual
#print axioms oneLink_twoForward_fundamental_schur
#print axioms oneLink_twoReverse_fundamental_schur
#print axioms oneLink_twoForward_diagonal_selfDual
#print axioms oneLink_twoForward_offDiagonal_selfDual

end YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
