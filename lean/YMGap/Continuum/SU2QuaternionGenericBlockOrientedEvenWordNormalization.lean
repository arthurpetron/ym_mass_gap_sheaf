/-
# Orientation-complete normalization of four- and six-valent fundamental words

Every fundamental `SU(2)` coefficient is pseudoreal.  This leaf uses the exact
epsilon self-duality map to normalize an arbitrary ordered orientation word to
the balanced local projector conventions already proved at valence four and
six.  A reversed occurrence is not merely relabelled: its external indices are
complemented and transposed, and every off-diagonal dualization contributes a
minus sign.

The four-valent normal form follows the paired partial-Haar carrier

    (F1 * R1) * (F2 * R2),

so its projector arguments occur in the order `F1,F2,R1,R2`.  The six-valent
normal form is the canonical left comb `F1*F2*F3*R1*R2*R3`.  Polynomial
association or factor exchange is never asserted as raw list equality.

No global assignment family, bounded labelling family, trajectory, or full
trace network is materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
import YMGap.Continuum.SU2QuaternionGenericBlockPartialFourValentHaarProjector
import YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjector

namespace YMGap.Continuum.SU2QuaternionGenericBlockOrientedEvenWordNormalization

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
open YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
open YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector
open YMGap.Continuum.SU2QuaternionSixValentPairingGram
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFourValentHaarProjector
open YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjector

/-! ## 1. Constructive epsilon parity and positional normalization -/

/-- Constructive exclusive-or for epsilon-sign accumulation. -/
def signXor : Bool → Bool → Bool
  | false, value => value
  | true, false => true
  | true, true => false

/-- An off-diagonal fundamental coefficient carries the negative epsilon
sign when it is replaced by its dual. -/
def fundamentalEpsilonNegative (row column : Bool) : Bool :=
  signXor row column

end YMGap.Continuum.SU2QuaternionGenericBlockOrientedEvenWordNormalization

namespace YMGap.Continuum.SU2QuaternionFundamentalSelfDuality.FundamentalOccurrence

/-- Force one occurrence into the forward convention.  A reverse occurrence
is replaced by its exact epsilon dual, hence its row and column become the
complemented transpose `(!column,!row)`. -/
def toForward
    (occurrence : FundamentalOccurrence) : FundamentalOccurrence :=
  match occurrence.orientation with
  | .forward => occurrence
  | .reverse => occurrence.dual

/-- Force one occurrence into the reverse convention, with the same exact
complemented-transpose rule on a forward input. -/
def toReverse
    (occurrence : FundamentalOccurrence) : FundamentalOccurrence :=
  match occurrence.orientation with
  | .forward => occurrence.dual
  | .reverse => occurrence

end YMGap.Continuum.SU2QuaternionFundamentalSelfDuality.FundamentalOccurrence

namespace YMGap.Continuum.SU2QuaternionGenericBlockOrientedEvenWordNormalization

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
open YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport
open YMGap.Continuum.SU2QuaternionFundamentalSelfDuality
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
open YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector
open YMGap.Continuum.SU2QuaternionSixValentPairingGram
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFourValentHaarProjector
open YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjector

/-- The sign bit introduced while forcing an occurrence forward. -/
def forwardNormalizationNegative
    (occurrence : FundamentalOccurrence) : Bool :=
  match occurrence.orientation with
  | .forward => false
  | .reverse => fundamentalEpsilonNegative occurrence.row occurrence.column

/-- The sign bit introduced while forcing an occurrence reverse. -/
def reverseNormalizationNegative
    (occurrence : FundamentalOccurrence) : Bool :=
  match occurrence.orientation with
  | .forward => fundamentalEpsilonNegative occurrence.row occurrence.column
  | .reverse => false

/-- Apply one accumulated sign to a complex polynomial. -/
def signedComplexRatPoly
    (negative : Bool) (value : ComplexRatPoly) : ComplexRatPoly :=
  if negative then complexRatPolyNeg value else value

/-- Apply one accumulated sign to a rational-complex value. -/
def signedRationalComplex
    (negative : Bool) (value : RationalComplex) : RationalComplex :=
  if negative then (-value.1, -value.2) else value

/-! ## 2. Raw sign algebra without polynomial reordering -/

private theorem q_neg_mul_eq (left right : Q') :
    (-left) * right = -(left * right) := by
  rcases left with ⟨leftNumerator, leftDenominatorPredecessor⟩
  rcases right with ⟨rightNumerator, rightDenominatorPredecessor⟩
  change
    Q'.mk ((-leftNumerator) * rightNumerator)
        ((leftDenominatorPredecessor + 1) *
          (rightDenominatorPredecessor + 1) - 1) =
      Q'.mk (-(leftNumerator * rightNumerator))
        ((leftDenominatorPredecessor + 1) *
          (rightDenominatorPredecessor + 1) - 1)
  rw [Int.neg_mul]

private theorem q_mul_neg_eq (left right : Q') :
    left * (-right) = -(left * right) := by
  rcases left with ⟨leftNumerator, leftDenominatorPredecessor⟩
  rcases right with ⟨rightNumerator, rightDenominatorPredecessor⟩
  change
    Q'.mk (leftNumerator * (-rightNumerator))
        ((leftDenominatorPredecessor + 1) *
          (rightDenominatorPredecessor + 1) - 1) =
      Q'.mk (-(leftNumerator * rightNumerator))
        ((leftDenominatorPredecessor + 1) *
          (rightDenominatorPredecessor + 1) - 1)
  rw [Int.mul_neg]

private theorem q_neg_neg_eq (value : Q') : -(-value) = value := by
  rcases value with ⟨numerator, denominatorPredecessor⟩
  change Q'.mk (-(-numerator)) denominatorPredecessor =
    Q'.mk numerator denominatorPredecessor
  rw [Int.neg_neg]

private theorem polyNeg_add_raw (left right : RatPoly) :
    polyNeg (polyAdd left right) =
      polyAdd (polyNeg left) (polyNeg right) := by
  simp [polyNeg, polyAdd, List.map_append]

private theorem polyNeg_neg_raw : ∀ polynomial : RatPoly,
    polyNeg (polyNeg polynomial) = polynomial
  | [] => rfl
  | (monomial, coefficient) :: polynomial => by
      change
        (monomial, -(-coefficient)) :: polyNeg (polyNeg polynomial) =
          (monomial, coefficient) :: polynomial
      rw [q_neg_neg_eq, polyNeg_neg_raw polynomial]

private theorem polyMul_neg_left_row_raw
    (monomial : List Nat) (coefficient : Q') : ∀ right : RatPoly,
    right.map (fun term =>
        (monoMul monomial term.1, (-coefficient) * term.2)) =
      polyNeg (right.map (fun term =>
        (monoMul monomial term.1, coefficient * term.2)))
  | [] => rfl
  | (rightMonomial, rightCoefficient) :: right => by
      change
        (monoMul monomial rightMonomial,
            (-coefficient) * rightCoefficient) ::
          right.map (fun term =>
            (monoMul monomial term.1, (-coefficient) * term.2)) =
        (monoMul monomial rightMonomial,
            -(coefficient * rightCoefficient)) ::
          polyNeg (right.map (fun term =>
            (monoMul monomial term.1, coefficient * term.2)))
      rw [q_neg_mul_eq,
        polyMul_neg_left_row_raw monomial coefficient right]

private theorem polyMul_neg_left_raw (left right : RatPoly) :
    polyMul (polyNeg left) right = polyNeg (polyMul left right) := by
  induction left with
  | nil => rfl
  | cons term polynomial ih =>
      rcases term with ⟨monomial, coefficient⟩
      change
        polyAdd
          (right.map (fun term =>
            (monoMul monomial term.1, (-coefficient) * term.2)))
          (polyMul (polyNeg polynomial) right) =
        polyNeg
          (polyAdd
            (right.map (fun term =>
              (monoMul monomial term.1, coefficient * term.2)))
            (polyMul polynomial right))
      rw [polyNeg_add_raw, polyMul_neg_left_row_raw, ih]

private theorem polyMul_neg_right_row_raw
    (monomial : List Nat) (coefficient : Q') : ∀ right : RatPoly,
    (polyNeg right).map (fun term =>
        (monoMul monomial term.1, coefficient * term.2)) =
      polyNeg (right.map (fun term =>
        (monoMul monomial term.1, coefficient * term.2)))
  | [] => rfl
  | (rightMonomial, rightCoefficient) :: right => by
      change
        (monoMul monomial rightMonomial,
            coefficient * (-rightCoefficient)) ::
          (polyNeg right).map (fun term =>
            (monoMul monomial term.1, coefficient * term.2)) =
        (monoMul monomial rightMonomial,
            -(coefficient * rightCoefficient)) ::
          polyNeg (right.map (fun term =>
            (monoMul monomial term.1, coefficient * term.2)))
      rw [q_mul_neg_eq,
        polyMul_neg_right_row_raw monomial coefficient right]

private theorem polyMul_neg_right_raw (left right : RatPoly) :
    polyMul left (polyNeg right) = polyNeg (polyMul left right) := by
  induction left with
  | nil => rfl
  | cons term polynomial ih =>
      rcases term with ⟨monomial, coefficient⟩
      change
        polyAdd
          ((polyNeg right).map (fun term =>
            (monoMul monomial term.1, coefficient * term.2)))
          (polyMul polynomial (polyNeg right)) =
        polyNeg
          (polyAdd
            (right.map (fun term =>
              (monoMul monomial term.1, coefficient * term.2)))
            (polyMul polynomial right))
      rw [polyNeg_add_raw, polyMul_neg_right_row_raw, ih]

/-- Negating the left complex factor negates the literal product without
changing its term order or association. -/
theorem complexRatPolyMul_neg_left_raw
    (left right : ComplexRatPoly) :
    complexRatPolyMul (complexRatPolyNeg left) right =
      complexRatPolyNeg (complexRatPolyMul left right) := by
  rcases left with ⟨leftReal, leftImaginary⟩
  rcases right with ⟨rightReal, rightImaginary⟩
  simp [complexRatPolyNeg, complexRatPolyMul, polyNeg_add_raw,
    polyNeg_neg_raw, polyMul_neg_left_raw]

/-- Negating the right complex factor likewise negates the literal product
without a commutativity claim. -/
theorem complexRatPolyMul_neg_right_raw
    (left right : ComplexRatPoly) :
    complexRatPolyMul left (complexRatPolyNeg right) =
      complexRatPolyNeg (complexRatPolyMul left right) := by
  rcases left with ⟨leftReal, leftImaginary⟩
  rcases right with ⟨rightReal, rightImaginary⟩
  simp [complexRatPolyNeg, complexRatPolyMul, polyNeg_add_raw,
    polyNeg_neg_raw, polyMul_neg_right_raw]

/-- Multiplication accumulates two explicit epsilon signs by exclusive-or,
as raw equality with the original factor order and association preserved. -/
theorem signedComplexRatPoly_mul
    (leftNegative rightNegative : Bool)
    (left right : ComplexRatPoly) :
    complexRatPolyMul
        (signedComplexRatPoly leftNegative left)
        (signedComplexRatPoly rightNegative right) =
      signedComplexRatPoly (signXor leftNegative rightNegative)
        (complexRatPolyMul left right) := by
  cases leftNegative <;> cases rightNegative
  · rfl
  · change
      complexRatPolyMul left (complexRatPolyNeg right) =
        complexRatPolyNeg (complexRatPolyMul left right)
    exact complexRatPolyMul_neg_right_raw left right
  · change
      complexRatPolyMul (complexRatPolyNeg left) right =
        complexRatPolyNeg (complexRatPolyMul left right)
    exact complexRatPolyMul_neg_left_raw left right
  · change
      complexRatPolyMul (complexRatPolyNeg left)
          (complexRatPolyNeg right) =
        complexRatPolyMul left right
    rw [complexRatPolyMul_neg_left_raw,
      complexRatPolyMul_neg_right_raw, complexRatPolyNeg_neg]

/-- Componentwise rational-complex equivalence is preserved by a fixed sign. -/
theorem signedRationalComplex_congr
    (negative : Bool) {left right : RationalComplex}
    (h : RationalComplexEqv left right) :
    RationalComplexEqv
      (signedRationalComplex negative left)
      (signedRationalComplex negative right) := by
  cases negative
  · exact h
  · exact ⟨Q'.neg_eqv_congr _ _ h.1, Q'.neg_eqv_congr _ _ h.2⟩

private theorem fundamentalDualityAction_eq_signed
    (row column : Bool) (value : ComplexRatPoly) :
    fundamentalDualityAction row column value =
      signedComplexRatPoly (fundamentalEpsilonNegative row column) value := by
  cases row <;> cases column <;>
    rfl

/-- A coefficient is its forced-forward coefficient with exactly the
epsilon sign of the dualization. -/
theorem fundamentalOccurrenceCoefficient_eq_signed_toForward
    (block : Nat) (occurrence : FundamentalOccurrence) :
    fundamentalOccurrenceCoefficient block occurrence =
      signedComplexRatPoly (forwardNormalizationNegative occurrence)
        (fundamentalOccurrenceCoefficient block occurrence.toForward) := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation
  · rfl
  · rw [fundamentalOccurrenceCoefficient_eq_dual]
    simpa only [FundamentalOccurrence.toForward,
      forwardNormalizationNegative] using
      (fundamentalDualityAction_eq_signed row column
        (fundamentalOccurrenceCoefficient block
          (⟨.reverse, row, column⟩ : FundamentalOccurrence).dual))

/-- A coefficient is its forced-reverse coefficient with exactly the
epsilon sign of the dualization. -/
theorem fundamentalOccurrenceCoefficient_eq_signed_toReverse
    (block : Nat) (occurrence : FundamentalOccurrence) :
    fundamentalOccurrenceCoefficient block occurrence =
      signedComplexRatPoly (reverseNormalizationNegative occurrence)
        (fundamentalOccurrenceCoefficient block occurrence.toReverse) := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation
  · rw [fundamentalOccurrenceCoefficient_eq_dual]
    simpa only [FundamentalOccurrence.toReverse,
      reverseNormalizationNegative] using
      (fundamentalDualityAction_eq_signed row column
        (fundamentalOccurrenceCoefficient block
          (⟨.forward, row, column⟩ : FundamentalOccurrence).dual))
  · rfl

/-! ## 3. Literal words, balanced normal forms, and their kernels -/

/-- The literal paired four-occurrence word.  Its association agrees with the
existing arbitrary-block partial four-valent theorem after positional
normalization to `F,R,F,R`. -/
def orientedFourFundamentalWord
    (block : Nat)
    (first second third fourth : FundamentalOccurrence) : ComplexRatPoly :=
  complexRatPolyMul
    (complexRatPolyMul
      (fundamentalOccurrenceCoefficient block first)
      (fundamentalOccurrenceCoefficient block second))
    (complexRatPolyMul
      (fundamentalOccurrenceCoefficient block third)
      (fundamentalOccurrenceCoefficient block fourth))

/-- Epsilon parity of the paired four-occurrence normalization. -/
def orientedFourNormalizationNegative
    (first second third fourth : FundamentalOccurrence) : Bool :=
  signXor
    (signXor (forwardNormalizationNegative first)
      (reverseNormalizationNegative second))
    (signXor (forwardNormalizationNegative third)
      (reverseNormalizationNegative fourth))

/-- The paired balanced four-valent polynomial produced by normalization. -/
def normalizedFourFundamentalWord
    (block : Nat)
    (first second third fourth : FundamentalOccurrence) : ComplexRatPoly :=
  pairedTwoForwardTwoReverseFundamentalTerm block
    first.toForward.row first.toForward.column
    third.toForward.row third.toForward.column
    second.toReverse.row second.toReverse.column
    fourth.toReverse.row fourth.toReverse.column

/-- The signed inverse-Gram projector selected by an arbitrary four-word. -/
def orientedFourNormalizedHaarProjector
    (first second third fourth : FundamentalOccurrence) : RationalComplex :=
  signedRationalComplex
    (orientedFourNormalizationNegative first second third fourth)
    (orientedFourFundamentalHaarProjector
      first.toForward.row first.toForward.column
      third.toForward.row third.toForward.column
      second.toReverse.row second.toReverse.column
      fourth.toReverse.row fourth.toReverse.column)

/-- Literal left-associated word of six arbitrary oriented occurrences. -/
def orientedSixFundamentalWord
    (block : Nat)
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    ComplexRatPoly :=
  complexRatPolyMulSixLeft
    (fundamentalOccurrenceCoefficient block first)
    (fundamentalOccurrenceCoefficient block second)
    (fundamentalOccurrenceCoefficient block third)
    (fundamentalOccurrenceCoefficient block fourth)
    (fundamentalOccurrenceCoefficient block fifth)
    (fundamentalOccurrenceCoefficient block sixth)

/-- Epsilon parity of the canonical `F,F,F,R,R,R` normalization. -/
def orientedSixNormalizationNegative
    (first second third fourth fifth sixth : FundamentalOccurrence) : Bool :=
  signXor
    (signXor
      (signXor
        (signXor
          (signXor (forwardNormalizationNegative first)
            (forwardNormalizationNegative second))
          (forwardNormalizationNegative third))
        (reverseNormalizationNegative fourth))
      (reverseNormalizationNegative fifth))
    (reverseNormalizationNegative sixth)

/-- The balanced six-valent polynomial produced by normalization. -/
def normalizedSixFundamentalWord
    (block : Nat)
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    ComplexRatPoly :=
  threeForwardThreeReverseFundamentalTerm block
    first.toForward.row first.toForward.column
    second.toForward.row second.toForward.column
    third.toForward.row third.toForward.column
    fourth.toReverse.row fourth.toReverse.column
    fifth.toReverse.row fifth.toReverse.column
    sixth.toReverse.row sixth.toReverse.column

/-- The signed rank-five projector selected by an arbitrary six-word. -/
def orientedSixNormalizedHaarProjector
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    RationalComplex :=
  signedRationalComplex
    (orientedSixNormalizationNegative first second third fourth fifth sixth)
    (orientedSixFundamentalHaarProjector
      first.toForward.row first.toForward.column
      second.toForward.row second.toForward.column
      third.toForward.row third.toForward.column
      fourth.toReverse.row fourth.toReverse.column
      fifth.toReverse.row fifth.toReverse.column
      sixth.toReverse.row sixth.toReverse.column)

/-! ## 4. Exact raw normalization -/

theorem fundamentalOccurrenceCoefficient_toForward
    (block : Nat) (occurrence : FundamentalOccurrence) :
    fundamentalOccurrenceCoefficient block occurrence.toForward =
      forwardFundamentalCoefficient block
        occurrence.toForward.row occurrence.toForward.column := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation <;> rfl

theorem fundamentalOccurrenceCoefficient_toReverse
    (block : Nat) (occurrence : FundamentalOccurrence) :
    fundamentalOccurrenceCoefficient block occurrence.toReverse =
      reverseFundamentalCoefficient block
        occurrence.toReverse.row occurrence.toReverse.column := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation <;> rfl

/-- Every paired four-word is raw-equal to one signed balanced word.  This
uses only sign bubbling; neither factors nor polynomial lists are reordered. -/
theorem orientedFourFundamentalWord_eq_signed_normalized
    (block : Nat)
    (first second third fourth : FundamentalOccurrence) :
    orientedFourFundamentalWord block first second third fourth =
      signedComplexRatPoly
        (orientedFourNormalizationNegative first second third fourth)
        (normalizedFourFundamentalWord block first second third fourth) := by
  unfold orientedFourFundamentalWord orientedFourNormalizationNegative
  rw [fundamentalOccurrenceCoefficient_eq_signed_toForward block first,
    fundamentalOccurrenceCoefficient_eq_signed_toReverse block second,
    fundamentalOccurrenceCoefficient_eq_signed_toForward block third,
    fundamentalOccurrenceCoefficient_eq_signed_toReverse block fourth]
  rw [signedComplexRatPoly_mul, signedComplexRatPoly_mul,
    signedComplexRatPoly_mul]
  unfold normalizedFourFundamentalWord
    pairedTwoForwardTwoReverseFundamentalTerm
    orientedFundamentalLinkContraction
  rw [fundamentalOccurrenceCoefficient_toForward,
    fundamentalOccurrenceCoefficient_toReverse,
    fundamentalOccurrenceCoefficient_toForward,
    fundamentalOccurrenceCoefficient_toReverse]

/-- Every six-word is raw-equal to one signed canonical `F F F R R R` word,
again with its literal left-comb association preserved. -/
theorem orientedSixFundamentalWord_eq_signed_normalized
    (block : Nat)
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    orientedSixFundamentalWord block first second third fourth fifth sixth =
      signedComplexRatPoly
        (orientedSixNormalizationNegative first second third fourth fifth sixth)
        (normalizedSixFundamentalWord block first second third fourth fifth sixth) := by
  unfold orientedSixFundamentalWord orientedSixNormalizationNegative
  rw [fundamentalOccurrenceCoefficient_eq_signed_toForward block first,
    fundamentalOccurrenceCoefficient_eq_signed_toForward block second,
    fundamentalOccurrenceCoefficient_eq_signed_toForward block third,
    fundamentalOccurrenceCoefficient_eq_signed_toReverse block fourth,
    fundamentalOccurrenceCoefficient_eq_signed_toReverse block fifth,
    fundamentalOccurrenceCoefficient_eq_signed_toReverse block sixth]
  unfold complexRatPolyMulSixLeft
  rw [signedComplexRatPoly_mul, signedComplexRatPoly_mul,
    signedComplexRatPoly_mul, signedComplexRatPoly_mul,
    signedComplexRatPoly_mul]
  unfold normalizedSixFundamentalWord
    threeForwardThreeReverseFundamentalTerm complexRatPolyMulSixLeft
  rw [fundamentalOccurrenceCoefficient_toForward,
    fundamentalOccurrenceCoefficient_toForward,
    fundamentalOccurrenceCoefficient_toForward,
    fundamentalOccurrenceCoefficient_toReverse,
    fundamentalOccurrenceCoefficient_toReverse,
    fundamentalOccurrenceCoefficient_toReverse]

/-! ## 5. Partial-Haar sign transport -/

private theorem q_add_congr_local {a a' b b' : Q'}
    (ha : a.eqv a') (hb : b.eqv b') :
    (a + b).eqv (a' + b') :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right a a' b ha)
    (Q'.add_eqv_congr_left a' b b' hb)

private theorem blockIntegratedCoefficientSum_neg_local
    (block : Nat) : ∀ polynomial : RatPoly,
    (blockIntegratedCoefficientSum block (polyNeg polynomial)).eqv
      (-(blockIntegratedCoefficientSum block polynomial))
  | [] => by
      change (0 : Q').eqv (-0)
      decide
  | term :: tail => by
      change
        (((-term.2) * quaternionBlockMoment block term.1) +
          blockIntegratedCoefficientSum block (polyNeg tail)).eqv
        (-(term.2 * quaternionBlockMoment block term.1 +
          blockIntegratedCoefficientSum block tail))
      exact Q'.eqv_trans _
        (-(term.2 * quaternionBlockMoment block term.1) +
          -(blockIntegratedCoefficientSum block tail)) _
        (q_add_congr_local
          (Q'.neg_mul_eqv term.2 (quaternionBlockMoment block term.1))
          (blockIntegratedCoefficientSum_neg_local block tail))
        (Q'.eqv_symm
          (Q'.neg_add_eqv
            (term.2 * quaternionBlockMoment block term.1)
            (blockIntegratedCoefficientSum block tail)))

/-- Partial integration transports one already-accumulated raw sign. -/
theorem integratedComplexCoefficientSum_signed
    (block : Nat) (negative : Bool) (value : ComplexRatPoly) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (signedComplexRatPoly negative value))
      (signedRationalComplex negative
        (integratedComplexCoefficientSum block value)) := by
  cases negative
  · exact rationalComplexEqv_refl _
  · exact ⟨blockIntegratedCoefficientSum_neg_local block value.1,
      blockIntegratedCoefficientSum_neg_local block value.2⟩

/-! ## 6. Orientation-complete partial projectors -/

/-- **Exact arbitrary-block projector for every oriented four-word.** -/
theorem integrated_orientedFourFundamentalWord_projector
    (block : Nat)
    (first second third fourth : FundamentalOccurrence) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedFourFundamentalWord block first second third fourth))
      (orientedFourNormalizedHaarProjector first second third fourth) := by
  rw [orientedFourFundamentalWord_eq_signed_normalized]
  refine rationalComplexEqv_trans
    (integratedComplexCoefficientSum_signed block
      (orientedFourNormalizationNegative first second third fourth)
      (normalizedFourFundamentalWord block first second third fourth)) ?_
  exact signedRationalComplex_congr _
    (integrated_pairedTwoForwardTwoReverse_projector block
      first.toForward.row first.toForward.column
      third.toForward.row third.toForward.column
      second.toReverse.row second.toReverse.column
      fourth.toReverse.row fourth.toReverse.column)

/-- **Exact arbitrary-block projector for every oriented six-word.** -/
theorem integrated_orientedSixFundamentalWord_projector
    (block : Nat)
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedSixFundamentalWord block
          first second third fourth fifth sixth))
      (orientedSixNormalizedHaarProjector
        first second third fourth fifth sixth) := by
  rw [orientedSixFundamentalWord_eq_signed_normalized]
  refine rationalComplexEqv_trans
    (integratedComplexCoefficientSum_signed block
      (orientedSixNormalizationNegative
        first second third fourth fifth sixth)
      (normalizedSixFundamentalWord block
        first second third fourth fifth sixth)) ?_
  exact signedRationalComplex_congr _
    (integrated_threeForwardThreeReverse_projector block
      first.toForward.row first.toForward.column
      second.toForward.row second.toForward.column
      third.toForward.row third.toForward.column
      fourth.toReverse.row fourth.toReverse.column
      fifth.toReverse.row fifth.toReverse.column
      sixth.toReverse.row sixth.toReverse.column)

/-! ## 7. Block locality and independent-spectator lifts -/

theorem complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient
    (block : Nat) (occurrence : FundamentalOccurrence) :
    ComplexQuaternionBlockLocal block
      (fundamentalOccurrenceCoefficient block occurrence) := by
  rcases occurrence with ⟨orientation, row, column⟩
  cases orientation
  · exact complexQuaternionBlockLocal_forwardFundamentalCoefficient
      block row column
  · exact complexQuaternionBlockLocal_reverseFundamentalCoefficient
      block row column

theorem complexQuaternionBlockLocal_orientedFourFundamentalWord
    (block : Nat)
    (first second third fourth : FundamentalOccurrence) :
    ComplexQuaternionBlockLocal block
      (orientedFourFundamentalWord block first second third fourth) := by
  exact complexQuaternionBlockLocal_mul
    (complexQuaternionBlockLocal_mul
      (complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient block first)
      (complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient block second))
    (complexQuaternionBlockLocal_mul
      (complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient block third)
      (complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient block fourth))

theorem complexQuaternionBlockLocal_orientedSixFundamentalWord
    (block : Nat)
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    ComplexQuaternionBlockLocal block
      (orientedSixFundamentalWord block
        first second third fourth fifth sixth) := by
  unfold orientedSixFundamentalWord complexRatPolyMulSixLeft
  exact complexQuaternionBlockLocal_mul
    (complexQuaternionBlockLocal_mul
      (complexQuaternionBlockLocal_mul
        (complexQuaternionBlockLocal_mul
          (complexQuaternionBlockLocal_mul
            (complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient
              block first)
            (complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient
              block second))
          (complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient
            block third))
        (complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient
          block fourth))
      (complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient
        block fifth))
    (complexQuaternionBlockLocal_fundamentalOccurrenceCoefficient
      block sixth)

/-- Every oriented four-word may be eliminated beneath an arbitrary complex
spectator independent of the selected block. -/
theorem genericBlock_orientedFourFundamentalWord_projector_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent : ComplexQuaternionBlockIndependent block spectator)
    (first second third fourth : FundamentalOccurrence) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (orientedFourFundamentalWord block first second third fourth)))
      (SU2QuaternionGenericBlockPartialFundamentalSchur.rationalComplexMul
        (finiteProductHaarComplex blockCount spectator)
        (orientedFourNormalizedHaarProjector
          first second third fourth)) := by
  exact genericBlock_localFactor_with_complex_spectator
    blockCount block hblock spectator
    (orientedFourFundamentalWord block first second third fourth)
    hindependent
    (complexQuaternionBlockLocal_orientedFourFundamentalWord
      block first second third fourth)
    (orientedFourNormalizedHaarProjector first second third fourth)
    (integrated_orientedFourFundamentalWord_projector
      block first second third fourth)

/-- Every oriented six-word has the analogous independent-spectator lift. -/
theorem genericBlock_orientedSixFundamentalWord_projector_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent : ComplexQuaternionBlockIndependent block spectator)
    (first second third fourth fifth sixth : FundamentalOccurrence) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (orientedSixFundamentalWord block
            first second third fourth fifth sixth)))
      (SU2QuaternionGenericBlockPartialFundamentalSchur.rationalComplexMul
        (finiteProductHaarComplex blockCount spectator)
        (orientedSixNormalizedHaarProjector
          first second third fourth fifth sixth)) := by
  exact genericBlock_localFactor_with_complex_spectator
    blockCount block hblock spectator
    (orientedSixFundamentalWord block
      first second third fourth fifth sixth)
    hindependent
    (complexQuaternionBlockLocal_orientedSixFundamentalWord
      block first second third fourth fifth sixth)
    (orientedSixNormalizedHaarProjector
      first second third fourth fifth sixth)
    (integrated_orientedSixFundamentalWord_projector
      block first second third fourth fifth sixth)

/-! ## 8. Balanced recovery and epsilon-sign regressions -/

/-- The total four-word theorem recovers the existing paired balanced endpoint
without a sign or an index change. -/
theorem integrated_orientedFour_balanced_paired_compatible
    (block : Nat)
    (firstForwardRow firstForwardColumn
      firstReverseRow firstReverseColumn
      secondForwardRow secondForwardColumn
      secondReverseRow secondReverseColumn : Bool) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedFourFundamentalWord block
          ⟨.forward, firstForwardRow, firstForwardColumn⟩
          ⟨.reverse, firstReverseRow, firstReverseColumn⟩
          ⟨.forward, secondForwardRow, secondForwardColumn⟩
          ⟨.reverse, secondReverseRow, secondReverseColumn⟩))
      (orientedFourFundamentalHaarProjector
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn) := by
  simpa [orientedFourNormalizedHaarProjector,
    orientedFourNormalizationNegative, forwardNormalizationNegative,
    reverseNormalizationNegative, signXor, signedRationalComplex,
    FundamentalOccurrence.toForward, FundamentalOccurrence.toReverse] using
    (integrated_orientedFourFundamentalWord_projector block
      (⟨.forward, firstForwardRow, firstForwardColumn⟩ : FundamentalOccurrence)
      (⟨.reverse, firstReverseRow, firstReverseColumn⟩ : FundamentalOccurrence)
      (⟨.forward, secondForwardRow, secondForwardColumn⟩ : FundamentalOccurrence)
      (⟨.reverse, secondReverseRow, secondReverseColumn⟩ : FundamentalOccurrence))

/-- The total six-word theorem likewise recovers the canonical balanced
`F F F R R R` endpoint. -/
theorem integrated_orientedSix_balanced_compatible
    (block : Nat)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedSixFundamentalWord block
          ⟨.forward, firstForwardRow, firstForwardColumn⟩
          ⟨.forward, secondForwardRow, secondForwardColumn⟩
          ⟨.forward, thirdForwardRow, thirdForwardColumn⟩
          ⟨.reverse, firstReverseRow, firstReverseColumn⟩
          ⟨.reverse, secondReverseRow, secondReverseColumn⟩
          ⟨.reverse, thirdReverseRow, thirdReverseColumn⟩))
      (orientedSixFundamentalHaarProjector
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn) := by
  simpa [orientedSixNormalizedHaarProjector,
    orientedSixNormalizationNegative, forwardNormalizationNegative,
    reverseNormalizationNegative, signXor, signedRationalComplex,
    FundamentalOccurrence.toForward, FundamentalOccurrence.toReverse] using
    (integrated_orientedSixFundamentalWord_projector block
      (⟨.forward, firstForwardRow, firstForwardColumn⟩ : FundamentalOccurrence)
      (⟨.forward, secondForwardRow, secondForwardColumn⟩ : FundamentalOccurrence)
      (⟨.forward, thirdForwardRow, thirdForwardColumn⟩ : FundamentalOccurrence)
      (⟨.reverse, firstReverseRow, firstReverseColumn⟩ : FundamentalOccurrence)
      (⟨.reverse, secondReverseRow, secondReverseColumn⟩ : FundamentalOccurrence)
      (⟨.reverse, thirdReverseRow, thirdReverseColumn⟩ : FundamentalOccurrence))

/-- One off-diagonal dualization contributes the negative epsilon sign. -/
theorem integrated_orientedFour_one_offDiagonal_flip_negative
    (block : Nat) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedFourFundamentalWord block
          ⟨.forward, false, false⟩
          ⟨.reverse, false, false⟩
          ⟨.forward, false, true⟩
          ⟨.forward, true, false⟩))
      (-oneSixth, 0) := by
  refine rationalComplexEqv_trans
    (integrated_orientedFourFundamentalWord_projector block
      ⟨.forward, false, false⟩
      ⟨.reverse, false, false⟩
      ⟨.forward, false, true⟩
      ⟨.forward, true, false⟩) ?_
  constructor <;> decide

/-- Two off-diagonal dualizations cancel, leaving the positive
transpose-sensitive fourth-moment entry. -/
theorem integrated_orientedFour_two_offDiagonal_flips_positive
    (block : Nat) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedFourFundamentalWord block
          ⟨.forward, false, false⟩
          ⟨.reverse, false, false⟩
          ⟨.reverse, false, true⟩
          ⟨.forward, true, false⟩))
      (oneSixth, 0) := by
  refine rationalComplexEqv_trans
    (integrated_orientedFourFundamentalWord_projector block
      ⟨.forward, false, false⟩
      ⟨.reverse, false, false⟩
      ⟨.reverse, false, true⟩
      ⟨.forward, true, false⟩) ?_
  constructor <;> decide

/-- One off-diagonal dualization contributes the negative epsilon sign at
valence six. -/
theorem integrated_orientedSix_one_offDiagonal_flip_negative
    (block : Nat) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedSixFundamentalWord block
          ⟨.forward, false, false⟩
          ⟨.forward, false, false⟩
          ⟨.forward, false, true⟩
          ⟨.reverse, false, false⟩
          ⟨.reverse, false, false⟩
          ⟨.forward, true, false⟩))
      (-oneTwelfth, 0) := by
  refine rationalComplexEqv_trans
    (integrated_orientedSixFundamentalWord_projector block
      ⟨.forward, false, false⟩
      ⟨.forward, false, false⟩
      ⟨.forward, false, true⟩
      ⟨.reverse, false, false⟩
      ⟨.reverse, false, false⟩
      ⟨.forward, true, false⟩) ?_
  constructor <;> decide

/-- Two off-diagonal dualizations cancel at valence six. -/
theorem integrated_orientedSix_two_offDiagonal_flips_positive
    (block : Nat) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (orientedSixFundamentalWord block
          ⟨.forward, false, false⟩
          ⟨.forward, false, false⟩
          ⟨.reverse, false, true⟩
          ⟨.reverse, false, false⟩
          ⟨.reverse, false, false⟩
          ⟨.forward, true, false⟩))
      (oneTwelfth, 0) := by
  refine rationalComplexEqv_trans
    (integrated_orientedSixFundamentalWord_projector block
      ⟨.forward, false, false⟩
      ⟨.forward, false, false⟩
      ⟨.reverse, false, true⟩
      ⟨.reverse, false, false⟩
      ⟨.reverse, false, false⟩
      ⟨.forward, true, false⟩) ?_
  constructor <;> decide

/-! ## Axiom-dependency gates -/

#print axioms orientedFourFundamentalWord_eq_signed_normalized
#print axioms orientedSixFundamentalWord_eq_signed_normalized
#print axioms integrated_orientedFourFundamentalWord_projector
#print axioms integrated_orientedSixFundamentalWord_projector
#print axioms genericBlock_orientedFourFundamentalWord_projector_with_complex_spectator
#print axioms genericBlock_orientedSixFundamentalWord_projector_with_complex_spectator
#print axioms integrated_orientedFour_one_offDiagonal_flip_negative
#print axioms integrated_orientedFour_two_offDiagonal_flips_positive
#print axioms integrated_orientedSix_one_offDiagonal_flip_negative
#print axioms integrated_orientedSix_two_offDiagonal_flips_positive

end YMGap.Continuum.SU2QuaternionGenericBlockOrientedEvenWordNormalization
