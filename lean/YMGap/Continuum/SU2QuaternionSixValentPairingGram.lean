/-
# The five-pairing Gram projector for a six-valent fundamental SU(2) link

For three ordered forward fundamental indices and three ordered conjugate
indices, the six permutation pairings span only a five-dimensional space at
dimension two.  We retain the ordered basis

    [0,1,2], [1,0,2], [0,2,1], [1,2,0], [2,0,1]

and eliminate `[2,1,0]` by its pointwise Plucker relation.  The resulting
Gram matrix and inverse are

    G = [[8,4,4,2,2],       G^-1 = [[ 1/4,-1/6,-1/6, 1/12, 1/12],
         [4,8,2,4,4],               [-1/6, 1/3, 1/6,-1/6, -1/6 ],
         [4,2,8,4,4],               [-1/6, 1/6, 1/3,-1/6, -1/6 ],
         [2,4,4,8,2],               [ 1/12,-1/6,-1/6,1/4,  1/12],
         [2,4,4,2,8]]                [ 1/12,-1/6,-1/6,1/12, 1/4 ]].

This leaf certifies both inverse identities and freezes the externally
oriented inverse-Gram kernel.  Forward rows pair with external reverse
columns, and forward columns pair with external reverse rows.  The external
reverse pairs are not swapped: `reverseFundamentalCoefficient` already
contains the conjugate transpose internally.

All finite scalar contractions are split into two three-Bool stages.  No
six-deep Boolean sum is unfolded, reduced, evaluated, or printed.  There is
no global assignment carrier, bounded lattice labelling family, trajectory,
or length family.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector

namespace YMGap.Continuum.SU2QuaternionSixValentPairingGram

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Three-Bool scalar binders -/

/-- Three nested scalar Boolean binders.  Six-index contractions below are
always factored through two copies of this bounded carrier. -/
def rationalThreeBoolSum
    (family : Bool → Bool → Bool → Q') : Q' :=
  rationalBoolSum (fun first =>
    rationalBoolSum (fun second =>
      rationalBoolSum (fun third => family first second third)))

theorem rationalBoolSum_eqv_congr
    (left right : Bool → Q')
    (h : ∀ value, left value ≈ right value) :
    rationalBoolSum left ≈ rationalBoolSum right := by
  unfold rationalBoolSum
  exact Q'.eqv_trans _ (right false + left true) _
    (Q'.add_eqv_congr_right _ _ _ (h false))
    (Q'.add_eqv_congr_left _ _ _ (h true))

theorem rationalThreeBoolSum_eqv_congr
    (left right : Bool → Bool → Bool → Q')
    (h : ∀ first second third,
      left first second third ≈ right first second third) :
    rationalThreeBoolSum left ≈ rationalThreeBoolSum right := by
  unfold rationalThreeBoolSum
  exact rationalBoolSum_eqv_congr _ _ (fun first =>
    rationalBoolSum_eqv_congr _ _ (fun second =>
      rationalBoolSum_eqv_congr _ _ (fun third =>
        h first second third)))

/-! ## 2. The five independent permutation pairings -/

/-- Ordered independent permutation pairings. -/
inductive SixValentPairing where
  | identity
  | swapFirstTwo
  | swapLastTwo
  | cycleForward
  | cycleBackward
  deriving DecidableEq

/-- Five-term finite sum in the frozen pairing order. -/
def sixValentPairingSum (family : SixValentPairing → Q') : Q' :=
  (((family .identity + family .swapFirstTwo) +
      family .swapLastTwo) + family .cycleForward) +
    family .cycleBackward

/-- The pairing-basis Kronecker delta. -/
def sixValentPairingDelta
    (left right : SixValentPairing) : Q' :=
  if left = right then 1 else 0

/-- Pair three ordered forward indices with three ordered conjugate indices
according to one of the five retained permutations. -/
def tripleOrientedPairing :
    SixValentPairing → Bool → Bool → Bool →
      Bool → Bool → Bool → Q'
  | .identity, first, second, third,
      firstConjugate, secondConjugate, thirdConjugate =>
      boolKronecker first firstConjugate *
        (boolKronecker second secondConjugate *
          boolKronecker third thirdConjugate)
  | .swapFirstTwo, first, second, third,
      firstConjugate, secondConjugate, thirdConjugate =>
      boolKronecker first secondConjugate *
        (boolKronecker second firstConjugate *
          boolKronecker third thirdConjugate)
  | .swapLastTwo, first, second, third,
      firstConjugate, secondConjugate, thirdConjugate =>
      boolKronecker first firstConjugate *
        (boolKronecker second thirdConjugate *
          boolKronecker third secondConjugate)
  | .cycleForward, first, second, third,
      firstConjugate, secondConjugate, thirdConjugate =>
      boolKronecker first secondConjugate *
        (boolKronecker second thirdConjugate *
          boolKronecker third firstConjugate)
  | .cycleBackward, first, second, third,
      firstConjugate, secondConjugate, thirdConjugate =>
      boolKronecker first thirdConjugate *
        (boolKronecker second firstConjugate *
          boolKronecker third secondConjugate)

/-- The omitted transposition `[2,1,0]`. -/
def omittedOuterSwapOrientedPairing
    (first second third firstConjugate secondConjugate thirdConjugate : Bool) :
    Q' :=
  boolKronecker first thirdConjugate *
    (boolKronecker second secondConjugate *
      boolKronecker third firstConjugate)

/-- Alternating retained-basis combination in the dimension-two relation. -/
def retainedPairingPluckerCombination
    (first second third firstConjugate secondConjugate thirdConjugate : Bool) :
    Q' :=
  (((tripleOrientedPairing .identity
          first second third
          firstConjugate secondConjugate thirdConjugate +
        (-tripleOrientedPairing .swapFirstTwo
          first second third
          firstConjugate secondConjugate thirdConjugate)) +
      (-tripleOrientedPairing .swapLastTwo
        first second third
        firstConjugate secondConjugate thirdConjugate)) +
    tripleOrientedPairing .cycleForward
      first second third
      firstConjugate secondConjugate thirdConjugate) +
    tripleOrientedPairing .cycleBackward
      first second third
      firstConjugate secondConjugate thirdConjugate

/-- Dimension-two Plucker relation eliminating the sixth permutation
pairing. -/
theorem omittedOuterSwapOrientedPairing_plucker
    (first second third firstConjugate secondConjugate thirdConjugate : Bool) :
    omittedOuterSwapOrientedPairing
        first second third firstConjugate secondConjugate thirdConjugate ≈
      retainedPairingPluckerCombination
        first second third firstConjugate secondConjugate thirdConjugate := by
  cases first <;> cases second <;> cases third <;>
    cases firstConjugate <;> cases secondConjugate <;>
    cases thirdConjugate <;>
    unfold omittedOuterSwapOrientedPairing retainedPairingPluckerCombination
      tripleOrientedPairing boolKronecker <;>
    decide

/-! ## 3. Exact Gram table without a six-deep reduction -/

/-- After summing the three conjugate indices, two permutation tensors impose
the relative-permutation equalities displayed by this table. -/
def triplePairingForwardOverlap :
    SixValentPairing → SixValentPairing → Bool → Bool → Bool → Q'
  | .identity, .identity, _, _, _ => 1
  | .identity, .swapFirstTwo, first, second, _ =>
      boolKronecker first second
  | .identity, .swapLastTwo, _, second, third =>
      boolKronecker second third
  | .identity, .cycleForward, first, second, third =>
      boolKronecker first second * boolKronecker second third
  | .identity, .cycleBackward, first, second, third =>
      boolKronecker first second * boolKronecker second third
  | .swapFirstTwo, .identity, first, second, _ =>
      boolKronecker first second
  | .swapFirstTwo, .swapFirstTwo, _, _, _ => 1
  | .swapFirstTwo, .swapLastTwo, first, second, third =>
      boolKronecker first second * boolKronecker second third
  | .swapFirstTwo, .cycleForward, _, second, third =>
      boolKronecker second third
  | .swapFirstTwo, .cycleBackward, first, _, third =>
      boolKronecker first third
  | .swapLastTwo, .identity, _, second, third =>
      boolKronecker second third
  | .swapLastTwo, .swapFirstTwo, first, second, third =>
      boolKronecker first second * boolKronecker second third
  | .swapLastTwo, .swapLastTwo, _, _, _ => 1
  | .swapLastTwo, .cycleForward, first, _, third =>
      boolKronecker first third
  | .swapLastTwo, .cycleBackward, first, second, _ =>
      boolKronecker first second
  | .cycleForward, .identity, first, second, third =>
      boolKronecker first second * boolKronecker second third
  | .cycleForward, .swapFirstTwo, _, second, third =>
      boolKronecker second third
  | .cycleForward, .swapLastTwo, first, _, third =>
      boolKronecker first third
  | .cycleForward, .cycleForward, _, _, _ => 1
  | .cycleForward, .cycleBackward, first, second, third =>
      boolKronecker first second * boolKronecker second third
  | .cycleBackward, .identity, first, second, third =>
      boolKronecker first second * boolKronecker second third
  | .cycleBackward, .swapFirstTwo, first, _, third =>
      boolKronecker first third
  | .cycleBackward, .swapLastTwo, first, second, _ =>
      boolKronecker first second
  | .cycleBackward, .cycleForward, first, second, third =>
      boolKronecker first second * boolKronecker second third
  | .cycleBackward, .cycleBackward, _, _, _ => 1

/-- Sum over the three conjugate indices at fixed forward indices. -/
def tripleOrientedPairingReverseInner
    (left right : SixValentPairing)
    (first second third : Bool) : Q' :=
  rationalThreeBoolSum (fun firstConjugate secondConjugate thirdConjugate =>
    tripleOrientedPairing left first second third
        firstConjugate secondConjugate thirdConjugate *
      tripleOrientedPairing right first second third
        firstConjugate secondConjugate thirdConjugate)

/-- The inner three-index contraction gives the relative-permutation
constraint, pointwise in the three still-opaque forward indices. -/
theorem tripleOrientedPairingReverseInner_exact
    (left right : SixValentPairing)
    (first second third : Bool) :
    tripleOrientedPairingReverseInner left right first second third ≈
      triplePairingForwardOverlap left right first second third := by
  cases left <;> cases right <;>
    cases first <;> cases second <;> cases third <;>
    unfold tripleOrientedPairingReverseInner rationalThreeBoolSum
      rationalBoolSum tripleOrientedPairing triplePairingForwardOverlap
      boolKronecker <;>
    decide

/-- Exact inner product of two three-forward/three-conjugate pairing tensors,
factored into two depth-three scalar binders. -/
def tripleOrientedPairingInner
    (left right : SixValentPairing) : Q' :=
  rationalThreeBoolSum (fun first second third =>
    tripleOrientedPairingReverseInner left right first second third)

/-- Frozen `5 × 5` Gram table in the declared pairing order. -/
def sixValentPairingGram :
    SixValentPairing → SixValentPairing → Q'
  | .identity, .identity => 8
  | .identity, .swapFirstTwo => 4
  | .identity, .swapLastTwo => 4
  | .identity, .cycleForward => 2
  | .identity, .cycleBackward => 2
  | .swapFirstTwo, .identity => 4
  | .swapFirstTwo, .swapFirstTwo => 8
  | .swapFirstTwo, .swapLastTwo => 2
  | .swapFirstTwo, .cycleForward => 4
  | .swapFirstTwo, .cycleBackward => 4
  | .swapLastTwo, .identity => 4
  | .swapLastTwo, .swapFirstTwo => 2
  | .swapLastTwo, .swapLastTwo => 8
  | .swapLastTwo, .cycleForward => 4
  | .swapLastTwo, .cycleBackward => 4
  | .cycleForward, .identity => 2
  | .cycleForward, .swapFirstTwo => 4
  | .cycleForward, .swapLastTwo => 4
  | .cycleForward, .cycleForward => 8
  | .cycleForward, .cycleBackward => 2
  | .cycleBackward, .identity => 2
  | .cycleBackward, .swapFirstTwo => 4
  | .cycleBackward, .swapLastTwo => 4
  | .cycleBackward, .cycleForward => 2
  | .cycleBackward, .cycleBackward => 8

theorem sixValentPairingGram_symmetric
    (left right : SixValentPairing) :
    sixValentPairingGram left right =
      sixValentPairingGram right left := by
  cases left <;> cases right <;> rfl

/-- The pairing tensors realize the frozen Gram table.  The proof first
contracts only the three conjugate indices and then only the three forward
indices. -/
theorem tripleOrientedPairing_gram_exact
    (left right : SixValentPairing) :
    tripleOrientedPairingInner left right ≈
      sixValentPairingGram left right := by
  refine Q'.eqv_trans _
    (rationalThreeBoolSum (fun first second third =>
      triplePairingForwardOverlap left right first second third)) _ ?_ ?_
  · exact rationalThreeBoolSum_eqv_congr _ _
      (fun first second third =>
        tripleOrientedPairingReverseInner_exact
          left right first second third)
  · cases left <;> cases right <;>
      unfold rationalThreeBoolSum rationalBoolSum
        triplePairingForwardOverlap sixValentPairingGram boolKronecker <;>
      decide

/-! ## 4. Certified inverse Gram matrix -/

def oneQuarter : Q' := Q'.mkPos 1 4 (by decide)
def oneTwelfth : Q' := Q'.mkPos 1 12 (by decide)
def threeQuarters : Q' := Q'.mkPos 3 4 (by decide)

/-- Exact inverse of `sixValentPairingGram`. -/
def sixValentPairingGramInverse :
    SixValentPairing → SixValentPairing → Q'
  | .identity, .identity => oneQuarter
  | .identity, .swapFirstTwo => -oneSixth
  | .identity, .swapLastTwo => -oneSixth
  | .identity, .cycleForward => oneTwelfth
  | .identity, .cycleBackward => oneTwelfth
  | .swapFirstTwo, .identity => -oneSixth
  | .swapFirstTwo, .swapFirstTwo => oneThird
  | .swapFirstTwo, .swapLastTwo => oneSixth
  | .swapFirstTwo, .cycleForward => -oneSixth
  | .swapFirstTwo, .cycleBackward => -oneSixth
  | .swapLastTwo, .identity => -oneSixth
  | .swapLastTwo, .swapFirstTwo => oneSixth
  | .swapLastTwo, .swapLastTwo => oneThird
  | .swapLastTwo, .cycleForward => -oneSixth
  | .swapLastTwo, .cycleBackward => -oneSixth
  | .cycleForward, .identity => oneTwelfth
  | .cycleForward, .swapFirstTwo => -oneSixth
  | .cycleForward, .swapLastTwo => -oneSixth
  | .cycleForward, .cycleForward => oneQuarter
  | .cycleForward, .cycleBackward => oneTwelfth
  | .cycleBackward, .identity => oneTwelfth
  | .cycleBackward, .swapFirstTwo => -oneSixth
  | .cycleBackward, .swapLastTwo => -oneSixth
  | .cycleBackward, .cycleForward => oneTwelfth
  | .cycleBackward, .cycleBackward => oneQuarter

theorem sixValentPairingGramInverse_symmetric
    (left right : SixValentPairing) :
    sixValentPairingGramInverse left right =
      sixValentPairingGramInverse right left := by
  cases left <;> cases right <;> rfl

/-- Left inverse identity `G G^-1 ≃ I`. -/
theorem sixValentPairingGram_mul_inverse
    (row column : SixValentPairing) :
    sixValentPairingSum (fun middle =>
      sixValentPairingGram row middle *
        sixValentPairingGramInverse middle column) ≈
      sixValentPairingDelta row column := by
  cases row <;> cases column <;>
    unfold sixValentPairingSum sixValentPairingGram
      sixValentPairingGramInverse sixValentPairingDelta
      oneQuarter oneTwelfth oneThird oneSixth <;>
    decide

/-- Right inverse identity `G^-1 G ≃ I`. -/
theorem sixValentPairingGramInverse_mul_gram
    (row column : SixValentPairing) :
    sixValentPairingSum (fun middle =>
      sixValentPairingGramInverse row middle *
        sixValentPairingGram middle column) ≈
      sixValentPairingDelta row column := by
  cases row <;> cases column <;>
    unfold sixValentPairingSum sixValentPairingGram
      sixValentPairingGramInverse sixValentPairingDelta
      oneQuarter oneTwelfth oneThird oneSixth <;>
    decide

/-! ## 5. The externally oriented inverse-Gram kernel -/

/-- Scalar entry of the normalized three-forward/three-reverse invariant
projector. -/
def orientedSixFundamentalHaarProjectorScalar
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) : Q' :=
  sixValentPairingSum (fun rowPairing =>
    sixValentPairingSum (fun columnPairing =>
      sixValentPairingGramInverse rowPairing columnPairing *
        (tripleOrientedPairing rowPairing
            firstForwardRow secondForwardRow thirdForwardRow
            firstReverseColumn secondReverseColumn thirdReverseColumn *
          tripleOrientedPairing columnPairing
            firstForwardColumn secondForwardColumn thirdForwardColumn
            firstReverseRow secondReverseRow thirdReverseRow)))

/-- Rational-complex form of the six-valent projector entry. -/
def orientedSixFundamentalHaarProjector
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) : RationalComplex :=
  (orientedSixFundamentalHaarProjectorScalar
    firstForwardRow firstForwardColumn
    secondForwardRow secondForwardColumn
    thirdForwardRow thirdForwardColumn
    firstReverseRow firstReverseColumn
    secondReverseRow secondReverseColumn
    thirdReverseRow thirdReverseColumn, 0)

/-- Deliberately wrong external convention, retained only for the
transpose-sensitive regression below. -/
def untransposedSixFundamentalProjectorScalar
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) : Q' :=
  sixValentPairingSum (fun rowPairing =>
    sixValentPairingSum (fun columnPairing =>
      sixValentPairingGramInverse rowPairing columnPairing *
        (tripleOrientedPairing rowPairing
            firstForwardRow secondForwardRow thirdForwardRow
            firstReverseRow secondReverseRow thirdReverseRow *
          tripleOrientedPairing columnPairing
            firstForwardColumn secondForwardColumn thirdForwardColumn
            firstReverseColumn secondReverseColumn thirdReverseColumn)))

/-- All indices equal gives the positive entry `1/4`. -/
theorem orientedSixFundamentalHaarProjectorScalar_all_false :
    orientedSixFundamentalHaarProjectorScalar
      false false false false false false
      false false false false false false ≈ oneQuarter := by
  unfold orientedSixFundamentalHaarProjectorScalar sixValentPairingSum
    sixValentPairingGramInverse tripleOrientedPairing boolKronecker
    oneQuarter oneTwelfth oneThird oneSixth
  decide

/-- A concrete negative inverse-Gram interference entry. -/
theorem orientedSixFundamentalHaarProjectorScalar_negative_entry :
    orientedSixFundamentalHaarProjectorScalar
      false false false false true true
      false false false true true false ≈ -oneTwelfth := by
  unfold orientedSixFundamentalHaarProjectorScalar sixValentPairingSum
    sixValentPairingGramInverse tripleOrientedPairing boolKronecker
    oneQuarter oneTwelfth oneThird oneSixth
  decide

/-- The correct external reverse convention gives `1/12` on a
transpose-sensitive entry. -/
theorem orientedSixFundamentalHaarProjectorScalar_transpose_sensitive_entry :
    orientedSixFundamentalHaarProjectorScalar
      false false false false false true
      false false false false true false ≈ oneTwelfth := by
  unfold orientedSixFundamentalHaarProjectorScalar sixValentPairingSum
    sixValentPairingGramInverse tripleOrientedPairing boolKronecker
    oneQuarter oneTwelfth oneThird oneSixth
  decide

/-- Omitting the external reverse transpose would make the same entry zero. -/
theorem untransposedSixFundamentalProjectorScalar_sensitive_entry_zero :
    untransposedSixFundamentalProjectorScalar
      false false false false false true
      false false false false true false ≈ 0 := by
  unfold untransposedSixFundamentalProjectorScalar sixValentPairingSum
    sixValentPairingGramInverse tripleOrientedPairing boolKronecker
    oneQuarter oneTwelfth oneThird oneSixth
  decide

/-! ## 6. Closed trace, split into two depth-three contractions -/

/-- Sum only the three reverse diagonal indices, leaving the forward indices
opaque. -/
def orientedSixFundamentalProjectorReverseDiagonalSum
    (firstForward secondForward thirdForward : Bool) : Q' :=
  rationalThreeBoolSum (fun firstReverse secondReverse thirdReverse =>
    orientedSixFundamentalHaarProjectorScalar
      firstForward firstForward
      secondForward secondForward
      thirdForward thirdForward
      firstReverse firstReverse
      secondReverse secondReverse
      thirdReverse thirdReverse)

/-- Partial trace value: `1/4` when the three forward bits coincide and
`3/4` otherwise. -/
def sixValentProjectorForwardTraceValue
    (first second third : Bool) : Q' :=
  if first = second ∧ second = third then oneQuarter else threeQuarters

theorem orientedSixFundamentalProjectorReverseDiagonalSum_exact
    (first second third : Bool) :
    orientedSixFundamentalProjectorReverseDiagonalSum first second third ≈
      sixValentProjectorForwardTraceValue first second third := by
  cases first <;> cases second <;> cases third <;>
    unfold orientedSixFundamentalProjectorReverseDiagonalSum
      rationalThreeBoolSum rationalBoolSum
      orientedSixFundamentalHaarProjectorScalar sixValentPairingSum
      sixValentPairingGramInverse tripleOrientedPairing boolKronecker
      sixValentProjectorForwardTraceValue oneQuarter oneTwelfth
      threeQuarters oneThird oneSixth <;>
    decide

/-- The full diagonal trace, represented as an outer three-Bool sum of the
already isolated reverse partial traces. -/
def orientedSixFundamentalHaarProjectorDiagonalTrace : Q' :=
  rationalThreeBoolSum (fun first second third =>
    orientedSixFundamentalProjectorReverseDiagonalSum first second third)

/-- The signed rank-five projector has closed trace exactly five. -/
theorem orientedSixFundamentalHaarProjector_diagonal_trace_exact :
    orientedSixFundamentalHaarProjectorDiagonalTrace ≈ 5 := by
  unfold orientedSixFundamentalHaarProjectorDiagonalTrace
  refine Q'.eqv_trans _
    (rationalThreeBoolSum (fun first second third =>
      sixValentProjectorForwardTraceValue first second third)) _ ?_ ?_
  · exact rationalThreeBoolSum_eqv_congr _ _
      (fun first second third =>
        orientedSixFundamentalProjectorReverseDiagonalSum_exact
          first second third)
  · unfold rationalThreeBoolSum rationalBoolSum
      sixValentProjectorForwardTraceValue oneQuarter threeQuarters
    decide

#print axioms rationalThreeBoolSum_eqv_congr
#print axioms omittedOuterSwapOrientedPairing_plucker
#print axioms tripleOrientedPairingReverseInner_exact
#print axioms tripleOrientedPairing_gram_exact
#print axioms sixValentPairingGram_mul_inverse
#print axioms sixValentPairingGramInverse_mul_gram
#print axioms orientedSixFundamentalHaarProjectorScalar_all_false
#print axioms orientedSixFundamentalHaarProjectorScalar_negative_entry
#print axioms orientedSixFundamentalHaarProjectorScalar_transpose_sensitive_entry
#print axioms untransposedSixFundamentalProjectorScalar_sensitive_entry_zero
#print axioms orientedSixFundamentalProjectorReverseDiagonalSum_exact
#print axioms orientedSixFundamentalHaarProjector_diagonal_trace_exact

end YMGap.Continuum.SU2QuaternionSixValentPairingGram
