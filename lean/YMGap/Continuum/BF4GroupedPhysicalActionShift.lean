/-
# The grouped positive BF4 carrier has the physical action after normalization

The grouped reflected carrier uses three positive exponentials:

* the source complement `E_s = B - D_s`;
* its reflected target copy `E_t = B - D_t`; and
* the positive kinetic cross term `X`.

This file assembles their literal ten-holonomy polynomial

  `G = E_s + E_t + X`

and proves the arbitrary-insertion sphere identity

  `H(P G) + H(P A) = (B + B) H(P)`.

Here `A` is the genuine compact coupled BF4 action.  Consequently the
normalization omitted from the positive half-amplitudes is exactly
`exp (-2B)`, not the older compact shift `exp (-133/4)` by itself.

This is the finite polynomial/action layer needed before the constructive
Mertens comparison of the separated grouped series with the single physical
negative-action series.

## Axiom gate

Only finite exact `Q'` polynomial algebra, kernel normalization, and
quaternion-Haar sphere identities are used.  No `Classical.*`, `Real`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4GroupedHolonomyPositiveLimit
import YMGap.Continuum.BF4CompactActionPhysicalLimit
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.ExpNegCongr
import YMGap.Constructive.ProductLaw

namespace YMGap.Continuum.BF4GroupedPhysicalActionShift

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Constructive.ExpPos
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4CompactActionDiagonalSOS
open YMGap.Continuum.BF4CompactActionMomentPositivity
open YMGap.Continuum.BF4CompactActionPhysicalLimit
open YMGap.Continuum.BF4CompactActionSphereShift
open YMGap.Continuum.BF4CompactActionShiftedLimit
open YMGap.Continuum.BF4CompactCoupledActionBounds
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GroupedGramChoiKernel
open YMGap.Continuum.BF4GroupedHolonomyCrossMajorant
open YMGap.Continuum.BF4GroupedHolonomyPositiveLimit
open YMGap.Continuum.BF4ReflectedAllSpinMehlerGramEndpoint
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionArbitraryHaarHomogenization
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarRingNormalizer
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

/-- Cancellation-free exact `Q'` normalization. -/
local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Q'.invSucc_num, Q'.invSucc_den,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

private def groupedSumExpressions :
    List RingNormaliser.PolyExpr → RingNormaliser.PolyExpr
  | [] => RingNormaliser.PolyExpr.const 0
  | expression :: rest =>
      RingNormaliser.PolyExpr.add expression
        (groupedSumExpressions rest)

/-! ## 1. Literal reflected target complement -/

/-- Five reflected-target quaternion radius squares. -/
def targetFiveRadiusSumExpression :
    RingNormaliser.PolyExpr :=
  groupedSumExpressions
    ((List.range 20).map fun coordinate =>
      RingNormaliser.PolyExpr.mul
        (RingNormaliser.PolyExpr.var (20 + coordinate))
        (RingNormaliser.PolyExpr.var (20 + coordinate)))

/-- Cleared reflected-target complement `B-D_t`. -/
def targetClearedDiagonalComplementExpression :
    RingNormaliser.PolyExpr :=
  RingNormaliser.PolyExpr.add
    (RingNormaliser.PolyExpr.mul
      (RingNormaliser.PolyExpr.const
        sourceDiagonalSphereCoefficient)
      targetFiveRadiusSumExpression)
    (RingNormaliser.PolyExpr.neg
      targetClearedDiagonalActionExpression)

/-- Normalized reflected-target complement. -/
def targetDiagonalComplementPolynomial : RatPoly :=
  polySmul oneOverSourceDiagonalClearing
    (exprToRatPoly
      targetClearedDiagonalComplementExpression)

/-! ## 2. The exact grouped positive exponent -/

/-- Componentwise source/target/cross presentation of the positive exponent
represented by the grouped carrier. -/
def groupedPositiveComponentPolynomial : RatPoly :=
  polyAdd sourceDiagonalComplementPolynomial
    (polyAdd targetDiagonalComplementPolynomial
      sourceTargetKineticCrossPolynomial)

/-- Cleared expression for the same grouped positive exponent. -/
def groupedPositiveComplementClearedExpression :
    RingNormaliser.PolyExpr :=
  RingNormaliser.PolyExpr.add
    sourceClearedDiagonalComplementExpression
    (RingNormaliser.PolyExpr.add
      targetClearedDiagonalComplementExpression
      sourceTargetKineticCrossExpression)

/-- Normalized compiled grouped positive exponent. -/
def groupedPositiveComplementPolynomial : RatPoly :=
  polySmul oneOverSourceDiagonalClearing
    (exprToRatPoly
      groupedPositiveComplementClearedExpression)

/-- The componentwise source/target/cross carrier and the compiled grouped
expression agree under every arbitrary ten-Haar insertion.  The statement is
Haar-level because the expression compiler retains harmless zero-coefficient
terms with different monomial padding on the two presentations. -/
theorem groupedPositiveComponent_haar_eq_compiled
    (polynomial : RatPoly) :
    quaternionHaar 10
        (polyMul polynomial
          groupedPositiveComponentPolynomial) ≈
      quaternionHaar 10
        (polyMul polynomial
          groupedPositiveComplementPolynomial) := by
  unfold groupedPositiveComponentPolynomial
  refine Q'.eqv_trans _
    (quaternionHaar 10
          (polyMul polynomial
            sourceDiagonalComplementPolynomial) +
      (quaternionHaar 10
            (polyMul polynomial
              targetDiagonalComplementPolynomial) +
        quaternionHaar 10
          (polyMul polynomial
            sourceTargetKineticCrossPolynomial))) _
    (Q'.eqv_trans _ _ _
      (quaternionHaar_polyMul_add_right
        10 polynomial sourceDiagonalComplementPolynomial
        (polyAdd targetDiagonalComplementPolynomial
          sourceTargetKineticCrossPolynomial))
      (Q'.add_eqv_congr_left _ _ _
        (quaternionHaar_polyMul_add_right
          10 polynomial targetDiagonalComplementPolynomial
          sourceTargetKineticCrossPolynomial))) ?_
  unfold sourceDiagonalComplementPolynomial
    targetDiagonalComplementPolynomial
    sourceTargetKineticCrossPolynomial
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
          quaternionHaar 10
            (polyMul polynomial
              (exprToRatPoly
                sourceClearedDiagonalComplementExpression)) +
      (oneOverSourceDiagonalClearing *
            quaternionHaar 10
              (polyMul polynomial
                (exprToRatPoly
                  targetClearedDiagonalComplementExpression)) +
        oneOverSourceDiagonalClearing *
          quaternionHaar 10
            (polyMul polynomial
              (exprToRatPoly
                sourceTargetKineticCrossExpression)))) _
    (Q'.add_eqv_congr'
      (quaternionHaar_polyMul_smul_right
        10 oneOverSourceDiagonalClearing polynomial
        (exprToRatPoly
          sourceClearedDiagonalComplementExpression))
      (Q'.add_eqv_congr'
        (quaternionHaar_polyMul_smul_right
          10 oneOverSourceDiagonalClearing polynomial
          (exprToRatPoly
            targetClearedDiagonalComplementExpression))
        (quaternionHaar_polyMul_smul_right
          10 oneOverSourceDiagonalClearing polynomial
          (exprToRatPoly
            sourceTargetKineticCrossExpression)))) ?_
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      (quaternionHaar 10
            (polyMul polynomial
              (exprToRatPoly
                sourceClearedDiagonalComplementExpression)) +
        (quaternionHaar 10
              (polyMul polynomial
                (exprToRatPoly
                  targetClearedDiagonalComplementExpression)) +
          quaternionHaar 10
            (polyMul polynomial
              (exprToRatPoly
                sourceTargetKineticCrossExpression))))) _
    (by q_ring) ?_
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      quaternionHaar 10
        (polyMul polynomial
          (exprToRatPoly
            groupedPositiveComplementClearedExpression))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (quaternionHaar_polyMul_add_right
            10 polynomial
            (exprToRatPoly
              sourceClearedDiagonalComplementExpression)
            (exprToRatPoly
              (RingNormaliser.PolyExpr.add
                targetClearedDiagonalComplementExpression
                sourceTargetKineticCrossExpression)))
          (Q'.add_eqv_congr_left _ _ _
            (quaternionHaar_polyMul_add_right
              10 polynomial
              (exprToRatPoly
                targetClearedDiagonalComplementExpression)
              (exprToRatPoly
                sourceTargetKineticCrossExpression)))))) ?_
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_smul_right
      10 oneOverSourceDiagonalClearing polynomial
      (exprToRatPoly
        groupedPositiveComplementClearedExpression))

/-! ## 2a. The fifteen word atoms are the compiled kinetic cross term -/

/-- Reflection of one source kinetic feature is literally its target
feature polynomial; there is no coefficient or gauge convention hidden in
the coordinate shift. -/
theorem targetKineticFeaturePolynomial_eq_shift
    (feature : BF4KineticFeature) :
    targetKineticFeaturePolynomial feature =
      shiftPolynomial 20
        (sourceKineticFeaturePolynomial feature) := by
  revert feature
  decide

/-- One common source/target feature atom with its physical LDL weight. -/
def groupedKineticCrossFeatureAtom
    (feature : BF4KineticFeature) : RatPoly :=
  polySmul (bf4KineticFeatureWeight feature)
    (polyMul
      (sourceKineticFeaturePolynomial feature)
      (targetKineticFeaturePolynomial feature))

/-- Literal finite sum of all fifteen positive kinetic atoms.  The explicit
compiled zero keeps its list shape aligned with `sumExpressions`. -/
def groupedKineticCrossFeaturePolynomial : RatPoly :=
  bf4KineticFeatureAlphabet.foldr
    (fun feature total =>
      polyAdd
        (groupedKineticCrossFeatureAtom feature)
        total)
    (exprToRatPoly
      (RingNormaliser.PolyExpr.const 0))

/-- The feature sum and the LDL-compiled cross polynomial have identical
monomials in identical order and equivalent exact-rational coefficients. -/
theorem groupedKineticCrossFeaturePolynomial_termwise :
    RatPolyTermwiseEqv
      groupedKineticCrossFeaturePolynomial
      sourceTargetKineticCrossPolynomial := by
  decide

/-- Therefore every arbitrary insertion sees precisely the same cross term.
This is the finite all-label source/target Choi contraction at word length
one. -/
theorem groupedKineticCrossFeature_haar_eq_physical
    (polynomial : RatPoly) :
    quaternionHaar 10
        (polyMul polynomial
          groupedKineticCrossFeaturePolynomial) ≈
      quaternionHaar 10
        (polyMul polynomial
          sourceTargetKineticCrossPolynomial) :=
  quaternionHaar_polyMul_termwise_eqv
    10 polynomial
    groupedKineticCrossFeaturePolynomial_termwise

/-! ## 2b. Exact factorial weight of every ordered kinetic word -/

/-- Product of the fifteen physical LDL weights along one ordered word,
before its common factorial coefficient is inserted. -/
def bf4KineticFeatureWeightProduct :
    List BF4KineticFeature → Q'
  | [] => 1
  | feature :: rest =>
      bf4KineticFeatureWeight feature *
        bf4KineticFeatureWeightProduct rest

/-- The recursively defined feature-word weight is exactly

`(1 / word.length!) * ∏ᵢ weight(word[i])`.

This is the scalar identity needed to regroup the ordered all-label carrier
as a Taylor power of the fifteen-atom kinetic polynomial. -/
theorem bf4FeatureWordWeight_eq_factorial_product :
    ∀ word : List BF4KineticFeature,
      bf4FeatureWordWeight word ≈
        ExpNeg.termAbs 1 word.length *
          bf4KineticFeatureWeightProduct word
  | [] => by
      change (1 : Q') ≈ 1 * 1
      exact Q'.eqv_symm (Q'.one_mul_eqv 1)
  | feature :: rest => by
      change
        (bf4KineticFeatureWeight feature *
            Q'.invSucc rest.length) *
            bf4FeatureWordWeight rest ≈
          ExpNeg.termAbs 1 (rest.length + 1) *
            (bf4KineticFeatureWeight feature *
              bf4KineticFeatureWeightProduct rest)
      refine Q'.eqv_trans _
        ((bf4KineticFeatureWeight feature *
            Q'.invSucc rest.length) *
          (ExpNeg.termAbs 1 rest.length *
            bf4KineticFeatureWeightProduct rest)) _
        (Q'.mul_eqv_congr_left
          (bf4KineticFeatureWeight feature *
            Q'.invSucc rest.length) _ _
          (bf4FeatureWordWeight_eq_factorial_product rest)) ?_
      rw [ExpNeg.termAbs_succ]
      q_ring

/-- Product of the already-weighted reflected kinetic atoms in one ordered
word.  The empty word is the polynomial unit. -/
def groupedKineticCrossWordProduct :
    List BF4KineticFeature → RatPoly
  | [] => polyOne
  | feature :: rest =>
      polyMul
        (groupedKineticCrossFeatureAtom feature)
        (groupedKineticCrossWordProduct rest)

/-- The factorially weighted atom word. -/
def groupedKineticCrossWordTaylorPolynomial
    (word : List BF4KineticFeature) : RatPoly :=
  polySmul (ExpNeg.termAbs 1 word.length)
    (groupedKineticCrossWordProduct word)

/-- The fifteen-atom sum without the expression compiler's harmless final
zero term.  This presentation is convenient for exact word enumeration. -/
def groupedKineticCrossAtomSumPolynomial : RatPoly :=
  bf4KineticFeatureAlphabet.foldr
    (fun feature total =>
      polyAdd
        (groupedKineticCrossFeatureAtom feature)
        total)
    polyZero

/-- Haar moment of one unscaled ordered atom word after an arbitrary
ten-holonomy insertion. -/
def groupedKineticCrossWordMoment
    (polynomial : RatPoly)
    (word : List BF4KineticFeature) : Q' :=
  quaternionHaar 10
    (polyMul polynomial
      (groupedKineticCrossWordProduct word))

/-- Sum of all ordered-word moments at one exact length. -/
def groupedKineticCrossWordsExactMoment
    (polynomial : RatPoly)
    (length : Nat) : Q' :=
  listQSum
    (groupedKineticCrossWordMoment polynomial)
    (bf4FeatureWordsExact length)

private theorem quaternionHaar_polyMul_zero_right_ten
    (polynomial : RatPoly) :
    quaternionHaar 10
        (polyMul polynomial polyZero) ≈ 0 := by
  have hzero :
      polyMul polynomial polyZero = polyZero := by
    simp [polyMul, polyZero]
  rw [hzero]
  exact Q'.eqv_refl 0

private theorem listQSum_groupedAtomMoment_eq_foldr
    (polynomial : RatPoly) :
    ∀ features : List BF4KineticFeature,
      listQSum
          (fun feature =>
            quaternionHaar 10
              (polyMul polynomial
                (groupedKineticCrossFeatureAtom feature)))
          features ≈
        quaternionHaar 10
          (polyMul polynomial
            (features.foldr
              (fun feature total =>
                polyAdd
                  (groupedKineticCrossFeatureAtom feature)
                  total)
              polyZero))
  | [] =>
      Q'.eqv_symm
        (quaternionHaar_polyMul_zero_right_ten
          polynomial)
  | feature :: rest => by
      change
        quaternionHaar 10
              (polyMul polynomial
                (groupedKineticCrossFeatureAtom feature)) +
            listQSum
              (fun next =>
                quaternionHaar 10
                  (polyMul polynomial
                    (groupedKineticCrossFeatureAtom next)))
              rest ≈
          quaternionHaar 10
            (polyMul polynomial
              (polyAdd
                (groupedKineticCrossFeatureAtom feature)
                (rest.foldr
                  (fun next total =>
                    polyAdd
                      (groupedKineticCrossFeatureAtom next)
                      total)
                  polyZero)))
      refine Q'.eqv_trans _
        (quaternionHaar 10
              (polyMul polynomial
                (groupedKineticCrossFeatureAtom feature)) +
          quaternionHaar 10
            (polyMul polynomial
              (rest.foldr
                (fun next total =>
                  polyAdd
                    (groupedKineticCrossFeatureAtom next)
                    total)
                polyZero))) _
        (Q'.add_eqv_congr_left _ _ _
          (listQSum_groupedAtomMoment_eq_foldr
            polynomial rest)) ?_
      exact Q'.eqv_symm
        (quaternionHaar_polyMul_add_right
          10 polynomial
          (groupedKineticCrossFeatureAtom feature)
          (rest.foldr
            (fun next total =>
              polyAdd
                (groupedKineticCrossFeatureAtom next)
                total)
            polyZero))

private theorem groupedKineticCrossWordMoment_cons
    (polynomial : RatPoly)
    (feature : BF4KineticFeature)
    (rest : List BF4KineticFeature) :
    groupedKineticCrossWordMoment polynomial
        (feature :: rest) ≈
    groupedKineticCrossWordMoment
        (polyMul polynomial
          (groupedKineticCrossFeatureAtom feature))
        rest := by
  change
    quaternionHaar 10
        (polyMul polynomial
          (polyMul
            (groupedKineticCrossFeatureAtom feature)
            (groupedKineticCrossWordProduct rest))) ≈
      quaternionHaar 10
        (polyMul
          (polyMul polynomial
            (groupedKineticCrossFeatureAtom feature))
          (groupedKineticCrossWordProduct rest))
  exact Q'.eqv_symm
    (quaternionHaar_polyMul_assoc
      10 polynomial
      (groupedKineticCrossFeatureAtom feature)
      (groupedKineticCrossWordProduct rest))

private theorem groupedKineticCrossWordMoment_map_cons_sum
    (polynomial : RatPoly)
    (length : Nat)
    (feature : BF4KineticFeature) :
    listQSum
        (groupedKineticCrossWordMoment polynomial)
        ((bf4FeatureWordsExact length).map
          fun word => feature :: word) ≈
      groupedKineticCrossWordsExactMoment
        (polyMul polynomial
          (groupedKineticCrossFeatureAtom feature))
        length := by
  rw [listQSum_map]
  unfold groupedKineticCrossWordsExactMoment
  apply listQSum_congr
  intro word
  exact groupedKineticCrossWordMoment_cons
    polynomial feature word

/-- **Exact all-label atom regrouping.**  For every insertion and every
word length, summing all `15^n` ordered kinetic labels is exactly the Haar
moment of the `n`-th power of their common fifteen-atom polynomial. -/
theorem groupedKineticCrossWordsExactMoment_eq_power :
    ∀ (polynomial : RatPoly) (length : Nat),
      groupedKineticCrossWordsExactMoment
          polynomial length ≈
        quaternionHaar 10
          (polyMul polynomial
            (polynomialPower
              groupedKineticCrossAtomSumPolynomial
              length))
  | polynomial, 0 => by
      change
        quaternionHaar 10
              (polyMul polynomial polyOne) + 0 ≈
          quaternionHaar 10
            (polyMul polynomial polyOne)
      exact Q'.eqv_of_eq
        (Q'.add_zero'
          (quaternionHaar 10
            (polyMul polynomial polyOne)))
  | polynomial, length + 1 => by
      change
        listQSum
            (groupedKineticCrossWordMoment polynomial)
            (bf4KineticFeatureAlphabet.flatMap
              fun feature =>
                (bf4FeatureWordsExact length).map
                  fun word => feature :: word) ≈
          quaternionHaar 10
            (polyMul polynomial
              (polyMul
                (polynomialPower
                  groupedKineticCrossAtomSumPolynomial
                  length)
                groupedKineticCrossAtomSumPolynomial))
      refine Q'.eqv_trans _
        (listQSum
          (fun feature =>
            groupedKineticCrossWordsExactMoment
              (polyMul polynomial
                (groupedKineticCrossFeatureAtom feature))
              length)
          bf4KineticFeatureAlphabet) _
        (Q'.eqv_trans _ _ _
          (listQSum_flatMap
            (groupedKineticCrossWordMoment polynomial)
            (fun feature =>
              (bf4FeatureWordsExact length).map
                fun word => feature :: word)
            bf4KineticFeatureAlphabet)
          (listQSum_congr
            (groupedKineticCrossWordMoment_map_cons_sum
              polynomial length)
            bf4KineticFeatureAlphabet)) ?_
      refine Q'.eqv_trans _
        (listQSum
          (fun feature =>
            quaternionHaar 10
              (polyMul
                (polyMul polynomial
                  (groupedKineticCrossFeatureAtom feature))
                (polynomialPower
                  groupedKineticCrossAtomSumPolynomial
                  length)))
          bf4KineticFeatureAlphabet) _
        (listQSum_congr
          (fun feature =>
            groupedKineticCrossWordsExactMoment_eq_power
              (polyMul polynomial
                (groupedKineticCrossFeatureAtom feature))
              length)
          bf4KineticFeatureAlphabet) ?_
      refine Q'.eqv_trans _
        (listQSum
          (fun feature =>
            quaternionHaar 10
              (polyMul
                (polyMul polynomial
                  (polynomialPower
                    groupedKineticCrossAtomSumPolynomial
                    length))
                (groupedKineticCrossFeatureAtom feature)))
          bf4KineticFeatureAlphabet) _ ?_ ?_
      · apply listQSum_congr
        intro feature
        exact Q'.eqv_trans _ _ _
          (quaternionHaar_polyMul_assoc
            10 polynomial
            (groupedKineticCrossFeatureAtom feature)
            (polynomialPower
              groupedKineticCrossAtomSumPolynomial
              length))
          (Q'.eqv_trans _ _ _
            (quaternionHaar_polyMul_middle_comm
              10 polynomial
              (groupedKineticCrossFeatureAtom feature)
              (polynomialPower
                groupedKineticCrossAtomSumPolynomial
                length))
            (Q'.eqv_symm
              (quaternionHaar_polyMul_assoc
                10 polynomial
                (polynomialPower
                  groupedKineticCrossAtomSumPolynomial
                  length)
                (groupedKineticCrossFeatureAtom feature))))
      · exact Q'.eqv_trans _ _ _
          (listQSum_groupedAtomMoment_eq_foldr
            (polyMul polynomial
              (polynomialPower
                groupedKineticCrossAtomSumPolynomial
                length))
            bf4KineticFeatureAlphabet)
          (quaternionHaar_polyMul_assoc
            10 polynomial
            (polynomialPower
              groupedKineticCrossAtomSumPolynomial
              length)
            groupedKineticCrossAtomSumPolynomial)

/-- Sum of the factorially scaled ordered-word moments at one exact
kinetic length. -/
def groupedKineticCrossWordsExactTaylorMoment
    (polynomial : RatPoly)
    (length : Nat) : Q' :=
  listQSum
    (fun word =>
      quaternionHaar 10
        (polyMul polynomial
          (groupedKineticCrossWordTaylorPolynomial word)))
    (bf4FeatureWordsExact length)

/-- **Quantitative all-label Taylor collapse.**  The physical LDL weights
and the word factorial combine so that every exact-length all-label sum is
one ordinary Taylor term of the fifteen-atom kinetic polynomial. -/
theorem groupedKineticCrossWordsExactTaylorMoment_eq_term :
    ∀ (polynomial : RatPoly) (length : Nat),
      groupedKineticCrossWordsExactTaylorMoment
          polynomial length ≈
        quaternionHaar 10
          (polyMul polynomial
            (polySmul (ExpNeg.termAbs 1 length)
              (polynomialPower
                groupedKineticCrossAtomSumPolynomial
                length))) := by
  intro polynomial length
  let coefficient := ExpNeg.termAbs 1 length
  refine Q'.eqv_trans _
    (listQSum
      (fun word =>
        coefficient *
          groupedKineticCrossWordMoment polynomial word)
      (bf4FeatureWordsExact length)) _ ?_ ?_
  · unfold groupedKineticCrossWordsExactTaylorMoment
    apply listQSum_congr_on
    intro word hword
    have hlength :=
      bf4FeatureWordsExact_word_length
        length word hword
    unfold groupedKineticCrossWordTaylorPolynomial
      groupedKineticCrossWordMoment coefficient
    rw [hlength]
    exact quaternionHaar_polyMul_smul_right
      10 (ExpNeg.termAbs 1 length) polynomial
      (groupedKineticCrossWordProduct word)
  · refine Q'.eqv_trans _
      (coefficient *
        groupedKineticCrossWordsExactMoment
          polynomial length) _
      (listQSum_mul_left
        coefficient
        (groupedKineticCrossWordMoment polynomial)
        (bf4FeatureWordsExact length)) ?_
    refine Q'.eqv_trans _
      (coefficient *
        quaternionHaar 10
          (polyMul polynomial
            (polynomialPower
              groupedKineticCrossAtomSumPolynomial
              length))) _
      (Q'.mul_eqv_congr_left coefficient _ _
        (groupedKineticCrossWordsExactMoment_eq_power
          polynomial length)) ?_
    exact Q'.eqv_symm
      (quaternionHaar_polyMul_smul_right
        10 coefficient polynomial
        (polynomialPower
          groupedKineticCrossAtomSumPolynomial
          length))

/-! ## 3. Exact two-sphere shift -/

/-- Adding the factorized physical action to the grouped complement cancels
both diagonal actions and the kinetic cross term. -/
def groupedComplementPlusActionExpression :
    RingNormaliser.PolyExpr :=
  RingNormaliser.PolyExpr.add
    groupedPositiveComplementClearedExpression
    factorizedClearedCoupledActionExpression

/-- Ten-sphere scalar representative of twice the one-sided shift. -/
def groupedTenRadiusShiftExpression :
    RingNormaliser.PolyExpr :=
  RingNormaliser.PolyExpr.mul
    (RingNormaliser.PolyExpr.const
      sourceDiagonalSphereCoefficient)
    tenRadiusSumExpr

theorem groupedComplementPlusAction_normal :
    RingNormaliser.normalize
        groupedComplementPlusActionExpression =
      RingNormaliser.normalize
        groupedTenRadiusShiftExpression := by
  decide

/-- The displayed source-plus-target radius expression compiles to the
canonical ten-quaternion radius-prefix polynomial. -/
theorem groupedTenRadiusShiftPolynomial_eq :
    exprToRatPoly groupedTenRadiusShiftExpression =
      polyAdd
        (polySmul
          (Q'.ofInt sourceDiagonalSphereCoefficient)
          (quaternionRadiusPrefixSum 10))
        (exprToRatPoly
          (RingNormaliser.PolyExpr.const 0)) := by
  decide

private theorem quaternionHaar_polyMul_compiledZero_right_ten :
    ∀ polynomial : RatPoly,
      quaternionHaar 10
          (polyMul polynomial
            (exprToRatPoly
              (RingNormaliser.PolyExpr.const 0))) ≈
        0
  | [] => Q'.eqv_refl 0
  | term :: rest => by
      change
        (term.2 * 0) *
              quaternionHaarMono 10
                (monoMul term.1 []) +
            quaternionHaar 10
              (polyMul rest
                (exprToRatPoly
                  (RingNormaliser.PolyExpr.const 0))) ≈
          0
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_zero_eqv term.2))
            (Q'.zero_mul_eqv _))
          (quaternionHaar_polyMul_compiledZero_right_ten
            rest)
      · exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-- **Grouped arbitrary-insertion sphere shift.**

The literal grouped positive exponent `G` and the LDL-factorized coupled
action add to the common scalar `2B` after normalized ten-Haar integration.
The insertion is arbitrary and may couple all ten holonomies. -/
theorem groupedPositiveComplement_factorizedAction_sphere_shift
    (polynomial : RatPoly) :
    quaternionHaar 10
          (polyMul polynomial
            groupedPositiveComplementPolynomial) +
        quaternionHaar 10
          (polyMul polynomial
            factorizedCoupledBF4ActionPolynomial) ≈
      (sourceDiagonalSphereShift +
          sourceDiagonalSphereShift) *
        quaternionHaar 10 polynomial := by
  unfold groupedPositiveComplementPolynomial
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      (quaternionHaar 10
          (polyMul polynomial
            (exprToRatPoly
              groupedPositiveComplementClearedExpression)) +
        quaternionHaar 10
          (polyMul polynomial
            (exprToRatPoly
              factorizedClearedCoupledActionExpression)))) _
    ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr'
        (quaternionHaar_polyMul_smul_right
          10 oneOverSourceDiagonalClearing polynomial
          (exprToRatPoly
            groupedPositiveComplementClearedExpression))
        (quaternionHaar_polyMul_smul_right
          10 oneOverSourceDiagonalClearing polynomial
          (exprToRatPoly
            factorizedClearedCoupledActionExpression)))
      (Q'.eqv_symm
        (Q'.mul_add_eqv
          oneOverSourceDiagonalClearing _ _))
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      quaternionHaar 10
        (polyMul polynomial
          (exprToRatPoly
            groupedComplementPlusActionExpression))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (Q'.eqv_symm
        (quaternionHaar_polyMul_add_right
          10 polynomial
          (exprToRatPoly
            groupedPositiveComplementClearedExpression)
          (exprToRatPoly
            factorizedClearedCoupledActionExpression)))) ?_
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      quaternionHaar 10
        (polyMul polynomial
          (exprToRatPoly
            groupedTenRadiusShiftExpression))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (quaternionHaar_mul_expr_congr_of_normal_eq
        10 groupedComplementPlusActionExpression
        groupedTenRadiusShiftExpression
        groupedComplementPlusAction_normal
        polynomial)) ?_
  rw [groupedTenRadiusShiftPolynomial_eq]
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      (quaternionHaar 10
          (polyMul polynomial
            (polySmul
              (Q'.ofInt sourceDiagonalSphereCoefficient)
              (quaternionRadiusPrefixSum 10))) +
        quaternionHaar 10
          (polyMul polynomial
            (exprToRatPoly
              (RingNormaliser.PolyExpr.const 0))))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (quaternionHaar_polyMul_add_right
        10 polynomial
        (polySmul
          (Q'.ofInt sourceDiagonalSphereCoefficient)
          (quaternionRadiusPrefixSum 10))
        (exprToRatPoly
          (RingNormaliser.PolyExpr.const 0)))) ?_
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      ((Q'.ofInt sourceDiagonalSphereCoefficient) *
          quaternionHaar 10
            (polyMul polynomial
              (quaternionRadiusPrefixSum 10)) +
        0)) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (Q'.add_eqv_congr'
        (quaternionHaar_polyMul_smul_right
          10 (Q'.ofInt sourceDiagonalSphereCoefficient)
          polynomial (quaternionRadiusPrefixSum 10))
        (quaternionHaar_polyMul_compiledZero_right_ten
          polynomial))) ?_
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      ((Q'.ofInt sourceDiagonalSphereCoefficient) *
        (Q'.ofNat 10 * quaternionHaar 10 polynomial))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (Q'.eqv_trans _ _ _
        (QPoly.q_add_zero_eqv _)
        (Q'.mul_eqv_congr_left
          (Q'.ofInt sourceDiagonalSphereCoefficient) _ _
          (quaternionHaar_mul_radiusPrefixSum
            10 polynomial)))) ?_
  unfold sourceDiagonalSphereShift
  have hten :
      Q'.ofNat 10 ≈
        Q'.ofNat 5 + Q'.ofNat 5 := by
    decide
  refine Q'.eqv_trans _
    (oneOverSourceDiagonalClearing *
      (Q'.ofInt sourceDiagonalSphereCoefficient *
        ((Q'.ofNat 5 + Q'.ofNat 5) *
          quaternionHaar 10 polynomial))) _
    (Q'.mul_eqv_congr_left
      oneOverSourceDiagonalClearing _ _
      (Q'.mul_eqv_congr_left
        (Q'.ofInt sourceDiagonalSphereCoefficient) _ _
        (Q'.mul_eqv_congr_right _ _ _ hten))) ?_
  q_ring

/-- Replacing the factorized action by the already-identified genuine
compact BF4 action leaves the grouped sphere shift unchanged. -/
theorem groupedPositiveComplement_physicalAction_sphere_shift
    (polynomial : RatPoly) :
    quaternionHaar 10
          (polyMul polynomial
            groupedPositiveComplementPolynomial) +
        quaternionHaar 10
          (polyMul polynomial
            compactCoupledBF4ActionPolynomial) ≈
      (sourceDiagonalSphereShift +
          sourceDiagonalSphereShift) *
        quaternionHaar 10 polynomial := by
  refine Q'.eqv_trans _
    (quaternionHaar 10
          (polyMul polynomial
            groupedPositiveComplementPolynomial) +
      quaternionHaar 10
          (polyMul polynomial
            factorizedCoupledBF4ActionPolynomial)) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (factorizedCoupledBF4Action_haar_eq_physical
          polynomial)))
    (groupedPositiveComplement_factorizedAction_sphere_shift
      polynomial)

/-! ## 4. Exact comparison with the compact `133/4-A` complement -/

/-- The scalar by which the grouped positive exponent exceeds the compact
`133/4-A` complement in the ten-sphere quotient. -/
def groupedToCompactComplementShift : Q' :=
  (sourceDiagonalSphereShift +
      sourceDiagonalSphereShift) -
    compactCoupledBF4ActionCeiling

theorem groupedToCompactComplementShift_pos :
    (0 : Q') < groupedToCompactComplementShift := by
  unfold groupedToCompactComplementShift
    sourceDiagonalSphereShift
    oneOverSourceDiagonalClearing
    sourceDiagonalClearing
    sourceDiagonalSphereCoefficient
    compactCoupledBF4ActionCeiling
  decide

private theorem q_add_cancel_reorder
    (x y z : Q') :
    (x + y) + (z + (-x)) ≈ z + y := by
  refine Q'.eqv_trans _ (((x + y) + z) + (-x)) _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv (x + y) z (-x))) ?_
  have hreorder :
      (x + y) + z ≈ (z + y) + x := by
    refine Q'.eqv_trans _ (z + (x + y)) _
      (Q'.add_comm_eqv (x + y) z) ?_
    refine Q'.eqv_trans _ (z + (y + x)) _
      (Q'.add_eqv_congr_left z _ _
        (Q'.add_comm_eqv x y)) ?_
    exact Q'.eqv_symm
      (Q'.add_assoc_eqv z y x)
  refine Q'.eqv_trans _ (((z + y) + x) + (-x)) _
    (Q'.add_eqv_congr'
      hreorder (Q'.eqv_refl (-x))) ?_
  refine Q'.eqv_trans _ ((z + y) + (x + (-x))) _
    (Q'.add_assoc_eqv (z + y) x (-x)) ?_
  refine Q'.eqv_trans _ ((z + y) + 0) _
    (Q'.add_eqv_congr_left (z + y) _ _
      (Q'.add_neg_self_eqv x)) ?_
  exact QPoly.q_add_zero_eqv (z + y)

private theorem q_grouped_shift_recombine
    (groupedShift compactShift haar action : Q') :
    groupedShift * haar + (-action) ≈
      (compactShift * haar + (-action)) +
        (groupedShift - compactShift) * haar := by
  let x := compactShift * haar
  let y := -action
  let z := groupedShift * haar
  have hdifference :
      (groupedShift - compactShift) * haar ≈
        z + (-x) := by
    change
      (groupedShift + (-compactShift)) * haar ≈
        groupedShift * haar + (-(compactShift * haar))
    refine Q'.eqv_trans _
      (groupedShift * haar + (-compactShift) * haar) _
      (Q'.add_mul_eqv groupedShift (-compactShift) haar) ?_
    exact Q'.add_eqv_congr_left
      (groupedShift * haar) _ _
      (Q'.neg_mul_eqv compactShift haar)
  refine Q'.eqv_symm
    (Q'.eqv_trans _ ((x + y) + (z + (-x))) _
      (Q'.add_eqv_congr_left (x + y) _ _
        hdifference) ?_)
  exact q_add_cancel_reorder x y z

/-- Under every arbitrary insertion,

`G = (133/4-A) + (2B-133/4)`

in the exact ten-sphere Haar quotient.  This is the coefficient-level bridge
between the grouped positive series and the already-constructed compact
shifted exponential. -/
theorem groupedPositiveComplement_haar_eq_compact_add_shift
    (polynomial : RatPoly) :
    quaternionHaar 10
        (polyMul polynomial
          groupedPositiveComplementPolynomial) ≈
      quaternionHaar 10
          (polyMul polynomial
            compactActionComplementPolynomial) +
        groupedToCompactComplementShift *
          quaternionHaar 10 polynomial := by
  let grouped :=
    quaternionHaar 10
      (polyMul polynomial
        groupedPositiveComplementPolynomial)
  let compact :=
    quaternionHaar 10
      (polyMul polynomial
        compactActionComplementPolynomial)
  let action :=
    quaternionHaar 10
      (polyMul polynomial
        compactCoupledBF4ActionPolynomial)
  let haar := quaternionHaar 10 polynomial
  let groupedShift :=
    sourceDiagonalSphereShift +
      sourceDiagonalSphereShift
  let compactShift :=
    compactCoupledBF4ActionCeiling
  have hgrouped :
      grouped + action ≈ groupedShift * haar :=
    groupedPositiveComplement_physicalAction_sphere_shift
      polynomial
  have hcompact :
      compact + action ≈ compactShift * haar :=
    compactPhysicalAction_sphere_shift polynomial
  have hgroupedSolved :
      grouped ≈ groupedShift * haar + (-action) := by
    refine Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (-action)
          (Q'.eqv_symm hgrouped)) ?_)
    refine Q'.eqv_trans _
      (grouped + (action + (-action))) _
      (Q'.add_assoc_eqv grouped action (-action)) ?_
    refine Q'.eqv_trans _ (grouped + 0) _
      (Q'.add_eqv_congr_left grouped _ _
        (Q'.add_neg_self_eqv action)) ?_
    exact QPoly.q_add_zero_eqv grouped
  have hcompactSolved :
      compact ≈ compactShift * haar + (-action) := by
    refine Q'.eqv_symm
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (-action)
          (Q'.eqv_symm hcompact)) ?_)
    refine Q'.eqv_trans _
      (compact + (action + (-action))) _
      (Q'.add_assoc_eqv compact action (-action)) ?_
    refine Q'.eqv_trans _ (compact + 0) _
      (Q'.add_eqv_congr_left compact _ _
        (Q'.add_neg_self_eqv action)) ?_
    exact QPoly.q_add_zero_eqv compact
  refine Q'.eqv_trans _
    (groupedShift * haar + (-action)) _
    hgroupedSolved ?_
  change
    groupedShift * haar + (-action) ≈
      compact +
        (groupedShift - compactShift) * haar
  refine Q'.eqv_trans _
    ((compactShift * haar + (-action)) +
      (groupedShift - compactShift) * haar) _
    ?_ ?_
  · exact q_grouped_shift_recombine
      groupedShift compactShift haar action
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm hcompactSolved)

/-! ## 5. The correctly normalized grouped located endpoint -/

/-- The scalar removed from the two positive diagonal half-amplitudes. -/
def groupedPhysicalNormalization : Q' :=
  sourceDiagonalSphereShift +
    sourceDiagonalSphereShift

theorem groupedPhysicalNormalization_nonnegative :
    (0 : Q') ≤ groupedPhysicalNormalization := by
  decide

/-- The joint grouped BF4 endpoint with the omitted `exp(-B)` factor restored
on both reflected halves. -/
def bf4PacketPhysicalNormalizedGroupedLimit
    (packet : BF4HolonomyStatePacket) :
    CReal :=
  CReal.mul
    (ExpNeg.expNeg groupedPhysicalNormalization
      groupedPhysicalNormalization_nonnegative)
    (bf4PacketGroupedSquareJointLimit packet)

/-- Physical normalization preserves the manifest CP/nonnegative order. -/
theorem bf4PacketPhysicalNormalizedGroupedLimit_nonnegative
    (packet : BF4HolonomyStatePacket) :
    ExpPos.geRat
      (bf4PacketPhysicalNormalizedGroupedLimit packet) 0 := by
  have hjoint :
      ExpPos.geRat
        (bf4PacketGroupedSquareJointLimit packet) 0 := by
    apply ExpPos.geRat_of_eventually
    exact
      ⟨0, fun stage _ =>
        bf4PacketCrossSOSPartial_nonnegative
          stage stage packet⟩
  exact CReal.mul_nonneg
    (expNeg_geRat_zero
      groupedPhysicalNormalization
      groupedPhysicalNormalization_nonnegative)
    hjoint

/-! ## 6. Abstract grouped exponential already normalizes to the physical
compact endpoint -/

/-- The two sound scalar inequalities for `exp(shift) exp(-shift)` combine
to a genuine constructive-real equivalence with one. -/
theorem expPos_mul_expNeg_equiv_cone
    (value : Q') (hvalue : (0 : Q') ≤ value) :
    CReal.Equiv
      (CReal.mul
        (ExpPos.expPos value hvalue)
        (ExpNeg.expNeg value hvalue))
      CReal.cone := by
  intro epsilon hepsilon
  obtain ⟨upperCutoff, hupper⟩ :=
    expProd_leRat value hvalue epsilon hepsilon
  obtain ⟨lowerCutoff, hlower⟩ :=
    expProd_geRat value hvalue epsilon hepsilon
  refine
    ⟨max upperCutoff lowerCutoff,
      fun stage hstage => ⟨?_, ?_⟩⟩
  · exact hupper stage
      (Nat.le_trans
        (Nat.le_max_left _ _) hstage)
  · exact hlower stage
      (Nat.le_trans
        (Nat.le_max_right _ _) hstage)

/-- The positive grouped exponential represented abstractly as

`exp(2B-133/4) H(P² exp(133/4-A))`.

The remaining carrier theorem must identify the joint word/diagonal limit
with this already-located object. -/
def abstractGroupedPositiveQuadraticLimit
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    CReal :=
  CReal.mul
    (ExpPos.expPos groupedToCompactComplementShift
      (Q'.le_of_lt
        groupedToCompactComplementShift_pos))
    (compactActionShiftedTaylorQuadraticLimit
      polynomial hsupport)

/-- Restore the omitted source and target shifts to the abstract grouped
positive endpoint. -/
def abstractPhysicalNormalizedGroupedQuadraticLimit
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    CReal :=
  CReal.mul
    (ExpNeg.expNeg groupedPhysicalNormalization
      groupedPhysicalNormalization_nonnegative)
    (abstractGroupedPositiveQuadraticLimit
      polynomial hsupport)

private theorem groupedPhysicalNormalization_decompose :
    groupedPhysicalNormalization ≈
      compactCoupledBF4ActionCeiling +
        groupedToCompactComplementShift := by
  unfold groupedToCompactComplementShift
    groupedPhysicalNormalization
  exact Q'.add_sub_cancel_eqv
    (sourceDiagonalSphereShift +
      sourceDiagonalSphereShift)
    compactCoupledBF4ActionCeiling

private theorem groupedScalarNormalization_equiv :
    CReal.Equiv
      (CReal.mul
        (ExpNeg.expNeg groupedPhysicalNormalization
          groupedPhysicalNormalization_nonnegative)
        (ExpPos.expPos groupedToCompactComplementShift
          (Q'.le_of_lt
            groupedToCompactComplementShift_pos)))
      (ExpNeg.expNeg compactCoupledBF4ActionCeiling
        (by decide)) := by
  let compactShift := compactCoupledBF4ActionCeiling
  let residual := groupedToCompactComplementShift
  have hcompact0 : (0 : Q') ≤ compactShift := by
    decide
  have hresidual0 : (0 : Q') ≤ residual :=
    Q'.le_of_lt groupedToCompactComplementShift_pos
  have hsum0 : (0 : Q') ≤ compactShift + residual :=
    Q'.zero_le_add _ _ hcompact0 hresidual0
  have hsplit :
      CReal.Equiv
        (ExpNeg.expNeg groupedPhysicalNormalization
          groupedPhysicalNormalization_nonnegative)
        (CReal.mul
          (ExpNeg.expNeg compactShift hcompact0)
          (ExpNeg.expNeg residual hresidual0)) := by
    refine CReal.Equiv.trans
      (expNeg_eqv_congr
        groupedPhysicalNormalization_nonnegative
        hsum0
        groupedPhysicalNormalization_decompose) ?_
    exact CReal.Equiv.symm
      (expNeg_add_equiv
        compactShift residual hcompact0 hresidual0)
  refine CReal.Equiv.trans
    (CReal.mul_congr_left hsplit) ?_
  refine CReal.Equiv.trans
    (CRealAlg.cmul_assoc
      (ExpNeg.expNeg compactShift hcompact0)
      (ExpNeg.expNeg residual hresidual0)
      (ExpPos.expPos residual hresidual0)) ?_
  have hcancel :
      CReal.Equiv
        (CReal.mul
          (ExpNeg.expNeg residual hresidual0)
          (ExpPos.expPos residual hresidual0))
        CReal.cone :=
    CReal.Equiv.trans
      (CRealAlg.cmul_comm
        (ExpNeg.expNeg residual hresidual0)
        (ExpPos.expPos residual hresidual0))
      (expPos_mul_expNeg_equiv_cone
        residual hresidual0)
  exact CReal.Equiv.trans
    (CRealAlg.cmul_comm
      (ExpNeg.expNeg compactShift hcompact0)
      (CReal.mul
        (ExpNeg.expNeg residual hresidual0)
        (ExpPos.expPos residual hresidual0)))
    (CReal.Equiv.trans
      (CReal.mul_congr_left hcancel)
      (CRealAlg.cone_mul
        (ExpNeg.expNeg compactShift hcompact0)))

/-- **Abstract normalized grouped endpoint equals the physical endpoint.**

No carrier convergence is assumed here: it is a scalar consequence of the
proved shift `G=(133/4-A)+(2B-133/4)`.  The sole remaining identification is
therefore the actual joint grouped carrier with
`abstractGroupedPositiveQuadraticLimit`. -/
theorem abstractPhysicalNormalizedGrouped_equiv_compactPhysical
    (polynomial : RatPoly)
    (hsupport :
      SupportedQuaternionBlocks 10 polynomial) :
    CReal.Equiv
      (abstractPhysicalNormalizedGroupedQuadraticLimit
        polynomial hsupport)
      (compactPhysicalNegativeTaylorQuadraticLimit
        polynomial hsupport) := by
  unfold abstractPhysicalNormalizedGroupedQuadraticLimit
    abstractGroupedPositiveQuadraticLimit
    compactPhysicalNegativeTaylorQuadraticLimit
  refine CReal.Equiv.trans
    (CReal.Equiv.symm
      (CRealAlg.cmul_assoc
        (ExpNeg.expNeg groupedPhysicalNormalization
          groupedPhysicalNormalization_nonnegative)
        (ExpPos.expPos groupedToCompactComplementShift
          (Q'.le_of_lt
            groupedToCompactComplementShift_pos))
        (compactActionShiftedTaylorQuadraticLimit
          polynomial hsupport))) ?_
  exact CReal.mul_congr_left
    groupedScalarNormalization_equiv

/-! ## 7. Exact packet boundary and the final same-carrier target -/

/-- The literal source packet before every diagonal or kinetic insertion.
Order one and the empty word are exactly the unit diagonal/empty cross
channel of the grouped construction. -/
def bf4PacketBoundarySourcePolynomial
    (packet : BF4HolonomyStatePacket) : RatPoly :=
  bf4PacketHalfPolynomial 1 [] packet

/-- Reflected copy on the target five-holonomy block. -/
def bf4PacketBoundaryTargetPolynomial
    (packet : BF4HolonomyStatePacket) : RatPoly :=
  shiftPolynomial 20
    (bf4PacketBoundarySourcePolynomial packet)

theorem bf4PacketBoundarySource_supported
    (packet : BF4HolonomyStatePacket) :
    SupportedQuaternionBlocks 10
      (bf4PacketBoundarySourcePolynomial packet) := by
  intro term hterm
  unfold bf4PacketBoundarySourcePolynomial at hterm
  rw [bf4PacketHalfPolynomial_term_length
    1 [] packet term hterm]
  omega

theorem bf4PacketBoundaryTarget_supported
    (packet : BF4HolonomyStatePacket) :
    SupportedQuaternionBlocks 10
      (bf4PacketBoundaryTargetPolynomial packet) := by
  intro term hterm
  unfold bf4PacketBoundaryTargetPolynomial
    shiftPolynomial at hterm
  simp only [List.mem_map] at hterm
  rcases hterm with ⟨source, hsource, rfl⟩
  simp only [List.length_append, List.length_replicate]
  have hlength :
      source.1.length = 20 :=
    bf4PacketHalfPolynomial_term_length
      1 [] packet source hsource
  rw [hlength]
  omega

private theorem supported_polyAdd_ten_local
    {left right : RatPoly}
    (hleft : SupportedQuaternionBlocks 10 left)
    (hright : SupportedQuaternionBlocks 10 right) :
    SupportedQuaternionBlocks 10
      (polyAdd left right) := by
  intro term hterm
  simp only [polyAdd, List.mem_append] at hterm
  rcases hterm with hterm | hterm
  · exact hleft term hterm
  · exact hright term hterm

private theorem supported_polySmul_ten_local
    (coefficient : Q') {polynomial : RatPoly}
    (hsupport : SupportedQuaternionBlocks 10 polynomial) :
    SupportedQuaternionBlocks 10
      (polySmul coefficient polynomial) := by
  intro term hterm
  simp only [polySmul, List.mem_map] at hterm
  rcases hterm with ⟨source, hsource, rfl⟩
  exact hsupport source hsource

/-- Polarization sum for the actual packet source/target carrier. -/
def bf4PacketBoundarySumPolynomial
    (packet : BF4HolonomyStatePacket) : RatPoly :=
  polyAdd
    (bf4PacketBoundarySourcePolynomial packet)
    (bf4PacketBoundaryTargetPolynomial packet)

/-- Polarization difference for the same carrier. -/
def bf4PacketBoundaryDifferencePolynomial
    (packet : BF4HolonomyStatePacket) : RatPoly :=
  polyAdd
    (bf4PacketBoundarySourcePolynomial packet)
    (polySmul (-1)
      (bf4PacketBoundaryTargetPolynomial packet))

theorem bf4PacketBoundarySum_supported
    (packet : BF4HolonomyStatePacket) :
    SupportedQuaternionBlocks 10
      (bf4PacketBoundarySumPolynomial packet) :=
  supported_polyAdd_ten_local
    (bf4PacketBoundarySource_supported packet)
    (bf4PacketBoundaryTarget_supported packet)

theorem bf4PacketBoundaryDifference_supported
    (packet : BF4HolonomyStatePacket) :
    SupportedQuaternionBlocks 10
      (bf4PacketBoundaryDifferencePolynomial packet) :=
  supported_polyAdd_ten_local
    (bf4PacketBoundarySource_supported packet)
    (supported_polySmul_ten_local (-1)
      (bf4PacketBoundaryTarget_supported packet))

/-- Polarized normalized abstract grouped coefficient on the literal packet
carrier. -/
def abstractPhysicalNormalizedGroupedPacketLimit
    (packet : BF4HolonomyStatePacket) : CReal :=
  CReal.mul
    (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
    (CReal.add
      (abstractPhysicalNormalizedGroupedQuadraticLimit
        (bf4PacketBoundarySumPolynomial packet)
        (bf4PacketBoundarySum_supported packet))
      (CReal.neg
        (abstractPhysicalNormalizedGroupedQuadraticLimit
          (bf4PacketBoundaryDifferencePolynomial packet)
          (bf4PacketBoundaryDifference_supported packet))))

/-- The corresponding polarized genuine compact physical coefficient. -/
def compactPhysicalPacketReflectedLimit
    (packet : BF4HolonomyStatePacket) : CReal :=
  CReal.mul
    (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
    (CReal.add
      (compactPhysicalNegativeTaylorQuadraticLimit
        (bf4PacketBoundarySumPolynomial packet)
        (bf4PacketBoundarySum_supported packet))
      (CReal.neg
        (compactPhysicalNegativeTaylorQuadraticLimit
          (bf4PacketBoundaryDifferencePolynomial packet)
          (bf4PacketBoundaryDifference_supported packet))))

/-- The normalized abstract grouped packet coefficient is already the
genuine compact physical reflected coefficient. -/
theorem abstractPhysicalNormalizedGroupedPacket_equiv_compactPhysical
    (packet : BF4HolonomyStatePacket) :
    CReal.Equiv
      (abstractPhysicalNormalizedGroupedPacketLimit packet)
      (compactPhysicalPacketReflectedLimit packet) := by
  let plusGrouped :=
    abstractPhysicalNormalizedGroupedQuadraticLimit
      (bf4PacketBoundarySumPolynomial packet)
      (bf4PacketBoundarySum_supported packet)
  let minusGrouped :=
    abstractPhysicalNormalizedGroupedQuadraticLimit
      (bf4PacketBoundaryDifferencePolynomial packet)
      (bf4PacketBoundaryDifference_supported packet)
  let plusPhysical :=
    compactPhysicalNegativeTaylorQuadraticLimit
      (bf4PacketBoundarySumPolynomial packet)
      (bf4PacketBoundarySum_supported packet)
  let minusPhysical :=
    compactPhysicalNegativeTaylorQuadraticLimit
      (bf4PacketBoundaryDifferencePolynomial packet)
      (bf4PacketBoundaryDifference_supported packet)
  have hplus : CReal.Equiv plusGrouped plusPhysical :=
    abstractPhysicalNormalizedGrouped_equiv_compactPhysical
      (bf4PacketBoundarySumPolynomial packet)
      (bf4PacketBoundarySum_supported packet)
  have hminus : CReal.Equiv minusGrouped minusPhysical :=
    abstractPhysicalNormalizedGrouped_equiv_compactPhysical
      (bf4PacketBoundaryDifferencePolynomial packet)
      (bf4PacketBoundaryDifference_supported packet)
  have hpolarized :
      CReal.Equiv
        (CReal.add plusGrouped (CReal.neg minusGrouped))
        (CReal.add plusPhysical (CReal.neg minusPhysical)) :=
    CReal.Equiv.trans
      (CReal.add_congr_left hplus)
      (CReal.add_congr_right
        (CReal.neg_congr hminus))
  unfold abstractPhysicalNormalizedGroupedPacketLimit
    compactPhysicalPacketReflectedLimit
  exact CReal.Equiv.trans
    (CRealAlg.cmul_comm
      (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))
      (CReal.add plusGrouped (CReal.neg minusGrouped)))
    (CReal.Equiv.trans
      (CReal.mul_congr_left hpolarized)
      (CRealAlg.cmul_comm
        (CReal.add plusPhysical (CReal.neg minusPhysical))
        (CReal.ofQ' (Q'.mkPos 1 4 (by decide)))))

end YMGap.Continuum.BF4GroupedPhysicalActionShift

#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.groupedPositiveComponent_haar_eq_compiled
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.targetKineticFeaturePolynomial_eq_shift
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.groupedKineticCrossFeaturePolynomial_termwise
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.groupedKineticCrossFeature_haar_eq_physical
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.bf4FeatureWordWeight_eq_factorial_product
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.groupedComplementPlusAction_normal
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.groupedPositiveComplement_factorizedAction_sphere_shift
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.groupedPositiveComplement_physicalAction_sphere_shift
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.groupedPositiveComplement_haar_eq_compact_add_shift
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.bf4PacketPhysicalNormalizedGroupedLimit
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.bf4PacketPhysicalNormalizedGroupedLimit_nonnegative
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.expPos_mul_expNeg_equiv_cone
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.abstractPhysicalNormalizedGrouped_equiv_compactPhysical
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.bf4PacketBoundarySource_supported
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.bf4PacketBoundaryTarget_supported
#print axioms YMGap.Continuum.BF4GroupedPhysicalActionShift.abstractPhysicalNormalizedGroupedPacket_equiv_compactPhysical
