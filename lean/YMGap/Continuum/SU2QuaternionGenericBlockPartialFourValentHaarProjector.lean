/-
# Generic-block partial signed four-valent Haar projector

This leaf lifts the balanced fundamental fourth moment from block zero to an
arbitrary quaternion block.  Partial integration is represented honestly:
clearing a block leaves trailing-zero monomial aliases, so the local result is
first stated through their exact coefficient sum and only then transported
through an independent complex spectator.

No raw equality with a constant polynomial is asserted.  No global face
assignment space, bounded labelling family, trajectory, or double-cube trace
network is unfolded or materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
import YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector

namespace YMGap.Continuum.SU2QuaternionGenericBlockPartialFourValentHaarProjector

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RationalQuaternionRatPoly
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarSphereIdeal
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionComplexRatPolyAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarComplexReordering
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
open YMGap.Continuum.SU2QuaternionFundamentalPlaquetteTraceExpansion
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector

/-! ## 1. A block-local paired representative -/

/-- Pair each forward coefficient with one reverse coefficient.  This raw
association is chosen for the later locality proof; Haar reordering identifies
it with the canonical `F F R R` word. -/
def pairedTwoForwardTwoReverseFundamentalTerm
    (block : Nat)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) : ComplexRatPoly :=
  complexRatPolyMul
    (orientedFundamentalLinkContraction block
      firstForwardRow firstForwardColumn
      firstReverseRow firstReverseColumn)
    (orientedFundamentalLinkContraction block
      secondForwardRow secondForwardColumn
      secondReverseRow secondReverseColumn)

/-- The paired representative has the same finite-product Haar value as the
canonical left-associated `F F R R` word. -/
theorem finiteProductHaarComplex_pairedTwoForwardTwoReverse_eq_canonical
    (blockCount block : Nat)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (pairedTwoForwardTwoReverseFundamentalTerm block
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn))
      (finiteProductHaarComplex blockCount
        (twoForwardTwoReverseFundamentalTerm block
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn)) := by
  unfold pairedTwoForwardTwoReverseFundamentalTerm
    orientedFundamentalLinkContraction
    twoForwardTwoReverseFundamentalTerm complexRatPolyMulFourLeft
  refine rationalComplexEqv_trans
    (finiteProductHaarComplex_mul_four_swap blockCount
      (forwardFundamentalCoefficient block
        firstForwardRow firstForwardColumn)
      (reverseFundamentalCoefficient block
        firstReverseRow firstReverseColumn)
      (forwardFundamentalCoefficient block
        secondForwardRow secondForwardColumn)
      (reverseFundamentalCoefficient block
        secondReverseRow secondReverseColumn)) ?_
  exact rationalComplexEqv_symm
    (finiteProductHaarComplex_mul_assoc blockCount
      (complexRatPolyMul
        (forwardFundamentalCoefficient block
          firstForwardRow firstForwardColumn)
        (forwardFundamentalCoefficient block
          secondForwardRow secondForwardColumn))
      (reverseFundamentalCoefficient block
        firstReverseRow firstReverseColumn)
      (reverseFundamentalCoefficient block
        secondReverseRow secondReverseColumn))

/-- The paired representative may be canonicalized beneath an arbitrary
complex spectator.  This is a genuine contextual Haar theorem; it does not
rewrite a bare Haar equality under multiplication. -/
theorem finiteProductHaarComplex_mul_pairedTwoForwardTwoReverse_eq_canonical
    (blockCount block : Nat) (spectator : ComplexRatPoly)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (pairedTwoForwardTwoReverseFundamentalTerm block
            firstForwardRow firstForwardColumn
            secondForwardRow secondForwardColumn
            firstReverseRow firstReverseColumn
            secondReverseRow secondReverseColumn)))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (twoForwardTwoReverseFundamentalTerm block
            firstForwardRow firstForwardColumn
            secondForwardRow secondForwardColumn
            firstReverseRow firstReverseColumn
            secondReverseRow secondReverseColumn))) := by
  unfold pairedTwoForwardTwoReverseFundamentalTerm
    orientedFundamentalLinkContraction
    twoForwardTwoReverseFundamentalTerm complexRatPolyMulFourLeft
  let firstForward := forwardFundamentalCoefficient block
    firstForwardRow firstForwardColumn
  let secondForward := forwardFundamentalCoefficient block
    secondForwardRow secondForwardColumn
  let firstReverse := reverseFundamentalCoefficient block
    firstReverseRow firstReverseColumn
  let secondReverse := reverseFundamentalCoefficient block
    secondReverseRow secondReverseColumn
  have hpaired : RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (complexRatPolyMul firstForward firstReverse)
            (complexRatPolyMul secondForward secondReverse))))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul
          (complexRatPolyMul spectator firstForward)
          (complexRatPolyMul secondForward
            (complexRatPolyMul firstReverse secondReverse)))) := by
    refine rationalComplexEqv_trans
      (finiteProductHaarComplex_mul_assoc_context blockCount spectator
        (complexRatPolyMul firstForward firstReverse)
        (complexRatPolyMul secondForward secondReverse)) ?_
    refine rationalComplexEqv_trans
      (finiteProductHaarComplex_mul_four_assoc blockCount spectator
        firstForward firstReverse
        (complexRatPolyMul secondForward secondReverse)) ?_
    exact finiteProductHaarComplex_mul_adjacent_swap blockCount
      (complexRatPolyMul spectator firstForward)
      firstReverse secondForward secondReverse
  have hcanonical : RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (complexRatPolyMul
            (complexRatPolyMul
              (complexRatPolyMul firstForward secondForward)
              firstReverse)
            secondReverse)))
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul
          (complexRatPolyMul spectator firstForward)
          (complexRatPolyMul secondForward
            (complexRatPolyMul firstReverse secondReverse)))) := by
    refine rationalComplexEqv_trans
      (finiteProductHaarComplex_mul_assoc_context blockCount spectator
        (complexRatPolyMul
          (complexRatPolyMul firstForward secondForward) firstReverse)
        secondReverse) ?_
    refine rationalComplexEqv_trans
      (finiteProductHaarComplex_mul_four_assoc blockCount spectator
        (complexRatPolyMul firstForward secondForward)
        firstReverse secondReverse) ?_
    exact finiteProductHaarComplex_mul_four_assoc blockCount spectator
      firstForward secondForward
      (complexRatPolyMul firstReverse secondReverse)
  exact rationalComplexEqv_trans hpaired
    (rationalComplexEqv_symm hcanonical)

/-! ## 2. Exact arbitrary-block coefficient sum -/

/-- Exponent lookup in a raw variable monomial, retained locally so the
arbitrary block offset reduces without unfolding a symbolic replicated list. -/
private theorem exponentAt_varMono_local (source coordinate : Nat) :
    exponentAt (varMono source) coordinate =
      if coordinate = source then 1 else 0 := by
  induction source generalizing coordinate with
  | zero =>
      cases coordinate <;> rfl
  | succ source ih =>
      have hvar : varMono (source + 1) = 0 :: varMono source := by
        unfold varMono
        rw [List.replicate_succ]
        rfl
      cases coordinate with
      | zero => rfl
      | succ coordinate =>
          rw [hvar]
          simpa only [exponentAt, List.getD,
            List.getElem?_cons_succ, Nat.add_one_inj]
            using ih coordinate

private theorem exponentAt_blockVariableNat_local
    (block component query : Nat) :
    exponentAt (varMono (4 * block + component)) (4 * block + query) =
      if query = component then 1 else 0 := by
  rw [exponentAt_varMono_local]
  by_cases heq : query = component
  · simp only [heq, if_true]
  · have hcoordinate :
        4 * block + query ≠ 4 * block + component := by omega
    simp only [hcoordinate, heq, if_false]

private theorem exponentAt_blockBase_query_local
    (block query : Nat) :
    exponentAt (varMono (4 * block)) (4 * block + query) =
      if query = 0 then 1 else 0 := by
  simpa only [Nat.add_zero] using
    exponentAt_blockVariableNat_local block 0 query

private theorem exponentAt_blockComponent_base_local
    (block component : Nat) :
    exponentAt (varMono (4 * block + component)) (4 * block) =
      if 0 = component then 1 else 0 := by
  simpa only [Nat.add_zero] using
    exponentAt_blockVariableNat_local block component 0

private theorem exponentAt_blockBase_base_local (block : Nat) :
    exponentAt (varMono (4 * block)) (4 * block) = 1 := by
  simpa only [Nat.add_zero] using
    exponentAt_blockVariableNat_local block 0 0

/-- **Exact arbitrary-block signed fourth moment.**  After integrating the
selected quaternion block, the coefficient sum of the paired local word is
the same inverse-Gram projector as at block zero.  The fourth moments remain
opaque while the symbolic block offset is normalized; only the resulting
closed, finite Boolean arithmetic is decided. -/
theorem integrated_pairedTwoForwardTwoReverse_projector
    (block : Nat)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (pairedTwoForwardTwoReverseFundamentalTerm block
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn))
      (orientedFourFundamentalHaarProjector
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn) := by
  cases firstForwardRow <;> cases firstForwardColumn <;>
    cases secondForwardRow <;> cases secondForwardColumn <;>
    cases firstReverseRow <;> cases firstReverseColumn <;>
    cases secondReverseRow <;> cases secondReverseColumn <;>
    constructor <;>
      simp only [integratedComplexCoefficientSum,
        blockIntegratedCoefficientSum,
        integrateQuaternionBlock,
        integrateQuaternionBlockTerm,
        pairedTwoForwardTwoReverseFundamentalTerm,
        orientedFundamentalLinkContraction, forwardFundamentalCoefficient,
        reverseFundamentalCoefficient, complexRatPolyConj,
        fundamentalLinkQuaternion, fundamentalMatrixCoefficient, variablesAt,
        complexRatPolyMul, polyAdd, polyMul, polyNeg, polyVar, coefficientSum,
        List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.nil_append, List.cons_append,
        quaternionBlockMoment, exponentAt_monoMul,
        exponentAt_blockVariableNat_local,
        exponentAt_blockBase_query_local,
        exponentAt_blockComponent_base_local,
        exponentAt_blockBase_base_local,
        orientedFourFundamentalHaarProjector,
        orientedFourFundamentalHaarProjectorScalar,
        directOrientedPairing, crossedOrientedPairing, boolKronecker,
        oneThird, oneSixth] <;> decide

/-- The positive diagonal projector entry is block-independent already at the
raw partial-integration coefficient-sum level. -/
theorem integrated_pairedTwoForwardTwoReverse_positive_diagonal_entry
    (block : Nat) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (pairedTwoForwardTwoReverseFundamentalTerm block
          false false false false false false false false))
      (oneThird, 0) := by
  refine rationalComplexEqv_trans
    (integrated_pairedTwoForwardTwoReverse_projector block
      false false false false false false false false) ?_
  constructor <;> decide

/-- The signed mixed projector entry is likewise independent of the selected
block. This is the load-bearing arbitrary-block sign regression. -/
theorem integrated_pairedTwoForwardTwoReverse_negative_mixed_entry
    (block : Nat) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (pairedTwoForwardTwoReverseFundamentalTerm block
          false false true true true false false true))
      (-oneSixth, 0) := by
  refine rationalComplexEqv_trans
    (integrated_pairedTwoForwardTwoReverse_projector block
      false false true true true false false true) ?_
  constructor <;> decide

/-- A transpose-sensitive positive off-diagonal entry.  The correct reverse
coefficient convention gives `1/6`; omitting its row/column transpose would
give zero for these same external indices. -/
theorem integrated_pairedTwoForwardTwoReverse_transpose_sensitive_entry
    (block : Nat) :
    RationalComplexEqv
      (integratedComplexCoefficientSum block
        (pairedTwoForwardTwoReverseFundamentalTerm block
          false false false true false false true false))
      (oneSixth, 0) := by
  refine rationalComplexEqv_trans
    (integrated_pairedTwoForwardTwoReverse_projector block
      false false false true false false true false) ?_
  constructor <;> decide

/-! ## 3. Block-locality and independent-spectator lift -/

/-- The paired four-valent factor is local to its selected quaternion block. -/
theorem complexQuaternionBlockLocal_pairedTwoForwardTwoReverseFundamentalTerm
    (block : Nat)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) :
    ComplexQuaternionBlockLocal block
      (pairedTwoForwardTwoReverseFundamentalTerm block
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn) := by
  unfold pairedTwoForwardTwoReverseFundamentalTerm
  exact complexQuaternionBlockLocal_mul
    (complexQuaternionBlockLocal_orientedFundamentalLinkContraction block
      firstForwardRow firstForwardColumn
      firstReverseRow firstReverseColumn)
    (complexQuaternionBlockLocal_orientedFundamentalLinkContraction block
      secondForwardRow secondForwardColumn
      secondReverseRow secondReverseColumn)

/-- **Arbitrary-block signed projector with an independent spectator.** -/
theorem genericBlock_pairedTwoForwardTwoReverse_projector_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent :
      ComplexQuaternionBlockIndependent block spectator)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (pairedTwoForwardTwoReverseFundamentalTerm block
            firstForwardRow firstForwardColumn
            secondForwardRow secondForwardColumn
            firstReverseRow firstReverseColumn
            secondReverseRow secondReverseColumn)))
      (SU2QuaternionGenericBlockPartialFundamentalSchur.rationalComplexMul
        (finiteProductHaarComplex blockCount spectator)
        (orientedFourFundamentalHaarProjector
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn)) := by
  exact genericBlock_localFactor_with_complex_spectator
    blockCount block hblock spectator
    (pairedTwoForwardTwoReverseFundamentalTerm block
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn)
    hindependent
    (complexQuaternionBlockLocal_pairedTwoForwardTwoReverseFundamentalTerm
      block firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn)
    (orientedFourFundamentalHaarProjector
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn)
    (integrated_pairedTwoForwardTwoReverse_projector block
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn)

/-- Canonical `F F R R` form of the arbitrary-block signed projector with an
independent spectator. -/
theorem genericBlock_twoForwardTwoReverse_projector_with_complex_spectator
    (blockCount block : Nat) (hblock : block < blockCount)
    (spectator : ComplexRatPoly)
    (hindependent :
      ComplexQuaternionBlockIndependent block spectator)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn : Bool) :
    RationalComplexEqv
      (finiteProductHaarComplex blockCount
        (complexRatPolyMul spectator
          (twoForwardTwoReverseFundamentalTerm block
            firstForwardRow firstForwardColumn
            secondForwardRow secondForwardColumn
            firstReverseRow firstReverseColumn
            secondReverseRow secondReverseColumn)))
      (SU2QuaternionGenericBlockPartialFundamentalSchur.rationalComplexMul
        (finiteProductHaarComplex blockCount spectator)
        (orientedFourFundamentalHaarProjector
          firstForwardRow firstForwardColumn
          secondForwardRow secondForwardColumn
          firstReverseRow firstReverseColumn
          secondReverseRow secondReverseColumn)) := by
  refine rationalComplexEqv_trans
    (rationalComplexEqv_symm
      (finiteProductHaarComplex_mul_pairedTwoForwardTwoReverse_eq_canonical
        blockCount block spectator
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn)) ?_
  exact genericBlock_pairedTwoForwardTwoReverse_projector_with_complex_spectator
    blockCount block hblock spectator hindependent
    firstForwardRow firstForwardColumn
    secondForwardRow secondForwardColumn
    firstReverseRow firstReverseColumn
    secondReverseRow secondReverseColumn

#print axioms finiteProductHaarComplex_pairedTwoForwardTwoReverse_eq_canonical
#print axioms finiteProductHaarComplex_mul_pairedTwoForwardTwoReverse_eq_canonical
#print axioms integrated_pairedTwoForwardTwoReverse_projector
#print axioms integrated_pairedTwoForwardTwoReverse_positive_diagonal_entry
#print axioms integrated_pairedTwoForwardTwoReverse_negative_mixed_entry
#print axioms integrated_pairedTwoForwardTwoReverse_transpose_sensitive_entry
#print axioms complexQuaternionBlockLocal_pairedTwoForwardTwoReverseFundamentalTerm
#print axioms genericBlock_pairedTwoForwardTwoReverse_projector_with_complex_spectator
#print axioms genericBlock_twoForwardTwoReverse_projector_with_complex_spectator

end YMGap.Continuum.SU2QuaternionGenericBlockPartialFourValentHaarProjector
