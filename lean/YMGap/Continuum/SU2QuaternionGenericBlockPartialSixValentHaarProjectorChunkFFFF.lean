/- One serially compiled 256-case fiber with the first four selectors `0000`. -/

import YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjectorCore

namespace YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjector

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
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
open YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport
open YMGap.Continuum.SU2QuaternionOneLinkFourValentHaarProjector
open YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector
open YMGap.Continuum.SU2QuaternionSixValentPairingGram

/-- Shared kernel-computational closer for one 256-case fiber.  Keeping this
recipe in the first serial chunk gives every later fiber identical reduction
boundaries without putting multiple fibers in one Lean process. -/
syntax "solve_generic_block_partial_six_valent_fiber "
  Lean.Parser.Tactic.elimTarget ", " Lean.Parser.Tactic.elimTarget ", "
  Lean.Parser.Tactic.elimTarget ", " Lean.Parser.Tactic.elimTarget ", "
  Lean.Parser.Tactic.elimTarget ", " Lean.Parser.Tactic.elimTarget ", "
  Lean.Parser.Tactic.elimTarget ", " Lean.Parser.Tactic.elimTarget : tactic

macro_rules
  | `(tactic| solve_generic_block_partial_six_valent_fiber
      $thirdForwardRow, $thirdForwardColumn,
      $firstReverseRow, $firstReverseColumn,
      $secondReverseRow, $secondReverseColumn,
      $thirdReverseRow, $thirdReverseColumn) =>
    `(tactic|
      (cases $thirdForwardRow <;> cases $thirdForwardColumn <;>
      cases $firstReverseRow <;> cases $firstReverseColumn <;>
      cases $secondReverseRow <;> cases $secondReverseColumn <;>
      cases $thirdReverseRow <;> cases $thirdReverseColumn <;>
      constructor <;>
        simp only [integratedComplexCoefficientSum,
          blockIntegratedCoefficientSum,
          integrateQuaternionBlock, integrateQuaternionBlockTerm,
          threeForwardThreeReverseFundamentalTerm, complexRatPolyMulSixLeft,
          forwardFundamentalCoefficient, reverseFundamentalCoefficient,
          complexRatPolyConj, fundamentalLinkQuaternion,
          fundamentalMatrixCoefficient, variablesAt,
          complexRatPolyMul, polyAdd, polyMul, polyNeg, polyVar, coefficientSum,
          List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.nil_append, List.cons_append,
          quaternionBlockMoment, exponentAt_monoMul,
          exponentAt_blockVariableNat, exponentAt_blockBase_query,
          exponentAt_blockComponent_base, exponentAt_blockBase_base,
          orientedSixFundamentalHaarProjector,
          orientedSixFundamentalHaarProjectorScalar,
          sixValentPairingSum, sixValentPairingGramInverse,
          tripleOrientedPairing, boolKronecker,
          oneQuarter, oneTwelfth, oneThird, oneSixth] <;>
        decide))

theorem genericBlock_partial_sixValent_chunk_ffff
    (block : Nat)
    (thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    GenericBlockPartialSixValentProjectorStatement block
      false false false false
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn := by
  solve_generic_block_partial_six_valent_fiber
    thirdForwardRow, thirdForwardColumn,
    firstReverseRow, firstReverseColumn,
    secondReverseRow, secondReverseColumn,
    thirdReverseRow, thirdReverseColumn

#print axioms genericBlock_partial_sixValent_chunk_ffff

end YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjector
