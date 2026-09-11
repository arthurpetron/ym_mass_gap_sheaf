/-
# Core carrier for the arbitrary-block six-valent Haar projector

This lightweight leaf fixes the exact partial-integration statement for the
literal `F F F R R R` word at a symbolic quaternion block.  The closed Boolean
arithmetic is compiled in separate, serially chained fibers so no declaration
asks Lean to elaborate all 4,096 external-index configurations at once.

The locality theorem is structural and is shared by the later independent-
spectator lift.  No bounded assignment family or twelve-Bool sum is
materialized.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport
import YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjectorCore

namespace YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjector

open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionGenericBlockPartialFundamentalSchur
open YMGap.Continuum.SU2QuaternionGenericBlockFundamentalCoefficientSupport
open YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector
open YMGap.Continuum.SU2QuaternionSixValentPairingGram

/-- Proposition evaluated by the sixteen serially compiled 256-case fibers.
It states the exact arbitrary-block coefficient-sum form of the balanced
fundamental sixth moment. -/
def GenericBlockPartialSixValentProjectorStatement
    (block : Nat)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) : Prop :=
  RationalComplexEqv
    (integratedComplexCoefficientSum block
      (threeForwardThreeReverseFundamentalTerm block
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn))
    (orientedSixFundamentalHaarProjector
      firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn)

/-- The literal six-coefficient word is supported entirely on its selected
quaternion block.  The proof follows the actual left association of the raw
polynomial product and never expands a coefficient. -/
theorem complexQuaternionBlockLocal_threeForwardThreeReverseFundamentalTerm
    (block : Nat)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) :
    ComplexQuaternionBlockLocal block
      (threeForwardThreeReverseFundamentalTerm block
        firstForwardRow firstForwardColumn
        secondForwardRow secondForwardColumn
        thirdForwardRow thirdForwardColumn
        firstReverseRow firstReverseColumn
        secondReverseRow secondReverseColumn
        thirdReverseRow thirdReverseColumn) := by
  unfold threeForwardThreeReverseFundamentalTerm complexRatPolyMulSixLeft
  exact complexQuaternionBlockLocal_mul
    (complexQuaternionBlockLocal_mul
      (complexQuaternionBlockLocal_mul
        (complexQuaternionBlockLocal_mul
          (complexQuaternionBlockLocal_mul
            (complexQuaternionBlockLocal_forwardFundamentalCoefficient
              block firstForwardRow firstForwardColumn)
            (complexQuaternionBlockLocal_forwardFundamentalCoefficient
              block secondForwardRow secondForwardColumn))
          (complexQuaternionBlockLocal_forwardFundamentalCoefficient
            block thirdForwardRow thirdForwardColumn))
        (complexQuaternionBlockLocal_reverseFundamentalCoefficient
          block firstReverseRow firstReverseColumn))
      (complexQuaternionBlockLocal_reverseFundamentalCoefficient
        block secondReverseRow secondReverseColumn))
    (complexQuaternionBlockLocal_reverseFundamentalCoefficient
      block thirdReverseRow thirdReverseColumn)

#print axioms complexQuaternionBlockLocal_threeForwardThreeReverseFundamentalTerm

end YMGap.Continuum.SU2QuaternionGenericBlockPartialSixValentHaarProjector
