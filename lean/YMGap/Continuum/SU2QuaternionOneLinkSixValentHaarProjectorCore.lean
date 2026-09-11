/-
# Core carrier for the one-link six-valent Haar projector

This lightweight leaf fixes the literal `F F F R R R` polynomial word and
the exact inverse-Gram target.  The 4096 Boolean configurations are proved in
four separately compiled, serially imported chunk modules.
-/

import YMGap.Continuum.SU2QuaternionSixValentPairingGram

namespace YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector

open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchur
open YMGap.Continuum.SU2QuaternionSixValentPairingGram

/-- Left-associated product of six honest complex rational polynomials. -/
def complexRatPolyMulSixLeft
    (first second third fourth fifth sixth : ComplexRatPoly) :
    ComplexRatPoly :=
  complexRatPolyMul
    (complexRatPolyMul
      (complexRatPolyMul
        (complexRatPolyMul
          (complexRatPolyMul first second) third) fourth) fifth) sixth

/-- Three forward followed by three reverse fundamental coefficients on one
quaternion block. -/
def threeForwardThreeReverseFundamentalTerm
    (block : Nat)
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) : ComplexRatPoly :=
  complexRatPolyMulSixLeft
    (forwardFundamentalCoefficient block
      firstForwardRow firstForwardColumn)
    (forwardFundamentalCoefficient block
      secondForwardRow secondForwardColumn)
    (forwardFundamentalCoefficient block
      thirdForwardRow thirdForwardColumn)
    (reverseFundamentalCoefficient block
      firstReverseRow firstReverseColumn)
    (reverseFundamentalCoefficient block
      secondReverseRow secondReverseColumn)
    (reverseFundamentalCoefficient block
      thirdReverseRow thirdReverseColumn)

/-- Proposition evaluated by the sixteen bounded proof chunks. -/
def OneLinkSixValentProjectorStatement
    (firstForwardRow firstForwardColumn
      secondForwardRow secondForwardColumn
      thirdForwardRow thirdForwardColumn
      firstReverseRow firstReverseColumn
      secondReverseRow secondReverseColumn
      thirdReverseRow thirdReverseColumn : Bool) : Prop :=
  RationalComplexEqv
    (finiteProductHaarComplex 1
      (threeForwardThreeReverseFundamentalTerm 0
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

end YMGap.Continuum.SU2QuaternionOneLinkSixValentHaarProjector
