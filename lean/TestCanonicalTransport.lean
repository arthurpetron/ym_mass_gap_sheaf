import YMGap.Continuum.SU2QuaternionCanonicalEightWilsonWeight
import YMGap.Continuum.SU2QuaternionWilsonReferenceWeight

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
open YMGap.Continuum.SU2QuaternionCanonicalEightHaar
open YMGap.Continuum.SU2QuaternionCanonicalEightWilsonWeight
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionHaarSphereIdeal

local infix:50 " ≈ " => Q'.eqv

example (t : Term8) :
    productHaarLinearSum
        (polyMul [embedTerm8 t] (embedPoly8 retainedRelativeWeight8)) ≈
      productHaarLinearSum
        (polyMul [embedTerm8 t] retainedRelativeWeight) := by
  simp [embedPoly8, retainedRelativeWeight8,
    relativeFundamentalCharacter8, relativeDot8, crossCoordinate8,
    crossMono8, basisMono8, gIndex8, hIndex8,
    retainedRelativeWeight, relativeFundamentalCharacter, relativeDot,
    gCoordinate, hCoordinate, polyAdd8, polySmul8, polyOne8,
    polyAdd, polySmul, polyOne, polyVar, polyMul, productHaarLinearSum,
    productHaarMono, exponentAt, allZero, mono8ToList, monoMul]
  constructor <;> omega

