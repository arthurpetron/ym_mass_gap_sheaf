/-
# Explicit inner regularity of the strict-cylinder OS pairing

The completed-pairing construction needs Type-level approximation cutoffs for
each `CReal` term.  The legacy `CReal.cauchy` field only asserts such a cutoff
inside `Prop`, so it cannot be extracted without choice.  Here we package the
already proved geometric half-power estimate for the strict quadratic as
explicit `CReal.InnerRegularity` data and propagate it through polarization.

This is analytic bookkeeping for the actual OS form, not finite enumeration.
-/

import YMGap.Constructive.CRealInnerRegularity
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealBilinearInnerRegularity

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOSDistanceContraction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

private theorem two_sided_add_of_abs_sub_le_local
    {a b epsilon : Q'} (h : Q'.abs (a + (-b)) <= epsilon) :
    a <= b + epsilon /\ b <= a + epsilon := by
  constructor
  · exact ExpNeg.le_add_of_abs_sub_le h
  · apply ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a)) h

/-! ## 1. Explicit regularity of the fixed strict quadratic -/

/-- The geometric half-power cutoff from the fixed quadratic limit, retained
as Type-level data rather than hidden under `CReal.cauchy`. -/
def centralNormalizedStrictJointFixedQuadraticInnerRegularity
    (coupling : Q') (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} {roots : List (List Nat)}
    (hroots : forall root, root ∈ roots ->
      root ∈ canonicalSurfacePolymers base)
    (coefficient : List Bool -> Q') :
    CReal.InnerRegularity
      (centralNormalizedStrictJointFixedQuadraticLimit
        coupling hcoupling hle hroots coefficient) where
  rate tolerance :=
    (tolerance * Q'.invSucc
      (strictJointFixedQuadraticCauchyCoefficient
        roots coefficient).num.toNat).den
  regular := by
    intro tolerance htolerance m n hm hn
    let cauchyCoefficient :=
      strictJointFixedQuadraticCauchyCoefficient roots coefficient
    let scaledTolerance :=
      tolerance * Q'.invSucc cauchyCoefficient.num.toNat
    have hcoefficient : (0 : Q') <= cauchyCoefficient :=
      strictJointFixedQuadraticCauchyCoefficient_nonnegative
        roots coefficient
    have hscaledPositive : (0 : Q') < scaledTolerance :=
      Q'.mul_pos htolerance
        (Q'.invSucc_pos cauchyCoefficient.num.toNat)
    have hscaledFinal : cauchyCoefficient * scaledTolerance <= tolerance :=
      ExpNeg.mul_le_of_mul_invSucc_toNat cauchyCoefficient tolerance
        hcoefficient (Q'.le_of_lt htolerance)
    rcases Nat.le_total m n with hmn | hnm
    · have hpair :=
        centralNormalizedStrictJointFixedQuadraticSequence_pair_abs_le
          hcoupling hle hmn hroots coefficient
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hm
      have hhalf : HalfPow.half ^ m <=
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den <=
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ m) scaledTolerance cauchyCoefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (centralNormalizedStrictJointFixedQuadraticSequence
              coupling hcoupling base roots coefficient n +
            (-centralNormalizedStrictJointFixedQuadraticSequence
              coupling hcoupling base roots coefficient m)) <= tolerance :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      have htwo := two_sided_add_of_abs_sub_le_local habs
      exact ⟨htwo.2, htwo.1⟩
    · have hpair :=
        centralNormalizedStrictJointFixedQuadraticSequence_pair_abs_le
          hcoupling hle hnm hroots coefficient
      obtain ⟨offset, hoffset⟩ := Nat.exists_eq_add_of_le hn
      have hhalf : HalfPow.half ^ n <=
          HalfPow.half ^ scaledTolerance.den := by
        rw [hoffset]
        exact ExpNeg.pow_half_antitone scaledTolerance.den offset
      have hhalfTolerance : HalfPow.half ^ scaledTolerance.den <=
          scaledTolerance :=
        HalfPow.pow_half_le scaledTolerance hscaledPositive
      have hscaled := Q'.mul_le_mul_of_nonneg_left
        (HalfPow.half ^ n) scaledTolerance cauchyCoefficient
        (Q'.le_trans' _ _ _ hhalf hhalfTolerance) hcoefficient
      have habs : Q'.abs
          (centralNormalizedStrictJointFixedQuadraticSequence
              coupling hcoupling base roots coefficient m +
            (-centralNormalizedStrictJointFixedQuadraticSequence
              coupling hcoupling base roots coefficient n)) <= tolerance :=
        Q'.le_trans' _ _ _ hpair
          (Q'.le_trans' _ _ _ hscaled hscaledFinal)
      exact two_sided_add_of_abs_sub_le_local habs

/-- Every strict cylinder quadratic carries its explicit geometric inner
regularity modulus. -/
def strictJointCylinderReflectionQuadraticInnerRegularity
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base) :
    CReal.InnerRegularity (vector.reflectionQuadratic hcoupling hle) :=
  centralNormalizedStrictJointFixedQuadraticInnerRegularity
    coupling hcoupling hle vector.rootsCanonical vector.coefficient

/-! ## 2. Explicit regularity of the polarized pairing -/

/-- Polarization preserves explicit inner regularity. -/
def strictJointCylinderReflectionBilinearInnerRegularity
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) :
    CReal.InnerRegularity
      (strictJointCylinderReflectionBilinear hcoupling hle left right) :=
  CReal.InnerRegularity.scaleLeft
    (CReal.InnerRegularity.add
      (strictJointCylinderReflectionQuadraticInnerRegularity
        hcoupling hle (left.add right))
      (CReal.InnerRegularity.neg
        (strictJointCylinderReflectionQuadraticInnerRegularity
          hcoupling hle (left.add (right.smul (-1))))))
    strictJointPolarizationQuarter (by decide)

/-- The staged maximum-common-base pairing inherits explicit inner
regularity. -/
def strictJointCylinderStageReflectionBilinearInnerRegularity
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.InnerRegularity
      (strictJointCylinderStageReflectionBilinear
        hcoupling hle left right) :=
  strictJointCylinderReflectionBilinearInnerRegularity hcoupling hle
    (boxTransportStrictJointCylinderVector
      (Nat.le_max_left left.base right.base) left.vector)
    (boxTransportStrictJointCylinderVector
      (Nat.le_max_right left.base right.base) right.vector)

/-! ## 3. Explicit regularity of the squared distance -/

/-- The fixed-base OS squared distance is the quadratic of the presentation
difference, hence inherits the same explicit half-power modulus. -/
def strictJointCylinderReflectionDistSqInnerRegularity
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) :
    CReal.InnerRegularity
      (strictJointCylinderReflectionDistSq hcoupling hle left right) :=
  strictJointCylinderReflectionQuadraticInnerRegularity hcoupling hle
    (strictJointCylinderDifference left right)

/-- The maximum-common-base staged squared distance also has a computable
inner modulus. -/
def strictJointCylinderStageReflectionDistSqInnerRegularity
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.InnerRegularity
      (strictJointCylinderStageReflectionDistSq hcoupling hle left right) :=
  strictJointCylinderReflectionDistSqInnerRegularity hcoupling hle
    (boxTransportStrictJointCylinderVector
      (Nat.le_max_left left.base right.base) left.vector)
    (boxTransportStrictJointCylinderVector
      (Nat.le_max_right left.base right.base) right.vector)

#print axioms centralNormalizedStrictJointFixedQuadraticInnerRegularity
#print axioms strictJointCylinderReflectionQuadraticInnerRegularity
#print axioms strictJointCylinderReflectionBilinearInnerRegularity
#print axioms strictJointCylinderStageReflectionBilinearInnerRegularity
#print axioms strictJointCylinderReflectionDistSqInnerRegularity
#print axioms strictJointCylinderStageReflectionDistSqInnerRegularity

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealBilinearInnerRegularity
