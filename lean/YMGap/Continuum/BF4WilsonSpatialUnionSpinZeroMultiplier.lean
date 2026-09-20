/-
# Spin-zero character multiplier is the identity on the SAME Wilson completion

The spin-zero character is literally the constant polynomial one.  Its
lifted source image therefore gives the existing padded source identity, which
descends through the original union seminorm to an all-input completed map.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
import YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra

namespace YMGap.Continuum.BF4WilsonSpatialUnionSpinZeroMultiplier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop sourceCharacter)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier
open YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity
open YMGap.Continuum.BF4WilsonSpatialUnionObservableDescent
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_one)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyOne)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4GeometricSpinNetworkMehler (characterPolynomial)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs

private theorem spinZero_source_identity {base H : Nat} (L : SourceLoop base)
    (z : IntrinsicExpression base) (hz : z.radius ≤ H) :
    PaddedPolynomialCoeffEqv ((H+1) * (List.length (baseLinks base)))
      (sourcePolynomial (chart H (BF4WilsonTimeZeroIntrinsicMultiplier.multiply L 0 z)))
      (sourcePolynomial (chart H z)) := by
  rw [BF4WilsonTimeZeroIntrinsicMultiplier.chart_multiply H L 0 z hz]
  have hloop : PaddedPolynomialCoeffEqv ((H+1) * (List.length (baseLinks base)))
      (sourcePolynomial (.loop H L 0)) polyOne := by
    simpa only [sourcePolynomial, sourceCharacter, characterPolynomial, Nat.mul_zero,
      Nat.zero_add] using
      (lift_one ((H+1) * (List.length (baseLinks base)))
        (H * List.length (baseLinks base)))
  exact (hloop.mul (PaddedPolynomialCoeffEqv.refl _ _)).trans
    (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.one_mul _))

theorem completedMultiply_spin_zero {base : Nat} (L : SourceLoop base) (x : V) :
    completedMultiply hw0 hw1 hsmall hd hs L 0 x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  apply Quotient.sound
  refine ⟨CRealSeminormCompletion.SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun k => ?_)⟩
  let y := X.seq k
  let N := max base y.base
  have hL : base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have hN : 0 < N := Nat.lt_of_lt_of_le y.positive hy
  let z := atBase y hy
  let m : IntrinsicExpression N :=
    BF4WilsonTimeZeroIntrinsicMultiplier.multiply (loopAt L hL) 0 z
  have hmul : atBase (multiplyStage L 0 y)
      (Nat.max_le.mpr ⟨hL, hy⟩) = m := by
    simpa only [m, z] using atBase_multiply L 0 y hL hy
  have hybase : atBase y hy = z := rfl
  change Equiv (distSq hw0 hw1 hsmall hd hs (multiplyStage L 0 y) y) czero
  have hpin := distSq_at_base hw0 hw1 hsmall hd hs
    (multiplyStage L 0 y) y N (Nat.max_le.mpr ⟨hL,hy⟩) hy
  rw [hmul, hybase] at hpin
  have hpoly := spinZero_source_identity (loopAt L hL) z (Nat.le_refl _)
  have hzero := intrinsic_distSq_zero_of_padded_diagonal
    hw0 hw1 hsmall hd hs hN z.radius m z (Nat.le_refl _) (Nat.le_refl _)
    (fun n => chartInsertion_source_congr n z.radius n
      (chart z.radius m) (chart z.radius z)
      (chart_within z.radius m (Nat.le_refl _))
      (chart_within z.radius z (Nat.le_refl _)) hpoly)
  exact hpin.trans hzero

#print axioms completedMultiply_spin_zero

end YMGap.Continuum.BF4WilsonSpatialUnionSpinZeroMultiplier
