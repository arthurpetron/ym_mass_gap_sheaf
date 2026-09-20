/-
# Original chronological kernels concatenate on every completed input

Compose a duration-K original window with a duration-H original window.
The resulting operator is exactly the duration-(H+K) kernel of their graft:
the later observable is shifted by K and multiplied by the earlier one.

The proof first identifies both actions on arbitrary original finite windows,
then uses coherent spatial inclusions and the separating completed pairing.
This is an actual gluing law on the existing Wilson carrier, not an equality
only on the vacuum. No continuum time calibration or OS/QFT closure is claimed.
-/

import YMGap.Continuum.BF4WilsonKernelOriginalInputs

namespace YMGap.Continuum.BF4WilsonKernelConcatenation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear
open YMGap.Continuum.BF4WilsonSpatialUnionSourceIdentity (embedWindow_eq_of_source_identity)
open YMGap.Continuum.BF4WilsonWindowOperatorPins
open YMGap.Continuum.BF4WilsonChronologicalProgram
open YMGap.Continuum.BF4WilsonChronologicalOperator
open YMGap.Continuum.BF4WilsonChronologicalCompositionSyntax
open YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra
open YMGap.Continuum.BF4WilsonChronologicalKernel
open YMGap.Continuum.BF4WilsonChronologicalBaseCoherence
open YMGap.Continuum.BF4WilsonKernelInclusionSyntax
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

theorem includeExpression_graft {base larger : Nat} (h : base ≤ larger)
    (K : Nat) (e f : WindowExpression base) :
    includeExpression h (graft K e f) =
      graft K (includeExpression h e) (includeExpression h f) := by
  simp only [graft, includeExpression_mul, shift, includeExpression_mapOffsets]

theorem graft_assoc_source {base : Nat} (K R : Nat) (e f z : WindowExpression base) :
    RatPolyCoeffEqv (sourcePolynomial (graft (K+R) e (graft R f z)))
      (sourcePolynomial (graft R (graft K e f) z)) := by
  change RatPolyCoeffEqv
    (polyMul (sourcePolynomial (shift (K+R) e))
      (polyMul (sourcePolynomial (shift R f)) (sourcePolynomial z)))
    (polyMul (sourcePolynomial (.mul (shift R (shift K e)) (shift R f))) (sourcePolynomial z))
  rw [shift_comp]
  exact (RatPolyCoeffEqv.mul_assoc _ _ _).symm

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "E" => embedStage hw0 hw1 hsmall hd hs
local notation "Op" => act hw0 hw1 hsmall hd hs
local notation "Adj" => adjointAct hw0 hw1 hsmall hd hs

private theorem eq_of_stage_pairings (x y : V)
    (h : ∀ z : Stage, B x (E z) = B y (E z)) : x = y := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  revert h
  refine Quotient.inductionOn₃ x y z ?_
  intro X Y Z h
  apply Quotient.sound
  apply CRealSeminormPairingCompletion.representativeInner_eq_of_right_stage_pairings
    (pairingData hw0 hw1 hsmall hd hs) X Y Z
  intro stage
  exact Quotient.exact (h stage)

private theorem operatorEq_of_stage_inputs {base : Nat} (p q : Program base)
    (h : ∀ z : Stage, Op p (E z) = Op q (E z)) :
    OperatorEq hw0 hw1 hsmall hd hs p q := by
  have hadj (test : V) : Adj p test = Adj q test := by
    apply eq_of_stage_pairings hw0 hw1 hsmall hd hs
    intro z
    rw [completedInner_symm hw0 hw1 hsmall hd hs (Adj p test),
      completedInner_symm hw0 hw1 hsmall hd hs (Adj q test),
      ← adjoint_balance, ← adjoint_balance, h z]
  intro x
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro test
  rw [adjoint_balance, adjoint_balance, hadj test]

theorem compileKernel_concat_onWindow {base : Nat} (hb : 0 < base) (H K R : Nat)
    (e f z : WindowExpression base) (he : Within H e) (hf : Within K f) (hz : Within R z) :
    Op (compileKernel H e) (Op (compileKernel K f) (embedWindow hw0 hw1 hsmall hd hs hb R z hz)) =
      Op (compileKernel (H+K) (graft K e f)) (embedWindow hw0 hw1 hsmall hd hs hb R z hz) := by
  rw [compileKernel_graft hw0 hw1 hsmall hd hs hb K R f z hf hz,
    compileKernel_graft hw0 hw1 hsmall hd hs hb H (K+R) e (graft R f z) he (graft_within f z hf hz),
    compileKernel_graft hw0 hw1 hsmall hd hs hb (H+K) R (graft K e f) z (graft_within e f he hf) hz]
  have h := embedWindow_eq_of_source_identity hw0 hw1 hsmall hd hs hb ((H+K)+R)
    (graft (K+R) e (graft R f z)) (graft R (graft K e f) z)
    (by simpa only [Nat.add_assoc] using graft_within e (graft R f z) he (graft_within f z hf hz))
    (graft_within (graft K e f) z (graft_within e f he hf) hz)
    (PaddedPolynomialCoeffEqv.of_coeff (graft_assoc_source K R e f z))
  simpa only [Nat.add_assoc] using h

/-- SAME original kernels, every completion input, with the exact discrete duration. -/
theorem compileKernel_concat {base : Nat} (H K : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within K f) (x : V) :
    Op (compileKernel H e) (Op (compileKernel K f) x) =
      Op (compileKernel (H+K) (graft K e f)) x := by
  have h : OperatorEq hw0 hw1 hsmall hd hs
      (compose (compileKernel H e) (compileKernel K f))
      (compileKernel (H+K) (graft K e f)) := by
    apply operatorEq_of_stage_inputs hw0 hw1 hsmall hd hs
    intro z
    let N := max base z.base
    have hb : base ≤ N := Nat.le_max_left _ _
    have hz : z.base ≤ N := Nat.le_max_right _ _
    rw [act_compose, embedStage_atBase hw0 hw1 hsmall hd hs z hz,
      ← act_includeProgram hw0 hw1 hsmall hd hs hb (compileKernel H e),
      ← act_includeProgram hw0 hw1 hsmall hd hs hb (compileKernel K f),
      ← act_includeProgram hw0 hw1 hsmall hd hs hb (compileKernel (H+K) (graft K e f)),
      includeProgram_compileKernel, includeProgram_compileKernel, includeProgram_compileKernel,
      includeExpression_graft]
    exact compileKernel_concat_onWindow hw0 hw1 hsmall hd hs
      (Nat.lt_of_lt_of_le z.positive hz) H K (atBase z hz).radius
      (includeExpression hb e) (includeExpression hb f) (atBase z hz).expression
      ((includeExpression_within hb H e).mpr he) ((includeExpression_within hb K f).mpr hf)
      (atBase z hz).within
  simpa only [act_compose] using h x

end YMGap.Continuum.BF4WilsonKernelConcatenation

#print axioms YMGap.Continuum.BF4WilsonKernelConcatenation.includeExpression_graft
#print axioms YMGap.Continuum.BF4WilsonKernelConcatenation.graft_assoc_source
#print axioms YMGap.Continuum.BF4WilsonKernelConcatenation.compileKernel_concat_onWindow
#print axioms YMGap.Continuum.BF4WilsonKernelConcatenation.compileKernel_concat
