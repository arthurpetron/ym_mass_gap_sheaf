/-
# Finite source-Haar identities determine the SAME completed Wilson kernel

One supported Haar identity on the original source window suffices. The graft
transport theorem carries it through every larger input chart, retaining the
original reflected test and interacting action. Existing null descent gives
equal grafted states. The original-input kernel pin and dense-stage operator
criterion then prove equality on EVERY completed input.

This is observable-presentation descent for the duration-preserving compiler,
not the disproved extension of the old vacuum-vector compiler. The concrete
backtrack sphere identity supplies an unconditional physical-loop instance.
Only fixed-spacing guarded SU(2) Wilson-window syntax is covered; no full
gauge-observable coverage, canonical continuum OS root or Clay claim follows.
-/

import YMGap.Continuum.BF4WilsonGraftHaarTransport
import YMGap.Continuum.BF4WilsonKernelConcatenation

namespace YMGap.Continuum.BF4WilsonKernelHaarIdentity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (chart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionLinear
open YMGap.Continuum.BF4WilsonSpatialUnionLinearLaws (completedSmul_one completedTime_smul)
open YMGap.Continuum.BF4WilsonSpatialUnionBilinear (completedAdd_zero)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeZeroMultiplier (completedMultiply)
open YMGap.Continuum.BF4WilsonSpatialUnionHaarObservableDescent (embedStage_eq_of_haar_diagonal)
open YMGap.Continuum.BF4WilsonChronologicalOperator
open YMGap.Continuum.BF4WilsonChronologicalOperatorAlgebra
open YMGap.Continuum.BF4WilsonChronologicalKernel
open YMGap.Continuum.BF4WilsonKernelOriginalInputs
open YMGap.Continuum.BF4WilsonKernelConcatenation (operatorEq_of_stage_inputs)
open YMGap.Continuum.BF4WilsonGraftHaarTransport (chart_graft_haar_congr)
open YMGap.Continuum.BF4WilsonExpressionExpansion (expand)
open YMGap.Continuum.BF4WilsonTimedWordOrder (orderWord insertWord)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

local notation:max "N" base:arg => List.length (baseLinks base)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "E" => embedStage hw0 hw1 hsmall hd hs
local notation "Op" => act hw0 hw1 hsmall hd hs

/-- Every finite original input may have a different base and radius. -/
theorem graftStage_haar_congr {base : Nat} (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f)
    (hp : SupportedHaarEqv ((H+1)*(N base)) (sourcePolynomial e) (sourcePolynomial f))
    (x : Stage) : E (graftStage H e he x) = E (graftStage H f hf x) := by
  let larger := max base x.base
  have hb : base ≤ larger := Nat.le_max_left _ _
  have hx : x.base ≤ larger := Nat.le_max_right _ _
  have hN : 0 < larger := Nat.lt_of_lt_of_le x.positive hx
  let z := atBase x hx
  have hep := (includeExpression_within hb H e).mpr he
  have hfp := (includeExpression_within hb H f).mpr hf
  have h := embedStage_eq_of_haar_diagonal hw0 hw1 hsmall hd hs hN (H+z.radius)
    ⟨H+z.radius, graft z.radius (includeExpression hb e) z.expression, graft_within _ _ hep z.within⟩
    ⟨H+z.radius, graft z.radius (includeExpression hb f) z.expression, graft_within _ _ hfp z.within⟩
    (Nat.le_refl _) (Nat.le_refl _) (fun n => by
      simpa only [chart, Nat.sub_self, shift_zero] using
        chart_graft_haar_congr hb H z.radius n n e f he hf hp z.expression)
  exact h

/-- ONE finite source identity gives equality of the actual kernels on ALL
completion inputs. No family of regulator-indexed equalities is supplied. -/
theorem compileKernel_haar_congr {base : Nat} (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f)
    (hp : SupportedHaarEqv ((H+1)*(N base)) (sourcePolynomial e) (sourcePolynomial f)) :
    OperatorEq hw0 hw1 hsmall hd hs (compileKernel H e) (compileKernel H f) := by
  apply operatorEq_of_stage_inputs hw0 hw1 hsmall hd hs
  intro x
  rw [compileKernel_stage_pin hw0 hw1 hsmall hd hs H e he,
    compileKernel_stage_pin hw0 hw1 hsmall hd hs H f hf]
  exact graftStage_haar_congr hw0 hw1 hsmall hd hs H e f he hf hp x

theorem compileKernel_padded_congr {base : Nat} (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f)
    (hp : PaddedPolynomialCoeffEqv ((H+1)*(N base)) (sourcePolynomial e) (sourcePolynomial f)) :
    OperatorEq hw0 hw1 hsmall hd hs (compileKernel H e) (compileKernel H f) :=
  compileKernel_haar_congr hw0 hw1 hsmall hd hs H e f he hf
    (SupportedHaarEqv.of_padded hp (source_supported H e he) (source_supported H f hf))

open BF4WilsonBacktrackSourceIdentity

/-- A genuine sphere identity, not free-polynomial equality: the character
of forward/reverse traversal acts as twice the identity on the SAME carrier. -/
theorem completedMultiply_backtrack (x : V) :
    completedMultiply hw0 hw1 hsmall hd hs sourceLoop 1 x =
      completedSmul hw0 hw1 hsmall hd hs 2 x := by
  have h := compileKernel_haar_congr hw0 hw1 hsmall hd hs
    0 backtrack constant backtrack_within constant_within
    (by simpa only [Nat.zero_add, Nat.one_mul] using source_supported_haar) x
  simpa only [backtrack, constant, compileKernel, expand, termsKernel,
    List.map_cons, List.map_nil,
    wordKernel, orderWord, insertWord, orderedKernel, act, Nat.sub_zero,
    completedTime_zero, completedSmul_one, completedAdd_zero] using h

/-- The same physical backtrack identity remains valid at every elapsed
duration, not merely as equality of its vacuum output. -/
theorem kernel_backtrack_constant (H : Nat) (x : V) :
    Op (compileKernel H backtrack) x = Op (compileKernel H constant) x := by
  simp only [backtrack, constant, compileKernel, expand, termsKernel,
    List.map_cons, List.map_nil,
    wordKernel, orderWord, insertWord, orderedKernel, act, Nat.sub_zero,
    completedTime_zero, completedMultiply_backtrack, completedSmul_one, completedAdd_zero,
    completedTime_smul]
  rfl

end YMGap.Continuum.BF4WilsonKernelHaarIdentity

#print axioms YMGap.Continuum.BF4WilsonKernelHaarIdentity.graftStage_haar_congr
#print axioms YMGap.Continuum.BF4WilsonKernelHaarIdentity.compileKernel_haar_congr
#print axioms YMGap.Continuum.BF4WilsonKernelHaarIdentity.compileKernel_padded_congr
#print axioms YMGap.Continuum.BF4WilsonKernelHaarIdentity.completedMultiply_backtrack
#print axioms YMGap.Continuum.BF4WilsonKernelHaarIdentity.kernel_backtrack_constant
