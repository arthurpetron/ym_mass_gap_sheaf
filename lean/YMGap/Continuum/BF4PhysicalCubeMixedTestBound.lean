/-
# A marginal test controls the reflected transfer response

For every vector x of the ENTIRE reflected completion and every original
finite cube test y, <x,y>_E^2 <= <T x,x>_E ||y||_marginal^2.
On physical dense vectors this is ordinary marginal Cauchy--Schwarz after
the exact identity E(a,b)=<P a,b>. Both sides pass through the existing
represented pairing limits. No inverse of P or choice of representatives
is used. The test norm is the original marginal norm, not its weaker E norm.

Scope: fixed w=1/400, extent one. No common strict gap or geometric time.
-/

import YMGap.Continuum.BF4PhysicalCubeDissipation
import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovCorrelationDecay

namespace YMGap.Continuum.BF4PhysicalCubeMixedTestBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSDenseCompletionLaws
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeCompletion
open YMGap.Continuum.BF4PhysicalCubeObservableRealization
open YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage
open YMGap.Continuum.BF4PhysicalCubeDenseTransfer
open YMGap.Continuum.BF4PhysicalCubeCompletedTransfer
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalCubeDissipation
open YMGap.Continuum.BF4PhysicalCubeSectorVacuum
open YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInner
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerOuter
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedMarkovCorrelationDecay
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovConcreteAdaptiveTransfer
open YMGap.Continuum.BF4PhysicalCutoffReflectedFormLaws
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.ScaledGNSCompletion
open YMGap.Continuum.ScaledGNSCompletionEstimates
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "G" => centralPhysicalCutoffLinearSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "S" => centralPhysicalVacuumSectorCylinderSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "M" => centralPhysicalCutoffCompletedInner (w := anchorCoupling) (by decide) (by decide) 0
local notation "P" => centralPhysicalConcreteAdaptiveCompletedMarkovTransfer
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "J" => cubeToCompleted (w := anchorCoupling) (by decide) (by decide)
local notation "B" => cubeReflectedInner
local notation "T" => cubeTransfer
local notation "j" => cubeReflectedEmbed
local notation "N" => anchorNormalization.value
local notation "raw" => Quotient.mk (cauchySetoid D)

def marginalNorm (test : CubeSpan) : CReal :=
  innerLimit (w := anchorCoupling) (by decide) (by decide) 0 (cubeObservable test) (cubeObservable test)

theorem marginalNorm_class (test : CubeSpan) :
    Quotient.mk crealSetoid (marginalNorm test) = M (J test) (J test) :=
  (centralPhysicalCutoffCompletedInner_embedRep (by decide) (by decide) 0 _ _).symm

theorem dense_transfer_norm_pin (terms : CubeSpan) :
    B (T (j terms)) (j terms) = M (P (J terms)) (P (J terms)) := by
  have h := cubeTransferPower_sector_moments 1
    ((S).embedRep (spanPresentation terms)) ((S).embedRep (spanPresentation terms))
  rw [spanPresentation_reflected, spanPresentation_global] at h
  change B (j terms) (T (j terms)) = M (J terms) (P (P (J terms))) at h
  exact Eq.trans (cubeTransfer_selfAdjoint _ _)
    (Eq.trans h (concrete_selfAdjoint (w := anchorCoupling) (by decide) (by decide) 0 _ _).symm)

theorem dense_mixed_test_bound (terms test : CubeSpan) :
    RCle (RCmul (B (j terms) (j test)) (B (j terms) (j test)))
      (RCmul (B (T (j terms)) (j terms)) (Quotient.mk crealSetoid (marginalNorm test))) := by
  rw [dense_transfer_norm_pin, marginalNorm_class, cubeReflectedInner_embed]
  unfold completedReflectedForm
  rw [← concrete_selfAdjoint]
  exact centralPhysicalCutoffCompletedInner_cauchy_schwarz (by decide) (by decide) 0 _ _

private theorem dense_pairing_converges (X : CauchyGNS D) (test : CubeSpan) :
    ConvergesTo (fun n => (D).cinnerRep (constCauchy D (X.seq n)) (constCauchy D test))
      ((D).cinnerRep X (constCauchy D test)) := by
  apply convergesTo_limit_congr ((D).cinnerRep_continuous_left (inputOuter X) (constCauchy D test))
  apply Quotient.exact (s := crealSetoid)
  exact congrArg (fun x => (D).cinnerCompl x (embedV D test)) (inputOuter_lim_class X)

/-- Both limits retain the original representatives and the physical
normalization. The target need not come from the marginal completion. -/
theorem represented_mixed_test_bound (X : CauchyGNS D) (test : CubeSpan) :
    RCle (RCmul (B (rawToReflected (raw X)) (j test)) (B (rawToReflected (raw X)) (j test)))
      (RCmul (B (T (rawToReflected (raw X))) (rawToReflected (raw X)))
        (Quotient.mk crealSetoid (marginalNorm test))) := by
  have hp := CReal.convergesTo_mul_general (dense_pairing_converges X test) (convergesTo_const N)
  have ht := CReal.convergesTo_mul_general (mixed_left_converges denseTransferData X X) (convergesTo_const N)
  have h := leEv_of_convergesTo_le (CReal.convergesTo_mul_general hp hp)
    (CReal.convergesTo_mul_general ht (convergesTo_const (marginalNorm test))) (fun n => by
      have hn := dense_mixed_test_bound (X.seq n) test
      rw [← rawToReflected_embed, ← rawToReflected_embed,
        cubeTransfer_rawComparison, cubeRawTransfer_embed,
        cubeReflectedInner_comparison, cubeReflectedInner_comparison] at hn
      exact hn)
  rw [← rawToReflected_embed, cubeTransfer_rawComparison,
    cubeReflectedInner_comparison, cubeReflectedInner_comparison]
  exact h

/-- The original marginal test norm controls response on EVERY reflected
completion vector, not just vectors already represented in the marginal image. -/
theorem mixed_test_bound (x : CubeReflectedCompletion) (test : CubeSpan) :
    RCle (RCmul (B x (j test)) (B x (j test)))
      (RCmul (B (T x) x) (Quotient.mk crealSetoid (marginalNorm test))) := by
  have h : ∀ z : CubeCompletion anchorCoupling (by decide),
      RCle (RCmul (B (rawToReflected z) (j test)) (B (rawToReflected z) (j test)))
        (RCmul (B (T (rawToReflected z)) (rawToReflected z))
          (Quotient.mk crealSetoid (marginalNorm test))) := fun z =>
    Quotient.inductionOn z (fun X => represented_mixed_test_bound X test)
  have hx := h (reflectedToRaw x)
  rwa [reflected_raw_inverse] at hx

/-- Computed from the fixed supplied marginal representative; no ceiling is
selected from an existential bound. -/
def marginalCeiling (test : CubeSpan) : Q' :=
  Q'.ofNat (physicalCauchyNormCeil (w := anchorCoupling) (by decide) (by decide) 0
    ((G).constant (cubeObservable test)))

private theorem ceiling_pos (X : (G).Cauchy) :
    (0 : Q') < Q'.ofNat (physicalCauchyNormCeil (by decide) (by decide) 0 X) :=
  Q'.ofNat_succ_pos _

theorem marginalCeiling_pos (test : CubeSpan) : (0 : Q') < marginalCeiling test :=
  ceiling_pos ((G).constant (cubeObservable test))

theorem marginalNorm_le_ceiling (test : CubeSpan) :
    RCle (Quotient.mk crealSetoid (marginalNorm test)) (Rq (marginalCeiling test)) :=
  physicalCauchyStageDiagonal_leEv_normCeil (by decide) (by decide) 0
    ((G).constant (cubeObservable test)) _ (Nat.le_refl _)

/-- A positive test pairing gives a positive rational transfer-response
floor. No division by a possibly zero completed-vector norm is performed. -/
theorem response_floor_of_test (x : CubeReflectedCompletion) (test : CubeSpan)
    (floor : Q') (hfloor : (0 : Q') ≤ floor)
    (hpairing : RCle (Rq floor) (B x (j test))) :
    RCle (Rq (Q'.divPos (floor * floor) (marginalCeiling test) (marginalCeiling_pos test)))
      (B (T x) x) := by
  apply cancel_q (marginalCeiling test) (marginalCeiling_pos test)
  rw [rq_mul, rq_eqv (Q'.divPos_mul_eqv _ _ _)]
  exact RCle_trans (positive_test_square hfloor hpairing)
    (RCle_trans (mixed_test_bound x test)
      (mul_mono_left (cubeTransfer_positive x) (marginalNorm_le_ceiling test)))

private theorem eq_zero_of_square_le_zero (a : RC)
    (h : RCle (RCmul a a) RCzero) : a = RCzero := by
  revert h
  refine Quotient.inductionOn a ?_
  intro A h
  apply Quotient.sound
  intro epsilon hepsilon
  obtain ⟨index, hN⟩ := h (epsilon * epsilon) (Q'.mul_pos hepsilon hepsilon)
  refine ⟨index, fun n hn => ?_⟩
  have hs : A.approx n * A.approx n ≤ epsilon * epsilon := by
    have hs := hN n hn
    change A.approx n * A.approx n ≤ 0 + epsilon * epsilon at hs
    rwa [Q'.zero_add'] at hs
  have ha := Q'.abs_le_two_sided (Q'.abs_le_of_sq_le_sq hepsilon hs)
  constructor
  · exact Q'.le_trans' _ _ _ ha.1 (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' _)))
  · apply Q'.le_add_of_sub_le
    change 0 + -A.approx n ≤ epsilon
    rw [Q'.zero_add']
    exact ha.2

private theorem zero_mul (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv (A.approx n)))

/-- The actual reflected transfer form has no radical on the completed
carrier. This excludes a zero-response vector, not a near-vacuum mode. -/
theorem eq_zero_of_response_zero (x : CubeReflectedCompletion)
    (h : B (T x) x = RCzero) : x = j [] := by
  apply cubeReflected_ext_dense
  intro test
  have hs := mixed_test_bound x test
  rw [h, zero_mul] at hs
  rw [cubeReflectedInner_zero_left]
  exact eq_zero_of_square_le_zero _ hs

/-- In particular, the SAME completed transfer kills no nonzero vector. -/
theorem transfer_kernel_trivial (x : CubeReflectedCompletion)
    (h : T x = j []) : x = j [] := by
  apply eq_zero_of_response_zero x
  rw [h, cubeReflectedInner_zero_left]

end YMGap.Continuum.BF4PhysicalCubeMixedTestBound

#print axioms YMGap.Continuum.BF4PhysicalCubeMixedTestBound.marginalNorm
#print axioms YMGap.Continuum.BF4PhysicalCubeMixedTestBound.marginalNorm_class
#print axioms YMGap.Continuum.BF4PhysicalCubeMixedTestBound.dense_transfer_norm_pin
#print axioms YMGap.Continuum.BF4PhysicalCubeMixedTestBound.dense_mixed_test_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeMixedTestBound.represented_mixed_test_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeMixedTestBound.mixed_test_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeMixedTestBound.marginalCeiling
#print axioms YMGap.Continuum.BF4PhysicalCubeMixedTestBound.marginalCeiling_pos
#print axioms YMGap.Continuum.BF4PhysicalCubeMixedTestBound.marginalNorm_le_ceiling
#print axioms YMGap.Continuum.BF4PhysicalCubeMixedTestBound.response_floor_of_test
#print axioms YMGap.Continuum.BF4PhysicalCubeMixedTestBound.eq_zero_of_response_zero
#print axioms YMGap.Continuum.BF4PhysicalCubeMixedTestBound.transfer_kernel_trivial
