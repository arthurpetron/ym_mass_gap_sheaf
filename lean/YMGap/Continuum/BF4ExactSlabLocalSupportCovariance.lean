/-
# Local variance comparison for the original finite and cutoff-limit covariance

This transports the exact original normalized variance comparison to the
existing full-face finite covariance and then to its fixed-extent heat-cutoff
limit. The ratio depends on nome and the supplied literal support size. No
thermodynamic, scaling, OS-time, or completed Dirichlet estimate is asserted.
-/

import YMGap.Continuum.BF4ExactSlabLocalSupportVariance
import YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
import YMGap.Continuum.FCLimitContinuity
import YMGap.Continuum.RCCauchySchwarz

namespace YMGap.Continuum.BF4ExactSlabLocalSupportCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabLocalSupportVariance
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)
local notation "faces" extent => slabPhysicalFaceEdges extent

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- The diagonal of the existing original finite covariance is literally
the selected-action normalized variance at the same cutoff. -/
theorem finite_covariance_eq_normalized_variance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (p : RatPoly) (stage : Nat) :
    normalizedVariance (blocks extent)
      (polynomialProduct (faceHeatPolynomial w (headCutoff w+stage) extent) (faces extent)) p
      (selectedMass_positive hw0 hw1 (headCutoff w+stage) extent
        (Nat.le_add_right _ _) (faces extent) (fun _ hi => hi)) ≈
    finiteCovariance w hw0 hw1 extent (faces extent) (fun _ hi => hi) p p stage := by
  have hm := normalizedMoment_finiteValue hw0 hw1 extent (faces extent)
    (fun _ hi => hi) p stage
  have hs := normalizedMoment_finiteValue hw0 hw1 extent (faces extent)
    (fun _ hi => hi) (polyMul p p) stage
  exact Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _ (qmul hm hm))

/-- Both rational bounds concern the SAME full-action finite covariance,
not a star-deleted or independent-link reference measure. -/
theorem finite_covariance_support_comparison {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (S : List Z4Link) (size : Nat) (hsize : S.length ≤ size)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hl : LinkLocal extent S p) (stage : Nat) :
    supportRatio hw0 hw1 size * bareVariance (blocks extent) p ≤
      finiteCovariance w hw0 hw1 extent (faces extent) (fun _ hi => hi) p p stage ∧
    supportRatio hw0 hw1 size *
      finiteCovariance w hw0 hw1 extent (faces extent) (fun _ hi => hi) p p stage ≤
        bareVariance (blocks extent) p := by
  have hv := support_variance_comparison hw0 hw1 (headCutoff w+stage) extent
    (Nat.le_add_right _ _) S size hsize p hp hl
  have he := finite_covariance_eq_normalized_variance hw0 hw1 extent p stage
  exact ⟨Q'.le_trans' _ _ _ hv.1 (Q'.le_of_eqv he),
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ he)) hv.2⟩

/-- Cutoff removal at fixed extent preserves the two original-action local
variance bounds. The second uses the actual positive ratio multiplying the
cutoff-limit covariance; no partition or collar is replaced by a floor. -/
theorem covariance_support_comparison {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (S : List Z4Link) (size : Nat) (hsize : S.length ≤ size)
    (p : RatPoly) (hp : SupportedQuaternionBlocks (blocks extent) p)
    (hl : LinkLocal extent S p) :
    leEv (ofQ' (supportRatio hw0 hw1 size * bareVariance (blocks extent) p))
      (covariance w hw0 hw1 extent (faces extent) (fun _ hi => hi) p p) ∧
    leEv (CReal.mul (ofQ' (supportRatio hw0 hw1 size))
      (covariance w hw0 hw1 extent (faces extent) (fun _ hi => hi) p p))
      (ofQ' (bareVariance (blocks extent) p)) := by
  let c := supportRatio hw0 hw1 size
  let v := fun stage => finiteCovariance w hw0 hw1 extent (faces extent)
    (fun _ hi => hi) p p stage
  have hv := finite_covariance_support_comparison hw0 hw1 extent S size hsize p hp hl
  have hc := finite_covariance_converges w hw0 hw1 extent (faces extent)
    (fun _ hi => hi) p p
  have hcm : ConvergesTo (fun stage => ofQ' (c*v stage))
      (CReal.mul (ofQ' c)
        (covariance w hw0 hw1 extent (faces extent) (fun _ hi => hi) p p)) := by
    apply TrigAddCReal.convergesTo_congr_seq
      (fun stage => CReal.Equiv.symm (CRealAlg.ofQ'_mul c (v stage)))
    exact CReal.convergesTo_const_mul (ofQ' c) hc
  constructor
  · apply CReal.leEv_of_ofQ'_limit_le
      (CReal.convergesTo_const (ofQ' (c*bareVariance (blocks extent) p))) hc
    intro epsilon he
    exact ⟨0, fun stage _ => Q'.le_trans' _ _ _ (hv stage).1
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩
  · apply CReal.leEv_of_ofQ'_limit_le hcm
      (CReal.convergesTo_const (ofQ' (bareVariance (blocks extent) p)))
    intro epsilon he
    exact ⟨0, fun stage _ => Q'.le_trans' _ _ _ (hv stage).2
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

end YMGap.Continuum.BF4ExactSlabLocalSupportCovariance

#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportCovariance.finite_covariance_eq_normalized_variance
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportCovariance.finite_covariance_support_comparison
#print axioms YMGap.Continuum.BF4ExactSlabLocalSupportCovariance.covariance_support_comparison
