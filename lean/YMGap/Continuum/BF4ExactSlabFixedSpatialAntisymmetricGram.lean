/-
# Exact removal of the two Gram means for the antisymmetric ORIGINAL source

The existing spatialSpan is explicitly coefficient-pinned to the literal
p01-minus-p02 Wilson expression. Strict padding supplies syntactic fringe
independence for that span; coefficient equality is NOT used to infer locality.
Finite cutoff stage and terminal depth are independent parameters. Exact
original means and the existing bare full-heat eigenimage remove J and M,
while the complete source-jump cost and signed cross credit remain unestimated.
This is no filtering rate, scaling budget or survival claim.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialAntisymmetricPlaquette
import YMGap.Continuum.BF4WilsonPlaquetteFamilyIncrement
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyHeatEigen
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
import YMGap.Continuum.SU2QuaternionProductHeatSumGram
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialAntisymmetricGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialAntisymmetricPlaquette
open YMGap.Continuum.BF4WilsonPlaquetteFamilyIncrement (source_family_shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOwnCenterLimit (expressionOwnMean)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPadding (windowRatio_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddleRatioPins (massRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBracket (massRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialGroundStateEnergy (endpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_lt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamilySchedule (spatialSpan spatialSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFringeIndependent
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyHeatEigen
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff headFloor)
open YMGap.Continuum.BF4ExactSlabJacobiDeficitInterval (bandSize bandSize_le_deficitCutoff)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatJumpMean (jump_mean)
open YMGap.Continuum.SU2QuaternionProductHeatSumGram (sumTest_mean)
open YMGap.Continuum.SU2QuaternionProductHeatSumTest (sumTest)
open YMGap.Continuum.SU2QuaternionProductHeatSumNorm (sourceSumIncrementCost)
open YMGap.Continuum.SU2QuaternionProductHeatSourceYoung (singleEndedCost)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump)
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)
open YMGap.Continuum.QuaternionHaarSquareCertificate (supported_one haar_of_coeff)
open YMGap.Continuum.QuaternionHaarDensityVariance (normalizedMoment shifted)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage spatialSpan
  energy oddVariance

/-- Exact recoding of the already constructed Wilson source, not a new source. -/
theorem source_spatialSpan_pin {width : Nat} (hw : 1 ≤ width) :
    RatPolyCoeffEqv (sourcePolynomial (expression hw)) (spatialSpan width coefficient faces) := by
  simpa only [expression, shift_zero, Nat.zero_mul, liftBoundary] using
    source_family_shift width faces coefficient (faces_physical hw) 0

theorem source_fringe_independent {width : Nat} (hw : 2 ≤ width) :
    ∀ i, i ∈ fringeBlocks width →
      QuaternionBlockIndependent i (spatialSpan width coefficient faces) :=
  spatialSpan_fringe_independent_after_padding (by omega : 1 < width)
    coefficient faces (faces_physical (Nat.le_refl 1))

private theorem cutoff_one (w : Q') (stage : Nat) : 1 ≤ headCutoff w+stage := by
  have h := bandSize_le_deficitCutoff w (headFloor w)
  dsimp only [bandSize] at h
  change 1 ≤ BF4ExactSlabJacobiDeficitInterval.deficitCutoff w (headFloor w)+stage
  omega

private theorem middle_congr (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < 1)
    (K width : Nat) (hK : headCutoff w ≤ K) (m n : Nat) {p p' : RatPoly}
    (hp : RatPolyCoeffEqv p p') :
    middleRatio hw0 hw1 K width hK m n p ≈ middleRatio hw0 hw1 K width hK m n p' :=
  massRatio_congr w K width (terminalPair_positive hw0 hw1 K width hK m n)
    (terminalPair_positive hw0 hw1 K width hK m n)
    (weightedMass_congr w K width
      (((RatPolyCoeffEqv.refl _).mul hp).mul (RatPolyCoeffEqv.refl _))) (Q'.eqv_refl _)

private theorem mul_congr {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h) (Q'.mul_eqv_congr_left _ _ _ k)

section Finite
variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < 1)
  {width : Nat} (hw : 2 ≤ width) (stage depth : Nat)
include hw0 hw1 hw

local notation "K" => headCutoff w+stage
local notation "f" => spatialSpan width coefficient faces
local notation "q" => projectedEndpointSource w K width (terminalMessage w K width depth)
local notation "psi" => oddCentered hw0 hw1 K width (Nat.le_add_right _ _) depth f

private theorem middle_mean_zero (m n : Nat) :
    middleRatio hw0 hw1 K width (Nat.le_add_right _ _) m n f ≈ 0 := by
  have hp := source_spatialSpan_pin (by omega : 1 ≤ width)
  have hz := Q'.eqv_trans _ _ _
    (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 0
      (expression (by omega : 1 ≤ width)) (expression_within _) stage m n))
    (original_mean_zero hw0 hw1 (by omega : 1 ≤ width) 0 stage m n)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (windowRatio_zero hw0 hw1 K width (Nat.le_add_right _ _) m n
      (spatialSpan_supported width coefficient faces)))
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (windowRatio_congr hw0 hw1 K width (Nat.le_add_right _ _) m 0 n hp)) hz)

/-- The two chronological terminal depths and the source are unchanged. -/
theorem ownMean_spatialSpan_pin :
    middleRatio hw0 hw1 K width (Nat.le_add_right _ _) (depth+1) depth f ≈
      expressionOwnMean hw0 hw1 (expression (by omega : 1 ≤ width)) stage depth :=
  middle_congr w hw0 hw1 K width (Nat.le_add_right _ _) (depth+1) depth
    (source_spatialSpan_pin (by omega : 1 ≤ width)).symm

theorem oddCentered_source_pin :
    RatPolyCoeffEqv psi (sourcePolynomial (expression (by omega : 1 ≤ width))) := by
  have hm : normalizedMoment (N width) (marginalWeight w K width depth) f
      (marginalMass_positive hw0 hw1 K width (Nat.le_add_right _ _) depth) ≈ 0 :=
    Q'.eqv_trans _ _ _ (marginalMoment_pin hw0 hw1 K width (Nat.le_add_right _ _) depth f)
      (Q'.eqv_trans _ _ _ (ownMean_spatialSpan_pin hw0 hw1 hw stage depth)
        (ownMean_zero hw0 hw1 (by omega : 1 ≤ width) stage depth))
  have hshift : RatPolyCoeffEqv psi f := by
    unfold oddCentered shifted
    exact ((RatPolyCoeffEqv.one_smul _).add
      ((RatPolyCoeffEqv.smul_coefficient
        (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hm)
          (by decide : -(0 : Q') ≈ 0)) polyOne).trans
        (RatPolyCoeffEqv.zero_smul polyOne))).trans (RatPolyCoeffEqv.add_zero _)
  exact hshift.trans (source_spatialSpan_pin (by omega : 1 ≤ width)).symm

private theorem oddCentered_span_pin : RatPolyCoeffEqv psi f :=
  (oddCentered_source_pin hw0 hw1 hw stage depth).trans
    (source_spatialSpan_pin (by omega : 1 ≤ width))

/-- Zero of the raw original endpoint moment, before fringe integration. -/
theorem raw_endpoint_mean_zero :
    quaternionHaar (N width)
      (polyMul (endpointSource w K width (terminalMessage w K width depth)) f) ≈ 0 := by
  let g := terminalMessage w K width depth
  let z := weightedMass w K width (polyMul g (terminalMessage w K width 0))
  let hz := terminalPair_positive hw0 hw1 K width (Nat.le_add_right _ _) depth 0
  let a := weightedMass w K width (polyMul (polyMul g f) (terminalMessage w K width 0))
  have hratio : a*Q'.recipPos z hz ≈ 0 := middle_mean_zero hw0 hw1 hw stage depth 0
  have hc : (a*Q'.recipPos z hz)*z ≈ a :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_trans _ _ _
          (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv z hz))) (Q'.mul_one_eqv a))
  have ha : a ≈ 0 := Q'.eqv_trans _ _ _ (Q'.eqv_symm hc)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ z hratio) (Q'.zero_mul_eqv z))
  have hnum : a ≈ quaternionHaar (N width)
      (polyMul (endpointSource w K width g) f) := by
    change weightedMass w K width
      (polyMul (polyMul g f) (terminalMessage w K width 0)) ≈ _
    rw [show terminalMessage w K width 0 = polyOne by unfold terminalMessage; rfl]
    unfold weightedMass endpointSource
    exact haar_of_coeff (((RatPolyCoeffEqv.mul_one (polyMul g f)).mul_left _).trans
      (RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) g f).symm)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hnum) ha

/-- Actual projected endpoint q, not a supplied symmetric replacement. -/
theorem projected_endpoint_mean_zero : quaternionHaar (N width) (polyMul q f) ≈ 0 := by
  let a := endpointSource w K width (terminalMessage w K width depth)
  have hp := familyProject_mul_of_independent (fringeBlocks width) f a
    (source_fringe_independent hw)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm q f))
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (haar_of_coeff hp))
      (Q'.eqv_trans _ _ _ (familyProject_mean (N width) (fringeBlocks width)
        (fun i hi => fringeBlocks_lt width i hi) (polyMul f a))
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm f a))
          (raw_endpoint_mean_zero hw0 hw1 hw stage depth))))

private theorem q_supported : SupportedQuaternionBlocks (N width) q :=
  familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width)
    (terminalMessage_supported w K width depth))

theorem projected_heat_mean_zero :
    quaternionHaar (N width)
      (polyMul q (productMap (N width) w K (List.range (N width)) f)) ≈ 0 := by
  have he := spatialSpan_fullRange width coefficient faces
    (faces_physical (by omega : 1 ≤ width)) w K (cutoff_one w stage)
  exact Q'.eqv_trans _ _ _ (he q (q_supported hw0 hw1 hw stage depth))
    (Q'.eqv_trans _ _ _ (quaternionHaar_polyMul_smul_right (N width) (qpow w 12) q f)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (projected_endpoint_mean_zero hw0 hw1 hw stage depth))
        (Q'.mul_zero_eqv _)))

theorem jump_mean_zero :
    weightedPair (N width+N width) (productHeat (N width) w K (List.range (N width)))
      (polyMul (jump (N width) q) (jump (N width) f)) polyOne ≈ 0 := by
  have hj := jump_mean (N width) w K (List.range (N width))
    (CayleyParentInj.range_nodup _) (fun i hi => List.mem_range.mp hi)
    (q_supported hw0 hw1 hw stage depth) (spatialSpan_supported width coefficient faces)
  exact Q'.eqv_trans _ _ _ hj
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 _ _
      (Q'.add_eqv_congr' (projected_endpoint_mean_zero hw0 hw1 hw stage depth)
        (Q'.neg_eqv_congr _ _ (projected_heat_mean_zero hw0 hw1 hw stage depth))))
      (by decide : (2 : Q')*(0 + -0) ≈ 0))

theorem sum_mean_zero :
    weightedPair (N width+N width) (productHeat (N width) w K (List.range (N width)))
      (sumTest (N width) q psi) polyOne ≈ 0 := by
  have hp := oddCentered_span_pin hw0 hw1 hw stage depth
  have h0 : quaternionHaar (N width) (polyMul q psi) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (hp.mul_left q))
      (projected_endpoint_mean_zero hw0 hw1 hw stage depth)
  have h1 : quaternionHaar (N width)
      (polyMul q (productMap (N width) w K (List.range (N width)) psi)) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff
      ((productMap_congr (N width) w K (List.range (N width)) hp).mul_left q))
      (projected_heat_mean_zero hw0 hw1 hw stage depth)
  exact Q'.eqv_trans _ _ _
    (sumTest_mean (N width) w K (List.range (N width)) (CayleyParentInj.range_nodup _)
      (fun i hi => List.mem_range.mp hi) (q_supported hw0 hw1 hw stage depth)
      (oddCentered_supported hw0 hw1 K width (Nat.le_add_right _ _) depth
        (spatialSpan_supported width coefficient faces)))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left 2 _ _ (Q'.add_eqv_congr' h0 h1))
      (by decide : (2 : Q')*(0+0) ≈ 0))

/-- SAME original energy and actual projected q. Both even source-jump cost
and signed cross credit remain literal; no sign or useful relative cap is added. -/
theorem original_energy_response_budget :
    let n := N width
    let W := productHeat n w K (List.range n)
    let r := polyMul (jump n q) (jump n f)
    let s := sumTest n q psi
    let V := 16*(oddMass w K width depth*oddVariance hw0 hw1 K width
        (Nat.le_add_right _ _) depth f) +
      -(8*energy w K width (terminalMessage w K width depth) f) +
      sourceSumIncrementCost n w K (List.range n) q psi
    let X := weightedPair (n+n) W r s
    4*V*energy w K width (terminalMessage w K width depth) f + X*X ≤
      2*V*singleEndedCost n w K (List.range n) q f := by
  dsimp only
  let W := productHeat (N width) w K (List.range (N width))
  let r := polyMul (jump (N width) q) (jump (N width) f)
  let s := sumTest (N width) q psi
  let J := weightedPair (N width+N width) W r polyOne
  let M := weightedPair (N width+N width) W s polyOne
  let V := 16*(oddMass w K width depth*oddVariance hw0 hw1 K width
      (Nat.le_add_right _ _) depth f) +
    -(8*energy w K width (terminalMessage w K width depth) f) +
    sourceSumIncrementCost (N width) w K (List.range (N width)) q psi
  let E := energy w K width (terminalMessage w K width depth) f
  let X := weightedPair (N width+N width) W r s
  let C := singleEndedCost (N width) w K (List.range (N width)) q f
  have hJ : J ≈ 0 := jump_mean_zero hw0 hw1 hw stage depth
  have hM : M ≈ 0 := sum_mean_zero hw0 hw1 hw stage depth
  have hV : V + -(M*M) ≈ V := Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl V)
      (Q'.neg_eqv_congr _ _ (mul_congr hM hM)))
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.mul (.const 0) (.const 0))))
      (.var 0) (by decide) (fun _ => V))
  have hX : X + -(J*M) ≈ X := Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl X)
      (Q'.neg_eqv_congr _ _ (mul_congr hJ hM)))
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.mul (.const 0) (.const 0))))
      (.var 0) (by decide) (fun _ => X))
  have hleft : 4*(V + -(M*M))*E + (V + -(M*M))*(J*J) +
      (X + -(J*M))*(X + -(J*M)) ≈ 4*V*E+X*X :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ E (Q'.mul_eqv_congr_left 4 _ _ hV))
        (mul_congr hV (mul_congr hJ hJ)))
      (mul_congr hX hX))
      (poly_identity_of_normal_eq
        (.add (.add (.mul (.mul (.const 4) (.var 0)) (.var 1))
          (.mul (.var 0) (.mul (.const 0) (.const 0)))) (.mul (.var 2) (.var 2)))
        (.add (.mul (.mul (.const 4) (.var 0)) (.var 1)) (.mul (.var 2) (.var 2)))
        (by decide) (fun
          | 0 => V
          | 1 => E
          | _ => X))
  have hright : 2*(V + -(M*M))*C ≈ 2*V*C :=
    Q'.mul_eqv_congr_right _ _ C (Q'.mul_eqv_congr_left 2 _ _ hV)
  have h := original_centered_energy_response_budget hw0 hw1 K width
    (Nat.le_add_right _ _) depth (spatialSpan_supported width coefficient faces)
    (source_fringe_independent hw)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ h (Q'.le_of_eqv hright))

end Finite

#print axioms source_spatialSpan_pin
#print axioms source_fringe_independent
#print axioms ownMean_spatialSpan_pin
#print axioms oddCentered_source_pin
#print axioms raw_endpoint_mean_zero
#print axioms projected_endpoint_mean_zero
#print axioms projected_heat_mean_zero
#print axioms jump_mean_zero
#print axioms sum_mean_zero
#print axioms original_energy_response_budget

end YMGap.Continuum.BF4ExactSlabFixedSpatialAntisymmetricGram
