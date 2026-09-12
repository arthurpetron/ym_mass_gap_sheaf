/-
# Norm and same-object correlation decay on the whole reflected complement

On marginal-sector images, E(T Rx,T Rx)=M(Px,P^2 x). The marginal form
gap at Px and the sharp square-form bound at x give

  M(Px,P^2 x) <= q M(Px,Px) <= q^2 M(Px,x).

Thus the original reflected norm contracts by q^2. The already constructed
centered approximants, output error bound, and joint pairing limit pass
this estimate to EVERY reflected vacuum-orthogonal vector. Induction and
ordinary reflected Cauchy--Schwarz then give norm and correlation decay.

All objects are the original SU(2) BF4 conditional operator and reflected
completion at w=1/400, extent one. Conditional iterations are NOT identified
with geometric Euclidean time; no volume/spacing, continuum, or Clay claim.
-/

import YMGap.Continuum.BF4PhysicalCubeCompletedReflectedGap

namespace YMGap.Continuum.BF4PhysicalCubeCompletedReflectedDecay

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.ScaledGNSCompletion
open YMGap.Continuum.ScaledGNSCompletionEstimates
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCubeSectorCompletedPairing
open YMGap.Continuum.BF4PhysicalCubeCompletedTransfer
open YMGap.Continuum.BF4PhysicalCubeCompletedTransferLaws
open YMGap.Continuum.BF4PhysicalCubeSectorVacuumNorm
open YMGap.Continuum.BF4PhysicalCubeSectorCenteredRealization
open YMGap.Continuum.BF4PhysicalCubeCenteredDensity
open YMGap.Continuum.BF4PhysicalCubeDissipation
open YMGap.Continuum.BF4PhysicalCubeDenseFormClosure
open YMGap.Continuum.BF4PhysicalCubeCompletedMarginalGap
open YMGap.Continuum.BF4PhysicalCubeCompletedReflectedGap
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedInnerLaws
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovJointAdaptiveCauchySchwarz
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedMoments
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderTransferLift
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local notation "D" => cubeGNSData anchorCoupling (by decide)
local notation "lambda" => Quotient.mk crealSetoid anchorNormalization.value
local notation "rawClass" => GNSRepresentedApproximation.classOf D
local notation "B" => cubeReflectedInner
local notation "T" => cubeTransfer
local notation "q" => reflectedGapRate
local notation "BM" => centralPhysicalVacuumSectorCylinderCompletedInner
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "PM" => centralPhysicalVacuumSectorCylinderCompletedTransfer
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "MC" => CentralPhysicalVacuumSectorCylinderCompletedVacuumComplement
  (w := anchorCoupling) (by decide) (by decide) 0

private theorem scale_eq_mul (s : Q') (x : RC) : RCscale s x = RCmul (Rq s) x := by
  refine Quotient.inductionOn x ?_
  intro X
  rfl

private theorem normalization_cancel (a b : RC)
    (h : RCle (RCmul a lambda) (RCmul b lambda)) : RCle a b := by
  refine Quotient.inductionOn₂ a b ?_ h
  intro A B hab
  exact RCBilinearDifference.cancel_positive_factor anchorNormalization.floor
    anchorNormalization.floor_pos anchorNormalization.lower hab

/-- No marginal-norm prefactor: the right side is the SAME reflected norm. -/
theorem sector_image_norm_bound (x : MC) :
    RCle (B (T (sectorToReflected x.val)) (T (sectorToReflected x.val)))
      (RCscale (q * q) (B (sectorToReflected x.val) (sectorToReflected x.val))) := by
  let gap := completedSectorFormGap (w := anchorCoupling) (by decide) (by decide) (by decide)
  let Px := centralPhysicalVacuumSectorCylinderCompletedVacuumTransfer
    (w := anchorCoupling) (by decide) (by decide) 0 x
  have hform : RCle (BM (PM x.val) (PM (PM x.val)))
      (RCscale q (BM (PM x.val) (PM x.val))) := by
    have hs : BM (PM x.val) (PM (PM x.val)) = BM (PM (PM x.val)) (PM x.val) :=
      centralPhysicalCutoffCompletedInner_symm
        (w := anchorCoupling) (by decide) (by decide) 0 _ _
    rw [hs]
    exact gap.form_gap Px
  have hsquare := centralPhysicalVacuumSectorCylinderCompletedTransfer_square_form_gap
    (centralPhysicalVacuumSectorCylinderCompletedMarkovFormCauchySchwarzData
      (w := anchorCoupling) (by decide) (by decide) 0) gap x
  have h := RCle_trans hform (RCscale_mono (Q'.le_of_lt reflectedGapRate_pos) hsquare)
  rw [RCscale_RCscale] at h
  rw [cubeTransfer_sector]
  change RCle (B (sectorToReflected (PM x.val)) (sectorToReflected (PM x.val)))
    (RCscale (q * q) (B (sectorToReflected x.val) (sectorToReflected x.val)))
  rw [reflected_pairing_eq_sector, reflected_pairing_eq_sector]
  have hs : BM x.val (PM x.val) = BM (PM x.val) x.val :=
    centralPhysicalCutoffCompletedInner_symm
      (w := anchorCoupling) (by decide) (by decide) 0 _ _
  rw [hs]
  exact h

theorem dense_reflected_norm_bound (base : Nat) (coefficient : Nat → Q') :
    let y := (centeredCubeVector base coefficient).val
    RCle (B (T y) (T y)) (RCscale (q * q) (B y y)) :=
  sector_image_norm_bound
    ⟨centeredSectorSource base coefficient, centeredSectorSource_mean_zero base coefficient⟩

/-- The existing action approximation rate works on BOTH sides of the
pairing. No new Cauchy or continuity premise is introduced. -/
theorem raw_action_norm_converges (x : CubeSectorVacuumComplement) (X : CauchyGNS D)
    (hX : rawToReflected (rawClass X) = x.val) :
    CReal.ConvergesTo
      (fun n => (D).cinnerRep (denseTransferData.mapRep (rawApproximant X n))
        (denseTransferData.mapRep (rawApproximant X n)))
      ((D).cinnerRep (denseTransferData.mapRep X) (denseTransferData.mapRep X)) :=
  GNSRepresentedApproximation.pairing_converges_to D (denseTransferData.mapRep X)
    (fun n => denseTransferData.mapRep (rawApproximant X n)) (rawApproximationRate X)
    (raw_action_approximation_bound x X hX) (denseTransferData.mapRep X)
    (fun n => denseTransferData.mapRep (rawApproximant X n)) (rawApproximationRate X)
    (raw_action_approximation_bound x X hX)

private theorem raw_norm_bound (y : GNSCompletionSpace D)
    (h : RCle (B (T (rawToReflected y)) (T (rawToReflected y)))
      (RCscale (q * q) (B (rawToReflected y) (rawToReflected y)))) :
    RCle ((D).cinnerCompl (cubeRawTransfer y) (cubeRawTransfer y))
      (RCmul (Rq (q * q)) ((D).cinnerCompl y y)) := by
  rw [scale_eq_mul, cubeTransfer_rawComparison, cubeReflectedInner_comparison,
    cubeReflectedInner_comparison, ← BF4PhysicalCubeDissipation.mul_assoc] at h
  exact normalization_cancel _ _ h

private theorem represented_norm_bound (x : CubeSectorVacuumComplement) (X : CauchyGNS D)
    (hX : rawToReflected (rawClass X) = x.val) :
    RCle (B (T x.val) (T x.val)) (RCscale (q * q) (B x.val x.val)) := by
  have hstage (n : Nat) :
      CReal.leEv
        ((D).cinnerRep (denseTransferData.mapRep (rawApproximant X n))
          (denseTransferData.mapRep (rawApproximant X n)))
        (CReal.mul (CReal.ofQ' (q * q))
          ((D).cinnerRep (rawApproximant X n) (rawApproximant X n))) := by
    apply raw_norm_bound (rawClass (rawApproximant X n))
    rw [rawApproximant_reflected]
    exact dense_reflected_norm_bound (approximationPresentation X n).base
      (approximationPresentation X n).coefficient
  have hraw := CReal.leEv_of_convergesTo_le (raw_action_norm_converges x X hX)
    (CReal.convergesTo_const_mul (CReal.ofQ' (q * q)) (raw_norm_converges x X hX)) hstage
  change RCle ((D).cinnerCompl (cubeRawTransfer (rawClass X)) (cubeRawTransfer (rawClass X)))
    (RCmul (Rq (q * q)) ((D).cinnerCompl (rawClass X) (rawClass X))) at hraw
  have hscaled := mul_mono_right (normalization_nonnegative anchorNormalization) hraw
  rw [scale_eq_mul, ← hX, cubeTransfer_rawComparison,
    cubeReflectedInner_comparison, cubeReflectedInner_comparison]
  rw [← BF4PhysicalCubeDissipation.mul_assoc]
  exact hscaled

/-- The original completed conditional operator contracts the original
reflected squared norm by q^2 on the ENTIRE vacuum complement. -/
theorem completed_reflected_norm_bound (x : CubeSectorVacuumComplement) :
    RCle (B (T x.val) (T x.val)) (RCscale (q * q) (B x.val x.val)) := by
  rcases x with ⟨x, hx⟩
  revert hx
  refine Quotient.inductionOn x ?_
  intro X hx
  exact represented_norm_bound ⟨Quotient.mk _ X, hx⟩
    (toRawCauchy D anchorNormalization X) (reflected_raw_inverse (Quotient.mk _ X))

theorem power_preserves_complement (n : Nat) (x : CubeSectorVacuumComplement) :
    B BF4PhysicalCubeSectorVacuum.reflectedSectorVacuum (cubeTransferPower n x.val) = RCzero := by
  induction n with
  | zero => exact x.property
  | succ n ih =>
    exact cubeTransfer_preserves_vacuumComplement ⟨cubeTransferPower n x.val, ih⟩

/-- One explicit geometric rate controls every iterate and every completed
vacuum-orthogonal vector, with only its own reflected norm as prefactor. -/
theorem completed_reflected_power_norm_decay (n : Nat) (x : CubeSectorVacuumComplement) :
    RCle (B (cubeTransferPower n x.val) (cubeTransferPower n x.val))
      (RCscale ((q * q) ^ n) (B x.val x.val)) := by
  induction n with
  | zero =>
    rw [cubeTransferPower, Q'.pow_zero, RCscale_one]
    exact RCle_refl _
  | succ n ih =>
    have h := completed_reflected_norm_bound
      ⟨cubeTransferPower n x.val, power_preserves_complement n x⟩
    have hq := Q'.mul_nonneg q q (Q'.le_of_lt reflectedGapRate_pos)
      (Q'.le_of_lt reflectedGapRate_pos)
    have hscaled := RCscale_mono hq ih
    have hnext := RCle_trans h hscaled
    rw [RCscale_RCscale] at hnext
    exact hnext

/-- Squared correlations of the SAME completed operator decay with the
same geometric rate. No interpretation as geometric time is inferred. -/
theorem completed_reflected_correlation_sq_decay (n : Nat)
    (x y : CubeSectorVacuumComplement) :
    RCle
      (RCmul (B x.val (cubeTransferPower n y.val)) (B x.val (cubeTransferPower n y.val)))
      (RCmul (B x.val x.val) (RCscale ((q * q) ^ n) (B y.val y.val))) :=
  RCle_trans (inner_cauchySchwarz x.val (cubeTransferPower n y.val))
    (mul_mono_left (inner_nonnegative x.val) (completed_reflected_power_norm_decay n y))

/-- Directly bounds the already realized connected conditional correlator,
whose exact physical moment identity retains its one-insertion shift. -/
theorem centeredCubeCorrelator_sq_decay (base : Nat) (coefficient : Nat → Q') (n : Nat) :
    let y := (centeredCubeVector base coefficient).val
    RCle
      (RCmul (centeredCubeCorrelator base coefficient n) (centeredCubeCorrelator base coefficient n))
      (RCmul (B y y) (RCscale ((q * q) ^ n) (B y y))) :=
  completed_reflected_correlation_sq_decay n
    (centeredCubeVector base coefficient) (centeredCubeVector base coefficient)

end YMGap.Continuum.BF4PhysicalCubeCompletedReflectedDecay

#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedDecay.sector_image_norm_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedDecay.dense_reflected_norm_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedDecay.raw_action_norm_converges
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedDecay.completed_reflected_norm_bound
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedDecay.power_preserves_complement
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedDecay.completed_reflected_power_norm_decay
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedDecay.completed_reflected_correlation_sq_decay
#print axioms YMGap.Continuum.BF4PhysicalCubeCompletedReflectedDecay.centeredCubeCorrelator_sq_decay
