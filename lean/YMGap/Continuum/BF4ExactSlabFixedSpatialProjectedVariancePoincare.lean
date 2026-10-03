/-
# ORIGINAL projected variance paid by genuine reference angular energy

The complete original source/action/transfer stay at K. The auxiliary
reference heat alone uses L. Actual lower-fringe independence identifies
the joint sweep loss with the projected source's OWN determinant variance,
including its actual conditional mean and normalization. The constructed
fixed-source onset yields the factor 1-w^2 with no link-count prefactor.

Fringe projection further contracts this SECOND-derivative energy into
that of the complete original first derivative. The near-unit K/L variance
comparison then pays the original active Jensen debt. This does NOT turn
Gamma(Q) into Q^2, control it by the SAME surviving norm, or justify any
changing-family, physical/OS/continuum/QFT/every-group/Clay conclusion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVarianceCutoff
import YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedInputAngularEnergy
import YMGap.Continuum.SU2QuaternionProductHeatConditionalVariance

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVariancePoincare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks fringeBlocks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepSourceDerivative
open YMGap.Continuum.BF4ExactSlabFixedSpatialLastStepProjectedDerivative
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVarianceCutoff
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedInputAngularEnergy
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatEfronStein
open YMGap.Continuum.SU2QuaternionProductHeatConditionalVariance
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.QuaternionHaarSquareCertificate

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] baseLinks kineticWeight

/-- Computed auxiliary onset for the complete ORIGINAL projected source.
K is an argument of the source, not the reference kernel cutoff L. -/
def projectedSourcePoincareCutoff (w : Q') (K width s i j : Nat)
    (a c : RatPoly) : Nat :=
  jointPoincareCutoff (N width) w (activeBlocks width)
    (lastStepProjectedDerivative w K width s i j a c)

/-- Every inactive LOWER block is removed by the actual fringe projection.
No inactive UPPER variable or original action factor is deleted. -/
theorem projected_source_inactive (w : Q') (K width s i j : Nat) (a c : RatPoly)
    (b : Nat) (hb : b < N width) (hnot : b ∉ activeBlocks width) :
    QuaternionBlockIndependent b (lastStepProjectedDerivative w K width s i j a c) :=
  familyProject_independent (fringeBlocks width) _ b
    ((fringeBlocks_mem_iff width b).mpr ⟨hb,hnot⟩)

/-- The full reference variance, not only its sweep loss, now has the
ORIGINAL input angular bound under arbitrary certified output W. -/
theorem projected_reference_variance_angular_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K L width s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) (a c W : RatPoly)
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c)
    (hW : SupportedQuaternionBlocks (N width) W) (P : Certificate (N width) W)
    (hL : projectedSourcePoincareCutoff w K width s i j a c ≤ L) :
    quaternionHaar (N width) (polyMul W (projectedReferenceVariance w K L width s i j a c)) ≤
      (1-w*w)*jointAngularEnergy (N width) w L (activeBlocks width) W
        (lastStepProjectedDerivative w K width s i j a c) (activeBlocks width) := by
  unfold projectedReferenceVariance
  rw [kineticWeight_eq_indexedProduct]
  exact conditional_variance_angular_poincare (N width) hw0 hw1 L
    (activeBlocks width) (activeBlocks_nodup width) (activeBlocks_lt width) W _ hW P
    (lastStepProjectedDerivative_supported w K width s i j hs hi hj ha hc)
    (projected_source_inactive w K width s i j a c) hL

private theorem energy_pairing (w : Q') (L width b : Nat) (p W : RatPoly) :
    quaternionHaar (N width) (polyMul W (inputAngularReferenceEnergy w L width b p)) ≈
      quaternionHaar (N width+N width)
        (polyMul (jointWeight (N width) w L (activeBlocks width) W) (blockAngularSquare b p)) := by
  have h := inputAngularReferenceEnergy_pairing w L width b p W
  rw [kineticWeight_eq_indexedProduct] at h
  exact Q'.eqv_trans _ _ _ h
    (haar_of_coeff ((RatPolyCoeffEqv.mul_comm _ _).mul_right (blockAngularSquare b p)))

/-- Coefficient-one contraction of the full active input-energy sum into
the complete ORIGINAL derivative, retaining all shared reference weights. -/
theorem projected_angularEnergy_le_source {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K L width : Nat)
    (hL : headCutoff w ≤ L) (s i j : Nat) (hs : s < N width) (hi : i < 4) (hj : j < 4)
    (a c W : RatPoly) (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c) (P : Certificate (N width) W) :
    ∀ xs : List Nat, (∀ b, b ∈ xs → b < N width) →
      jointAngularEnergy (N width) w L (activeBlocks width) W
        (lastStepProjectedDerivative w K width s i j a c) xs ≤
      jointAngularEnergy (N width) w L (activeBlocks width) W
        (lastStepSourceDerivative w K width s i j a c) xs
  | [], _ => Q'.le_refl' _
  | b::xs, hxs => by
      have hb := hxs b List.mem_cons_self
      have H := projected_inputAngularEnergy_weighted_le hw0 hw1 K L width hL b s i j
        hb hs hi hj a c W ha hc P
      have HE : quaternionHaar (N width+N width)
          (polyMul (jointWeight (N width) w L (activeBlocks width) W)
            (blockAngularSquare b (lastStepProjectedDerivative w K width s i j a c))) ≤
          quaternionHaar (N width+N width)
          (polyMul (jointWeight (N width) w L (activeBlocks width) W)
            (blockAngularSquare b (lastStepSourceDerivative w K width s i j a c))) :=
        Q'.le_trans' _ _ _ (Q'.ge_of_eqv (energy_pairing w L width b _ W))
          (Q'.le_trans' _ _ _ H (Q'.le_of_eqv (energy_pairing w L width b _ W)))
      exact Q'.add_le_add HE
        (projected_angularEnergy_le_source hw0 hw1 K L width hL s i j hs hi hj a c W ha hc P
          xs (fun d hd => hxs d (List.mem_cons_of_mem b hd)))

private theorem angular_factor_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : (0 : Q') ≤ 1-w*w :=
  Q'.sub_nonneg_of_le (Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left w 1 w (Q'.le_of_lt hw1) (Q'.le_of_lt hw0))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv w)) (Q'.le_of_lt hw1)))

/-- Reference variance paid by genuine SECOND-derivative energy of the
complete ORIGINAL source, not by its first-derivative square budget. -/
theorem projected_reference_variance_source_energy_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K L width s i j : Nat)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) (a c W : RatPoly)
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c)
    (hW : SupportedQuaternionBlocks (N width) W) (P : Certificate (N width) W)
    (hL : projectedSourcePoincareCutoff w K width s i j a c ≤ L) :
    quaternionHaar (N width) (polyMul W (projectedReferenceVariance w K L width s i j a c)) ≤
      (1-w*w)*jointAngularEnergy (N width) w L (activeBlocks width) W
        (lastStepSourceDerivative w K width s i j a c) (activeBlocks width) := by
  have hhead : headCutoff w ≤ L := Nat.le_trans (Nat.le_max_left _ _) hL
  exact Q'.le_trans' _ _ _
    (projected_reference_variance_angular_le hw0 hw1 K L width s i j hs hi hj a c W ha hc hW P hL)
    (Q'.mul_le_mul_of_nonneg_left _ _ (1-w*w)
      (projected_angularEnergy_le_source hw0 hw1 K L width hhead s i j hs hi hj a c W ha hc P
        (activeBlocks width) (activeBlocks_lt width)) (angular_factor_nonnegative hw0 hw1))

/-- The original active Jensen debt is bounded after the already proved
near-unit cutoff comparison. Both original source terms remain at K. -/
theorem projected_active_variance_source_energy_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (eta : Q')
    (he : (0 : Q') < eta) (he1 : eta ≤ 1) (K L width s i j : Nat)
    (hK : projectedVarianceCutoff w eta width ≤ K)
    (hLcut : projectedVarianceCutoff w eta width ≤ L)
    (hs : s < N width) (hi : i < 4) (hj : j < 4) (a c W : RatPoly)
    (ha : SupportedQuaternionBlocks (N width) a)
    (hc : SupportedQuaternionBlocks (N width) c)
    (hW : SupportedQuaternionBlocks (N width) W) (P : Certificate (N width) W)
    (hL : projectedSourcePoincareCutoff w K width s i j a c ≤ L) :
    quaternionHaar (N width) (polyMul W (projectedActiveVariance w K width s i j a c)) ≤
      (1+eta)*((1-w*w)*jointAngularEnergy (N width) w L (activeBlocks width) W
        (lastStepSourceDerivative w K width s i j a c) (activeBlocks width)) :=
  Q'.le_trans' _ _ _
    (projected_variance_cutoff_weighted_le hw0 hw1 eta he he1 K L width hK hLcut
      s i j hs hi hj ha hc P)
    (Q'.mul_le_mul_of_nonneg_left _ _ (1+eta)
      (projected_reference_variance_source_energy_le hw0 hw1 K L width s i j hs hi hj
        a c W ha hc hW P hL)
      (Q'.zero_le_add _ _ (by decide) (Q'.le_of_lt he)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVariancePoincare

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVariancePoincare.projectedSourcePoincareCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVariancePoincare.projected_source_inactive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVariancePoincare.projected_reference_variance_angular_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVariancePoincare.projected_angularEnergy_le_source
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVariancePoincare.projected_reference_variance_source_energy_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedVariancePoincare.projected_active_variance_source_energy_le
