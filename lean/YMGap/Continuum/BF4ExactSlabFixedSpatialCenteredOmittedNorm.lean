/-
# Cutoff norm control on the ORIGINAL OWN-centered Wilson source

Apply the proved omitted operator estimates to q=P_fringe(V*g_n) and the
observable centered with its own ORIGINAL odd-marginal mean. The diagonal
Haar square is Z*OWNVar-C, with C signed; the mixed cap retains raw Haar
mass and the quartic square. The complete cubic-minus-omitted numerator is
bounded and normalized by the same original partition.

No raw q^2 law is identified with q*P(q). No moment is assumed small, no
physical scaling family is constructed, and the separate angular/Ward
debts and retained projection gain have not been combined with this cap.
-/

import YMGap.Continuum.SU2QuaternionCyclicOmittedOperator
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredOmittedNorm

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection (familyProject_supported)
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionCyclicSecondOrder
open YMGap.Continuum.SU2QuaternionCyclicOmittedNorm
open YMGap.Continuum.SU2QuaternionCyclicOmittedOperator
open YMGap.Continuum.SU2QuaternionCompleteRemainderSquare (sourceSquareMass observableSquare)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks baseLinks_mem_iff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy (projectedEndpointSource)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard (oddVariance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram (oddCentered oddCentered_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredRemainderSquare
  (centeredCorrection centered_sourceSquare_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (oddMass oddMass_positive)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks terminalMessage projectedEndpointSource oddMass oddVariance

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem source_supported (w : Q') (K width n : Nat) :
    SupportedQuaternionBlocks (N width)
      (projectedEndpointSource w K width (terminalMessage w K width n)) := by
  unfold projectedEndpointSource
  exact familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (K width : Nat) (hK : headCutoff w ≤ K) (n : Nat) (f : RatPoly)

local notation "q" => projectedEndpointSource w K width (terminalMessage w K width n)
local notation "psi" => oddCentered hw0 hw1 K width hK n f
local notation "Z" => oddMass w K width n
local notation "V" => oddVariance hw0 hw1 K width hK n f
local notation "C" => centeredCorrection hw0 hw1 K width hK n f

/-- Actual diagonal debt with the original signed correction retained. -/
theorem centered_diagonalOmitted_le_variance
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    pairOmitted (N width-1) w K (polyMul q psi) (polyMul q psi) ≤
      omittedRate w K*(Z*V-C) := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hraw := pairOmitted_diagonal_le_haar (N width-1) (Q'.le_of_lt hw0) (Q'.le_of_lt hw1)
    K (polyMul q psi) (by simpa only [hN] using
      (supported_polyMul (source_supported w K width n)
        (oddCentered_supported hw0 hw1 K width hK n hf)))
  exact Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _
    (centered_sourceSquare_pin hw0 hw1 K width hK n hf hind)))

/-- Mixed debt under the SAME original centered observable. The quartic
mass is raw Haar and is not silently replaced by interacting variance. -/
theorem centered_mixedOmitted_square_bound
    (hf : SupportedQuaternionBlocks (N width) f) :
    pairOmitted (N width-1) w K q (polyMul q (polyMul psi psi))*
        pairOmitted (N width-1) w K q (polyMul q (polyMul psi psi)) ≤
      (omittedRate w K*omittedRate w K)*
        (H (N width) (polyMul q q)*H (N width)
          (polyMul (polyMul q (polyMul psi psi)) (polyMul q (polyMul psi psi)))) := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hq := source_supported w K width n
  have hp := oddCentered_supported hw0 hw1 K width hK n hf
  have h := pairOmitted_square_le_haar (N width-1) (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) K
    q (polyMul q (polyMul psi psi)) (by simpa only [hN] using hq)
    (by simpa only [hN] using supported_polyMul hq (supported_polyMul hp hp))
  simpa only [hN] using h

/-- Concrete original error cap. Only the diagonal Haar square is contracted
to Z*OWNVar-C; raw mass and fourth moment remain visible. -/
def centeredHaarBudget : Q' :=
  ((((1 : Q')-w)*((1 : Q')-w))*((1 : Q')-w))*
    (pairCubicBudget (N width-1) q (polyMul q (polyMul psi psi))+
      pairCubicBudget (N width-1) (polyMul q psi) (polyMul q psi))+
    omittedRate w K*(HalfPow.half*(H (N width) (polyMul q q)+
      H (N width) (polyMul (polyMul q (polyMul psi psi)) (polyMul q (polyMul psi psi))))+
      (Z*V-C))

theorem centeredHaarBudget_pin
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    sourceHaarErrorBudget (N width-1) w K q psi ≈
      centeredHaarBudget hw0 hw1 K width hK n f := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have hp := centered_sourceSquare_pin hw0 hw1 K width hK n hf hind
  unfold sourceSquareMass observableSquare at hp
  simp only [hN] at hp
  unfold sourceHaarErrorBudget centeredHaarBudget
  rw [hN]
  exact Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_left _ _ _ (Q'.add_eqv_congr' (Q'.eqv_refl _) hp))

/-- Entire actual cubic-minus-omitted numerator, with no omitted leaf costs
and no favorable sign assumed for the centering correction. -/
theorem centered_sourceError_le_haar
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    sourceCubic (N width-1) w q psi-sourceOmitted (N width-1) w K q psi ≤
      centeredHaarBudget hw0 hw1 K width hK n f := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  exact Q'.le_trans' _ _ _ (sourceError_le_haar (N width-1)
    (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) K q psi
    (by simpa only [hN] using source_supported w K width n)
    (by simpa only [hN] using oddCentered_supported hw0 hw1 K width hK n hf))
    (Q'.le_of_eqv (centeredHaarBudget_pin hw0 hw1 K width hK n f hf hind))

/-- BOTH sides divided by the SAME original positive partition. -/
theorem normalized_centered_sourceError_le_haar
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i f) :
    (sourceCubic (N width-1) w q psi-sourceOmitted (N width-1) w K q psi)*
        Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK n) ≤
      centeredHaarBudget hw0 hw1 K width hK n f*
        Q'.recipPos Z (oddMass_positive hw0 hw1 K width hK n) :=
  Q'.mul_le_mul_of_nonneg_right _ _ _
    (centered_sourceError_le_haar hw0 hw1 K width hK n f hf hind)
    (Q'.le_of_lt (Q'.recipPos_pos Z _))

end YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredOmittedNorm

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredOmittedNorm.centered_diagonalOmitted_le_variance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredOmittedNorm.centered_mixedOmitted_square_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredOmittedNorm.centeredHaarBudget
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredOmittedNorm.centeredHaarBudget_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredOmittedNorm.centered_sourceError_le_haar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredOmittedNorm.normalized_centered_sourceError_le_haar
