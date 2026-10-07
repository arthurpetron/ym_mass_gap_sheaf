/-
# Actual interacting transfer output paid by projected-source norm loss

Retain the COMPLETE original source V*f, integrate only the absent kinetic
coordinates, and use the checked full-product reverse-Poincare inequality.
One norm decrement pays all output angular directions without an active-plane
count. The norm is ordinary Haar on q=Pi_fringe(V*f), NOT ell_V[f^2], the
conditional score law, or the completed OS norm. In particular this estimate
cannot be multiplied by the output-dependent Vbar^2*Gout^2. The conditional
score/action and scaling joins remain open.
-/

import YMGap.Continuum.SU2QuaternionProductHeatReversePoincare
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSmoothing

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTransferReversePoincare

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSmoothing
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionChannelCasimirSquare
open YMGap.Continuum.SU2QuaternionChannelAngularContraction
open YMGap.Continuum.SU2QuaternionLiteralCasimirPairing
open YMGap.Continuum.SU2QuaternionProductHeatReversePoincare
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" n:arg => quaternionHaar n
attribute [local irreducible] baseLinks spatialWeight

private theorem baseLinks_positive (width : Nat) : 0 < N width := by
  have h : ((0,0,0,0),Dir4.x0) ∈ baseLinks width :=
    (baseLinks_mem_iff width _).mpr
      ⟨by decide, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl⟩
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) (List.idxOf_lt_length_of_mem h)

private theorem square_congr (n : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (heq : SupportedHaarEqv n p q) : H n (polyMul p p) ≈ H n (polyMul q q) :=
  Q'.eqv_trans _ _ _ (heq p hp)
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm p q)) (heq q hq))

private theorem angular_congr (n : Nat) (p q : RatPoly)
    (hp : SupportedQuaternionBlocks n p) (hq : SupportedQuaternionBlocks n q)
    (heq : SupportedHaarEqv n p q) :
    angularListSum n (List.range n) p ≈ angularListSum n (List.range n) q := by
  let C := activeCasimirPolynomial (List.range n)
  have hCp := activeCasimirPolynomial_supported (List.range n)
    (fun i hi => List.mem_range.mp hi) hp
  have hCq := activeCasimirPolynomial_supported (List.range n)
    (fun i hi => List.mem_range.mp hi) hq
  exact Q'.eqv_trans _ _ _ (haar_activeCasimir_self n _
      (fun i hi => List.mem_range.mp hi) p).symm
    (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (heq (C p) hCp)
        (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
          (Q'.eqv_trans _ _ _ (literalPair_symm n (List.range n)
            (fun i hi => List.mem_range.mp hi) p q)
            (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
              (Q'.eqv_trans _ _ _ (heq (C q) hCq)
                (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
                  (haar_activeCasimir_self n _ (fun i hi => List.mem_range.mp hi) q))))))))

/-- All angular directions of the ACTUAL original transfer, paid by ONE
projected full-source norm loss. All finite cutoffs and both nome endpoints
are covered. No heat floor or source/partition inverse is used. -/
theorem transferStep_angular_projected_norm_loss_le {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (K width : Nat)
    (f : RatPoly) (hf : SupportedQuaternionBlocks (N width) f) :
    let q := familyProject (fringeBlocks width) (polyMul (spatialWeight w K width) f)
    (1-w*w)*angularListSum (N width) (List.range (N width))
        (transferStep w K width f) +
      (w*w)*H (N width) (polyMul (transferStep w K width f) (transferStep w K width f)) ≤
      (w*w)*H (N width) (polyMul q q) := by
  dsimp only
  let q := familyProject (fringeBlocks width) (polyMul (spatialWeight w K width) f)
  let Pq := productMap (N width) w K (List.range (N width)) q
  have hq := familyProject_supported (fringeBlocks width)
    (supported_polyMul (spatialWeight_supported w K width) hf)
  have hPq := productMap_supported (N width) w K (List.range (N width))
    (fun i hi => List.mem_range.mp hi) hq
  have hT := transferStep_supported w K width hf
  have he := transferStep_projected_full_heat w K width f hf
  have ha := angular_congr (N width) _ Pq hT hPq he
  have hn := square_congr (N width) _ Pq hT hPq he
  have hsize : N width-1+1 = N width := Nat.sub_add_cancel (baseLinks_positive width)
  have h := productMap_angular_norm_loss_le (N width-1) hw0 hw1 K q (by rwa [hsize])
  rw [hsize] at h
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (1-w*w) _ _ ha)
      (Q'.mul_eqv_congr_left (w*w) _ _ hn))) h

end YMGap.Continuum.BF4ExactSlabFixedSpatialTransferReversePoincare

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTransferReversePoincare.transferStep_angular_projected_norm_loss_le
