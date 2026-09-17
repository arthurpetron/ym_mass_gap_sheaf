/-
# Spatial weighted projection onto all inactive coordinates

Integrate the full fringe in the original spatial weight V. Both terminal
messages are independent of these coordinates, at every depth including
zero, so their factors pull through without being discarded. The spatial
conditional mass and numerator contain no time-depth parameter.

The division-free residual R=(P_F V)f-P_F(Vf) is exactly orthogonal to
fringe-independent tests in the SAME odd marginal, and T(g_n*R) vanishes
under every Haar test. No normalized inverse or stable active estimate
is presumed. This R is a new specified choice, not the old fringeSum.
-/

import YMGap.Continuum.SU2QuaternionProductHeatFamilyNull
import YMGap.Continuum.BF4ExactSlabFixedSpatialFringeKernel

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
  (activeBlocks activeBlocks_lt kineticWeight_eq_indexedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual (terminal_inactive_independent)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalPair)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow
  (fringeBlocks fringeBlocks_mem_iff fringeBlocks_lt)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
  (QuaternionBlockIndependent quaternionBlockIndependent_polyOne quaternionBlockIndependent_polyMul)
open YMGap.Continuum.SU2QuaternionHaarFamilyProjection
open YMGap.Continuum.SU2QuaternionProductHeatFamilyNull
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap productMap_congr)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] spatialWeight baseLinks kineticWeight activeBlocks

def fringeProject (width : Nat) (f : RatPoly) : RatPoly :=
  familyProject (fringeBlocks width) f

def spatialFringeMass (w : Q') (K width : Nat) : RatPoly :=
  fringeProject width (spatialWeight w K width)

def spatialFringeMean (w : Q') (K width : Nat) (f : RatPoly) : RatPoly :=
  fringeProject width (polyMul (spatialWeight w K width) f)

def spatialFringeResidual (w : Q') (K width : Nat) (f : RatPoly) : RatPoly :=
  familyWeightedResidual (fringeBlocks width) (spatialWeight w K width) f

theorem spatialFringeMass_supported (w : Q') (K width : Nat) :
    SupportedQuaternionBlocks (N width) (spatialFringeMass w K width) :=
  familyProject_supported _ (spatialWeight_supported w K width)

theorem spatialFringeMean_supported (w : Q') (K width : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (spatialFringeMean w K width f) :=
  familyProject_supported _ (supported_polyMul (spatialWeight_supported w K width) hf)

theorem spatialFringeResidual_supported (w : Q') (K width : Nat) {f : RatPoly}
    (hf : SupportedQuaternionBlocks (N width) f) :
    SupportedQuaternionBlocks (N width) (spatialFringeResidual w K width f) :=
  familyWeightedResidual_supported _ (spatialWeight_supported w K width) hf

theorem spatialFringeMass_independent (w : Q') (K width i : Nat)
    (hi : i ∈ fringeBlocks width) : QuaternionBlockIndependent i (spatialFringeMass w K width) :=
  familyProject_independent _ _ i hi

theorem spatialFringeMean_independent (w : Q') (K width : Nat) (f : RatPoly) (i : Nat)
    (hi : i ∈ fringeBlocks width) : QuaternionBlockIndependent i (spatialFringeMean w K width f) :=
  familyProject_independent _ _ i hi

/-- The original scaled observable is recovered coefficientwise. -/
theorem spatialFringeResidual_split (w : Q') (K width : Nat) (f : RatPoly) :
    RatPolyCoeffEqv (polyAdd (spatialFringeResidual w K width f) (spatialFringeMean w K width f))
      (polyMul (spatialFringeMass w K width) f) :=
  coeffEvalExpr_eqv_of_normalize_eq
    (.add (.add (.mul (.var 0) (.var 1)) (.neg (.var 2))) (.var 2))
    (.mul (.var 0) (.var 1)) (by decide)
    (fun | 0 => spatialFringeMass w K width | 1 => f | _ => spatialFringeMean w K width f)

/-- Both terminal messages, including g_0=1, omit every inactive coordinate. -/
theorem terminal_fringe_independent (w : Q') (K width n i : Nat)
    (hi : i ∈ fringeBlocks width) : QuaternionBlockIndependent i (terminalMessage w K width n) := by
  cases n with
  | zero => exact quaternionBlockIndependent_polyOne i
  | succ n =>
      exact terminal_inactive_independent w K width n i (fringeBlocks_lt width i hi)
        (((fringeBlocks_mem_iff width i).mp hi).2)

def depthFactor (w : Q') (K width n : Nat) : RatPoly :=
  polyMul (terminalMessage w K width n) (terminalMessage w K width (n+1))

theorem depthFactor_independent (w : Q') (K width n i : Nat)
    (hi : i ∈ fringeBlocks width) : QuaternionBlockIndependent i (depthFactor w K width n) :=
  quaternionBlockIndependent_polyMul (terminal_fringe_independent w K width n i hi)
    (terminal_fringe_independent w K width (n+1) i hi)

/-- The conditional denominator retains the exact depth factor, while its
spatial part is independent of depth. No division is performed. -/
theorem marginal_fringe_mass_pin (w : Q') (K width n : Nat) :
    RatPolyCoeffEqv (fringeProject width (marginalWeight w K width n))
      (polyMul (depthFactor w K width n) (spatialFringeMass w K width)) :=
  (familyProject_congr _ (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.mul (.var 1) (.var 2)) (.var 0))
    (by decide) (fun
      | 0 => spatialWeight w K width | 1 => terminalMessage w K width n
      | _ => terminalMessage w K width (n+1)))).trans
    (familyProject_mul_of_independent _ _ _ (depthFactor_independent w K width n))

theorem marginal_fringe_mean_pin (w : Q') (K width n : Nat) (f : RatPoly) :
    RatPolyCoeffEqv (fringeProject width (polyMul (marginalWeight w K width n) f))
      (polyMul (depthFactor w K width n) (spatialFringeMean w K width f)) :=
  (familyProject_congr _ (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.var 3))
    (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3))) (by decide)
    (fun
      | 0 => spatialWeight w K width | 1 => terminalMessage w K width n
      | 2 => terminalMessage w K width (n+1) | _ => f))).trans
    (familyProject_mul_of_independent _ _ _ (depthFactor_independent w K width n))

/-- Orthogonality in the SAME original odd marginal, with the complete
spatial weight. The test's fringe independence is explicit. -/
theorem spatialFringeResidual_orthogonal (w : Q') (K width n : Nat) (f b : RatPoly)
    (hb : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i b) :
    marginalPair w K width n (spatialFringeResidual w K width f) b ≈ 0 :=
  Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 3) (.var 4)))
    (.mul (.var 0) (.mul (.var 3) (.mul (.mul (.var 1) (.var 2)) (.var 4))))
    (by decide) (fun
      | 0 => spatialWeight w K width | 1 => terminalMessage w K width n
      | 2 => terminalMessage w K width (n+1) | 3 => spatialFringeResidual w K width f | _ => b)))
    (familyWeightedResidual_orthogonal (fringeBlocks width) (fringeBlocks_lt width)
      (spatialWeight w K width) f (polyMul (depthFactor w K width n) b)
      (fun i hi => quaternionBlockIndependent_polyMul (depthFactor_independent w K width n i hi) (hb i hi)))

/-- The whole-family residual is centered against the original lower
endpoint weight V*g_n. No per-coordinate centering premise is needed. -/
theorem spatialFringeResidual_endpoint_centered (w : Q') (K width n : Nat) (f : RatPoly) :
    RatPolyCoeffEqv (fringeProject width (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) (spatialFringeResidual w K width f)))
      polyZero :=
  (familyProject_congr _ (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.mul (.var 1) (.mul (.var 0) (.var 2)))
    (by decide) (fun
      | 0 => spatialWeight w K width | 1 => terminalMessage w K width n
      | _ => spatialFringeResidual w K width f))).trans
    ((familyProject_mul_of_independent _ _ _ (terminal_fringe_independent w K width n)).trans
      (((familyProject_weightedResidual_zero _ _ f).mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _)))

private theorem transfer_product (w : Q') (K width : Nat) (f : RatPoly) :
    transferStep w K width f = productMap (N width) w K (activeBlocks width)
      (polyMul (spatialWeight w K width) f) := by
  unfold transferStep step productMap kernelMap
  rw [kineticWeight_eq_indexedProduct]
  rfl

/-- An arbitrary fringe-independent polynomial multiplier preserves the
same weighted transfer kernel. This includes the finite spatial reciprocal. -/
theorem spatialFringeResidual_scaled_transfer_zero (w : Q') (K width n : Nat)
    (f J p : RatPoly) (hJ : ∀ i, i ∈ fringeBlocks width → QuaternionBlockIndependent i J) :
    quaternionHaar (N width) (polyMul p (transferStep w K width
      (polyMul (terminalMessage w K width n) (polyMul J (spatialFringeResidual w K width f))))) ≈ 0 := by
  rw [transfer_product]
  apply productMap_family_pair_zero (N width) w K (activeBlocks width) (activeBlocks_lt width)
    (fringeBlocks width) (fringeBlocks_lt width)
    (fun i hi => ((fringeBlocks_mem_iff width i).mp hi).2)
  exact (familyProject_congr _ (coeffEvalExpr_eqv_of_normalize_eq
    (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 3))))
    (.mul (.mul (.var 1) (.var 2)) (.mul (.var 0) (.var 3))) (by decide)
    (fun
      | 0 => spatialWeight w K width | 1 => terminalMessage w K width n
      | 2 => J | _ => spatialFringeResidual w K width f))).trans
    ((familyProject_mul_of_independent _ _ _ (fun i hi =>
      quaternionBlockIndependent_polyMul (terminal_fringe_independent w K width n i hi) (hJ i hi))).trans
      (((familyProject_weightedResidual_zero _ _ f).mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.fringeProject
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.spatialFringeMass
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.spatialFringeMean
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.spatialFringeResidual
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.spatialFringeMass_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.spatialFringeMean_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.spatialFringeResidual_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.spatialFringeMass_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.spatialFringeMean_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.spatialFringeResidual_split
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.terminal_fringe_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.depthFactor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.depthFactor_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.marginal_fringe_mass_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.marginal_fringe_mean_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.spatialFringeResidual_orthogonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.spatialFringeResidual_endpoint_centered
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeProjection.spatialFringeResidual_scaled_transfer_zero
