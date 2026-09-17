/-
# Original-energy control of averaged fringe directions

An inactive kinetic coordinate is averaged, not frozen. The actual terminal
message t is independent of that coordinate, and the actual nu=a*t residual
is t times its a-residual. Thus its a-centering is exact without an inverse.
The unchanged full edge gives coefficient-one dual control by energy(f).

This pays concrete fringe directions. It does not assert that active and
fringe residuals form a complete, stable decomposition.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLinkDual

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat (kineticWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (edgeDensity energy energy_identity edgeCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarBlockProjection (project)
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini (QuaternionBlockIndependent)
open YMGap.Continuum.SU2QuaternionWeightedBlockCentering
open YMGap.Continuum.SU2QuaternionHeadChainComposition (step)
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap)
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap (edgeWeight)
open YMGap.Continuum.SU2QuaternionWeightedProductDualEnergy (jump jump_supported erased_jump_pairing)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)

attribute [local irreducible] spatialWeight baseLinks kineticWeight

/-- Literal product-message pin, before any conditional or normalization operation. -/
theorem terminal_product (w : Q') (K width n : Nat) :
    terminalMessage w K width (n+1) =
      productMap (N width) w K (activeBlocks width)
        (polyMul (spatialWeight w K width) (terminalMessage w K width n)) := by
  rw [← terminalMessage_next]
  unfold transferStep step productMap kernelMap
  rw [kineticWeight_eq_indexedProduct]
  rfl

/-- Absence of a kinetic factor means the output coordinate is absent. -/
theorem terminal_inactive_independent (w : Q') (K width n i : Nat)
    (hi : i < N width) (hnot : i ∉ activeBlocks width) :
    QuaternionBlockIndependent i (terminalMessage w K width (n+1)) := by
  rw [terminal_product]
  exact productMap_independent_of_not_mem (N width) w K (activeBlocks width)
    (activeBlocks_lt width) i hi hnot _
    (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n))

/-- Conditional residuals pull through a genuinely independent right weight. -/
theorem weightedResidual_independent_right (i : Nat) (a t s : RatPoly)
    (ht : QuaternionBlockIndependent i t) :
    RatPolyCoeffEqv (weightedResidual i (polyMul a t) s)
      (polyMul (weightedResidual i a s) t) := by
  have hp := project_mul_right_of_independent i a t ht
  have hq : RatPolyCoeffEqv (project i (polyMul (polyMul a t) s))
      (polyMul (project i (polyMul a s)) t) :=
    (project_congr i (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
      (fun | 0 => a | 1 => t | _ => s))).trans
      (project_mul_right_of_independent i (polyMul a s) t ht)
  exact ((hp.mul_right s).add (RatPolyCoeffEqv.neg hq)).trans
    (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.mul (.var 0) (.var 1)) (.var 2)) (.neg (.mul (.var 3) (.var 1))))
      (.mul (.add (.mul (.var 0) (.var 2)) (.neg (.var 3))) (.var 1)) (by decide)
      (fun | 0 => project i a | 1 => t | 2 => s | _ => project i (polyMul a s)))

/-- The actual-marginal fringe residual is centered in the endpoint weight a,
not merely in nu. Its proof needs no reciprocal of the terminal message. -/
theorem fringeResidual_centered (w : Q') (K width n i : Nat)
    (hi : i < N width) (hnot : i ∉ activeBlocks width) (s : RatPoly) :
    RatPolyCoeffEqv (project i (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n))
      (weightedResidual i (marginalWeight w K width n) s))) polyZero := by
  let a := polyMul (spatialWeight w K width) (terminalMessage w K width n)
  let t := terminalMessage w K width (n+1)
  have ht := terminal_inactive_independent w K width n i hi hnot
  have hp := weightedResidual_independent_right i a t s ht
  exact (project_congr i ((hp.mul_left a).trans (RatPolyCoeffEqv.mul_assoc a _ t).symm)).trans
    ((project_mul_right_of_independent i _ t ht).trans
      (((project_weightedResidual_zero i a s).mul_right t).trans (RatPolyCoeffEqv.mul_zero_left t)))

private theorem full_edge (w : Q') (K width n : Nat) :
    edgeWeight (N width) w K (activeBlocks width)
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) =
      edgeDensity w K width (terminalMessage w K width n) := by
  unfold edgeWeight edgeDensity
  rw [kineticWeight_eq_indexedProduct]
  rfl

/-- Coefficient-one dual control for any a-centered inactive-coordinate test.
The edge kernel is unchanged; no fictitious heat factor is inserted. -/
theorem inactive_dual_energy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n i : Nat) (hi : i < N width) (hnot : i ∉ activeBlocks width)
    {f q : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (hq : SupportedQuaternionBlocks (N width) q)
    (hc : RatPolyCoeffEqv (project i (polyMul
      (polyMul (spatialWeight w K width) (terminalMessage w K width n)) q)) polyZero) :
    marginalPair w K width n f q * marginalPair w K width n f q ≤
      energy w K width (terminalMessage w K width n) f * marginalPair w K width n q q := by
  let g := terminalMessage w K width n
  let a := polyMul (spatialWeight w K width) g
  let e := edgeDensity w K width g
  have ha := supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n)
  have hp (x : RatPoly) (hx : SupportedQuaternionBlocks (N width) x) :
      weightedPair (N width+N width) e (jump (N width) x) (jump (N width) q) ≈
        (2 : Q')*marginalPair w K width n x q := by
    have h := erased_jump_pairing (N width) w K i (activeBlocks width) hi hnot
      (activeBlocks_lt width) ha hx hq hc
    rw [full_edge] at h
    unfold SU2QuaternionWeightedProductDualEnergy.marginalPair at h
    rw [← terminal_product] at h
    exact h
  have hj : weightedPair (N width+N width) e (jump (N width) f) (jump (N width) f) ≈
      (2 : Q')*energy w K width g f :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_symm (energy_identity w K width (terminalMessage_supported w K width n) hf))
  have hcs := weighted_cauchySchwarz (N width+N width) e (jump (N width) f) (jump (N width) q)
    (edgeCertificate hw0 hw1 K width hK (terminalMessage_supported w K width n)
      (terminalMessage_certificate hw0 hw1 K width hK n)) (jump_supported hf) (jump_supported hq)
  have hcros := hp f hf
  have hdiag := hp q hq
  have he := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hcros)
      (Q'.mul_eqv_congr_left _ _ _ hcros)))
    (Q'.le_trans' _ _ _ hcs
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hj)
        (Q'.mul_eqv_congr_left _ _ _ hdiag))))
  have factor (x y : Q') : ((2 : Q')*x)*((2 : Q')*y) ≈ (4 : Q')*(x*y) :=
    poly_identity_of_normal_eq
      (.mul (.mul (.const 2) (.var 0)) (.mul (.const 2) (.var 1)))
      (.mul (.const 4) (.mul (.var 0) (.var 1))) (by decide) (fun | 0 => x | _ => y)
  exact Q'.le_of_mul_le_mul_left
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (factor _ _))
      (Q'.le_trans' _ _ _ he (Q'.le_of_eqv (factor _ _)))) (show (0 : Q') < (4 : Q') by decide)

/-- Concrete fringe tests supplied by the actual-marginal residual construction. -/
theorem fringeResidual_dual_energy {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K width : Nat) (hK : headCutoff w ≤ K)
    (n i : Nat) (hi : i < N width) (hnot : i ∉ activeBlocks width)
    {f s : RatPoly} (hf : SupportedQuaternionBlocks (N width) f)
    (hs : SupportedQuaternionBlocks (N width) s) :
    let q := weightedResidual i (marginalWeight w K width n) s
    marginalPair w K width n f q * marginalPair w K width n f q ≤
      energy w K width (terminalMessage w K width n) f * marginalPair w K width n q q :=
  inactive_dual_energy hw0 hw1 K width hK n i hi hnot hf
    (weightedResidual_supported i (marginalWeight_supported w K width n) hs)
    (fringeResidual_centered w K width n i hi hnot s)

end YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual.terminal_product
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual.terminal_inactive_independent
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual.weightedResidual_independent_right
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual.fringeResidual_centered
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual.inactive_dual_energy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFringeDual.fringeResidual_dual_energy
