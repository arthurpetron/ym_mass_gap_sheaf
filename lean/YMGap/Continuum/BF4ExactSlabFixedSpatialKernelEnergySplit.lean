/-
# Exact original energy splitting at a transfer-kernel component

For g=T^n1, a polynomial r whose T(g*r) pairs to zero with every Haar
test has energy exactly equal to its original odd-marginal squared norm.
If r is orthogonal to b in that SAME marginal, the energy of r+b is
the norm of r plus the energy of b. Original V-weighted transfer symmetry
removes the reverse mixed term; no raw coefficient-zero transfer assertion
is needed.

These are finite identities for the literal T=K V and nu=V*g*Tg. No
positivity, cutoff threshold, stationary law or strict spectral estimate
is assumed. The consumer is the constructed full-fringe decomposition;
the active-sector coercivity estimate remains separate.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow
import YMGap.Continuum.QuaternionHaarFamilySquare

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialKernelEnergySplit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferBound
  (stepWeight transferStep_kernelMap transferStep_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSymmetry (transferStep_weighted_symmetric)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWeightedMass (weightedMass_congr weightedMass_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletForm (energy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight marginalPair)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHaarKernelBound (kernelMap_congr)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarFamilySquare (haar_weighted_add)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] weightedMass spatialWeight baseLinks

private theorem transfer_congr (w : Q') (K width : Nat) {f q : RatPoly}
    (h : RatPolyCoeffEqv f q) :
    RatPolyCoeffEqv (transferStep w K width f) (transferStep w K width q) :=
  (transferStep_kernelMap w K width f).trans
    ((kernelMap_congr (N width) (stepWeight w K width) h).trans
      (transferStep_kernelMap w K width q).symm)

private theorem null_weighted_pair (w : Q') (K width : Nat) (g r p : RatPoly)
    (hnull : ∀ q, quaternionHaar (N width)
      (polyMul q (transferStep w K width (polyMul g r))) ≈ 0) :
    weightedMass w K width (polyMul p (transferStep w K width (polyMul g r))) ≈ 0 := by
  unfold weightedMass
  exact Q'.eqv_trans _ _ _
    (haar_of_coeff (RatPolyCoeffEqv.mul_assoc (spatialWeight w K width) p
      (transferStep w K width (polyMul g r))).symm)
    (hnull (polyMul (spatialWeight w K width) p))

private theorem terminal_diagonal (w : Q') (K width n : Nat) (f q : RatPoly) :
    weightedMass w K width
      (polyMul (polyMul (terminalMessage w K width n)
        (transferStep w K width (terminalMessage w K width n))) (polyMul f q)) ≈
      marginalPair w K width n f q := by
  rw [terminalMessage_next]
  unfold weightedMass marginalPair marginalWeight
  exact haar_of_coeff
    ((RatPolyCoeffEqv.mul_assoc (spatialWeight w K width)
      (polyMul (terminalMessage w K width n) (terminalMessage w K width (n+1)))
      (polyMul f q)).symm.trans
      (((RatPolyCoeffEqv.mul_assoc (spatialWeight w K width)
        (terminalMessage w K width n) (terminalMessage w K width (n+1))).symm).mul_right
          (polyMul f q)))

private theorem mixed_add_of_null (w : Q') (K width : Nat) {g r b : RatPoly}
    (hg : SupportedQuaternionBlocks (N width) g)
    (hr : SupportedQuaternionBlocks (N width) r)
    (hb : SupportedQuaternionBlocks (N width) b)
    (hnull : ∀ p, quaternionHaar (N width)
      (polyMul p (transferStep w K width (polyMul g r))) ≈ 0) :
    weightedMass w K width (polyMul (polyMul g (polyAdd r b))
      (transferStep w K width (polyMul g (polyAdd r b)))) ≈
      weightedMass w K width (polyMul (polyMul g b) (transferStep w K width (polyMul g b))) := by
  let gr := polyMul g r
  let gb := polyMul g b
  let tr := transferStep w K width gr
  let tb := transferStep w K width gb
  have hs : RatPolyCoeffEqv (polyMul g (polyAdd r b)) (polyAdd gr gb) :=
    RatPolyCoeffEqv.mul_add_right g r b
  have ht : RatPolyCoeffEqv (transferStep w K width (polyMul g (polyAdd r b)))
      (polyAdd tr tb) :=
    (transfer_congr w K width hs).trans (transferStep_add w K width gr gb)
  have hcross : weightedMass w K width (polyMul gr tb) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (transferStep_weighted_symmetric w K width (supported_polyMul hg hb) (supported_polyMul hg hr))
      (null_weighted_pair w K width g r gb hnull)
  have hrest : weightedMass w K width (polyMul (polyAdd gr gb) tb) ≈
      weightedMass w K width (polyMul gb tb) := by
    rw [polyMul_add_left_exact]
    exact Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hcross (Q'.eqv_refl _))
        (QPoly.q_zero_add_eqv _))
  exact Q'.eqv_trans _ _ _ (weightedMass_congr w K width (hs.mul ht))
    (Q'.eqv_trans _ _ _
      (weightedMass_congr w K width (RatPolyCoeffEqv.mul_add_right (polyAdd gr gb) tr tb))
      (Q'.eqv_trans _ _ _ (weightedMass_add w K width _ _)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (null_weighted_pair w K width g r (polyAdd gr gb) hnull) hrest)
          (QPoly.q_zero_add_eqv _))))

private theorem marginal_norm_add (w : Q') (K width n : Nat) (r b : RatPoly)
    (horth : marginalPair w K width n r b ≈ 0) :
    marginalPair w K width n (polyAdd r b) (polyAdd r b) ≈
      marginalPair w K width n r r + marginalPair w K width n b b := by
  have hs : RatPolyCoeffEqv (polyMul (polyAdd r b) (polyAdd r b))
      (polyAdd (polyAdd (polyMul r r) (polyMul b b))
        (polyAdd (polyMul r b) (polyMul r b))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
        (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))))
      (by decide) (fun | 0 => r | _ => b)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff (hs.mul_left (marginalWeight w K width n)))
    (Q'.eqv_trans _ _ _ (haar_weighted_add (N width) (marginalWeight w K width n) _ _)
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (haar_weighted_add (N width) (marginalWeight w K width n) _ _)
          (Q'.eqv_trans _ _ _ (haar_weighted_add (N width) (marginalWeight w K width n) _ _)
            (Q'.add_eqv_congr' horth horth)))
        (Q'.eqv_of_eq (Q'.add_zero' _))))

/-- Weak annihilation under arbitrary Haar tests suffices for energy equal
to the SAME marginal norm. No support premise is needed for this identity. -/
theorem terminal_kernel_energy (w : Q') (K width n : Nat) {r : RatPoly}
    (hnull : ∀ p, quaternionHaar (N width) (polyMul p
      (transferStep w K width (polyMul (terminalMessage w K width n) r))) ≈ 0) :
    energy w K width (terminalMessage w K width n) r ≈ marginalPair w K width n r r := by
  have hm := null_weighted_pair w K width (terminalMessage w K width n) r
    (polyMul (terminalMessage w K width n) r) hnull
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (terminal_diagonal w K width n r r) (Q'.neg_eqv_congr _ _ hm))
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.const 0))) (.var 0)
      (by decide) (fun _ => marginalPair w K width n r r))

/-- An orthogonal transfer-kernel component splits off with coefficient
one. Only the reverse mixed transfer pairing uses the support hypotheses. -/
theorem terminal_kernel_energy_split (w : Q') (K width n : Nat) {r b : RatPoly}
    (hr : SupportedQuaternionBlocks (N width) r)
    (hb : SupportedQuaternionBlocks (N width) b)
    (hnull : ∀ p, quaternionHaar (N width) (polyMul p
      (transferStep w K width (polyMul (terminalMessage w K width n) r))) ≈ 0)
    (horth : marginalPair w K width n r b ≈ 0) :
    energy w K width (terminalMessage w K width n) (polyAdd r b) ≈
      marginalPair w K width n r r + energy w K width (terminalMessage w K width n) b := by
  have hd := Q'.eqv_trans _ _ _ (terminal_diagonal w K width n (polyAdd r b) (polyAdd r b))
    (marginal_norm_add w K width n r b horth)
  have hm := mixed_add_of_null w K width (terminalMessage_supported w K width n) hr hb hnull
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hd (Q'.neg_eqv_congr _ _ hm))
    (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (Q'.add_eqv_congr' (Q'.eqv_symm (terminal_diagonal w K width n b b)) (Q'.eqv_refl _))))

#print axioms terminal_kernel_energy
#print axioms terminal_kernel_energy_split

end YMGap.Continuum.BF4ExactSlabFixedSpatialKernelEnergySplit
