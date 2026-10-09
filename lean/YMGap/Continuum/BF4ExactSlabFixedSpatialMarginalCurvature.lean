/-
Lower frozen curvature order for the ORIGINAL odd marginal V*g_n*g_(n+1).
The spatial certificate and both actual terminal output-jet orders tensorize
under arbitrary certified insertions. This is integrated denominator-cleared
order, NOT a Certificate for the marginal, weighted Bochner, variance or gap.
The reciprocal passage to a W-weighted log-Hessian remains a separate join.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCurvature
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram
import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection (quaternionHaar)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.ClusterCount4DProgress (Z4Link)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (spatialWeight spatialWeight_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalMessage_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalLocalSignedGram
  (sourceMarginalFirst sourceMarginalSecond terminal_marginal_curvature_nonnegative_nearFlat)
open YMGap.Continuum.SU2QuaternionPairedFrozenHeatPrefixCurvature
  (nearFlatPrefixCurvatureCost nearFlatPrefixFrozenCurvatureCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteHeatPrefixCurvature
  (plaquetteCurvatureCost plaquetteCurvatureCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialCurvature
  (spatialWeight_frozen_curvature_nearFlat_certificate)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarConditionalScorePairedFrame (threeSquare)
open YMGap.Continuum.QPolyHaarPairedAtFrozenChain (frozenFirstAt)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFrozenHessian (frozenSecondAt)
open YMGap.Continuum.QPolyHaarPairedAtFrozenZero (one_blockIndependent)
open YMGap.Continuum.QuaternionHaarPairedAtFrozenCurvatureProduct

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks spatialWeight terminalMessage transferStep

/-- Opposite certified squares tensorize INTEGRATED orders. No polynomial
certificate for either factor's curvature is inferred from its Haar order. -/
private theorem productOrder {blocks : Nat} (s : Nat) (C D : Q') (p q : RatPoly)
    (u : Fin 3 → RatPoly)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q)
    (P : ∀ {R : RatPoly}, Certificate blocks R →
      (0 : Q') ≤ quaternionHaar blocks (polyMul R (frozenCurvatureAt s C p u)))
    (Q : ∀ {R : RatPoly}, Certificate blocks R →
      (0 : Q') ≤ quaternionHaar blocks (polyMul R (frozenCurvatureAt s D q u)))
    {R : RatPoly} (PR : Certificate blocks R) :
    (0 : Q') ≤ quaternionHaar blocks
      (polyMul R (frozenCurvatureAt s (C+D) (polyMul p q) u)) := by
  have hporder := P (PR.mul (Certificate.square q hq))
  have hqorder := Q (PR.mul (Certificate.square p hp))
  have hpin : RatPolyCoeffEqv
      (polyMul R (frozenCurvatureAt s (C+D) (polyMul p q) u))
      (polyAdd
        (polyMul (polyMul R (polyMul q q)) (frozenCurvatureAt s C p u))
        (polyMul (polyMul R (polyMul p p)) (frozenCurvatureAt s D q u))) :=
    ((frozenCurvatureAt_product_pin s C D p q u).mul_left R).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 0) (.add (.mul (.var 1) (.var 2)) (.mul (.var 3) (.var 4))))
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 2))
          (.mul (.mul (.var 0) (.var 3)) (.var 4)))
        (by decide) (fun
          | 0 => R | 1 => polyMul q q | 2 => frozenCurvatureAt s C p u
          | 3 => polyMul p p | _ => frozenCurvatureAt s D q u))
  have hv := Q'.eqv_trans _ _ _ (haar_of_coeff (blocks := blocks) hpin)
    (quaternionHaar_append blocks _ _)
  exact Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ hporder hqorder) (Q'.ge_of_eqv hv)

/-- Every actual terminal depth has lower-output frozen curvature order,
including g_0=1. The cost is fixed-nome and depth/width independent. -/
theorem terminalMessage_frozen_curvature_nonnegative_nearFlat {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width s n : Nat) (hs : s ∈ activeBlocks width)
    (hK : nearFlatPrefixFrozenCurvatureCutoff w ≤ K)
    (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i))
    {R : RatPoly} (PR : Certificate (N width) R) :
    (0 : Q') ≤ quaternionHaar (N width)
      (polyMul R (frozenCurvatureAt s (nearFlatPrefixCurvatureCost w)
        (terminalMessage w K width n) u)) := by
  cases n with
  | zero =>
      have hC : (0 : Q') ≤ nearFlatPrefixCurvatureCost w :=
        Q'.zero_le_add _ _
          (JacobiHeatPrefixCurvaturePrecision.nearFlatCurvatureCap_nonnegative hw0)
          Q'.zero_le_one
      have P0 := frozen_independent_curvature_zero_certificate (blocks := N width)
        s polyOne u (one_blockIndependent s)
      have PC := frozenCurvatureAt_raise_cost_certificate s polyOne u hu
        (supported_one (N width)) hC P0
      have hzero : terminalMessage w K width 0 = polyOne := by
        unfold terminalMessage
        rfl
      rw [hzero]
      exact (PR.mul PC).haar_nonnegative
  | succ m =>
      let a := terminalMessage w K width m
      let A := transferStep w K width a
      let C := nearFlatPrefixCurvatureCost w
      have h := terminal_marginal_curvature_nonnegative_nearFlat hw0 hw1
        K width s m 0 hs hK u hu PR
      simp only [Nat.add_zero] at h
      have hclear : RatPolyCoeffEqv (frozenCurvatureAt s C A u)
          (polyAdd
            (polyMul A (polyAdd (sourceMarginalSecond w K width s a u)
              (polyMul (polyMul (cap C) (threeSquare u)) A)))
            (polyNeg (polyMul (sourceMarginalFirst w K width s a u)
              (sourceMarginalFirst w K width s a u)))) :=
        coeffEvalExpr_eqv_of_normalize_eq
          (.add (.mul (.var 0) (.mul (.var 1) (.mul (.var 2) (.var 2))))
            (.add (.mul (.var 2) (.var 4)) (.neg (.mul (.var 3) (.var 3)))))
          (.add (.mul (.var 2)
            (.add (.var 4) (.mul (.mul (.var 0) (.var 1)) (.var 2))))
            (.neg (.mul (.var 3) (.var 3))))
          (by decide) (fun
            | 0 => cap C | 1 => threeSquare u | 2 => A
            | 3 => frozenFirstAt s u A | _ => frozenSecondAt s u A)
      have hout : (0 : Q') ≤ quaternionHaar (N width)
          (polyMul R (frozenCurvatureAt s C A u)) :=
        Q'.le_trans' _ _ _ h
          (Q'.ge_of_eqv (haar_of_coeff (hclear.mul_left R)))
      simpa only [A, a, C, terminalMessage_next, Nat.succ_eq_add_one] using hout

/-- Actual full-marginal cost: six spatial faces plus TWO terminal messages. -/
def marginalCurvatureCost (w : Q') : Q' :=
  (6*plaquetteCurvatureCost w + nearFlatPrefixCurvatureCost w) + nearFlatPrefixCurvatureCost w

/-- Both cutoffs are produced before the finite action is selected. -/
def marginalCurvatureCutoff (w : Q') : Nat :=
  max (plaquetteCurvatureCutoff w) (nearFlatPrefixFrozenCurvatureCutoff w)

/-- Lower frozen curvature of the literal chronological odd marginal under
EVERY certified insertion. This order is not a marginal polynomial certificate
and does not yet remove the W denominator in weighted log-Hessian estimates. -/
theorem marginalWeight_frozen_curvature_nonnegative_nearFlat {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width n : Nat) (hK : marginalCurvatureCutoff w ≤ K)
    (selected : Z4Link) (hl : selected ∈ baseLinks width)
    (hs : (baseLinks width).idxOf selected ∈ activeBlocks width)
    (u : Fin 3 → RatPoly)
    (hu : ∀ i, SupportedQuaternionBlocks (N width) (u i))
    {R : RatPoly} (PR : Certificate (N width) R) :
    (0 : Q') ≤ quaternionHaar (N width)
      (polyMul R (frozenCurvatureAt ((baseLinks width).idxOf selected)
        (marginalCurvatureCost w) (marginalWeight w K width n) u)) := by
  have hsp : plaquetteCurvatureCutoff w ≤ K := by unfold marginalCurvatureCutoff at hK; omega
  have hterm : nearFlatPrefixFrozenCurvatureCutoff w ≤ K := by
    unfold marginalCurvatureCutoff at hK
    omega
  let s := (baseLinks width).idxOf selected
  let V := spatialWeight w K width
  let g := terminalMessage w K width n
  let h := terminalMessage w K width (n+1)
  let P := spatialWeight_frozen_curvature_nearFlat_certificate hw0 hw1 K width hsp selected hl u hu
  have PV : ∀ {R : RatPoly}, Certificate (N width) R →
      (0 : Q') ≤ quaternionHaar (N width)
        (polyMul R (frozenCurvatureAt s (6*plaquetteCurvatureCost w) V u)) :=
    fun PR => (PR.mul P).haar_nonnegative
  have Pg : ∀ {R : RatPoly}, Certificate (N width) R →
      (0 : Q') ≤ quaternionHaar (N width)
        (polyMul R (frozenCurvatureAt s (nearFlatPrefixCurvatureCost w) g u)) :=
    fun PR => terminalMessage_frozen_curvature_nonnegative_nearFlat
      hw0 hw1 K width s n hs hterm u hu PR
  have Ph : ∀ {R : RatPoly}, Certificate (N width) R →
      (0 : Q') ≤ quaternionHaar (N width)
        (polyMul R (frozenCurvatureAt s (nearFlatPrefixCurvatureCost w) h u)) :=
    fun PR => terminalMessage_frozen_curvature_nonnegative_nearFlat
      hw0 hw1 K width s (n+1) hs hterm u hu PR
  have PVg : ∀ {R : RatPoly}, Certificate (N width) R →
      (0 : Q') ≤ quaternionHaar (N width)
        (polyMul R (frozenCurvatureAt s
          (6*plaquetteCurvatureCost w+nearFlatPrefixCurvatureCost w) (polyMul V g) u)) :=
    fun PR => productOrder s _ _ V g u (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n) PV Pg PR
  exact productOrder s _ _ (polyMul V g) h u
    (supported_polyMul (spatialWeight_supported w K width)
      (terminalMessage_supported w K width n))
    (terminalMessage_supported w K width (n+1)) PVg Ph PR

end YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature.productOrder
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature.terminalMessage_frozen_curvature_nonnegative_nearFlat
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature.marginalCurvatureCost
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature.marginalCurvatureCutoff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialMarginalCurvature.marginalWeight_frozen_curvature_nonnegative_nearFlat
