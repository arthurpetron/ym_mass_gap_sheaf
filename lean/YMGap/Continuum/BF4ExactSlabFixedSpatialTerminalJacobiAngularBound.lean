/-
# The actual terminal message with a floor-free relative angular constant

For g = T^(n+1)1 and every active output-link rotation, the original action
and entire terminal history satisfy B(w)g ± Dg >= 0 in the Haar certificate
cone. Here B(w)=32*JacobiShiftedRelativeSlope.budget(w)+1. The positive heat
floor enters only the explicitly late cutoff, not this constant.

This is a source-regularity estimate. It is not the missing signed relative
energy estimate, a near-one-nome bound, or a completed/continuum mass gap.
-/

import YMGap.Continuum.SU2QuaternionProductHeatRelativeAngularMessage
import YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalAngularBound

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalJacobiAngularBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialOrder
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticHeat
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
open YMGap.Continuum.BF4ExactSlabFixedSpatialDirichletWindow (terminalMessage_next)
open YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionProductHeatRelativeAngularMessage
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarRelativeAngularBound
open YMGap.Continuum.QuaternionHaarHeatRelativeAngularBound
open YMGap.Continuum.QuaternionHaarWeightedCauchySchwarz (weightedPair)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] kineticWeight spatialWeight baseLinks

private theorem terminal_cons_pin (w : Q') (K width n s : Nat)
    (hs : s ∈ activeBlocks width) :
    RatPolyCoeffEqv (terminalMessage w K width (n+1))
      (productMap (N width) w K (s::eraseIndex s (activeBlocks width))
        (polyMul (spatialWeight w K width) (terminalMessage w K width n))) := by
  rw [← terminalMessage_next]
  unfold transferStep step
  rw [kineticWeight_eq_indexedProduct]
  exact partialHaarHeads_congr (N width)
    ((polynomialProduct_perm _ (select_perm s hs)).mul_right _)

/-- Every positive-depth original terminal source, with a cutoff, width,
depth and active-link independent relative constant at the supplied nome. -/
def terminalMessageRelativeBound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K) (n s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    RelativeBound (N width) (4*s+i) (4*s+j)
      (terminalMessage w K width (n+1)) (relativeCap w 32) := by
  have hhead := Nat.le_trans (headCutoff_le_relativeCutoff w 32) hK
  exact .ofCoeff (terminal_cons_pin w K width n s hs)
    (productMapRelativeBound (N width) hw0 hw1 K hK s _ (activeBlocks_lt width s hs)
      (not_mem_erase s (activeBlocks_nodup width))
      (fun k hk => activeBlocks_lt width k (mem_of_mem_erase s hk))
      (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n))
      ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hhead).mul
        (terminalMessage_certificate hw0 hw1 K width hhead n)) hi hj)

/-- The derivative square is retained with its negative sign, against the
same terminal message, without a heat-floor coefficient multiplying it. -/
def terminalMessageRelativeSquare {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K) (n s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    let g := terminalMessage w K width (n+1)
    let d := angularDerivative (4*s+i) (4*s+j) g
    let a := polyMul (cap (relativeCap w 32)) g
    Certificate (N width) (polyAdd (polyMul a a) (polyNeg (polyMul d d))) := by
  let P := terminalMessageRelativeBound hw0 hw1 K width hK n s hs hi hj
  exact .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 1))))
    (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.var 1)))
    (by decide) (fun
      | 0 => polyMul (cap (relativeCap w 32)) (terminalMessage w K width (n+1))
      | _ => angularDerivative (4*s+i) (4*s+j) (terminalMessage w K width (n+1))))
    (P.upper.mul P.lower)

private theorem haar_neg (blocks : Nat) : ∀ p : RatPoly,
    quaternionHaar blocks (polyNeg p) ≈ -(quaternionHaar blocks p)
  | [] => by change (0 : Q') ≈ -0; decide
  | t::p => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.neg_mul_eqv t.2 (quaternionHaarMono blocks t.1)) (haar_neg blocks p))
      (Q'.eqv_symm (Q'.neg_add_eqv_split _ _))

private theorem scaled_square_pair (blocks : Nat) (c : Q') (p R : RatPoly) :
    quaternionHaar blocks
      (polyMul (polyMul (polyMul (cap c) p) (polyMul (cap c) p)) R) ≈
      (c*c) * weightedPair blocks R p p := by
  have he : RatPolyCoeffEqv
      (polyMul (polyMul (polyMul (cap c) p) (polyMul (cap c) p)) R)
      (polySmul (c*c) (polyMul (polyMul p p) R)) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.var 2))
      (.mul (.mul (.var 0) (.var 0)) (.mul (.mul (.var 1) (.var 1)) (.var 2)))
      (by decide) (fun | 0 => cap c | 1 => p | _ => R)).trans
      (((cap_mul c c).mul_right _).trans (cap_mul_left (c*c) _))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he) (quaternionHaar_polySmul _ _ _)

/-- Concrete quadratic source bound under any positive background, including
the full shared-variable spatial action. No normalization is discarded. -/
theorem terminalMessageRelativeWeightedSquare {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : relativeCutoff w 32 ≤ K) (n s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    {R : RatPoly} (HR : Certificate (N width) R) :
    let g := terminalMessage w K width (n+1)
    let d := angularDerivative (4*s+i) (4*s+j) g
    weightedPair (N width) R d d ≤
      (relativeCap w 32 * relativeCap w 32) * weightedPair (N width) R g g := by
  let g := terminalMessage w K width (n+1)
  let d := angularDerivative (4*s+i) (4*s+j) g
  let a := polyMul (cap (relativeCap w 32)) g
  have P := (terminalMessageRelativeSquare hw0 hw1 K width hK n s hs hi hj).mul HR
  have he : quaternionHaar (N width)
      (polyMul (polyAdd (polyMul a a) (polyNeg (polyMul d d))) R) ≈
      (relativeCap w 32 * relativeCap w 32) * weightedPair (N width) R g g +
        -(weightedPair (N width) R d d) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => polyMul a a | 1 => polyMul d d | _ => R)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' (scaled_square_pair (N width) (relativeCap w 32) g R) (haar_neg _ _)))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ P.haar_nonnegative (Q'.le_of_eqv he))

end YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalJacobiAngularBound

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalJacobiAngularBound.terminalMessageRelativeBound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalJacobiAngularBound.terminalMessageRelativeSquare
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalJacobiAngularBound.terminalMessageRelativeWeightedSquare
