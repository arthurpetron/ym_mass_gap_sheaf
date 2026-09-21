/-
# Width- and depth-independent relative derivatives of the ACTUAL message

For g = T^(n+1)1 and any active link rotation D, construct both positive
certificates C(w)g - h(w)Dg and C(w)g + h(w)Dg. Here h is the existing
one-factor heat floor and C is the explicit quartic heat derivative cap.
The entire original spatial action and terminal history remain in g.

No reciprocal of g, factorized substitute, or volume-dependent product floor
is used. Nome-uniform control is not proved. This is source regularity,
not the missing near-one-nome relative energy estimate or continuum survival.
-/

import YMGap.Continuum.SU2QuaternionProductHeatAngularMessage
import YMGap.Continuum.BF4ExactSlabFixedSpatialConditionalMessage

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalAngularBound

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
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionWeightedProductLocalGap
open YMGap.Continuum.SU2QuaternionProductHeatAngularMessage
open YMGap.Continuum.SU2QuaternionRelativeHeatAngularBound
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarHeatAngularDerivative
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

private def clearBounds {blocks : Nat} {g r d : RatPoly} {c h : Q'}
    (hc : (0 : Q') ≤ c) (hh : (0 : Q') ≤ h)
    (F : Certificate blocks (polyAdd g (polyNeg (polyMul (cap h) r))))
    (U : Certificate blocks (polyAdd (polyMul (cap c) r) (polyNeg d)))
    (L : Certificate blocks (polyAdd (polyMul (cap c) r) d)) :
    Certificate blocks (polyAdd (polyMul (cap c) g) (polyNeg (polyMul (cap h) d))) ×
    Certificate blocks (polyAdd (polyMul (cap c) g) (polyMul (cap h) d)) := by
  let env : Nat → RatPoly := fun | 0 => g | 1 => r | 2 => d | 3 => cap c | _ => cap h
  let A := (Certificate.constant blocks c hc).mul F
  exact ⟨.ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 3) (.var 0)) (.neg (.mul (.var 4) (.var 2))))
      (.add (.mul (.var 3) (.add (.var 0) (.neg (.mul (.var 4) (.var 1)))))
        (.mul (.var 4) (.add (.mul (.var 3) (.var 1)) (.neg (.var 2)))))
      (by decide) env) (A.add ((Certificate.constant blocks h hh).mul U)),
    .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.var 3) (.var 0)) (.mul (.var 4) (.var 2)))
      (.add (.mul (.var 3) (.add (.var 0) (.neg (.mul (.var 4) (.var 1)))))
        (.mul (.var 4) (.add (.mul (.var 3) (.var 1)) (.var 2))))
      (by decide) env) (A.add ((Certificate.constant blocks h hh).mul L))⟩

/-- Two denominator-cleared relative derivative certificates on the SAME
terminal message. Width, depth, selected link, and cutoff remain quantified;
the two constants depend only on the explicit strict nome. -/
def terminalMessage_angular_bounds {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    let g := terminalMessage w K width (n+1)
    let d := angularDerivative (4*s+i) (4*s+j) g
    Certificate (N width)
      (polyAdd (polyMul (cap (heatDerivativeCap w 32)) g)
        (polyNeg (polyMul (cap (headFloor w)) d))) ×
    Certificate (N width)
      (polyAdd (polyMul (cap (heatDerivativeCap w 32)) g)
        (polyMul (cap (headFloor w)) d)) := by
  have hsn := activeBlocks_lt width s hs
  have hrange : ∀ k, k ∈ eraseIndex s (activeBlocks width) → k < N width :=
    fun k hk => activeBlocks_lt width k (mem_of_mem_erase s hk)
  have B := productMap_angular_bounds (N width) hw0 hw1 K hK s _ hsn
    (not_mem_erase s (activeBlocks_nodup width)) hrange
    (supported_polyMul (spatialWeight_supported w K width) (terminalMessage_supported w K width n))
    ((spatialCertificate hw0 hw1 K width (N width) (Nat.le_refl _) hK).mul
      (terminalMessage_certificate hw0 hw1 K width hK n)) hi hj
  have pin := angularDerivative_congr (4*s+i) (4*s+j) (terminal_cons_pin w K width n s hs)
  have U := Certificate.ofCoeff ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg pin)) B.1
  have L := Certificate.ofCoeff ((RatPolyCoeffEqv.refl _).add pin) B.2
  have F := Certificate.ofCoeff
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.neg (cap_mul_left (headFloor w) _)))
    (conditionalMessage_lowerCertificate hw0 hw1 K width hK n s hs)
  have hc := (heatAngularInterval (show s < N width + N width by omega)
    (show N width+s < N width + N width by omega)
    (show 4*(N width+s)+i < 4*(N width+N width) by omega)
    (show 4*(N width+s)+j < 4*(N width+N width) by omega) hw0 hw1 K).nonnegative
  exact clearBounds hc (Q'.le_of_lt (headFloor_positive hw0 hw1)) F U L

/-- Multiplying the two relative certificates retains the exact negative
derivative square. Any further certified positive background may multiply
this witness, including the complete original spatial action. -/
def terminalMessage_angular_square_certificate {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    let g := terminalMessage w K width (n+1)
    let d := angularDerivative (4*s+i) (4*s+j) g
    let a := polyMul (cap (heatDerivativeCap w 32)) g
    let b := polyMul (cap (headFloor w)) d
    Certificate (N width) (polyAdd (polyMul a a) (polyNeg (polyMul b b))) := by
  have B := terminalMessage_angular_bounds hw0 hw1 K width hK n s hs hi hj
  exact .ofCoeff (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 1) (.var 1))))
    (.mul (.add (.var 0) (.neg (.var 1))) (.add (.var 0) (.var 1)))
    (by decide) (fun
      | 0 => polyMul (cap (heatDerivativeCap w 32)) (terminalMessage w K width (n+1))
      | _ => polyMul (cap (headFloor w))
          (angularDerivative (4*s+i) (4*s+j) (terminalMessage w K width (n+1))))) (B.1.mul B.2)

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

/-- A concrete relative quadratic bound against ANY certified positive
background on the original carrier. In particular the background may be
the complete spatial action; no independence or normalization is assumed. -/
theorem terminalMessage_angular_weighted_square {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (n s : Nat)
    (hs : s ∈ activeBlocks width) {i j : Nat} (hi : i < 4) (hj : j < 4)
    {R : RatPoly} (HR : Certificate (N width) R) :
    let g := terminalMessage w K width (n+1)
    let d := angularDerivative (4*s+i) (4*s+j) g
    (headFloor w * headFloor w) * weightedPair (N width) R d d ≤
      (heatDerivativeCap w 32 * heatDerivativeCap w 32) * weightedPair (N width) R g g := by
  let g := terminalMessage w K width (n+1)
  let d := angularDerivative (4*s+i) (4*s+j) g
  let a := polyMul (cap (heatDerivativeCap w 32)) g
  let b := polyMul (cap (headFloor w)) d
  have P := (terminalMessage_angular_square_certificate hw0 hw1 K width hK n s hs hi hj).mul HR
  have he : quaternionHaar (N width)
      (polyMul (polyAdd (polyMul a a) (polyNeg (polyMul b b))) R) ≈
      (heatDerivativeCap w 32 * heatDerivativeCap w 32) * weightedPair (N width) R g g +
        -((headFloor w * headFloor w) * weightedPair (N width) R d d) :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.add (.var 0) (.neg (.var 1))) (.var 2))
      (.add (.mul (.var 0) (.var 2)) (.neg (.mul (.var 1) (.var 2))))
      (by decide) (fun | 0 => polyMul a a | 1 => polyMul b b | _ => R)))
      (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
        (Q'.add_eqv_congr' (scaled_square_pair (N width) (heatDerivativeCap w 32) g R)
          (Q'.eqv_trans _ _ _ (haar_neg _ _)
            (Q'.neg_eqv_congr _ _ (scaled_square_pair (N width) (headFloor w) d R)))))
  exact Q'.le_of_sub_nonneg (Q'.le_trans' _ _ _ P.haar_nonnegative (Q'.le_of_eqv he))

end YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalAngularBound

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalAngularBound.terminalMessage_angular_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalAngularBound.terminalMessage_angular_square_certificate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalAngularBound.terminalMessage_angular_weighted_square
