/-
# The angular weight defect against the SAME original odd marginal

For q=P_fringe(V*g_n), the Taylor weight q^2 is not the original odd
marginal q*P_full(q). Keep their difference as the signed integral
sum_i H[q*(P_full(q)-q)*Gamma_i(f)]. Exact inactive integration identifies
the remaining term with the literal original marginal V*g_n*g_(n+1).

The full signed source is differentiated before taking its square. No
sign, size, parameter-uniform bound or scaling survival is asserted for
the weight defect. Original spatial and terminal factors remain present.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceTaylor
import YMGap.Continuum.SU2QuaternionAngularSquareLocality
import YMGap.Constructive.FinSumAlg

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularReindex
open YMGap.Continuum.SU2QuaternionAngularSquareLocality
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionProductHeatMarginals (productMap)
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy (sourceMoment)
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor (weightedAngularEnergy)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyFlow (fringeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket (terminalMessage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual (marginalWeight)
open YMGap.Continuum.BF4ExactSlabFixedSpatialProjectedSourceEnergy
  (projectedEndpointSource oddMoment_projected_source)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks
attribute [local irreducible] baseLinks terminalMessage marginalWeight projectedEndpointSource

/-- The original odd-marginal angular energy, with no replacement density. -/
def marginalAngular (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  finSum (fun i => H (N width)
    (polyMul (marginalWeight w K width n) (blockAngularSquare i f))) (N width)

/-- The complete signed difference between q*P(q) and q^2. -/
def angularWeightDefect (w : Q') (K width n : Nat) (f : RatPoly) : Q' :=
  let q := projectedEndpointSource w K width (terminalMessage w K width n)
  let Pq := productMap (N width) w K (List.range (N width)) q
  finSum (fun i => H (N width)
    (polyMul (polyMul q (polyAdd Pq (polyNeg q))) (blockAngularSquare i f))) (N width)

/-- A differentiated block on the fringe contributes zero coefficientwise;
away from it, differentiation preserves the required independence. This
avoids the false syntactic claim that a formal zero derivative is empty. -/
theorem angular_moment_pin (w : Q') (K width n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f)
    (hind : ∀ j, j ∈ fringeBlocks width → QuaternionBlockIndependent j f)
    (i : Nat) (hi : i < N width) :
    H (N width) (polyMul (marginalWeight w K width n) (blockAngularSquare i f)) ≈
      sourceMoment (N width) w K (List.range (N width))
        (projectedEndpointSource w K width (terminalMessage w K width n))
        (blockAngularSquare i f) := by
  by_cases hm : i ∈ fringeBlocks width
  · have hz := blockAngularSquare_zero (hind i hm)
    have hl : H (N width)
        (polyMul (marginalWeight w K width n) (blockAngularSquare i f)) ≈ 0 :=
      haar_of_coeff ((hz.mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _))
    have hr : sourceMoment (N width) w K (List.range (N width))
        (projectedEndpointSource w K width (terminalMessage w K width n))
        (blockAngularSquare i f) ≈ 0 :=
      haar_of_coeff (((hz.mul_left _).trans (RatPolyCoeffEqv.mul_zero_right _)).mul_right _
        |>.trans (RatPolyCoeffEqv.mul_zero_left _))
    exact Q'.eqv_trans _ _ _ hl hr.symm
  · exact oddMoment_projected_source w K width n (blockAngularSquare i f)
      (blockAngularSquare_supported hi hf)
      (fun j hj => blockAngularSquare_independent_of_ne (block := i) (selected := j)
        (fun he => hm (he.symm ▸ hj)) (hind j hj))

private theorem squareWeight_add_defect (blocks : Nat) (w : Q') (K : Nat)
    (q p : RatPoly) :
    H blocks (polyMul (polyMul q q) p) +
      H blocks (polyMul (polyMul q
        (polyAdd (productMap blocks w K (List.range blocks) q) (polyNeg q))) p) ≈
      sourceMoment blocks w K (List.range blocks) q p := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_append blocks _ _)) ?_
  exact haar_of_coeff (coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.mul (.var 0) (.var 0)) (.var 2))
      (.mul (.mul (.var 0) (.add (.var 1) (.neg (.var 0)))) (.var 2)))
    (.mul (.mul (.var 0) (.var 2)) (.var 1)) (by decide)
    (fun | 0 => q | 1 => productMap blocks w K (List.range blocks) q | _ => p))

/-- Exact leading-weight conversion to the ORIGINAL odd marginal. The
signed defect is retained, never assumed zero or assigned a sign. -/
theorem angular_weight_identity (w : Q') (K width n : Nat) (f : RatPoly)
    (hf : SupportedQuaternionBlocks (N width) f) (hb : 0 < N width)
    (hind : ∀ j, j ∈ fringeBlocks width → QuaternionBlockIndependent j f) :
    weightedAngularEnergy (N width-1)
        (projectedEndpointSource w K width (terminalMessage w K width n)) f +
      angularWeightDefect w K width n f ≈ marginalAngular w K width n f := by
  have hN : N width-1+1 = N width := Nat.sub_add_cancel hb
  unfold weightedAngularEnergy angularWeightDefect marginalAngular
  rw [hN]
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (finSum_add _ _ (N width))) ?_
  exact finSum_eqv_congr_lt _ _ (N width) (fun i hi =>
    Q'.eqv_trans _ _ _ (squareWeight_add_defect (N width) w K _ (blockAngularSquare i f))
      (Q'.eqv_symm (angular_moment_pin w K width n f hf hind i hi)))

#print axioms marginalAngular
#print axioms angularWeightDefect
#print axioms angular_moment_pin
#print axioms angular_weight_identity

end YMGap.Continuum.BF4ExactSlabFixedSpatialAngularMarginal
