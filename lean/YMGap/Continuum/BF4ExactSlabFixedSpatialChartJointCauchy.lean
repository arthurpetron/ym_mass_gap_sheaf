/-
# Joint cutoff and boundary-time Cauchy data for the actual common-chart scalar

The physical signed presentations x,y and their supplied common chart H stay
fixed. Each raw term is chartScalar: the original selected-chain finiteValue,
with its original partition and the literal mirrored/ordinary placements.
Its boundary-time modulus is independent of the late heat-cutoff stage.

At one computed intermediate boundary depth, the existing finiteCauchy gives
cutoff control. Three comparisons through that same depth give a rectangular
two-parameter estimate, without a cutoff estimate uniform over all depths.
An explicit diagonal retains Type-level Cauchy data and defines the joint
CReal limit. Boundary depth is not a physical lag, and no spatial-width or
spacing-uniform estimate or completed cutoff-limit carrier is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (placedSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (radius encodeChart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteCauchy)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyMul)
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)

local infix:50 " ≃ " => Q'.eqv

/-- Cutoff Cauchy data for the same original action at one fixed boundary
depth. Radius guards are only needed for the boundary-time comparison. -/
def chartCutoffCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width H : Nat) (x y : PhysicalSpan width) (t : Nat) :
    QCauchy (fun stage => chartScalar hw0 hw1 width stage H x y t) :=
  let E := adjacentEvenExtent (width+t+H)
  let start := width+1
  finiteCauchy w hw0 hw1 E (chainIds E width start (t+(2*H+t)))
    (fun _ hi => chainIds_physical hi)
    (polyMul (placedSpan E (start+t) (mirrorSpan H (encodeChart H x.val)))
      (placedSpan E (start+t) (encodeChart H y.val)))

-- Use the proved scalar estimates without expanding the finite Haar sums.
attribute [local irreducible] chartScalar

/-- A common comparison depth, at one quarter of the error budget. Stage
zero only selects the existing stage-independent boundary-time modulus. -/
def chartJointTimeThreshold {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) (epsilon : Q') : Nat :=
  (chartCauchy hw0 hw1 width 0 H x y hx hy).M
    (HalfPow.half * (HalfPow.half * epsilon))

/-- Cutoff control at the displayed intermediate boundary depth, rather
than a cutoff estimate uniform over an unbounded family of chains. -/
def chartJointCutoffThreshold {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) (epsilon : Q') : Nat :=
  (chartCutoffCauchy hw0 hw1 width H x y
    (chartJointTimeThreshold hw0 hw1 width H x y hx hy epsilon)).M
      (HalfPow.half * (HalfPow.half * epsilon))

/-- The executable diagonal threshold retains both independent budgets. -/
def chartJointModulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) (epsilon : Q') : Nat :=
  max (chartJointTimeThreshold hw0 hw1 width H x y hx hy epsilon)
    (chartJointCutoffThreshold hw0 hw1 width H x y hx hy epsilon)

attribute [local irreducible] chartCutoffCauchy

private theorem three_quarter_chain (epsilon : Q') (he : (0 : Q') < epsilon)
    (u v x z : Q')
    (hu : u ≤ v + HalfPow.half * (HalfPow.half * epsilon))
    (hv : v ≤ x + HalfPow.half * (HalfPow.half * epsilon))
    (hx : x ≤ z + HalfPow.half * (HalfPow.half * epsilon)) : u ≤ z + epsilon := by
  let q := HalfPow.half * (HalfPow.half * epsilon)
  have hq : (0 : Q') ≤ q := Q'.le_of_lt
    (ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon he))
  have h1 := Q'.le_trans' _ _ _ hu (Q'.add_le_add_right _ _ q hv)
  have h2 := Q'.le_trans' _ _ _ h1
    (Q'.add_le_add_right _ _ q (Q'.add_le_add_right _ _ q hx))
  have h3 := Q'.le_trans' _ _ _ h2 (Q'.add_le_self_of_nonneg _ q hq)
  have hfour : (((z+q)+q)+q)+q ≃ z+epsilon := by
    have hqq : q+q ≃ HalfPow.half*epsilon := ExpNeg.two_halves (HalfPow.half*epsilon)
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv ((z+q)+q) q q) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (q+q) (Q'.add_assoc_eqv z q q)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv z (q+q) (q+q)) ?_
    exact Q'.add_eqv_congr_left z _ _
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hqq hqq) (ExpNeg.two_halves epsilon))
  exact Q'.le_trans' _ _ _ h3 (Q'.le_of_eqv hfour)

/-- Rectangular control of independently late cutoff stages k,j and boundary
depths t,u. All four scalars retain the same chart and physical presentations. -/
theorem chartJoint_rectangle {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H)
    (epsilon : Q') (he : (0 : Q') < epsilon) (k t j u : Nat)
    (hk : chartJointCutoffThreshold hw0 hw1 width H x y hx hy epsilon ≤ k)
    (ht : chartJointTimeThreshold hw0 hw1 width H x y hx hy epsilon ≤ t)
    (hj : chartJointCutoffThreshold hw0 hw1 width H x y hx hy epsilon ≤ j)
    (hu : chartJointTimeThreshold hw0 hw1 width H x y hx hy epsilon ≤ u) :
    chartScalar hw0 hw1 width k H x y t ≤ chartScalar hw0 hw1 width j H x y u + epsilon ∧
      chartScalar hw0 hw1 width j H x y u ≤ chartScalar hw0 hw1 width k H x y t + epsilon := by
  let delta := HalfPow.half * (HalfPow.half * epsilon)
  have hd : (0 : Q') < delta := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos epsilon he)
  let a := chartJointTimeThreshold hw0 hw1 width H x y hx hy epsilon
  have hleft := (chartCauchy hw0 hw1 width k H x y hx hy).bound
    delta hd t a ht (Nat.le_refl _)
  have hmiddle := (chartCutoffCauchy hw0 hw1 width H x y a).bound delta hd k j hk hj
  have hright := (chartCauchy hw0 hw1 width j H x y hx hy).bound
    delta hd a u (Nat.le_refl _) hu
  exact ⟨three_quarter_chain epsilon he _ _ _ _ hleft.1 hmiddle.1 hright.1,
    three_quarter_chain epsilon he _ _ _ _ hright.2 hmiddle.2 hleft.2⟩

/-- Constructive Cauchy data for the literal stage/depth diagonal, with no
choice of subsequence and no additional analytic estimate. -/
def chartJointCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    QCauchy (fun s => chartScalar hw0 hw1 width s H x y s) where
  M := chartJointModulus hw0 hw1 width H x y hx hy
  bound := fun epsilon he i j hi hj =>
    chartJoint_rectangle hw0 hw1 width H x y hx hy epsilon he i i j j
      (Nat.le_trans (Nat.le_max_right _ _) hi) (Nat.le_trans (Nat.le_max_left _ _) hi)
      (Nat.le_trans (Nat.le_max_right _ _) hj) (Nat.le_trans (Nat.le_max_left _ _) hj)

/-- Joint CReal limit for this fixed physical common-chart correlator. -/
def chartJointLimit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) : CReal :=
  ofQ'CauchySeq _ (chartJointCauchy hw0 hw1 width H x y hx hy)

theorem chartJoint_diagonal_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width H : Nat)
    (x y : PhysicalSpan width) (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    ConvergesTo (fun s => ofQ' (chartScalar hw0 hw1 width s H x y s))
      (chartJointLimit hw0 hw1 width H x y hx hy) :=
  convergesTo_ofQ'CauchySeq _ (chartJointCauchy hw0 hw1 width H x y hx hy)

/-- The joint limit controls the whole late rectangle, not only its
diagonal. The raw-index and representative-index thresholds are explicit. -/
theorem chartJoint_approx {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H)
    (epsilon : Q') (he : (0 : Q') < epsilon) (k t p : Nat)
    (hk : chartJointCutoffThreshold hw0 hw1 width H x y hx hy epsilon ≤ k)
    (ht : chartJointTimeThreshold hw0 hw1 width H x y hx hy epsilon ≤ t)
    (hp : chartJointModulus hw0 hw1 width H x y hx hy epsilon ≤ p) :
    chartScalar hw0 hw1 width k H x y t ≤
        (chartJointLimit hw0 hw1 width H x y hx hy).approx p + epsilon ∧
      (chartJointLimit hw0 hw1 width H x y hx hy).approx p ≤
        chartScalar hw0 hw1 width k H x y t + epsilon := by
  let c := chartJointCauchy hw0 hw1 width H x y hx hy
  let s := QMhat _ c p
  have hs : chartJointModulus hw0 hw1 width H x y hx hy epsilon ≤ s :=
    Nat.le_trans hp (self_le_QMhat _ c p)
  exact chartJoint_rectangle hw0 hw1 width H x y hx hy epsilon he k t s s hk ht
    (Nat.le_trans (Nat.le_max_right _ _) hs) (Nat.le_trans (Nat.le_max_left _ _) hs)

end YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy.chartCutoffCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy.chartJointTimeThreshold
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy.chartJointCutoffThreshold
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy.chartJointModulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy.chartJoint_rectangle
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy.chartJointCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy.chartJointLimit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy.chartJoint_diagonal_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy.chartJoint_approx
