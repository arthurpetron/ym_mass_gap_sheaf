/-
# Original finite correlators in a supplied common intrinsic chart

The supplied radius H is held fixed while both temporal boundaries recede.
Every term is the actual selected-chain finiteValue on the same centered
ambient slab, with the same selected action and its original partition.
Only the two physical signed presentations vary between applications. Thus
joint and unit-marginal streams may use exactly one H and one action/Z.

The existing original bilinear pin supplies finite equality to the actual
window ratio. Its computed modulus gives Type-level Cauchy data, and chart
independence identifies its limit with the SAME intrinsic reflected pairing.
No lag is inserted implicitly, and the selected fixed-width chain is not
replaced by the full growing-box action. No cutoff interchange, strict gap,
continuum theory or new physical observable identification is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalCorrelator
import YMGap.Continuum.FCLimitContinuity

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
  (placedSpan windowRatio_span_mul_originalFiniteValue)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection
  (mirrorSchedule_within mirrorSchedule_faces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyMul)
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval (polynomialCap)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (centralExtent)
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)

local infix:50 " ≈ " => Q'.eqv

private theorem mirror_within (H : Nat) (xs : Span) : Within (2*H) (mirrorSpan H xs) := by
  intro x hm
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_within H y.2

private theorem mirror_physical {width : Nat} (H : Nat) (xs : Span)
    (hx : Physical width xs) : Physical width (mirrorSpan H xs) := by
  intro x hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_faces H y.2 (hx y hy)

/-- One original finiteValue and its selected-chain partition, with no implicit lag.
The same width, stage, chart H and buffer t specify the action for every x,y. -/
def chartScalar {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage H : Nat) (x y : PhysicalSpan width) (t : Nat) : Q' :=
  let E := adjacentEvenExtent (width+t+H)
  let start := width+1
  finiteValue w hw0 hw1 E (chainIds E width start (t+(2*H+t)))
    (fun _ hi => chainIds_physical hi)
    (polyMul (placedSpan E (start+t) (mirrorSpan H (encodeChart H x.val)))
      (placedSpan E (start+t) (encodeChart H y.val))) stage

/-- The supplied common-chart guards refer to the actual intrinsic distance
supports; no original-face or action factor is dropped by the finite pin. -/
theorem chartScalar_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage H : Nat) (x y : PhysicalSpan width)
    (_hx : radius x.val ≤ H) (hy : radius y.val ≤ H) (t : Nat) :
    chartScalar hw0 hw1 width stage H x y t ≈
      windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        t (2*H) t (mixedProduct width H (encodeChart H x.val) (encodeChart H y.val)) := by
  let E := adjacentEvenExtent (width+t+H)
  have hw : width ≤ E := by unfold E adjacentEvenExtent centralExtent; omega
  have ht : (width+1)+(t+(2*H+t)) ≤ E := by
    unfold E adjacentEvenExtent centralExtent
    omega
  have hxfaces : Physical width (encodeChart H x.val) :=
    encodeChart_physical H x.val x.property
  have hyfaces : Physical width (encodeChart H y.val) :=
    encodeChart_physical H y.val y.property
  have hyhalf : Within H (encodeChart H y.val) := encodeChart_within H y.val hy
  have hywithin : Within (2*H) (encodeChart H y.val) := by
    intro a ha e he
    have h := hyhalf a ha e he
    omega
  exact Q'.eqv_symm (windowRatio_span_mul_originalFiniteValue hw0 hw1
    (width := width) (start := width+1) (m := t) (L := 2*H) (n := t) (extent := E)
    hw ht (mirrorSpan H (encodeChart H x.val)) (encodeChart H y.val)
    (mirror_within H (encodeChart H x.val))
    (mirror_physical H (encodeChart H x.val) hxfaces) hywithin hyfaces stage)

attribute [local irreducible] chartScalar windowRatio baseLinks

/-- The existing computed window modulus is retained as Type-level data.
Both common-chart guards stay explicit in the public API. -/
def chartCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    QCauchy (fun t => chartScalar hw0 hw1 width stage H x y t) where
  M := windowTimeModulus hw0 hw1 width
    (polynomialCap (mixedProduct width H (encodeChart H x.val) (encodeChart H y.val)))
  bound := by
    intro epsilon he i j hi hj
    have hp := mixedProduct_supported width H (encodeChart H x.val) (encodeChart H y.val)
      (encodeChart_within H y.val hy)
    have h := (polynomialWindowCauchy hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) (2*H)
      (mixedProduct width H (encodeChart H x.val) (encodeChart H y.val)) hp).bound epsilon he i j hi hj
    have hip := chartScalar_pin hw0 hw1 width stage H x y hx hy i
    have hjp := chartScalar_pin hw0 hw1 width stage H x y hx hy j
    exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hip)
        (Q'.le_trans' _ _ _ h.1 (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hjp))),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hjp)
        (Q'.le_trans' _ _ _ h.2 (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hip)))⟩

theorem chartCauchy_modulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) (epsilon : Q') :
    (chartCauchy hw0 hw1 width stage H x y hx hy).M epsilon =
      windowTimeModulus hw0 hw1 width
        (polynomialCap (mixedProduct width H (encodeChart H x.val) (encodeChart H y.val))) epsilon := rfl

/-- Fixed-chart original finite values converge to the intrinsic pairing.
The chart may exceed the minimum radius, with chart independence proved. -/
theorem chartScalar_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    ConvergesTo (fun t => ofQ' (chartScalar hw0 hw1 width stage H x y t))
      (pairing hw0 hw1 width x.val y.val stage) := by
  have hform := form_converges hw0 hw1 width H (encodeChart H x.val) (encodeChart H y.val)
    (encodeChart_within H x.val hx) (encodeChart_within H y.val hy) stage
  have hpair := CReal.convergesTo_limit_congr hform
    (Equiv.symm (pairing_chart hw0 hw1 width H x.val y.val hx hy stage))
  exact TrigAddCReal.convergesTo_congr_seq
    (s := fun t => ofQ' (windowRatio hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) t (2*H) t
      (mixedProduct width H (encodeChart H x.val) (encodeChart H y.val))))
    (fun t => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.eqv_symm (chartScalar_pin hw0 hw1 width stage H x y hx hy t))) hpair

/-- The directly constructed common-chart scalar limit is the SAME intrinsic
pairing, not a new chart-dependent state or an interchange of limits. -/
theorem chartScalar_limit {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage H : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ H) (hy : radius y.val ≤ H) :
    Equiv (ofQ'CauchySeq (fun t => chartScalar hw0 hw1 width stage H x y t)
        (chartCauchy hw0 hw1 width stage H x y hx hy))
      (pairing hw0 hw1 width x.val y.val stage) :=
  Equiv_of_limit_of_equal
    (fun t => Equiv.refl (ofQ' (chartScalar hw0 hw1 width stage H x y t)))
    (convergesTo_ofQ'CauchySeq _ (chartCauchy hw0 hw1 width stage H x y hx hy))
    (chartScalar_converges hw0 hw1 width stage H x y hx hy)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator.chartScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator.chartScalar_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator.chartCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator.chartCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator.chartScalar_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator.chartScalar_limit
