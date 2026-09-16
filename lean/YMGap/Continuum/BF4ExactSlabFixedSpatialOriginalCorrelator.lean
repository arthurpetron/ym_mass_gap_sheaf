/-
# Completed physical correlators from the actual original finite chain

Fix nome, spatial width, retained heat stage, two physical signed probe
presentations, and a physical lag n. Their common intrinsic chart is computed
once. At boundary depth t the SAME mirrored/advanced probe product is placed
in a reflection-centered original slab, with the selected fixed-width chain
action and its original finiteValue partition. Only the ambient placement
and the two time buffers depend on t; n and the compact insertion do not.

The existing bilinear original-observable pin identifies every finite term
with the actual window ratio. Its computed Cauchy modulus and convergence
therefore carry over, and the completed time correlator equals the quotient
class of this explicit original scalar stream's CReal limit.

The insertion is a literal product of placed signed spatial-probe spans;
no new reflection-image theorem or replacement observable is assumed.
This is the selected fixed-width action, not the full growing-box action.
No cutoff/time interchange, one-step positivity, strict gap, Hilbert-space
completion theorem or continuum assertion is made here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalCorrelator

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan
  (sourceSpan placedSpan windowRatio_span_mul_originalFiniteValue)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflection
  (mirrorSchedule_within mirrorSchedule_faces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
  (advanceSpan advanceSpan_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
  (embedSpan completedTime)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedInner (completedInner)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedTimeForm (completedTime_correlator)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval (polynomialCap)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (centralExtent)
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry (adjacentEvenExtent)

local infix:50 " ≈ " => Q'.eqv

/-- One fixed common chart for the two observables, including physical lag n. -/
def chartRadius {width : Nat} (n : Nat) (x y : PhysicalSpan width) : Nat :=
  max (radius x.val) (radius (advanceSpan n y.val))

/-- The compact mixed reflected insertion is independent of boundary depth. -/
def sourcePolynomial {width : Nat} (n : Nat) (x y : PhysicalSpan width) : RatPoly :=
  let H := chartRadius n x y
  mixedProduct width H (encodeChart H x.val) (encodeChart H (advanceSpan n y.val))

theorem sourcePolynomial_supported {width : Nat} (n : Nat) (x y : PhysicalSpan width) :
    SupportedQuaternionBlocks ((2*chartRadius n x y+1)*(baseLinks width).length)
      (sourcePolynomial n x y) :=
  mixedProduct_supported width (chartRadius n x y)
    (encodeChart (chartRadius n x y) x.val)
    (encodeChart (chartRadius n x y) (advanceSpan n y.val))
    (encodeChart_within (chartRadius n x y) (advanceSpan n y.val) (Nat.le_max_right _ _))

private theorem mirror_within (h : Nat) (xs : Span) : Within (2*h) (mirrorSpan h xs) := by
  intro x hm
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_within h y.2

private theorem mirror_physical {width : Nat} (h : Nat) (xs : Span)
    (hx : Physical width xs) : Physical width (mirrorSpan h xs) := by
  intro x hm
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  exact mirrorSchedule_faces h y.2 (hx y hy)

/-- The actual original finiteValue, with a symmetric ambient placement and
the SAME selected chain partition. The physical lag n is not the buffer t. -/
def originalScalar {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage n : Nat) (x y : PhysicalSpan width) (t : Nat) : Q' :=
  let H := chartRadius n x y
  let E := adjacentEvenExtent (width+t+H)
  let start := width+1
  finiteValue w hw0 hw1 E (chainIds E width start (t+(2*H+t)))
    (fun _ hi => chainIds_physical hi)
    (polyMul (placedSpan E (start+t) (mirrorSpan H (encodeChart H x.val)))
      (placedSpan E (start+t) (encodeChart H (advanceSpan n y.val)))) stage

/-- Every original finite term is the diagonal window ratio of the same
fixed compact insertion, including all signed mixed terms. -/
theorem originalScalar_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage n : Nat) (x y : PhysicalSpan width) (t : Nat) :
    originalScalar hw0 hw1 width stage n x y t ≈
      windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        t (2*chartRadius n x y) t (sourcePolynomial n x y) := by
  let H := chartRadius n x y
  let E := adjacentEvenExtent (width+t+H)
  have hw : width ≤ E := by unfold E adjacentEvenExtent centralExtent; omega
  have ht : (width+1)+(t+(2*H+t)) ≤ E := by
    unfold E adjacentEvenExtent centralExtent
    omega
  have hxfaces : Physical width (encodeChart H x.val) :=
    encodeChart_physical H x.val x.property
  have hyfaces : Physical width (encodeChart H (advanceSpan n y.val)) :=
    encodeChart_physical H (advanceSpan n y.val) (advanceSpan_physical n y.val y.property)
  have hyhalf : Within H (encodeChart H (advanceSpan n y.val)) :=
    encodeChart_within H (advanceSpan n y.val) (Nat.le_max_right _ _)
  have hywithin : Within (2*H) (encodeChart H (advanceSpan n y.val)) := by
    intro a ha e he
    have h := hyhalf a ha e he
    omega
  exact Q'.eqv_symm (windowRatio_span_mul_originalFiniteValue hw0 hw1
    (width := width) (start := width+1) (m := t) (L := 2*H) (n := t) (extent := E)
    hw ht (mirrorSpan H (encodeChart H x.val)) (encodeChart H (advanceSpan n y.val))
    (mirror_within H (encodeChart H x.val)) (mirror_physical H (encodeChart H x.val) hxfaces)
    hywithin hyfaces stage)

attribute [local irreducible] originalScalar windowRatio baseLinks

/-- Type-level Cauchy data for the actual original stream. Its modulus is
the existing computed window modulus, not a newly assumed convergence rate. -/
def originalCauchy {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage n : Nat) (x y : PhysicalSpan width) :
    QCauchy (fun t => originalScalar hw0 hw1 width stage n x y t) where
  M := windowTimeModulus hw0 hw1 width (polynomialCap (sourcePolynomial n x y))
  bound := by
    intro epsilon he i j hi hj
    have h := (polynomialWindowCauchy hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) (2*chartRadius n x y) (sourcePolynomial n x y)
      (sourcePolynomial_supported n x y)).bound epsilon he i j hi hj
    have hip := originalScalar_pin hw0 hw1 width stage n x y i
    have hjp := originalScalar_pin hw0 hw1 width stage n x y j
    exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv hip)
        (Q'.le_trans' _ _ _ h.1 (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hjp))),
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hjp)
        (Q'.le_trans' _ _ _ h.2 (Q'.ge_of_eqv (Q'.add_eqv_congr_right _ _ epsilon hip)))⟩

theorem originalCauchy_modulus {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage n : Nat) (x y : PhysicalSpan width) (epsilon : Q') :
    (originalCauchy hw0 hw1 width stage n x y).M epsilon =
      windowTimeModulus hw0 hw1 width (polynomialCap (sourcePolynomial n x y)) epsilon := rfl

/-- Original finite values converge to the already constructed intrinsic
pairing, with physical lag fixed while both time boundaries recede. -/
theorem originalScalar_converges {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage n : Nat) (x y : PhysicalSpan width) :
    ConvergesTo (fun t => ofQ' (originalScalar hw0 hw1 width stage n x y t))
      (pairing hw0 hw1 width x.val (advanceSpan n y.val) stage) := by
  have h := polynomialWindow_converges hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) (2*chartRadius n x y) (sourcePolynomial n x y)
    (sourcePolynomial_supported n x y)
  exact TrigAddCReal.convergesTo_congr_seq
    (s := fun t => ofQ' (windowRatio hw0 hw1 (headCutoff w+stage) width
      (Nat.le_add_right _ _) t (2*chartRadius n x y) t (sourcePolynomial n x y)))
    (fun t => SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.eqv_symm (originalScalar_pin hw0 hw1 width stage n x y t))) h

/-- The CReal constructed directly from the original finite stream is
equivalent to the SAME intrinsic correlator; no limit is interchanged. -/
theorem originalScalar_limit {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage n : Nat) (x y : PhysicalSpan width) :
    Equiv (ofQ'CauchySeq (fun t => originalScalar hw0 hw1 width stage n x y t)
        (originalCauchy hw0 hw1 width stage n x y))
      (pairing hw0 hw1 width x.val (advanceSpan n y.val) stage) :=
  Equiv_of_limit_of_equal (fun t => Equiv.refl
      (ofQ' (originalScalar hw0 hw1 width stage n x y t)))
    (convergesTo_ofQ'CauchySeq _ (originalCauchy hw0 hw1 width stage n x y))
    (originalScalar_converges hw0 hw1 width stage n x y)

/-- Exact original-observable pin on the completed carrier: the completed
time correlator is the explicit original finiteValue stream's limit class. -/
theorem completedTime_originalCorrelator {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage n : Nat) (x y : PhysicalSpan width) :
    completedInner hw0 hw1 width stage (embedSpan hw0 hw1 width stage x)
        (completedTime hw0 hw1 width stage n (embedSpan hw0 hw1 width stage y)) =
      Quotient.mk crealSetoid
        (ofQ'CauchySeq (fun t => originalScalar hw0 hw1 width stage n x y t)
          (originalCauchy hw0 hw1 width stage n x y)) := by
  rw [completedTime_correlator]
  exact Quotient.sound (Equiv.symm (originalScalar_limit hw0 hw1 width stage n x y))

end YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalCorrelator

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalCorrelator.chartRadius
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalCorrelator.sourcePolynomial
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalCorrelator.sourcePolynomial_supported
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalCorrelator.originalScalar
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalCorrelator.originalScalar_pin
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalCorrelator.originalCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalCorrelator.originalCauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalCorrelator.originalScalar_converges
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalCorrelator.originalScalar_limit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalCorrelator.completedTime_originalCorrelator
