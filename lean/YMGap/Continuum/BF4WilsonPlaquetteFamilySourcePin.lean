/-
# Signed plaquette families as literal radius-zero Wilson expressions

The signed radius-zero face presentation and a literal sum of physical Wilson
loops have the same source polynomial. The first and diagonal mixed products
therefore agree coefficientwise; no limit or carrier identification is used.
-/

import YMGap.Continuum.BF4WilsonPlaquetteSourcePin
import YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamily
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm

namespace YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation (finitePolySum)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbe (windowProbe)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (sourceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm (mixedProduct)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (encodeChart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit
  (unitSpan encodeChart_unit sourceSpan_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe
  (mirrorSpan_encodeChart)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
  (plaquetteLoop sourceCharacter_plaquette)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteFamily
  (familyPresentation familySpan familySpan_radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceHeat (plaquette)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_coeff)

local notation:max "N" width:arg => List.length (baseLinks width)

/-- Literal signed Wilson syntax. Empty families become the zero multiple of
the unit; repetitions and coefficient signs remain in their original order. -/
def familyExpression (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) : WindowExpression width :=
  match qs with
  | [] => .smul 0 .one
  | p :: ps =>
      .add (.smul (c p) (.loop 0 (plaquetteLoop p (hqs p List.mem_cons_self)) 1))
        (familyExpression width ps c (fun q hq => hqs q (List.mem_cons_of_mem p hq)))

theorem family_within (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    Within 0 (familyExpression width qs c hqs) := by
  induction qs with
  | nil => exact True.intro
  | cons p ps ih =>
      exact ⟨Nat.le_refl 0,
        ih (fun q hq => hqs q (List.mem_cons_of_mem p hq))⟩

/-- The source has radius zero on the actual all-nome intrinsic syntax. -/
def familyState (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) : IntrinsicExpression width :=
  ⟨0, familyExpression width qs c hqs, family_within width qs c hqs⟩

private theorem singleton_product (C : Z4Plaq → Nat → RatPoly) (p : Z4Plaq) :
    RatPolyCoeffEqv
      (BF4ExactSlabTemporalSweep.product C [(p, [(1, 1)])]) (C p 1) :=
  ((((RatPolyCoeffEqv.one_smul (C p 1)).add (RatPolyCoeffEqv.refl polyZero)).trans
    (RatPolyCoeffEqv.add_zero (C p 1))).mul (RatPolyCoeffEqv.refl polyOne)).trans
      (RatPolyCoeffEqv.mul_one _)

private theorem singleton_window (width : Nat) (p : Z4Plaq) :
    RatPolyCoeffEqv
      (windowProbe width [(0, [(p, [(1, 1)])])])
      (liftBoundary (0 * (N width))
        (characterPolynomial (plaquette width p).scalar 1)) :=
  ((lift_coeff (0 * (N width))
    (singleton_product
      (fun q spin => characterPolynomial (plaquette width q).scalar spin) p)).mul
      (RatPolyCoeffEqv.refl polyOne)).trans (RatPolyCoeffEqv.mul_one _)

/-- Exact coefficient identity between the old signed presentation and the
literal Wilson expression, including the empty and repeated-face cases. -/
theorem source_family_span (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    RatPolyCoeffEqv (sourcePolynomial (familyExpression width qs c hqs))
      (sourceSpan width (familyPresentation qs c)) := by
  induction qs with
  | nil =>
      change RatPolyCoeffEqv (polySmul 0 polyOne) polyZero
      exact RatPolyCoeffEqv.zero_smul polyOne
  | cons p ps ih =>
      have hp : p ∈ spatialFaces width := hqs p List.mem_cons_self
      have hloop : RatPolyCoeffEqv
          (sourcePolynomial (.loop 0 (plaquetteLoop p hp) 1))
          (windowProbe width [(0, [(p, [(1, 1)])])]) :=
        (lift_coeff _ (sourceCharacter_plaquette width p 1)).trans
          (singleton_window width p).symm
      change RatPolyCoeffEqv
        (polyAdd
          (polySmul (c p)
            (sourcePolynomial (.loop 0 (plaquetteLoop p hp) 1)))
          (sourcePolynomial (familyExpression width ps c
            (fun q hq => hqs q (List.mem_cons_of_mem p hq)))))
        (polyAdd (polySmul (c p)
          (windowProbe width [(0, [(p, [(1, 1)])])]))
          (sourceSpan width (familyPresentation ps c)))
      exact (hloop.smul (c p)).add
        (ih (fun q hq => hqs q (List.mem_cons_of_mem p hq)))

private theorem mirror_family_zero (width : Nat) (qs : List Z4Plaq)
    (c : Z4Plaq → Q') (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    mirror 0 (familyExpression width qs c hqs) =
      familyExpression width qs c hqs := by
  induction qs with
  | nil => rfl
  | cons p ps ih =>
      have htail := ih (fun q hq => hqs q (List.mem_cons_of_mem p hq))
      simpa only [familyExpression, mirror, mapOffsets, Nat.zero_sub] using
        congrArg (fun e => WindowExpression.add
          (WindowExpression.smul (c p)
            (WindowExpression.loop 0
              (plaquetteLoop p (hqs p List.mem_cons_self)) 1)) e) htail

/-- Original mixed mean polynomial equals the literal radius-zero Wilson
family mean polynomial, with no nome or positivity hypothesis. -/
theorem mixedProduct_mean (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    RatPolyCoeffEqv
      (mixedProduct width 0
        (encodeChart 0 (familySpan width qs c hqs).val)
        (encodeChart 0 unitSpan))
      (sourcePolynomial
        (.mul (mirror 0 (familyExpression width qs c hqs)) .one)) := by
  have hx : BF4ExactSlabFixedSpatialIntrinsicReflectedForm.radius
      (familySpan width qs c hqs).val ≤ 0 := by
    rw [familySpan_radius]
    exact Nat.le_refl 0
  rw [mixedProduct, mirrorSpan_encodeChart 0 (familySpan width qs c hqs).val hx,
    BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSpan_zero,
    encodeChart_unit, sourceSpan_unit]
  rw [mirror_family_zero width qs c hqs]
  exact ((source_family_span width qs c hqs).symm.mul
    (RatPolyCoeffEqv.refl polyOne))

/-- The diagonal original mixed product is exactly the literal Wilson square
at radius zero; no off-diagonal family Gram claim is made. -/
theorem mixedProduct_square (width : Nat) (qs : List Z4Plaq) (c : Z4Plaq → Q')
    (hqs : ∀ p, p ∈ qs → p ∈ spatialFaces width) :
    RatPolyCoeffEqv
      (mixedProduct width 0
        (encodeChart 0 (familySpan width qs c hqs).val)
        (encodeChart 0 (familySpan width qs c hqs).val))
      (sourcePolynomial
        (.mul (mirror 0 (familyExpression width qs c hqs))
          (familyExpression width qs c hqs))) := by
  have hx : BF4ExactSlabFixedSpatialIntrinsicReflectedForm.radius
      (familySpan width qs c hqs).val ≤ 0 := by
    rw [familySpan_radius]
    exact Nat.le_refl 0
  rw [mixedProduct, mirrorSpan_encodeChart 0 (familySpan width qs c hqs).val hx,
    BF4ExactSlabFixedSpatialPhysicalTimeShift.advanceSpan_zero]
  have hchart : encodeChart 0 (familySpan width qs c hqs).val =
      familyPresentation qs c := by
    simp [BF4ExactSlabFixedSpatialIntrinsicReflectedForm.encodeChart,
      BF4ExactSlabFixedSpatialIntrinsicReflectedForm.encodeSchedule,
      familySpan, familyPresentation]
  rw [hchart, mirror_family_zero width qs c hqs]
  exact (source_family_span width qs c hqs).symm.mul
    (source_family_span width qs c hqs).symm

#print axioms familyExpression
#print axioms family_within
#print axioms familyState
#print axioms source_family_span
#print axioms mixedProduct_mean
#print axioms mixedProduct_square

end YMGap.Continuum.BF4WilsonPlaquetteFamilySourcePin
