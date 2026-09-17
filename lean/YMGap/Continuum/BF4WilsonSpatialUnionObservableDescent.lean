/-
# Original observable equality gives equality in the SAME Wilson completion

Padded coefficient equality of two lower observables on the existing spatial,
cutoff and time diagonal preserves every mixed reflected finite expectation.
The upper observable and the full selected heat action remain fixed, and the
normalizing partition is unchanged. The two existing limit witnesses therefore
give equality in the right slot of the actual limiting reflected form.

Apply this to the upper difference e-f. Bilinearity makes its reflected norm
zero, and the original seminorm embedding identifies the two completed states.
Commutativity of the actual polynomial product supplies a concrete application.

This is semantic polynomial equality, NOT a claim that arbitrary OS-null
states may be multiplied. No observable operator algebra on the completion,
full gauge-observable coverage, rational-valued canonical GNSData, or continuum
OS/QFT reconstruction is constructed here. All original guards are retained.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality
import YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

namespace YMGap.Continuum.BF4WilsonSpatialUnionObservableDescent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialComparison
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSpatialLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz (form)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws
  (form_difference_right)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (distSq_chart)
open YMGap.Continuum.BF4WilsonSpatialUnion (ofExpression distSq_ofExpression)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm (unionSeminorm embedStage)
open YMGap.Continuum.BF4ExactSlabFixedSpatialAlignedBoxes (chartExtent chartIds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter (paddedWidth)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality (heatProduct_supported)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem chartInsertion_supported {base : Nat} (r H t : Nat)
    (e : WindowExpression base) :
    SupportedQuaternionBlocks (B (chartExtent base r H t)) (chartInsertion r H t e) :=
  placed_supported (chartExtent base r H t) (paddedWidth base r+1+t) (centeredExpression r e)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {base : Nat}

/-- The fixed upper observable AND every selected action factor are retained. -/
theorem chartScalar_reflected_padded_right (H : Nat) (g e f : WindowExpression base)
    (r stage t : Nat)
    (hp : PaddedPolynomialCoeffEqv (B (chartExtent base r H t))
      (chartInsertion r H t e) (chartInsertion r H t f)) :
    chartScalar hw0 hw1 H (.mul (mirror H g) e) r stage t ≈
      chartScalar hw0 hw1 H (.mul (mirror H g) f) r stage t := by
  let upper := chartInsertion r H t (mirror H g)
  let action := polynomialProduct
    (faceHeatPolynomial w (headCutoff w+stage) (chartExtent base r H t))
    (chartIds base r H t)
  have hu : SupportedQuaternionBlocks (B (chartExtent base r H t)) upper :=
    chartInsertion_supported r H t (mirror H g)
  have he := chartInsertion_supported r H t e
  have hf := chartInsertion_supported r H t f
  have ha : SupportedQuaternionBlocks (B (chartExtent base r H t)) action :=
    heatProduct_supported w (headCutoff w+stage) (chartExtent base r H t) (chartIds base r H t)
  have hproduct := ((PaddedPolynomialCoeffEqv.refl _ upper).mul hp).mul
    (PaddedPolynomialCoeffEqv.refl _ action)
  have hhaar := hproduct.haar
    (supported_polyMul (supported_polyMul hu he) ha)
    (supported_polyMul (supported_polyMul hu hf) ha)
  unfold chartScalar finiteValue numerator
  exact Q'.mul_eqv_congr_right _ _ _ hhaar

attribute [local irreducible] chartScalar spatialLimit

variable (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0<base)

/-- Only the existing diagonal is required; both limit moduli are unchanged. -/
theorem form_padded_diagonal_right (H : Nat) (g e f : WindowExpression base)
    (hg : Within H g) (he : Within H e) (hf : Within H f)
    (hp : ∀ n, PaddedPolynomialCoeffEqv (B (chartExtent base n H n))
      (chartInsertion n H n e) (chartInsertion n H n f)) :
    Equiv (form hw0 hw1 hsmall hd hs hb H g e hg he)
      (form hw0 hw1 hsmall hd hs hb H g f hg hf) := by
  unfold form
  apply Equiv_of_limit_of_equal
    (aSeq := fun n => ofQ' (chartScalar hw0 hw1 H (.mul (mirror H g) e) n n n))
    (bSeq := fun n => ofQ' (chartScalar hw0 hw1 H (.mul (mirror H g) f) n n n))
  · intro n
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      chartScalar_reflected_padded_right hw0 hw1 H g e f n n n (hp n))
  · exact spatial_diagonal_converges hw0 hw1 H (.mul (mirror H g) e)
      ⟨mirror_within H g, within_mono (by omega : H ≤ 2*H) e he⟩ hsmall hd hs hb
  · exact spatial_diagonal_converges hw0 hw1 H (.mul (mirror H g) f)
      ⟨mirror_within H g, within_mono (by omega : H ≤ 2*H) f hf⟩ hsmall hd hs hb

attribute [local irreducible] form

/-- The upper difference is merely a fixed spectator; no reflected equality is assumed. -/
theorem window_distSq_zero_of_padded_diagonal (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f)
    (hp : ∀ n, PaddedPolynomialCoeffEqv (B (chartExtent base n H n))
      (chartInsertion n H n e) (chartInsertion n H n f)) :
    Equiv (BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq
      hw0 hw1 hsmall hd hs hb H ⟨e, he⟩ ⟨f, hf⟩) czero := by
  let d : WindowExpression base := .add e (.smul (-1) f)
  have hdifference : Within H d := ⟨he, hf⟩
  have hright := form_padded_diagonal_right hw0 hw1 hsmall hd hs hb H d e f
    hdifference he hf hp
  change Equiv (form hw0 hw1 hsmall hd hs hb H d d hdifference hdifference) czero
  exact (form_difference_right hw0 hw1 hsmall hd hs hb H d e f hdifference he hf).trans
    ((Equiv_add hright (Equiv.refl _)).trans (sub_self_eqv_zero _))

/-- Semantic equality at one valid common horizon kills the existing intrinsic distance. -/
theorem intrinsic_distSq_zero_of_padded_diagonal (H : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H)
    (hp : ∀ n, PaddedPolynomialCoeffEqv (B (chartExtent base n H n))
      (chartInsertion n H n (chart H x)) (chartInsertion n H n (chart H y))) :
    Equiv (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq
      hw0 hw1 hsmall hd hs hb x y) czero :=
  (distSq_chart hw0 hw1 hsmall hd hs hb x y H hx hy).trans
    (window_distSq_zero_of_padded_diagonal hw0 hw1 hsmall hd hs hb H (chart H x) (chart H y)
      (chart_within H x hx) (chart_within H y hy) hp)

/-- Equality in the already constructed union completion, not in a new quotient. -/
theorem embedStage_eq_of_padded_diagonal (H : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H)
    (hp : ∀ n, PaddedPolynomialCoeffEqv (B (chartExtent base n H n))
      (chartInsertion n H n (chart H x)) (chartInsertion n H n (chart H y))) :
    embedStage hw0 hw1 hsmall hd hs (ofExpression base hb x) =
      embedStage hw0 hw1 hsmall hd hs (ofExpression base hb y) := by
  apply (unionSeminorm hw0 hw1 hsmall hd hs).embedRep_eq_of_null
  change Equiv (BF4WilsonSpatialUnion.distSq hw0 hw1 hsmall hd hs
    (ofExpression base hb x) (ofExpression base hb y)) czero
  exact (distSq_ofExpression hw0 hw1 hsmall hd hs base hb x y).trans
    (intrinsic_distSq_zero_of_padded_diagonal hw0 hw1 hsmall hd hs hb H x y hx hy hp)

/-- A literal polynomial identity descends to actual states. This does not define
product on arbitrary OS-null classes or on the completed carrier. -/
theorem embedStage_mul_comm (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f) :
    embedStage hw0 hw1 hsmall hd hs (ofExpression base hb ⟨H, .mul e f, ⟨he, hf⟩⟩) =
      embedStage hw0 hw1 hsmall hd hs (ofExpression base hb ⟨H, .mul f e, ⟨hf, he⟩⟩) := by
  apply embedStage_eq_of_padded_diagonal hw0 hw1 hsmall hd hs hb H
    ⟨H, .mul e f, ⟨he, hf⟩⟩ ⟨H, .mul f e, ⟨hf, he⟩⟩ (Nat.le_refl _) (Nat.le_refl _)
  intro n
  simp only [chart, Nat.sub_self, shift_zero]
  exact PaddedPolynomialCoeffEqv.of_coeff
    (RatPolyCoeffEqv.mul_comm (chartInsertion n H n e) (chartInsertion n H n f))

#print axioms chartScalar_reflected_padded_right
#print axioms form_padded_diagonal_right
#print axioms window_distSq_zero_of_padded_diagonal
#print axioms intrinsic_distSq_zero_of_padded_diagonal
#print axioms embedStage_eq_of_padded_diagonal
#print axioms embedStage_mul_comm

end YMGap.Continuum.BF4WilsonSpatialUnionObservableDescent
