/-
# Original Haar-observable equality descends to the SAME Wilson completion

The existing SupportedHaarEqv relation on each original chart identifies two
lower observables against every supported insertion. We apply it to the fixed
upper observable times the COMPLETE selected heat action. No spectator factor
is removed, and the common partition and all existing limit witnesses remain
unchanged. The actual limiting reflected form therefore has equal right slots.

The upper difference then has zero reflected norm. The original seminorm
embedding identifies the two states in the already constructed completion.
This includes identities valid on the quaternion Haar carrier, without
requiring free-polynomial coefficient equality.

This is observable-identity descent, NOT multiplication on arbitrary OS-null
classes. It does not construct a completed observable operator algebra, full
gauge-observable coverage, canonical rational GNSData, or continuum OS/QFT.
All original physical guards and regulator schedules are retained.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionObservableDescent
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra

namespace YMGap.Continuum.BF4WilsonSpatialUnionHaarObservableDescent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
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
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (SupportedHaarEqv)
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
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

private theorem haar_swap_lower_action (blocks : Nat) (upper lower action : RatPoly) :
    quaternionHaar blocks (polyMul (polyMul upper lower) action) ≈
      quaternionHaar blocks (polyMul (polyMul upper action) lower) :=
  haar_of_coeff ((RatPolyCoeffEqv.mul_assoc upper lower action).trans
    (((RatPolyCoeffEqv.mul_comm lower action).mul_left upper).trans
      (RatPolyCoeffEqv.mul_assoc upper action lower).symm))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {base : Nat}

/-- The Haar test is the supported upper observable times every original action factor. -/
theorem chartScalar_reflected_haar_right (H : Nat) (g e f : WindowExpression base)
    (r stage t : Nat)
    (hp : SupportedHaarEqv (B (chartExtent base r H t))
      (chartInsertion r H t e) (chartInsertion r H t f)) :
    chartScalar hw0 hw1 H (.mul (mirror H g) e) r stage t ≈
      chartScalar hw0 hw1 H (.mul (mirror H g) f) r stage t := by
  let upper := chartInsertion r H t (mirror H g)
  let action := polynomialProduct
    (faceHeatPolynomial w (headCutoff w+stage) (chartExtent base r H t))
    (chartIds base r H t)
  have hu : SupportedQuaternionBlocks (B (chartExtent base r H t)) upper :=
    chartInsertion_supported r H t (mirror H g)
  have ha : SupportedQuaternionBlocks (B (chartExtent base r H t)) action :=
    heatProduct_supported w (headCutoff w+stage) (chartExtent base r H t) (chartIds base r H t)
  have htest := hp (polyMul upper action) (supported_polyMul hu ha)
  have hhaar := Q'.eqv_trans _ _ _
    (haar_swap_lower_action (B (chartExtent base r H t)) upper (chartInsertion r H t e) action)
    (Q'.eqv_trans _ _ _ htest
      (Q'.eqv_symm (haar_swap_lower_action (B (chartExtent base r H t))
        upper (chartInsertion r H t f) action)))
  unfold chartScalar finiteValue numerator
  exact Q'.mul_eqv_congr_right _ _ _ hhaar

attribute [local irreducible] chartScalar spatialLimit

variable (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0<base)

/-- Only the original diagonal is required; its two quantitative limit witnesses remain fixed. -/
theorem form_haar_diagonal_right (H : Nat) (g e f : WindowExpression base)
    (hg : Within H g) (he : Within H e) (hf : Within H f)
    (hp : ∀ n, SupportedHaarEqv (B (chartExtent base n H n))
      (chartInsertion n H n e) (chartInsertion n H n f)) :
    Equiv (form hw0 hw1 hsmall hd hs hb H g e hg he)
      (form hw0 hw1 hsmall hd hs hb H g f hg hf) := by
  unfold form
  apply Equiv_of_limit_of_equal
    (aSeq := fun n => ofQ' (chartScalar hw0 hw1 H (.mul (mirror H g) e) n n n))
    (bSeq := fun n => ofQ' (chartScalar hw0 hw1 H (.mul (mirror H g) f) n n n))
  · intro n
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      chartScalar_reflected_haar_right hw0 hw1 H g e f n n n (hp n))
  · exact spatial_diagonal_converges hw0 hw1 H (.mul (mirror H g) e)
      ⟨mirror_within H g, within_mono (by omega : H ≤ 2*H) e he⟩ hsmall hd hs hb
  · exact spatial_diagonal_converges hw0 hw1 H (.mul (mirror H g) f)
      ⟨mirror_within H g, within_mono (by omega : H ≤ 2*H) f hf⟩ hsmall hd hs hb

attribute [local irreducible] form

/-- Use the upper difference as a spectator; no reflected equality is assumed. -/
theorem window_distSq_zero_of_haar_diagonal (H : Nat) (e f : WindowExpression base)
    (he : Within H e) (hf : Within H f)
    (hp : ∀ n, SupportedHaarEqv (B (chartExtent base n H n))
      (chartInsertion n H n e) (chartInsertion n H n f)) :
    Equiv (BF4ExactSlabFixedSpatialWilsonWindowSeminorm.distSq
      hw0 hw1 hsmall hd hs hb H ⟨e, he⟩ ⟨f, hf⟩) czero := by
  let d : WindowExpression base := .add e (.smul (-1) f)
  have hdifference : Within H d := ⟨he, hf⟩
  have hright := form_haar_diagonal_right hw0 hw1 hsmall hd hs hb H d e f
    hdifference he hf hp
  change Equiv (form hw0 hw1 hsmall hd hs hb H d d hdifference hdifference) czero
  exact (form_difference_right hw0 hw1 hsmall hd hs hb H d e f hdifference he hf).trans
    ((Equiv_add hright (Equiv.refl _)).trans (sub_self_eqv_zero _))

/-- Observable equality at a valid common horizon kills the actual intrinsic distance. -/
theorem intrinsic_distSq_zero_of_haar_diagonal (H : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H)
    (hp : ∀ n, SupportedHaarEqv (B (chartExtent base n H n))
      (chartInsertion n H n (chart H x)) (chartInsertion n H n (chart H y))) :
    Equiv (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq
      hw0 hw1 hsmall hd hs hb x y) czero :=
  (distSq_chart hw0 hw1 hsmall hd hs hb x y H hx hy).trans
    (window_distSq_zero_of_haar_diagonal hw0 hw1 hsmall hd hs hb H (chart H x) (chart H y)
      (chart_within H x hx) (chart_within H y hy) hp)

/-- Literal equality in the existing union completion, without defining a new quotient. -/
theorem embedStage_eq_of_haar_diagonal (H : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H)
    (hp : ∀ n, SupportedHaarEqv (B (chartExtent base n H n))
      (chartInsertion n H n (chart H x)) (chartInsertion n H n (chart H y))) :
    embedStage hw0 hw1 hsmall hd hs (ofExpression base hb x) =
      embedStage hw0 hw1 hsmall hd hs (ofExpression base hb y) := by
  apply (unionSeminorm hw0 hw1 hsmall hd hs).embedRep_eq_of_null
  change Equiv (BF4WilsonSpatialUnion.distSq hw0 hw1 hsmall hd hs
    (ofExpression base hb x) (ofExpression base hb y)) czero
  exact (distSq_ofExpression hw0 hw1 hsmall hd hs base hb x y).trans
    (intrinsic_distSq_zero_of_haar_diagonal hw0 hw1 hsmall hd hs hb H x y hx hy hp)

#print axioms chartScalar_reflected_haar_right
#print axioms form_haar_diagonal_right
#print axioms window_distSq_zero_of_haar_diagonal
#print axioms intrinsic_distSq_zero_of_haar_diagonal
#print axioms embedStage_eq_of_haar_diagonal

end YMGap.Continuum.BF4WilsonSpatialUnionHaarObservableDescent
