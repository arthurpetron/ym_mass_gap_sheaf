/- # Literal fixed-width all-nome reflected Wilson form

The form below uses the original joint cutoff/time limit at the literal source
width.  No small-nome, entropy, spatial-limit, completion, carrier-isometry,
or continuum claim is made. -/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedSymmetry
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm

namespace YMGap.Continuum.BF4WilsonAllNomeReflectedForm
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization (blockCount)
open YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction (selectedHeat selectedHeat_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection (selectedIds)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSymmetry
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift shift_within mirror_shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredLimit (originalJoint_centered_shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem finite_reflected_image {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (radius width start depth : Nat) (p p' q : RatPoly)
    (hp' : SupportedQuaternionBlocks (blockCount radius) p')
    (hq : SupportedQuaternionBlocks (blockCount radius) q)
    (hr : ReflectionImage (adjacentEvenExtent radius) p p') (stage : Nat) :
    finiteValue w hw0 hw1 (adjacentEvenExtent radius) (selectedIds radius width start depth)
      (fun _ hi => chainIds_physical hi)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent radius) p) q) stage ≈
    finiteValue w hw0 hw1 (adjacentEvenExtent radius) (selectedIds radius width start depth)
      (fun _ hi => chainIds_physical hi) (polyMul p' q) stage := by
  have ha := selectedHeat_supported w (headCutoff w+stage) radius
    (selectedIds radius width start depth)
  apply Q'.mul_eqv_congr_right
  exact ((PaddedPolynomialCoeffEqv.mul hr (.refl _ q)).mul (.refl _
    (selectedHeat w (headCutoff w+stage) radius
      (selectedIds radius width start depth)))).haar
    (supported_polyMul (supported_polyMul
      (reflectCorrectedSlabPolynomial_support _ _) hq) ha)
    (supported_polyMul (supported_polyMul hp' hq) ha)

/-- Finite reflected symmetry on the literal source width and original action. -/
theorem originalWindowScalar_reflected_symm {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H : Nat) (e f : WindowExpression width)
    (he : Within H e) (hf : Within H f) (stage t : Nat) :
    originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H e) f) stage t t ≈
      originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H f) e) stage t t := by
  let radius := width+t+H
  let start := width+1
  let E := adjacentEvenExtent radius
  have hw : width ≤ E := by unfold E adjacentEvenExtent centralExtent radius; omega
  have hcenter : start+t+H=radius+1 := by unfold start radius; omega
  have ht : start+(t+(2*H+t)) ≤ E := by
    unfold E adjacentEvenExtent centralExtent radius start
    omega
  let p := placedPolynomial E (start+t) e
  let q := placedPolynomial E (start+t) f
  let rp := placedPolynomial E (start+t) (mirror H e)
  let rq := placedPolynomial E (start+t) (mirror H f)
  have hp := placed_supported E (start+t) e
  have hq := placed_supported E (start+t) f
  have hrp := placed_supported E (start+t) (mirror H e)
  have hrq := placed_supported E (start+t) (mirror H f)
  have hleft := finite_reflected_image hw0 hw1 radius width start (t+H)
    p rp q hrp hq (placed_reflection hw hcenter e he) stage
  have hright := finite_reflected_image hw0 hw1 radius width start (t+H)
    q rq p hrq hp (placed_reflection hw hcenter f hf) stage
  have hs := originalChain_finiteValue_reflected_symm hw0 hw1 radius width start (t+H)
    (by omega) p q hp hq stage
  have hmixed := Q'.eqv_trans _ _ _ (Q'.eqv_symm hleft)
    (Q'.eqv_trans _ _ _ hs hright)
  have hpx := windowRatio_originalFiniteValue hw0 hw1 (m := t) (L := 2*H) (n := t)
    hw ht (.mul (mirror H e) f)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩ stage
  have hpy := windowRatio_originalFiniteValue hw0 hw1 (m := t) (L := 2*H) (n := t)
    hw ht (.mul (mirror H f) e)
    ⟨mirror_within H f, within_mono (by omega : H ≤ 2*H) e he⟩ stage
  have hfin := Q'.eqv_trans _ _ _ hpx
    (Q'.eqv_trans _ _ _ (by
      simpa only [p, q, rp, rq, E, radius, start, selectedIds, placedPolynomial,
        show t+(2*H+t)=2*(t+H) by omega] using hmixed) (Q'.eqv_symm hpy))
  exact Q'.eqv_trans _ _ _
    (originalWindowScalar_pin hw0 hw1 (2*H) (.mul (mirror H e) f)
      ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩ stage t t)
    (Q'.eqv_trans _ _ _ hfin (Q'.eqv_symm
      (originalWindowScalar_pin hw0 hw1 (2*H) (.mul (mirror H f) e)
        ⟨mirror_within H f, within_mono (by omega : H ≤ 2*H) e he⟩ stage t t)))

/-- The literal common-window form before choosing the maximum radius. -/
def commonForm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H : Nat) (e f : WindowExpression width)
    (he : Within H e) (hf : Within H f) : CReal :=
  originalJointLimit hw0 hw1 (2*H) (.mul (mirror H e) f)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩

/-- Enlarging the common chart changes neither the literal fixed-width form
nor its original action. -/
theorem commonForm_shift {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H d : Nat) (e f : WindowExpression width)
    (he : Within H e) (hf : Within H f) :
    Equiv
      (commonForm hw0 hw1 (H+d) (shift d e) (shift d f)
        (shift_within H d e he) (shift_within H d f hf))
      (commonForm hw0 hw1 H e f he hf) := by
  have hp : WindowExpression.mul (mirror (H+d) (shift d e)) (shift d f) =
      shift d (.mul (mirror H e) f) := by
    change WindowExpression.mul (mirror (H+d) (shift d e)) (shift d f) =
      WindowExpression.mul (shift d (mirror H e)) (shift d f)
    rw [mirror_shift H d e he]
  have h := originalJoint_centered_shift hw0 hw1 (2*H) d
    (.mul (mirror H e) f)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩
  simpa only [commonForm, hp, show 2*H+2*d=2*(H+d) by omega] using h

theorem commonForm_symm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H : Nat) (e f : WindowExpression width)
    (he : Within H e) (hf : Within H f) :
    Equiv (commonForm hw0 hw1 H e f he hf) (commonForm hw0 hw1 H f e hf he) :=
  Equiv_of_limit_of_equal
    (fun stage => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      originalWindowScalar_reflected_symm hw0 hw1 H e f he hf stage stage))
    (originalJoint_diagonal_converges hw0 hw1 (2*H) (.mul (mirror H e) f)
      ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) f hf⟩)
    (originalJoint_diagonal_converges hw0 hw1 (2*H) (.mul (mirror H f) e)
      ⟨mirror_within H f, within_mono (by omega : H ≤ 2*H) e he⟩)

theorem commonForm_nonnegative {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H : Nat) (e : WindowExpression width) (he : Within H e) :
    leEv (ofQ' 0) (commonForm hw0 hw1 H e e he he) :=
  originalJoint_reflected_nonnegative hw0 hw1 H e he

def intrinsicForm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (x y : IntrinsicExpression width) : CReal :=
  commonForm hw0 hw1 (max x.radius y.radius)
    (chart (max x.radius y.radius) x) (chart (max x.radius y.radius) y)
    (chart_within _ x (Nat.le_max_left _ _))
    (chart_within _ y (Nat.le_max_right _ _))

/-- Every valid common temporal chart realizes the same literal-width form;
no spatial recentering or larger-width action enters the comparison. -/
theorem intrinsicForm_chart {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (x y : IntrinsicExpression width) (H : Nat)
    (hx : x.radius ≤ H) (hy : y.radius ≤ H) :
    Equiv (intrinsicForm hw0 hw1 x y)
      (commonForm hw0 hw1 H (chart H x) (chart H y)
        (chart_within H x hx) (chart_within H y hy)) := by
  let M := max x.radius y.radius
  have hxM : x.radius ≤ M := Nat.le_max_left _ _
  have hyM : y.radius ≤ M := Nat.le_max_right _ _
  have hMH : M ≤ H := Nat.max_le.mpr ⟨hx,hy⟩
  have hsum : M+(H-M)=H := by omega
  have hcx : shift (H-M) (chart M x) = chart H x := by
    rw [← chart_step M (H-M) x hxM, hsum]
  have hcy : shift (H-M) (chart M y) = chart H y := by
    rw [← chart_step M (H-M) y hyM, hsum]
  have h := commonForm_shift hw0 hw1 M (H-M)
    (chart M x) (chart M y) (chart_within M x hxM) (chart_within M y hyM)
  simpa only [hsum, hcx, hcy, intrinsicForm, M] using h.symm

theorem intrinsicForm_symm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (x y : IntrinsicExpression width) :
    Equiv (intrinsicForm hw0 hw1 x y) (intrinsicForm hw0 hw1 y x) := by
  unfold intrinsicForm
  simpa only [Nat.max_comm] using commonForm_symm hw0 hw1 (max x.radius y.radius)
    (chart (max x.radius y.radius) x) (chart (max x.radius y.radius) y)
    (chart_within _ x (Nat.le_max_left _ _)) (chart_within _ y (Nat.le_max_right _ _))

theorem intrinsicForm_nonnegative {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (x : IntrinsicExpression width) :
    leEv (ofQ' 0) (intrinsicForm hw0 hw1 x x) := by
  unfold intrinsicForm
  simpa only [Nat.max_self] using commonForm_nonnegative hw0 hw1 x.radius
    (chart x.radius x) (chart_within x.radius x (Nat.le_refl _))

end YMGap.Continuum.BF4WilsonAllNomeReflectedForm

#print axioms YMGap.Continuum.BF4WilsonAllNomeReflectedForm.originalWindowScalar_reflected_symm
#print axioms YMGap.Continuum.BF4WilsonAllNomeReflectedForm.commonForm
#print axioms YMGap.Continuum.BF4WilsonAllNomeReflectedForm.commonForm_shift
#print axioms YMGap.Continuum.BF4WilsonAllNomeReflectedForm.commonForm_symm
#print axioms YMGap.Continuum.BF4WilsonAllNomeReflectedForm.commonForm_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeReflectedForm.intrinsicForm
#print axioms YMGap.Continuum.BF4WilsonAllNomeReflectedForm.intrinsicForm_chart
#print axioms YMGap.Continuum.BF4WilsonAllNomeReflectedForm.intrinsicForm_symm
#print axioms YMGap.Continuum.BF4WilsonAllNomeReflectedForm.intrinsicForm_nonnegative
