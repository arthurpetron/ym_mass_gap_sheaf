/- # Time-zero multiplication on the literal all-nome Wilson form

The finite estimate uses the selected original action and its own positive
partition reciprocal.  Exact window-ratio pinning transfers it to the literal
source width before taking the original joint cutoff/time limit.  No spatial
union or small-nome assumption enters these dense bounds. -/

import YMGap.Continuum.BF4WilsonTimeZeroMultiplierBound
import YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier
import YMGap.Continuum.BF4WilsonAllNomeSeminorm

namespace YMGap.Continuum.BF4WilsonAllNomeTimeZeroBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSiteHaarFactorization (blockCount Local)
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare (OneSided)
open YMGap.Continuum.BF4ExactSlabSiteSelectedHeatAction
open YMGap.Continuum.BF4ExactSlabSiteMultiplierBound
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry (chainIds_physical)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop placeLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflection
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within chart_self)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (difference chart_difference)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (distSq)
open YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier
  (multiply chart_multiply)
open YMGap.Continuum.BF4WilsonTimeZeroChart
  (fixedLoop_local fixedLoop_squareBound)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal (reciprocalTerm)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit (numerator)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (characterBound SquareBound)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex (slabFaceReflectId)
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem finite_reflected_value {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H : Nat) (e : WindowExpression width)
    (he : Within H e) (stage t : Nat) :
    finiteValue w hw0 hw1 (adjacentEvenExtent (width+t+H))
      (selectedIds (width+t+H) width (width+1) (t+H))
      (fun _ hi => chainIds_physical hi)
      (polyMul (reflectCorrectedSlabPolynomial (adjacentEvenExtent (width+t+H))
        (placedPolynomial (adjacentEvenExtent (width+t+H)) (width+1+t) e))
        (placedPolynomial (adjacentEvenExtent (width+t+H)) (width+1+t) e)) stage ≈
    originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H e) e) stage t t := by
  let radius := width+t+H
  let start := width+1
  let E := adjacentEvenExtent radius
  have hw : width ≤ E := by unfold E adjacentEvenExtent centralExtent radius; omega
  have hcenter : start+t+H=radius+1 := by unfold start radius; omega
  have ht : start+(t+(2*H+t)) ≤ E := by
    unfold E adjacentEvenExtent centralExtent radius start
    omega
  let p := placedPolynomial E (start+t) e
  let rp := placedPolynomial E (start+t) (mirror H e)
  have hp := placed_supported E (start+t) e
  have hrp := placed_supported E (start+t) (mirror H e)
  have ha := selectedHeat_supported w (headCutoff w+stage) radius
    (selectedIds radius width start (t+H))
  have hhaar := ((PaddedPolynomialCoeffEqv.mul
    (placed_reflection hw hcenter e he) (.refl _ p)).mul (.refl _
      (selectedHeat w (headCutoff w+stage) radius
        (selectedIds radius width start (t+H))))).haar
    (supported_polyMul (supported_polyMul
      (reflectCorrectedSlabPolynomial_support _ _) hp) ha)
    (supported_polyMul (supported_polyMul hrp hp) ha)
  have hreflected :
      finiteValue w hw0 hw1 E (selectedIds radius width start (t+H))
        (fun _ hi => chainIds_physical hi)
        (polyMul (reflectCorrectedSlabPolynomial E p) p) stage ≈
      finiteValue w hw0 hw1 E (selectedIds radius width start (t+H))
        (fun _ hi => chainIds_physical hi) (polyMul rp p) stage := by
    unfold finiteValue numerator
    exact Q'.mul_eqv_congr_right _ _ _ hhaar
  have hpin := windowRatio_originalFiniteValue hw0 hw1 (m := t) (L := 2*H)
    (n := t) hw ht (.mul (mirror H e) e)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) e he⟩ stage
  have hfin : originalWindowScalar hw0 hw1 (2*H) (.mul (mirror H e) e)
      stage t t ≈
      finiteValue w hw0 hw1 E (selectedIds radius width start (t+H))
        (fun _ hi => chainIds_physical hi) (polyMul rp p) stage :=
    Q'.eqv_trans _ _ _
      (originalWindowScalar_pin hw0 hw1 (2*H) (.mul (mirror H e) e)
        ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) e he⟩ stage t t)
      (by simpa only [p, rp, E, radius, start, selectedIds, placedPolynomial,
        show t+(2*H+t)=2*(t+H) by omega] using hpin)
  exact Q'.eqv_trans _ _ _ (by simpa only [radius, start, E, p] using hreflected)
    (Q'.eqv_symm hfin)

/-- Same selected action, same partition: finite multiplication at literal width. -/
theorem originalWindowScalar_timeZero_multiplier_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H : Nat) (L : SourceLoop width) (spin : Nat)
    (e : WindowExpression width) (he : Within H e) (stage t : Nat) :
    originalWindowScalar hw0 hw1 (2*H)
      (.mul (mirror H (.mul (.loop H L spin) e)) (.mul (.loop H L spin) e))
      stage t t ≤
    characterBound spin * originalWindowScalar hw0 hw1 (2*H)
      (.mul (mirror H e) e) stage t t := by
  let radius := width+t+H
  let start := width+1
  let E := adjacentEvenExtent radius
  let ids := selectedIds radius width start (t+H)
  let p := placedPolynomial E (start+t) e
  let a := placedPolynomial E (start+t) (.loop H L spin)
  have hw : width ≤ E := by unfold E adjacentEvenExtent centralExtent radius; omega
  have hcenter : start+t+H=radius+1 := by unfold start radius; omega
  have hp : OneSided radius p := placed_oneSided hw hcenter e he
  have hps := placed_supported E (start+t) e
  have hperm : ((lowerFaceIds radius ids).map (slabFaceReflectId E)).Perm
      (upperFaceIds radius ids) := by
    have h := selectedLower_reflection_perm (radius := radius) (width := width)
      (start := start) (depth := t+H) (by dsimp [radius, start]; omega)
    simpa only [ids, E, selectedIds, show t+(2*H+t)=2*(t+H) by omega] using h
  let placedL : YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord.SpatialLoop
      E (radius+1) := placeLoop hw (by
    unfold E adjacentEvenExtent centralExtent radius
    omega) L
  have ha : Local radius .fixed a := by
    simpa only [a, placedPolynomial, E, hcenter, placedL, placeLoop] using
      (fixedLoop_local radius placedL spin)
  have hA : SquareBound (blockCount radius) a (characterBound spin) := by
    simpa only [a, placedPolynomial, E, hcenter, placedL, placeLoop] using
      (fixedLoop_squareBound radius placedL spin)
  have hraw := selectedAction_multiplier_bound hw0 hw1 (headCutoff w+stage) radius
    (Nat.le_add_right _ _) ids (fun _ hi => chainIds_physical hi) hperm p a hp hps ha hA
  let reciprocal := reciprocalTerm w hw0 hw1 E ids
    (fun _ hi => chainIds_physical hi) stage
  have hr : (0 : Q') ≤ reciprocal :=
    Q'.le_of_lt (PositiveRationalCauchyReciprocal.term_pos _ _ _ stage)
  have hnormalized :
      finiteValue w hw0 hw1 E ids (fun _ hi => chainIds_physical hi)
        (polyMul (reflectCorrectedSlabPolynomial E (polyMul a p)) (polyMul a p)) stage ≤
      characterBound spin * finiteValue w hw0 hw1 E ids
        (fun _ hi => chainIds_physical hi)
        (polyMul (reflectCorrectedSlabPolynomial E p) p) stage :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ reciprocal hraw hr)
      (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
  have hleft := finite_reflected_value hw0 hw1 H
    (.mul (.loop H L spin) e) ⟨Nat.le_refl H, he⟩ stage t
  have hright := finite_reflected_value hw0 hw1 H e he stage t
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (by
    simpa only [a, p, radius, start, E, ids, placedPolynomial] using hleft))
    (Q'.le_trans' _ _ _ hnormalized
      (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (by
        simpa only [p, radius, start, E, ids] using hright))))

/-- The original joint limit inherits the fixed-width finite cap at every nome. -/
theorem commonForm_timeZero_multiplier_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H : Nat) (L : SourceLoop width) (spin : Nat)
    (e : WindowExpression width) (he : Within H e) :
    leEv (commonForm hw0 hw1 H
      (.mul (.loop H L spin) e) (.mul (.loop H L spin) e)
      ⟨Nat.le_refl H, he⟩ ⟨Nat.le_refl H, he⟩)
      (mul (ofQ' (characterBound spin)) (commonForm hw0 hw1 H e e he he)) := by
  let ae : WindowExpression width := .mul (.loop H L spin) e
  have hae : Within H ae := ⟨Nat.le_refl H, he⟩
  have hleft := originalJoint_diagonal_converges hw0 hw1 (2*H)
    (.mul (mirror H ae) ae)
    ⟨mirror_within H ae, within_mono (by omega : H ≤ 2*H) ae hae⟩
  have hright := originalJoint_diagonal_converges hw0 hw1 (2*H)
    (.mul (mirror H e) e)
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H) e he⟩
  apply leEv_of_convergesTo_le hleft
    (convergesTo_const_mul (ofQ' (characterBound spin)) hright)
  intro n
  apply leEv_ofQ'_of_approx_ge
  intro k
  exact originalWindowScalar_timeZero_multiplier_bound hw0 hw1 H L spin e he n n

/-- The actual intrinsic all-nome squared form has a spin-only cap. -/
theorem intrinsicForm_multiplier_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : SourceLoop width) (spin : Nat)
    (x : IntrinsicExpression width) :
    leEv (intrinsicForm hw0 hw1 (multiply L spin x) (multiply L spin x))
      (mul (ofQ' (characterBound spin)) (intrinsicForm hw0 hw1 x x)) := by
  have hleft := intrinsicForm_chart hw0 hw1
    (multiply L spin x) (multiply L spin x) x.radius (Nat.le_refl _) (Nat.le_refl _)
  have hright := intrinsicForm_chart hw0 hw1 x x x.radius
    (Nat.le_refl _) (Nat.le_refl _)
  simp only [chart_multiply x.radius L spin x (Nat.le_refl _), chart_self] at hleft
  simp only [chart_self] at hright
  exact leEv_trans (leEv_of_equiv hleft)
    (leEv_trans (commonForm_timeZero_multiplier_bound hw0 hw1
      x.radius L spin x.expression x.within)
      (leEv_of_equiv (Pivot2.mul_congr_right hright.symm)))

/-- A time-zero loop can be moved between the two entries of the literal form. -/
theorem commonForm_multiplier_balance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H : Nat) (L : SourceLoop width) (spin : Nat)
    (e f : WindowExpression width) (he : Within H e) (hf : Within H f) :
    Equiv (commonForm hw0 hw1 H (.mul (.loop H L spin) e) f
      ⟨Nat.le_refl H, he⟩ hf)
      (commonForm hw0 hw1 H e (.mul (.loop H L spin) f)
        he ⟨Nat.le_refl H, hf⟩) := by
  have hloop : mirror H (.loop H L spin) = .loop H L spin := by
    change WindowExpression.loop (2*H-H) L spin = .loop H L spin
    congr 1
    omega
  apply YMGap.Continuum.BF4WilsonJointFunctionalLaws.joint_congr hw0 hw1 (2*H)
    (.mul (mirror H (.mul (.loop H L spin) e)) f)
    (.mul (mirror H e) (.mul (.loop H L spin) f))
    ⟨mirror_within H (.mul (.loop H L spin) e),
      within_mono (by omega : H ≤ 2*H) f hf⟩
    ⟨mirror_within H e, within_mono (by omega : H ≤ 2*H)
      (.mul (.loop H L spin) f) ⟨Nat.le_refl H, hf⟩⟩
  change RatPolyCoeffEqv
    (polyMul (polyMul (sourcePolynomial (mirror H (.loop H L spin)))
      (sourcePolynomial (mirror H e))) (sourcePolynomial f))
    (polyMul (sourcePolynomial (mirror H e))
      (polyMul (sourcePolynomial (.loop H L spin)) (sourcePolynomial f)))
  rw [hloop]
  exact ((RatPolyCoeffEqv.mul_comm
    (sourcePolynomial (.loop H L spin)) (sourcePolynomial (mirror H e))).mul_right
      (sourcePolynomial f)).trans
    (RatPolyCoeffEqv.mul_assoc (sourcePolynomial (mirror H e))
      (sourcePolynomial (.loop H L spin)) (sourcePolynomial f))

/-- The intrinsic dense multiplier is symmetric on the same all-nome form. -/
theorem intrinsicForm_multiplier_balance {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : SourceLoop width) (spin : Nat)
    (x y : IntrinsicExpression width) :
    Equiv (intrinsicForm hw0 hw1 (multiply L spin x) y)
      (intrinsicForm hw0 hw1 x (multiply L spin y)) := by
  let H := max x.radius y.radius
  have hx : x.radius ≤ H := Nat.le_max_left _ _
  have hy : y.radius ≤ H := Nat.le_max_right _ _
  have hleft := intrinsicForm_chart hw0 hw1 (multiply L spin x) y H hx hy
  have hright := intrinsicForm_chart hw0 hw1 x (multiply L spin y) H hx hy
  simp only [chart_multiply H L spin x hx] at hleft
  simp only [chart_multiply H L spin y hy] at hright
  exact hleft.trans ((commonForm_multiplier_balance hw0 hw1 H L spin
    (chart H x) (chart H y) (chart_within H x hx) (chart_within H y hy)).trans
    hright.symm)

private theorem distribute (a e f : RatPoly) :
    RatPolyCoeffEqv
      (polyAdd (polyMul a e) (polySmul (-1) (polyMul a f)))
      (polyMul a (polyAdd e (polySmul (-1) f))) :=
  ((RatPolyCoeffEqv.mul_add_right a e (polySmul (-1) f)).trans
    ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.polyMul_smul_right (-1) a f))).symm

private theorem commonForm_distribute_diagonal {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (H : Nat) (a e f : WindowExpression width)
    (ha : Within H a) (he : Within H e) (hf : Within H f) :
    Equiv (commonForm hw0 hw1 H
      (.add (.mul a e) (.smul (-1) (.mul a f)))
      (.add (.mul a e) (.smul (-1) (.mul a f)))
      ⟨⟨ha, he⟩, ⟨ha, hf⟩⟩ ⟨⟨ha, he⟩, ⟨ha, hf⟩⟩)
      (commonForm hw0 hw1 H
        (.mul a (.add e (.smul (-1) f)))
        (.mul a (.add e (.smul (-1) f)))
        ⟨ha, ⟨he, hf⟩⟩ ⟨ha, ⟨he, hf⟩⟩) := by
  let d : WindowExpression width := .add (.mul a e) (.smul (-1) (.mul a f))
  let m : WindowExpression width := .mul a (.add e (.smul (-1) f))
  have hD : Within H d := ⟨⟨ha, he⟩, ⟨ha, hf⟩⟩
  have hM : Within H m := ⟨ha, ⟨he, hf⟩⟩
  apply YMGap.Continuum.BF4WilsonJointFunctionalLaws.joint_congr hw0 hw1 (2*H)
    (.mul (mirror H d) d) (.mul (mirror H m) m)
    ⟨mirror_within H d, within_mono (by omega : H ≤ 2*H) d hD⟩
    ⟨mirror_within H m, within_mono (by omega : H ≤ 2*H) m hM⟩
  exact (distribute (sourcePolynomial (mirror H a))
    (sourcePolynomial (mirror H e)) (sourcePolynomial (mirror H f))).mul
    (distribute (sourcePolynomial a) (sourcePolynomial e) (sourcePolynomial f))

/-- Dense squared-distance cap on literal intrinsic all-nome expressions. -/
theorem distSq_multiplier_bound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (L : SourceLoop width) (spin : Nat)
    (x y : IntrinsicExpression width) :
    leEv (distSq hw0 hw1 (multiply L spin x) (multiply L spin y))
      (mul (ofQ' (characterBound spin)) (distSq hw0 hw1 x y)) := by
  let H := max x.radius y.radius
  have hx : x.radius ≤ H := Nat.le_max_left _ _
  have hy : y.radius ≤ H := Nat.le_max_right _ _
  have hleft := intrinsicForm_chart hw0 hw1
    (difference (multiply L spin x) (multiply L spin y))
    (difference (multiply L spin x) (multiply L spin y)) H
    (Nat.max_le.mpr ⟨hx, hy⟩) (Nat.max_le.mpr ⟨hx, hy⟩)
  have hright := intrinsicForm_chart hw0 hw1
    (difference x y) (difference x y) H
    (Nat.max_le.mpr ⟨hx, hy⟩) (Nat.max_le.mpr ⟨hx, hy⟩)
  simp only [chart_difference H (multiply L spin x) (multiply L spin y) hx hy,
    chart_multiply H L spin x hx, chart_multiply H L spin y hy] at hleft
  simp only [chart_difference H x y hx hy] at hright
  exact leEv_trans (leEv_of_equiv hleft)
    (leEv_trans (leEv_of_equiv (commonForm_distribute_diagonal hw0 hw1 H
      (.loop H L spin) (chart H x) (chart H y) (Nat.le_refl _)
      (chart_within H x hx) (chart_within H y hy)))
      (leEv_trans (commonForm_timeZero_multiplier_bound hw0 hw1 H L spin
        (.add (chart H x) (.smul (-1) (chart H y)))
        ⟨chart_within H x hx, chart_within H y hy⟩)
        (leEv_of_equiv (Pivot2.mul_congr_right hright.symm))))

#print axioms originalWindowScalar_timeZero_multiplier_bound
#print axioms commonForm_timeZero_multiplier_bound
#print axioms intrinsicForm_multiplier_bound
#print axioms commonForm_multiplier_balance
#print axioms intrinsicForm_multiplier_balance
#print axioms distSq_multiplier_bound

end YMGap.Continuum.BF4WilsonAllNomeTimeZeroBound
