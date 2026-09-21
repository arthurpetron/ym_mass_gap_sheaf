/-
# Cutoff- and background-independent cost of the ORIGINAL coupling score

Expand the normalized score before estimating it:
 s = gain_v*(F_v-F_u) + (gain_v-gain_u)*F_u.
The actual face floors bound the gains; the relative mass perturbation bounds
their difference. Original square certificates bound both polynomial terms.
Thus the centered score's second moment has an explicit O(|v-u|^2) budget
independent of the late cutoff, face extent and entire positive background.

All dependence on u,v,W remains explicit. No uniformity at weak coupling,
spatial decay, limit of changing scores, or continuum survival follows here.
-/
import YMGap.Continuum.BF4ExactSlabCouplingCenteredResponse
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment

namespace YMGap.Continuum.BF4ExactSlabCouplingScoreBound

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeTailInterval
open YMGap.Continuum.BF4ExactSlabCouplingVariationInterval
open YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability
open YMGap.Continuum.BF4ExactSlabOneFaceCutoffStability (faceMass faceMoment faceMass_positive)
open YMGap.Continuum.BF4ExactSlabFaceSetBoundaryComparison (ratio_difference_bound)
open YMGap.Continuum.BF4ExactSlabCouplingCenteredResponse
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarCenteredResponse
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

/-- Nome-dependent inverse of the proved original one-face head floor. -/
def inverseHead (w : Q') : Q' := HKConv.divPos 1 (headFloor w)

theorem inverseHead_nonnegative (w : Q') : (0 : Q') ≤ inverseHead w :=
  HKConv.divPos_nonneg Q'.zero_le_one

private theorem inverseHead_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    inverseHead w * headFloor w ≈ 1 :=
  HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (headFloor_positive hw0 hw1))

private theorem mass_le_inverse {Z z ell inv : Q'} (hi : (0 : Q') ≤ inv)
    (hpin : inv*ell ≈ 1) (hfloor : ell*Z ≤ z) : Z ≤ inv*z := by
  have hc : inv*(ell*Z) ≈ Z := Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hpin) (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hc)
    (Q'.mul_le_mul_of_nonneg_left _ _ inv hfloor hi)

private theorem gain_le {Z z inv : Q'} (hz : (0 : Q') < z) (h : Z ≤ inv*z) :
    Z*Q'.recipPos z hz ≤ inv :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ h (Q'.le_of_lt (Q'.recipPos_pos z hz)))
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv z hz))
        (Q'.mul_one_eqv _))))

/-- Numerator mass is fixed: only ONE relative partition perturbation is paid. -/
private theorem gain_difference_le {Z z z' inv eta : Q'}
    (hZ : (0 : Q') ≤ Z) (hz : (0 : Q') < z) (hz' : (0 : Q') < z')
    (he : (0 : Q') ≤ eta) (h : Z ≤ inv*z)
    (hdiff : Q'.abs (z' + -z) ≤ eta*z') :
    Q'.abs (Z*Q'.recipPos z' hz' + -(Z*Q'.recipPos z hz)) ≤ eta*inv := by
  apply ratio_difference_bound Z Z z' z (eta*inv) hz' hz
  have hc : Z*z + -(Z*z') ≈ -(Z*(z' + -z)) :=
    poly_identity_of_normal_eq (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (.neg (.mul (.var 0) (.add (.var 2) (.neg (.var 1))))) (by decide)
      (fun | 0 => Z | 1 => z | _ => z')
  have ha := ExpNeg.abs_mul_le Z (z' + -z)
  rw [ExpNeg.abs_of_nonneg hZ] at ha
  have hb := Q'.mul_le_mul_of_nonneg_left _ _ Z hdiff hZ
  have hm := Q'.mul_le_mul_of_nonneg_right _ _ (eta*z') h (Q'.mul_nonneg _ _ he (Q'.le_of_lt hz'))
  have hs : (inv*z)*(eta*z') ≈ (eta*inv)*(z'*z) := by
    show _ * (_ : Int) = _ * (_ : Int)
    simp only [Q'.mul_num_cast, Q'.mul_den_cast]
    ac_rfl
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hc))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_neg' _))
      (Q'.le_trans' _ _ _ ha (Q'.le_trans' _ _ _ hb
        (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hs)))))

private theorem square_le_of_abs_le {a c : Q'} (hc : (0 : Q') ≤ c) (h : Q'.abs a ≤ c) :
    a*a ≤ c*c :=
  Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le a a)
      (Q'.mul_le_mul_of_nonneg h h hc (Q'.abs_nonneg a)))

/-- Explicit quadratic coupling budget; no cutoff, extent or background occurs. -/
def scoreVarianceCap (W u v : Q') : Q' :=
  sumBound ((inverseHead v*inverseHead v)*(variationCap W u v*variationCap W u v))
    (((relativeVariation W u v*inverseHead u)*(relativeVariation W u v*inverseHead u))*
      (prefixCap u*prefixCap u))

/-- Human-readable factorization: 2*(delta/headFloor(v))^2 times
1+(prefixCap(u)/headFloor(u))^2. All coupling dependence remains explicit. -/
theorem scoreVarianceCap_formula {v : Q'} (hv0 : (0 : Q') < v) (hv1 : v < (1 : Q'))
    (W u : Q') :
    scoreVarianceCap W u v ≈
      2*(relativeVariation W u v*relativeVariation W u v)*
        (1+(inverseHead u*prefixCap u)*(inverseHead u*prefixCap u)) := by
  let eta := relativeVariation W u v
  let delta := variationCap W u v
  let iv := inverseHead v
  have he : eta ≈ delta*iv := by
    have hs : eta*(iv*headFloor v) ≈ (eta*headFloor v)*iv := by
      show _ * (_ : Int) = _ * (_ : Int)
      simp only [Q'.mul_num_cast, Q'.mul_den_cast]
      ac_rfl
    exact Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_one_eqv eta))
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left eta _ _ (Q'.eqv_symm (inverseHead_pin hv0 hv1)))
        (Q'.eqv_trans _ _ _ hs (Q'.mul_eqv_congr_right _ _ iv (relativeVariation_floor hv0 hv1))))
  have hf : (iv*iv)*(delta*delta) ≈ eta*eta := by
    have hs : (iv*iv)*(delta*delta) ≈ (delta*iv)*(delta*iv) := by
      show _ * (_ : Int) = _ * (_ : Int)
      simp only [Q'.mul_num_cast, Q'.mul_den_cast]
      ac_rfl
    exact Q'.eqv_trans _ _ _ hs (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm he))
      (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm he)))
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' hf hf) (Q'.eqv_refl _))
    (poly_identity_of_normal_eq
      (.add (.add (.mul (.var 0) (.var 0)) (.mul (.var 0) (.var 0)))
        (.add (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 2)))
          (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1))) (.mul (.var 2) (.var 2)))))
      (.mul (.mul (.const 2) (.mul (.var 0) (.var 0)))
        (.add (.const 1) (.mul (.mul (.var 1) (.var 2)) (.mul (.var 1) (.var 2)))))
      (by decide) (fun | 0 => eta | 1 => inverseHead u | _ => prefixCap u))

variable {u v W : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v) (hvW : v ≤ W) (hW1 : W < (1 : Q'))
  (K extent id : Nat) (hi : id ∈ slabPhysicalFaceEdges extent)
  (hKu : headCutoff u ≤ K) (hKv : headCutoff v ≤ K)
  {B : RatPoly} (HB : Certificate (blocks extent) B)
  (hB : (0 : Q') < quaternionHaar (blocks extent) B)

local notation "hv0" => Q'.pos_of_lt_of_le hu0 huv
local notation "hv1" => Q'.lt_of_le_of_lt hvW hW1
local notation "hu1" => Q'.lt_of_le_of_lt huv hv1
local notation "hW0" => Q'.pos_of_lt_of_le hv0 hvW
local notation "hU" => faceMass_positive hu0 hu1 extent id hi HB K hKu hB
local notation "hV" => faceMass_positive hv0 hv1 extent id hi HB K hKv hB
local notation "alphaU" => quaternionHaar (blocks extent) B * Q'.recipPos (faceMass u K extent id B) hU
local notation "alphaV" => quaternionHaar (blocks extent) B * Q'.recipPos (faceMass v K extent id B) hV
local notation "score" => faceScore hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB

private theorem gainV_bound : alphaV ≤ inverseHead v :=
  gain_le hV (mass_le_inverse (inverseHead_nonnegative v) (inverseHead_pin hv0 hv1)
    (faceHead_weighted_floor hv0 hv1 K extent id hi hKv HB))

private theorem gainChange_bound : Q'.abs (alphaV + -alphaU) ≤ relativeVariation W u v*inverseHead u :=
  gain_difference_le (Q'.le_of_lt hB) hU hV (relativeVariation_nonnegative hW0 u v)
    (mass_le_inverse (inverseHead_nonnegative u) (inverseHead_pin hu0 hu1)
      (faceHead_weighted_floor hu0 hu1 K extent id hi hKu HB))
    (mass_difference_bound hu0 huv hvW hW1 K extent id hi hKv HB)

/-- The difference is expanded BEFORE bounding either normalized endpoint. -/
theorem score_decomposition : RatPolyCoeffEqv score
    (polyAdd (polySmul alphaV (faceDifference u v K extent id))
      (polySmul (alphaV + -alphaU) (faceHeatPolynomial u K extent id))) := by
  let F := faceHeatPolynomial u K extent id
  let D := faceDifference u v K extent id
  have hneg : RatPolyCoeffEqv (polySmul (-1) (polySmul alphaU F)) (polySmul (-alphaU) F) :=
    (RatPolyCoeffEqv.smul_assoc (-1) alphaU F).trans
      (RatPolyCoeffEqv.smul_coefficient
        (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
          (by decide) (fun _ => alphaU)) F)
  have hmain := (((faceDifference_pin u v K extent id).smul alphaV).trans
    (RatPolyCoeffEqv.smul_add alphaV F D)).add hneg
  have horder : RatPolyCoeffEqv
      (polyAdd (polyAdd (polySmul alphaV F) (polySmul alphaV D)) (polySmul (-alphaU) F))
      (polyAdd (polySmul alphaV D) (polyAdd (polySmul alphaV F) (polySmul (-alphaU) F))) :=
    coeffEvalExpr_eqv_of_normalize_eq (.add (.add (.var 0) (.var 1)) (.var 2))
      (.add (.var 1) (.add (.var 0) (.var 2))) (by decide)
      (fun | 0 => polySmul alphaV F | 1 => polySmul alphaV D | _ => polySmul (-alphaU) F)
  exact hmain.trans (horder.trans ((RatPolyCoeffEqv.refl _).add
    (RatPolyCoeffEqv.add_smul_same alphaV (-alphaU) F)))

/-- The centered score's actual second moment is bounded with NO cutoff,
extent, spectator-volume or background-mass factor in the explicit budget. -/
theorem score_secondMoment_bound :
    normalizedMoment (blocks extent) B (polyMul score score) hB ≤ scoreVarianceCap W u v := by
  let delta := variationCap W u v
  let eta := relativeVariation W u v
  let P := QuaternionHaarIntervalSecondMoment.Interval.squareBound
    (faceDifferenceInterval (Q'.le_of_lt hu0) huv hvW hW0 hW1 K extent id hi)
  let Q := QuaternionHaarIntervalSecondMoment.Interval.squareBound
    (facePrefixInterval hu0 hu1 K extent id hi)
  let R := (P.smul alphaV).add (Q.smul (alphaV + -alphaU))
  have hraw := QuaternionHaarIntervalSecondMoment.Interval.normalized_square_le R HB hB
  have hd := score_decomposition hu0 huv hvW hW1 K extent id hi hKu hKv HB hB
  have hp := QuaternionHaarNormalizedMomentCongruence.normalizedMoment_congr hB hB
    (RatPolyCoeffEqv.refl B) (hd.mul hd)
  have hgain0 : (0 : Q') ≤ alphaV :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt hB) (Q'.le_of_lt (Q'.recipPos_pos _ hV))
  have hsqV : alphaV*alphaV ≤ inverseHead v*inverseHead v :=
    square_le_of_abs_le (inverseHead_nonnegative v)
      (by rw [ExpNeg.abs_of_nonneg hgain0]; exact gainV_bound hu0 huv hvW hW1 K extent id hi hKv HB hB)
  have hsqChange : (alphaV + -alphaU)*(alphaV + -alphaU) ≤
      (eta*inverseHead u)*(eta*inverseHead u) :=
    square_le_of_abs_le
      (Q'.mul_nonneg _ _ (relativeVariation_nonnegative hW0 u v) (inverseHead_nonnegative u))
      (gainChange_bound hu0 huv hvW hW1 K extent id hi hKu hKv HB hB)
  have hfirst := Q'.mul_le_mul_of_nonneg_right _ _ (delta*delta) hsqV
    (SumOfSquares.q_mul_self_nonneg delta)
  have hsecond := Q'.mul_le_mul_of_nonneg_right _ _ (prefixCap u*prefixCap u) hsqChange
    (SumOfSquares.q_mul_self_nonneg (prefixCap u))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hp) (Q'.le_trans' _ _ _ hraw
    (Q'.add_le_add (Q'.add_le_add hfirst hfirst) (Q'.add_le_add hsecond hsecond)))

/-- SAME original normalized endpoints, now with a fully computed score cost.
The observable's retained-background variance remains, not a sup-norm input. -/
theorem face_response_variance_bound {p : RatPoly}
    (hp : SupportedQuaternionBlocks (blocks extent) p) :
    let d := faceMoment v K extent id B p * Q'.recipPos (faceMass v K extent id B) hV +
      -(faceMoment u K extent id B p * Q'.recipPos (faceMass u K extent id B) hU)
    d*d ≤ normalizedVariance (blocks extent) B p hB * scoreVarianceCap W u v :=
  Q'.le_trans' _ _ _
    (face_response_square_bound hu0 hu1 hv0 hv1 K extent id hi hKu hKv HB hB hp)
    (Q'.mul_le_mul_of_nonneg_left _ _ _
      (score_secondMoment_bound hu0 huv hvW hW1 K extent id hi hKu hKv HB hB)
      (normalizedVariance_nonnegative HB hB hp))

include hu0 huv hvW hW1 hi hKu hKv in
/-- Original spectator-product instance. The explicit coupling budget has no
dependence on the spectator nome, its cutoff, its face count, or the extent. -/
theorem original_background_variance_bound
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (J : Nat) (hJ : headCutoff w ≤ J) (ids : List Nat)
    (hids : ∀ j, j ∈ ids → j ∈ slabPhysicalFaceEdges extent)
    {p : RatPoly} (hp : SupportedQuaternionBlocks (blocks extent) p) :
    let B := polynomialProduct (faceHeatPolynomial w J extent) ids
    let HB := headProduct_certificate hw0 hw1 J extent hJ ids hids
    let hB : (0 : Q') < quaternionHaar (blocks extent) B :=
      Q'.pos_of_lt_of_le (BF4ExactSlabAllNomeFaceSetReciprocal.partitionFloor_pos hw0 hw1 ids)
        (BF4ExactSlabAllNomeFaceSetReciprocal.partition_floor hw0 hw1 extent ids hids J hJ)
    let hOld := faceMass_positive hu0 hu1 extent id hi HB K hKu hB
    let hNew := faceMass_positive hv0 hv1 extent id hi HB K hKv hB
    let d := faceMoment v K extent id B p * Q'.recipPos (faceMass v K extent id B) hNew +
      -(faceMoment u K extent id B p * Q'.recipPos (faceMass u K extent id B) hOld)
    d*d ≤ normalizedVariance (blocks extent) B p hB * scoreVarianceCap W u v :=
  face_response_variance_bound hu0 huv hvW hW1 K extent id hi hKu hKv
    (headProduct_certificate hw0 hw1 J extent hJ ids hids)
    (Q'.pos_of_lt_of_le (BF4ExactSlabAllNomeFaceSetReciprocal.partitionFloor_pos hw0 hw1 ids)
      (BF4ExactSlabAllNomeFaceSetReciprocal.partition_floor hw0 hw1 extent ids hids J hJ)) hp

end YMGap.Continuum.BF4ExactSlabCouplingScoreBound

#print axioms YMGap.Continuum.BF4ExactSlabCouplingScoreBound.inverseHead
#print axioms YMGap.Continuum.BF4ExactSlabCouplingScoreBound.inverseHead_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabCouplingScoreBound.scoreVarianceCap
#print axioms YMGap.Continuum.BF4ExactSlabCouplingScoreBound.scoreVarianceCap_formula
#print axioms YMGap.Continuum.BF4ExactSlabCouplingScoreBound.score_decomposition
#print axioms YMGap.Continuum.BF4ExactSlabCouplingScoreBound.score_secondMoment_bound
#print axioms YMGap.Continuum.BF4ExactSlabCouplingScoreBound.face_response_variance_bound
#print axioms YMGap.Continuum.BF4ExactSlabCouplingScoreBound.original_background_variance_bound
