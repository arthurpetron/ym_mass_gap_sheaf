/-
# Strict covariance factor from the selected plaquette prediction floor

The original selected-action covariance has a nome-dependent strict factor
when one observable is an actual plaquette character and the other misses a
link of that plaquette.  This is a one-pair covariance estimate, not an
iterated spatial or physical-time decay theorem.
-/

import YMGap.Continuum.BF4ExactSlabSelectedPredictionCovariance
import YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds
import YMGap.Continuum.BF4ExactSlabSharpCharacterWeights
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment
import YMGap.Continuum.ChebyshevBound

namespace YMGap.Continuum.BF4ExactSlabSelectedPredictionRate

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
open YMGap.Continuum.BF4ExactSlabSelectedPredictionCovariance
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabConnectedFaceResponse
open YMGap.Continuum.BF4ExactSlabAllNomeFiniteMomentBounds
open YMGap.Continuum.BF4ExactSlabSharpCharacterWeights
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarPredictionCovariance
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal
  (convergesTo_mul_general)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-- A single covariance factor, not an iterable decay rate. -/
def eta (w : Q') : Q' := 1 + -(starRatio w * quarter)

theorem eta_lower_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    Q'.mkPos 3 4 (by decide) ≤ eta w := by
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ quarter
    (starRatio_le_one hw0 hw1) (by decide : (0 : Q') ≤ quarter)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by decide : Q'.mkPos 3 4 (by decide) ≈ 1 + -(1*quarter)))
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hmul))

theorem eta_lt_one {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    eta w < 1 := by
  let e := starRatio w * quarter
  have hp : (0 : Q') < e :=
    Q'.mul_pos (starRatio_positive hw0 hw1) (by decide : (0 : Q') < quarter)
  have hn : (0 : Int) < e.num := Q'.num_pos_of_pos hp
  change (((1 : Int) * (e.den : Int) + (-e.num) * (1 : Int)) * (1 : Int)) <
    ((1 : Int) * (((1 : Nat) * e.den : Nat) : Int))
  simp only [Nat.one_mul, Int.one_mul, Int.mul_one]
  omega

private theorem face_variance_le_four {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K extent : Nat) (hK : headCutoff w ≤ K)
    (ids : List Nat) (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (face : Z4Plaq) (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    normalizedVariance (N extent)
      (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (faceCharacter extent face)
      (selectedMass_positive hw0 hw1 K extent hK ids hids) ≤ 4 := by
  let W := polynomialProduct (faceHeatPolynomial w K extent) ids
  let hZ := selectedMass_positive hw0 hw1 K extent hK ids hids
  let p := faceCharacter extent face
  have hcert := headProduct_certificate hw0 hw1 K extent hK ids hids
  have hsq := QuaternionHaarIntervalSecondMoment.Interval.squareBound
    (faceCharacterInterval extent face hf 1)
  have hsecond := QuaternionHaarIntervalSecondMoment.Interval.normalized_square_le hsq hcert hZ
  have hcap : Q'.eqv (dimQ 1 * dimQ 1) 4 := by decide
  have hsecond4 : normalizedMoment (N extent) W (polyMul p p) hZ ≤ 4 :=
    Q'.le_trans' _ _ _ hsecond (Q'.le_of_eqv hcap)
  have hvar : normalizedVariance (N extent) W p hZ ≤
      normalizedMoment (N extent) W (polyMul p p) hZ := by
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left _ _ _
        (Q'.nonpos_neg_of_nonneg (Cheb.square_nonneg _)))
      (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _)))
  exact Q'.le_trans' _ _ _ hvar hsecond4

private theorem deficit_le_rate {w A : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (hA : A ≤ 4) :
    A + -(starRatio w) ≤ eta w * A := by
  let s := starRatio w
  have hk : (0 : Q') ≤ s*quarter :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (starRatio_positive hw0 hw1)) (by decide)
  have hfour : (s*quarter)*4 ≈ s :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left s _ _ (by decide : quarter*4 ≈ 1))
        (Q'.mul_one_eqv s))
  have hpaid : (s*quarter)*A ≤ s :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hA hk)
      (Q'.le_of_eqv hfour)
  have he : A + -((s*quarter)*A) ≈ eta w*A :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.neg (.mul (.mul (.var 1) (.var 2)) (.var 0))))
      (.mul (.add (.const 1) (.neg (.mul (.var 1) (.var 2)))) (.var 0))
      (by decide) (fun | 0 => A | 1 => s | _ => quarter)
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left A _ _ (Q'.neg_le_neg hpaid)) (Q'.le_of_eqv he)

/-- Original selected-action covariance, with an explicit nome-only factor
and no small-nome assumption. -/
theorem finite_covariance_rate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N extent) q) (links : List Z4Link)
    (hlocal : LinkLocal extent links q) (hfree : link ∉ links) (stage : Nat) :
    let p := faceCharacter extent face
    let C := fun a b => finiteCovariance w hw0 hw1 extent ids hids a b stage
    C p q * C p q ≤ eta w * (C p p * C q q) := by
  dsimp only
  let p := faceCharacter extent face
  let C := fun a b => finiteCovariance w hw0 hw1 extent ids hids a b stage
  have hdef := finite_covariance_deficit hw0 hw1 extent ids hids hnodup
    hf link hl q hq links hlocal hfree stage
  have hpp := normalizedCovariance_finiteCovariance hw0 hw1 extent ids hids p p stage
  have hqq := normalizedCovariance_finiteCovariance hw0 hw1 extent ids hids q q stage
  have hp4 : C p p ≤ 4 := Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpp)
    (face_variance_le_four hw0 hw1 (headCutoff w+stage) extent
      (Nat.le_add_right _ _) ids hids face hf)
  have hqnonneg : (0 : Q') ≤ C q q := Q'.le_trans' _ _ _
    (QuaternionHaarPredictionCovariance.normalizedVariance_nonnegative
    (headProduct_certificate hw0 hw1 (headCutoff w + stage) extent
      (Nat.le_add_right _ _) ids hids)
    (selectedMass_positive hw0 hw1 (headCutoff w + stage) extent
      (Nat.le_add_right _ _) ids hids) hq) (Q'.le_of_eqv hqq)
  have hscalar := deficit_le_rate hw0 hw1 hp4
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hscalar hqnonneg
  exact Q'.le_trans' _ _ _ hdef
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)))

/-- The same strict factor survives removal of the heat cutoff at fixed
extent. There is still no distance or time iteration in this statement. -/
theorem covariance_rate {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N extent) q) (links : List Z4Link)
    (hlocal : LinkLocal extent links q) (hfree : link ∉ links) :
    let p := faceCharacter extent face
    let C := covariance w hw0 hw1 extent ids hids
    leEv (CReal.mul (C p q) (C p q))
      (CReal.mul (ofQ' (eta w)) (CReal.mul (C p p) (C q q))) := by
  dsimp only
  let p := faceCharacter extent face
  let C := covariance w hw0 hw1 extent ids hids
  let f : RatPoly → RatPoly → Nat → CReal :=
    fun a b stage => ofQ' (finiteCovariance w hw0 hw1 extent ids hids a b stage)
  have hpq := finite_covariance_converges w hw0 hw1 extent ids hids
    (faceCharacter extent face) q
  have hpp := finite_covariance_converges w hw0 hw1 extent ids hids
    (faceCharacter extent face) (faceCharacter extent face)
  have hqq := finite_covariance_converges w hw0 hw1 extent ids hids q q
  have hleft : ConvergesTo (fun stage => CReal.mul (f p q stage) (f p q stage))
      (CReal.mul (C p q) (C p q)) := convergesTo_mul_general hpq hpq
  have hright : ConvergesTo
      (fun stage => CReal.mul (ofQ' (eta w))
        (CReal.mul (f p p stage) (f q q stage)))
      (CReal.mul (ofQ' (eta w)) (CReal.mul (C p p) (C q q))) :=
    CReal.convergesTo_const_mul (ofQ' (eta w)) (convergesTo_mul_general hpp hqq)
  apply CReal.leEv_of_convergesTo_le hleft hright
  intro stage
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have hfin := finite_covariance_rate hw0 hw1 extent ids hids hnodup
    hf link hl q hq links hlocal hfree stage
  exact Q'.le_trans' _ _ _ hfin
    (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε))

#print axioms eta_lower_bound
#print axioms eta_lt_one
#print axioms finite_covariance_rate
#print axioms covariance_rate

end YMGap.Continuum.BF4ExactSlabSelectedPredictionRate
