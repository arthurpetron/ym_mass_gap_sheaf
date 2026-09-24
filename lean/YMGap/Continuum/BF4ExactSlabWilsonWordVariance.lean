/-
# Actual selected-action variance of a forward-head Wilson word

An arbitrary physical no-repetition face list is retained, so the theorem
applies to the actual fixed-width chain action as well as the whole slab.
Only factors incident to the selected link are compared. The remaining
action and its first/second moments are kept inside the original Haar law.
Every rational center satisfies the strengthened factor (1+c*c); selecting
the SAME full-action mean yields its actual normalized variance.

The computed positive floor still depends on nome. No scaling survival,
spatial mixing, or continuum mass-gap theorem is asserted.
-/

import YMGap.Continuum.BF4ExactSlabWilsonWordSingleLinkMoments
import YMGap.Continuum.BF4ExactSlabSelectedStarVariance

namespace YMGap.Continuum.BF4ExactSlabWilsonWordVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance
  (selectedRest selected_star_bounds selectedMass_positive normalizedMoment_finiteValue)
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation (finiteValue)
open YMGap.Continuum.BF4ExactSlabWilsonWordSingleLinkMoments
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionOneLinkFundamentalSchurSpectatorFubini
open YMGap.Continuum.SU2QuaternionHaarBlockConditionalAlgebra
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

private theorem rest_physical {extent : Nat} {ids : List Nat}
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (link : Z4Link) {id : Nat} (hi : id ∈ selectedRest extent ids link) :
    id ∈ slabPhysicalFaceEdges extent :=
  hids id (List.mem_filter.mp hi).1

private theorem rest_independent (w : Q') (K extent : Nat) (ids : List Nat)
    (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent) :
    QuaternionBlockIndependent ((boundaryCompleteSlabLinks extent).idxOf link)
      (polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link)) := by
  apply degree_zero_independent
  apply linkLocal_degree_zero (heatProduct_local w K extent _) link hl
  intro hm
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hm
  have hn : link ∉ edgesOf (slabPlaquetteAt extent id) := by
    have h := (List.mem_filter.mp hi).2
    simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using h
  exact hn he

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

/-- All selected action factors remain, and the center factor is not dropped.
The partition on the left is the SAME selected-action partition. -/
theorem shifted_square_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)
    (tail : List OrientedBF4Link)
    (hphysical : ∀ e, e ∈ tail → e.link ∈ boundaryCompleteSlabLinks extent)
    (habsent : ∀ e, e ∈ tail → e.link ≠ link) (c : Q') :
    let A := polynomialProduct (faceHeatPolynomial w K extent) ids
    let p := character extent (⟨link, false⟩ :: tail) 1
    (starRatio w * (1+c*c)) * quaternionHaar (B extent) A ≤
      quaternionHaar (B extent) (polyMul A (polyMul (shifted p c) (shifted p c))) := by
  let A := polynomialProduct (faceHeatPolynomial w K extent) ids
  let R := polynomialProduct (faceHeatPolynomial w K extent) (selectedRest extent ids link)
  let p := character extent (⟨link, false⟩ :: tail) 1
  let s := polyMul (shifted p c) (shifted p c)
  let Z := quaternionHaar (B extent) R
  have PR := headProduct_certificate hw0 hw1 K extent hK (selectedRest extent ids link)
    (fun _ hi => rest_physical hids link hi)
  have hr := rest_independent w K extent ids link hl
  have hm : quaternionHaar (B extent) (polyMul R p) ≈ 0 :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (original_word_first_moment extent link hl tail habsent R hr)
  have hsq : quaternionHaar (B extent) (polyMul R (polyMul p p)) ≈ Z :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (original_word_second_moment extent link hl tail hphysical habsent R hr)
  have htest : quaternionHaar (B extent) (polyMul s R) ≈ (1+c*c)*Z :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
      (Q'.eqv_trans _ _ _ (shifted_moment_expansion PR (character_supported extent _ 1) c)
        (Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr' (Q'.add_eqv_congr' hsq
            (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_left (2*c) _ _ hm))) (Q'.eqv_refl _))
          (poly_identity_of_normal_eq
            (.add (.add (.var 0) (.neg (.mul (.mul (.const 2) (.var 1)) (.const 0))))
              (.mul (.mul (.var 1) (.var 1)) (.var 0)))
            (.mul (.add (.const 1) (.mul (.var 1) (.var 1))) (.var 0))
            (by decide) (fun | 0 => Z | _ => c))))
  have hlo : lowerFactor w * ((1+c*c)*Z) ≤ quaternionHaar (B extent) (polyMul A s) :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.mul_eqv_congr_left _ _ _ htest))
      (Q'.le_trans' _ _ _
        (selected_star_bounds hw0 hw1 K extent hK ids hids hnodup link
          (Certificate.square (shifted p c) (shifted_supported (character_supported extent _ 1) c))).1
        (Q'.le_of_eqv (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))))
  have hhi : quaternionHaar (B extent) A ≤ upperFactor w * Z :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (haar_of_coeff (RatPolyCoeffEqv.one_mul A)))
      (Q'.le_trans' _ _ _
        (selected_star_bounds hw0 hw1 K extent hK ids hids hnodup link (Certificate.one (B extent))).2
        (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (haar_of_coeff (RatPolyCoeffEqv.one_mul R)))))
  have hc : (0 : Q') ≤ 1+c*c := Q'.le_trans' _ _ _ Q'.zero_le_one
    (Q'.add_le_self_of_nonneg 1 _ (SumOfSquares.q_mul_self_nonneg c))
  have he : (starRatio w*(1+c*c))*(upperFactor w*Z) ≈ lowerFactor w*((1+c*c)*Z) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 3))) (by decide)
      (fun | 0 => starRatio w | 1 => 1+c*c | 2 => upperFactor w | _ => Z))
      (Q'.mul_eqv_congr_right _ _ _
        (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos (upperFactor_positive hw0))))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hhi
      (Q'.mul_nonneg _ _ (Q'.le_of_lt (starRatio_positive hw0 hw1)) hc))
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv he) hlo)

/-- The center is now the actual SAME selected-action mean, not the free mean. -/
theorem normalizedVariance_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)
    (tail : List OrientedBF4Link)
    (hphysical : ∀ e, e ∈ tail → e.link ∈ boundaryCompleteSlabLinks extent)
    (habsent : ∀ e, e ∈ tail → e.link ≠ link) :
    let A := polynomialProduct (faceHeatPolynomial w K extent) ids
    let p := character extent (⟨link, false⟩ :: tail) 1
    let hz := selectedMass_positive hw0 hw1 K extent hK ids hids
    let m := normalizedMoment (B extent) A p hz
    starRatio w*(1+m*m) ≤ normalizedVariance (B extent) A p hz := by
  let A := polynomialProduct (faceHeatPolynomial w K extent) ids
  let p := character extent (⟨link, false⟩ :: tail) 1
  let hz := selectedMass_positive hw0 hw1 K extent hK ids hids
  let m := normalizedMoment (B extent) A p hz
  let r := Q'.recipPos (quaternionHaar (B extent) A) hz
  have hraw := shifted_square_floor hw0 hw1 K extent hK ids hids hnodup link hl tail hphysical habsent m
  have he : ((starRatio w*(1+m*m))*quaternionHaar (B extent) A)*r ≈ starRatio w*(1+m*m) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_recipPos_eqv _ hz))
        (Q'.mul_one_eqv _))
  have hpin := own_mean_pin (headProduct_certificate hw0 hw1 K extent hK ids hids)
    (character_supported extent (⟨link, false⟩ :: tail) 1) hz
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ r hraw (Q'.le_of_lt (Q'.recipPos_pos _ hz)))
      (Q'.le_of_eqv hpin))

/-- The original finiteValue numerator and reciprocal are retained exactly. -/
theorem finiteValue_variance_floor_with_mean {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)
    (tail : List OrientedBF4Link)
    (hphysical : ∀ e, e ∈ tail → e.link ∈ boundaryCompleteSlabLinks extent)
    (habsent : ∀ e, e ∈ tail → e.link ≠ link) (stage : Nat) :
    let p := character extent (⟨link, false⟩ :: tail) 1
    let m := finiteValue w hw0 hw1 extent ids hids p stage
    starRatio w*(1+m*m) ≤ finiteValue w hw0 hw1 extent ids hids (polyMul p p) stage + -(m*m) := by
  let p := character extent (⟨link, false⟩ :: tail) 1
  have hm := normalizedMoment_finiteValue hw0 hw1 extent ids hids p stage
  have hs := normalizedMoment_finiteValue hw0 hw1 extent ids hids (polyMul p p) stage
  have hlhs := Q'.mul_eqv_congr_left (starRatio w) _ _
    (Q'.add_eqv_congr' (Q'.eqv_refl 1) (qmul hm hm))
  have hrhs := Q'.add_eqv_congr' hs (Q'.neg_eqv_congr _ _ (qmul hm hm))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hlhs)
    (Q'.le_trans' _ _ _
      (normalizedVariance_floor hw0 hw1 (headCutoff w+stage) extent (Nat.le_add_right _ _)
        ids hids hnodup link hl tail hphysical habsent)
      (Q'.le_of_eqv hrhs))

/-- In particular the SAME finite selected-action variance is strictly bounded
below at each fixed nome, independently of the physical face-list size. -/
theorem finiteValue_variance_floor {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (hnodup : ids.Nodup)
    (link : Z4Link) (hl : link ∈ boundaryCompleteSlabLinks extent)
    (tail : List OrientedBF4Link)
    (hphysical : ∀ e, e ∈ tail → e.link ∈ boundaryCompleteSlabLinks extent)
    (habsent : ∀ e, e ∈ tail → e.link ≠ link) (stage : Nat) :
    let p := character extent (⟨link, false⟩ :: tail) 1
    let m := finiteValue w hw0 hw1 extent ids hids p stage
    starRatio w ≤ finiteValue w hw0 hw1 extent ids hids (polyMul p p) stage + -(m*m) := by
  let m := finiteValue w hw0 hw1 extent ids hids (character extent (⟨link, false⟩ :: tail) 1) stage
  have hm : starRatio w ≤ starRatio w*(1+m*m) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_one_eqv _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.add_le_self_of_nonneg 1 _ (SumOfSquares.q_mul_self_nonneg m))
        (Q'.le_of_lt (starRatio_positive hw0 hw1)))
  exact Q'.le_trans' _ _ _ hm
    (finiteValue_variance_floor_with_mean hw0 hw1 extent ids hids hnodup link hl tail hphysical habsent stage)

#print axioms shifted_square_floor
#print axioms normalizedVariance_floor
#print axioms finiteValue_variance_floor_with_mean
#print axioms finiteValue_variance_floor

end YMGap.Continuum.BF4ExactSlabWilsonWordVariance
