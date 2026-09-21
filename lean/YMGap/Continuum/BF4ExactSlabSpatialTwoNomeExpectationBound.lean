/-
# Cutoff-removed expectation comparison after the volume-free path bound

The common-cutoff streams are the existing finite-volume states.  The new
summed coupling path supplies their full-slab difference bound, so the same
pre-existing CReal expectations inherit it without introducing a new limit.
-/

import YMGap.Continuum.BF4ExactSlabSummedCouplingPath
import YMGap.Continuum.BF4ExactSlabTwoNomeExpectationBound

namespace YMGap.Continuum.BF4ExactSlabSpatialTwoNomeExpectationBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetReciprocal
open YMGap.Continuum.BF4ExactSlabAllNomeFaceSetExpectation
open YMGap.Continuum.BF4ExactSlabOneFaceCouplingStability (relativeVariation)
open YMGap.Continuum.BF4ExactSlabFiniteCouplingPath
open YMGap.Continuum.BF4ExactSlabCommonCutoffExpectations
open YMGap.Continuum.BF4ExactSlabTwoNomeExpectationBound
open YMGap.Continuum.BF4ExactSlabSummedCouplingPath
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarNormalizedMomentCongruence
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv
local notation:max "blocks" extent:max => List.length (boundaryCompleteSlabLinks extent)

variable {u v W : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v) (hvW : v ≤ W) (hW1 : W < (1 : Q'))
  (hsmall : heatRatio W ≤ HalfPow.half) (hd : heatRemainderBound W < 1)
  (hs : entropyRate 625 (adjustedCoreRate W hd) < 1)

local notation "hv0" => Q'.pos_of_lt_of_le hu0 huv
local notation "hv1" => Q'.lt_of_le_of_lt hvW hW1
local notation "hu1" => Q'.lt_of_le_of_lt huv hv1

private theorem one_positive (extent : Nat) :
    (0 : Q') < quaternionHaar (blocks extent) polyOne :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv (QPolyHaarPositiveSubstitution.haar_one _))

private theorem commonValue_normalized_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat)
    (hi : ∀ i, i ∈ ids → i ∈ slabPhysicalFaceEdges extent)
    (p : RatPoly) (K0 n : Nat) (hK0 : headCutoff w ≤ K0) :
    commonValue w hw0 hw1 extent ids hi p K0 n ≈
      normalizedMoment (blocks extent)
        (polynomialProduct (faceHeatPolynomial w (K0+n) extent) ids) p
        (Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
          (partition_floor hw0 hw1 extent ids hi (K0+n)
            (Nat.le_trans hK0 (Nat.le_add_right _ _)))) := by
  let hZ := Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
    (partition_floor hw0 hw1 extent ids hi (K0+n)
      (Nat.le_trans hK0 (Nat.le_add_right _ _)))
  have hweight := commonValue_weighted_pin hw0 hw1 extent ids hi p K0 n hK0
  have hnorm : weightedValue hw0 hw1 (K0+n) extent
      (Nat.le_trans hK0 (Nat.le_add_right _ _)) ids hi
      (Certificate.one _) (one_positive extent) p ≈
      normalizedMoment (blocks extent)
        (polynomialProduct (faceHeatPolynomial w (K0+n) extent) ids) p hZ :=
    normalizedMoment_congr _ _ (RatPolyCoeffEqv.one_mul _) (RatPolyCoeffEqv.refl _)
  exact Q'.eqv_trans _ _ _ hweight hnorm

variable (extent : Nat)
local notation "fullIds" => slabPhysicalFaceEdges extent
local notation "fullPhys" => (fun id (hi : id ∈ slabPhysicalFaceEdges extent) => hi)

include hu0 huv hvW hW1 hsmall hd hs in
theorem commonValue_difference_bound (p : RatPoly) (c : Q')
    (P : Interval (blocks extent) p c) (left : List Z4Link) (carrier : ProbeCarrier left)
    (hp : LinkLocal extent left p) (n : Nat) :
    Q'.abs (commonValue v hv0 hv1 extent fullIds fullPhys p (commonCutoff u v) n +
      -(commonValue u hu0 hu1 extent fullIds fullPhys p (commonCutoff u v) n)) ≤
      pathBudget hu0 huv hvW hd hs carrier c 0 := by
  have hKu : headCutoff u ≤ commonCutoff u v := Nat.le_max_left _ _
  have hKv : headCutoff v ≤ commonCutoff u v := Nat.le_max_right _ _
  have hpinV := commonValue_normalized_pin hv0 hv1 extent fullIds fullPhys p _ n hKv
  have hpinU := commonValue_normalized_pin hu0 hu1 extent fullIds fullPhys p _ n hKu
  have hfinite := full_slab_original_change_bound hu0 huv hvW hW1 hsmall hd hs
    (commonCutoff u v + n) extent
    (Nat.le_trans hKu (Nat.le_add_right _ _))
    (Nat.le_trans hKv (Nat.le_add_right _ _)) P left carrier hp
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr'
      hpinV (Q'.neg_eqv_congr _ _ hpinU)))) hfinite

include hu0 huv hvW hW1 hsmall hd hs in
theorem expectation_difference_bound (p : RatPoly) (c : Q')
    (P : Interval (blocks extent) p c) (left : List Z4Link) (carrier : ProbeCarrier left)
    (hp : LinkLocal extent left p) :
    leEv (CReal.abs (CReal.sub (expectation v hv0 hv1 extent fullIds fullPhys p)
      (expectation u hu0 hu1 extent fullIds fullPhys p)))
      (ofQ' (pathBudget hu0 huv hvW hd hs carrier c 0)) := by
  have h := convergesTo_abs (convergesTo_add
    (commonValue_converges v hv0 hv1 extent fullIds fullPhys p (commonCutoff u v))
    (TrigAddCReal.convergesTo_neg
      (commonValue_converges u hu0 hu1 extent fullIds fullPhys p (commonCutoff u v))))
  have hc : ConvergesTo (fun n => ofQ' (Q'.abs
      (commonValue v hv0 hv1 extent fullIds fullPhys p (commonCutoff u v) n +
        -(commonValue u hu0 hu1 extent fullIds fullPhys p (commonCutoff u v) n))))
      (CReal.abs (CReal.sub (expectation v hv0 hv1 extent fullIds fullPhys p)
        (expectation u hu0 hu1 extent fullIds fullPhys p))) := by
    refine TrigAddCReal.convergesTo_congr_seq ?_ h
    intro n
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  apply leEv_of_ofQ'_limit_le hc (convergesTo_const _)
  intro epsilon he
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _
    (commonValue_difference_bound hu0 huv hvW hW1 hsmall hd hs extent p c P left carrier hp n)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

end YMGap.Continuum.BF4ExactSlabSpatialTwoNomeExpectationBound

#print axioms YMGap.Continuum.BF4ExactSlabSpatialTwoNomeExpectationBound.commonValue_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabSpatialTwoNomeExpectationBound.expectation_difference_bound
