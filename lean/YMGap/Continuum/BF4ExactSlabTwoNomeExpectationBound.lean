/-
# Coupling comparison of the EXISTING cutoff-removed original expectations

One explicit common cutoff exceeds the positive-head thresholds at both
nomes. The constructed finite coupling path compares actual normalized
moments there, with a linear face-count cost. Passing those same streams to
their pre-existing CReal expectations preserves that cap exactly.

No new state or convergence premise is introduced. This is all-nome,
finite-volume control; the face-count and W-dependent cost remain explicit.
The intended next consumer localizes to a retained finite window using the
original boundary-decay estimate rather than ignoring the exterior cost.
-/
import YMGap.Continuum.BF4ExactSlabFiniteCouplingPath
import YMGap.Continuum.BF4ExactSlabCommonCutoffExpectations

namespace YMGap.Continuum.BF4ExactSlabTwoNomeExpectationBound

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

def commonCutoff (u v : Q') : Nat := max (headCutoff u) (headCutoff v)
def finiteSetCap (W u v c : Q') (ids : List Nat) : Q' :=
  Q'.ofNat ids.length * (2*c*relativeVariation W u v)

private theorem one_positive (extent : Nat) : (0 : Q') < quaternionHaar (blocks extent) polyOne :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.ge_of_eqv (QPolyHaarPositiveSubstitution.haar_one _))

/-- Literal common-cutoff normalized values, pinned to the finite path's
original Haar moments with the unit spectator (not to a surrogate model). -/
theorem commonValue_weighted_pin {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat) (hi : ∀ i, i ∈ ids → i ∈ slabPhysicalFaceEdges extent)
    (p : RatPoly) (K0 n : Nat) (hK0 : headCutoff w ≤ K0) :
    commonValue w hw0 hw1 extent ids hi p K0 n ≈
      weightedValue hw0 hw1 (K0+n) extent (Nat.le_trans hK0 (Nat.le_add_right _ _)) ids hi
        (Certificate.one _) (one_positive extent) p := by
  have hZ := Q'.pos_of_lt_of_le (partitionFloor_pos hw0 hw1 ids)
    (partition_floor hw0 hw1 extent ids hi (K0+n) (Nat.le_trans hK0 (Nat.le_add_right _ _)))
  have hp : weightedValue hw0 hw1 (K0+n) extent (Nat.le_trans hK0 (Nat.le_add_right _ _)) ids hi
      (Certificate.one _) (one_positive extent) p ≈
      normalizedMoment (blocks extent) (polynomialProduct (faceHeatPolynomial w (K0+n) extent) ids) p hZ :=
    normalizedMoment_congr _ _ (RatPolyCoeffEqv.one_mul _) (RatPolyCoeffEqv.refl _)
  have hm : normalizedMoment (blocks extent) (polynomialProduct (faceHeatPolynomial w (K0+n) extent) ids) p hZ ≈
      numerator w (blocks extent) extent ids p (K0+n) *
        Q'.recipPos (heatProductHaar w (blocks extent) extent ids (K0+n)) hZ :=
    Q'.mul_eqv_congr_right _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ p))
  exact Q'.eqv_trans _ _ _ (commonValue_formula w hw0 hw1 extent ids hi p K0 n hK0)
    (Q'.eqv_symm (Q'.eqv_trans _ _ _ hp hm))

variable {u v W : Q'} (hu0 : (0 : Q') < u) (huv : u ≤ v) (hvW : v ≤ W) (hW1 : W < (1 : Q'))
  (extent : Nat) (ids : List Nat) (hi : ∀ i, i ∈ ids → i ∈ slabPhysicalFaceEdges extent)
  {p : RatPoly} {c : Q'} (P : Interval (blocks extent) p c)

local notation "hv0" => Q'.pos_of_lt_of_le hu0 huv
local notation "hv1" => Q'.lt_of_le_of_lt hvW hW1
local notation "hu1" => Q'.lt_of_le_of_lt huv hv1

include hu0 huv hvW hW1 hi P in
theorem commonValue_difference_bound (n : Nat) :
    Q'.abs (commonValue v hv0 hv1 extent ids hi p (commonCutoff u v) n +
      -(commonValue u hu0 hu1 extent ids hi p (commonCutoff u v) n)) ≤ finiteSetCap W u v c ids := by
  have hKu : headCutoff u ≤ commonCutoff u v := Nat.le_max_left _ _
  have hKv : headCutoff v ≤ commonCutoff u v := Nat.le_max_right _ _
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr'
    (commonValue_weighted_pin hv0 hv1 extent ids hi p _ n hKv)
    (Q'.neg_eqv_congr _ _ (commonValue_weighted_pin hu0 hu1 extent ids hi p _ n hKu)))))
    (weighted_difference_bound hu0 huv hvW hW1 (commonCutoff u v+n) extent
      (Nat.le_trans hKu (Nat.le_add_right _ _)) (Nat.le_trans hKv (Nat.le_add_right _ _)) ids hi
      (Certificate.one _) (one_positive extent) P)

include hu0 huv hvW hW1 hi P in
/-- Actual pre-existing CReal states at DIFFERENT nomes, same observable,
same selected physical faces. The representation cutoff is fully removed. -/
theorem expectation_difference_bound :
    leEv (CReal.abs (CReal.sub (expectation v hv0 hv1 extent ids hi p)
      (expectation u hu0 hu1 extent ids hi p))) (ofQ' (finiteSetCap W u v c ids)) := by
  have h := convergesTo_abs (convergesTo_add
    (commonValue_converges v hv0 hv1 extent ids hi p (commonCutoff u v))
    (TrigAddCReal.convergesTo_neg (commonValue_converges u hu0 hu1 extent ids hi p (commonCutoff u v))))
  have hc : ConvergesTo (fun n => ofQ' (Q'.abs
      (commonValue v hv0 hv1 extent ids hi p (commonCutoff u v) n +
        -(commonValue u hu0 hu1 extent ids hi p (commonCutoff u v) n))))
      (CReal.abs (CReal.sub (expectation v hv0 hv1 extent ids hi p)
        (expectation u hu0 hu1 extent ids hi p))) := by
    refine TrigAddCReal.convergesTo_congr_seq ?_ h
    intro n
    exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
  apply leEv_of_ofQ'_limit_le hc (convergesTo_const _)
  intro epsilon he
  exact ⟨0, fun n _ => Q'.le_trans' _ _ _
    (commonValue_difference_bound hu0 huv hvW hW1 extent ids hi P n)
    (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he))⟩

end YMGap.Continuum.BF4ExactSlabTwoNomeExpectationBound

#print axioms YMGap.Continuum.BF4ExactSlabTwoNomeExpectationBound.commonCutoff
#print axioms YMGap.Continuum.BF4ExactSlabTwoNomeExpectationBound.finiteSetCap
#print axioms YMGap.Continuum.BF4ExactSlabTwoNomeExpectationBound.commonValue_weighted_pin
#print axioms YMGap.Continuum.BF4ExactSlabTwoNomeExpectationBound.commonValue_difference_bound
#print axioms YMGap.Continuum.BF4ExactSlabTwoNomeExpectationBound.expectation_difference_bound
