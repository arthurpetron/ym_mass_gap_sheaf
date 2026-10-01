/-
# Two-sided weak-step slope of the ORIGINAL source energy

For a FIXED supplied polynomial source and observable, the existing signed
Taylor remainders give both sides of the first-order estimate. A computed
radius controls the energy divided by the heat step, without performing
that division. The actual sufficient-cutoff guard remains in every bound.

The coefficient is the original source-squared angular energy, NOT the
interacting variance. Its radius depends on the source and observable;
there is no uniform changing-source, terminal-depth, or physical-scale claim.
-/

import YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.SU2QuaternionProductHeatSourceSlope

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionProductHeatSourceTaylor
open YMGap.Continuum.SU2QuaternionProductHeatAngularTaylor
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2HeatCutoffCasimirBound

local infix:50 " ≈ " => Q'.eqv

/-- The lower companion retains BOTH signed remainder budgets. -/
theorem sourceEnergy_ge_firstOrder_sub_quadratic (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) :
    ((1 : Q')-w)*sourceFirstOrder tail a f -
        (((1 : Q')-w)*((1 : Q')-w))*sourceTaylorBudget tail a f ≤
      sourceEnergy (tail+1) w K (List.range (tail+1)) a f := by
  let h := (1 : Q')-w
  let r1 := pairRemainder tail w K a (polyMul a (polyMul f f))
  let r2 := pairRemainder tail w K (polyMul a f) (polyMul a f)
  have hneg := Q'.add_le_add
    (neg_pairRemainder_le_quadratic tail hw0 hw1 K hK a (polyMul a (polyMul f f)))
    (pairRemainder_le_quadratic tail hw0 hw1 K hK (polyMul a f) (polyMul a f))
  have hshape : -(r1-r2) ≈ -r1+r2 :=
    poly_identity_of_normal_eq (.neg (.add (.var 0) (.neg (.var 1))))
      (.add (.neg (.var 0)) (.var 1)) (by decide) (fun | 0 => r1 | _ => r2)
  have hbound : -(r1-r2) ≤ (h*h)*sourceTaylorBudget tail a f :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hshape)
      (Q'.le_trans' _ _ _ hneg
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_add_eqv (h*h) _ _))))
  have hrem : -((h*h)*sourceTaylorBudget tail a f) ≤ r1-r2 :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hbound)
      (Q'.le_of_eqv (Q'.neg_neg_eqv _))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left (h*sourceFirstOrder tail a f) _ _ hrem)
    (Q'.ge_of_eqv (sourceEnergy_taylor tail w K a f ha hf))

/-- A strictly positive computable cap, with all source dependence explicit. -/
def slopeCap (tail : Nat) (a f : RatPoly) : Q' :=
  (1 : Q') + Q'.abs (sourceTaylorBudget tail a f)

theorem slopeCap_positive (tail : Nat) (a f : RatPoly) :
    (0 : Q') < slopeCap tail a f :=
  Q'.pos_add_nonneg (by decide) (Q'.abs_nonneg _)

theorem sourceTaylorBudget_le_slopeCap (tail : Nat) (a f : RatPoly) :
    sourceTaylorBudget tail a f ≤ slopeCap tail a f :=
  Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    (Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (Q'.abs (sourceTaylorBudget tail a f)) 1 (by decide))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- The numerator is the requested precision, not an opaque rate. -/
def slopeRadius (tail : Nat) (a f : RatPoly) (e : Q') : Q' :=
  e * Q'.recipPos (slopeCap tail a f) (slopeCap_positive tail a f)

theorem slopeRadius_positive (tail : Nat) (a f : RatPoly) (e : Q')
    (he : (0 : Q') < e) : (0 : Q') < slopeRadius tail a f e :=
  Q'.mul_pos he (Q'.recipPos_pos _ _)

private theorem radius_mul_cap (tail : Nat) (a f : RatPoly) (e : Q') :
    slopeRadius tail a f e * slopeCap tail a f ≈ e :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left e _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
          (Q'.mul_recipPos_eqv _ _)))
      (Q'.mul_one_eqv e))

/-- Uniform over every cutoff above its ACTUAL sufficient-cutoff guard,
but only for this fixed supplied source and observable. -/
theorem sourceEnergy_slope_interval (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) (e : Q')
    (hstep : (1 : Q')-w ≤ slopeRadius tail a f e) :
    (((1 : Q')-w)*(weightedAngularEnergy tail a f-e) ≤
      sourceEnergy (tail+1) w K (List.range (tail+1)) a f) ∧
    (sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
      ((1 : Q')-w)*(weightedAngularEnergy tail a f+e)) := by
  let h := (1 : Q')-w
  let A := weightedAngularEnergy tail a f
  let B := sourceTaylorBudget tail a f
  have hh : (0 : Q') ≤ h := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hcap : h*slopeCap tail a f ≤ e :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ (slopeCap tail a f) hstep
        (Q'.le_of_lt (slopeCap_positive tail a f)))
      (Q'.le_of_eqv (radius_mul_cap tail a f e))
  have hB : h*B ≤ e := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ h (sourceTaylorBudget_le_slopeCap tail a f) hh) hcap
  have hquad : (h*h)*B ≤ h*e :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _))
      (Q'.mul_le_mul_of_nonneg_left _ _ h hB hh)
  have hfirst := sourceFirstOrder_eq_weightedAngularEnergy tail a f ha hf
  have hl := sourceEnergy_ge_firstOrder_sub_quadratic tail hw0 hw1 K hK a f ha hf
  have hu := sourceEnergy_le_firstOrder_add_quadratic tail hw0 hw1 K hK a f ha hf
  have hlow : h*A-(h*h)*B ≤ sourceEnergy (tail+1) w K (List.range (tail+1)) a f :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left h _ _ hfirst) (Q'.eqv_refl _))) hl
  have hupp : sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤ h*A+(h*h)*B :=
    Q'.le_trans' _ _ _ hu
      (Q'.le_of_eqv (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left h _ _ hfirst) (Q'.eqv_refl _)))
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ _ _)
        (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.mul_neg_eqv h e))))
      (Q'.le_trans' _ _ _
        (Q'.add_le_add_left (h*A) _ _ (Q'.neg_le_neg hquad)) hlow)
  · exact Q'.le_trans' _ _ _ hupp
      (Q'.le_trans' _ _ _ (Q'.add_le_add_left (h*A) _ _ hquad)
        (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_add_eqv h A e))))

/-- A constructive fixed-source first-order certificate; no choice of a
cutoff, source, physical trajectory or variance is concealed in Prop. -/
def slopeCertificate (tail : Nat) (a f : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a)
    (hf : SupportedQuaternionBlocks (tail+1) f) (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ (w : Q'), (0 : Q') ≤ w → w < (1 : Q') → (1 : Q')-w ≤ r →
        ∀ K : Nat, sufficientCutoff w ≤ K →
          (((1 : Q')-w)*(weightedAngularEnergy tail a f-e) ≤
            sourceEnergy (tail+1) w K (List.range (tail+1)) a f) ∧
          (sourceEnergy (tail+1) w K (List.range (tail+1)) a f ≤
            ((1 : Q')-w)*(weightedAngularEnergy tail a f+e))) :=
  ⟨slopeRadius tail a f e,slopeRadius_positive tail a f e he,
    fun w hw0 hw1 hs K hK => sourceEnergy_slope_interval tail hw0 hw1 K hK a f ha hf e hs⟩

#print axioms sourceEnergy_ge_firstOrder_sub_quadratic
#print axioms slopeCap
#print axioms slopeCap_positive
#print axioms sourceTaylorBudget_le_slopeCap
#print axioms slopeRadius
#print axioms slopeRadius_positive
#print axioms sourceEnergy_slope_interval
#print axioms slopeCertificate

end YMGap.Continuum.SU2QuaternionProductHeatSourceSlope
