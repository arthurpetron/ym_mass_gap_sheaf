/-
# Original fixed-source moments at the zero heat-step endpoint

The moment remains H[(a*p)*P(a)] at the ACTUAL nome and cutoff. Its
zero-step endpoint is H[(a*p)*a], not an interacting variance substituted
at a positive step. A computable radius controls every cutoff satisfying
the original sufficient-cutoff guard. Signed insertions are allowed.

The source is fixed before the nome varies. These bounds do NOT supply a
modulus for changing terminal sources or a physical continuum limit.
-/

import YMGap.Continuum.SU2QuaternionProductHeatSourceSlope

namespace YMGap.Continuum.SU2QuaternionProductHeatSourceMomentLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionProductHeatProjectedSourceEnergy
open YMGap.Continuum.SU2QuaternionCyclicModeTaylor
open YMGap.Continuum.SU2HeatCutoffCasimirBound

local infix:50 " ≈ " => Q'.eqv

def zeroStepMoment (tail : Nat) (a p : RatPoly) : Q' :=
  quaternionHaar (tail+1) (polyMul (polyMul a p) a)

/-- Explicit first-order plus remainder cap; no positivity of p is needed. -/
def momentCap (tail : Nat) (a p : RatPoly) : Q' :=
  (1 : Q') + Q'.abs (pairCasimir tail a (polyMul a p)) +
    Q'.abs (pairBudget tail a (polyMul a p))

theorem momentCap_positive (tail : Nat) (a p : RatPoly) :
    (0 : Q') < momentCap tail a p :=
  Q'.pos_add_nonneg (Q'.pos_add_nonneg (by decide) (Q'.abs_nonneg _))
    (Q'.abs_nonneg _)

def momentRadius (tail : Nat) (a p : RatPoly) (e : Q') : Q' :=
  e*Q'.recipPos (momentCap tail a p) (momentCap_positive tail a p)

theorem momentRadius_positive (tail : Nat) (a p : RatPoly) (e : Q')
    (he : (0 : Q') < e) : (0 : Q') < momentRadius tail a p e :=
  Q'.mul_pos he (Q'.recipPos_pos _ _)

private theorem neg_bound {r c : Q'} (h : -r ≤ c) : -c ≤ r :=
  Q'.le_trans' _ _ _ (Q'.neg_le_neg h) (Q'.le_of_eqv (Q'.neg_neg_eqv _))

private theorem radius_mul_cap (tail : Nat) (a p : RatPoly) (e : Q') :
    momentRadius tail a p e * momentCap tail a p ≈ e :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _)
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left e _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.mul_recipPos_eqv _ _)))
      (Q'.mul_one_eqv e))

/-- Two-sided bound around the actual q-squared endpoint. All nome/cutoff
parameters and the fixed source are explicit in the statement. -/
theorem sourceMoment_endpoint_interval (tail : Nat) {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (K : Nat)
    (hK : sufficientCutoff w ≤ K) (a p : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a) :
    (zeroStepMoment tail a p - ((1 : Q')-w)*momentCap tail a p ≤
      sourceMoment (tail+1) w K (List.range (tail+1)) a p) ∧
    (sourceMoment (tail+1) w K (List.range (tail+1)) a p ≤
      zeroStepMoment tail a p + ((1 : Q')-w)*momentCap tail a p) := by
  let h := (1 : Q')-w
  let C := pairCasimir tail a (polyMul a p)
  let B := pairBudget tail a (polyMul a p)
  let R := pairRemainder tail w K a (polyMul a p)
  let cap := momentCap tail a p
  have hh : (0 : Q') ≤ h := Q'.sub_nonneg_of_le (Q'.le_of_lt hw1)
  have hle : h ≤ (1 : Q') := Q'.le_trans' _ _ _
    (Q'.add_le_add_left 1 _ _ (Q'.neg_le_neg hw0))
    (Q'.le_of_eqv (by decide : (1 : Q')+0 ≈ 1))
  have hsq : h*h ≤ h := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ h hle hh)
    (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have hbudget : (h*h)*B ≤ h*Q'.abs B := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ (h*h) (Q'.le_abs_self B)
      (Q'.mul_nonneg _ _ hh hh))
    (Q'.mul_le_mul_of_nonneg_right _ _ (Q'.abs B) hsq (Q'.abs_nonneg B))
  have hrU : R ≤ h*Q'.abs B := Q'.le_trans' _ _ _
    (pairRemainder_le_quadratic tail hw0 hw1 K hK a (polyMul a p)) hbudget
  have hrL : -(h*Q'.abs B) ≤ R := neg_bound (Q'.le_trans' _ _ _
    (neg_pairRemainder_le_quadratic tail hw0 hw1 K hK a (polyMul a p)) hbudget)
  have hcU : -(h*C) ≤ h*Q'.abs C := Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.mul_neg_eqv h C))
    (Q'.mul_le_mul_of_nonneg_left _ _ h (Q'.neg_le_abs C) hh)
  have hcL : -(h*Q'.abs C) ≤ -(h*C) :=
    Q'.neg_le_neg (Q'.mul_le_mul_of_nonneg_left _ _ h (Q'.le_abs_self C) hh)
  have hcap0 : Q'.abs C+Q'.abs B ≤ cap := Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (Q'.abs C+Q'.abs B) 1 (by decide))
    (Q'.le_of_eqv (poly_identity_of_normal_eq
      (.add (.add (.var 0) (.var 1)) (.const 1))
      (.add (.add (.const 1) (.var 0)) (.var 1)) (by decide)
      (fun | 0 => Q'.abs C | _ => Q'.abs B)))
  have hcap := Q'.mul_le_mul_of_nonneg_left _ _ h hcap0 hh
  have hsumU : -(h*C)+R ≤ h*cap := Q'.le_trans' _ _ _
    (Q'.add_le_add hcU hrU)
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.mul_add_eqv h _ _)) hcap)
  have hsumL : -(h*cap) ≤ -(h*C)+R := Q'.le_trans' _ _ _
    (Q'.neg_le_neg hcap)
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.neg_eqv_congr _ _ (Q'.mul_add_eqv h _ _)) (Q'.neg_add_eqv _ _)))
      (Q'.add_le_add hcL hrL))
  have ht := productPair_taylor tail w K a (polyMul a p) ha
  have regroup : zeroStepMoment tail a p + -(h*C)+R ≈
      zeroStepMoment tail a p + (-(h*C)+R) := Q'.add_assoc_eqv _ _ _
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left (zeroStepMoment tail a p) _ _ hsumL)
      (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ ht regroup))
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ ht regroup))
      (Q'.add_le_add_left (zeroStepMoment tail a p) _ _ hsumU)

/-- A returned radius for every signed original fixed-source moment. -/
def momentCertificate (tail : Nat) (a p : RatPoly)
    (ha : SupportedQuaternionBlocks (tail+1) a) (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ (w : Q'), (0 : Q') ≤ w → w < (1 : Q') → (1 : Q')-w ≤ r →
        ∀ K : Nat, sufficientCutoff w ≤ K →
          (zeroStepMoment tail a p-e ≤ sourceMoment (tail+1) w K (List.range (tail+1)) a p) ∧
          (sourceMoment (tail+1) w K (List.range (tail+1)) a p ≤ zeroStepMoment tail a p+e)) := by
  refine ⟨momentRadius tail a p e,momentRadius_positive tail a p e he,?_⟩
  intro w hw0 hw1 hs K hK
  have hc : ((1 : Q')-w)*momentCap tail a p ≤ e := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ (momentCap tail a p) hs
      (Q'.le_of_lt (momentCap_positive tail a p)))
    (Q'.le_of_eqv (radius_mul_cap tail a p e))
  have hi := sourceMoment_endpoint_interval tail hw0 hw1 K hK a p ha
  exact ⟨Q'.le_trans' _ _ _
      (Q'.add_le_add_left (zeroStepMoment tail a p) _ _ (Q'.neg_le_neg hc)) hi.1,
    Q'.le_trans' _ _ _ hi.2 (Q'.add_le_add_left (zeroStepMoment tail a p) _ _ hc)⟩

#print axioms momentCap_positive
#print axioms momentRadius
#print axioms momentRadius_positive
#print axioms sourceMoment_endpoint_interval
#print axioms momentCertificate

end YMGap.Continuum.SU2QuaternionProductHeatSourceMomentLimit
