/-
# Positive-rational represented Neumann limit on the original Wilson sector

Every partial iterate retains its original time-range witness. For each
positive rational t, the checked scaled physical reflection supplies the
same strict squared-distance factor 1/4. Its input-dependent geometric
modulus and fixed-point equation remain on the SAME original carrier.
No scaled Cayley product limit or physical-time group is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSScaledReflection
import YMGap.Continuum.BF4WilsonAllNomeResolventNeumannLimit
import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation

namespace YMGap.Continuum.BF4WilsonAllNomeScaledResolventNeumannLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear (ofState bondValue_ofState)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime (bondValue_inner bondValue_distance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSScaledReflection
  (reflection neumannStep square_complement_bound neumannStep_distance_bound)
open YMGap.Continuum.BF4WilsonAllNomeResolventNeumannLimit (scaleState subState)
open YMGap.Continuum.BF4WilsonAllNomeSectorNeumannPartial (affine_dist)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}
  (t : Q') (ht : (0 : Q') < t)

local notation "V" => Completion hw0 hw1 width
local notation "S" => State hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "Scale" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "P" => distanceData hw0 hw1 (width := width)
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The old sector resolvent state at 1/t, multiplied by 1/t. Both
original range witnesses remain constructed data. -/
def scaledResolventState (x : S) : S :=
  scaleState hw0 hw1 (BF4WilsonAllNomeBondOSScaledResolvent.reciprocal t ht)
    (BF4WilsonAllNomeSectorResolvent.state hw0 hw1
      (BF4WilsonAllNomeBondOSScaledResolvent.reciprocal t ht)
      (BF4WilsonAllNomeBondOSScaledResolvent.reciprocal_pos t ht) x)

theorem scaledResolventState_pin (x : S) :
    ofState hw0 hw1 (scaledResolventState hw0 hw1 t ht x) =
      BF4WilsonAllNomeBondOSScaledResolvent.resolvent hw0 hw1 t ht
        (ofState hw0 hw1 x) := by
  apply BF4WilsonAllNomeBondOSTime.bondValue_injective hw0 hw1
  rw [bondValue_ofState,
    BF4WilsonAllNomeBondOSScaledResolvent.resolvent_value,
    BF4WilsonAllNomeBondOSLinear.bondValue_smul,
    BF4WilsonAllNomeBondOSResolvent.bondValue_resolvent,
    bondValue_ofState]
  rfl

private theorem scaleState_pin (a : Q') (x : S) :
    ofState hw0 hw1 (scaleState hw0 hw1 a x) =
      BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 a (ofState hw0 hw1 x) := by
  apply BF4WilsonAllNomeBondOSTime.bondValue_injective hw0 hw1
  rw [bondValue_ofState,BF4WilsonAllNomeBondOSLinear.bondValue_smul,bondValue_ofState]
  rfl

private theorem subState_pin (x y : S) :
    ofState hw0 hw1 (subState hw0 hw1 x y) =
      BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
        (ofState hw0 hw1 x) (ofState hw0 hw1 y) := by
  apply BF4WilsonAllNomeBondOSTime.bondValue_injective hw0 hw1
  rw [bondValue_ofState,BF4WilsonAllNomeBondOSLinear.bondValue_sub,
    bondValue_ofState,bondValue_ofState]
  rfl

def reflectionState (x : S) : S := subState hw0 hw1
  (scaleState hw0 hw1 2 (scaledResolventState hw0 hw1 t ht x)) x

def complementState (x : S) : S := subState hw0 hw1 x
  (reflectionState hw0 hw1 t ht (reflectionState hw0 hw1 t ht x))

def stepState (x : S) : S :=
  scaleState hw0 hw1 HalfPow.half (complementState hw0 hw1 t ht x)

theorem reflectionState_pin (x : S) :
    ofState hw0 hw1 (reflectionState hw0 hw1 t ht x) =
      reflection hw0 hw1 t ht (ofState hw0 hw1 x) := by
  unfold reflectionState reflection
  rw [subState_pin,scaleState_pin,scaledResolventState_pin]

private theorem complementState_pin (x : S) :
    ofState hw0 hw1 (complementState hw0 hw1 t ht x) =
      BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 (ofState hw0 hw1 x)
        (reflection hw0 hw1 t ht
          (reflection hw0 hw1 t ht (ofState hw0 hw1 x))) := by
  unfold complementState
  rw [subState_pin,reflectionState_pin,reflectionState_pin]

/-- The witnessed state iteration pins exactly to the scaled physical
Neumann step, with no choice of quotient representative. -/
theorem stepState_pin (x : S) :
    ofState hw0 hw1 (stepState hw0 hw1 t ht x) =
      neumannStep hw0 hw1 t ht (ofState hw0 hw1 x) := by
  unfold stepState BF4WilsonAllNomeBondOSScaledReflection.neumannStep
  rw [scaleState_pin,complementState_pin]

theorem complement_norm_bound (x : S) :
    RCle (B (complementState hw0 hw1 t ht x).val (complementState hw0 hw1 t ht x).val)
      (B x.val x.val) := by
  have h := square_complement_bound hw0 hw1 t ht (ofState hw0 hw1 x)
  rw [← complementState_pin, bondValue_inner, bondValue_inner,
    bondValue_ofState, bondValue_ofState] at h
  exact h

theorem step_distance_bound (x y : S) :
    RCle (dist (stepState hw0 hw1 t ht x).val (stepState hw0 hw1 t ht y).val)
      (RCscale (HalfPow.half*HalfPow.half) (dist x.val y.val)) := by
  have h := neumannStep_distance_bound hw0 hw1 t ht (ofState hw0 hw1 x) (ofState hw0 hw1 y)
  rw [← stepState_pin, ← stepState_pin, bondValue_distance, bondValue_distance,
    bondValue_ofState, bondValue_ofState, bondValue_ofState, bondValue_ofState] at h
  exact h

theorem step_congr {x y : S} (h : x.val = y.val) :
    (stepState hw0 hw1 t ht x).val = (stepState hw0 hw1 t ht y).val := by
  have hs := congrArg (fun a => BF4WilsonAllNomeBondOSTime.bondValue hw0 hw1
    (neumannStep hw0 hw1 t ht a)) (BF4WilsonAllNomeBondOSLinear.ofState_congr hw0 hw1 h)
  dsimp only at hs
  rw [← stepState_pin, ← stepState_pin, bondValue_ofState, bondValue_ofState] at hs
  exact hs

def neumannPartial (x : S) : Nat → S
  | 0 => BF4WilsonAllNomeTimeSector.zero hw0 hw1
  | n+1 => BF4WilsonAllNomeTimeSector.add hw0 hw1
      (scaleState hw0 hw1 HalfPow.half x) (stepState hw0 hw1 t ht (neumannPartial x n))

theorem partial_succ (x : S) (n : Nat) :
    (neumannPartial hw0 hw1 t ht x (n+1)).val =
      A (Scale HalfPow.half x.val) (stepState hw0 hw1 t ht (neumannPartial hw0 hw1 t ht x n)).val := rfl

private theorem half_norm_sum (a : RC) :
    RCadd (RCscale HalfPow.half a) (RCscale HalfPow.half a) = a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => ExpNeg.two_halves (X.approx n)))

theorem partial_norm_bound (x : S) (n : Nat) :
    RCle (B (neumannPartial hw0 hw1 t ht x n).val (neumannPartial hw0 hw1 t ht x n).val) (B x.val x.val) := by
  induction n with
  | zero =>
      rw [neumannPartial, BF4WilsonAllNomeTimeSector.zero, completedInner_zero_left]
      exact completedInner_nonnegative hw0 hw1 x.val
  | succ n ih =>
      have hc := BF4WilsonAllNomeRootResolventPartial.convex_norm_le hw0 hw1
        HalfPow.half (by decide) (by decide) x.val
        (complementState hw0 hw1 t ht (neumannPartial hw0 hw1 t ht x n)).val
      rw [completedSmul_congr hw0 hw1 (by decide : Q'.eqv (1-HalfPow.half) HalfPow.half)] at hc
      have hl := RCle_trans (complement_norm_bound hw0 hw1 t ht _) ih
      have h := RCle_trans hc (RCadd_le_add (RCle_refl _)
        (RCscale_mono (by decide) hl))
      rw [scale_congr (by decide : Q'.eqv (1-HalfPow.half) HalfPow.half), half_norm_sum] at h
      exact h

private theorem translate_dist (b u v : V) : dist (A b u) (A b v) = dist u v := by
  have h := affine_dist hw0 hw1 b 1 u v
  rw [completedSmul_one, completedSmul_one, scale_congr (by decide : Q'.eqv ((1 : Q')*1) 1),
    RCscale_one] at h
  exact h

theorem partial_step_bound (x : S) (m n : Nat) :
    RCle (dist (neumannPartial hw0 hw1 t ht x (m+1)).val (neumannPartial hw0 hw1 t ht x (n+1)).val)
      (RCscale (HalfPow.half*HalfPow.half)
        (dist (neumannPartial hw0 hw1 t ht x m).val (neumannPartial hw0 hw1 t ht x n).val)) := by
  rw [partial_succ, partial_succ, translate_dist]
  exact step_distance_bound hw0 hw1 t ht _ _

theorem partial_tail_bound (x : S) (n k : Nat) :
    RCle (dist (neumannPartial hw0 hw1 t ht x (n+k)).val (neumannPartial hw0 hw1 t ht x n).val)
      (RCscale (HalfPow.half^n*HalfPow.half^n) (B x.val x.val)) := by
  induction n with
  | zero =>
      rw [Nat.zero_add, neumannPartial, BF4WilsonAllNomeTimeSector.zero,
        dist_zero, Q'.pow_zero, scale_congr (by decide : Q'.eqv ((1 : Q')*1) 1), RCscale_one]
      exact partial_norm_bound hw0 hw1 t ht x k
  | succ n ih =>
      rw [show n+1+k = (n+k)+1 by omega]
      have h := RCle_trans (partial_step_bound hw0 hw1 t ht x (n+k) n)
        (RCscale_mono (by decide) ih)
      rw [RCscale_RCscale] at h
      have hp : Q'.eqv
          ((HalfPow.half*HalfPow.half)*(HalfPow.half^n*HalfPow.half^n))
          (HalfPow.half^(n+1)*HalfPow.half^(n+1)) := by
        rw [Q'.pow_succ]
        exact RingNormaliser.poly_identity_of_normal_eq
          (.mul (.mul (.var 0) (.var 0)) (.mul (.var 1) (.var 1)))
          (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
          (by decide) (fun | 0 => HalfPow.half | _ => HalfPow.half^n)
      rwa [scale_congr hp] at h

/-- Computed threshold from the input's stored original range representative. -/
def modulus (x : S) (epsilon : Q') : Nat :=
  geometricCutoff HalfPow.half (normCeiling PD (representative hw0 hw1 x.range)) epsilon

private theorem ordered_small (x : S) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m n : Nat) (hmn : m ≤ n) (hm : modulus hw0 hw1 x epsilon ≤ m) :
    RCle (dist (neumannPartial hw0 hw1 t ht x n).val (neumannPartial hw0 hw1 t ht x m).val) (rat epsilon) := by
  let X := representative hw0 hw1 x.range
  have h := partial_tail_bound hw0 hw1 t ht x m (n-m)
  rw [Nat.add_sub_of_le hmn] at h
  have hp0 := Q'.pow_nonneg HalfPow.half (by decide) m
  have hp1 := HKPos.pow_le_one (by decide : (0 : Q') ≤ HalfPow.half)
    (by decide : HalfPow.half ≤ (1 : Q')) m
  have hsq : HalfPow.half^m*HalfPow.half^m ≤ HalfPow.half^m := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hp1 hp0) (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have hnorm : RCle (B x.val x.val) (rat (normCeiling PD X)) := by
    rw [← representative_pin hw0 hw1 x.range]
    exact completedInner_diagonal_le_normCeiling PD X
  have hcap := RCle_trans h (RCscale_mono (Q'.mul_nonneg _ _ hp0 hp0) hnorm)
  have hs : RCscale (HalfPow.half^m*HalfPow.half^m) (rat (normCeiling PD X)) =
      rat ((HalfPow.half^m*HalfPow.half^m)*normCeiling PD X) :=
    Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
  rw [hs] at hcap
  exact RCle_trans hcap (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hsq (normCeiling_nonnegative PD X))
    (geometric_bound (by decide) (by decide) (normCeiling_nonnegative PD X) he m hm)))

def rows (x : S) : BF4WilsonAllNomeTimeSector.CauchySequence hw0 hw1 (width := width) where
  seq := neumannPartial hw0 hw1 t ht x
  modulus := modulus hw0 hw1 x
  bound := by
    intro epsilon he m n hm hn
    rcases Nat.le_total m n with hmn | hnm
    · rw [completedDist_symm]
      exact ordered_small hw0 hw1 t ht x epsilon he m n hmn hm
    · exact ordered_small hw0 hw1 t ht x epsilon he n m hnm hn

def normalized (x : S) : S := BF4WilsonAllNomeTimeSector.limit hw0 hw1 (rows hw0 hw1 t ht x)

def normalizedRate (x : S) : Q' → Nat :=
  BF4WilsonAllNomeTimeSector.limitRate hw0 hw1 (rows hw0 hw1 t ht x)

theorem normalized_bound (x : S) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : normalizedRate hw0 hw1 t ht x epsilon ≤ n) :
    RCle (dist (neumannPartial hw0 hw1 t ht x n).val (normalized hw0 hw1 t ht x).val) (rat epsilon) :=
  BF4WilsonAllNomeTimeSector.limit_bound hw0 hw1 (rows hw0 hw1 t ht x) epsilon he n hn

theorem normalized_norm_bound (x : S) :
    RCle (B (normalized hw0 hw1 t ht x).val (normalized hw0 hw1 t ht x).val) (B x.val x.val) := by
  apply rowLimit_norm_bound hw0 hw1
    (BF4WilsonAllNomeTimeSector.representedRows hw0 hw1 (rows hw0 hw1 t ht x))
  intro n
  rw [BF4WilsonAllNomeTimeSector.representedRows_point]
  exact partial_norm_bound hw0 hw1 t ht x n

theorem fixed_point (x : S) :
    (normalized hw0 hw1 t ht x).val = A (Scale HalfPow.half x.val)
      (stepState hw0 hw1 t ht (normalized hw0 hw1 t ht x)).val := by
  apply CRealSeminormCauchyRows.completed_eq_of_small P
  intro epsilon he
  let delta := quarter epsilon
  have hd : (0 : Q') < delta := quarter_pos he
  let n := normalizedRate hw0 hw1 t ht x delta
  apply CRealSeminormCompletedApproximation.completedDist_two_segment P
    _ (neumannPartial hw0 hw1 t ht x (n+1)).val _ epsilon
  · change RCle (dist _ _) (rat delta)
    rw [completedDist_symm]
    exact normalized_bound hw0 hw1 t ht x delta hd (n+1) (Nat.le_succ n)
  · change RCle (dist _ _) (rat delta)
    rw [partial_succ, translate_dist]
    have h := step_distance_bound hw0 hw1 t ht (neumannPartial hw0 hw1 t ht x n) (normalized hw0 hw1 t ht x)
    have hs := RCscale_scalar_mono (by decide : HalfPow.half*HalfPow.half ≤ (1 : Q'))
      (completedDist_nonnegative hw0 hw1
        (neumannPartial hw0 hw1 t ht x n).val (normalized hw0 hw1 t ht x).val)
    rw [RCscale_one] at hs
    exact RCle_trans h (RCle_trans hs
      (normalized_bound hw0 hw1 t ht x delta hd n (Nat.le_refl n)))

theorem normalized_congr {x y : S} (h : x.val = y.val) :
    (normalized hw0 hw1 t ht x).val = (normalized hw0 hw1 t ht y).val := by
  apply BF4WilsonAllNomeCauchyRows.limit_independent hw0 hw1
    (BF4WilsonAllNomeTimeSector.representedRows hw0 hw1 (rows hw0 hw1 t ht x))
    (BF4WilsonAllNomeTimeSector.representedRows hw0 hw1 (rows hw0 hw1 t ht y))
  intro n
  simp only [BF4WilsonAllNomeTimeSector.representedRows_point, rows]
  induction n with
  | zero => rfl
  | succ n ih => rw [partial_succ, partial_succ, h, step_congr hw0 hw1 t ht ih]

#print axioms scaledResolventState
#print axioms scaledResolventState_pin
#print axioms reflectionState
#print axioms reflectionState_pin
#print axioms complementState
#print axioms stepState
#print axioms stepState_pin
#print axioms complement_norm_bound
#print axioms step_distance_bound
#print axioms step_congr
#print axioms neumannPartial
#print axioms partial_norm_bound
#print axioms partial_step_bound
#print axioms partial_tail_bound
#print axioms modulus
#print axioms rows
#print axioms normalized
#print axioms normalizedRate
#print axioms normalized_bound
#print axioms normalized_norm_bound
#print axioms fixed_point
#print axioms normalized_congr

end YMGap.Continuum.BF4WilsonAllNomeScaledResolventNeumannLimit
