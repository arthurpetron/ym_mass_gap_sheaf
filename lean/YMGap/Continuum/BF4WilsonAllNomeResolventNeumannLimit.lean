/-
# Represented Neumann limit for the ORIGINAL resolvent denominator

Every iterate retains its original time-range witness. The proved physical
operator N=2R(I-R), R=(I+A)^(-1), has squared-distance factor 1/4.
The normalized recurrence b_0=0, b_(n+1)=x/2+N b_n is norm bounded and
converges with an explicit geometric modulus. Its constructed limit obeys
the exact fixed-point equation. No centered-subspace input is needed.

This supplies the represented input for the actual denominator inverse on
the physical bond quotient. It does not assume an inverse, a Cayley map,
physical-time scaling, or a continuum Hamiltonian.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSResolventReflection
import YMGap.Continuum.BF4WilsonAllNomeSectorNeumannPartial
import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation

namespace YMGap.Continuum.BF4WilsonAllNomeResolventNeumannLimit

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
open YMGap.Continuum.BF4WilsonAllNomeBondOSResolventReflection
  (reflection neumannStep square_complement_bound neumannStep_distance_bound)
open YMGap.Continuum.BF4WilsonAllNomeSectorNeumannPartial (affine_dist)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.RCSignedPairBudget (scale_congr)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

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

/-- Rational scaling propagates the supplied original range data. -/
def scaleState (a : Q') (x : S) : S where
  val := Scale a x.val
  range := BF4WilsonAllNomeTimeRangeLinear.rationalSmul hw0 hw1 a x.range

def subState (x y : S) : S := BF4WilsonAllNomeTimeSector.add hw0 hw1 x
  (BF4WilsonAllNomeTimeSector.negate hw0 hw1 y)

def reflectionState (x : S) : S := subState hw0 hw1
  (scaleState hw0 hw1 2 (BF4WilsonAllNomeSectorResolvent.state hw0 hw1 1 (by decide) x)) x

def complementState (x : S) : S := subState hw0 hw1 x
  (reflectionState hw0 hw1 (reflectionState hw0 hw1 x))

def stepState (x : S) : S := scaleState hw0 hw1 HalfPow.half (complementState hw0 hw1 x)

/-- The iterated witnessed map is exactly the checked physical operator. -/
theorem stepState_pin (x : S) :
    ofState hw0 hw1 (stepState hw0 hw1 x) = neumannStep hw0 hw1 (ofState hw0 hw1 x) := by
  apply BF4WilsonAllNomeBondOSTime.bondValue_injective hw0 hw1
  unfold neumannStep reflection
  simp only [bondValue_ofState, BF4WilsonAllNomeBondOSLinear.bondValue_smul,
    BF4WilsonAllNomeBondOSLinear.bondValue_sub,
    BF4WilsonAllNomeBondOSResolvent.bondValue_resolvent]
  rfl

private theorem complementState_pin (x : S) :
    ofState hw0 hw1 (complementState hw0 hw1 x) =
      BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 (ofState hw0 hw1 x)
        (reflection hw0 hw1 (reflection hw0 hw1 (ofState hw0 hw1 x))) := by
  apply BF4WilsonAllNomeBondOSTime.bondValue_injective hw0 hw1
  unfold reflection
  simp only [bondValue_ofState, BF4WilsonAllNomeBondOSLinear.bondValue_smul,
    BF4WilsonAllNomeBondOSLinear.bondValue_sub,
    BF4WilsonAllNomeBondOSResolvent.bondValue_resolvent]
  rfl

theorem complement_norm_bound (x : S) :
    RCle (B (complementState hw0 hw1 x).val (complementState hw0 hw1 x).val)
      (B x.val x.val) := by
  have h := square_complement_bound hw0 hw1 (ofState hw0 hw1 x)
  rw [← complementState_pin, bondValue_inner, bondValue_inner,
    bondValue_ofState, bondValue_ofState] at h
  exact h

theorem step_distance_bound (x y : S) :
    RCle (dist (stepState hw0 hw1 x).val (stepState hw0 hw1 y).val)
      (RCscale (HalfPow.half*HalfPow.half) (dist x.val y.val)) := by
  have h := neumannStep_distance_bound hw0 hw1 (ofState hw0 hw1 x) (ofState hw0 hw1 y)
  rw [← stepState_pin, ← stepState_pin, bondValue_distance, bondValue_distance,
    bondValue_ofState, bondValue_ofState, bondValue_ofState, bondValue_ofState] at h
  exact h

theorem step_congr {x y : S} (h : x.val = y.val) :
    (stepState hw0 hw1 x).val = (stepState hw0 hw1 y).val := by
  have hs := congrArg (fun a => BF4WilsonAllNomeBondOSTime.bondValue hw0 hw1
    (neumannStep hw0 hw1 a)) (BF4WilsonAllNomeBondOSLinear.ofState_congr hw0 hw1 h)
  dsimp only at hs
  rw [← stepState_pin, ← stepState_pin, bondValue_ofState, bondValue_ofState] at hs
  exact hs

def neumannPartial (x : S) : Nat → S
  | 0 => BF4WilsonAllNomeTimeSector.zero hw0 hw1
  | n+1 => BF4WilsonAllNomeTimeSector.add hw0 hw1
      (scaleState hw0 hw1 HalfPow.half x) (stepState hw0 hw1 (neumannPartial x n))

theorem partial_succ (x : S) (n : Nat) :
    (neumannPartial hw0 hw1 x (n+1)).val =
      A (Scale HalfPow.half x.val) (stepState hw0 hw1 (neumannPartial hw0 hw1 x n)).val := rfl

private theorem half_norm_sum (a : RC) :
    RCadd (RCscale HalfPow.half a) (RCscale HalfPow.half a) = a := by
  refine Quotient.inductionOn a ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => ExpNeg.two_halves (X.approx n)))

theorem partial_norm_bound (x : S) (n : Nat) :
    RCle (B (neumannPartial hw0 hw1 x n).val (neumannPartial hw0 hw1 x n).val) (B x.val x.val) := by
  induction n with
  | zero =>
      rw [neumannPartial, BF4WilsonAllNomeTimeSector.zero, completedInner_zero_left]
      exact completedInner_nonnegative hw0 hw1 x.val
  | succ n ih =>
      have hc := BF4WilsonAllNomeRootResolventPartial.convex_norm_le hw0 hw1
        HalfPow.half (by decide) (by decide) x.val
        (complementState hw0 hw1 (neumannPartial hw0 hw1 x n)).val
      rw [completedSmul_congr hw0 hw1 (by decide : Q'.eqv (1-HalfPow.half) HalfPow.half)] at hc
      have hl := RCle_trans (complement_norm_bound hw0 hw1 _) ih
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
    RCle (dist (neumannPartial hw0 hw1 x (m+1)).val (neumannPartial hw0 hw1 x (n+1)).val)
      (RCscale (HalfPow.half*HalfPow.half)
        (dist (neumannPartial hw0 hw1 x m).val (neumannPartial hw0 hw1 x n).val)) := by
  rw [partial_succ, partial_succ, translate_dist]
  exact step_distance_bound hw0 hw1 _ _

theorem partial_tail_bound (x : S) (n k : Nat) :
    RCle (dist (neumannPartial hw0 hw1 x (n+k)).val (neumannPartial hw0 hw1 x n).val)
      (RCscale (HalfPow.half^n*HalfPow.half^n) (B x.val x.val)) := by
  induction n with
  | zero =>
      rw [Nat.zero_add, neumannPartial, BF4WilsonAllNomeTimeSector.zero,
        dist_zero, Q'.pow_zero, scale_congr (by decide : Q'.eqv ((1 : Q')*1) 1), RCscale_one]
      exact partial_norm_bound hw0 hw1 x k
  | succ n ih =>
      rw [show n+1+k = (n+k)+1 by omega]
      have h := RCle_trans (partial_step_bound hw0 hw1 x (n+k) n)
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
    RCle (dist (neumannPartial hw0 hw1 x n).val (neumannPartial hw0 hw1 x m).val) (rat epsilon) := by
  let X := representative hw0 hw1 x.range
  have h := partial_tail_bound hw0 hw1 x m (n-m)
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
  seq := neumannPartial hw0 hw1 x
  modulus := modulus hw0 hw1 x
  bound := by
    intro epsilon he m n hm hn
    rcases Nat.le_total m n with hmn | hnm
    · rw [completedDist_symm]
      exact ordered_small hw0 hw1 x epsilon he m n hmn hm
    · exact ordered_small hw0 hw1 x epsilon he n m hnm hn

def normalized (x : S) : S := BF4WilsonAllNomeTimeSector.limit hw0 hw1 (rows hw0 hw1 x)

def normalizedRate (x : S) : Q' → Nat :=
  BF4WilsonAllNomeTimeSector.limitRate hw0 hw1 (rows hw0 hw1 x)

theorem normalized_bound (x : S) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : normalizedRate hw0 hw1 x epsilon ≤ n) :
    RCle (dist (neumannPartial hw0 hw1 x n).val (normalized hw0 hw1 x).val) (rat epsilon) :=
  BF4WilsonAllNomeTimeSector.limit_bound hw0 hw1 (rows hw0 hw1 x) epsilon he n hn

theorem normalized_norm_bound (x : S) :
    RCle (B (normalized hw0 hw1 x).val (normalized hw0 hw1 x).val) (B x.val x.val) := by
  apply rowLimit_norm_bound hw0 hw1
    (BF4WilsonAllNomeTimeSector.representedRows hw0 hw1 (rows hw0 hw1 x))
  intro n
  rw [BF4WilsonAllNomeTimeSector.representedRows_point]
  exact partial_norm_bound hw0 hw1 x n

theorem fixed_point (x : S) :
    (normalized hw0 hw1 x).val = A (Scale HalfPow.half x.val)
      (stepState hw0 hw1 (normalized hw0 hw1 x)).val := by
  apply CRealSeminormCauchyRows.completed_eq_of_small P
  intro epsilon he
  let delta := quarter epsilon
  have hd : (0 : Q') < delta := quarter_pos he
  let n := normalizedRate hw0 hw1 x delta
  apply CRealSeminormCompletedApproximation.completedDist_two_segment P
    _ (neumannPartial hw0 hw1 x (n+1)).val _ epsilon
  · change RCle (dist _ _) (rat delta)
    rw [completedDist_symm]
    exact normalized_bound hw0 hw1 x delta hd (n+1) (Nat.le_succ n)
  · change RCle (dist _ _) (rat delta)
    rw [partial_succ, translate_dist]
    have h := step_distance_bound hw0 hw1 (neumannPartial hw0 hw1 x n) (normalized hw0 hw1 x)
    have hs := RCscale_scalar_mono (by decide : HalfPow.half*HalfPow.half ≤ (1 : Q'))
      (completedDist_nonnegative hw0 hw1
        (neumannPartial hw0 hw1 x n).val (normalized hw0 hw1 x).val)
    rw [RCscale_one] at hs
    exact RCle_trans h (RCle_trans hs
      (normalized_bound hw0 hw1 x delta hd n (Nat.le_refl n)))

theorem normalized_congr {x y : S} (h : x.val = y.val) :
    (normalized hw0 hw1 x).val = (normalized hw0 hw1 y).val := by
  apply BF4WilsonAllNomeCauchyRows.limit_independent hw0 hw1
    (BF4WilsonAllNomeTimeSector.representedRows hw0 hw1 (rows hw0 hw1 x))
    (BF4WilsonAllNomeTimeSector.representedRows hw0 hw1 (rows hw0 hw1 y))
  intro n
  simp only [BF4WilsonAllNomeTimeSector.representedRows_point, rows]
  induction n with
  | zero => rfl
  | succ n ih => rw [partial_succ, partial_succ, h, step_congr hw0 hw1 ih]

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

end YMGap.Continuum.BF4WilsonAllNomeResolventNeumannLimit
