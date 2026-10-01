/-
# Represented Neumann limit of the normalized original vacuum inverse

The finite iterates stay in the original witnessed time-range sector and
vacuum complement. Their geometric squared-distance bound gives an explicit
Cauchy modulus from the input's supplied representative. The resulting limit
obeys the exact affine fixed-point equation on the original completion.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorNeumannPartial
import YMGap.Continuum.BF4WilsonAllNomeTimeSector
import YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
import YMGap.Continuum.PositiveContractionResidual
import YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation

namespace YMGap.Continuum.BF4WilsonAllNomeSectorNeumannLimit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeCauchyRows
open YMGap.Continuum.BF4WilsonAllNomeRowPairingLimit
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeSectorVacuumInverse
  (Centered val contraction contraction_dist_bound)
open YMGap.Continuum.BF4WilsonAllNomeSectorNeumannPartial
  (neumannPartial partial_succ partial_norm_bound partial_tail_bound affine_dist)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)
open YMGap.Continuum.PositiveContractionResidual (geometricCutoff geometric_bound)
open YMGap.Continuum.BF4ExactSlabPlaquetteCompletedApproximation (quarter quarter_pos)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "P" => distanceData hw0 hw1 (width := width)
local notation "PD" => pairingData hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "C" => Centered hw0 hw1 (width := width)
local notation "v" => val hw0 hw1
local notation "L" => contraction hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- Computed geometric threshold from the input's original range witness. -/
def modulus (q : Q') (x : C) (epsilon : Q') : Nat :=
  geometricCutoff q (normCeiling PD (representative hw0 hw1 x.state.range)) epsilon

private theorem ordered_small (q : Q') (hq0 : (0 : Q') ≤ q)
    (hq1 : q < (1 : Q')) (x : C) (epsilon : Q')
    (he : (0 : Q') < epsilon) (m n : Nat) (hmn : m ≤ n)
    (hm : modulus hw0 hw1 q x epsilon ≤ m) :
    RCle (dist (v (neumannPartial hw0 hw1 q x n))
      (v (neumannPartial hw0 hw1 q x m))) (rat epsilon) := by
  let X := representative hw0 hw1 x.state.range
  have h := partial_tail_bound hw0 hw1 q hq0 hq1 m (n-m) x
  rw [Nat.add_sub_of_le hmn] at h
  have hp0 := Q'.pow_nonneg q hq0 m
  have hp1 := HKPos.pow_le_one hq0 (Q'.le_of_lt hq1) m
  have hsq : q^m*q^m ≤ q^m := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hp1 hp0)
    (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have hnorm : RCle (B (v x) (v x)) (rat (normCeiling PD X)) := by
    change RCle (B x.state.val x.state.val) (rat (normCeiling PD X))
    rw [← representative_pin hw0 hw1 x.state.range]
    exact completedInner_diagonal_le_normCeiling PD X
  have hcap := RCle_trans h (RCscale_mono
    (Q'.mul_nonneg _ _ hp0 hp0) hnorm)
  have hs : RCscale (q^m*q^m) (rat (normCeiling PD X)) =
      rat ((q^m*q^m)*normCeiling PD X) :=
    Quotient.sound (CRealAlg.ofQ'_mul _ _).symm
  rw [hs] at hcap
  exact RCle_trans hcap (leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hsq (normCeiling_nonnegative PD X))
    (geometric_bound hq0 hq1 (normCeiling_nonnegative PD X) he m hm)))

/-- An original-sector Cauchy sequence with no selected quotient preimages. -/
def rows (q : Q') (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q')) (x : C) :
    BF4WilsonAllNomeTimeSector.CauchySequence hw0 hw1 (width := width) where
  seq := fun n => (neumannPartial hw0 hw1 q x n).state
  modulus := modulus hw0 hw1 q x
  bound := by
    intro epsilon he m n hm hn
    rcases Nat.le_total m n with hmn | hnm
    · rw [completedDist_symm]
      exact ordered_small hw0 hw1 q hq0 hq1 x epsilon he m n hmn hm
    · exact ordered_small hw0 hw1 q hq0 hq1 x epsilon he n m hnm hn

/-- The actual represented limit remains in the original vacuum complement. -/
def normalized (q : Q') (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (x : C) : C where
  state := BF4WilsonAllNomeTimeSector.limit hw0 hw1 (rows hw0 hw1 q hq0 hq1 x)
  orthogonal := by
    apply BF4WilsonAllNomeCauchyRows.limit_orthogonal hw0 hw1
      (BF4WilsonAllNomeTimeSector.representedRows hw0 hw1
        (rows hw0 hw1 q hq0 hq1 x))
    intro n
    rw [BF4WilsonAllNomeTimeSector.representedRows_point]
    exact (neumannPartial hw0 hw1 q x n).orthogonal

/-- Supplied convergence rate for the original completed vector. -/
def normalizedRate (q : Q') (hq0 : (0 : Q') ≤ q) (hq1 : q < (1 : Q'))
    (x : C) : Q' → Nat :=
  BF4WilsonAllNomeTimeSector.limitRate hw0 hw1 (rows hw0 hw1 q hq0 hq1 x)

theorem normalized_bound (q : Q') (hq0 : (0 : Q') ≤ q)
    (hq1 : q < (1 : Q')) (x : C) (epsilon : Q')
    (he : (0 : Q') < epsilon) (n : Nat)
    (hn : normalizedRate hw0 hw1 q hq0 hq1 x epsilon ≤ n) :
    RCle (dist (v (neumannPartial hw0 hw1 q x n))
      (v (normalized hw0 hw1 q hq0 hq1 x))) (rat epsilon) :=
  BF4WilsonAllNomeTimeSector.limit_bound hw0 hw1
    (rows hw0 hw1 q hq0 hq1 x) epsilon he n hn

/-- The normalized limit has the same fixed-carrier norm cap as every
finite convex Neumann partial. -/
theorem normalized_norm_bound (q : Q') (hq0 : (0 : Q') ≤ q)
    (hq1 : q < (1 : Q')) (x : C) :
    RCle (B (v (normalized hw0 hw1 q hq0 hq1 x))
      (v (normalized hw0 hw1 q hq0 hq1 x))) (B (v x) (v x)) := by
  apply BF4WilsonAllNomeRowPairingLimit.rowLimit_norm_bound hw0 hw1
    (BF4WilsonAllNomeTimeSector.representedRows hw0 hw1
      (rows hw0 hw1 q hq0 hq1 x))
  intro n
  rw [BF4WilsonAllNomeTimeSector.representedRows_point]
  exact partial_norm_bound hw0 hw1 q hq0 hq1 n x

/-- The represented limit obeys the actual affine equation, retaining the
original contraction and time-range carrier. -/
theorem fixed_point (q : Q') (hq0 : (0 : Q') ≤ q)
    (hq1 : q < (1 : Q')) (x : C) :
    v (normalized hw0 hw1 q hq0 hq1 x) =
      A (S (1-q) (v x))
        (S q (v (L (normalized hw0 hw1 q hq0 hq1 x)))) := by
  apply CRealSeminormCauchyRows.completed_eq_of_small P
  intro epsilon he
  let delta := quarter epsilon
  have hd : (0 : Q') < delta := quarter_pos he
  let n := normalizedRate hw0 hw1 q hq0 hq1 x delta
  apply CRealSeminormCompletedApproximation.completedDist_two_segment P
    _ (v (neumannPartial hw0 hw1 q x (n+1))) _ epsilon
  · change RCle (dist _ _) (rat delta)
    rw [completedDist_symm]
    exact normalized_bound hw0 hw1 q hq0 hq1 x delta hd (n+1) (Nat.le_succ n)
  · change RCle (dist _ _) (rat delta)
    rw [partial_succ]
    rw [affine_dist]
    have hsq : q*q ≤ 1 := Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg (Q'.le_of_lt hq1) (Q'.le_of_lt hq1)
        Q'.zero_le_one hq0) (by decide)
    have hscale := RCscale_mono (SumOfSquares.q_mul_self_nonneg q)
      (contraction_dist_bound hw0 hw1 (neumannPartial hw0 hw1 q x n)
        (normalized hw0 hw1 q hq0 hq1 x))
    have hscalar := RCscale_scalar_mono hsq
      (completedDist_nonnegative hw0 hw1 (v (neumannPartial hw0 hw1 q x n))
        (v (normalized hw0 hw1 q hq0 hq1 x)))
    rw [RCscale_one] at hscalar
    exact RCle_trans hscale (RCle_trans hscalar
      (normalized_bound hw0 hw1 q hq0 hq1 x delta hd n (Nat.le_refl n)))

#print axioms normalized
#print axioms normalized_bound
#print axioms normalized_norm_bound
#print axioms fixed_point

end YMGap.Continuum.BF4WilsonAllNomeSectorNeumannLimit
