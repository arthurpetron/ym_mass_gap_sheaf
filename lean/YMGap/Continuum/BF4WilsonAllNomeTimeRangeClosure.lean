/-
# Explicit defect-power decay on the represented original time-range closure

A local convergence witness retains original T(1)-preimage representatives
and its squared-distance modulus. This is not a new frontier enumeration or
an assertion of density in the entire carrier. One supplied preimage at a
tolerance-dependent stage suffices to control (I-T)^n on the limit.
No uniform preimage norm bound, inverse of T or countable choice is used.
-/

import YMGap.Continuum.BF4WilsonAllNomeDefectContraction
import YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail
import YMGap.Continuum.BF4WilsonAllNomeGraphDistance
import YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity

namespace YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeGraphDistance
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (defectPower)
open YMGap.Continuum.BF4WilsonAllNomeDefectContraction (defectPower_distance_contraction)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeTail
open YMGap.Continuum.CRealSeminormPairingCompletion
  (normCeiling normCeiling_nonnegative completedInner_diagonal_le_normCeiling)
open YMGap.Continuum.BF4ExactSlabThermodynamicPolynomialContinuity
  (linearTolerance linearTolerance_pos linearTolerance_budget)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "P" => pairingData hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "DP" => defectPower hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Z" => completedZero hw0 hw1 width
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

def quarter (e : Q') : Q' := HalfPow.half*(HalfPow.half*e)

theorem quarter_positive {e : Q'} (he : (0 : Q') < e) : (0 : Q') < quarter e :=
  ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos _ he)

theorem four_quarters (e : Q') :
    RCadd (RCadd (rat (quarter e)) (rat (quarter e)))
      (RCadd (rat (quarter e)) (rat (quarter e))) = rat e :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (ExpNeg.two_halves (HalfPow.half*e))
        (ExpNeg.two_halves (HalfPow.half*e))) (ExpNeg.two_halves e)))

/-- Actual source representatives and an all-tail convergence modulus. -/
structure RangeLimit (x : V) where
  preimage : Nat → (D).Cauchy
  modulus : Q' → Nat
  bound : ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
    RCle (dist (T 1 (Class (preimage n))) x) (rat e)

def fromTime (X : (D).Cauchy) : RangeLimit hw0 hw1 (T 1 (Class X)) where
  preimage := fun _ => X
  modulus := fun _ => 0
  bound := by
    intro e he n _
    rw [(completedDist_zero_iff hw0 hw1 _ _).mpr rfl]
    exact leEv_le_ofQ'_of_approx_le (fun _ => Q'.le_of_lt he)

def representedTailModulus (X : (D).Cauchy) (e : Q') : Nat :=
  relativeTailModulus (linearTolerance (normCeiling P X)
    (normCeiling_nonnegative P X) e)

theorem represented_tail_small (X : (D).Cauchy) (e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : representedTailModulus hw0 hw1 X e ≤ n) :
    RCle (B (DP n (T 1 (Class X))) (DP n (T 1 (Class X)))) (rat e) := by
  let cap := normCeiling P X
  have hc : (0 : Q') ≤ cap := normCeiling_nonnegative P X
  let delta := linearTolerance cap hc e
  have hd : (0 : Q') < delta := linearTolerance_pos cap hc he
  have h := RCle_trans (positiveTimeTail_small hw0 hw1 delta hd n hn (Class X))
    (RCscale_mono (Q'.le_of_lt hd) (completedInner_diagonal_le_normCeiling P X))
  exact RCle_trans h (leEv_le_ofQ'_of_approx_le (fun _ =>
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv delta cap))
      (linearTolerance_budget cap hc he)))

/-- Only ONE supplied preimage norm enters the computed tail cutoff. -/
def defectModulus {x : V} (R : RangeLimit hw0 hw1 x) (e : Q') : Nat :=
  representedTailModulus hw0 hw1 (R.preimage (R.modulus (quarter e))) (quarter e)

theorem defect_small {x : V} (R : RangeLimit hw0 hw1 x)
    (e : Q') (he : (0 : Q') < e) (n : Nat)
    (hn : defectModulus hw0 hw1 R e ≤ n) :
    RCle (B (DP n x) (DP n x)) (rat e) := by
  let delta := quarter e
  have hd : (0 : Q') < delta := quarter_positive he
  let k := R.modulus delta
  let a := T 1 (Class (R.preimage k))
  have hclose : RCle (dist a x) (rat delta) := R.bound delta hd k (Nat.le_refl _)
  have hleft : RCle (dist (DP n x) (DP n a)) (rat delta) :=
    RCle_trans (defectPower_distance_contraction hw0 hw1 n x a)
      (by rw [completedDist_symm]; exact hclose)
  have hright : RCle (dist (DP n a) Z) (rat delta) := by
    rw [dist_zero_right]
    exact represented_tail_small hw0 hw1 (R.preimage k) delta hd n hn
  have h := RCle_trans (completedDist_triangle hw0 hw1 (DP n x) (DP n a) Z)
    (RCadd_le_add (RCadd_le_add hleft hleft) (RCadd_le_add hright hright))
  rwa [dist_zero_right,four_quarters] at h

def defectDecayCertificate {x : V} (R : RangeLimit hw0 hw1 x)
    (e : Q') (he : (0 : Q') < e) :
    {N : Nat // ∀ n, N ≤ n → RCle (B (DP n x) (DP n x)) (rat e)} :=
  ⟨defectModulus hw0 hw1 R e,defect_small hw0 hw1 R e he⟩

/-- This witnessed sector intersects the original time kernel only at zero.
The ambient carrier and its boundary kernel have not been modified. -/
theorem kernel_zero {x : V} (R : RangeLimit hw0 hw1 x) (hx : T 1 x = Z) : x = Z := by
  apply (BF4WilsonAllNomeGeometry.completedInner_posdef hw0 hw1 width x).mp
  apply RCle_antisymm ?_ (completedInner_nonnegative hw0 hw1 x)
  apply RationalScalarTwoSidedError.le_of_all_errors
  intro e he
  let n := R.modulus e
  have hp : B x (T 1 (Class (R.preimage n))) = RCzero := by
    rw [← completedInner_time_balance,hx,completedInner_zero_left]
  have h := RCle_trans (norm_le_dist_of_orthogonal hw0 hw1 x _ hp)
    (by rw [completedDist_symm]; exact R.bound e he n (Nat.le_refl _))
  have hz : RCadd RCzero (rat e) = rat e :=
    Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun _ => Q'.eqv_of_eq (Q'.zero_add' e)))
  rw [hz]
  exact h

#print axioms quarter
#print axioms quarter_positive
#print axioms four_quarters
#print axioms RangeLimit
#print axioms fromTime
#print axioms representedTailModulus
#print axioms represented_tail_small
#print axioms defectModulus
#print axioms defect_small
#print axioms defectDecayCertificate
#print axioms kernel_zero

end YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
