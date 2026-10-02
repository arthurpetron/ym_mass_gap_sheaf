/-
# ALL dyadic increments on the SAME positively anchored Wilson bond state

The existing ORIGINAL dyadic dissipation estimate applies to the literal
unit excitation after side(scale)+lag time steps. Every supplied dyadic
increment of value at most side(scale)*2^(-k) has squared distance at most
2^(-k), uniformly in nome, width and scale. Zero mesh increments are included
on the completed carrier; positive meshes recover the actual bond action.

The computed geometric radius half*half^epsilon.den leaves the factor-two
slack needed by the existing positive-real-time approximation. This is
within-state continuity support, not cross-scale convergence, a surviving
limiting norm, physical time calibration or a continuum Yang--Mills theorem.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchor
import YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy
import YMGap.Constructive.DyadicTimeRationals

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchorContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.HalfPow (half)
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint embed)
open YMGap.Constructive.DyadicTimeRationals
  (value value_num value_den value_le_iff half_power_num half_power_den)
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeDyadicSemigroup (meshAction mesh_original action_embed)
open YMGap.Continuum.BF4WilsonAllNomeDyadicEnergy (anchored_small_bound)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
  (dyadicUnitExcitation dyadicUnitExcitation_norm)
open YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchor
  (anchoredBondExcitation anchoredBond_value)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion (bondCompletedDistance)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondAction bondAction_value bondValue_distance)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimePins (positiveAction_dyadic)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (dyadicTime)

local notation "Rq" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "half" => YMGap.Constructive.HalfPow.half

private theorem scaled_mesh_pin (count k : Nat) :
    Q'.eqv (value ⟨k,count⟩) (Q'.ofNat count*half^k) := by
  change (value ⟨k,count⟩).num * ((Q'.ofNat count*half^k).den : Int) =
    (Q'.ofNat count*half^k).num * ((value ⟨k,count⟩).den : Int)
  rw [value_num, value_den, Q'.mul_den_cast, Q'.mul_num_cast]
  change (count : Int)*(1*((half^k).den : Int)) =
    ((count : Int)*(half^k).num)*(2^k : Nat)
  rw [half_power_num k, half_power_den k]
  rw [Int.one_mul, Int.mul_one]

private theorem scale_rational_one (q : Q') : RCscale q (Rq 1) = Rq q :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.mul_one_eqv q))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation "T" => completedTime hw0 hw1
local notation "u" => Subtype.val (dyadicUnitExcitation hw0 hw1 scale width hwidth)
local notation "x" lag:arg => anchoredBondExcitation hw0 hw1 scale width hwidth lag

/-- Every mesh presentation, including zero steps, on the literal completed
positive-time image. No fractional operator is substituted for the original. -/
theorem anchoredMesh_increment_bound (lag : Nat) (p : MeshPoint) (k : Nat)
    (ht : value p ≤ Q'.ofNat (side scale)*half^k) :
    RCle (completedDist hw0 hw1
      (meshAction hw0 hw1 p.depth p.steps (T (side scale+lag) u))
      (T (side scale+lag) u)) (Rq (half^k)) := by
  have hv : value p ≤ value ⟨k,side scale⟩ := Q'.le_trans' _ _ _ ht
    (Q'.ge_of_eqv (scaled_mesh_pin (side scale) k))
  have hsteps := (value_le_iff p ⟨k,side scale⟩).mp hv
  have hbudget : (p.steps*2^0)*2^k ≤ (side scale+lag)*2^p.depth := by
    simp only [Nat.pow_zero, Nat.mul_one]
    exact Nat.le_trans hsteps
      (Nat.mul_le_mul_right (2^p.depth) (Nat.le_add_right (side scale) lag))
  have h := anchored_small_bound hw0 hw1 0 (side scale+lag)
    p.depth p.steps k hbudget u
  simp only [mesh_original, dyadicUnitExcitation_norm, scale_rational_one] at h
  exact h

/-- Positive dyadic time is the existing actual bond action, with the same
uniform ceiling. The strict step guard only constructs positive numerical time. -/
theorem anchoredBond_dyadic_increment_bound (lag : Nat) (p : MeshPoint)
    (hp : 0 < p.steps) (k : Nat)
    (ht : value p ≤ Q'.ofNat (side scale)*half^k) :
    RCle (bondCompletedDistance hw0 hw1
      (bondAction hw0 hw1 (dyadicTime p hp) (x lag)) (x lag)) (Rq (half^k)) := by
  rw [bondValue_distance, bondAction_value, anchoredBond_value,
    positiveAction_dyadic, action_embed]
  exact anchoredMesh_increment_bound hw0 hw1 scale width hwidth lag p k ht

/-- Geometric radius, independent of nome, width and scale. The original
lattice-time radius is side(scale) times this scalar. -/
def anchoredRadius (epsilon : Q') : Q' := half*half^epsilon.den

theorem anchoredRadius_positive (epsilon : Q') :
    (0 : Q') < anchoredRadius epsilon := by
  unfold anchoredRadius
  have hp : ∀ k : Nat, (0 : Q') < half^k := by
    intro k
    induction k with
    | zero => decide
    | succ k ih => exact Q'.mul_pos (by decide : (0 : Q') < half) ih
  exact Q'.mul_pos (by decide : (0 : Q') < half) (hp epsilon.den)

/-- Exact slack budget used to bound eventual real-time mesh approximants. -/
theorem radius_double (scale : Nat) (epsilon : Q') :
    Q'.eqv
      (Q'.ofNat (side scale)*anchoredRadius epsilon +
        Q'.ofNat (side scale)*anchoredRadius epsilon)
      (Q'.ofNat (side scale)*half^epsilon.den) := by
  unfold anchoredRadius
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq
      (.add (.mul (.var 0) (.mul (.var 1) (.var 2)))
        (.mul (.var 0) (.mul (.var 1) (.var 2))))
      (.add (.mul (.var 1) (.mul (.var 0) (.var 2)))
        (.mul (.var 1) (.mul (.var 0) (.var 2)))) (by decide)
      (fun
        | 0 => Q'.ofNat (side scale)
        | 1 => half
        | _ => half^epsilon.den))
    (ExpNeg.two_halves _)

theorem half_den_small (epsilon : Q') (he : (0 : Q') < epsilon) :
    half^epsilon.den ≤ epsilon :=
  Q'.le_trans' _ _ _ (HalfPow.pow_half_le_invSucc epsilon.den)
    (HalfPow.invSucc_den_le epsilon he)

#print axioms anchoredMesh_increment_bound
#print axioms anchoredBond_dyadic_increment_bound
#print axioms anchoredRadius
#print axioms anchoredRadius_positive
#print axioms radius_double
#print axioms half_den_small

end YMGap.Continuum.BF4WilsonAllNomeDyadicBondAnchorContinuity
