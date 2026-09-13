/-
# The ORIGINAL unit line is exactly the fixed space of positive lattice time

The completed strict contraction rules out a nonzero fixed centered vector.
For every positive integer lag, T_n x=x if and only if P x=x, where P is the
existing original rank-one unit projection. A supplied Cauchy representative
returns the fixed vector's actual scalar coefficient and its modulus.

The vector fixed by positive time with unit coefficient one is exactly the
existing nonzero unit. This proves fixed-space uniqueness for the current
original thermodynamic plaquette OS completion at nome 1/1024. It does not
construct a nonzero excitation, a continuum theory, or a Hamiltonian spectrum.
-/

import YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation
import YMGap.Continuum.ContinuousTransferCalculus

namespace YMGap.Continuum.BF4ExactSlabThermodynamicFixedUnit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabThermodynamicSeminormCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedInner
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedPosdef
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletionLinear
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedRealScalar
open YMGap.Continuum.BF4ExactSlabThermodynamicUnitProjection
open YMGap.Continuum.BF4ExactSlabThermodynamicCenteredCompletion
open YMGap.Continuum.BF4ExactSlabThermodynamicCompletedTime
open YMGap.Continuum.BF4ExactSlabThermodynamicRelaxation
open YMGap.Continuum.MeanExpConvexProgress (le_of_add_le_add_right)

local notation "D" => seminorm
local notation "B" => completedInner
local notation "u" => completedUnit

private theorem le_zero_of_le_half (a : CReal) (h : leEv a (CReal.mul (ofQ' HalfPow.half) a)) : leEv a czero := by
  intro epsilon he
  obtain ⟨N, hN⟩ := h (HalfPow.half*epsilon) (ExpNeg.half_mul_pos epsilon he)
  refine ⟨N, fun n hn => ?_⟩
  have hh := Q'.add_le_add (hN n hn) (hN n hn)
  have heq : Q'.eqv
      ((HalfPow.half*a.approx n+HalfPow.half*epsilon)+(HalfPow.half*a.approx n+HalfPow.half*epsilon))
      (epsilon+a.approx n) :=
    Q'.eqv_trans _ _ _
      (RingNormaliser.poly_identity_of_normal_eq
        (.add (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1)))
        (.add (.add (.var 1) (.var 1)) (.add (.var 0) (.var 0))) (by decide)
        (fun | 0 => HalfPow.half*a.approx n | _ => HalfPow.half*epsilon))
      (Q'.add_eqv_congr' (ExpNeg.two_halves epsilon) (ExpNeg.two_halves (a.approx n)))
  have hx : a.approx n ≤ epsilon := le_of_add_le_add_right (Q'.le_trans' _ _ _ hh (Q'.le_of_eqv heq))
  simpa only [czero, ofQ', Q'.zero_add'] using hx

private theorem zero_of_le_half {a : RC} (ha : RCnonneg a) (h : RCle a (RCscale HalfPow.half a)) : a = RCzero := by
  revert ha h
  refine Quotient.inductionOn a ?_
  intro A hA h
  exact RCle_antisymm (le_zero_of_le_half A h) hA

/-- A positive-time fixed state has no centered component, without deciding its norm. -/
theorem fixed_center_zero (n : Nat) (hn : 0<n) (x : Completion) (hx : completedTime n x = x) :
    center x = completedZero := by
  have hc : completedTime n (center x) = center x := by rw [completedTime_center, hx]
  have h := centered_norm_decay x n
  rw [hc] at h
  have hhalf := RCle_trans h (RCscale_scalar_mono
    (show HalfPow.half^n ≤ HalfPow.half from half_pow_antitone 1 n hn)
    (completedInner_nonnegative (center x)))
  exact (completedInner_posdef (center x)).mp (zero_of_le_half (completedInner_nonnegative _) hhalf)

theorem time_fixed_iff_projection (n : Nat) (hn : 0<n) (x : Completion) :
    completedTime n x = x ↔ unitProjection x = x := by
  constructor
  · intro hx
    have h := center_decomposition x
    rw [fixed_center_zero n hn x hx, completedZero_add] at h
    exact h
  · intro hx
    exact (congrArg (completedTime n) hx.symm).trans ((completedTime_projection n x).trans hx)

theorem twoStep_fixed_iff_projection (x : Completion) :
    twoStepTransfer x = x ↔ unitProjection x = x := time_fixed_iff_projection 2 (by decide) x

/-- Existing coefficient and QCauchy data, not a freely chosen vacuum scalar. -/
def fixedScalarWitness (n : Nat) (hn : 0<n) (X : (D).Cauchy)
    (hX : completedTime n (Quotient.mk (D).completionSetoid X) = Quotient.mk (D).completionSetoid X) :
    Σ' c : CReal, Σ' cc : QCauchy c.approx,
      Quotient.mk (D).completionSetoid X = completedRealSmul c cc u :=
  ⟨unitCoefficient X, unitCoefficientCauchy X,
    ((time_fixed_iff_projection n hn _).mp hX).symm.trans (unitProjection_mk X)⟩

private theorem unit_mul (a : RC) : RCmul (Quotient.mk crealSetoid cone) a = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun k => Q'.one_mul_eqv (A.approx k)))

theorem fixed_unitCoefficient_one (n : Nat) (hn : 0<n) (x : Completion)
    (hx : completedTime n x = x) (hc : B x u = Quotient.mk crealSetoid cone) : x = u := by
  have hP := (time_fixed_iff_projection n hn x).mp hx
  refine hP.symm.trans ?_
  apply completed_eq_of_pairings
  intro y
  rw [unitProjection_pairing, hc, unit_mul]

/-- The unique unit-coefficient-one fixed vector exists and is nonzero. -/
theorem unit_fixed_normalized_nonzero (n : Nat) :
    completedTime n u = u ∧ B u u = Quotient.mk crealSetoid cone ∧ u ≠ completedZero :=
  ⟨completedTime_unit n, completedUnit_norm_one, completedUnit_ne_zero⟩

end YMGap.Continuum.BF4ExactSlabThermodynamicFixedUnit

#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFixedUnit.fixed_center_zero
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFixedUnit.time_fixed_iff_projection
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFixedUnit.twoStep_fixed_iff_projection
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFixedUnit.fixedScalarWitness
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFixedUnit.fixed_unitCoefficient_one
#print axioms YMGap.Continuum.BF4ExactSlabThermodynamicFixedUnit.unit_fixed_normalized_nonzero
