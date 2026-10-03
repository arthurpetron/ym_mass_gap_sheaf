/-
# Signed gain propagates the actual fixed bent orbit

The constructed original relative gain C2-w^18*C1>=C2/4 gives the
rational adjacent floor rho=(4/3)*w^18 at start one. Existing positivity
of powers of the SAME completed time map propagates this floor. Together
with the checked C2>=2^(-128), every integer-time image has an explicit
positive squared norm. No real division, spectrum or new normalization
is used.

All statements concern nome 1/16, width two and the literal bent state.
The resulting response-drop coefficient s*(1-rho) grows with s; it is
not a scale-uniform signed block-Rayleigh estimate or a changing-family
survival result. No finite inequality is inferred by reversing convergence.
-/

import YMGap.Continuum.BF4WilsonSmallNomeBentSignedLimit
import YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredGeometricSurvival

namespace YMGap.Continuum.BF4WilsonSmallNomeBentSignedOrbit

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
  (smallNome smallNome_pos)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTerminalGain (relativeSquareFloor)
open YMGap.Continuum.BF4WilsonSmallNomeBentCompletedGain
  (bentLoop bent_centered_lag_two_floor)
open YMGap.Continuum.BF4WilsonSmallNomeBentSignedLimit
  (bent_completed_signed_gain_relative_lower)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
  (centeredVector centeredVector_time_pairing)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedInner_time_sum)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (completedInner_zero_left)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedZero)
open YMGap.Continuum.BF4WilsonAllNomeDyadicFilteredGeometricSurvival
  (response_shifted_step_lower response_shifted_geometric_lower)
open YMGap.Continuum.RCSignedPairBudget (neg_mono)

local infix:50 " ≈ " => Q'.eqv
local notation "hw0" => smallNome_pos
local notation "hw1" => (by decide : smallNome < (1 : Q'))
local notation "v" => centeredVector hw0 hw1 (loopState bentLoop)
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "Rq" a:arg => Quotient.mk crealSetoid (ofQ' a)
local notation "quarter" => Q'.mkPos 1 4 (by decide)
local notation "fourThirds" => Q'.mkPos 4 3 (by decide)

/-- The actual rational coefficient extracted from the proved signed gain. -/
def orbitRate : Q' := fourThirds*qpow smallNome 18

theorem orbitRate_positive : (0 : Q') < orbitRate := by decide

theorem orbitRate_le_one : orbitRate ≤ (1 : Q') := by decide

private theorem sub_self (x : RC) : RCsub x x = RCzero := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.add_neg_self_eqv (X.approx n)))

private theorem zero_add (x : RC) : RCadd RCzero x = x := by
  refine Quotient.inductionOn x ?_
  intro X
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (X.approx n))))

private theorem sub_add (x y : RC) : RCadd (RCsub x y) y = x := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.sub_add_cancel_eqv (X.approx n) (Y.approx n)))

private theorem collect (x y : Q') :
    fourThirds*(x+ -(qpow smallNome 18*y))+ -(fourThirds*(quarter*x)) ≈
      x+ -(orbitRate*y) := by
  have h := poly_identity_of_normal_eq
    (.add (.mul (.var 0) (.add (.var 1) (.neg (.mul (.var 2) (.var 3)))))
      (.neg (.mul (.var 0) (.mul (.var 4) (.var 1)))))
    (.add (.mul (.add (.var 0) (.neg (.mul (.var 0) (.var 4)))) (.var 1))
      (.neg (.mul (.mul (.var 0) (.var 2)) (.var 3))))
    (by decide) (fun
      | 0 => fourThirds
      | 1 => x
      | 2 => qpow smallNome 18
      | 3 => y
      | _ => quarter)
  exact Q'.eqv_trans _ _ _ h
    (Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ x
        (by decide : fourThirds+ -(fourThirds*quarter) ≈ (1 : Q')))
        (Q'.one_mul_eqv x)))

private theorem collect_real (x y : RC) :
    RCsub (RCscale fourThirds (RCsub x (RCscale (qpow smallNome 18) y)))
      (RCscale fourThirds (RCscale quarter x)) = RCsub x (RCscale orbitRate y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => collect (X.approx n) (Y.approx n)))

/-- The original signed-gain inequality supplies the initial ratio itself. -/
theorem bent_response_start_floor :
    RCle (RCscale orbitRate (B v (T 1 v))) (B v (T 2 v)) := by
  have hs := RCscale_mono (by decide : (0 : Q') ≤ fourThirds)
    bent_completed_signed_gain_relative_lower
  have hn := RCadd_le_add hs
    (RCle_refl (RCneg (RCscale fourThirds (RCscale quarter (B v (T 2 v))))))
  change RCle
    (RCsub (RCscale fourThirds (RCscale quarter (B v (T 2 v))))
      (RCscale fourThirds (RCscale quarter (B v (T 2 v)))))
    (RCsub (RCscale fourThirds
      (RCsub (B v (T 2 v)) (RCscale (qpow smallNome 18) (B v (T 1 v)))))
      (RCscale fourThirds (RCscale quarter (B v (T 2 v))))) at hn
  rw [sub_self, collect_real] at hn
  have h := RCadd_le_add hn (RCle_refl (RCscale orbitRate (B v (T 1 v))))
  rwa [zero_add, sub_add] at h

attribute [local irreducible] centeredVector loopState bentLoop

/-- Every adjacent lag after the same original lag-one anchor. -/
theorem bent_response_step_floor (k : Nat) :
    RCle (RCscale orbitRate (B v (T (k+1) v))) (B v (T (k+2) v)) := by
  have h := response_shifted_step_lower hw0 hw1 v orbitRate
    (Q'.le_of_lt orbitRate_positive) 1 bent_response_start_floor k
  have hleft : 1+k=k+1 := Nat.add_comm 1 k
  have hright : (k+1)+1=k+2 := by omega
  rw [hleft, hright] at h
  exact h

private theorem scale_rational (q r : Q') : RCscale q (Rq r) = Rq (q*r) := by
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => Q'.eqv_refl (q*r)))

/-- Computed positive lower coefficient, with no supplied reserve. -/
theorem bent_response_geometric_floor (k : Nat) :
    RCle (Rq (orbitRate^k*relativeSquareFloor)) (B v (T (k+2) v)) := by
  have htwo : RCle (Rq relativeSquareFloor) (B v (T 2 v)) := by
    rw [centeredVector_time_pairing]
    exact bent_centered_lag_two_floor
  have hstart : RCle (RCscale orbitRate (B v (T 2 v))) (B v (T 3 v)) :=
    bent_response_step_floor 1
  have h := RCle_trans
    (RCscale_mono (Q'.pow_nonneg orbitRate (Q'.le_of_lt orbitRate_positive) k) htwo)
    (response_shifted_geometric_lower hw0 hw1 v orbitRate
      (Q'.le_of_lt orbitRate_positive) 2 hstart k)
  rw [scale_rational] at h
  rw [show 2+k=k+2 from Nat.add_comm 2 k] at h
  exact h

private theorem power_positive (q : Q') (hq : (0 : Q') < q) :
    ∀ n : Nat, (0 : Q') < q^n
  | 0 => by change (0 : Q') < (1 : Q'); decide
  | n+1 => Q'.mul_pos hq (power_positive q hq n)

/-- Squared norm of the actual integer-time image on the existing carrier. -/
theorem bent_time_norm_floor (n : Nat) :
    RCle (Rq (orbitRate^(2*n)*relativeSquareFloor))
      (B (T (n+1) v) (T (n+1) v)) := by
  have htime : (n+1)+(n+1)=2*n+2 := by omega
  rw [completedInner_time_sum, htime]
  exact bent_response_geometric_floor (2*n)

theorem bent_time_norm_ne_zero (n : Nat) :
    B (T (n+1) v) (T (n+1) v) ≠ RCzero := by
  intro hz
  have h := bent_time_norm_floor n
  rw [hz] at h
  have hbad : orbitRate^(2*n)*relativeSquareFloor ≤ (0 : Q') := by
    apply Q'.le_of_forall_pos_add
    intro epsilon he
    obtain ⟨M, hM⟩ := h epsilon he
    exact hM M (Nat.le_refl M)
  have hp := Q'.mul_pos (power_positive orbitRate orbitRate_positive (2*n))
    (by decide : (0 : Q') < relativeSquareFloor)
  exact (by decide : ¬ (0 : Q') < (0 : Q')) (Q'.pos_of_lt_of_le hp hbad)

theorem bent_time_ne_zero (n : Nat) : T (n+1) v ≠ completedZero hw0 hw1 2 := by
  intro hz
  apply bent_time_norm_ne_zero n
  rw [hz, completedInner_zero_left]

/-- A completed response-loss estimate only. The coefficient does not
shrink with lag and supplies no finite reverse-convergence estimate. -/
theorem bent_response_drop_bound (k : Nat) :
    RCle (RCsub (B v (T (k+1) v)) (B v (T (k+2) v)))
      (RCscale (1-orbitRate) (B v (T (k+1) v))) := by
  have h := RCadd_le_add (RCle_refl (B v (T (k+1) v)))
    (neg_mono (bent_response_step_floor k))
  have hid (x : RC) : RCsub x (RCscale orbitRate x) = RCscale (1-orbitRate) x := by
    refine Quotient.inductionOn x ?_
    intro X
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr' (Q'.one_mul_eqv (X.approx n))
          (Q'.neg_mul_eqv orbitRate (X.approx n))))))
  change RCle _ (RCsub (B v (T (k+1) v)) (RCscale orbitRate (B v (T (k+1) v)))) at h
  rwa [hid] at h

end YMGap.Continuum.BF4WilsonSmallNomeBentSignedOrbit

#print axioms YMGap.Continuum.BF4WilsonSmallNomeBentSignedOrbit.orbitRate
#print axioms YMGap.Continuum.BF4WilsonSmallNomeBentSignedOrbit.orbitRate_positive
#print axioms YMGap.Continuum.BF4WilsonSmallNomeBentSignedOrbit.orbitRate_le_one
#print axioms YMGap.Continuum.BF4WilsonSmallNomeBentSignedOrbit.bent_response_start_floor
#print axioms YMGap.Continuum.BF4WilsonSmallNomeBentSignedOrbit.bent_response_step_floor
#print axioms YMGap.Continuum.BF4WilsonSmallNomeBentSignedOrbit.bent_response_geometric_floor
#print axioms YMGap.Continuum.BF4WilsonSmallNomeBentSignedOrbit.bent_time_norm_floor
#print axioms YMGap.Continuum.BF4WilsonSmallNomeBentSignedOrbit.bent_time_norm_ne_zero
#print axioms YMGap.Continuum.BF4WilsonSmallNomeBentSignedOrbit.bent_time_ne_zero
#print axioms YMGap.Continuum.BF4WilsonSmallNomeBentSignedOrbit.bent_response_drop_bound
