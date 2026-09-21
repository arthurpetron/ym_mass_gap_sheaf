/-
# A common 1/16 two-step bound on the SAME completed Wilson carrier

The descent-count estimate is passed through the EXISTING original Wilson
connected-scalar limits. The original even-moment inequalities eliminate
the expression-dependent amplitude. The existing union and completion
pairing limits then give one rate 1/16 for every vector in the actual unit
complement, throughout the old guarded nome region.

No carrier, time map, state or guard is replaced. In particular, allowing
the old, looser entropy upper rate to approach one cannot by itself give
a slow channel. Physical scaling and its survival implications are separate
consumers; this module does not claim a continuum Yang--Mills theorem.
-/
import YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay
import YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap
import YMGap.Continuum.BF4WilsonSpatialUnionRelaxation

namespace YMGap.Continuum.BF4WilsonDescentCompletedGap

set_option autoImplicit false
open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay (sizeLoss)
open YMGap.Continuum.BF4WilsonDescentUniformConnectedDecay
open YMGap.Continuum.BF4WilsonSpatialUnion (Stage)
open YMGap.Continuum.BF4WilsonSpatialUnionCenteredForm (centeredMoment centeredMoment_diagonal_pin)
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4WilsonSpatialUnionPairingData (completedInner)
open YMGap.Continuum.BF4WilsonSpatialUnionCompletedGap
  (representativeCenteredMoment representativeCenteredMoment_converges
   representativeCenteredMoment_pin completedCenteredScalar completedCenteredScalar_of_orthogonal)
open YMGap.Continuum.BF4WilsonSpatialUnionTimeForm
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap (dyadic_geometric_first_le)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

attribute [local irreducible] intrinsicForm

/-- The original regulator diagonal, not a different measure, carries the bound. -/
theorem centeredTimeMoment_bound {base : Nat} (hb : 0<base) (R n : Nat)
    (x y : IntrinsicExpression base) (hx : x.radius ≤ R) (hy : y.radius ≤ R) :
    leEv (centeredTimeMoment hw0 hw1 hsmall hd hs hb n x y)
      (ofQ' (decayAmplitude w hd base R x y * timeRate^(R+n+1-sizeLoss base R))) :=
  leEv_of_convergesTo_le
    (connectedScalar_time_converges hw0 hw1 hsmall hd hs hb n (R+n) x y
      (Nat.le_trans hx (Nat.le_add_right _ _)) (Nat.add_le_add_right hy n))
    (convergesTo_const _)
    (fun k => leEv_ofQ'_of_approx_ge (fun _ => Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (connectedScalar_uniform_bound hw0 hw1 hsmall hd hs base k R n k k x y hx hy)))

def positivePrefactor (w : Q') (hd : heatRemainderBound w < 1)
    {base : Nat} (R : Nat) (x y : IntrinsicExpression base) : Q' :=
  RationalShiftedGeometric.amplitude timeRate (decayAmplitude w hd base R x y)
    timeRate_positive (sizeLoss base R)

theorem positivePrefactor_pos (w : Q') (hd : heatRemainderBound w < 1)
    {base : Nat} (R : Nat) (x y : IntrinsicExpression base) :
    (0 : Q') < positivePrefactor w hd R x y :=
  RationalShiftedGeometric.amplitude_pos _ _ timeRate_positive
    (decayAmplitude_nonnegative w hd base R x y) _

theorem centeredTimeMoment_le_geometric {base : Nat} (hb : 0<base) (R n : Nat)
    (x y : IntrinsicExpression base) (hx : x.radius ≤ R) (hy : y.radius ≤ R) :
    leEv (centeredTimeMoment hw0 hw1 hsmall hd hs hb n x y)
      (ofQ' (positivePrefactor w hd R x y * timeRate^n)) := by
  have h := RationalShiftedGeometric.shifted_bound timeRate_positive timeRate_lt_one
    (decayAmplitude_nonnegative w hd base R x y) (sizeLoss base R) R n
  rw [Nat.add_comm n R] at h
  exact leEv_trans (centeredTimeMoment_bound hw0 hw1 hsmall hd hs hb R n x y hx hy)
    (leEv_ofQ'_of_approx_ge (fun _ => h))

theorem evenMoment_le_geometric {base : Nat} (hb : 0<base) (x : IntrinsicExpression base) (k : Nat) :
    leEv (evenMoment hw0 hw1 hsmall hd hs hb x k)
      (ofQ' (positivePrefactor w hd x.radius x x * twoStepRate^k)) :=
  leEv_trans
    (centeredTimeMoment_le_geometric hw0 hw1 hsmall hd hs hb x.radius (2*k) x x
      (Nat.le_refl _) (Nat.le_refl _))
    (leEv_of_equiv (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.mul_eqv_congr_left _ _ _ (RationalShiftedGeometric.even_power timeRate k))))

/-- The actual same-object moment proof removes all probe/coupling amplitudes. -/
theorem evenMoment_first_le {base : Nat} (hb : 0<base) (x : IntrinsicExpression base) :
    leEv (evenMoment hw0 hw1 hsmall hd hs hb x 1)
      (mul (ofQ' twoStepRate) (evenMoment hw0 hw1 hsmall hd hs hb x 0)) :=
  dyadic_geometric_first_le (evenMoment hw0 hw1 hsmall hd hs hb x)
    twoStepRate (positivePrefactor w hd x.radius x x)
    twoStepRate_positive (positivePrefactor_pos w hd x.radius x x)
    (evenMoment_nonnegative hw0 hw1 hsmall hd hs hb x)
    (evenMoment_le_zero hw0 hw1 hsmall hd hs hb x)
    (evenMoment_dyadic hw0 hw1 hsmall hd hs hb x)
    (evenMoment_le_geometric hw0 hw1 hsmall hd hs hb x)

theorem centered_twoStep_bound (x : Stage) :
    leEv (centeredMoment hw0 hw1 hsmall hd hs 2 x x)
      (mul (ofQ' twoStepRate) (centeredMoment hw0 hw1 hsmall hd hs 0 x x)) :=
  leEv_trans (leEv_of_equiv (centeredMoment_diagonal_pin hw0 hw1 hsmall hd hs 2 x))
    (leEv_trans (evenMoment_first_le hw0 hw1 hsmall hd hs x.positive x.value)
      (leEv_of_equiv (TrigSignedAdd.mul_congr_right
        (centeredMoment_diagonal_pin hw0 hw1 hsmall hd hs 0 x).symm)))

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs

theorem representative_twoStep_form_gap (X : (D).Cauchy) :
    leEv (representativeCenteredMoment hw0 hw1 hsmall hd hs 2 X X)
      (mul (ofQ' twoStepRate) (representativeCenteredMoment hw0 hw1 hsmall hd hs 0 X X)) :=
  leEv_of_convergesTo_le
    (representativeCenteredMoment_converges hw0 hw1 hsmall hd hs 2 X X)
    (convergesTo_const_mul (ofQ' twoStepRate)
      (representativeCenteredMoment_converges hw0 hw1 hsmall hd hs 0 X X))
    (fun k => centered_twoStep_bound hw0 hw1 hsmall hd hs (X.seq k))

theorem completedCenteredScalar_twoStep_gap (x : V) :
    RCle (completedCenteredScalar hw0 hw1 hsmall hd hs 2 x x)
      (RCmul (Quotient.mk crealSetoid (ofQ' twoStepRate))
        (completedCenteredScalar hw0 hw1 hsmall hd hs 0 x x)) := by
  refine Quotient.inductionOn x ?_
  intro X
  rw [representativeCenteredMoment_pin hw0 hw1 hsmall hd hs 2 X X,
    representativeCenteredMoment_pin hw0 hw1 hsmall hd hs 0 X X]
  exact representative_twoStep_form_gap hw0 hw1 hsmall hd hs X

/-- EVERY completed vector, on the existing carrier and time map. The
coupling guards remain, but the certified rate itself is the constant 1/16. -/
theorem completed_twoStep_form_gap (x : V) (hx : B x U = RCzero) :
    RCle (B x (T 2 x)) (RCscale twoStepRate (B x x)) := by
  have h := completedCenteredScalar_twoStep_gap hw0 hw1 hsmall hd hs x
  rw [completedCenteredScalar_of_orthogonal hw0 hw1 hsmall hd hs 2 x hx,
    completedCenteredScalar_of_orthogonal hw0 hw1 hsmall hd hs 0 x hx,
    completedTime_zero] at h
  exact h

theorem oneStep_norm_gap (x : V) (hx : B x U = RCzero) :
    RCle (B (T 1 x) (T 1 x)) (RCscale twoStepRate (B x x)) := by
  rw [completedInner_time_balance, ← completedTime_add]
  exact completed_twoStep_form_gap hw0 hw1 hsmall hd hs x hx

/-- The improved constant applies to the SAME original even-time response,
not just to one isolated form value. -/
theorem norm_decay (x : V) (hx : B x U = RCzero) : ∀ n : Nat,
    RCle (B (T n x) (T n x)) (RCscale (twoStepRate^n) (B x x))
  | 0 => by
      rw [completedTime_zero, show twoStepRate^0 = (1 : Q') from rfl, RCscale_one]
      exact RCle_refl _
  | n+1 => by
      have hstep := oneStep_norm_gap hw0 hw1 hsmall hd hs (T n x)
        (completedTime_preserves_orthogonal hw0 hw1 hsmall hd hs n x hx)
      rw [← completedTime_add, Nat.add_comm 1 n] at hstep
      have h := RCle_trans hstep (RCscale_mono (Q'.le_of_lt twoStepRate_positive) (norm_decay x hx n))
      rw [RCscale_RCscale] at h
      exact h

theorem even_autocorrelation_decay (x : V) (hx : B x U = RCzero) (n : Nat) :
    RCle (B x (T (2*n) x)) (RCscale (twoStepRate^n) (B x x)) := by
  rw [completedInner_even_diagonal]
  exact norm_decay hw0 hw1 hsmall hd hs x hx n

end YMGap.Continuum.BF4WilsonDescentCompletedGap

#print axioms YMGap.Continuum.BF4WilsonDescentCompletedGap.centeredTimeMoment_bound
#print axioms YMGap.Continuum.BF4WilsonDescentCompletedGap.positivePrefactor
#print axioms YMGap.Continuum.BF4WilsonDescentCompletedGap.positivePrefactor_pos
#print axioms YMGap.Continuum.BF4WilsonDescentCompletedGap.centeredTimeMoment_le_geometric
#print axioms YMGap.Continuum.BF4WilsonDescentCompletedGap.evenMoment_le_geometric
#print axioms YMGap.Continuum.BF4WilsonDescentCompletedGap.evenMoment_first_le
#print axioms YMGap.Continuum.BF4WilsonDescentCompletedGap.centered_twoStep_bound
#print axioms YMGap.Continuum.BF4WilsonDescentCompletedGap.representative_twoStep_form_gap
#print axioms YMGap.Continuum.BF4WilsonDescentCompletedGap.completedCenteredScalar_twoStep_gap
#print axioms YMGap.Continuum.BF4WilsonDescentCompletedGap.completed_twoStep_form_gap
#print axioms YMGap.Continuum.BF4WilsonDescentCompletedGap.oneStep_norm_gap
#print axioms YMGap.Continuum.BF4WilsonDescentCompletedGap.norm_decay
#print axioms YMGap.Continuum.BF4WilsonDescentCompletedGap.even_autocorrelation_decay
