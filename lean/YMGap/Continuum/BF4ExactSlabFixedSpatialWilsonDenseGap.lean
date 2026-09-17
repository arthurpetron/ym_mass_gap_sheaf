/-
# Strict two-step bound on the SAME intrinsic Wilson reflected form

The actual finite connected estimate passes through the original common-
action three-regulator diagonal. Its explicit support loss is absorbed by
a positive rational prefactor independent of physical lag. The SAME even
moments have positivity, contraction and sharp dyadic Cauchy--Schwarz;
the existing constructive moment theorem eliminates that prefactor.

Only the scalar rate definitions and their positivity/smallness proofs are
reused from the older plaquette carrier. No bound on that older carrier is
transported or assumed. This is fixed-spacing small-nome SU(2), not a
changing-spacing or continuum Hamiltonian mass-gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonDenseGap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonOriginalConnectedCorrelator
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonUniformConnectedDecay
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredTimeMoments
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialDenseGap
  (timeRate timeRate_positive twoStepRate twoStepRate_positive twoStepRate_lt_one)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDenseDyadicGap (dyadic_geometric_first_le)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {base : Nat} (hb : 0<base)

attribute [local irreducible] intrinsicForm

/-- The SAME original connected moment inherits a regulator-independent bound. -/
theorem centeredTimeMoment_bound (R n : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ R) (hy : y.radius ≤ R) :
    leEv (centeredTimeMoment hw0 hw1 hsmall hd hs hb n x y)
      (ofQ' (decayAmplitude w hd hs base R x y * timeRate w hd^(R+n+1-sizeLoss base R))) :=
  leEv_of_convergesTo_le
    (connectedScalar_time_converges hw0 hw1 hsmall hd hs hb n (R+n) x y
      (Nat.le_trans hx (Nat.le_add_right _ _)) (Nat.add_le_add_right hy n))
    (convergesTo_const _)
    (fun k => leEv_ofQ'_of_approx_ge (fun _ => Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (connectedScalar_uniform_bound hw0 hw1 hsmall hd hs base k R n k k x y hx hy)))

/-- An actual positive prefactor, independent of time and all three regulators. -/
def positivePrefactor (R : Nat) (x y : IntrinsicExpression base) : Q' :=
  RationalShiftedGeometric.amplitude (timeRate w hd) (decayAmplitude w hd hs base R x y)
    (timeRate_positive hw0 hd) (sizeLoss base R)

theorem positivePrefactor_pos (R : Nat) (x y : IntrinsicExpression base) :
    (0 : Q') < positivePrefactor hw0 hd hs R x y :=
  RationalShiftedGeometric.amplitude_pos _ _ (timeRate_positive hw0 hd)
    (decayAmplitude_nonnegative w hd hs base R x y) _

theorem centeredTimeMoment_le_geometric (R n : Nat) (x y : IntrinsicExpression base)
    (hx : x.radius ≤ R) (hy : y.radius ≤ R) :
    leEv (centeredTimeMoment hw0 hw1 hsmall hd hs hb n x y)
      (ofQ' (positivePrefactor hw0 hd hs R x y * timeRate w hd^n)) := by
  have h := RationalShiftedGeometric.shifted_bound (timeRate_positive hw0 hd) hs
    (decayAmplitude_nonnegative w hd hs base R x y) (sizeLoss base R) R n
  rw [Nat.add_comm n R] at h
  exact leEv_trans (centeredTimeMoment_bound hw0 hw1 hsmall hd hs hb R n x y hx hy)
    (leEv_ofQ'_of_approx_ge (fun _ => h))

theorem evenMoment_le_geometric (x : IntrinsicExpression base) (k : Nat) :
    leEv (evenMoment hw0 hw1 hsmall hd hs hb x k)
      (ofQ' (positivePrefactor hw0 hd hs x.radius x x * twoStepRate w hd^k)) :=
  leEv_trans
    (centeredTimeMoment_le_geometric hw0 hw1 hsmall hd hs hb x.radius (2*k) x x
      (Nat.le_refl _) (Nat.le_refl _))
    (leEv_of_equiv (SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.mul_eqv_congr_left _ _ _ (RationalShiftedGeometric.even_power (timeRate w hd) k))))

/-- The expression-dependent prefactor disappears, including zero-norm inputs. -/
theorem evenMoment_first_le (x : IntrinsicExpression base) :
    leEv (evenMoment hw0 hw1 hsmall hd hs hb x 1)
      (mul (ofQ' (twoStepRate w hd)) (evenMoment hw0 hw1 hsmall hd hs hb x 0)) :=
  dyadic_geometric_first_le (evenMoment hw0 hw1 hsmall hd hs hb x)
    (twoStepRate w hd) (positivePrefactor hw0 hd hs x.radius x x)
    (twoStepRate_positive hw0 hd) (positivePrefactor_pos hw0 hd hs x.radius x x)
    (evenMoment_nonnegative hw0 hw1 hsmall hd hs hb x)
    (evenMoment_le_zero hw0 hw1 hsmall hd hs hb x)
    (evenMoment_dyadic hw0 hw1 hsmall hd hs hb x)
    (evenMoment_le_geometric hw0 hw1 hsmall hd hs hb x)

local notation "F" => intrinsicForm hw0 hw1 hsmall hd hs hb

private theorem centered_of_orthogonal (n : Nat) (x : IntrinsicExpression base)
    (hx : Equiv (F x (unit base)) czero) :
    Equiv (centeredTimeMoment hw0 hw1 hsmall hd hs hb n x x) (F x (advance n x)) := by
  have hz : Equiv (mul (F x (unit base)) (F (unit base) x)) czero :=
    (CReal.mul_congr_left hx).trans
      (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.zero_mul_eqv _))
  exact (Equiv_add (Equiv.refl _) (neg_congr hz)).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-(0 : Q')) 0))
      (QPoly.q_add_zero_eqv _)))

/-- One nome-dependent rate on EVERY intrinsic Wilson expression orthogonal
to the actual unit, independent of its radius, coefficients and positive base. -/
theorem dense_unitComplement_twoStep_bound (x : IntrinsicExpression base)
    (hx : Equiv (F x (unit base)) czero) :
    leEv (F x (advance 2 x)) (mul (ofQ' (twoStepRate w hd)) (F x x)) := by
  have hzero := centered_of_orthogonal hw0 hw1 hsmall hd hs hb 0 x hx
  rw [advance_zero] at hzero
  exact leEv_trans (leEv_of_equiv (centered_of_orthogonal hw0 hw1 hsmall hd hs hb 2 x hx).symm)
    (leEv_trans (evenMoment_first_le hw0 hw1 hsmall hd hs hb x)
      (leEv_of_equiv (TrigSignedAdd.mul_congr_right hzero)))

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonDenseGap

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonDenseGap.centeredTimeMoment_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonDenseGap.positivePrefactor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonDenseGap.positivePrefactor_pos
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonDenseGap.centeredTimeMoment_le_geometric
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonDenseGap.evenMoment_le_geometric
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonDenseGap.evenMoment_first_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonDenseGap.dense_unitComplement_twoStep_bound
