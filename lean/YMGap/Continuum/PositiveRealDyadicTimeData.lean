/-
# Constructed dyadic approximations of represented positive real times

PositiveTime carries an existing CReal, its explicit QCauchy data, and a
positive rational floor after a supplied index. These are ordinary numerical
time witnesses, not a physical analytic hypothesis or a frontier scorecard.
Shifting beyond that index and rounding upward constructs positive dyadic
times, their rational Cauchy modulus, and equality to the original real.
No modulus is extracted from the legacy Prop-valued CReal.cauchy field.
-/

import YMGap.Constructive.DyadicTimeRationals
import YMGap.Continuum.GNSHilbertSpace
import YMGap.Continuum.RegularLinearGeometricModulus

namespace YMGap.Continuum.PositiveRealDyadicTimeData

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint)
open YMGap.Constructive.DyadicTimeRationals (value upper upper_error)
open YMGap.Constructive.HalfPow (half half_nonneg)
open YMGap.Continuum.RegularLinearGeometricModulus (halfCutoff halfCutoff_spec)

structure PositiveTime where
  real : CReal
  cauchy : QCauchy real.approx
  floor : Q'
  floor_positive : (0 : Q') < floor
  start : Nat
  lower : ∀ n, start ≤ n → floor ≤ real.approx n

def rational (q : Q') (hq : (0 : Q') < q) : PositiveTime where
  real := ofQ' q
  cauchy := { M := fun _ => 0, bound := fun e he _ _ _ _ =>
    ⟨Q'.add_le_self_of_nonneg q e (Q'.le_of_lt he), Q'.add_le_self_of_nonneg q e (Q'.le_of_lt he)⟩ }
  floor := q
  floor_positive := hq
  start := 0
  lower := fun _ _ => Q'.le_refl' q

def sample (D : PositiveTime) (n : Nat) : Q' := D.real.approx (D.start+n)

theorem sample_lower (D : PositiveTime) (n : Nat) : D.floor ≤ sample D n :=
  D.lower _ (Nat.le_add_right _ _)

theorem sample_nonnegative (D : PositiveTime) (n : Nat) : (0 : Q') ≤ sample D n :=
  Q'.le_trans' _ _ _ (Q'.le_of_lt D.floor_positive) (sample_lower D n)

def approximation (D : PositiveTime) (n : Nat) : MeshPoint := upper (sample D n) n

theorem approximation_lower (D : PositiveTime) (n : Nat) : D.floor ≤ value (approximation D n) :=
  Q'.le_trans' _ _ _ (sample_lower D n) (upper_error _ (sample_nonnegative D n) n).1

theorem approximation_error (D : PositiveTime) (n : Nat) :
    sample D n ≤ value (approximation D n) ∧ value (approximation D n) ≤ sample D n + half^n :=
  upper_error _ (sample_nonnegative D n) n

theorem half_chain (a b c e : Q') (hab : a ≤ b + half*e) (hbc : b ≤ c + half*e) : a ≤ c+e :=
  Q'.le_trans' _ _ _ hab (Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ hbc)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves e)))))

def approximationModulus (D : PositiveTime) (epsilon : Q') : Nat :=
  max (D.cauchy.M (half*epsilon)) (halfCutoff (half*epsilon))

theorem mesh_error_small (D : PositiveTime) (epsilon : Q') (he : (0 : Q') < epsilon)
    (n : Nat) (hn : approximationModulus D epsilon ≤ n) : half^n ≤ half*epsilon :=
  Q'.le_trans' _ _ _ (half_pow_antitone _ n (Nat.le_trans (Nat.le_max_right _ _) hn))
    (halfCutoff_spec _ (ExpNeg.half_mul_pos epsilon he))

theorem approximation_cauchy (D : PositiveTime) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m n : Nat) (hm : approximationModulus D epsilon ≤ m) (hn : approximationModulus D epsilon ≤ n) :
    value (approximation D m) ≤ value (approximation D n) + epsilon ∧
    value (approximation D n) ≤ value (approximation D m) + epsilon := by
  have hh := ExpNeg.half_mul_pos epsilon he
  have hc := D.cauchy.bound (half*epsilon) hh (D.start+m) (D.start+n)
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hm) (Nat.le_add_left _ _))
    (Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hn) (Nat.le_add_left _ _))
  have hup (j : Nat) (hj : approximationModulus D epsilon ≤ j) :
      value (approximation D j) ≤ sample D j + half*epsilon :=
    Q'.le_trans' _ _ _ (approximation_error D j).2
      (Q'.add_le_add_left _ _ _ (mesh_error_small D epsilon he j hj))
  exact ⟨half_chain _ _ _ epsilon (hup m hm)
      (Q'.le_trans' _ _ _ hc.1 (Q'.add_le_add_right _ _ _ (approximation_error D n).1)),
    half_chain _ _ _ epsilon (hup n hn)
      (Q'.le_trans' _ _ _ hc.2 (Q'.add_le_add_right _ _ _ (approximation_error D m).1))⟩

def approximationCauchy (D : PositiveTime) : QCauchy (fun n => value (approximation D n)) where
  M := approximationModulus D
  bound := approximation_cauchy D

def approximationReal (D : PositiveTime) : CReal where
  approx := fun n => value (approximation D n)
  cauchy := fun e he => ⟨approximationModulus D e, approximation_cauchy D e he⟩

/-- The numerical dyadic stream represents the supplied real time, not a new target. -/
theorem approximationReal_equiv (D : PositiveTime) : Equiv (approximationReal D) D.real := by
  intro epsilon he
  refine ⟨approximationModulus D epsilon, fun n hn => ?_⟩
  have hh := ExpNeg.half_mul_pos epsilon he
  have hnM := Nat.le_trans (Nat.le_max_left _ _) hn
  have hc := D.cauchy.bound (half*epsilon) hh (D.start+n) n
    (Nat.le_trans hnM (Nat.le_add_left _ _)) hnM
  have hu : value (approximation D n) ≤ sample D n + half*epsilon :=
    Q'.le_trans' _ _ _ (approximation_error D n).2
      (Q'.add_le_add_left _ _ _ (mesh_error_small D epsilon he n hn))
  exact ⟨half_chain _ _ _ epsilon hu hc.1,
    half_chain _ _ _ epsilon hc.2 (Q'.le_trans' _ _ _ (approximation_error D n).1
      (Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt hh)))⟩

theorem rational_sample (q : Q') (hq : (0 : Q') < q) (n : Nat) : sample (rational q hq) n = q := rfl

theorem rational_real (q : Q') (hq : (0 : Q') < q) : (rational q hq).real = ofQ' q := rfl

end YMGap.Continuum.PositiveRealDyadicTimeData

#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.PositiveTime
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.rational
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.sample
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.sample_lower
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.sample_nonnegative
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.approximation
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.approximation_lower
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.approximation_error
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.half_chain
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.approximationModulus
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.mesh_error_small
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.approximation_cauchy
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.approximationCauchy
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.approximationReal
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.approximationReal_equiv
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.rational_sample
#print axioms YMGap.Continuum.PositiveRealDyadicTimeData.rational_real
