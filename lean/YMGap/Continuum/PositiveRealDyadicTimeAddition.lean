/-
# Constructed addition of the SAME positive real times

The sum is represented by sums of the two certified dyadic streams.
Its numerical QCauchy rate and positive floor are computed. The time
value is exactly the pre-existing CReal/RC sum of the supplied real
values, not a new formal addition unrelated to those values.
No physical hypothesis or quotient representative selection is used.
-/

import YMGap.Continuum.PositiveRealDyadicTimeData
import YMGap.Continuum.SelfAdjointHamiltonian

namespace YMGap.Continuum.PositiveRealDyadicTimeAddition

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.NonnegativeDyadicTime (MeshPoint addMesh)
open YMGap.Constructive.DyadicTimeRationals (value value_num value_den)
open YMGap.Continuum.PositiveRealDyadicTimeData

theorem value_addMesh (p q : MeshPoint) : Q'.eqv (value (addMesh p q)) (value p + value q) := by
  change (value (addMesh p q)).num * ((value p + value q).den : Int) =
    ((value p).num * ((value q).den : Int) + (value q).num * ((value p).den : Int)) *
      ((value (addMesh p q)).den : Int)
  rw [Q'.add_den_cast, value_num, value_num, value_num, value_den, value_den, value_den]
  simp only [addMesh, Nat.pow_add, Int.natCast_add, Int.natCast_mul]

def sumSample (D E : PositiveTime) (n : Nat) : Q' := value (approximation D n) + value (approximation E n)

def sumModulus (D E : PositiveTime) (epsilon : Q') : Nat :=
  max (approximationModulus D (HalfPow.half*epsilon)) (approximationModulus E (HalfPow.half*epsilon))

theorem half_sum_bound (a b c d epsilon : Q')
    (hab : a ≤ b + HalfPow.half*epsilon) (hcd : c ≤ d + HalfPow.half*epsilon) :
    a+c ≤ (b+d)+epsilon :=
  Q'.le_trans' _ _ _ (Q'.add_le_add hab hcd)
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (Q'.regroup b d (HalfPow.half*epsilon))
      (Q'.add_eqv_congr_left _ _ _ (ExpNeg.two_halves epsilon))))

theorem sum_cauchy (D E : PositiveTime) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m n : Nat) (hm : sumModulus D E epsilon ≤ m) (hn : sumModulus D E epsilon ≤ n) :
    sumSample D E m ≤ sumSample D E n + epsilon ∧ sumSample D E n ≤ sumSample D E m + epsilon := by
  have hh := ExpNeg.half_mul_pos epsilon he
  have hD := approximation_cauchy D _ hh m n
    (Nat.le_trans (Nat.le_max_left _ _) hm) (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hE := approximation_cauchy E _ hh m n
    (Nat.le_trans (Nat.le_max_right _ _) hm) (Nat.le_trans (Nat.le_max_right _ _) hn)
  exact ⟨half_sum_bound _ _ _ _ epsilon hD.1 hE.1, half_sum_bound _ _ _ _ epsilon hD.2 hE.2⟩

def sumCauchy (D E : PositiveTime) : QCauchy (sumSample D E) where
  M := sumModulus D E
  bound := sum_cauchy D E

def sumReal (D E : PositiveTime) : CReal where
  approx := sumSample D E
  cauchy := fun e he => ⟨(sumCauchy D E).M e, (sumCauchy D E).bound e he⟩

theorem sum_floor_positive (D E : PositiveTime) : (0 : Q') < D.floor + E.floor :=
  Q'.add_pos D.floor_positive E.floor_positive

theorem sum_lower (D E : PositiveTime) (n : Nat) : D.floor + E.floor ≤ sumSample D E n :=
  Q'.add_le_add (approximation_lower D n) (approximation_lower E n)

def sumTime (D E : PositiveTime) : PositiveTime where
  real := sumReal D E
  cauchy := sumCauchy D E
  floor := D.floor + E.floor
  floor_positive := sum_floor_positive D E
  start := 0
  lower := fun n _ => sum_lower D E n

theorem sumTime_sample (D E : PositiveTime) (n : Nat) : sample (sumTime D E) n = sumSample D E n := by
  change sumSample D E (0+n) = sumSample D E n
  rw [Nat.zero_add]

theorem sumTime_real_equiv (D E : PositiveTime) : Equiv (sumTime D E).real (CReal.add D.real E.real) := by
  change Equiv (CReal.add (approximationReal D) (approximationReal E)) (CReal.add D.real E.real)
  exact Equiv_add (approximationReal_equiv D) (approximationReal_equiv E)

theorem sumTime_real_pin (D E : PositiveTime) :
    Quotient.mk crealSetoid (sumTime D E).real =
      RCadd (Quotient.mk crealSetoid D.real) (Quotient.mk crealSetoid E.real) :=
  Quotient.sound (sumTime_real_equiv D E)

def sumMesh (D E : PositiveTime) (n : Nat) : MeshPoint := addMesh (approximation D n) (approximation E n)

theorem sumMesh_value (D E : PositiveTime) (n : Nat) : Q'.eqv (value (sumMesh D E n)) (sumSample D E n) :=
  value_addMesh _ _

theorem sumMesh_lower (D E : PositiveTime) (n : Nat) : D.floor + E.floor ≤ value (sumMesh D E n) :=
  Q'.le_trans' _ _ _ (sum_lower D E n) (Q'.ge_of_eqv (sumMesh_value D E n))

theorem sumMesh_cauchy (D E : PositiveTime) (epsilon : Q') (he : (0 : Q') < epsilon)
    (m n : Nat) (hm : sumModulus D E epsilon ≤ m) (hn : sumModulus D E epsilon ≤ n) :
    value (sumMesh D E m) ≤ value (sumMesh D E n) + epsilon ∧
    value (sumMesh D E n) ≤ value (sumMesh D E m) + epsilon := by
  have h := sum_cauchy D E epsilon he m n hm hn
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv (sumMesh_value D E m))
      (Q'.le_trans' _ _ _ h.1 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (sumMesh_value D E n)))),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (sumMesh_value D E n))
      (Q'.le_trans' _ _ _ h.2 (Q'.add_le_add_right _ _ _ (Q'.ge_of_eqv (sumMesh_value D E m))))⟩

end YMGap.Continuum.PositiveRealDyadicTimeAddition

#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.value_addMesh
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sumSample
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sumModulus
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.half_sum_bound
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sum_cauchy
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sumCauchy
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sumReal
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sum_floor_positive
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sum_lower
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sumTime
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sumTime_sample
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sumTime_real_equiv
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sumTime_real_pin
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sumMesh
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sumMesh_value
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sumMesh_lower
#print axioms YMGap.Continuum.PositiveRealDyadicTimeAddition.sumMesh_cauchy
