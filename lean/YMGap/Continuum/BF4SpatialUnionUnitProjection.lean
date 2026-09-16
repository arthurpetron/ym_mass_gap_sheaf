/-
# Computed projection onto the actual spatial-union unit

The actual completed unit coefficient has explicit rational approximation
data. Rational multiples of the original unit form a Cauchy stream whose
squared distances are exactly the squared coefficient differences. This
constructs the projection without a general real-scalar action, a common
support bound for the input stream, or selection of quotient representatives.

The projection descends onto the SAME union completion. Its pairing,
idempotence and physical-time identities concern the original limiting
form and time map; no continuum or metric-completeness claim is made.
-/

import YMGap.Continuum.BF4SpatialUnionBilinear
import YMGap.Continuum.BF4SpatialUnionGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream

namespace YMGap.Continuum.BF4SpatialUnionUnitProjection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnion
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4SpatialUnionPairingData
  (pairingData completedInner completedInner_symm completedUnit_norm_one)
open YMGap.Continuum.BF4SpatialUnionGeometry
  (completedZero completedInner_cauchySchwarz completedInner_time_balance completedUnitCoefficient_time)
open YMGap.Continuum.BF4SpatialUnionBilinear
  (completed_eq_of_pairings completedInner_zero_left)
open YMGap.Continuum.CRealSeminormPairingCompletion
  (representativeInner representativeInnerCauchy pairSequence_converges)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear (smulSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
  (inclusion_smul inclusion_unit inclusion_refl)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
  (spatialPairing spatialPairing_smul_left spatialPairing_smul_right
    spatialPairing_unit_unit spatialPairing_difference_diagonal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredStream
  (centerTolerance centerTolerance_positive coefficient_square_bound)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- Literal rational multiples of the original unit, all in positive base 1. -/
def unitMultiple (q : Q') : Stage := ofSpan 1 (by decide) (smulSpan q (unit 1))

theorem time_unitMultiple (n : Nat) (q : Q') : time n (unitMultiple q) = unitMultiple q := rfl

private theorem sub_congr {a b c d : CReal} (h : Equiv a b) (k : Equiv c d) :
    Equiv (sub a c) (sub b d) := Equiv_add h (neg_congr k)

private theorem rc_mul_one (a : RC) : RCmul a (Quotient.mk crealSetoid cone) = a := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound (CRealAlg.cmul_cone A)

private theorem rc_one_mul (a : RC) : RCmul (Quotient.mk crealSetoid cone) a = a := by
  rw [RCmul_comm, rc_mul_one]

private theorem rc_zero_mul (a : RC) : RCmul RCzero a = RCzero := by
  refine Quotient.inductionOn a ?_
  exact fun A => Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv (A.approx n)))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "PD" => pairingData hw0 hw1 hsmall hd hs
local notation "P" => pairing hw0 hw1 hsmall hd hs
local notation "B" => completedInner hw0 hw1 hsmall hd hs
local notation "U" => completedUnit hw0 hw1 hsmall hd hs
local notation "T" => completedTime hw0 hw1 hsmall hd hs

/-- The second input may have any finite support base. -/
theorem unitMultiple_pairing (q : Q') (y : Stage) :
    Equiv (P (unitMultiple q) y) (mul (ofQ' q) (P unitStage y)) := by
  have h := pairing_at_base hw0 hw1 hsmall hd hs (unitMultiple q) y
    y.base y.positive (Nat.le_refl _)
  simp only [atBase, unitMultiple, ofSpan, inclusion_smul, inclusion_unit, inclusion_refl] at h
  have hu := pairing_at_base hw0 hw1 hsmall hd hs unitStage y
    y.base y.positive (Nat.le_refl _)
  simp only [atBase_unit, atBase_self] at hu
  exact h.trans ((spatialPairing_smul_left hw0 hw1 y.base hsmall hd hs y.positive
    q (unit y.base) y.value).trans (TrigSignedAdd.mul_congr_right hu.symm))

private theorem unit_pair (q r : Q') :
    Equiv (spatialPairing hw0 hw1 1 hsmall hd hs (by decide)
      (smulSpan q (unit 1)) (smulSpan r (unit 1))) (ofQ' (q*r)) := by
  have h := (spatialPairing_smul_left hw0 hw1 1 hsmall hd hs (by decide)
      q (unit 1) (smulSpan r (unit 1))).trans
    (TrigSignedAdd.mul_congr_right
      ((spatialPairing_smul_right hw0 hw1 1 hsmall hd hs (by decide) r (unit 1) (unit 1)).trans
        ((TrigSignedAdd.mul_congr_right
          (spatialPairing_unit_unit hw0 hw1 1 hsmall hd hs (by decide))).trans
          (CRealAlg.cmul_cone (ofQ' r)))))
  exact h.trans (SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _))

/-- Exact coefficient-square distance in the SAME union seminorm. -/
theorem unitMultiple_distance (q r : Q') :
    Equiv (distSq hw0 hw1 hsmall hd hs (unitMultiple q) (unitMultiple r))
      (ofQ' ((q + -r)^2)) := by
  have h := (distSq_ofSpan hw0 hw1 hsmall hd hs 1 (by decide)
      (smulSpan q (unit 1)) (smulSpan r (unit 1))).trans
    (spatialPairing_difference_diagonal hw0 hw1 1 hsmall hd hs (by decide)
      (smulSpan q (unit 1)) (smulSpan r (unit 1)))
  have hfour := sub_congr
    (sub_congr (unit_pair hw0 hw1 hsmall hd hs q q) (unit_pair hw0 hw1 hsmall hd hs q r))
    (sub_congr (unit_pair hw0 hw1 hsmall hd hs r q) (unit_pair hw0 hw1 hsmall hd hs r r))
  refine h.trans (hfour.trans ?_)
  apply SumOfSquares.Equiv_of_approx_eqv
  intro k
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.var 0)) (.neg (.mul (.var 0) (.var 1))))
      (.neg (.add (.mul (.var 1) (.var 0)) (.neg (.mul (.var 1) (.var 1))))))
    (.mul (.add (.var 0) (.neg (.var 1)))
      (.mul (.add (.var 0) (.neg (.var 1))) (.const 1)))
    (by decide) (fun i => if i = 0 then q else r)

/-- A supplied scalar modulus constructs its actual multiple of the unit. -/
def scalarUnitCauchy (s : CReal) (cs : QCauchy s.approx) : (D).Cauchy where
  seq n := unitMultiple (s.approx n)
  modulus epsilon := cs.M (centerTolerance epsilon)
  isCauchy := by
    intro epsilon he m n hm hn
    have h := cs.bound (centerTolerance epsilon) (centerTolerance_positive he) m n hm hn
    exact leEv_trans (leEv_of_equiv (unitMultiple_distance hw0 hw1 hsmall hd hs _ _))
      (leEv_of_le (ofQ'_le_ofQ' (coefficient_square_bound he h)))

theorem scalarUnitCauchy_modulus (s : CReal) (cs : QCauchy s.approx) :
    (scalarUnitCauchy hw0 hw1 hsmall hd hs s cs).modulus =
      fun epsilon => cs.M (centerTolerance epsilon) := rfl

def unitCauchy : (D).Cauchy := (D).constant unitStage

def unitCoefficient (X : (D).Cauchy) : CReal := representativeInner PD X (unitCauchy hw0 hw1 hsmall hd hs)

def unitCoefficientCauchy (X : (D).Cauchy) :
    QCauchy (unitCoefficient hw0 hw1 hsmall hd hs X).approx :=
  representativeInnerCauchy PD X (unitCauchy hw0 hw1 hsmall hd hs)

theorem unitCoefficient_pin (X : (D).Cauchy) :
    Quotient.mk crealSetoid (unitCoefficient hw0 hw1 hsmall hd hs X) =
      B (Quotient.mk (D).completionSetoid X) U := rfl

theorem scalarUnit_representative_pairing (s : CReal) (cs : QCauchy s.approx) (Y : (D).Cauchy) :
    Equiv (representativeInner PD (scalarUnitCauchy hw0 hw1 hsmall hd hs s cs) Y)
      (mul s (representativeInner PD (unitCauchy hw0 hw1 hsmall hd hs) Y)) :=
  Equiv_of_limit_of_equal
    (fun n => unitMultiple_pairing hw0 hw1 hsmall hd hs (s.approx n) (Y.seq n))
    (pairSequence_converges PD (scalarUnitCauchy hw0 hw1 hsmall hd hs s cs) Y)
    (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
      (CReal.convergesTo_self s) (pairSequence_converges PD (unitCauchy hw0 hw1 hsmall hd hs) Y))

theorem scalarUnitCauchy_pairing (s : CReal) (cs : QCauchy s.approx)
    (y : UnionCompletion hw0 hw1 hsmall hd hs) :
    B (Quotient.mk (D).completionSetoid (scalarUnitCauchy hw0 hw1 hsmall hd hs s cs)) y =
      RCmul (Quotient.mk crealSetoid s) (B U y) := by
  refine Quotient.inductionOn y ?_
  exact fun Y => Quotient.sound (scalarUnit_representative_pairing hw0 hw1 hsmall hd hs s cs Y)

def unitProjectionCauchy (X : (D).Cauchy) : (D).Cauchy :=
  scalarUnitCauchy hw0 hw1 hsmall hd hs
    (unitCoefficient hw0 hw1 hsmall hd hs X) (unitCoefficientCauchy hw0 hw1 hsmall hd hs X)

theorem unitProjectionCauchy_pairing (X : (D).Cauchy) (y : UnionCompletion hw0 hw1 hsmall hd hs) :
    B (Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 hsmall hd hs X)) y =
      RCmul (B (Quotient.mk (D).completionSetoid X) U) (B U y) :=
  scalarUnitCauchy_pairing hw0 hw1 hsmall hd hs _ _ y

theorem unitProjectionCauchy_congr (X Y : (D).Cauchy)
    (h : Quotient.mk (D).completionSetoid X = Quotient.mk (D).completionSetoid Y) :
    Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 hsmall hd hs X) =
      Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 hsmall hd hs Y) := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro z
  rw [unitProjectionCauchy_pairing, unitProjectionCauchy_pairing, h]

/-- Choice-free descent onto the SAME union completion. -/
def unitProjection : UnionCompletion hw0 hw1 hsmall hd hs → UnionCompletion hw0 hw1 hsmall hd hs :=
  Quotient.lift (fun X => Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 hsmall hd hs X))
    (fun X Y h => unitProjectionCauchy_congr hw0 hw1 hsmall hd hs X Y (Quotient.sound h))

theorem unitProjection_mk (X : (D).Cauchy) :
    unitProjection hw0 hw1 hsmall hd hs (Quotient.mk (D).completionSetoid X) =
      Quotient.mk (D).completionSetoid (unitProjectionCauchy hw0 hw1 hsmall hd hs X) := rfl

theorem unitProjection_pairing (x y : UnionCompletion hw0 hw1 hsmall hd hs) :
    B (unitProjection hw0 hw1 hsmall hd hs x) y = RCmul (B x U) (B U y) := by
  refine Quotient.inductionOn x ?_
  exact fun X => unitProjectionCauchy_pairing hw0 hw1 hsmall hd hs X y

theorem unitProjection_coefficient (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    B (unitProjection hw0 hw1 hsmall hd hs x) U = B x U := by
  rw [unitProjection_pairing, completedUnit_norm_one, rc_mul_one]

theorem unitProjection_selfAdjoint (x y : UnionCompletion hw0 hw1 hsmall hd hs) :
    B (unitProjection hw0 hw1 hsmall hd hs x) y = B x (unitProjection hw0 hw1 hsmall hd hs y) := by
  rw [completedInner_symm hw0 hw1 hsmall hd hs x, unitProjection_pairing, unitProjection_pairing,
    completedInner_symm hw0 hw1 hsmall hd hs U y, completedInner_symm hw0 hw1 hsmall hd hs U x,
    RCmul_comm]

theorem unitProjection_idempotent (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    unitProjection hw0 hw1 hsmall hd hs (unitProjection hw0 hw1 hsmall hd hs x) =
      unitProjection hw0 hw1 hsmall hd hs x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [unitProjection_pairing, unitProjection_coefficient, unitProjection_pairing]

theorem unitProjection_unit : unitProjection hw0 hw1 hsmall hd hs U = U := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [unitProjection_pairing, completedUnit_norm_one, rc_one_mul]

theorem unitProjection_inner (x y : UnionCompletion hw0 hw1 hsmall hd hs) :
    B (unitProjection hw0 hw1 hsmall hd hs x) (unitProjection hw0 hw1 hsmall hd hs y) =
      RCmul (B x U) (B U y) := by
  rw [unitProjection_pairing, completedInner_symm hw0 hw1 hsmall hd hs U,
    unitProjection_coefficient, completedInner_symm hw0 hw1 hsmall hd hs y U]

theorem unitProjection_norm_le (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    RCle (B (unitProjection hw0 hw1 hsmall hd hs x) (unitProjection hw0 hw1 hsmall hd hs x))
      (B x x) := by
  have h := completedInner_cauchySchwarz hw0 hw1 hsmall hd hs x U
  rw [completedUnit_norm_one, rc_mul_one] at h
  rw [unitProjection_inner, completedInner_symm hw0 hw1 hsmall hd hs U x]
  exact h

theorem time_unitProjection (n : Nat) (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    T n (unitProjection hw0 hw1 hsmall hd hs x) = unitProjection hw0 hw1 hsmall hd hs x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [completedInner_time_balance, unitProjection_pairing, unitProjection_pairing,
    ← completedInner_time_balance hw0 hw1 hsmall hd hs n U y, completedUnit_fixed]

theorem unitProjection_time (n : Nat) (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    unitProjection hw0 hw1 hsmall hd hs (T n x) = unitProjection hw0 hw1 hsmall hd hs x := by
  apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
  intro y
  rw [unitProjection_pairing, unitProjection_pairing, completedUnitCoefficient_time]

theorem unitProjection_zero_iff (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    unitProjection hw0 hw1 hsmall hd hs x = completedZero hw0 hw1 hsmall hd hs ↔ B x U = RCzero := by
  constructor
  · intro h
    rw [← unitProjection_coefficient hw0 hw1 hsmall hd hs x, h, completedInner_zero_left]
  · intro h
    apply completed_eq_of_pairings hw0 hw1 hsmall hd hs
    intro y
    rw [unitProjection_pairing, h, rc_zero_mul, completedInner_zero_left]

end YMGap.Continuum.BF4SpatialUnionUnitProjection

#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitMultiple
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.time_unitMultiple
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitMultiple_pairing
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitMultiple_distance
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.scalarUnitCauchy
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.scalarUnitCauchy_modulus
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitCauchy
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitCoefficient
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitCoefficientCauchy
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitCoefficient_pin
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.scalarUnit_representative_pairing
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.scalarUnitCauchy_pairing
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjectionCauchy
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjectionCauchy_pairing
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjectionCauchy_congr
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjection
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjection_mk
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjection_pairing
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjection_coefficient
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjection_selfAdjoint
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjection_idempotent
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjection_unit
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjection_inner
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjection_norm_le
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.time_unitProjection
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjection_time
#print axioms YMGap.Continuum.BF4SpatialUnionUnitProjection.unitProjection_zero_iff
