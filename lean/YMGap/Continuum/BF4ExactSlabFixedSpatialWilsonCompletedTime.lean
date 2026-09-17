/-
# Original discrete time on the SAME completed Wilson reflected carrier

The proved intrinsic distance contraction makes literal advance a
nonexpansive map. The existing completion construction applies it pointwise
to supplied Cauchy streams and retains their moduli verbatim. Its semigroup
laws descend to the already constructed Wilson Completion, not a new space.
The unit is fixed using its proved limiting null distance, not equality of
the source expressions' different radius tags.

The original time-sum and norm-contraction laws pass through each actual
representative pairing limit. Even-time positivity is its half-time
diagonal identity. These results do not assert one-step positivity, a
strict bound, full Hilbert completeness, uniqueness or physical spectral
identification of the fixed unit, or a continuum/all-group Yang--Mills result.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTimeContraction
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

local notation "D" => seminorm hw0 hw1 hsmall hd hs hb
local notation "PD" => pairingData hw0 hw1 hsmall hd hs hb
local notation "V" => Completion hw0 hw1 hsmall hd hs hb
local notation "B" => completedInner hw0 hw1 hsmall hd hs hb
local notation "U" => embed hw0 hw1 hsmall hd hs hb (unit base)

/-- Nonexpansiveness is the proved SAME intrinsic reflected-distance estimate. -/
def timeNonexpansive (n : Nat) : (D).Nonexpansive where
  toFun := advance n
  contraction := distSq_advance_contraction hw0 hw1 hsmall hd hs hb n

def timeSemigroup : (D).NonexpansiveSemigroup where
  op := timeNonexpansive hw0 hw1 hsmall hd hs hb
  zero_law := by
    intro x
    change Equiv (distSq hw0 hw1 hsmall hd hs hb (advance 0 x) x) czero
    rw [advance_zero]
    exact distSq_refl hw0 hw1 hsmall hd hs hb x
  add_law := by
    intro m n x
    change Equiv (distSq hw0 hw1 hsmall hd hs hb (advance (m+n) x)
      (advance m (advance n x))) czero
    rw [advance_add]
    exact distSq_refl hw0 hw1 hsmall hd hs hb _

/-- Endomorphism of the EXISTING Wilson Cauchy quotient. -/
def completedTime (n : Nat) : V → V :=
  (timeNonexpansive hw0 hw1 hsmall hd hs hb n).completionMap

local notation "T" => completedTime hw0 hw1 hsmall hd hs hb
local notation "A" n => timeNonexpansive hw0 hw1 hsmall hd hs hb n

theorem completedTime_zero (x : V) : T 0 x = x :=
  (timeSemigroup hw0 hw1 hsmall hd hs hb).completionMap_zero x

theorem completedTime_add (m n : Nat) (x : V) : T (m+n) x = T m (T n x) :=
  (timeSemigroup hw0 hw1 hsmall hd hs hb).completionMap_add m n x

theorem completedTime_embed (n : Nat) (x : IntrinsicExpression base) :
    T n (embed hw0 hw1 hsmall hd hs hb x) =
      embed hw0 hw1 hsmall hd hs hb (advance n x) := rfl

theorem time_cauchy_seq (n : Nat) (X : (D).Cauchy) (k : Nat) :
    ((A n).mapCauchy X).seq k = advance n (X.seq k) := rfl

/-- No new modulus is selected or extracted by the completed time map. -/
theorem time_cauchy_modulus (n : Nat) (X : (D).Cauchy) :
    ((A n).mapCauchy X).modulus = X.modulus := rfl

/-- The actual embedded unit is fixed modulo the SAME limiting seminorm. -/
theorem completedUnit_fixed (n : Nat) : T n U = U := by
  rw [completedTime_embed]
  exact (D).embedRep_eq_of_null (advance_unit_null hw0 hw1 hsmall hd hs hb n)

attribute [local irreducible] intrinsicForm

/-- Physical time and Cauchy approximation indices are independent parameters. -/
theorem representativeInner_time_sum (m n : Nat) (X Y : (D).Cauchy) :
    Equiv
      (representativeInner hw0 hw1 hsmall hd hs hb ((A m).mapCauchy X) ((A n).mapCauchy Y))
      (representativeInner hw0 hw1 hsmall hd hs hb X ((A (m+n)).mapCauchy Y)) := by
  have hleft := CRealSeminormPairingCompletion.pairSequence_converges PD
    ((A m).mapCauchy X) ((A n).mapCauchy Y)
  have hright := CRealSeminormPairingCompletion.pairSequence_converges PD
    X ((A (m+n)).mapCauchy Y)
  apply Equiv_of_limit_of_equal (hA := hleft) (hB := hright)
  intro k
  exact intrinsicForm_time_sum hw0 hw1 hsmall hd hs hb m n (X.seq k) (Y.seq k)

/-- Original time-sum identity on arbitrary vectors of THIS completion. -/
theorem completedInner_time_sum (m n : Nat) (x y : V) :
    B (T m x) (T n y) = B x (T (m+n) y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro X Y
  exact Quotient.sound (representativeInner_time_sum hw0 hw1 hsmall hd hs hb m n X Y)

/-- Pairing symmetry of each discrete advance, not a full spectral theorem. -/
theorem completedInner_time_balance (n : Nat) (x y : V) :
    B (T n x) y = B x (T n y) := by
  simpa only [completedTime_zero, Nat.add_zero] using
    completedInner_time_sum hw0 hw1 hsmall hd hs hb n 0 x y

theorem representativeInner_time_contraction (n : Nat) (X : (D).Cauchy) :
    leEv
      (representativeInner hw0 hw1 hsmall hd hs hb ((A n).mapCauchy X) ((A n).mapCauchy X))
      (representativeInner hw0 hw1 hsmall hd hs hb X X) := by
  have hleft := CRealSeminormPairingCompletion.pairSequence_converges PD
    ((A n).mapCauchy X) ((A n).mapCauchy X)
  have hright := CRealSeminormPairingCompletion.pairSequence_converges PD X X
  apply leEv_of_convergesTo_le hleft hright
  intro k
  exact intrinsicForm_advance_contraction hw0 hw1 hsmall hd hs hb n (X.seq k)

/-- Constant-one contraction on EVERY vector, with no strict rate asserted. -/
theorem completedInner_time_contraction (n : Nat) (x : V) :
    RCle (B (T n x) (T n x)) (B x x) := by
  refine Quotient.inductionOn x ?_
  intro X
  exact representativeInner_time_contraction hw0 hw1 hsmall hd hs hb n X

theorem completedInner_even_diagonal (n : Nat) (x : V) :
    B x (T (2*n) x) = B (T n x) (T n x) := by
  simpa only [Nat.two_mul] using
    (completedInner_time_sum hw0 hw1 hsmall hd hs hb n n x x).symm

/-- Positivity of EVEN physical times only; one-step positivity is not inferred. -/
theorem completedInner_even_nonnegative (n : Nat) (x : V) :
    RCnonneg (B x (T (2*n) x)) := by
  rw [completedInner_even_diagonal]
  exact completedInner_nonnegative hw0 hw1 hsmall hd hs hb (T n x)

theorem completedInner_even_le_identity (n : Nat) (x : V) :
    RCle (B x (T (2*n) x)) (B x x) := by
  rw [completedInner_even_diagonal]
  exact completedInner_time_contraction hw0 hw1 hsmall hd hs hb n x

/-- In particular, time preserves orthogonality to the SAME embedded unit. -/
theorem completedUnitCoefficient_time (n : Nat) (x : V) : B (T n x) U = B x U := by
  rw [completedInner_time_balance, completedUnit_fixed]

/-- Dense correlators retain the literal original distance advance. -/
theorem completedTime_correlator (n : Nat) (x y : IntrinsicExpression base) :
    B (embed hw0 hw1 hsmall hd hs hb x) (T n (embed hw0 hw1 hsmall hd hs hb y)) =
      Quotient.mk crealSetoid (intrinsicForm hw0 hw1 hsmall hd hs hb x (advance n y)) := by
  rw [completedTime_embed, completedInner_embed]

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.timeNonexpansive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.timeSemigroup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.completedTime
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.completedTime_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.completedTime_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.completedTime_embed
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.time_cauchy_seq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.time_cauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.completedUnit_fixed
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.representativeInner_time_sum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.completedInner_time_sum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.completedInner_time_balance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.representativeInner_time_contraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.completedInner_time_contraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.completedInner_even_diagonal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.completedInner_even_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.completedInner_even_le_identity
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.completedUnitCoefficient_time
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime.completedTime_correlator
