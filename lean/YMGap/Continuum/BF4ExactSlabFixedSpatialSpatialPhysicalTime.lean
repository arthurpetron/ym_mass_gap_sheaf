/-
# Physical time on the actual spatial-limit reflected completion

The literal distance advance commutes with recentering. Its proved joint
form balance, even positivity and contraction therefore pass through the
actual spatial limit. The SAME advance is nonexpansive for the new spatial
seminorm and descends through the existing explicit-modulus Cauchy quotient.
Every supplied Cauchy modulus is retained verbatim.

This completion uses finite-base physical presentations and the spatial
limiting form, not any of the finite-width completions. Base coherence,
extension of the observable algebra, a completed inner product and metric
completeness are not asserted here. Positivity is explicitly even-time;
no one-step positivity, strict infinite-volume gap or continuum limit is
inferred from nonexpansiveness.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
import YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
  (physicalTime physicalTime_zero physicalTime_add unit zero physicalTime_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPhysicalTime
  (jointPairing_time_sum jointPairing_advance_contraction jointPairing_even_nonnegative
    jointPhysicalTime_contraction)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits (jointPairing)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter
  (paddedWidth recenter recenter_time)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "P" => spatialPairing hw0 hw1 base hsmall hd hs hb
local notation "D" => spatialSeminorm hw0 hw1 base hsmall hd hs hb

attribute [local irreducible] jointPairing spatialPairing

/-- The two actual distance advances add inside the spatial limiting form. -/
theorem spatialPairing_time_sum (r s : Nat) (x y : PhysicalSpan base) :
    Equiv (P (physicalTime r x) (physicalTime s y)) (P x (physicalTime (r+s) y)) :=
  Equiv_of_limit_of_equal
    (aSeq := fun margin => jointPairing hw0 hw1 (paddedWidth base margin)
      (recenter margin (physicalTime r x)) (recenter margin (physicalTime s y)))
    (bSeq := fun margin => jointPairing hw0 hw1 (paddedWidth base margin)
      (recenter margin x) (recenter margin (physicalTime (r+s) y)))
    (fun margin => by
      simpa only [recenter_time] using
        jointPairing_time_sum hw0 hw1 (paddedWidth base margin) r s
          (recenter margin x) (recenter margin y))
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb (physicalTime r x) (physicalTime s y))
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x (physicalTime (r+s) y))

theorem spatialPairing_time_balance (n : Nat) (x y : PhysicalSpan base) :
    Equiv (P (physicalTime n x) y) (P x (physicalTime n y)) := by
  simpa only [physicalTime_zero, Nat.add_zero] using
    spatialPairing_time_sum hw0 hw1 base hsmall hd hs hb n 0 x y

/-- Fixed physical lag contraction, without a strict rate or sign restriction. -/
theorem spatialPairing_advance_contraction (n : Nat) (x : PhysicalSpan base) :
    leEv (P (physicalTime n x) (physicalTime n x)) (P x x) :=
  leEv_of_convergesTo_le
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb (physicalTime n x) (physicalTime n x))
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x x)
    (fun margin => by
      simpa only [recenter_time] using
        jointPairing_advance_contraction hw0 hw1 (paddedWidth base margin) n (recenter margin x))

/-- Site reflection supplies even-time positivity, not one-step positivity. -/
theorem spatialPairing_even_nonnegative (n : Nat) (x : PhysicalSpan base) :
    leEv czero (P x (physicalTime (2*n) x)) :=
  leEv_of_convergesTo_le (convergesTo_const czero)
    (spatialPairing_converges hw0 hw1 base hsmall hd hs hb x (physicalTime (2*n) x))
    (fun margin => by
      simpa only [recenter_time] using
        jointPairing_even_nonnegative hw0 hw1 (paddedWidth base margin) n (recenter margin x))

/-- Nonexpansiveness in the SAME spatial limiting reflected distance. -/
theorem spatialPhysicalTime_contraction (n : Nat) (x y : PhysicalSpan base) :
    leEv (spatialDistSq hw0 hw1 base hsmall hd hs hb (physicalTime n x) (physicalTime n y))
      (spatialDistSq hw0 hw1 base hsmall hd hs hb x y) :=
  leEv_of_convergesTo_le
    (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb (physicalTime n x) (physicalTime n y))
    (distSq_converges_spatial hw0 hw1 base hsmall hd hs hb x y)
    (fun margin => by
      simpa only [recenter_time] using
        jointPhysicalTime_contraction hw0 hw1 (paddedWidth base margin) n
          (recenter margin x) (recenter margin y))

def spatialTimeNonexpansive (n : Nat) : (D).Nonexpansive where
  toFun := physicalTime n
  contraction := spatialPhysicalTime_contraction hw0 hw1 base hsmall hd hs hb n

def spatialTimeSemigroup : (D).NonexpansiveSemigroup where
  op := spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb
  zero_law := by
    intro x
    change Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb (physicalTime 0 x) x) czero
    rw [physicalTime_zero]
    exact spatialDistSq_refl hw0 hw1 base hsmall hd hs hb x
  add_law := by
    intro m n x
    change Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb (physicalTime (m+n) x)
      (physicalTime m (physicalTime n x))) czero
    rw [physicalTime_add]
    exact spatialDistSq_refl hw0 hw1 base hsmall hd hs hb _

/-- The explicit-modulus Cauchy quotient of this spatial seminorm. -/
def SpatialCompletion : Type := (D).Completion

def spatialEmbedSpan (x : PhysicalSpan base) : SpatialCompletion hw0 hw1 base hsmall hd hs hb :=
  (D).embedRep x

def spatialCompletedTime (n : Nat) :
    SpatialCompletion hw0 hw1 base hsmall hd hs hb → SpatialCompletion hw0 hw1 base hsmall hd hs hb :=
  (spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).completionMap

theorem spatialCompletedTime_zero (x : SpatialCompletion hw0 hw1 base hsmall hd hs hb) :
    spatialCompletedTime hw0 hw1 base hsmall hd hs hb 0 x = x :=
  (spatialTimeSemigroup hw0 hw1 base hsmall hd hs hb).completionMap_zero x

theorem spatialCompletedTime_add (m n : Nat) (x : SpatialCompletion hw0 hw1 base hsmall hd hs hb) :
    spatialCompletedTime hw0 hw1 base hsmall hd hs hb (m+n) x =
      spatialCompletedTime hw0 hw1 base hsmall hd hs hb m
        (spatialCompletedTime hw0 hw1 base hsmall hd hs hb n x) :=
  (spatialTimeSemigroup hw0 hw1 base hsmall hd hs hb).completionMap_add m n x

theorem spatialCompletedTime_embedSpan (n : Nat) (x : PhysicalSpan base) :
    spatialCompletedTime hw0 hw1 base hsmall hd hs hb n
        (spatialEmbedSpan hw0 hw1 base hsmall hd hs hb x) =
      spatialEmbedSpan hw0 hw1 base hsmall hd hs hb (physicalTime n x) := rfl

theorem spatialTime_cauchy_seq (n : Nat) (X : (D).Cauchy) (k : Nat) :
    ((spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).mapCauchy X).seq k =
      physicalTime n (X.seq k) := rfl

/-- The supplied Cauchy modulus is retained, not selected or erased. -/
theorem spatialTime_cauchy_modulus (n : Nat) (X : (D).Cauchy) :
    ((spatialTimeNonexpansive hw0 hw1 base hsmall hd hs hb n).mapCauchy X).modulus = X.modulus := rfl

def spatialCompletedUnit : SpatialCompletion hw0 hw1 base hsmall hd hs hb :=
  spatialEmbedSpan hw0 hw1 base hsmall hd hs hb (unit base)

theorem spatialCompletedUnit_fixed (n : Nat) :
    spatialCompletedTime hw0 hw1 base hsmall hd hs hb n
        (spatialCompletedUnit hw0 hw1 base hsmall hd hs hb) =
      spatialCompletedUnit hw0 hw1 base hsmall hd hs hb := by
  unfold spatialCompletedUnit
  rw [spatialCompletedTime_embedSpan, physicalTime_unit]

/-- The original unit keeps its normalized distance from the zero presentation. -/
theorem spatialUnit_distance :
    Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb (unit base) (zero base)) (ofQ' 1) := by
  change Equiv (P (unit base) (unit base)) (ofQ' 1)
  exact spatialPairing_unit_unit hw0 hw1 base hsmall hd hs hb

/-- Equality of embedded constants forces nullity in the actual limiting distance. -/
theorem spatialEmbedSpan_eq_implies_null (x y : PhysicalSpan base)
    (h : spatialEmbedSpan hw0 hw1 base hsmall hd hs hb x =
      spatialEmbedSpan hw0 hw1 base hsmall hd hs hb y) :
    Equiv (spatialDistSq hw0 hw1 base hsmall hd hs hb x y) czero := by
  obtain ⟨hc⟩ := Quotient.exact h
  have hu : leEv (spatialDistSq hw0 hw1 base hsmall hd hs hb x y) czero := by
    intro epsilon he
    have hh := ExpNeg.half_mul_pos epsilon he
    have hclose := hc.close (HalfPow.half*epsilon) hh
      (hc.modulus (HalfPow.half*epsilon)) (Nat.le_refl _)
    obtain ⟨N, hN⟩ := hclose (HalfPow.half*epsilon) hh
    refine ⟨N, fun n hn => ?_⟩
    exact Q'.le_trans' _ _ _ (hN n hn)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (ExpNeg.two_halves epsilon)
        (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))
  exact equiv_of_leEv_leEv hu (spatialDistSq_nonnegative hw0 hw1 base hsmall hd hs hb x y)

/-- A nonzero fixed unit, without any assertion of vacuum uniqueness. -/
theorem spatialCompletedUnit_ne_zero :
    spatialCompletedUnit hw0 hw1 base hsmall hd hs hb ≠
      spatialEmbedSpan hw0 hw1 base hsmall hd hs hb (zero base) := by
  intro h
  have hnull := spatialEmbedSpan_eq_implies_null hw0 hw1 base hsmall hd hs hb (unit base) (zero base) h
  have hbad := Equiv.trans (Equiv.symm (spatialUnit_distance hw0 hw1 base hsmall hd hs hb)) hnull
  obtain ⟨N, hN⟩ := hbad HalfPow.half (by decide)
  have hle : (1 : Q') ≤ 0+HalfPow.half := (hN N (Nat.le_refl N)).1
  exact (by decide : ¬ ((1 : Q') ≤ 0+HalfPow.half)) hle

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialPairing_time_sum
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialPairing_time_balance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialPairing_advance_contraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialPairing_even_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialPhysicalTime_contraction
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialTimeNonexpansive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialTimeSemigroup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.SpatialCompletion
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialEmbedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialCompletedTime
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialCompletedTime_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialCompletedTime_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialCompletedTime_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialTime_cauchy_seq
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialTime_cauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialCompletedUnit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialCompletedUnit_fixed
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialUnit_distance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialEmbedSpan_eq_implies_null
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime.spatialCompletedUnit_ne_zero
