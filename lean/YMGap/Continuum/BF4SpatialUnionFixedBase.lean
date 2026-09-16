/-
# Fixed-base spatial completions map into the actual union completion

Lift each supplied Cauchy term by its literal fixed-base stage. Squared
distances are preserved by the proved same-form pin, so both Cauchy and
closeness moduli are retained verbatim. Quotient descent gives an actual
map, and scalar limit uniqueness identifies its completed mixed pairing
with the already constructed fixed-base spatial pairing.

The map intertwines the actual physical times and preserves unit and zero.
It is not a choice of a common support base for arbitrary union streams,
a claim that the union completion consists of fixed-base vectors, or a
full-observable/continuum identification.
-/

import YMGap.Continuum.BF4SpatialUnionPairingData
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialGenericPairingPin

namespace YMGap.Continuum.BF4SpatialUnionFixedBase

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnion
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (base : Nat)
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) (hb : 0 < base)

local notation "F" => spatialSeminorm hw0 hw1 base hsmall hd hs hb
local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "PU" => BF4SpatialUnionPairingData.pairingData hw0 hw1 hsmall hd hs
local notation "PF" => BF4ExactSlabFixedSpatialSpatialGenericPairingPin.pairingData
  hw0 hw1 base hsmall hd hs hb
local notation "BU" => BF4SpatialUnionPairingData.completedInner hw0 hw1 hsmall hd hs
local notation "BF" => BF4ExactSlabFixedSpatialSpatialCompletedInner.completedInner
  hw0 hw1 base hsmall hd hs hb

/-- The original stream and its original modulus, now as literal union stages. -/
def liftCauchy (X : (F).Cauchy) : (D).Cauchy where
  seq n := ofSpan base hb (X.seq n)
  modulus := X.modulus
  isCauchy := by
    intro epsilon he m n hm hn
    exact leEv_trans (leEv_of_equiv
      (distSq_ofSpan hw0 hw1 hsmall hd hs base hb (X.seq m) (X.seq n)))
      (X.isCauchy epsilon he m n hm hn)

theorem liftCauchy_seq (X : (F).Cauchy) (n : Nat) :
    (liftCauchy hw0 hw1 base hsmall hd hs hb X).seq n = ofSpan base hb (X.seq n) := rfl

theorem liftCauchy_modulus (X : (F).Cauchy) :
    (liftCauchy hw0 hw1 base hsmall hd hs hb X).modulus = X.modulus := rfl

/-- Closeness witnesses remain Type-level data with the same modulus. -/
def liftClose {X Y : (F).Cauchy} (h : (F).Close X Y) :
    (D).Close (liftCauchy hw0 hw1 base hsmall hd hs hb X)
      (liftCauchy hw0 hw1 base hsmall hd hs hb Y) where
  modulus := h.modulus
  close := by
    intro epsilon he n hn
    exact leEv_trans (leEv_of_equiv
      (distSq_ofSpan hw0 hw1 hsmall hd hs base hb (X.seq n) (Y.seq n)))
      (h.close epsilon he n hn)

theorem liftClose_modulus {X Y : (F).Cauchy} (h : (F).Close X Y) :
    (liftClose hw0 hw1 base hsmall hd hs hb h).modulus = h.modulus := rfl

/-- Actual descent; no representative of a quotient is selected. -/
def completionMap : SpatialCompletion hw0 hw1 base hsmall hd hs hb →
    UnionCompletion hw0 hw1 hsmall hd hs :=
  Quotient.lift
    (fun X => Quotient.mk (D).completionSetoid (liftCauchy hw0 hw1 base hsmall hd hs hb X))
    (fun _ _ h => by
      rcases h with ⟨h⟩
      exact Quotient.sound ⟨liftClose hw0 hw1 base hsmall hd hs hb h⟩)

theorem completionMap_mk (X : (F).Cauchy) :
    completionMap hw0 hw1 base hsmall hd hs hb (Quotient.mk (F).completionSetoid X) =
      Quotient.mk (D).completionSetoid (liftCauchy hw0 hw1 base hsmall hd hs hb X) := rfl

theorem completionMap_embedSpan (x : PhysicalSpan base) :
    completionMap hw0 hw1 base hsmall hd hs hb (spatialEmbedSpan hw0 hw1 base hsmall hd hs hb x) =
      embedStage hw0 hw1 hsmall hd hs (ofSpan base hb x) := rfl

/-- Uniqueness compares the actual per-term pairings, even though the two
scalar completions use different explicitly computed inner moduli. -/
theorem representativeInner_pin (X Y : (F).Cauchy) :
    Equiv
      (CRealSeminormPairingCompletion.representativeInner PU
        (liftCauchy hw0 hw1 base hsmall hd hs hb X) (liftCauchy hw0 hw1 base hsmall hd hs hb Y))
      (BF4ExactSlabFixedSpatialSpatialPairingLimit.representativeInner
        hw0 hw1 base hsmall hd hs hb X Y) := by
  have h := Equiv_of_limit_of_equal
    (fun n => pairing_ofSpan hw0 hw1 hsmall hd hs base hb (X.seq n) (Y.seq n))
    (CRealSeminormPairingCompletion.pairSequence_converges PU
      (liftCauchy hw0 hw1 base hsmall hd hs hb X) (liftCauchy hw0 hw1 base hsmall hd hs hb Y))
    (CRealSeminormPairingCompletion.pairSequence_converges PF X Y)
  exact h.trans (BF4ExactSlabFixedSpatialSpatialGenericPairingPin.representativeInner_pin
    hw0 hw1 base hsmall hd hs hb X Y)

/-- The image has exactly the original fixed-base completed mixed pairing. -/
theorem completedInner_map (x y : SpatialCompletion hw0 hw1 base hsmall hd hs hb) :
    BU (completionMap hw0 hw1 base hsmall hd hs hb x)
        (completionMap hw0 hw1 base hsmall hd hs hb y) = BF x y := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_pin hw0 hw1 base hsmall hd hs hb X Y)

theorem completionMap_time (n : Nat) (x : SpatialCompletion hw0 hw1 base hsmall hd hs hb) :
    completionMap hw0 hw1 base hsmall hd hs hb (spatialCompletedTime hw0 hw1 base hsmall hd hs hb n x) =
      completedTime hw0 hw1 hsmall hd hs n (completionMap hw0 hw1 base hsmall hd hs hb x) := by
  refine Quotient.inductionOn x ?_
  intro X
  rfl

theorem completionMap_unit :
    completionMap hw0 hw1 base hsmall hd hs hb (spatialCompletedUnit hw0 hw1 base hsmall hd hs hb) =
      completedUnit hw0 hw1 hsmall hd hs := by
  change completionMap hw0 hw1 base hsmall hd hs hb
    (spatialEmbedSpan hw0 hw1 base hsmall hd hs hb (unit base)) =
      embedStage hw0 hw1 hsmall hd hs unitStage
  rw [completionMap_embedSpan]
  apply (D).embedRep_eq_of_null
  have h := distSq_at_base hw0 hw1 hsmall hd hs (ofSpan base hb (unit base)) unitStage
    base (Nat.le_refl _) hb
  simp only [atBase_self, atBase_unit, ofSpan] at h
  exact h.trans (spatialDistSq_refl hw0 hw1 base hsmall hd hs hb (unit base))

theorem completionMap_zero :
    completionMap hw0 hw1 base hsmall hd hs hb
      (spatialEmbedSpan hw0 hw1 base hsmall hd hs hb (zero base)) =
      embedStage hw0 hw1 hsmall hd hs zeroStage := by
  rw [completionMap_embedSpan]
  apply (D).embedRep_eq_of_null
  have h := distSq_at_base hw0 hw1 hsmall hd hs (ofSpan base hb (zero base)) zeroStage
    base (Nat.le_refl _) hb
  simp only [atBase_self, atBase_zero, ofSpan] at h
  exact h.trans (spatialDistSq_refl hw0 hw1 base hsmall hd hs hb (zero base))

#print axioms liftCauchy
#print axioms liftCauchy_seq
#print axioms liftCauchy_modulus
#print axioms liftClose
#print axioms liftClose_modulus
#print axioms completionMap
#print axioms completionMap_mk
#print axioms completionMap_embedSpan
#print axioms representativeInner_pin
#print axioms completedInner_map
#print axioms completionMap_time
#print axioms completionMap_unit
#print axioms completionMap_zero

end YMGap.Continuum.BF4SpatialUnionFixedBase
