/-
# Actual fixed-base Wilson completions map into the spatial union

Each supplied Cauchy term is included as its literal fixed-base Stage.
The proved same-distance pin preserves both its Cauchy modulus and every
supplied closeness modulus verbatim. Quotient descent selects no quotient
representative. Uniqueness of the two actual pairing limits identifies the
image's completed mixed pairing with the existing fixed-base Wilson pairing,
despite their separately computed scalar representative moduli.

The map intertwines the original physical time and preserves unit and zero
as classes of the SAME spatial-union completion. This does not assert that
an arbitrary union stream has a common base, that this map is surjective,
or that a continuum/all-group Yang--Mills theory has been constructed.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionPairingData
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedTime
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedPosdef

namespace YMGap.Continuum.BF4WilsonSpatialUnionFixedBase

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (seminorm distSq_refl)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner (Completion embed)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1) {base : Nat} (hb : 0<base)

local notation "F" => seminorm hw0 hw1 hsmall hd hs hb
local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs
local notation "VF" => Completion hw0 hw1 hsmall hd hs hb
local notation "VU" => UnionCompletion hw0 hw1 hsmall hd hs
local notation "PU" => BF4WilsonSpatialUnionPairingData.pairingData hw0 hw1 hsmall hd hs
local notation "PF" => BF4ExactSlabFixedSpatialWilsonCompletedInner.pairingData hw0 hw1 hsmall hd hs hb
local notation "BU" => BF4WilsonSpatialUnionPairingData.completedInner hw0 hw1 hsmall hd hs
local notation "BF" => BF4ExactSlabFixedSpatialWilsonCompletedInner.completedInner hw0 hw1 hsmall hd hs hb
local notation "TF" => BF4ExactSlabFixedSpatialWilsonCompletedTime.completedTime hw0 hw1 hsmall hd hs hb

/-- Original stream and original modulus, now as literal fixed-base stages. -/
def liftCauchy (X : (F).Cauchy) : (D).Cauchy where
  seq n := ofExpression base hb (X.seq n)
  modulus := X.modulus
  isCauchy := by
    intro epsilon he m n hm hn
    exact leEv_trans (leEv_of_equiv
      (distSq_ofExpression hw0 hw1 hsmall hd hs base hb (X.seq m) (X.seq n)))
      (X.isCauchy epsilon he m n hm hn)

theorem liftCauchy_seq (X : (F).Cauchy) (n : Nat) :
    (liftCauchy hw0 hw1 hsmall hd hs hb X).seq n = ofExpression base hb (X.seq n) := rfl

theorem liftCauchy_modulus (X : (F).Cauchy) :
    (liftCauchy hw0 hw1 hsmall hd hs hb X).modulus = X.modulus := rfl

/-- The closeness witness stays Type-valued with its original explicit rate. -/
def liftClose {X Y : (F).Cauchy} (h : (F).Close X Y) :
    (D).Close (liftCauchy hw0 hw1 hsmall hd hs hb X)
      (liftCauchy hw0 hw1 hsmall hd hs hb Y) where
  modulus := h.modulus
  close := by
    intro epsilon he n hn
    exact leEv_trans (leEv_of_equiv
      (distSq_ofExpression hw0 hw1 hsmall hd hs base hb (X.seq n) (Y.seq n)))
      (h.close epsilon he n hn)

theorem liftClose_modulus {X Y : (F).Cauchy} (h : (F).Close X Y) :
    (liftClose hw0 hw1 hsmall hd hs hb h).modulus = h.modulus := rfl

/-- Quotient descent uses the supplied witness; no representative is chosen. -/
def completionMap : VF → VU :=
  Quotient.lift
    (fun X => Quotient.mk (D).completionSetoid (liftCauchy hw0 hw1 hsmall hd hs hb X))
    (fun _ _ h => by
      rcases h with ⟨h⟩
      exact Quotient.sound ⟨liftClose hw0 hw1 hsmall hd hs hb h⟩)

theorem completionMap_mk (X : (F).Cauchy) :
    completionMap hw0 hw1 hsmall hd hs hb (Quotient.mk (F).completionSetoid X) =
      Quotient.mk (D).completionSetoid (liftCauchy hw0 hw1 hsmall hd hs hb X) := rfl

theorem map_embed (x : IntrinsicExpression base) :
    completionMap hw0 hw1 hsmall hd hs hb (embed hw0 hw1 hsmall hd hs hb x) =
      embedStage hw0 hw1 hsmall hd hs (ofExpression base hb x) := rfl

/-- Actual per-term pairings pin the two separately constructed scalar limits. -/
theorem representativeInner_map (X Y : (F).Cauchy) :
    Equiv
      (CRealSeminormPairingCompletion.representativeInner PU
        (liftCauchy hw0 hw1 hsmall hd hs hb X) (liftCauchy hw0 hw1 hsmall hd hs hb Y))
      (BF4ExactSlabFixedSpatialWilsonCompletedInner.representativeInner hw0 hw1 hsmall hd hs hb X Y) :=
  Equiv_of_limit_of_equal
    (fun n => pairing_ofExpression hw0 hw1 hsmall hd hs base hb (X.seq n) (Y.seq n))
    (CRealSeminormPairingCompletion.pairSequence_converges PU
      (liftCauchy hw0 hw1 hsmall hd hs hb X) (liftCauchy hw0 hw1 hsmall hd hs hb Y))
    (CRealSeminormPairingCompletion.pairSequence_converges PF X Y)

/-- The image has exactly the existing fixed-base completed mixed pairing. -/
theorem completedInner_map (x y : VF) :
    BU (completionMap hw0 hw1 hsmall hd hs hb x)
      (completionMap hw0 hw1 hsmall hd hs hb y) = BF x y := by
  refine Quotient.inductionOn₂ x y ?_
  exact fun X Y => Quotient.sound (representativeInner_map hw0 hw1 hsmall hd hs hb X Y)

/-- Both stream operations retain the SAME terms and moduli. -/
theorem completionMap_time (n : Nat) (x : VF) :
    completionMap hw0 hw1 hsmall hd hs hb (TF n x) =
      completedTime hw0 hw1 hsmall hd hs n (completionMap hw0 hw1 hsmall hd hs hb x) := by
  refine Quotient.inductionOn x ?_
  intro X
  rfl

/-- Units at different bases are identified by their actual null distance. -/
theorem completionMap_unit :
    completionMap hw0 hw1 hsmall hd hs hb (embed hw0 hw1 hsmall hd hs hb (unit base)) =
      completedUnit hw0 hw1 hsmall hd hs := by
  change completionMap hw0 hw1 hsmall hd hs hb
    (embed hw0 hw1 hsmall hd hs hb (unit base)) = embedStage hw0 hw1 hsmall hd hs unitStage
  rw [map_embed]
  apply (D).embedRep_eq_of_null
  have h := distSq_at_base hw0 hw1 hsmall hd hs (ofExpression base hb (unit base)) unitStage
    base (Nat.le_refl _) hb
  simp only [atBase_self, atBase_unit, ofExpression] at h
  exact h.trans (distSq_refl hw0 hw1 hsmall hd hs hb (unit base))

theorem completionMap_zero :
    completionMap hw0 hw1 hsmall hd hs hb
      (BF4ExactSlabFixedSpatialWilsonCompletedPosdef.completedZero hw0 hw1 hsmall hd hs hb) =
      embedStage hw0 hw1 hsmall hd hs zeroStage := by
  change completionMap hw0 hw1 hsmall hd hs hb
    (embed hw0 hw1 hsmall hd hs hb (zero base)) = embedStage hw0 hw1 hsmall hd hs zeroStage
  rw [map_embed]
  apply (D).embedRep_eq_of_null
  have h := distSq_at_base hw0 hw1 hsmall hd hs (ofExpression base hb (zero base)) zeroStage
    base (Nat.le_refl _) hb
  simp only [atBase_self, atBase_zero, ofExpression] at h
  exact h.trans (distSq_refl hw0 hw1 hsmall hd hs hb (zero base))

end YMGap.Continuum.BF4WilsonSpatialUnionFixedBase

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionFixedBase.liftCauchy
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionFixedBase.liftCauchy_seq
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionFixedBase.liftCauchy_modulus
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionFixedBase.liftClose
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionFixedBase.liftClose_modulus
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionFixedBase.completionMap
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionFixedBase.completionMap_mk
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionFixedBase.map_embed
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionFixedBase.representativeInner_map
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionFixedBase.completedInner_map
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionFixedBase.completionMap_time
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionFixedBase.completionMap_unit
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionFixedBase.completionMap_zero
