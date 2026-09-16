/-
# Actual quantitative union form and its completed pairing

Every generic pairing-completion field is supplied here by the original
spatial-limit form in an explicit common base. No analytic certificate is
left as a hypothesis. The resulting completed pairing is on the SAME union
Cauchy carrier and accommodates growing supports. Symmetry, positivity and
unit normalization are inherited; full Hilbert/QFT structure remains open.
-/

import YMGap.Continuum.BF4SpatialUnionSeminorm
import YMGap.Continuum.CRealSeminormPairingCompletion
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingBounds
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingContinuity

namespace YMGap.Continuum.BF4SpatialUnionPairingData

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4SpatialUnion
open YMGap.Continuum.BF4SpatialUnionSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPhysicalTime (spatialPairing_time_balance)
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (pairingTolerance)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

local notation "P" => pairing hw0 hw1 hsmall hd hs
local notation "d" => distSq hw0 hw1 hsmall hd hs
local notation "D" => unionSeminorm hw0 hw1 hsmall hd hs

attribute [local irreducible] pairing distSq spatialPairing spatialDistSq

theorem pairing_symm (x y : Stage) : Equiv (P x y) (P y x) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  exact (pairing_at_base hw0 hw1 hsmall hd hs x y N hx hy).trans
    ((spatialPairing_symm hw0 hw1 N hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
      (atBase x hx) (atBase y hy)).trans
      (pairing_at_base hw0 hw1 hsmall hd hs y x N hy hx).symm)

theorem pairing_nonnegative (x : Stage) : leEv czero (P x x) := by
  unfold pairing
  exact spatialPairing_nonnegative hw0 hw1 _ hsmall hd hs _ _

theorem pairing_unit_unit : Equiv (P unitStage unitStage) cone :=
  (pairing_ofSpan hw0 hw1 hsmall hd hs 1 (by decide) _ _).trans
    (spatialPairing_unit_unit hw0 hw1 1 hsmall hd hs (by decide))

theorem pairing_anchor (x a : Stage) :
    leEv (P x x) (add (add (d x a) (d x a)) (add (P a a) (P a a))) := by
  let N := max x.base a.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have ha : a.base ≤ N := Nat.le_max_right _ _
  have hdxa := distSq_at_base hw0 hw1 hsmall hd hs x a N hx ha
  have haa := pairing_at_base hw0 hw1 hsmall hd hs a a N ha ha
  exact leEv_trans (leEv_of_equiv (pairing_at_base hw0 hw1 hsmall hd hs x x N hx hx))
    (leEv_trans (BF4ExactSlabFixedSpatialSpatialPairingBounds.diagonal_anchor_bound
      hw0 hw1 N hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx) (atBase a ha))
      (leEv_of_equiv (Equiv_add (Equiv_add hdxa hdxa) (Equiv_add haa haa)).symm))

/-- Quantitative continuity uses one common base for the FOUR actual inputs. -/
theorem pairing_close (x x' y y' : Stage) (B : Q') (hB : (0 : Q') ≤ B)
    (epsilon : Q') (he : (0 : Q') < epsilon)
    (hx : leEv (d x x') (ofQ' (pairingTolerance B hB epsilon)))
    (hy : leEv (d y y') (ofQ' (pairingTolerance B hB epsilon)))
    (hynorm : leEv (P y y) (ofQ' B)) (hxnorm : leEv (P x' x') (ofQ' B)) :
    leRat (sub (P x y) (P x' y')) epsilon ∧ leRat (sub (P x' y') (P x y)) epsilon := by
  let N := max (max x.base x'.base) (max y.base y'.base)
  have hxN : x.base ≤ N := by omega
  have hxN' : x'.base ≤ N := by omega
  have hyN : y.base ≤ N := by omega
  have hyN' : y'.base ≤ N := by omega
  have hxx := leEv_trans
    (leEv_of_equiv (distSq_at_base hw0 hw1 hsmall hd hs x x' N hxN hxN').symm) hx
  have hyy := leEv_trans
    (leEv_of_equiv (distSq_at_base hw0 hw1 hsmall hd hs y y' N hyN hyN').symm) hy
  have hny := leEv_trans
    (leEv_of_equiv (pairing_at_base hw0 hw1 hsmall hd hs y y N hyN hyN).symm) hynorm
  have hnx := leEv_trans
    (leEv_of_equiv (pairing_at_base hw0 hw1 hsmall hd hs x' x' N hxN' hxN').symm) hxnorm
  have h := BF4ExactSlabFixedSpatialSpatialPairingContinuity.pairing_close hw0 hw1 N
    hsmall hd hs (Nat.lt_of_lt_of_le x.positive hxN)
    (atBase x hxN) (atBase x' hxN') (atBase y hyN) (atBase y' hyN')
    B hB epsilon he hxx hyy hny hnx
  have hxy := pairing_at_base hw0 hw1 hsmall hd hs x y N hxN hyN
  have hxy' := pairing_at_base hw0 hw1 hsmall hd hs x' y' N hxN' hyN'
  exact ⟨leRat_of_equiv (Equiv_add hxy (neg_congr hxy')) h.1,
    leRat_of_equiv (Equiv_add hxy' (neg_congr hxy)) h.2⟩

/-- An actual instance: every quantitative field is discharged above. -/
def pairingData : CRealSeminormPairingCompletion.PairingData (D) where
  pairing := P
  pairingCauchy := pairingCauchy hw0 hw1 hsmall hd hs
  diagonal_anchor_bound := pairing_anchor hw0 hw1 hsmall hd hs
  pairing_close := pairing_close hw0 hw1 hsmall hd hs

def completedInner : UnionCompletion hw0 hw1 hsmall hd hs → UnionCompletion hw0 hw1 hsmall hd hs → RC :=
  CRealSeminormPairingCompletion.completedInner (pairingData hw0 hw1 hsmall hd hs)

theorem completedInner_embedStage (x y : Stage) :
    completedInner hw0 hw1 hsmall hd hs (embedStage hw0 hw1 hsmall hd hs x)
      (embedStage hw0 hw1 hsmall hd hs y) = Quotient.mk crealSetoid (P x y) :=
  CRealSeminormPairingCompletion.completedInner_embedRep (pairingData hw0 hw1 hsmall hd hs) x y

theorem completedInner_symm (x y : UnionCompletion hw0 hw1 hsmall hd hs) :
    completedInner hw0 hw1 hsmall hd hs x y = completedInner hw0 hw1 hsmall hd hs y x :=
  CRealSeminormPairingCompletion.completedInner_symm (pairingData hw0 hw1 hsmall hd hs)
    (pairing_symm hw0 hw1 hsmall hd hs) x y

theorem completedInner_nonnegative (x : UnionCompletion hw0 hw1 hsmall hd hs) :
    RCnonneg (completedInner hw0 hw1 hsmall hd hs x x) :=
  CRealSeminormPairingCompletion.completedInner_nonnegative (pairingData hw0 hw1 hsmall hd hs)
    (pairing_nonnegative hw0 hw1 hsmall hd hs) x

theorem completedUnit_norm_one :
    completedInner hw0 hw1 hsmall hd hs (completedUnit hw0 hw1 hsmall hd hs)
      (completedUnit hw0 hw1 hsmall hd hs) = Quotient.mk crealSetoid cone :=
  (completedInner_embedStage hw0 hw1 hsmall hd hs unitStage unitStage).trans
    (Quotient.sound (pairing_unit_unit hw0 hw1 hsmall hd hs))

end YMGap.Continuum.BF4SpatialUnionPairingData

#print axioms YMGap.Continuum.BF4SpatialUnionPairingData.pairing_symm
#print axioms YMGap.Continuum.BF4SpatialUnionPairingData.pairing_nonnegative
#print axioms YMGap.Continuum.BF4SpatialUnionPairingData.pairing_unit_unit
#print axioms YMGap.Continuum.BF4SpatialUnionPairingData.pairing_anchor
#print axioms YMGap.Continuum.BF4SpatialUnionPairingData.pairing_close
#print axioms YMGap.Continuum.BF4SpatialUnionPairingData.pairingData
#print axioms YMGap.Continuum.BF4SpatialUnionPairingData.completedInner
#print axioms YMGap.Continuum.BF4SpatialUnionPairingData.completedInner_embedStage
#print axioms YMGap.Continuum.BF4SpatialUnionPairingData.completedInner_symm
#print axioms YMGap.Continuum.BF4SpatialUnionPairingData.completedInner_nonnegative
#print axioms YMGap.Continuum.BF4SpatialUnionPairingData.completedUnit_norm_one
