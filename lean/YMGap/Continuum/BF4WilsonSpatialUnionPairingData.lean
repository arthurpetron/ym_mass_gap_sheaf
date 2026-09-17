/-
# Actual quantitative Wilson union form and its completed pairing

The original Wilson form supplies every quantitative pairing-completion
field in an explicit finite common base. Four current inputs determine the
base for continuity; no common base for an entire Cauchy stream is chosen.
The existing generic construction retains all supplied vector moduli and
computes the actual mixed scalar limit and its rational Cauchy data.

The completed pairing lives on the SAME staged Wilson Cauchy quotient.
Its dense pin, symmetry, positivity, normalized original unit and sharp
Cauchy--Schwarz inequality come from the actual limiting reflected form.
Full Hilbert completeness, full gauge-observable coverage, changing spacing
and continuum QFT are not asserted.
-/

import YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner

namespace YMGap.Continuum.BF4WilsonSpatialUnionPairingData

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSpatialUnion
open YMGap.Continuum.BF4WilsonSpatialUnionSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
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
local notation "V" => UnionCompletion hw0 hw1 hsmall hd hs

attribute [local irreducible] pairing distSq intrinsicForm

theorem pairing_symm (x y : Stage) : Equiv (P x y) (P y x) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  exact (pairing_at_base hw0 hw1 hsmall hd hs x y N hx hy).trans
    ((intrinsicForm_symm hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
      (atBase x hx) (atBase y hy)).trans
      (pairing_at_base hw0 hw1 hsmall hd hs y x N hy hx).symm)

theorem pairing_nonnegative (x : Stage) : leEv czero (P x x) := by
  unfold pairing
  exact intrinsicForm_nonnegative hw0 hw1 hsmall hd hs _ _

theorem pairing_unit_unit : Equiv (P unitStage unitStage) cone :=
  (pairing_ofExpression hw0 hw1 hsmall hd hs 1 (by decide) (unit 1) (unit 1)).trans
    (intrinsicForm_unit_unit hw0 hw1 hsmall hd hs (base := 1) (by decide))

theorem pairing_anchor (x a : Stage) :
    leEv (P x x) (add (add (d x a) (d x a)) (add (P a a) (P a a))) := by
  let N := max x.base a.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have ha : a.base ≤ N := Nat.le_max_right _ _
  have hdxa := distSq_at_base hw0 hw1 hsmall hd hs x a N hx ha
  have haa := pairing_at_base hw0 hw1 hsmall hd hs a a N ha ha
  exact leEv_trans (leEv_of_equiv (pairing_at_base hw0 hw1 hsmall hd hs x x N hx hx))
    (leEv_trans (BF4ExactSlabFixedSpatialWilsonCompletedInner.diagonal_anchor_bound
      hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx) (atBase a ha))
      (leEv_of_equiv (Equiv_add (Equiv_add hdxa hdxa) (Equiv_add haa haa)).symm))

/-- The FOUR actual finite inputs determine one common comparison base. -/
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
  have h := BF4ExactSlabFixedSpatialWilsonCompletedInner.pairing_close hw0 hw1
    hsmall hd hs (Nat.lt_of_lt_of_le x.positive hxN)
    (atBase x hxN) (atBase x' hxN') (atBase y hyN) (atBase y' hyN')
    B hB epsilon he hxx hyy hny hnx
  have hxy := pairing_at_base hw0 hw1 hsmall hd hs x y N hxN hyN
  have hxy' := pairing_at_base hw0 hw1 hsmall hd hs x' y' N hxN' hyN'
  exact ⟨leRat_of_equiv (Equiv_add hxy (neg_congr hxy')) h.1,
    leRat_of_equiv (Equiv_add hxy' (neg_congr hxy)) h.2⟩

theorem pairing_cauchySchwarz (x y : Stage) :
    leEv (mul (P x y) (P x y)) (mul (P x x) (P y y)) := by
  let N := max x.base y.base
  have hx : x.base ≤ N := Nat.le_max_left _ _
  have hy : y.base ≤ N := Nat.le_max_right _ _
  have hxy := pairing_at_base hw0 hw1 hsmall hd hs x y N hx hy
  have hxx := pairing_at_base hw0 hw1 hsmall hd hs x x N hx hx
  have hyy := pairing_at_base hw0 hw1 hsmall hd hs y y N hy hy
  exact leEv_trans (leEv_of_equiv (Pivot2.mul_congr hxy hxy))
    (leEv_trans (BF4ExactSlabFixedSpatialWilsonCompletedInner.intrinsicForm_cauchySchwarz
      hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx) (atBase y hy))
      (leEv_of_equiv (Pivot2.mul_congr hxx.symm hyy.symm)))

/-- Every quantitative field is proved for this SAME original Wilson form. -/
def pairingData : CRealSeminormPairingCompletion.PairingData (D) where
  pairing := P
  pairingCauchy := pairingCauchy hw0 hw1 hsmall hd hs
  diagonal_anchor_bound := pairing_anchor hw0 hw1 hsmall hd hs
  pairing_close := pairing_close hw0 hw1 hsmall hd hs

/-- The generic actual scalar limit of the two supplied staged streams. -/
def representativeInner (X Y : (D).Cauchy) : CReal :=
  CRealSeminormPairingCompletion.representativeInner (pairingData hw0 hw1 hsmall hd hs) X Y

/-- Rational Cauchy data are computed, never extracted from equivalence. -/
def representativeInnerCauchy (X Y : (D).Cauchy) :
    QCauchy (representativeInner hw0 hw1 hsmall hd hs X Y).approx :=
  CRealSeminormPairingCompletion.representativeInnerCauchy (pairingData hw0 hw1 hsmall hd hs) X Y

def completedInner : V → V → RC :=
  CRealSeminormPairingCompletion.completedInner (pairingData hw0 hw1 hsmall hd hs)

theorem completedInner_embedStage (x y : Stage) :
    completedInner hw0 hw1 hsmall hd hs (embedStage hw0 hw1 hsmall hd hs x)
      (embedStage hw0 hw1 hsmall hd hs y) = Quotient.mk crealSetoid (P x y) :=
  CRealSeminormPairingCompletion.completedInner_embedRep (pairingData hw0 hw1 hsmall hd hs) x y

theorem completedInner_symm (x y : V) :
    completedInner hw0 hw1 hsmall hd hs x y = completedInner hw0 hw1 hsmall hd hs y x :=
  CRealSeminormPairingCompletion.completedInner_symm (pairingData hw0 hw1 hsmall hd hs)
    (pairing_symm hw0 hw1 hsmall hd hs) x y

theorem completedInner_nonnegative (x : V) :
    RCnonneg (completedInner hw0 hw1 hsmall hd hs x x) :=
  CRealSeminormPairingCompletion.completedInner_nonnegative (pairingData hw0 hw1 hsmall hd hs)
    (pairing_nonnegative hw0 hw1 hsmall hd hs) x

theorem completedUnit_norm_one :
    completedInner hw0 hw1 hsmall hd hs (completedUnit hw0 hw1 hsmall hd hs)
      (completedUnit hw0 hw1 hsmall hd hs) = Quotient.mk crealSetoid cone :=
  (completedInner_embedStage hw0 hw1 hsmall hd hs unitStage unitStage).trans
    (Quotient.sound (pairing_unit_unit hw0 hw1 hsmall hd hs))

theorem completedInner_cauchySchwarz (x y : V) :
    RCle (RCmul (completedInner hw0 hw1 hsmall hd hs x y) (completedInner hw0 hw1 hsmall hd hs x y))
      (RCmul (completedInner hw0 hw1 hsmall hd hs x x) (completedInner hw0 hw1 hsmall hd hs y y)) :=
  CRealSeminormPairingCompletion.completedInner_cauchySchwarz (pairingData hw0 hw1 hsmall hd hs)
    (pairing_cauchySchwarz hw0 hw1 hsmall hd hs) x y

end YMGap.Continuum.BF4WilsonSpatialUnionPairingData

#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.pairing_symm
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.pairing_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.pairing_unit_unit
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.pairing_anchor
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.pairing_close
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.pairing_cauchySchwarz
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.pairingData
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.representativeInner
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.representativeInnerCauchy
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.completedInner
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.completedInner_embedStage
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.completedInner_symm
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.completedInner_nonnegative
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.completedUnit_norm_one
#print axioms YMGap.Continuum.BF4WilsonSpatialUnionPairingData.completedInner_cauchySchwarz
