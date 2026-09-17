/-
# Completed pairing of the same intrinsic Wilson limiting form

One explicit common horizon transports the proved window estimates to the
intrinsic carrier. The generic explicit-modulus completion then constructs
the mixed scalar limit on supplied Cauchy representatives and descends it
to their SAME quotient. No representative, stream ceiling or modulus is
selected by choice. Dense embeddings retain the original limiting form.

This is the represented Cauchy completion at one fixed source base. It is
not yet a full Hilbert completeness theorem, base-union/time realization,
enlarged strict bound, full observable coverage or a continuum QFT.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowPairingContinuity
import YMGap.Continuum.CRealSeminormPairingPosdef

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedCauchySchwarz
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonReflectedFormLaws
open YMGap.Continuum.BF4ExactSlabPlaquettePairingContinuity (pairingTolerance)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)
  {base : Nat} (hb : 0<base)

local notation "F" => intrinsicForm hw0 hw1 hsmall hd hs hb
local notation "d" => distSq hw0 hw1 hsmall hd hs hb
local notation "D" => seminorm hw0 hw1 hsmall hd hs hb

private theorem sub_congr {a b c e : CReal} (ha : Equiv a b) (hc : Equiv c e) :
    Equiv (sub a c) (sub b e) := Equiv_add ha (neg_congr hc)

theorem diagonal_anchor_bound (x a : IntrinsicExpression base) :
    leEv (F x x) (add (add (d x a) (d x a)) (add (F a a) (F a a))) := by
  let H := max x.radius a.radius
  have hx : x.radius ≤ H := Nat.le_max_left _ _
  have ha : a.radius ≤ H := Nat.le_max_right _ _
  have hp := intrinsicForm_chart hw0 hw1 hsmall hd hs hb x x H hx hx
  have hq := intrinsicForm_chart hw0 hw1 hsmall hd hs hb a a H ha ha
  have hdist := distSq_chart hw0 hw1 hsmall hd hs hb x a H hx ha
  exact leEv_trans (leEv_of_equiv hp)
    (leEv_trans
      (BF4ExactSlabFixedSpatialWilsonWindowPairingContinuity.diagonal_anchor_bound
        hw0 hw1 hsmall hd hs hb H (toWindow H x hx) (toWindow H a ha))
      (leEv_of_equiv (Equiv_add (Equiv_add hdist.symm hdist.symm) (Equiv_add hq.symm hq.symm))))

/-- One common horizon is computed from all four finite witnesses. -/
theorem pairing_close (x x' y y' : IntrinsicExpression base)
    (B : Q') (hB : (0 : Q') ≤ B) (epsilon : Q') (he : (0 : Q') < epsilon)
    (hx : leEv (d x x') (ofQ' (pairingTolerance B hB epsilon)))
    (hy : leEv (d y y') (ofQ' (pairingTolerance B hB epsilon)))
    (hynorm : leEv (F y y) (ofQ' B)) (hxnorm : leEv (F x' x') (ofQ' B)) :
    leRat (sub (F x y) (F x' y')) epsilon ∧
      leRat (sub (F x' y') (F x y)) epsilon := by
  let H := max (max x.radius x'.radius) (max y.radius y'.radius)
  have hxH : x.radius ≤ H := by dsimp [H]; omega
  have hx'H : x'.radius ≤ H := by dsimp [H]; omega
  have hyH : y.radius ≤ H := by dsimp [H]; omega
  have hy'H : y'.radius ≤ H := by dsimp [H]; omega
  have hxy := intrinsicForm_chart hw0 hw1 hsmall hd hs hb x y H hxH hyH
  have hx'y' := intrinsicForm_chart hw0 hw1 hsmall hd hs hb x' y' H hx'H hy'H
  have hdx := distSq_chart hw0 hw1 hsmall hd hs hb x x' H hxH hx'H
  have hdy := distSq_chart hw0 hw1 hsmall hd hs hb y y' H hyH hy'H
  have hyy := intrinsicForm_chart hw0 hw1 hsmall hd hs hb y y H hyH hyH
  have hxx := intrinsicForm_chart hw0 hw1 hsmall hd hs hb x' x' H hx'H hx'H
  have h := BF4ExactSlabFixedSpatialWilsonWindowPairingContinuity.pairing_close
    hw0 hw1 hsmall hd hs hb H (toWindow H x hxH) (toWindow H x' hx'H)
      (toWindow H y hyH) (toWindow H y' hy'H) B hB epsilon he
      (leEv_trans (leEv_of_equiv hdx.symm) hx)
      (leEv_trans (leEv_of_equiv hdy.symm) hy)
      (leEv_trans (leEv_of_equiv hyy.symm) hynorm)
      (leEv_trans (leEv_of_equiv hxx.symm) hxnorm)
  exact ⟨leRat_of_equiv (sub_congr hxy hx'y') h.1,
    leRat_of_equiv (sub_congr hx'y' hxy) h.2⟩

theorem intrinsicForm_cauchySchwarz (x y : IntrinsicExpression base) :
    leEv (mul (F x y) (F x y)) (mul (F x x) (F y y)) := by
  let H := max x.radius y.radius
  have hx : x.radius ≤ H := Nat.le_max_left _ _
  have hy : y.radius ≤ H := Nat.le_max_right _ _
  have hxy := intrinsicForm_chart hw0 hw1 hsmall hd hs hb x y H hx hy
  have hxx := intrinsicForm_chart hw0 hw1 hsmall hd hs hb x x H hx hx
  have hyy := intrinsicForm_chart hw0 hw1 hsmall hd hs hb y y H hy hy
  exact leEv_trans (leEv_of_equiv (Pivot2.mul_congr hxy hxy))
    (leEv_trans (spatialLimit_cauchySchwarz hw0 hw1 hsmall hd hs hb H
      (chart H x) (chart H y) (chart_within H x hx) (chart_within H y hy))
      (leEv_of_equiv (Pivot2.mul_congr hxx.symm hyy.symm)))

/-- All quantitative fields are actual theorems for this original form. -/
def pairingData : CRealSeminormPairingCompletion.PairingData D where
  pairing := F
  pairingCauchy := intrinsicFormCauchy hw0 hw1 hsmall hd hs hb
  diagonal_anchor_bound := diagonal_anchor_bound hw0 hw1 hsmall hd hs hb
  pairing_close := pairing_close hw0 hw1 hsmall hd hs hb

abbrev Completion := (D).Completion

def embed (x : IntrinsicExpression base) : Completion hw0 hw1 hsmall hd hs hb :=
  (D).embedRep x

/-- Scalar representatives and their approximation moduli are computed by
the existing generic construction from the supplied vector Cauchy data. -/
def representativeInner (X Y : (D).Cauchy) : CReal :=
  CRealSeminormPairingCompletion.representativeInner (pairingData hw0 hw1 hsmall hd hs hb) X Y

def representativeInnerCauchy (X Y : (D).Cauchy) :
    QCauchy (representativeInner hw0 hw1 hsmall hd hs hb X Y).approx :=
  CRealSeminormPairingCompletion.representativeInnerCauchy (pairingData hw0 hw1 hsmall hd hs hb) X Y

def completedInner : Completion hw0 hw1 hsmall hd hs hb → Completion hw0 hw1 hsmall hd hs hb → RC :=
  CRealSeminormPairingCompletion.completedInner (pairingData hw0 hw1 hsmall hd hs hb)

theorem completedInner_embed (x y : IntrinsicExpression base) :
    completedInner hw0 hw1 hsmall hd hs hb (embed hw0 hw1 hsmall hd hs hb x)
      (embed hw0 hw1 hsmall hd hs hb y) = Quotient.mk crealSetoid (F x y) :=
  CRealSeminormPairingCompletion.completedInner_embedRep (pairingData hw0 hw1 hsmall hd hs hb) x y

theorem completedInner_symm (x y : Completion hw0 hw1 hsmall hd hs hb) :
    completedInner hw0 hw1 hsmall hd hs hb x y = completedInner hw0 hw1 hsmall hd hs hb y x :=
  CRealSeminormPairingCompletion.completedInner_symm (pairingData hw0 hw1 hsmall hd hs hb)
    (intrinsicForm_symm hw0 hw1 hsmall hd hs hb) x y

theorem completedInner_nonnegative (x : Completion hw0 hw1 hsmall hd hs hb) :
    RCnonneg (completedInner hw0 hw1 hsmall hd hs hb x x) :=
  CRealSeminormPairingCompletion.completedInner_nonnegative (pairingData hw0 hw1 hsmall hd hs hb)
    (intrinsicForm_nonnegative hw0 hw1 hsmall hd hs hb) x

theorem completedInner_unit_unit :
    completedInner hw0 hw1 hsmall hd hs hb (embed hw0 hw1 hsmall hd hs hb (unit base))
      (embed hw0 hw1 hsmall hd hs hb (unit base)) = Quotient.mk crealSetoid cone :=
  CRealSeminormPairingCompletion.completedInner_unit_norm_one (pairingData hw0 hw1 hsmall hd hs hb)
    (unit base) (intrinsicForm_unit_unit hw0 hw1 hsmall hd hs hb)

theorem completedInner_cauchySchwarz (x y : Completion hw0 hw1 hsmall hd hs hb) :
    RCle (RCmul (completedInner hw0 hw1 hsmall hd hs hb x y) (completedInner hw0 hw1 hsmall hd hs hb x y))
      (RCmul (completedInner hw0 hw1 hsmall hd hs hb x x) (completedInner hw0 hw1 hsmall hd hs hb y y)) :=
  CRealSeminormPairingCompletion.completedInner_cauchySchwarz (pairingData hw0 hw1 hsmall hd hs hb)
    (intrinsicForm_cauchySchwarz hw0 hw1 hsmall hd hs hb) x y

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.diagonal_anchor_bound
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.pairing_close
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.intrinsicForm_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.pairingData
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.Completion
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.embed
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.representativeInner
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.representativeInnerCauchy
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.completedInner
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.completedInner_embed
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.completedInner_symm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.completedInner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.completedInner_unit_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCompletedInner.completedInner_cauchySchwarz
