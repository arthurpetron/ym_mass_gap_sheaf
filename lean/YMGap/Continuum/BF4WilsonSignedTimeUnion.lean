/-
# All finite spatial bases of the original signed-time observable source

A stage carries its positive spatial base and actual signed Wilson expression.
Two stages are related when their inclusions into the computed maximum base
are contextually equal. The proved inclusion reflection theorem shows that
ANY larger common base detects the same relation. Thus the actual product,
linear operations, invertible time and reflection respect one global setoid.

This is fixed-nome, discrete-time original source data, not a continuum limit
or a replacement for the physical reflected completion.
-/

import YMGap.Continuum.BF4WilsonSignedTimeBaseCoherence
import YMGap.Continuum.BF4WilsonSignedTimeContextInclusion

namespace YMGap.Continuum.BF4WilsonSignedTimeUnion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonSignedTimeExpression
open YMGap.Continuum.BF4WilsonSignedTimeExpectation
open YMGap.Continuum.BF4WilsonSignedTimeBaseInclusion
open YMGap.Continuum.BF4WilsonSignedTimeBaseCoherence
open YMGap.Continuum.BF4WilsonSignedTimeContext
open YMGap.Continuum.BF4WilsonSignedTimeContextInclusion (context_include_iff)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

structure Stage where
  base : Nat
  positive : 0 < base
  expression : Expression base

def atBase (x : Stage) {N : Nat} (hx : x.base ≤ N) : Expression N :=
  inclusion hx x.expression

theorem atBase_self (x : Stage) : atBase x (Nat.le_refl _) = x.expression :=
  inclusion_refl x.expression

theorem atBase_trans (x : Stage) {N M : Nat} (hx : x.base ≤ N) (hNM : N ≤ M) :
    inclusion hNM (atBase x hx) = atBase x (Nat.le_trans hx hNM) :=
  inclusion_trans hx hNM x.expression

def unitStage : Stage := ⟨1, by decide, .one⟩
def mulStage (x y : Stage) : Stage :=
  ⟨max x.base y.base, Nat.lt_of_lt_of_le x.positive (Nat.le_max_left _ _),
    .mul (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))⟩
def addStage (x y : Stage) : Stage :=
  ⟨max x.base y.base, Nat.lt_of_lt_of_le x.positive (Nat.le_max_left _ _),
    .add (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))⟩
def smulStage (s : Q') (x : Stage) : Stage := ⟨x.base, x.positive, .smul s x.expression⟩
def forwardStage (n : Nat) (x : Stage) : Stage := ⟨x.base, x.positive, forward n x.expression⟩
def backwardStage (n : Nat) (x : Stage) : Stage := ⟨x.base, x.positive, backward n x.expression⟩
def reflectStage (x : Stage) : Stage := ⟨x.base, x.positive, reflect x.expression⟩

theorem atBase_unit {N : Nat} (h : 1 ≤ N) : atBase unitStage h = .one := rfl
theorem atBase_mul (x y : Stage) {N : Nat} (hx : x.base ≤ N) (hy : y.base ≤ N) :
    atBase (mulStage x y) (Nat.max_le.mpr ⟨hx,hy⟩) = .mul (atBase x hx) (atBase y hy) := by
  change Expression.mul (inclusion _ (inclusion _ x.expression))
    (inclusion _ (inclusion _ y.expression)) = _
  rw [inclusion_trans, inclusion_trans]
  rfl
theorem atBase_add (x y : Stage) {N : Nat} (hx : x.base ≤ N) (hy : y.base ≤ N) :
    atBase (addStage x y) (Nat.max_le.mpr ⟨hx,hy⟩) = .add (atBase x hx) (atBase y hy) := by
  change Expression.add (inclusion _ (inclusion _ x.expression))
    (inclusion _ (inclusion _ y.expression)) = _
  rw [inclusion_trans, inclusion_trans]
  rfl
theorem atBase_smul (s : Q') (x : Stage) {N : Nat} (hx : x.base ≤ N) :
    atBase (smulStage s x) hx = .smul s (atBase x hx) := rfl
theorem atBase_forward (n : Nat) (x : Stage) {N : Nat} (hx : x.base ≤ N) :
    atBase (forwardStage n x) hx = forward n (atBase x hx) := include_forward hx n x.expression
theorem atBase_backward (n : Nat) (x : Stage) {N : Nat} (hx : x.base ≤ N) :
    atBase (backwardStage n x) hx = backward n (atBase x hx) := include_backward hx n x.expression
theorem atBase_reflect (x : Stage) {N : Nat} (hx : x.base ≤ N) :
    atBase (reflectStage x) hx = reflect (atBase x hx) := include_reflect hx x.expression

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

def Related (x y : Stage) : Prop :=
  ContextEq hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left _ _))
    (atBase x (Nat.le_max_left x.base y.base)) (atBase y (Nat.le_max_right _ _))

local notation "R" => Related hw0 hw1 hsmall hd hs

/-- Any witnessed common spatial base detects the same actual contextual relation. -/
theorem related_iff_at (x y : Stage) {N : Nat} (hx : x.base ≤ N) (hy : y.base ≤ N) :
    R x y ↔ ContextEq hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
      (atBase x hx) (atBase y hy) := by
  have h := context_include_iff hw0 hw1 hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left x.base y.base))
    (Nat.max_le.mpr ⟨hx,hy⟩)
    (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))
  simpa only [Related, atBase_trans] using h.symm

theorem related_refl (x : Stage) : R x x :=
  (related_iff_at hw0 hw1 hsmall hd hs x x (Nat.le_refl _) (Nat.le_refl _)).mpr
    (context_refl hw0 hw1 hsmall hd hs x.positive _)

theorem related_symm {x y : Stage} (h : R x y) : R y x :=
  (related_iff_at hw0 hw1 hsmall hd hs y x
    (Nat.le_max_right x.base y.base) (Nat.le_max_left _ _)).mpr
    (context_symm hw0 hw1 hsmall hd hs _ h)

theorem related_trans {x y z : Stage} (h : R x y) (k : R y z) : R x z := by
  let N := max x.base (max y.base z.base)
  have hx : x.base ≤ N := by omega
  have hy : y.base ≤ N := by omega
  have hz : z.base ≤ N := by omega
  exact (related_iff_at hw0 hw1 hsmall hd hs x z hx hz).mpr
    (context_trans hw0 hw1 hsmall hd hs _
      ((related_iff_at hw0 hw1 hsmall hd hs x y hx hy).mp h)
      ((related_iff_at hw0 hw1 hsmall hd hs y z hy hz).mp k))

theorem related_mul {a b c d : Stage} (h : R a b) (k : R c d) :
    R (mulStage a c) (mulStage b d) := by
  let N := max (max a.base b.base) (max c.base d.base)
  have ha : a.base ≤ N := by omega
  have hb : b.base ≤ N := by omega
  have hc : c.base ≤ N := by omega
  have hd' : d.base ≤ N := by omega
  apply (related_iff_at hw0 hw1 hsmall hd hs (mulStage a c) (mulStage b d)
    (Nat.max_le.mpr ⟨ha,hc⟩) (Nat.max_le.mpr ⟨hb,hd'⟩)).mpr
  rw [atBase_mul a c ha hc, atBase_mul b d hb hd']
  exact context_mul hw0 hw1 hsmall hd hs _
    ((related_iff_at hw0 hw1 hsmall hd hs a b ha hb).mp h)
    ((related_iff_at hw0 hw1 hsmall hd hs c d hc hd').mp k)

theorem related_add {a b c d : Stage} (h : R a b) (k : R c d) :
    R (addStage a c) (addStage b d) := by
  let N := max (max a.base b.base) (max c.base d.base)
  have ha : a.base ≤ N := by omega
  have hb : b.base ≤ N := by omega
  have hc : c.base ≤ N := by omega
  have hd' : d.base ≤ N := by omega
  apply (related_iff_at hw0 hw1 hsmall hd hs (addStage a c) (addStage b d)
    (Nat.max_le.mpr ⟨ha,hc⟩) (Nat.max_le.mpr ⟨hb,hd'⟩)).mpr
  rw [atBase_add a c ha hc, atBase_add b d hb hd']
  exact context_add hw0 hw1 hsmall hd hs _
    ((related_iff_at hw0 hw1 hsmall hd hs a b ha hb).mp h)
    ((related_iff_at hw0 hw1 hsmall hd hs c d hc hd').mp k)

theorem related_smul (s : Q') {x y : Stage} (h : R x y) : R (smulStage s x) (smulStage s y) :=
  context_smul hw0 hw1 hsmall hd hs _ s h

theorem related_forward (n : Nat) {x y : Stage} (h : R x y) :
    R (forwardStage n x) (forwardStage n y) := by
  change ContextEq hw0 hw1 hsmall hd hs _ (atBase (forwardStage n x) _) (atBase (forwardStage n y) _)
  rw [atBase_forward, atBase_forward]
  exact context_forward hw0 hw1 hsmall hd hs _ n h
theorem related_backward (n : Nat) {x y : Stage} (h : R x y) :
    R (backwardStage n x) (backwardStage n y) := by
  change ContextEq hw0 hw1 hsmall hd hs _ (atBase (backwardStage n x) _) (atBase (backwardStage n y) _)
  rw [atBase_backward, atBase_backward]
  exact context_backward hw0 hw1 hsmall hd hs _ n h
theorem related_reflect {x y : Stage} (h : R x y) : R (reflectStage x) (reflectStage y) := by
  change ContextEq hw0 hw1 hsmall hd hs _ (atBase (reflectStage x) _) (atBase (reflectStage y) _)
  rw [atBase_reflect, atBase_reflect]
  exact context_reflect hw0 hw1 hsmall hd hs _ h

def stageMean (x : Stage) : CReal := mean hw0 hw1 hsmall hd hs x.positive x.expression

theorem stageMean_at (x : Stage) {N : Nat} (hx : x.base ≤ N) :
    Equiv (stageMean hw0 hw1 hsmall hd hs x)
      (mean hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx)) :=
  mean_include hw0 hw1 hsmall hd hs hx x.positive x.expression

theorem stageMean_congr {x y : Stage} (h : R x y) :
    Equiv (stageMean hw0 hw1 hsmall hd hs x) (stageMean hw0 hw1 hsmall hd hs y) :=
  (stageMean_at hw0 hw1 hsmall hd hs x (Nat.le_max_left x.base y.base)).trans
    ((context_mean hw0 hw1 hsmall hd hs _ h).trans
      (stageMean_at hw0 hw1 hsmall hd hs y (Nat.le_max_right x.base y.base)).symm)

end YMGap.Continuum.BF4WilsonSignedTimeUnion

#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.Stage
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.atBase
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.unitStage
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.mulStage
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.addStage
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.smulStage
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.forwardStage
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.backwardStage
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.reflectStage
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.atBase_unit
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.atBase_self
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.atBase_trans
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.atBase_mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.atBase_add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.atBase_smul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.atBase_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.atBase_backward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.atBase_reflect
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.Related
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.related_iff_at
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.related_refl
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.related_symm
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.related_trans
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.related_mul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.related_add
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.related_smul
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.related_forward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.related_backward
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.related_reflect
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.stageMean
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.stageMean_at
#print axioms YMGap.Continuum.BF4WilsonSignedTimeUnion.stageMean_congr
