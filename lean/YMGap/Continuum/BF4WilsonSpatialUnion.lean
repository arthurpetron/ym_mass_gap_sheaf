/-
# One staged carrier for all finite-base Wilson presentations

Each stage contains a positive spatial support base and an original
radius-tagged signed Wilson expression. Pairing and squared distance are
the existing limiting form at the computed maximum base. Proved base
coherence identifies these values with every supplied larger common base;
the chosen scalar representatives retain their own explicit Cauchy data.

No common support bound for an entire Cauchy stream is selected. This is
the union of the existing spatial-loop window syntax, not a theorem that
this syntax covers every gauge observable or constructs continuum QFT.
In particular, advancing the unit changes its radius tag, so no equality
of the raw unit stage with its time advance is asserted here.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseCoherence

namespace YMGap.Continuum.BF4WilsonSpatialUnion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (smul zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance advance_zero advance_add)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseInclusion
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonBaseCoherence
  (intrinsicForm_inclusion distSq_inclusion)
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- A finite support bound is data for each stage, not for an entire stream. -/
structure Stage where
  base : Nat
  positive : 0 < base
  value : IntrinsicExpression base

def ofExpression (base : Nat) (hb : 0 < base) (x : IntrinsicExpression base) : Stage :=
  ⟨base, hb, x⟩

def atBase (x : Stage) {larger : Nat} (h : x.base ≤ larger) : IntrinsicExpression larger :=
  inclusion h x.value

theorem atBase_trans (x : Stage) {middle larger : Nat}
    (h : x.base ≤ middle) (k : middle ≤ larger) :
    inclusion k (atBase x h) = atBase x (Nat.le_trans h k) :=
  inclusion_trans h k x.value

theorem atBase_self (x : Stage) : atBase x (Nat.le_refl _) = x.value :=
  inclusion_refl x.value

def time (n : Nat) (x : Stage) : Stage :=
  ⟨x.base, x.positive, advance n x.value⟩

theorem time_zero (x : Stage) : time 0 x = x := by
  cases x
  simp only [time, advance_zero]

theorem time_add (m n : Nat) (x : Stage) : time (m+n) x = time m (time n x) := by
  simp only [time, advance_add]

theorem atBase_time (n : Nat) (x : Stage) {larger : Nat} (h : x.base ≤ larger) :
    atBase (time n x) h = advance n (atBase x h) :=
  inclusion_advance h n x.value

def unitStage : Stage := ofExpression 1 (by decide) (unit 1)
def zeroStage : Stage := ofExpression 1 (by decide) (zero 1)

theorem atBase_unit {larger : Nat} (h : 1 ≤ larger) :
    atBase unitStage h = unit larger := inclusion_unit h

theorem atBase_zero {larger : Nat} (h : 1 ≤ larger) :
    atBase zeroStage h = zero larger := inclusion_zero h

def sumStage (x y : Stage) : Stage :=
  ⟨max x.base y.base, Nat.lt_of_lt_of_le x.positive (Nat.le_max_left _ _),
    sum (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))⟩

def smulStage (c : Q') (x : Stage) : Stage :=
  ⟨x.base, x.positive, smul c x.value⟩

def difference (x y : Stage) : Stage :=
  ⟨max x.base y.base, Nat.lt_of_lt_of_le x.positive (Nat.le_max_left _ _),
    BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.difference
      (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))⟩

theorem atBase_sum (x y : Stage) {larger : Nat}
    (hx : x.base ≤ larger) (hy : y.base ≤ larger) :
    atBase (sumStage x y) (Nat.max_le.mpr ⟨hx,hy⟩) =
      sum (atBase x hx) (atBase y hy) := by
  simp only [atBase, sumStage, inclusion_sum, inclusion_trans]

theorem atBase_smul (c : Q') (x : Stage) {larger : Nat} (hx : x.base ≤ larger) :
    atBase (smulStage c x) hx = smul c (atBase x hx) :=
  inclusion_smul hx c x.value

theorem atBase_difference (x y : Stage) {larger : Nat}
    (hx : x.base ≤ larger) (hy : y.base ≤ larger) :
    atBase (difference x y) (Nat.max_le.mpr ⟨hx,hy⟩) =
      BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.difference
        (atBase x hx) (atBase y hy) := by
  simp only [atBase, difference, inclusion_difference, inclusion_trans]

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

/-- The original mixed Wilson limit at a computed common positive base. -/
def pairing (x y : Stage) : CReal :=
  intrinsicForm hw0 hw1 hsmall hd hs (base := max x.base y.base)
    (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left _ _))
    (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))

def pairingCauchy (x y : Stage) : QCauchy (pairing hw0 hw1 hsmall hd hs x y).approx :=
  intrinsicFormCauchy hw0 hw1 hsmall hd hs _ _ _

/-- Every supplied larger common base realizes the SAME limiting scalar. -/
theorem pairing_at_base (x y : Stage) (larger : Nat)
    (hx : x.base ≤ larger) (hy : y.base ≤ larger) :
    Equiv (pairing hw0 hw1 hsmall hd hs x y)
      (intrinsicForm hw0 hw1 hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
        (atBase x hx) (atBase y hy)) := by
  have h := intrinsicForm_inclusion hw0 hw1 hsmall hd hs
    (Nat.max_le.mpr ⟨hx,hy⟩)
    (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left x.base y.base))
    (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))
  simpa only [pairing, atBase_trans] using h

attribute [local irreducible] pairing intrinsicForm

theorem pairing_ofExpression (base : Nat) (hb : 0 < base) (x y : IntrinsicExpression base) :
    Equiv (pairing hw0 hw1 hsmall hd hs (ofExpression base hb x) (ofExpression base hb y))
      (intrinsicForm hw0 hw1 hsmall hd hs hb x y) := by
  simpa only [atBase, ofExpression, inclusion_refl] using pairing_at_base hw0 hw1 hsmall hd hs
    (ofExpression base hb x) (ofExpression base hb y) base (Nat.le_refl _) (Nat.le_refl _)

/-- Squared distance is the existing Wilson distance at the SAME maximum base. -/
def distSq (x y : Stage) : CReal :=
  BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq hw0 hw1 hsmall hd hs
    (base := max x.base y.base)
    (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left _ _))
    (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))

def distSqCauchy (x y : Stage) : QCauchy (distSq hw0 hw1 hsmall hd hs x y).approx :=
  BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSqCauchy hw0 hw1 hsmall hd hs _ _ _

theorem distSq_at_base (x y : Stage) (larger : Nat)
    (hx : x.base ≤ larger) (hy : y.base ≤ larger) :
    Equiv (distSq hw0 hw1 hsmall hd hs x y)
      (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq hw0 hw1 hsmall hd hs
        (Nat.lt_of_lt_of_le x.positive hx) (atBase x hx) (atBase y hy)) := by
  have h := distSq_inclusion hw0 hw1 hsmall hd hs
    (Nat.max_le.mpr ⟨hx,hy⟩)
    (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left x.base y.base))
    (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))
  simpa only [distSq, atBase_trans] using h

attribute [local irreducible] distSq BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq

theorem distSq_ofExpression (base : Nat) (hb : 0 < base) (x y : IntrinsicExpression base) :
    Equiv (distSq hw0 hw1 hsmall hd hs (ofExpression base hb x) (ofExpression base hb y))
      (BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm.distSq hw0 hw1 hsmall hd hs hb x y) := by
  simpa only [atBase, ofExpression, inclusion_refl] using distSq_at_base hw0 hw1 hsmall hd hs
    (ofExpression base hb x) (ofExpression base hb y) base (Nat.le_refl _) (Nat.le_refl _)

end YMGap.Continuum.BF4WilsonSpatialUnion

#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.Stage
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.ofExpression
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.atBase
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.atBase_trans
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.atBase_self
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.time
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.time_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.time_add
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.atBase_time
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.unitStage
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.zeroStage
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.atBase_unit
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.atBase_zero
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.sumStage
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.smulStage
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.difference
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.atBase_sum
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.atBase_smul
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.atBase_difference
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.pairing
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.pairingCauchy
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.pairing_at_base
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.pairing_ofExpression
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.distSq
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.distSqCauchy
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.distSq_at_base
#print axioms YMGap.Continuum.BF4WilsonSpatialUnion.distSq_ofExpression
