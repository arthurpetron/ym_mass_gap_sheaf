/-
# One staged carrier for all finite-base physical presentations

Each element carries a positive support base and the original signed physical
face words. Mixed pairings and squared distances are evaluated at the computed
maximum base. The already proved spatial-limit inclusion theorem makes these
values independent of any larger common base. No finite-volume measures or
fixed-base completions are identified, and no choice of a support bound for
an entire Cauchy stream is made.

This is the union of the existing presentation carriers, not a theorem that
they exhaust the full Yang--Mills observable algebra or its continuum limit.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialBaseCoherence
import YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm

namespace YMGap.Continuum.BF4SpatialUnion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicLinear (addSpan smulSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws (differenceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
  (physicalTime physicalTime_zero physicalTime_add unit zero physicalTime_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseInclusion
open YMGap.Continuum.BF4ExactSlabFixedSpatialBaseCoherence (spatialPairing_inclusion)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialPairingLaws
open YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialSeminorm
open YMGap.Continuum.BF4ExactSlabCollarAdjustedRate
open YMGap.Continuum.FiniteSizeGeometricSum
open YMGap.Continuum.QuaternionHaarCharacterInterval

/-- A finite support bound is data for each element, never for a whole stream. -/
structure Stage where
  base : Nat
  positive : 0 < base
  value : PhysicalSpan base

def ofSpan (base : Nat) (hb : 0 < base) (x : PhysicalSpan base) : Stage :=
  ⟨base, hb, x⟩

def atBase (x : Stage) {larger : Nat} (h : x.base ≤ larger) : PhysicalSpan larger :=
  inclusion h x.value

theorem atBase_trans (x : Stage) {middle larger : Nat}
    (h : x.base ≤ middle) (k : middle ≤ larger) :
    inclusion k (atBase x h) = atBase x (Nat.le_trans h k) :=
  inclusion_trans h k x.value

theorem atBase_self (x : Stage) : atBase x (Nat.le_refl _) = x.value :=
  inclusion_refl x.value

def time (n : Nat) (x : Stage) : Stage :=
  ⟨x.base, x.positive, physicalTime n x.value⟩

theorem time_zero (x : Stage) : time 0 x = x := by
  cases x
  simp only [time, physicalTime_zero]

theorem time_add (m n : Nat) (x : Stage) : time (m+n) x = time m (time n x) := by
  simp only [time, physicalTime_add]

theorem atBase_time (n : Nat) (x : Stage) {larger : Nat} (h : x.base ≤ larger) :
    atBase (time n x) h = physicalTime n (atBase x h) :=
  inclusion_time h n x.value

def unitStage : Stage := ofSpan 1 (by decide) (unit 1)
def zeroStage : Stage := ofSpan 1 (by decide) (zero 1)

theorem atBase_unit {larger : Nat} (h : 1 ≤ larger) :
    atBase unitStage h = unit larger := inclusion_unit h

theorem atBase_zero {larger : Nat} (h : 1 ≤ larger) :
    atBase zeroStage h = zero larger := inclusion_zero h

theorem time_unit (n : Nat) : time n unitStage = unitStage := by
  simp only [time, unitStage, ofSpan, physicalTime_unit]

def addStage (x y : Stage) : Stage :=
  ⟨max x.base y.base, Nat.lt_of_lt_of_le x.positive (Nat.le_max_left _ _),
    addSpan (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))⟩

def smulStage (c : Q') (x : Stage) : Stage :=
  ⟨x.base, x.positive, smulSpan c x.value⟩

def difference (x y : Stage) : Stage := addStage x (smulStage (-1) y)

theorem atBase_add (x y : Stage) {larger : Nat}
    (hx : x.base ≤ larger) (hy : y.base ≤ larger) :
    atBase (addStage x y) (Nat.max_le.mpr ⟨hx,hy⟩) =
      addSpan (atBase x hx) (atBase y hy) := by
  simp only [atBase, addStage, inclusion_add, inclusion_trans]

theorem atBase_smul (c : Q') (x : Stage) {larger : Nat} (hx : x.base ≤ larger) :
    atBase (smulStage c x) hx = smulSpan c (atBase x hx) :=
  inclusion_smul hx c x.value

theorem atBase_difference (x y : Stage) {larger : Nat}
    (hx : x.base ≤ larger) (hy : y.base ≤ larger) :
    atBase (difference x y) (Nat.max_le.mpr ⟨hx,hy⟩) =
      differenceSpan (atBase x hx) (atBase y hy) := by
  exact (atBase_add x (smulStage (-1) y) hx hy).trans
    (congrArg (addSpan (atBase x hx)) (atBase_smul (-1) y hy))

theorem inclusion_difference {base larger : Nat} (h : base ≤ larger)
    (x y : PhysicalSpan base) :
    inclusion h (differenceSpan x y) = differenceSpan (inclusion h x) (inclusion h y) :=
  (inclusion_add h x (smulSpan (-1) y)).trans
    (congrArg (addSpan (inclusion h x)) (inclusion_smul h (-1) y))

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (hsmall : heatRatio w ≤ HalfPow.half) (hd : heatRemainderBound w < 1)
  (hs : entropyRate 625 (adjustedCoreRate w hd) < 1)

/-- The actual spatial limiting form, evaluated at a computed common base. -/
def pairing (x y : Stage) : CReal :=
  spatialPairing hw0 hw1 (max x.base y.base) hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left _ _))
    (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))

def pairingCauchy (x y : Stage) : QCauchy (pairing hw0 hw1 hsmall hd hs x y).approx :=
  spatialPairingCauchy hw0 hw1 _ hsmall hd hs _ _ _

/-- Any supplied larger common base gives the SAME original spatial scalar. -/
theorem pairing_at_base (x y : Stage) (larger : Nat)
    (hx : x.base ≤ larger) (hy : y.base ≤ larger) :
    Equiv (pairing hw0 hw1 hsmall hd hs x y)
      (spatialPairing hw0 hw1 larger hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
        (atBase x hx) (atBase y hy)) := by
  have h := spatialPairing_inclusion hw0 hw1 hsmall hd hs
    (Nat.max_le.mpr ⟨hx,hy⟩)
    (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left x.base y.base))
    (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))
  simpa only [pairing, atBase_trans] using h

theorem pairing_ofSpan (base : Nat) (hb : 0 < base) (x y : PhysicalSpan base) :
    Equiv (pairing hw0 hw1 hsmall hd hs (ofSpan base hb x) (ofSpan base hb y))
      (spatialPairing hw0 hw1 base hsmall hd hs hb x y) := by
  simpa only [atBase_self] using pairing_at_base hw0 hw1 hsmall hd hs
    (ofSpan base hb x) (ofSpan base hb y) base (Nat.le_refl _) (Nat.le_refl _)

/-- Squared distance is computed in the same common-base limiting form. -/
def distSq (x y : Stage) : CReal :=
  spatialDistSq hw0 hw1 (max x.base y.base) hsmall hd hs
    (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left _ _))
    (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _))

def distSqCauchy (x y : Stage) : QCauchy (distSq hw0 hw1 hsmall hd hs x y).approx :=
  spatialDistSqCauchy hw0 hw1 _ hsmall hd hs _ _ _

theorem distSq_at_base (x y : Stage) (larger : Nat)
    (hx : x.base ≤ larger) (hy : y.base ≤ larger) :
    Equiv (distSq hw0 hw1 hsmall hd hs x y)
      (spatialDistSq hw0 hw1 larger hsmall hd hs (Nat.lt_of_lt_of_le x.positive hx)
        (atBase x hx) (atBase y hy)) := by
  have h := spatialPairing_inclusion hw0 hw1 hsmall hd hs
    (Nat.max_le.mpr ⟨hx,hy⟩)
    (Nat.lt_of_lt_of_le x.positive (Nat.le_max_left x.base y.base))
    (differenceSpan (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _)))
    (differenceSpan (atBase x (Nat.le_max_left _ _)) (atBase y (Nat.le_max_right _ _)))
  simpa only [distSq, spatialDistSq, inclusion_difference, atBase_trans] using h

theorem distSq_ofSpan (base : Nat) (hb : 0 < base) (x y : PhysicalSpan base) :
    Equiv (distSq hw0 hw1 hsmall hd hs (ofSpan base hb x) (ofSpan base hb y))
      (spatialDistSq hw0 hw1 base hsmall hd hs hb x y) := by
  simpa only [atBase_self] using distSq_at_base hw0 hw1 hsmall hd hs
    (ofSpan base hb x) (ofSpan base hb y) base (Nat.le_refl _) (Nat.le_refl _)

end YMGap.Continuum.BF4SpatialUnion

#print axioms YMGap.Continuum.BF4SpatialUnion.Stage
#print axioms YMGap.Continuum.BF4SpatialUnion.ofSpan
#print axioms YMGap.Continuum.BF4SpatialUnion.atBase
#print axioms YMGap.Continuum.BF4SpatialUnion.atBase_trans
#print axioms YMGap.Continuum.BF4SpatialUnion.atBase_self
#print axioms YMGap.Continuum.BF4SpatialUnion.time
#print axioms YMGap.Continuum.BF4SpatialUnion.time_zero
#print axioms YMGap.Continuum.BF4SpatialUnion.time_add
#print axioms YMGap.Continuum.BF4SpatialUnion.atBase_time
#print axioms YMGap.Continuum.BF4SpatialUnion.unitStage
#print axioms YMGap.Continuum.BF4SpatialUnion.zeroStage
#print axioms YMGap.Continuum.BF4SpatialUnion.atBase_unit
#print axioms YMGap.Continuum.BF4SpatialUnion.atBase_zero
#print axioms YMGap.Continuum.BF4SpatialUnion.time_unit
#print axioms YMGap.Continuum.BF4SpatialUnion.addStage
#print axioms YMGap.Continuum.BF4SpatialUnion.smulStage
#print axioms YMGap.Continuum.BF4SpatialUnion.difference
#print axioms YMGap.Continuum.BF4SpatialUnion.atBase_add
#print axioms YMGap.Continuum.BF4SpatialUnion.atBase_smul
#print axioms YMGap.Continuum.BF4SpatialUnion.atBase_difference
#print axioms YMGap.Continuum.BF4SpatialUnion.inclusion_difference
#print axioms YMGap.Continuum.BF4SpatialUnion.pairing
#print axioms YMGap.Continuum.BF4SpatialUnion.pairingCauchy
#print axioms YMGap.Continuum.BF4SpatialUnion.pairing_at_base
#print axioms YMGap.Continuum.BF4SpatialUnion.pairing_ofSpan
#print axioms YMGap.Continuum.BF4SpatialUnion.distSq
#print axioms YMGap.Continuum.BF4SpatialUnion.distSqCauchy
#print axioms YMGap.Continuum.BF4SpatialUnion.distSq_at_base
#print axioms YMGap.Continuum.BF4SpatialUnion.distSq_ofSpan
