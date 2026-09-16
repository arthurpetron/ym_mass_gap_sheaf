/-
# The actual physical time semigroup on the reflected Cauchy carrier

The squared seminorm is the original intrinsic reflected form of the signed
difference. Its proved contraction makes the literal physical advance a
nonexpansive map. The existing completion construction applies this map to
each Cauchy representative and retains its explicit modulus verbatim.
Zero and addition laws descend, and the original constant observable gives
a fixed completed vector distinct from the embedded zero presentation.

This constructs a completion carrier and time semigroup for the actual
fixed-nome, fixed-width, fixed-cutoff spatial-probe domain. It does not yet
construct the completed inner product/vector-space laws or certify a
physical Hilbert-space OS root. Vacuum isolation, nonconstant excitations,
strict gap, joint cutoff/volume/spacing limits and continuum QFT remain open.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
import YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeContraction

/-- Genuine distance-from-plane advance, retaining the physical-face guard. -/
def physicalTime {width : Nat} (n : Nat) (x : PhysicalSpan width) : PhysicalSpan width :=
  ⟨advanceSpan n x.val, advanceSpan_physical n x.val x.property⟩

theorem physicalTime_zero {width : Nat} (x : PhysicalSpan width) : physicalTime 0 x = x :=
  Subtype.ext (advanceSpan_zero x.val)

theorem physicalTime_add {width : Nat} (m n : Nat) (x : PhysicalSpan width) :
    physicalTime (m+n) x = physicalTime m (physicalTime n x) := by
  apply Subtype.ext
  exact (congrArg (fun k => advanceSpan k x.val) (Nat.add_comm m n)).trans
    (advanceSpan_add n m x.val)

/-- Nonexpansiveness is supplied by the proved ORIGINAL reflected-distance
bound, not assumed or transferred from an unrelated weighted L2 norm. -/
def timeNonexpansive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage n : Nat) : (seminorm hw0 hw1 width stage).Nonexpansive where
  toFun := physicalTime n
  contraction := fun x y => difference_contraction hw0 hw1 width n x.val y.val
    x.property y.property stage

def timeSemigroup {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) : (seminorm hw0 hw1 width stage).NonexpansiveSemigroup where
  op := timeNonexpansive hw0 hw1 width stage
  zero_law := by
    intro x
    change Equiv (distSq hw0 hw1 width stage (physicalTime 0 x) x) czero
    rw [physicalTime_zero]
    exact distSq_refl hw0 hw1 width stage x
  add_law := by
    intro m n x
    change Equiv (distSq hw0 hw1 width stage (physicalTime (m+n) x)
      (physicalTime m (physicalTime n x))) czero
    rw [physicalTime_add]
    exact distSq_refl hw0 hw1 width stage _

/-- The existing choice-free quotient of explicit-modulus Cauchy data. -/
def Completion {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) : Type := (seminorm hw0 hw1 width stage).Completion

def embedSpan {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (x : PhysicalSpan width) : Completion hw0 hw1 width stage :=
  (seminorm hw0 hw1 width stage).embedRep x

def completedTime {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage n : Nat) : Completion hw0 hw1 width stage → Completion hw0 hw1 width stage :=
  (timeNonexpansive hw0 hw1 width stage n).completionMap

theorem completedTime_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (x : Completion hw0 hw1 width stage) :
    completedTime hw0 hw1 width stage 0 x = x :=
  (timeSemigroup hw0 hw1 width stage).completionMap_zero x

theorem completedTime_add {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage m n : Nat) (x : Completion hw0 hw1 width stage) :
    completedTime hw0 hw1 width stage (m+n) x =
      completedTime hw0 hw1 width stage m (completedTime hw0 hw1 width stage n x) :=
  (timeSemigroup hw0 hw1 width stage).completionMap_add m n x

/-- On every original presentation, completed time is its literal advance. -/
theorem completedTime_embedSpan {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage n : Nat) (x : PhysicalSpan width) :
    completedTime hw0 hw1 width stage n (embedSpan hw0 hw1 width stage x) =
      embedSpan hw0 hw1 width stage (physicalTime n x) := rfl

/-- The modulus stored in every supplied Cauchy witness is preserved exactly. -/
theorem time_cauchy_modulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage n : Nat) (X : (seminorm hw0 hw1 width stage).Cauchy) :
    ((timeNonexpansive hw0 hw1 width stage n).mapCauchy X).modulus = X.modulus := rfl

def unit (width : Nat) : PhysicalSpan width := ⟨unitSpan, unit_physical width⟩

def zero (width : Nat) : PhysicalSpan width :=
  ⟨[], fun _ hx => False.elim (List.not_mem_nil hx)⟩

theorem physicalTime_unit (width n : Nat) : physicalTime n (unit width) = unit width :=
  Subtype.ext (advanceSpan_unit n)

def completedUnit {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) : Completion hw0 hw1 width stage :=
  embedSpan hw0 hw1 width stage (unit width)

theorem completedUnit_fixed {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage n : Nat) :
    completedTime hw0 hw1 width stage n (completedUnit hw0 hw1 width stage) =
      completedUnit hw0 hw1 width stage := by
  unfold completedUnit
  rw [completedTime_embedSpan, physicalTime_unit]

/-- Equality of embedded constants in the Cauchy carrier forces their
original reflected distance to vanish. All closeness moduli remain data. -/
theorem embedSpan_eq_implies_null {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) (x y : PhysicalSpan width)
    (h : embedSpan hw0 hw1 width stage x = embedSpan hw0 hw1 width stage y) :
    Equiv (distSq hw0 hw1 width stage x y) czero := by
  obtain ⟨hc⟩ := Quotient.exact h
  have hu : leEv (distSq hw0 hw1 width stage x y) czero := by
    intro epsilon he
    have hh := ExpNeg.half_mul_pos epsilon he
    have hb := hc.close (HalfPow.half*epsilon) hh
      (hc.modulus (HalfPow.half*epsilon)) (Nat.le_refl _)
    obtain ⟨N, hN⟩ := hb (HalfPow.half*epsilon) hh
    refine ⟨N, fun n hn => ?_⟩
    exact Q'.le_trans' _ _ _ (hN n hn)
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (ExpNeg.two_halves epsilon)
        (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))
  exact equiv_of_leEv_leEv hu (distSq_nonnegative hw0 hw1 width stage x y)

/-- The fixed completed unit is distinct from zero. This does not assert
a non-vacuum excitation or an isolated one-dimensional vacuum sector. -/
theorem completedUnit_ne_zero {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage : Nat) :
    completedUnit hw0 hw1 width stage ≠ embedSpan hw0 hw1 width stage (zero width) := by
  intro h
  exact unit_not_null hw0 hw1 width stage
    (embedSpan_eq_implies_null hw0 hw1 width stage (unit width) (zero width) h)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.physicalTime
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.physicalTime_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.physicalTime_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.timeNonexpansive
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.timeSemigroup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.Completion
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.completedTime
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.completedTime_zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.completedTime_add
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.completedTime_embedSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.time_cauchy_modulus
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.zero
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.physicalTime_unit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.completedUnit
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.completedUnit_fixed
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.embedSpan_eq_implies_null
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime.completedUnit_ne_zero
