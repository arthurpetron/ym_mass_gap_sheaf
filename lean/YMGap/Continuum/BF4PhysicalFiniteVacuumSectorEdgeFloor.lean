/-
# A common positive edge floor on every finite BF4 vacuum sector

The canonical BF4 vacuum sector is a finite list and every edge used by its
canonical positive-kernel paths has a strictly positive physical entry.  This
module converts those pointwise facts into one explicit rational floor.

For each ordered sector pair we replace a nonpositive entry by `1`; hence all
displayed candidates are strictly positive.  Folding `Q'.min'` over the finite
Cartesian list, with an additional positive fallback `1`, gives a positive
number below every candidate.  On an actually positive edge the candidate is
the physical kernel entry itself, so the floor applies to every edge used by
every canonical path.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. Generic located positive minimum -/

/-- Replace a value which is not strictly positive by the positive unit. -/
def positiveOrOne (value : Q') : Q' :=
  if _h : (0 : Q') < value then value else 1

theorem positiveOrOne_pos (value : Q') :
    (0 : Q') < positiveOrOne value := by
  unfold positiveOrOne
  by_cases h : (0 : Q') < value
  · rw [dif_pos h]
    exact h
  · rw [dif_neg h]
    decide

theorem positiveOrOne_eq_of_pos {value : Q'}
    (hvalue : (0 : Q') < value) :
    positiveOrOne value = value := by
  unfold positiveOrOne
  rw [dif_pos hvalue]

/-- Minimum of a finite list of positive candidates, with the positive unit as
the empty-list fallback and therefore also as a harmless extra candidate. -/
def listPositiveMinOne {State : Type}
    (value : State → Q') : List State → Q'
  | [] => 1
  | first :: rest =>
      Q'.min' (value first) (listPositiveMinOne value rest)

theorem listPositiveMinOne_pos
    {State : Type} (value : State → Q') :
    ∀ states : List State,
      (∀ state, state ∈ states → (0 : Q') < value state) →
      (0 : Q') < listPositiveMinOne value states
  | [], _ => by
      change (0 : Q') < 1
      decide
  | first :: rest, hpos => by
      have hfirst : (0 : Q') < value first :=
        hpos first List.mem_cons_self
      have hrest : (0 : Q') < listPositiveMinOne value rest :=
        listPositiveMinOne_pos value rest
          (fun state hstate =>
            hpos state (List.mem_cons_of_mem first hstate))
      unfold listPositiveMinOne Q'.min'
      by_cases hle : value first ≤ listPositiveMinOne value rest
      · rw [if_pos hle]
        exact hfirst
      · rw [if_neg hle]
        exact hrest

theorem listPositiveMinOne_le_of_mem
    {State : Type} (value : State → Q') :
    ∀ states : List State, ∀ state,
      state ∈ states →
      listPositiveMinOne value states ≤ value state
  | [], _, hstate => by cases hstate
  | first :: rest, state, hstate => by
      rcases List.mem_cons.mp hstate with hfirst | hrest
      · subst state
        exact Q'.min_le_left' _ _
      · exact Q'.le_trans' _ _ _
          (Q'.min_le_right' _ _)
          (listPositiveMinOne_le_of_mem value rest state hrest)

/-! ## 2. The BF4 sector edge floor -/

/-- All ordered pairs of indices in the canonical finite vacuum sector. -/
def centralPhysicalFiniteVacuumSectorPairs
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    List (Nat × Nat) :=
  cartesian
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)

/-- The explicit common positive floor: the minimum of `1` and every positive
physical entry (with nonpositive entries replaced by `1`). -/
def centralPhysicalFiniteVacuumSectorEdgeFloor
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  listPositiveMinOne
    (fun pair => positiveOrOne
      (centralPhysicalFiniteKernel
        w hw cutoff half pair.1 pair.2))
    (centralPhysicalFiniteVacuumSectorPairs
      w hw cutoff half)

theorem centralPhysicalFiniteVacuumSectorEdgeFloor_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') <
      centralPhysicalFiniteVacuumSectorEdgeFloor
        w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorEdgeFloor
  apply listPositiveMinOne_pos
  intro pair _hpair
  exact positiveOrOne_pos _

/-- The finite floor lies below every strictly positive physical entry between
two indices of the canonical vacuum sector. -/
theorem centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel w hw cutoff half left right) :
    centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half ≤
      centralPhysicalFiniteKernel w hw cutoff half left right := by
  have hpair : (left, right) ∈
      centralPhysicalFiniteVacuumSectorPairs w hw cutoff half := by
    exact (mem_cartesian_iff _ _ (left, right)).mpr
      ⟨hleft, hright⟩
  have hmin := listPositiveMinOne_le_of_mem
    (fun pair => positiveOrOne
      (centralPhysicalFiniteKernel
        w hw cutoff half pair.1 pair.2))
    (centralPhysicalFiniteVacuumSectorPairs w hw cutoff half)
    (left, right) hpair
  simpa [centralPhysicalFiniteVacuumSectorEdgeFloor,
    positiveOrOne, hpositive] using hmin

/-- The common floor immediately discharges the edge-floor premise of the
canonical path-energy theorem. -/
theorem centralPhysicalFiniteVacuumSector_edgeFloor_mul_endpoint_sq_le_pathEnergy
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q')
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half *
        ((coefficient left + -coefficient right) *
          (coefficient left + -coefficient right)) ≤
      BF4PhysicalFiniteVacuumSectorPathEnergy.PositiveKernelChainIn.amplifiedEnergy
        coefficient
        (BF4PhysicalFiniteVacuumSectorPathEnergy.centralPhysicalFiniteVacuumSectorPositivePath
          w hw cutoff half left right hleft hright) := by
  exact
    BF4PhysicalFiniteVacuumSectorPathEnergy.centralPhysicalFiniteVacuumSector_floor_mul_endpoint_sq_le_pathEnergy
      w hw cutoff half coefficient
      (centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half)
      (Q'.le_of_lt
        (centralPhysicalFiniteVacuumSectorEdgeFloor_pos
          w hw cutoff half))
      (centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
        w hw cutoff half)
      left right hleft hright

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor.listPositiveMinOne_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor.listPositiveMinOne_le_of_mem
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor.centralPhysicalFiniteVacuumSectorEdgeFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor.centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor.centralPhysicalFiniteVacuumSector_edgeFloor_mul_endpoint_sq_le_pathEnergy
