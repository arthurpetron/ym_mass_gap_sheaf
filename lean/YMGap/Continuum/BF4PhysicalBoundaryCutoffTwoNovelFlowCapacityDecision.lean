/-
# Exact finite decision procedure for the novel-flow capacity frontier

The preceding module contracts the four pointwise flow-capacity obligations
to one explicit finite minimum.  This module reflects that remaining finite
statement into a Boolean scan.  A successful scan constructs the full local
capacity certificate.  A failed scalar comparison is analyzed
constructively: either the requested strength already exceeds the unit
fallback, or the scan returns an actual full-sector edge with positive load
whose requested load payment is not bounded by its allocated physical
kernel.

Thus every fixed cutoff is now an exact certificate-or-obstruction
calculation.  The genuinely infinite open problem is proving success along a
constructively cofinal schedule; no uniform gap, thermodynamic/continuum
limit, or Clay conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityDecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. Generic finite-minimum reflection -/

/-- A candidate below the unit fallback and every entry of the finite list is
below the located positive minimum. -/
theorem le_listPositiveMinOne_of_forall
    {State : Type} (value : State → Q') (candidate : Q') :
    ∀ states : List State,
      candidate ≤ 1 →
      (∀ state, state ∈ states → candidate ≤ value state) →
      candidate ≤ listPositiveMinOne value states
  | [], hunit, _ => hunit
  | first :: rest, hunit, hall => by
      unfold listPositiveMinOne Q'.min'
      by_cases hle : value first ≤ listPositiveMinOne value rest
      · rw [if_pos hle]
        exact hall first List.mem_cons_self
      · rw [if_neg hle]
        exact le_listPositiveMinOne_of_forall value candidate rest hunit
          (fun state hstate =>
            hall state (List.mem_cons_of_mem first hstate))

/-- The unit fallback is an upper bound for the finite minimum. -/
theorem listPositiveMinOne_le_one
    {State : Type} (value : State → Q') :
    ∀ states : List State,
      listPositiveMinOne value states ≤ 1
  | [] => Q'.le_refl' 1
  | _first :: rest =>
      Q'.le_trans' _ _ _
        (Q'.min_le_right' _ _)
        (listPositiveMinOne_le_one value rest)

/-- Failure of a finite-minimum lower bound returns either failure at the unit
fallback or a literal list entry where the proposed lower bound fails. -/
theorem not_le_listPositiveMinOne_cases
    {State : Type} (value : State → Q') :
    ∀ (states : List State) (candidate : Q'),
      ¬ candidate ≤ listPositiveMinOne value states →
      (¬ candidate ≤ 1) ∨
        ∃ state, state ∈ states ∧ ¬ candidate ≤ value state
  | [], candidate, hfailure => Or.inl hfailure
  | first :: rest, candidate, hfailure => by
      unfold listPositiveMinOne Q'.min' at hfailure
      by_cases hle : value first ≤ listPositiveMinOne value rest
      · rw [if_pos hle] at hfailure
        exact Or.inr
          ⟨first, List.mem_cons_self, hfailure⟩
      · rw [if_neg hle] at hfailure
        rcases not_le_listPositiveMinOne_cases
            value rest candidate hfailure with hunit | hentry
        · exact Or.inl hunit
        · rcases hentry with ⟨state, hstate, hstateFailure⟩
          exact Or.inr
            ⟨state, List.mem_cons_of_mem first hstate, hstateFailure⟩

/-- Type-level form of the same failure witness.  Unlike propositional
disjunction/existence, this result may be inspected to build computational
certificate-or-obstruction data without eliminating a proposition into
`Type`. -/
inductive ListPositiveMinOneFailure
    {State : Type} (value : State → Q')
    (states : List State) (candidate : Q') : Type
  | unit (not_le_unit : ¬ candidate ≤ 1)
  | entry (state : State)
      (state_mem : state ∈ states)
      (not_le_value : ¬ candidate ≤ value state)

def locateListPositiveMinOneFailure
    {State : Type} (value : State → Q') :
    ∀ (states : List State) (candidate : Q'),
      ¬ candidate ≤ listPositiveMinOne value states →
      ListPositiveMinOneFailure value states candidate
  | [], candidate, hfailure =>
      ListPositiveMinOneFailure.unit hfailure
  | first :: rest, candidate, hfailure => by
      unfold listPositiveMinOne Q'.min' at hfailure
      by_cases hle : value first ≤ listPositiveMinOne value rest
      · rw [if_pos hle] at hfailure
        exact ListPositiveMinOneFailure.entry
          first List.mem_cons_self hfailure
      · rw [if_neg hle] at hfailure
        cases locateListPositiveMinOneFailure
            value rest candidate hfailure with
        | unit hunit =>
            exact ListPositiveMinOneFailure.unit hunit
        | entry state hstate hstateFailure =>
            exact ListPositiveMinOneFailure.entry state
              (List.mem_cons_of_mem first hstate) hstateFailure

/-! ## 2. The exact reflected cutoff checker -/

/-- Boolean scan of exactly the lower-bound conditions represented by the
finite minimum: the unit fallback and every ordered full-sector edge ratio. -/
def cutoffTwoNovelFlowCapacityCheck (later : Nat) : Bool :=
  decide (cutoffTwoNovelSimpleFlowCoercivityFloor ≤ (1 : Q')) &&
    (cutoffTwoNovelCapacityEdgePairs later).all
      (fun pair => decide
        (cutoffTwoNovelSimpleFlowCoercivityFloor ≤
          cutoffTwoNovelEdgeCapacityRatio later pair.1 pair.2))

/-- Soundness of the Boolean scan: success proves the scalar finite-floor
comparison consumed by the ratio compiler. -/
theorem cutoffTwoNovelFlowCapacityCheck_sound
    (later : Nat)
    (hcheck : cutoffTwoNovelFlowCapacityCheck later = true) :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later := by
  unfold cutoffTwoNovelFlowCapacityCheck at hcheck
  have hparts := (Bool.and_eq_true _ _).mp hcheck
  exact le_listPositiveMinOne_of_forall
    (fun pair : Nat × Nat =>
      cutoffTwoNovelEdgeCapacityRatio later pair.1 pair.2)
    cutoffTwoNovelSimpleFlowCoercivityFloor
    (cutoffTwoNovelCapacityEdgePairs later)
    (of_decide_eq_true hparts.1)
    (fun pair hpair =>
      of_decide_eq_true
        (List.all_eq_true.mp hparts.2 pair hpair))

/-- Completeness of the Boolean scan: the scalar finite-floor comparison
forces every scanned rational comparison to evaluate to true. -/
theorem cutoffTwoNovelFlowCapacityCheck_complete
    (later : Nat)
    (hfloor : cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later) :
    cutoffTwoNovelFlowCapacityCheck later = true := by
  unfold cutoffTwoNovelFlowCapacityCheck
  apply (Bool.and_eq_true _ _).mpr
  constructor
  · apply decide_eq_true
    exact Q'.le_trans' _ _ _ hfloor
      (listPositiveMinOne_le_one
        (fun pair : Nat × Nat =>
          cutoffTwoNovelEdgeCapacityRatio later pair.1 pair.2)
        (cutoffTwoNovelCapacityEdgePairs later))
  · apply List.all_eq_true.mpr
    intro pair hpair
    apply decide_eq_true
    exact Q'.le_trans' _ _ _ hfloor
      (listPositiveMinOne_le_of_mem
        (fun edge : Nat × Nat =>
          cutoffTwoNovelEdgeCapacityRatio later edge.1 edge.2)
        (cutoffTwoNovelCapacityEdgePairs later)
        pair hpair)

/-! ## 3. A constructive certificate-or-overloaded-edge outcome -/

/-- Exact result of inspecting one cutoff.  The third constructor is a
literal local obstruction to the chosen flow at the requested fixed
strength, rather than merely failure of an aggregate scalar test. -/
inductive CutoffTwoNovelFlowCapacityOutcome (later : Nat) : Type
  | certified
      (floor_le : cutoffTwoNovelSimpleFlowCoercivityFloor ≤
        cutoffTwoNovelFiniteFlowCapacityFloor later)
  | targetAboveUnit
      (not_le_unit : ¬ cutoffTwoNovelSimpleFlowCoercivityFloor ≤ (1 : Q'))
  | overloadedEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadFullStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadFullStates later)
      (load_pos : (0 : Q') <
        cutoffTwoNovelSimpleEdgeLoad later source target)
      (not_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelSimpleEdgeLoad later source target ≤
          cutoffTwoNovelAllocatedKernel later source target)

/-- Compute the exact outcome at a fixed cutoff.  If the finite lower bound
fails, recursively locating a failed minimum candidate and cancelling its
positive load produces an explicit overloaded directed edge. -/
def inspectCutoffTwoNovelFlowCapacity
    (later : Nat) : CutoffTwoNovelFlowCapacityOutcome later := by
  by_cases hfloor : cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later
  · exact CutoffTwoNovelFlowCapacityOutcome.certified hfloor
  · cases locateListPositiveMinOneFailure
        (fun pair : Nat × Nat =>
          cutoffTwoNovelEdgeCapacityRatio later pair.1 pair.2)
        (cutoffTwoNovelCapacityEdgePairs later)
        cutoffTwoNovelSimpleFlowCoercivityFloor hfloor with
    | unit hunit =>
        exact CutoffTwoNovelFlowCapacityOutcome.targetAboveUnit hunit
    | entry pair hpairMem hratio =>
      have hfull :=
        (mem_cartesian_iff
          (cutoffTwoEdgeLoadFullStates later)
          (cutoffTwoEdgeLoadFullStates later) pair).mp hpairMem
      by_cases hload : (0 : Q') <
          cutoffTwoNovelSimpleEdgeLoad later pair.1 pair.2
      · apply CutoffTwoNovelFlowCapacityOutcome.overloadedEdge
          pair.1 pair.2 hfull.1 hfull.2 hload
        intro hcapacity
        apply hratio
        unfold cutoffTwoNovelEdgeCapacityRatio
        rw [dif_pos hload]
        exact Q'.le_divPos_of_mul_le
          (cutoffTwoNovelAllocatedKernel later pair.1 pair.2)
          (cutoffTwoNovelSimpleEdgeLoad later pair.1 pair.2)
          hload hcapacity
      · apply CutoffTwoNovelFlowCapacityOutcome.targetAboveUnit
        intro htargetUnit
        apply hratio
        unfold cutoffTwoNovelEdgeCapacityRatio
        rw [dif_neg hload]
        exact htargetUnit

/-! ## 4. Checked cofinal schedules compile to the completed gap interface -/

/-- A cofinal schedule whose finite rational scans are kernel-checked.  This
is equivalent in strength to the scalar ratio family, but makes every finite
member directly executable and auditable. -/
structure CutoffTwoCofinalNovelFlowCapacityCheck : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  check : ∀ request,
    cutoffTwoNovelFlowCapacityCheck (anchor request) = true

namespace CutoffTwoCofinalNovelFlowCapacityCheck

def toCofinalNovelFlowCapacityRatio
    (checked : CutoffTwoCofinalNovelFlowCapacityCheck) :
    CutoffTwoCofinalNovelFlowCapacityRatio where
  anchor := checked.anchor
  anchor_ge := checked.anchor_ge
  fixed_floor_le := fun request =>
    cutoffTwoNovelFlowCapacityCheck_sound
      (checked.anchor request) (checked.check request)

def toCompletedStrictContractionData
    (checked : CutoffTwoCofinalNovelFlowCapacityCheck) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (by decide) (by decide) 0 :=
  checked.toCofinalNovelFlowCapacityRatio.toCompletedStrictContractionData

end CutoffTwoCofinalNovelFlowCapacityCheck

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityDecision

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityDecision.cutoffTwoNovelFlowCapacityCheck_sound
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityDecision.cutoffTwoNovelFlowCapacityCheck_complete
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityDecision.inspectCutoffTwoNovelFlowCapacity
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityDecision.CutoffTwoCofinalNovelFlowCapacityCheck.toCompletedStrictContractionData
