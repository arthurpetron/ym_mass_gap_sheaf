/-
# Exact finite decision procedure for concrete conditional-ratio-ceiling payment

The preceding module constructs, at every fixed cutoff, a rational ceiling for
all reverse/forward conditional-kernel ratios.  The remaining obligation is a
finite family of rational inequalities saying that the allocated conditional
kernel pays the resulting ceiling-weighted path load on every ordered carrier
edge.

This module reflects exactly that family into a Boolean scan.  Success compiles
to the finite flow-capacity floor and hence, along a cofinal schedule, to the
completed strict-contraction interface.  Failure is inspected constructively
and returns a literal ordered carrier edge where the conservative ceiling load
is not paid.

The checker is exact for this sufficient ceiling-payment condition.  It does
not assert that the checker succeeds at any cutoff, that a failed conservative
ceiling is a failure of the underlying exact flow, or that any uniform gap or
thermodynamic/continuum conclusion has been proved.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. Exact reflected payment checker -/

/-- Boolean scan of exactly the concrete ratio-ceiling payment inequalities on
all ordered pairs of the literal full carrier. -/
def cutoffTwoNovelConditionalFiniteRatioCeilingCheck
    (later : Nat) : Bool :=
  (cartesian
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadFullStates later)).all
    (fun pair => decide
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelConditionalFiniteRatioCeilingLoad
            later pair.1 pair.2 ≤
        cutoffTwoNovelAllocatedConditionalKernel
          later pair.1 pair.2))

/-- Soundness of the finite scan: success pays the concrete ceiling-weighted
load on every ordered carrier edge. -/
theorem cutoffTwoNovelConditionalFiniteRatioCeilingCheck_sound_capacity
    (later : Nat)
    (hcheck :
      cutoffTwoNovelConditionalFiniteRatioCeilingCheck later = true) :
    ∀ source,
      source ∈ cutoffTwoEdgeLoadFullStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadFullStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelConditionalFiniteRatioCeilingLoad
              later source target ≤
          cutoffTwoNovelAllocatedConditionalKernel
            later source target := by
  unfold cutoffTwoNovelConditionalFiniteRatioCeilingCheck at hcheck
  intro source hsource target htarget
  have hpair : (source, target) ∈
      cartesian
        (cutoffTwoEdgeLoadFullStates later)
        (cutoffTwoEdgeLoadFullStates later) :=
    (mem_cartesian_iff _ _ (source, target)).2
      ⟨hsource, htarget⟩
  exact of_decide_eq_true
    (List.all_eq_true.mp hcheck (source, target) hpair)

/-- Completeness of the finite scan for its stated payment predicate: if all
ordered carrier edges are paid, every Boolean comparison reduces to true. -/
theorem cutoffTwoNovelConditionalFiniteRatioCeilingCheck_complete
    (later : Nat)
    (hcapacity : ∀ source,
      source ∈ cutoffTwoEdgeLoadFullStates later →
      ∀ target,
        target ∈ cutoffTwoEdgeLoadFullStates later →
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelConditionalFiniteRatioCeilingLoad
              later source target ≤
          cutoffTwoNovelAllocatedConditionalKernel
            later source target) :
    cutoffTwoNovelConditionalFiniteRatioCeilingCheck later = true := by
  unfold cutoffTwoNovelConditionalFiniteRatioCeilingCheck
  apply List.all_eq_true.mpr
  intro pair hpair
  have hfull :=
    (mem_cartesian_iff
      (cutoffTwoEdgeLoadFullStates later)
      (cutoffTwoEdgeLoadFullStates later) pair).mp hpair
  apply decide_eq_true
  exact hcapacity pair.1 hfull.1 pair.2 hfull.2

/-- A successful reflected payment check feeds the already-proved concrete
ceiling compiler and hence bounds the exact finite flow-capacity floor. -/
theorem cutoffTwoNovelConditionalFiniteRatioCeilingCheck_sound_floor
    (later : Nat)
    (hcheck :
      cutoffTwoNovelConditionalFiniteRatioCeilingCheck later = true) :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later :=
  cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_finiteRatioCeiling later
    (cutoffTwoNovelConditionalFiniteRatioCeilingCheck_sound_capacity
      later hcheck)

/-! ## 2. Constructive certificate-or-overloaded-edge inspection -/

/-- Exact Type-level result of inspecting a finite list of rational
comparisons.  A failed result retains the offending entry as data. -/
inductive ListComparisonOutcome
    {State : Type} (lower upper : State → Q')
    (states : List State) : Type
  | certified
      (all_le : ∀ state, state ∈ states → lower state ≤ upper state)
  | failed
      (state : State)
      (state_mem : state ∈ states)
      (not_le : ¬ lower state ≤ upper state)

/-- Recursively inspect decidable rational comparisons without eliminating a
propositional existential into `Type`. -/
def inspectListComparison
    {State : Type} (lower upper : State → Q') :
    ∀ states : List State,
      ListComparisonOutcome lower upper states
  | [] =>
      ListComparisonOutcome.certified (fun _ hmem => by cases hmem)
  | first :: rest => by
      by_cases hfirst : lower first ≤ upper first
      · cases inspectListComparison lower upper rest with
        | certified hall =>
            apply ListComparisonOutcome.certified
            intro state hstate
            cases List.mem_cons.mp hstate with
            | inl heq =>
                exact heq ▸ hfirst
            | inr hrest =>
                exact hall state hrest
        | failed state hstate hfailure =>
            exact ListComparisonOutcome.failed state
              (List.mem_cons_of_mem first hstate) hfailure
      · exact ListComparisonOutcome.failed first
          List.mem_cons_self hfirst

/-- Fixed-cutoff result of inspecting the concrete ceiling payment.  Failure
means that this sufficient conservative ceiling overloads one literal ordered
carrier edge; it does not imply failure of the exact transition-product flow. -/
inductive CutoffTwoNovelConditionalFiniteRatioCeilingOutcome
    (later : Nat) : Type
  | certified
      (floor_le : cutoffTwoNovelSimpleFlowCoercivityFloor ≤
        cutoffTwoNovelFiniteFlowCapacityFloor later)
  | overloadedCeilingEdge
      (source target : Nat)
      (source_mem : source ∈ cutoffTwoEdgeLoadFullStates later)
      (target_mem : target ∈ cutoffTwoEdgeLoadFullStates later)
      (not_ceiling_capacity : ¬
        cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelConditionalFiniteRatioCeilingLoad
              later source target ≤
          cutoffTwoNovelAllocatedConditionalKernel
            later source target)

/-- Compute either a finite capacity certificate or an explicit edge where the
concrete ratio-ceiling payment condition fails. -/
def inspectCutoffTwoNovelConditionalFiniteRatioCeiling
    (later : Nat) :
    CutoffTwoNovelConditionalFiniteRatioCeilingOutcome later := by
  cases inspectListComparison
      (fun pair : Nat × Nat =>
        cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelConditionalFiniteRatioCeilingLoad
            later pair.1 pair.2)
      (fun pair : Nat × Nat =>
        cutoffTwoNovelAllocatedConditionalKernel
          later pair.1 pair.2)
      (cartesian
        (cutoffTwoEdgeLoadFullStates later)
        (cutoffTwoEdgeLoadFullStates later)) with
  | certified hall =>
      apply CutoffTwoNovelConditionalFiniteRatioCeilingOutcome.certified
      apply cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_finiteRatioCeiling
      intro source hsource target htarget
      exact hall (source, target)
        ((mem_cartesian_iff _ _ (source, target)).2
          ⟨hsource, htarget⟩)
  | failed pair hpair hfailure =>
      have hfull :=
        (mem_cartesian_iff
          (cutoffTwoEdgeLoadFullStates later)
          (cutoffTwoEdgeLoadFullStates later) pair).mp hpair
      exact
        CutoffTwoNovelConditionalFiniteRatioCeilingOutcome.overloadedCeilingEdge
          pair.1 pair.2 hfull.1 hfull.2 hfailure

/-! ## 3. Checked cofinal schedules compile to completed contraction -/

/-- A cofinal schedule whose concrete ceiling-payment scans are all
kernel-checked.  This remains open data: the module supplies the checker and
compiler, not a proof that the scans succeed. -/
structure CutoffTwoCofinalNovelConditionalFiniteRatioCeilingCheck : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  check : ∀ request,
    cutoffTwoNovelConditionalFiniteRatioCeilingCheck
      (anchor request) = true

namespace CutoffTwoCofinalNovelConditionalFiniteRatioCeilingCheck

def toCofinalNovelConditionalFiniteRatioCeilingBound
    (checked : CutoffTwoCofinalNovelConditionalFiniteRatioCeilingCheck) :
    CutoffTwoCofinalNovelConditionalFiniteRatioCeilingBound where
  anchor := checked.anchor
  anchor_ge := checked.anchor_ge
  ceiling_capacity := fun request =>
    cutoffTwoNovelConditionalFiniteRatioCeilingCheck_sound_capacity
      (checked.anchor request) (checked.check request)

def toCompletedStrictContractionData
    (checked : CutoffTwoCofinalNovelConditionalFiniteRatioCeilingCheck) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (by decide) (by decide) 0 :=
  checked.toCofinalNovelConditionalFiniteRatioCeilingBound.toCompletedStrictContractionData

end CutoffTwoCofinalNovelConditionalFiniteRatioCeilingCheck

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision.cutoffTwoNovelConditionalFiniteRatioCeilingCheck_sound_capacity
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision.cutoffTwoNovelConditionalFiniteRatioCeilingCheck_complete
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision.cutoffTwoNovelConditionalFiniteRatioCeilingCheck_sound_floor
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision.inspectCutoffTwoNovelConditionalFiniteRatioCeiling
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalFiniteRatioCeilingDecision.CutoffTwoCofinalNovelConditionalFiniteRatioCeilingCheck.toCompletedStrictContractionData
