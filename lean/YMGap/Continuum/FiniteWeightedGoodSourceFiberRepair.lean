/-
# Weighted target-fiber repair into a good finite subcarrier

The pointwise Peierls compiler first replaces every source-to-target weight
ratio by one global minimum and then pays an unweighted fiber cardinality.
That factorization is useful for bounded local maps, but it destroys a
geometric tail when larger inverse codes have smaller weights.

This module retains the weighted inverse fiber itself.  A deterministic
repair into a duplicate-free good target carrier has a displayed fraction
`rho` if, for every good target,

```text
rho * sum(sourceWeight over the repair fiber) <= targetWeight(target).
```

Finite Fubini then proves directly that the good target mass contains at
least `rho` of the complete source mass.  No pointwise minimum and no raw
fiber count occur.  This is the form consumed by component reconstruction
plus a weighted Peierls/entropy estimate.

Constructive contract: exact finite rational fibers and explicit witnesses
only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.FiniteWeightedGoodSourceFiberRepair

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → left item ≤ right item) →
        listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm =>
      Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hterm item (List.mem_cons_of_mem head hitem)))

/-- A deterministic repair whose complete weighted inverse fiber fits inside
the capacity of every displayed good target.  The fraction is part of the
certificate, so parameter-uniform applications must expose the same `rho` in
their type. -/
structure WeightedGoodSourceFiberRepairCertificate
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (goodTargets : List Target) (targetWeight : Target → Q')
    (rho : Q') : Type where
  rho_pos : (0 : Q') < rho
  rho_le_one : rho ≤ (1 : Q')
  goodTargets_nodup : goodTargets.Nodup
  repair : Source → Target
  repair_mem : ∀ source, source ∈ sources → repair source ∈ goodTargets
  weighted_fiber_capacity : ∀ target, target ∈ goodTargets →
    rho * fiberWeight sources sourceWeight repair target ≤
      targetWeight target

/-- A component-style producer for weighted-fiber capacity.  Each source has
its own reconstruction rate, and the rates—not the source cardinalities—are
summed over a common repair target. -/
structure VariableRateGoodSourceRepairCertificate
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (goodTargets : List Target) (targetWeight : Target → Q')
    (rho : Q') : Type where
  rho_pos : (0 : Q') < rho
  rho_le_one : rho ≤ (1 : Q')
  goodTargets_nodup : goodTargets.Nodup
  targetWeight_nonnegative : ∀ target, target ∈ goodTargets →
    (0 : Q') ≤ targetWeight target
  repair : Source → Target
  repair_mem : ∀ source, source ∈ sources → repair source ∈ goodTargets
  rate : Source → Q'
  source_weight_le_rate_mul_target : ∀ source, source ∈ sources →
    sourceWeight source ≤ targetWeight (repair source) * rate source
  scaled_rate_fiber_le_one : ∀ target, target ∈ goodTargets →
    rho * fiberWeight sources rate repair target ≤ (1 : Q')

namespace VariableRateGoodSourceRepairCertificate

private theorem reorder_three (left middle right : Q') :
    left * (middle * right) ≈ middle * (left * right) := by
  exact Q'.eqv_trans _ ((left * middle) * right) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv left middle right))
    (Q'.eqv_trans _ ((middle * left) * right) _
      (Q'.mul_eqv_congr_right _ _ right
        (Q'.mul_comm_eqv left middle))
      (Q'.mul_assoc_eqv middle left right))

/-- Variable source rates whose target-fiber sum is controlled construct the
direct weighted-fiber certificate without taking a pointwise minimum. -/
def toWeightedFiberRepairCertificate
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {sourceWeight : Source → Q'}
    {goodTargets : List Target} {targetWeight : Target → Q'}
    {rho : Q'}
    (data : VariableRateGoodSourceRepairCertificate
      sources sourceWeight goodTargets targetWeight rho) :
    WeightedGoodSourceFiberRepairCertificate
      sources sourceWeight goodTargets targetWeight rho where
  rho_pos := data.rho_pos
  rho_le_one := data.rho_le_one
  goodTargets_nodup := data.goodTargets_nodup
  repair := data.repair
  repair_mem := data.repair_mem
  weighted_fiber_capacity := by
    intro target htarget
    let fiber := sources.filter fun source =>
      decide (target = data.repair source)
    have hsourceLoad :
        fiberWeight sources sourceWeight data.repair target ≤
          targetWeight target *
            fiberWeight sources data.rate data.repair target := by
      unfold fiberWeight
      have hterms :
          listQSum sourceWeight fiber ≤
            listQSum
              (fun source => targetWeight target * data.rate source)
              fiber := by
        apply listQSum_le_termwise_local
        intro source hsource
        have hparts := List.mem_filter.mp hsource
        have heq : target = data.repair source :=
          of_decide_eq_true hparts.2
        have hbound :=
          data.source_weight_le_rate_mul_target source hparts.1
        rw [← heq] at hbound
        exact hbound
      exact Q'.le_trans' _ _ _ hterms
        (Q'.le_of_eqv
          (listQSum_mul_left (targetWeight target) data.rate fiber))
    have hscaledLoad := Q'.mul_le_mul_of_nonneg_left _ _ rho
      hsourceLoad (Q'.le_of_lt data.rho_pos)
    have hreorder :
        rho *
            (targetWeight target *
              fiberWeight sources data.rate data.repair target) ≈
          targetWeight target *
            (rho * fiberWeight sources data.rate data.repair target) :=
      reorder_three rho (targetWeight target)
        (fiberWeight sources data.rate data.repair target)
    have hrate := data.scaled_rate_fiber_le_one target htarget
    have htargetScaled := Q'.mul_le_mul_of_nonneg_left _ _
      (targetWeight target) hrate
      (data.targetWeight_nonnegative target htarget)
    exact Q'.le_trans' _ _ _ hscaledLoad
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder)
        (Q'.le_trans' _ _ _ htargetScaled
          (Q'.le_of_eqv (Q'.mul_one_eqv (targetWeight target)))))

end VariableRateGoodSourceRepairCertificate

namespace WeightedGoodSourceFiberRepairCertificate

/-- **Weighted-fiber Peierls theorem.**  Per-target weighted capacity sums to
the displayed global good-source density without introducing a raw
congestion factor. -/
theorem fraction_mul_sourceMass_le_goodTargetMass
    {Source Target : Type} [DecidableEq Target]
    {sources : List Source} {sourceWeight : Source → Q'}
    {goodTargets : List Target} {targetWeight : Target → Q'}
    {rho : Q'}
    (data : WeightedGoodSourceFiberRepairCertificate
      sources sourceWeight goodTargets targetWeight rho) :
    rho * listQSum sourceWeight sources ≤
      listQSum targetWeight goodTargets := by
  let pushed := fun target =>
    fiberWeight sources sourceWeight data.repair target
  have htotal : listQSum pushed goodTargets ≈
      listQSum sourceWeight sources :=
    fiberWeight_total sources sourceWeight data.repair goodTargets
      data.goodTargets_nodup data.repair_mem
  have hscale :
      listQSum (fun target => rho * pushed target) goodTargets ≈
        rho * listQSum pushed goodTargets :=
    listQSum_mul_left rho pushed goodTargets
  have hrecode :
      rho * listQSum sourceWeight sources ≈
        listQSum (fun target => rho * pushed target) goodTargets :=
    Q'.eqv_trans _ (rho * listQSum pushed goodTargets) _
      (Q'.mul_eqv_congr_left rho _ _ (Q'.eqv_symm htotal))
      (Q'.eqv_symm hscale)
  have hcapacity :
      listQSum (fun target => rho * pushed target) goodTargets ≤
        listQSum targetWeight goodTargets := by
    apply listQSum_le_termwise_local
    intro target htarget
    exact data.weighted_fiber_capacity target htarget
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hrecode) hcapacity

#print axioms WeightedGoodSourceFiberRepairCertificate
#print axioms VariableRateGoodSourceRepairCertificate
#print axioms VariableRateGoodSourceRepairCertificate.toWeightedFiberRepairCertificate
#print axioms WeightedGoodSourceFiberRepairCertificate.fraction_mul_sourceMass_le_goodTargetMass

end WeightedGoodSourceFiberRepairCertificate

end YMGap.Continuum.FiniteWeightedGoodSourceFiberRepair
