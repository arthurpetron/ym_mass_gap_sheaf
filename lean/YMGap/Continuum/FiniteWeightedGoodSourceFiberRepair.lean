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
#print axioms WeightedGoodSourceFiberRepairCertificate.fraction_mul_sourceMass_le_goodTargetMass

end WeightedGoodSourceFiberRepairCertificate

end YMGap.Continuum.FiniteWeightedGoodSourceFiberRepair
