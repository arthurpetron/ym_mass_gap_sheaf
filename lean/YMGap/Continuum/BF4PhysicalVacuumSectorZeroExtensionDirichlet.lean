/-
# Zero extension preserves the actual vacuum-sector Dirichlet energy

Extend a rational observable by zero outside the exact finite vacuum
component. There are no physical OS kernel entries crossing its boundary;
zero-marginal rows contribute nothing either. Its full half-state Dirichlet
energy is therefore exactly the canonical indexed sector energy, with no
normalization or cardinality loss. Both presentations use the same
partition-normalized physical joint kernel.

This exact identity enables reuse of the global inward-mate energy bounds
on the sector. It is not an all-vector coercivity estimate or a spectral gap.
No new analytic hypothesis, sorry, classical axiom, or enlarged proof budget.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet

namespace YMGap.Continuum.BF4PhysicalVacuumSectorZeroExtensionDirichlet

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateSectorLocalSourceCarrier
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-- Executable zero extension from the exact state-level vacuum component. -/
def vacuumSectorZeroExtension (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : EdgeLabelling → Q') (state : EdgeLabelling) : Q' :=
  if centralPhysicalFiniteVacuumSectorStateB w hw K half state then coefficient state else 0

theorem vacuumSectorZeroExtension_on_sector
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : EdgeLabelling → Q') {state : EdgeLabelling}
    (hstate : state ∈ centralPhysicalFiniteVacuumSectorStates w hw K half) :
    vacuumSectorZeroExtension w hw K half coefficient state = coefficient state := by
  have htest := (centralPhysicalFiniteVacuumSectorStateB_eq_true_iff w hw K half
    (centralPhysicalFiniteVacuumSectorState_mem_halfStates w hw K half hstate)).mpr hstate
  unfold vacuumSectorZeroExtension
  rw [htest]
  rfl

/-- The normalized physical kernel vanishes across the exact sector boundary,
including targets with zero marginal. -/
theorem normalizedKernel_eqv_zero_of_sector_outside
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    {source target : EdgeLabelling}
    (hsource : source ∈ centralPhysicalFiniteVacuumSectorStates w hw K half)
    (htarget : target ∈ centralHalfStates K half)
    (houtside : target ∉ centralPhysicalFiniteVacuumSectorStates w hw K half) :
    centralNormalizedPhysicalReflectedKernel w hw K half source target ≈ 0 := by
  by_cases hpos : (0 : Q') < centralPhysicalRowMarginal w hw K half target
  · have hpositive : target ∈ centralPositiveHalfStates w hw K half :=
      mem_centralPositiveHalfStates_iff.mpr ⟨htarget, hpos⟩
    obtain ⟨sourceIndex, hsourceIndex, hsourceEq⟩ := List.mem_map.mp hsource
    obtain ⟨targetIndex, htargetIndex, htargetEq⟩ :=
      centralPhysicalFiniteStateAt_exists w hw K half hpositive
    have hnot : targetIndex ∉ centralPhysicalFiniteVacuumSectorIndices w hw K half :=
      fun hi => houtside (centralPhysicalFiniteVacuumSectorState_mem_of_index
        w hw K half hi htargetEq)
    have hraw := centralPhysicalFiniteVacuumSector_rowClosed
      w hw K half hsourceIndex htargetIndex hnot
    unfold centralPhysicalFiniteRawKernel at hraw
    rw [hsourceEq, htargetEq] at hraw
    unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
    exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hraw)
      (Q'.zero_mul_eqv _)
  · exact centralNormalizedPhysicalReflectedKernel_eqv_zero_of_target_not_pos
      (centralPhysicalFiniteVacuumSectorState_mem_halfStates w hw K half hsource)
      htarget hpos

private theorem sum_if_eq_filter {A : Type} (test : A → Bool) (value : A → Q') :
    ∀ items : List A,
    listQSum (fun item => if test item then value item else 0) items ≈
      listQSum value (items.filter test)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
    cases ht : test head with
    | true =>
      simp only [listQSum, List.filter, ht, if_true]
      exact Q'.add_eqv_congr' (Q'.eqv_refl _) (sum_if_eq_filter test value tail)
    | false =>
      simp only [listQSum, List.filter, ht, Bool.false_eq_true, if_false, Q'.zero_add']
      exact sum_if_eq_filter test value tail

private theorem sum_zero {A : Type} : ∀ items : List A,
    listQSum (fun _ => (0 : Q')) items ≈ 0
  | [] => Q'.eqv_refl 0
  | _ :: tail => by
    change 0 + listQSum (fun _ => (0 : Q')) tail ≈ 0
    rw [Q'.zero_add']
    exact sum_zero tail

/-- Finite closed-event identity; no equality decision on the state type. -/
theorem finiteDirichlet_zeroExtension_eq_filter {A : Type}
    (states : List A) (test : A → Bool) (coefficient : A → Q')
    (joint : A → A → Q')
    (hcross : ∀ left, left ∈ states → ∀ right, right ∈ states →
      test left ≠ test right → joint left right ≈ 0) :
    finiteJointDirichletEnergy states
        (fun state => if test state then coefficient state else 0) joint ≈
      finiteJointDirichletEnergy (states.filter test) coefficient joint := by
  let energy := fun left right => joint left right *
    ((coefficient left + -coefficient right) * (coefficient left + -coefficient right))
  have hpoint : ∀ left, left ∈ states → ∀ right, right ∈ states →
      joint left right *
        (((if test left then coefficient left else 0) +
            -(if test right then coefficient right else 0)) *
          ((if test left then coefficient left else 0) +
            -(if test right then coefficient right else 0))) ≈
        (if test left then (if test right then energy left right else 0) else 0) := by
    intro left hl right hr
    cases hleft : test left <;> cases hright : test right
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (by decide :
          ((0 : Q') + -0) * (0 + -0) ≈ 0)) (Q'.mul_zero_eqv _)
    · simp only [Bool.false_eq_true, if_false, if_true]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (hcross left hl right hr (by rw [hleft, hright]; decide)))
        (Q'.zero_mul_eqv _)
    · simp only [Bool.false_eq_true, if_false, if_true]
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (hcross left hl right hr (by rw [hleft, hright]; decide)))
        (Q'.zero_mul_eqv _)
    · exact Q'.eqv_refl _
  unfold finiteJointDirichletEnergy
  refine Q'.eqv_trans _
    (listQSum (fun left => if test left then
      listQSum (fun right => if test right then energy left right else 0) states else 0) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro left hl
    refine Q'.eqv_trans _ _ _ (listQSum_congr_on _ _ states (hpoint left hl)) ?_
    cases ht : test left
    · simp only [Bool.false_eq_true, if_false]
      exact sum_zero states
    · exact Q'.eqv_refl _
  · refine Q'.eqv_trans _ _ _ (sum_if_eq_filter test _ states) ?_
    apply listQSum_congr
    intro left
    exact sum_if_eq_filter test (energy left) states

private theorem map_nodup_on {A B : Type} (f : A → B) : ∀ items : List A,
    items.Nodup → (∀ x, x ∈ items → ∀ y, y ∈ items → f x = f y → x = y) →
    (items.map f).Nodup
  | [], _, _ => List.nodup_nil
  | head :: tail, hnd, hinj => by
    apply List.nodup_cons.mpr
    refine ⟨?_, map_nodup_on f tail (List.nodup_cons.mp hnd).2
      (fun x hx y hy => hinj x (List.mem_cons_of_mem head hx) y (List.mem_cons_of_mem head hy))⟩
    intro hmem
    obtain ⟨item, hi, heq⟩ := List.mem_map.mp hmem
    have he := hinj item (List.mem_cons_of_mem head hi) head List.mem_cons_self heq
    exact (List.nodup_cons.mp hnd).1 (he ▸ hi)

theorem vacuumSectorStates_nodup (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    (centralPhysicalFiniteVacuumSectorStates w hw K half).Nodup := by
  apply map_nodup_on
  · exact centralPhysicalFiniteVacuumSectorIndices_nodup w hw K half
  · intro left hl right hr heq
    exact centralPhysicalFiniteStateAt_injective_of_lt
      (centralPhysicalFiniteVacuumSectorIndex_lt w hw K half hl)
      (centralPhysicalFiniteVacuumSectorIndex_lt w hw K half hr) heq

private theorem nonnegative_sum_same_members {A : Type}
    (left right : List A) (hleft : left.Nodup) (hright : right.Nodup)
    (hmem : ∀ item, item ∈ left ↔ item ∈ right) (weight : A → Q')
    (hnonnegative : ∀ item, (0 : Q') ≤ weight item) :
    listQSum weight left ≈ listQSum weight right := by
  apply Int.le_antisymm
  · exact listQSum_le_of_injective_nodup left right weight weight id hleft hright
      (fun item hi => (hmem item).mp hi) (fun _ _ _ _ he => he)
      (fun _ _ => Q'.le_refl' _) (fun item _ => hnonnegative item)
  · exact listQSum_le_of_injective_nodup right left weight weight id hright hleft
      (fun item hi => (hmem item).mpr hi) (fun _ _ _ _ he => he)
      (fun _ _ => Q'.le_refl' _) (fun item _ => hnonnegative item)

/-- **Same-object identity:** zero extension has exactly the canonical indexed
vacuum-sector energy, with the existing physical joint normalization. -/
theorem vacuumSectorZeroExtension_Dirichlet_eq_indexed
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (coefficient : EdgeLabelling → Q') :
    finiteJointDirichletEnergy (centralHalfStates K half)
        (vacuumSectorZeroExtension w hw K half coefficient)
        (centralNormalizedPhysicalReflectedKernel w hw K half) ≈
      finiteJointDirichletEnergy (centralPhysicalFiniteVacuumSectorIndices w hw K half)
        (centralPhysicalFiniteCoefficient w hw K half coefficient)
        (centralPhysicalFiniteKernel w hw K half) := by
  let test := centralPhysicalFiniteVacuumSectorStateB w hw K half
  let filtered := (centralHalfStates K half).filter test
  let sector := centralPhysicalFiniteVacuumSectorStates w hw K half
  let joint := centralNormalizedPhysicalReflectedKernel w hw K half
  have hcross : ∀ left, left ∈ centralHalfStates K half →
      ∀ right, right ∈ centralHalfStates K half → test left ≠ test right → joint left right ≈ 0 := by
    intro left hl right hr hne
    have hleft := centralPhysicalFiniteVacuumSectorStateB_eq_true_iff w hw K half hl
    have hright := centralPhysicalFiniteVacuumSectorStateB_eq_true_iff w hw K half hr
    cases hlt : test left <;> cases hrt : test right
    · exact False.elim (hne (hlt.trans hrt.symm))
    · exact Q'.eqv_trans _ _ _ (centralNormalizedPhysicalReflectedKernel_symm hl hr)
        (normalizedKernel_eqv_zero_of_sector_outside w hw K half (hright.mp hrt) hl
          (fun hs => by
            have ht : test left = true := hleft.mpr hs
            rw [hlt] at ht
            cases ht))
    · exact normalizedKernel_eqv_zero_of_sector_outside w hw K half (hleft.mp hlt) hr
        (fun hs => by
          have ht : test right = true := hright.mpr hs
          rw [hrt] at ht
          cases ht)
    · exact False.elim (hne (hlt.trans hrt.symm))
  have hfiltered := finiteDirichlet_zeroExtension_eq_filter
    (centralHalfStates K half) test coefficient joint hcross
  have hmem : ∀ state, state ∈ filtered ↔ state ∈ sector := by
    intro state
    constructor
    · intro hs
      have hp := List.mem_filter.mp hs
      exact (centralPhysicalFiniteVacuumSectorStateB_eq_true_iff w hw K half hp.1).mp hp.2
    · intro hs
      have hh := centralPhysicalFiniteVacuumSectorState_mem_halfStates w hw K half hs
      exact List.mem_filter.mpr ⟨hh,
        (centralPhysicalFiniteVacuumSectorStateB_eq_true_iff w hw K half hh).mpr hs⟩
  have hfnd : filtered.Nodup := List.filter_sublist.nodup (centralHalfStates_nodup K half)
  have hsnd : sector.Nodup := vacuumSectorStates_nodup w hw K half
  let energy := fun left right => joint left right *
    ((coefficient left + -coefficient right) * (coefficient left + -coefficient right))
  have he0 : ∀ left right, (0 : Q') ≤ energy left right := fun left right =>
    Q'.mul_nonneg _ _ (centralNormalizedPhysicalReflectedKernel_nonnegative hw K half left right)
      (q_mul_self_nonneg _)
  have hsector : finiteJointDirichletEnergy filtered coefficient joint ≈
      finiteJointDirichletEnergy sector coefficient joint := by
    refine Q'.eqv_trans _ (listQSum (fun left => listQSum (energy left) sector) filtered) _ ?_ ?_
    · apply listQSum_congr
      intro left
      exact nonnegative_sum_same_members filtered sector hfnd hsnd hmem (energy left) (he0 left)
    · exact nonnegative_sum_same_members filtered sector hfnd hsnd hmem _
        (fun left => listQSum_nonnegative_on _ _ (fun right _ => he0 left right))
  refine Q'.eqv_trans _ _ _ hfiltered (Q'.eqv_trans _ _ _ hsector ?_)
  unfold finiteJointDirichletEnergy sector centralPhysicalFiniteVacuumSectorStates
  rw [listQSum_map]
  apply listQSum_congr
  intro left
  rw [listQSum_map]
  exact Q'.eqv_refl _

end YMGap.Continuum.BF4PhysicalVacuumSectorZeroExtensionDirichlet

#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorZeroExtensionDirichlet.vacuumSectorZeroExtension_on_sector
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorZeroExtensionDirichlet.normalizedKernel_eqv_zero_of_sector_outside
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorZeroExtensionDirichlet.finiteDirichlet_zeroExtension_eq_filter
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorZeroExtensionDirichlet.vacuumSectorStates_nodup
#print axioms YMGap.Continuum.BF4PhysicalVacuumSectorZeroExtensionDirichlet.vacuumSectorZeroExtension_Dirichlet_eq_indexed
