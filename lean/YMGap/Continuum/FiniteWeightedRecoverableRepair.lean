/-
# Recoverable postprocessing of a weighted finite fiber

Suppose a code pays every complete weighted inverse fiber up to a global
factor.  A receiver map may identify sources only when their codes agree, and
each receiver weight may dominate the corresponding code weight up to an
insertion factor.  A single rational budget then pays every complete receiver
fiber.

This is the reusable finite algebra behind guarded source repair.  It keeps
the many-to-one code fiber explicit and never replaces recoverability by a
false source-level injectivity claim.

Constructive contract: finite filters and exact rational order only; no
`Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4HalfTimeReflectionLocalPairConditionalLaw

namespace YMGap.Continuum.FiniteWeightedRecoverableRepair

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_filter_le_filter_local
    {A : Type} (value : A → Q') (left right : A → Bool)
    (hvalue : ∀ item, (0 : Q') ≤ value item)
    (himp : ∀ item, left item = true → right item = true) :
    ∀ items : List A,
      listQSum value (items.filter left) ≤
        listQSum value (items.filter right)
  | [] => Q'.le_refl' 0
  | head :: tail => by
      have ih := listQSum_filter_le_filter_local
        value left right hvalue himp tail
      cases hleft : left head with
      | false =>
          cases hright : right head with
          | false => simpa only [List.filter, hleft, hright, listQSum] using ih
          | true =>
              simp only [List.filter, hleft, hright, listQSum]
              have hhead : listQSum value (tail.filter right) ≤
                  value head + listQSum value (tail.filter right) := by
                have hscaled := Q'.add_le_add_right
                  (0 : Q') (value head)
                  (listQSum value (tail.filter right)) (hvalue head)
                rwa [Q'.zero_add'] at hscaled
              exact Q'.le_trans' _ _ _ ih hhead
      | true =>
          have hright : right head = true := himp head hleft
          simp only [List.filter, hleft, hright, listQSum]
          exact Q'.add_le_add_left (value head) _ _ ih

private theorem swap_nested_mul (first second value : Q') :
    first * (second * value) ≈ second * (first * value) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv first second value)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ value
      (Q'.mul_comm_eqv first second)) ?_
  exact Q'.mul_assoc_eqv second first value

private theorem swap_product_mul (first second value : Q') :
    (first * second) * value ≈ second * (first * value) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv first second value) ?_
  exact swap_nested_mul first second value

/-- **Recoverable weighted-repair theorem.**  A fiber estimate for `code`
passes to `repair` whenever equal receivers recover equal codes and insertion
pays the code weight. -/
theorem recoverableRepair_fiberWeight_le
    {Source Code Receiver : Type}
    [DecidableEq Code] [DecidableEq Receiver]
    (sources : List Source) (sourceWeight : Source → Q')
    (sourceWeight_nonnegative : ∀ source, (0 : Q') ≤ sourceWeight source)
    (code : Source → Code) (codeWeight : Code → Q')
    (codeWeight_nonnegative : ∀ item, (0 : Q') ≤ codeWeight item)
    (repair : Source → Receiver) (receiverWeight : Receiver → Q')
    (receiverWeight_nonnegative : ∀ target, (0 : Q') ≤ receiverWeight target)
    (guard global insertion rho : Q')
    (guard_pos : (0 : Q') < guard)
    (rho_nonnegative : (0 : Q') ≤ rho)
    (code_fiber_bound : ∀ item,
      guard * fiberWeight sources sourceWeight code item ≤
        global * codeWeight item)
    (repair_recovers_code : ∀ first second,
      repair first = repair second → code first = code second)
    (insertion_floor : ∀ source,
      insertion * codeWeight (code source) ≤
        receiverWeight (repair source))
    (rate_budget : rho * global ≤ insertion * guard)
    (target : Receiver) :
    rho * fiberWeight sources sourceWeight repair target ≤
      receiverWeight target := by
  cases hfiber : sources.filter
      (fun source => decide (target = repair source)) with
  | nil =>
      unfold fiberWeight
      rw [hfiber]
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_zero_eqv rho))
        (receiverWeight_nonnegative target)
  | cons first rest =>
      have hfirstMem : first ∈ sources.filter
          (fun source => decide (target = repair source)) := by
        rw [hfiber]
        exact List.mem_cons_self
      have hfirstEq : target = repair first :=
        of_decide_eq_true (List.mem_filter.mp hfirstMem).2
      have hfilter :
          fiberWeight sources sourceWeight repair target ≤
            fiberWeight sources sourceWeight code (code first) := by
        unfold fiberWeight
        apply listQSum_filter_le_filter_local
        · exact sourceWeight_nonnegative
        · intro source hsource
          have hsourceEq : target = repair source :=
            of_decide_eq_true hsource
          have hrepairEq : repair source = repair first :=
            hsourceEq.symm.trans hfirstEq
          exact decide_eq_true
            (repair_recovers_code source first hrepairEq).symm
      have hscaledFilter := Q'.mul_le_mul_of_nonneg_left _ _ rho
        hfilter rho_nonnegative
      have hcode := code_fiber_bound (code first)
      have hscaledCode := Q'.mul_le_mul_of_nonneg_left _ _ rho
        hcode rho_nonnegative
      have hbudget := Q'.mul_le_mul_of_nonneg_right _ _
        (codeWeight (code first)) rate_budget
        (codeWeight_nonnegative (code first))
      have hinsertion := insertion_floor first
      have hinsertionScaled := Q'.mul_le_mul_of_nonneg_left _ _ guard
        hinsertion (Q'.le_of_lt guard_pos)
      have hguarded :
          guard *
              (rho * fiberWeight sources sourceWeight code (code first)) ≤
            guard * receiverWeight target := by
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv
            (swap_nested_mul guard rho
              (fiberWeight sources sourceWeight code (code first))))
          (Q'.le_trans' _ _ _ hscaledCode
            (Q'.le_trans' _ _ _
              (Q'.le_of_eqv
                (Q'.eqv_symm
                  (Q'.mul_assoc_eqv rho global
                    (codeWeight (code first)))))
              (Q'.le_trans' _ _ _ hbudget
                (Q'.le_trans' _ _ _
                  (Q'.le_of_eqv
                    (swap_product_mul insertion guard
                      (codeWeight (code first))))
                  (by
                    rw [hfirstEq]
                    exact hinsertionScaled)))))
      have hcodeToTarget :
          rho * fiberWeight sources sourceWeight code (code first) ≤
            receiverWeight target :=
        Q'.le_of_mul_le_mul_left hguarded guard_pos
      exact Q'.le_trans' _ _ _ hscaledFilter hcodeToTarget

#print axioms recoverableRepair_fiberWeight_le

end YMGap.Continuum.FiniteWeightedRecoverableRepair
