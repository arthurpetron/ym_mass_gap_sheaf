/-
# Exact positive rate for a finite weighted repair into another carrier

For a finite source carrier, a finite target carrier, and a deterministic
repair between them, take the capped minimum of the exact target-weight to
inverse-fiber-weight ratios.  Strict positivity of both displayed weights
gives an explicit positive common rate, and the resulting data is exactly a
`WeightedGoodSourceFiberRepairCertificate`.

Unlike the endomap-specialized construction, source and target types and
weights may differ.  No stability under variation of either carrier is
claimed.

Constructive contract: exact finite filters, positive rational division, and
finite minima only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
import YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity
import YMGap.Continuum.FiniteWeightedGoodSourceFiberRepair

namespace YMGap.Continuum.FinitePositiveWeightedGoodSourceFiberRate

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity
open YMGap.Continuum.FiniteWeightedGoodSourceFiberRepair
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

def finitePositiveMapFiberItems
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (repair : Source → Target) (target : Target) :
    List Source :=
  sources.filter fun source => decide (target = repair source)

theorem finitePositiveMapFiberWeight_pos_of_ne_nil
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (sourceWeight_pos : ∀ source, (0 : Q') < sourceWeight source)
    (repair : Source → Target) (target : Target)
    (hne : finitePositiveMapFiberItems sources repair target ≠ []) :
    (0 : Q') < fiberWeight sources sourceWeight repair target := by
  cases hfiber : finitePositiveMapFiberItems sources repair target with
  | nil => exact False.elim (hne hfiber)
  | cons first rest =>
      change (0 : Q') < listQSum sourceWeight
        (finitePositiveMapFiberItems sources repair target)
      rw [hfiber]
      exact listQSum_pos_of_mem sourceWeight
        (fun source => Q'.le_of_lt (sourceWeight_pos source))
        (first :: rest) List.mem_cons_self (sourceWeight_pos first)

def finitePositiveMapFiberRatio
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (sourceWeight_pos : ∀ source, (0 : Q') < sourceWeight source)
    (targetWeight : Target → Q')
    (repair : Source → Target) (target : Target) : Q' :=
  if hempty : finitePositiveMapFiberItems sources repair target = [] then
    1
  else
    Q'.divPos (targetWeight target)
      (fiberWeight sources sourceWeight repair target)
      (finitePositiveMapFiberWeight_pos_of_ne_nil
        sources sourceWeight sourceWeight_pos repair target hempty)

theorem finitePositiveMapFiberRatio_pos
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (sourceWeight_pos : ∀ source, (0 : Q') < sourceWeight source)
    (targetWeight : Target → Q')
    (targetWeight_pos : ∀ target, (0 : Q') < targetWeight target)
    (repair : Source → Target) (target : Target) :
    (0 : Q') < finitePositiveMapFiberRatio
      sources sourceWeight sourceWeight_pos targetWeight repair target := by
  unfold finitePositiveMapFiberRatio
  by_cases hempty : finitePositiveMapFiberItems sources repair target = []
  · rw [dif_pos hempty]
    decide
  · rw [dif_neg hempty]
    exact Q'.divPos_pos _ _ _ (targetWeight_pos target)

def finitePositiveMapFiberRate
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (sourceWeight_pos : ∀ source, (0 : Q') < sourceWeight source)
    (targets : List Target) (targetWeight : Target → Q')
    (repair : Source → Target) : Q' :=
  listPositiveMinOne
    (finitePositiveMapFiberRatio
      sources sourceWeight sourceWeight_pos targetWeight repair)
    targets

theorem finitePositiveMapFiberRate_pos
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (sourceWeight_pos : ∀ source, (0 : Q') < sourceWeight source)
    (targets : List Target) (targetWeight : Target → Q')
    (targetWeight_pos : ∀ target, (0 : Q') < targetWeight target)
    (repair : Source → Target) :
    (0 : Q') < finitePositiveMapFiberRate
      sources sourceWeight sourceWeight_pos targets targetWeight repair := by
  unfold finitePositiveMapFiberRate
  apply listPositiveMinOne_pos
  intro target _
  exact finitePositiveMapFiberRatio_pos
    sources sourceWeight sourceWeight_pos targetWeight targetWeight_pos
    repair target

private theorem listPositiveMinOne_le_one_local
    {Target : Type} (value : Target → Q') : ∀ targets : List Target,
    listPositiveMinOne value targets ≤ (1 : Q')
  | [] => Q'.le_refl' 1
  | _ :: rest =>
      Q'.le_trans' _ _ _ (Q'.min_le_right' _ _)
        (listPositiveMinOne_le_one_local value rest)

theorem finitePositiveMapFiberRate_le_one
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (sourceWeight_pos : ∀ source, (0 : Q') < sourceWeight source)
    (targets : List Target) (targetWeight : Target → Q')
    (repair : Source → Target) :
    finitePositiveMapFiberRate
        sources sourceWeight sourceWeight_pos targets targetWeight repair ≤
      (1 : Q') := by
  unfold finitePositiveMapFiberRate
  exact listPositiveMinOne_le_one_local _ targets

private theorem le_listPositiveMinOne_of_forall_local
    {Target : Type} (value : Target → Q') (candidate : Q') :
    ∀ targets : List Target,
      candidate ≤ (1 : Q') →
      (∀ target, target ∈ targets → candidate ≤ value target) →
      candidate ≤ listPositiveMinOne value targets
  | [], hunit, _ => hunit
  | first :: rest, hunit, hall => by
      unfold listPositiveMinOne Q'.min'
      by_cases hle : value first ≤ listPositiveMinOne value rest
      · rw [if_pos hle]
        exact hall first List.mem_cons_self
      · rw [if_neg hle]
        exact le_listPositiveMinOne_of_forall_local value candidate rest
          hunit (fun target htarget =>
            hall target (List.mem_cons_of_mem first htarget))

/-- **Universal property of the exact source-to-target fiber rate.**  Any
unit-capped candidate which pays every displayed weighted inverse fiber lies
below the computed finite minimum. -/
theorem le_finitePositiveMapFiberRate_of_mul_fiberWeight_le
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (sourceWeight_pos : ∀ source, (0 : Q') < sourceWeight source)
    (targets : List Target) (targetWeight : Target → Q')
    (repair : Source → Target) (candidate : Q')
    (candidate_le_one : candidate ≤ (1 : Q'))
    (candidate_pays : ∀ target, target ∈ targets →
      candidate * fiberWeight sources sourceWeight repair target ≤
        targetWeight target) :
    candidate ≤ finitePositiveMapFiberRate
      sources sourceWeight sourceWeight_pos targets targetWeight repair := by
  unfold finitePositiveMapFiberRate
  apply le_listPositiveMinOne_of_forall_local
  · exact candidate_le_one
  · intro target htarget
    unfold finitePositiveMapFiberRatio
    by_cases hempty : finitePositiveMapFiberItems
        sources repair target = []
    · rw [dif_pos hempty]
      exact candidate_le_one
    · rw [dif_neg hempty]
      exact Q'.le_divPos_of_mul_le
        (targetWeight target)
        (fiberWeight sources sourceWeight repair target)
        (finitePositiveMapFiberWeight_pos_of_ne_nil
          sources sourceWeight sourceWeight_pos repair target hempty)
        (candidate_pays target htarget)

private theorem listQSum_filter_le_local
    {Source : Type} (sourceWeight : Source → Q')
    (test : Source → Bool)
    (sourceWeight_nonnegative : ∀ source, (0 : Q') ≤ sourceWeight source) :
    ∀ sources : List Source,
      listQSum sourceWeight (sources.filter test) ≤
        listQSum sourceWeight sources
  | [] => Q'.le_refl' 0
  | first :: rest => by
      have ih := listQSum_filter_le_local
        sourceWeight test sourceWeight_nonnegative rest
      cases htest : test first with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            ↓reduceIte, listQSum]
          have hmono : listQSum sourceWeight rest ≤
              sourceWeight first + listQSum sourceWeight rest := by
            have hadd := Q'.add_le_add_right
              (0 : Q') (sourceWeight first)
              (listQSum sourceWeight rest)
              (sourceWeight_nonnegative first)
            rwa [Q'.zero_add'] at hadd
          exact Q'.le_trans' _ _ _ ih hmono
      | true =>
          simp only [List.filter_cons, htest, ↓reduceIte, listQSum]
          exact Q'.add_le_add_left (sourceWeight first) _ _ ih

private theorem listQSum_filter_le_filter_local
    {Source : Type} (sourceWeight : Source → Q')
    (left right : Source → Bool)
    (sourceWeight_nonnegative : ∀ source, (0 : Q') ≤ sourceWeight source)
    (himp : ∀ source, left source = true → right source = true) :
    ∀ sources : List Source,
      listQSum sourceWeight (sources.filter left) ≤
        listQSum sourceWeight (sources.filter right)
  | [] => Q'.le_refl' 0
  | first :: rest => by
      have ih := listQSum_filter_le_filter_local sourceWeight left right
        sourceWeight_nonnegative himp rest
      cases hleft : left first with
      | false =>
          cases hright : right first with
          | false =>
              simpa only [List.filter_cons, hleft, hright,
                Bool.false_eq_true, ↓reduceIte, listQSum] using ih
          | true =>
              simp only [List.filter_cons, hleft, hright,
                Bool.false_eq_true, ↓reduceIte, listQSum]
              have hmono : listQSum sourceWeight (rest.filter right) ≤
                  sourceWeight first +
                    listQSum sourceWeight (rest.filter right) := by
                have hadd := Q'.add_le_add_right
                  (0 : Q') (sourceWeight first)
                  (listQSum sourceWeight (rest.filter right))
                  (sourceWeight_nonnegative first)
                rwa [Q'.zero_add'] at hadd
              exact Q'.le_trans' _ _ _ ih hmono
      | true =>
          have hright : right first = true := himp first hleft
          simp only [List.filter_cons, hleft, hright, ↓reduceIte, listQSum]
          exact Q'.add_le_add_left (sourceWeight first) _ _ ih

/-- Forgetting structure from the target can only enlarge an inverse fiber.
In particular, attaching a proof that every repaired receiver is good does
not worsen any weighted congestion estimate already proved for the underlying
receiver map. -/
theorem finitePositiveMapFiberWeight_le_forgottenFiberWeight
    {Source Target Base : Type}
    [DecidableEq Target] [DecidableEq Base]
    (sources : List Source) (sourceWeight : Source → Q')
    (sourceWeight_nonnegative : ∀ source, (0 : Q') ≤ sourceWeight source)
    (repair : Source → Target) (forget : Target → Base)
    (baseRepair : Source → Base)
    (hforget : ∀ source, forget (repair source) = baseRepair source)
    (target : Target) :
    fiberWeight sources sourceWeight repair target ≤
      fiberWeight sources sourceWeight baseRepair (forget target) := by
  unfold fiberWeight
  apply listQSum_filter_le_filter_local
  · exact sourceWeight_nonnegative
  · intro source hsource
    have heq : target = repair source := of_decide_eq_true hsource
    exact decide_eq_true
      ((congrArg forget heq).trans (hforget source))

/-- A global source-mass estimate implies a lower bound for the exact fiber
rate.  This separates the analytic problem into a lower bound on every target
capacity and an upper bound on total source mass; the price is that it ignores
all finer congestion information in the repair. -/
theorem le_finitePositiveMapFiberRate_of_mul_totalSourceWeight_le
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (sourceWeight_pos : ∀ source, (0 : Q') < sourceWeight source)
    (targets : List Target) (targetWeight : Target → Q')
    (repair : Source → Target) (candidate : Q')
    (candidate_nonnegative : (0 : Q') ≤ candidate)
    (candidate_le_one : candidate ≤ (1 : Q'))
    (candidate_pays_total : ∀ target, target ∈ targets →
      candidate * listQSum sourceWeight sources ≤ targetWeight target) :
    candidate ≤ finitePositiveMapFiberRate
      sources sourceWeight sourceWeight_pos targets targetWeight repair := by
  apply le_finitePositiveMapFiberRate_of_mul_fiberWeight_le
    sources sourceWeight sourceWeight_pos targets targetWeight repair
    candidate candidate_le_one
  intro target htarget
  have hfiberTotal :
      fiberWeight sources sourceWeight repair target ≤
        listQSum sourceWeight sources := by
    unfold fiberWeight
    exact listQSum_filter_le_local sourceWeight
      (fun source => decide (target = repair source))
      (fun source => Q'.le_of_lt (sourceWeight_pos source)) sources
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ candidate
      hfiberTotal candidate_nonnegative)
    (candidate_pays_total target htarget)

theorem finitePositiveMapFiberRate_mul_fiberWeight_le
    {Source Target : Type} [DecidableEq Target]
    (sources : List Source) (sourceWeight : Source → Q')
    (sourceWeight_pos : ∀ source, (0 : Q') < sourceWeight source)
    (targets : List Target) (targetWeight : Target → Q')
    (targetWeight_pos : ∀ target, (0 : Q') < targetWeight target)
    (repair : Source → Target) (target : Target)
    (htarget : target ∈ targets) :
    finitePositiveMapFiberRate
          sources sourceWeight sourceWeight_pos targets targetWeight repair *
        fiberWeight sources sourceWeight repair target ≤
      targetWeight target := by
  by_cases hempty : finitePositiveMapFiberItems sources repair target = []
  · have hfiberZero : fiberWeight sources sourceWeight repair target = 0 := by
      change listQSum sourceWeight
        (finitePositiveMapFiberItems sources repair target) = 0
      rw [hempty]
      rfl
    rw [hfiberZero]
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_zero_eqv
          (finitePositiveMapFiberRate sources sourceWeight
            sourceWeight_pos targets targetWeight repair)))
      (Q'.le_of_lt (targetWeight_pos target))
  · have hrate : finitePositiveMapFiberRate
        sources sourceWeight sourceWeight_pos targets targetWeight repair ≤
      finitePositiveMapFiberRatio
        sources sourceWeight sourceWeight_pos targetWeight repair target := by
      unfold finitePositiveMapFiberRate
      exact listPositiveMinOne_le_of_mem _ targets target htarget
    have hfiberNonnegative : (0 : Q') ≤
        fiberWeight sources sourceWeight repair target := by
      unfold fiberWeight
      apply listQSum_nonnegative_on
      intro source _
      exact Q'.le_of_lt (sourceWeight_pos source)
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _
      hrate hfiberNonnegative
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (by
        unfold finitePositiveMapFiberRatio
        rw [dif_neg hempty]
        exact Q'.divPos_mul_eqv
          (targetWeight target)
          (fiberWeight sources sourceWeight repair target)
          (finitePositiveMapFiberWeight_pos_of_ne_nil
            sources sourceWeight sourceWeight_pos repair target hempty)))

#print axioms finitePositiveMapFiberRate_pos
#print axioms finitePositiveMapFiberRate_le_one
#print axioms le_finitePositiveMapFiberRate_of_mul_fiberWeight_le
#print axioms finitePositiveMapFiberWeight_le_forgottenFiberWeight
#print axioms le_finitePositiveMapFiberRate_of_mul_totalSourceWeight_le
#print axioms finitePositiveMapFiberRate_mul_fiberWeight_le

end YMGap.Continuum.FinitePositiveWeightedGoodSourceFiberRate
