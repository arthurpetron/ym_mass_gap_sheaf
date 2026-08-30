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
#print axioms finitePositiveMapFiberRate_mul_fiberWeight_le

end YMGap.Continuum.FinitePositiveWeightedGoodSourceFiberRate
