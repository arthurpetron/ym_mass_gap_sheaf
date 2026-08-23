/-
# Exact BF4 full-time-factorization restriction to the vacuum sector

A non-strict one-step density on the complete finite carrier may preserve the
canonical vacuum component even though no strictly contracting full-carrier
slice can exist at cutoff two.  On such a closed component, multiply the
one-step density by the component mass and divide the stationary weight by
that mass.  The factors cancel at every convolution.

This file packages the exact consequence in the syntax naturally supplied by
`finiteWeightedDensityPower`: a depth-`d` physical factorization is a power
with index `d - 1`, hence exactly `d` one-step factors.  It then proves the
sector centered-row estimate `qS^d` directly.  This separates the non-strict
full factorization from the genuinely sector-native strict contraction
obligation and avoids the already-refuted strict full-carrier route.

No factorization or strict rate is constructed here.  No thermodynamic or
continuum limit is constructed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower
import YMGap.Continuum.BF4PhysicalVacuumSectorLocalPowerBudgetGap

namespace YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorConditionedDensityPower
open YMGap.Continuum.BF4PhysicalVacuumSectorDensityMassDefect
open YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.CasimirMoment
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A total extension of a component-conditioned kernel -/

/-- On component endpoints this is `mass * fullKernel`.  Off the component it
is the stationary density one.  The extension makes the row and column laws
total, while none of its off-component values enter a sector power. -/
def finiteComponentConditionedKernelExtension
    {State : Type} [DecidableEq State]
    (sector : List State) (mass : Q')
    (fullKernel : State → State → Q')
    (source target : State) : Q' :=
  if source ∈ sector then
    if target ∈ sector then mass * fullKernel source target else 1
  else 1

/-- The extension has the required mass scaling on component endpoints. -/
theorem finiteComponentConditionedKernelExtension_eqv_of_mem
    {State : Type} [DecidableEq State]
    {sector : List State} {mass : Q'}
    {fullKernel : State → State → Q'}
    {source target : State}
    (hsource : source ∈ sector) (htarget : target ∈ sector) :
    finiteComponentConditionedKernelExtension
        sector mass fullKernel source target ≈
      mass * fullKernel source target := by
  unfold finiteComponentConditionedKernelExtension
  rw [if_pos hsource, if_pos htarget]
  exact Q'.eqv_refl _

/-- Restricting an outgoing-closed normalized full row and conditioning it by
the component mass gives a total normalized row on the conditioned carrier. -/
theorem finiteComponentConditionedKernelExtension_row_normalized
    {State : Type} [DecidableEq State]
    (full sector : List State)
    (mass : Q') (mass_pos : (0 : Q') < mass)
    (weight : State → Q') (fullKernel : State → State → Q')
    (hfullNodup : full.Nodup) (hsectorNodup : sector.Nodup)
    (hsubset : ∀ state, state ∈ sector → state ∈ full)
    (conditionedWeightTotal :
      listQSum
          (finiteCarrierMassNormalizedWeight mass mass_pos weight)
          sector ≈ 1)
    (hclosed : ∀ source target,
      source ∈ sector → target ∈ full → target ∉ sector →
        fullKernel source target ≈ 0)
    (fullRow : ∀ source,
      listQSum
          (fun target => weight target * fullKernel source target)
          full ≈ 1)
    (source : State) :
    listQSum
        (fun target =>
          finiteCarrierMassNormalizedWeight mass mass_pos weight target *
            finiteComponentConditionedKernelExtension
              sector mass fullKernel source target)
        sector ≈ 1 := by
  by_cases hsource : source ∈ sector
  · let normalizedWeight :=
      finiteCarrierMassNormalizedWeight mass mass_pos weight
    let value : State → Q' := fun target =>
      weight target * fullKernel source target
    have hterm : ∀ target, target ∈ sector →
        normalizedWeight target *
            finiteComponentConditionedKernelExtension
              sector mass fullKernel source target ≈
          value target := by
      intro target htarget
      refine Q'.eqv_trans _
        (normalizedWeight target *
          (mass * fullKernel source target)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (finiteComponentConditionedKernelExtension_eqv_of_mem
            hsource htarget)
      refine Q'.eqv_trans _
        ((normalizedWeight target * mass) *
          fullKernel source target) _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (normalizedWeight target) mass
            (fullKernel source target))) ?_
      exact Q'.mul_eqv_congr_right _ _ _
        (finiteCarrierMassNormalizedWeight_mul_mass_eqv_weight
          mass mass_pos weight target)
    have hzero : ∀ target, target ∈ full → target ∉ sector →
        value target ≈ 0 := by
      intro target htarget houtside
      unfold value
      refine Q'.eqv_trans _ (weight target * 0) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (hclosed source target hsource htarget houtside)
      · exact Q'.mul_zero_eqv _
    refine Q'.eqv_trans _ (listQSum value sector) _ ?_ ?_
    · apply listQSum_congr_on
      exact hterm
    exact Q'.eqv_trans _ (listQSum value full) _
      (listQSum_sector_eq_full_of_zero full sector value
        hfullNodup hsectorNodup hsubset hzero)
      (fullRow source)
  · refine Q'.eqv_trans _
      (listQSum
        (finiteCarrierMassNormalizedWeight mass mass_pos weight)
        sector) _ ?_ conditionedWeightTotal
    apply listQSum_congr_on
    intro target _
    unfold finiteComponentConditionedKernelExtension
    rw [if_neg hsource]
    exact Q'.mul_one_eqv _

/-- The incoming-closed column analogue of the conditioned row theorem. -/
theorem finiteComponentConditionedKernelExtension_column_normalized
    {State : Type} [DecidableEq State]
    (full sector : List State)
    (mass : Q') (mass_pos : (0 : Q') < mass)
    (weight : State → Q') (fullKernel : State → State → Q')
    (hfullNodup : full.Nodup) (hsectorNodup : sector.Nodup)
    (hsubset : ∀ state, state ∈ sector → state ∈ full)
    (conditionedWeightTotal :
      listQSum
          (finiteCarrierMassNormalizedWeight mass mass_pos weight)
          sector ≈ 1)
    (hclosed : ∀ source target,
      source ∈ full → source ∉ sector → target ∈ sector →
        fullKernel source target ≈ 0)
    (fullColumn : ∀ target,
      listQSum
          (fun source => weight source * fullKernel source target)
          full ≈ 1)
    (target : State) :
    listQSum
        (fun source =>
          finiteCarrierMassNormalizedWeight mass mass_pos weight source *
            finiteComponentConditionedKernelExtension
              sector mass fullKernel source target)
        sector ≈ 1 := by
  by_cases htarget : target ∈ sector
  · let normalizedWeight :=
      finiteCarrierMassNormalizedWeight mass mass_pos weight
    let value : State → Q' := fun source =>
      weight source * fullKernel source target
    have hterm : ∀ source, source ∈ sector →
        normalizedWeight source *
            finiteComponentConditionedKernelExtension
              sector mass fullKernel source target ≈
          value source := by
      intro source hsource
      refine Q'.eqv_trans _
        (normalizedWeight source *
          (mass * fullKernel source target)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (finiteComponentConditionedKernelExtension_eqv_of_mem
            hsource htarget)
      refine Q'.eqv_trans _
        ((normalizedWeight source * mass) *
          fullKernel source target) _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (normalizedWeight source) mass
            (fullKernel source target))) ?_
      exact Q'.mul_eqv_congr_right _ _ _
        (finiteCarrierMassNormalizedWeight_mul_mass_eqv_weight
          mass mass_pos weight source)
    have hzero : ∀ source, source ∈ full → source ∉ sector →
        value source ≈ 0 := by
      intro source hsource houtside
      unfold value
      refine Q'.eqv_trans _ (weight source * 0) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (hclosed source target hsource houtside htarget)
      · exact Q'.mul_zero_eqv _
    refine Q'.eqv_trans _ (listQSum value sector) _ ?_ ?_
    · apply listQSum_congr_on
      exact hterm
    exact Q'.eqv_trans _ (listQSum value full) _
      (listQSum_sector_eq_full_of_zero full sector value
        hfullNodup hsectorNodup hsubset hzero)
      (fullColumn target)
  · refine Q'.eqv_trans _
      (listQSum
        (finiteCarrierMassNormalizedWeight mass mass_pos weight)
        sector) _ ?_ conditionedWeightTotal
    apply listQSum_congr_on
    intro source hsource
    unfold finiteComponentConditionedKernelExtension
    rw [if_pos hsource, if_neg htarget]
    exact Q'.mul_one_eqv _

/-! ## 2. Direct sector density-power gluing -/

/-- A depth-`depth` factorization of the conditioned physical density by one
sector-local density, together with its strict centered one-step rate. -/
structure PhysicalBF4VacuumSectorDensityPowerGluing
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half depth : Nat)
    (oneStep : Nat → Nat → Q') (qS : Q') : Type 1 where
  depth_at_least_three : 3 ≤ depth
  qS_nonnegative : (0 : Q') ≤ qS
  oneStep_row : ∀ row,
    listQSum
        (fun state =>
          centralPhysicalFiniteVacuumSectorMassNormalizedWeight
              w hw cutoff half state *
            oneStep row state)
        (centralPhysicalFiniteVacuumSectorIndices
          w hw cutoff half) ≈ 1
  oneStep_column : ∀ column,
    listQSum
        (fun state =>
          centralPhysicalFiniteVacuumSectorMassNormalizedWeight
              w hw cutoff half state *
            oneStep state column)
        (centralPhysicalFiniteVacuumSectorIndices
          w hw cutoff half) ≈ 1
  density_power : ∀ source target,
    source ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
    target ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      centralPhysicalFiniteVacuumSectorMassNormalizedDensity
          w hw cutoff half source target ≈
        finiteWeightedDensityPower
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
            w hw cutoff half)
          oneStep (depth - 1) source target
  one_step_centered_bound : ∀ source,
    source ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      finiteWeightedCenteredRowMass
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
            w hw cutoff half)
          oneStep source ≤ qS

namespace PhysicalBF4VacuumSectorDensityPowerGluing

/-- The exact depth-`depth` factorization contracts a centered row by the
complete power `qS^depth`. -/
theorem conditionedDensityCenteredRow_le_pow
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half depth : Nat}
    {oneStep : Nat → Nat → Q'} {qS : Q'}
    (data : PhysicalBF4VacuumSectorDensityPowerGluing
      w hw cutoff half depth oneStep qS)
    (source : Nat)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    finiteWeightedCenteredRowMass
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedDensity
          w hw cutoff half)
        source ≤ qS ^ depth := by
  let states :=
    centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  let weight :=
    centralPhysicalFiniteVacuumSectorMassNormalizedWeight
      w hw cutoff half
  let power :=
    finiteWeightedDensityPower states weight oneStep (depth - 1)
  have hgluing :
      finiteWeightedCenteredRowMass states weight
          (centralPhysicalFiniteVacuumSectorMassNormalizedDensity
            w hw cutoff half) source ≈
        finiteWeightedCenteredRowMass states weight power source := by
    unfold finiteWeightedCenteredRowMass finiteL1Norm
      finiteWeightedCenteredTransition finiteCenteredDensity
      states weight power
    apply listQSum_congr_on
    intro target htarget
    apply Q'.abs_eqv_congr
    apply Q'.mul_eqv_congr_left
    apply Q'.add_eqv_congr_right
    exact data.density_power source target hsource htarget
  have hpower := finiteWeightedDensityPower_centered_row_le_pow
    states weight oneStep
    (centralPhysicalFiniteVacuumSectorMassNormalizedWeight_total_one
      w hw cutoff half)
    data.oneStep_row data.oneStep_column qS data.qS_nonnegative
    data.one_step_centered_bound (depth - 1) source hsource
  have hexponent : depth - 1 + 1 = depth := by
    have hdepth := data.depth_at_least_three
    omega
  rw [hexponent] at hpower
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hgluing) hpower

end PhysicalBF4VacuumSectorDensityPowerGluing

/-! ## 3. Full-factorization restriction adapter -/

/-- A non-strict full-carrier time factorization compatible with the
canonical vacuum component.  Strictness is intentionally absent: cutoff-two
reducibility forbids a strict full-carrier certificate. -/
structure PhysicalBF4FiniteVacuumCompatibleTimeFactorization
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half depth : Nat)
    (fullOneStep : Nat → Nat → Q') : Type 1 where
  depth_at_least_three : 3 ≤ depth
  full_oneStep_row : ∀ row,
    listQSum
        (fun state =>
          centralPhysicalFiniteWeight w hw cutoff half state *
            fullOneStep row state)
        (centralPhysicalFiniteIndexCarrier w hw cutoff half) ≈ 1
  full_oneStep_column : ∀ column,
    listQSum
        (fun state =>
          centralPhysicalFiniteWeight w hw cutoff half state *
            fullOneStep state column)
        (centralPhysicalFiniteIndexCarrier w hw cutoff half) ≈ 1
  outgoing_closed : ∀ source target,
    source ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
    target ∈ centralPhysicalFiniteIndexCarrier w hw cutoff half →
    target ∉ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      fullOneStep source target ≈ 0
  incoming_closed : ∀ source target,
    source ∈ centralPhysicalFiniteIndexCarrier w hw cutoff half →
    source ∉ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
    target ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      fullOneStep source target ≈ 0
  full_density_power : ∀ source target,
    source ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
    target ∈ centralPhysicalFiniteVacuumSectorIndices w hw cutoff half →
      centralPhysicalFiniteFullDensity w hw cutoff half source target ≈
        finiteWeightedDensityPower
          (centralPhysicalFiniteIndexCarrier w hw cutoff half)
          (centralPhysicalFiniteWeight w hw cutoff half)
          fullOneStep (depth - 1) source target

/-- The total component-conditioned one-step density associated to a
vacuum-compatible full factorization. -/
def centralPhysicalFiniteVacuumSectorConditionedTimeStep
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (fullOneStep : Nat → Nat → Q') : Nat → Nat → Q' :=
  finiteComponentConditionedKernelExtension
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
    fullOneStep

private theorem range_nodup_local (bound : Nat) :
    (List.range bound).Nodup := by
  induction bound with
  | zero => exact List.nodup_nil
  | succ bound ih =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨ih, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq : right = bound := List.mem_singleton.mp hright
      rw [heq, hrightEq] at hleft
      exact absurd (List.mem_range.mp hleft) (Nat.lt_irrefl bound)

namespace PhysicalBF4FiniteVacuumCompatibleTimeFactorization

private theorem sector_subset_full
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half state : Nat}
    (hstate : state ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    state ∈ centralPhysicalFiniteIndexCarrier w hw cutoff half :=
  rootComponent_subset
    (centralPhysicalFiniteSupportAdjacentB w hw cutoff half)
    (zero_mem_centralPhysicalFiniteIndexCarrier w hw cutoff half) hstate

/-- The conditioned extension of a compatible full step has exact stationary
row normalization on the sector. -/
theorem conditionedOneStep_row
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half depth : Nat}
    {fullOneStep : Nat → Nat → Q'}
    (data : PhysicalBF4FiniteVacuumCompatibleTimeFactorization
      w hw cutoff half depth fullOneStep)
    (row : Nat) :
    listQSum
        (fun state =>
          centralPhysicalFiniteVacuumSectorMassNormalizedWeight
              w hw cutoff half state *
            centralPhysicalFiniteVacuumSectorConditionedTimeStep
              w hw cutoff half fullOneStep row state)
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) ≈ 1 := by
  apply finiteComponentConditionedKernelExtension_row_normalized
    (centralPhysicalFiniteIndexCarrier w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
    (centralPhysicalFiniteWeight w hw cutoff half)
    fullOneStep
  · exact range_nodup_local _
  · exact centralPhysicalFiniteVacuumSectorIndices_nodup
      w hw cutoff half
  · intro state hstate
    exact sector_subset_full hstate
  · exact centralPhysicalFiniteVacuumSectorMassNormalizedWeight_total_one
      w hw cutoff half
  · exact data.outgoing_closed
  · exact data.full_oneStep_row

/-- The conditioned extension of a compatible full step has exact stationary
column normalization on the sector. -/
theorem conditionedOneStep_column
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half depth : Nat}
    {fullOneStep : Nat → Nat → Q'}
    (data : PhysicalBF4FiniteVacuumCompatibleTimeFactorization
      w hw cutoff half depth fullOneStep)
    (column : Nat) :
    listQSum
        (fun state =>
          centralPhysicalFiniteVacuumSectorMassNormalizedWeight
              w hw cutoff half state *
            centralPhysicalFiniteVacuumSectorConditionedTimeStep
              w hw cutoff half fullOneStep state column)
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) ≈ 1 := by
  apply finiteComponentConditionedKernelExtension_column_normalized
    (centralPhysicalFiniteIndexCarrier w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
    (centralPhysicalFiniteWeight w hw cutoff half)
    fullOneStep
  · exact range_nodup_local _
  · exact centralPhysicalFiniteVacuumSectorIndices_nodup
      w hw cutoff half
  · intro state hstate
    exact sector_subset_full hstate
  · exact centralPhysicalFiniteVacuumSectorMassNormalizedWeight_total_one
      w hw cutoff half
  · exact data.incoming_closed
  · exact data.full_oneStep_column

/-- **Exact adapter.**  A compatible full density-power factorization
restricts to the conditioned vacuum component at the same depth. -/
theorem conditionedDensity_eqv_conditionedOneStepPower
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half depth : Nat}
    {fullOneStep : Nat → Nat → Q'}
    (data : PhysicalBF4FiniteVacuumCompatibleTimeFactorization
      w hw cutoff half depth fullOneStep)
    (source target : Nat)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorMassNormalizedDensity
        w hw cutoff half source target ≈
      finiteWeightedDensityPower
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
          w hw cutoff half)
        (centralPhysicalFiniteVacuumSectorConditionedTimeStep
          w hw cutoff half fullOneStep)
        (depth - 1) source target := by
  have hphysical :=
    centralPhysicalFiniteVacuumSectorMassNormalizedDensity_eqv_mass_mul_fullDensity
      hsource htarget
  have hfull := data.full_density_power source target hsource htarget
  have hconditioned :=
    finiteWeightedConditionedDensityPower_eqv_mass_mul_fullPower
      (centralPhysicalFiniteIndexCarrier w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
      (centralPhysicalFiniteVacuumSectorWeightSum_pos w hw cutoff half)
      (centralPhysicalFiniteWeight w hw cutoff half)
      fullOneStep
      (centralPhysicalFiniteVacuumSectorConditionedTimeStep
        w hw cutoff half fullOneStep)
      (range_nodup_local _)
      (centralPhysicalFiniteVacuumSectorIndices_nodup w hw cutoff half)
      (fun state hstate => sector_subset_full hstate)
      data.outgoing_closed
      (fun first last hfirst hlast =>
        finiteComponentConditionedKernelExtension_eqv_of_mem
          hfirst hlast)
      (depth - 1) source target hsource htarget
  exact Q'.eqv_trans _ _ _ hphysical
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hfull)
      (Q'.eqv_symm hconditioned))

/-- Adding only a sector-local centered one-step bound turns the exact full
factorization into the direct sector density-power gluing interface. -/
def toVacuumSectorDensityPowerGluing
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half depth : Nat}
    {fullOneStep : Nat → Nat → Q'} {qS : Q'}
    (data : PhysicalBF4FiniteVacuumCompatibleTimeFactorization
      w hw cutoff half depth fullOneStep)
    (qS_nonnegative : (0 : Q') ≤ qS)
    (sector_centered_bound : ∀ source,
      source ∈ centralPhysicalFiniteVacuumSectorIndices
          w hw cutoff half →
        finiteWeightedCenteredRowMass
            (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
            (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
              w hw cutoff half)
            (centralPhysicalFiniteVacuumSectorConditionedTimeStep
              w hw cutoff half fullOneStep)
            source ≤ qS) :
    PhysicalBF4VacuumSectorDensityPowerGluing
      w hw cutoff half depth
      (centralPhysicalFiniteVacuumSectorConditionedTimeStep
        w hw cutoff half fullOneStep) qS where
  depth_at_least_three := data.depth_at_least_three
  qS_nonnegative := qS_nonnegative
  oneStep_row := data.conditionedOneStep_row
  oneStep_column := data.conditionedOneStep_column
  density_power := data.conditionedDensity_eqv_conditionedOneStepPower
  one_step_centered_bound := sector_centered_bound

end PhysicalBF4FiniteVacuumCompatibleTimeFactorization

end YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter.finiteComponentConditionedKernelExtension_row_normalized
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter.finiteComponentConditionedKernelExtension_column_normalized
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter.PhysicalBF4VacuumSectorDensityPowerGluing.conditionedDensityCenteredRow_le_pow
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter.PhysicalBF4FiniteVacuumCompatibleTimeFactorization.conditionedDensity_eqv_conditionedOneStepPower
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter.PhysicalBF4FiniteVacuumCompatibleTimeFactorization.toVacuumSectorDensityPowerGluing
