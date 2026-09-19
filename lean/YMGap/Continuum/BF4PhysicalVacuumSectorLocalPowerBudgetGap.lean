/-
# Depth-amplified sector-local contraction for the BF4 vacuum component

The sector-local gluing compiler initially used the convenient sufficient
condition `qS <= 1/4`.  That cap is stronger than the actual tensorization
needs.  The exact coefficient is

    (qS * qS) * qS^(depth - 2) = qS^depth.

This file therefore permits a cutoff-dependent local rate, including one
which approaches one, provided the displayed depth-amplified coefficient is
bounded by one fixed `rate < 1` along a constructively cofinal family.  Such a
power budget compiles directly to the corrected mass-normalized row
certificate and the completed same-object vacuum-sector gap.

No local slice or power budget is constructed here.  The exact density-power
gluing and the uniform power budget remain analytic producer obligations.  No
thermodynamic or continuum limit is constructed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing

namespace YMGap.Continuum.BF4PhysicalVacuumSectorLocalPowerBudgetGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredLimitGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorLocalContractionGluing
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedRowGap
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiveHolonomyPerronCutoff
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The tensorized coefficient is one exact power -/

/-- The two endpoint factors and the middle factor comprise exactly
`depth` copies of the local rate. -/
theorem localPowerCoefficient_eqv_pow
    (qS : Q') (depth : Nat) (hdepth : 2 ≤ depth) :
    (qS * qS) * (qS ^ (depth - 2)) ≈ qS ^ depth := by
  have htwo : qS * qS ≈ qS ^ (2 : Nat) := by
    rw [Q'.pow_succ, Q'.pow_succ, Q'.pow_zero]
    exact Q'.mul_eqv_congr_left qS qS (qS * 1)
      (Q'.eqv_symm (Q'.mul_one_eqv qS))
  have hexponent : 2 + (depth - 2) = depth := by omega
  have hsplit := Q'.pow_add_eqv qS 2 (depth - 2)
  rw [hexponent] at hsplit
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ htwo)
    (Q'.eqv_symm hsplit)

namespace PhysicalBF4VacuumSectorLocalSliceGluing

/-- Exact local gluing gives the full depth-amplified conditioned-density row
bound, without imposing a cutoff-independent cap on the one-step rate. -/
theorem conditionedDensityCenteredRow_le_localPower
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half depth : Nat}
    {oneStep : Nat → Nat → Q'} {qS : Q'}
    (slice : PhysicalBF4VacuumSectorLocalSliceGluing
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
        source ≤
      qS ^ depth := by
  have hcoefficient :=
    (slice.toRow source hsource).density_centered_row_le_local_power
  exact Q'.le_trans' _ _ _ hcoefficient
    (Q'.le_of_eqv
      (localPowerCoefficient_eqv_pow qS depth
        (Nat.le_trans (by decide : 2 ≤ 3)
          slice.depth_at_least_three)))

end PhysicalBF4VacuumSectorLocalSliceGluing

/-! ## 2. Cofinal local-power budget -/

/-- A constructively cofinal family of sector-local slices whose complete
depth-amplified coefficient is bounded by one fixed strict rate. -/
structure FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) (rate : Q') : Type 1 where
  rate_nonnegative : (0 : Q') ≤ rate
  rate_lt_one : rate < (1 : Q')
  anchor : Nat → Nat → Nat
  anchor_ge : ∀ base threshold,
    max base threshold ≤ anchor base threshold
  depth : Nat → Nat → Nat
  localRate : Nat → Nat → Q'
  oneStep : Nat → Nat → Nat → Nat → Q'
  localSlice : ∀ base threshold,
    PhysicalBF4VacuumSectorLocalSliceGluing
      w hw (anchor base threshold) half
      (depth base threshold) (oneStep base threshold)
      (localRate base threshold)
  powerBudget : ∀ base threshold,
    localRate base threshold ^ depth base threshold ≤ rate

namespace FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing

/-! ## 3. Forward/backward join from the quarter-slice route -/

/-- The older quarter-rate sector-slice interface is already strong enough to
produce the newer depth-amplified budget at the fixed physical rate
`1/16`.  The proof uses only the displayed local nonnegativity, the quarter
cap, and the explicit depth lower bound; no density-power identity is added
by this adapter.  Thus it joins the two producer interfaces without
silently turning a local slice into a full factorization. -/
def ofLocalSlice
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (family : FixedNomeCofinalVacuumSectorLocalSliceGluing
      w hw half) :
    FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing
      w hw half (Q'.mkPos 1 16 (by decide)) where
  rate_nonnegative := by decide
  rate_lt_one := by decide
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  depth := family.depth
  localRate := family.localRate
  oneStep := family.oneStep
  localSlice := family.localSlice
  powerBudget := by
    intro base threshold
    let slice := family.localSlice base threshold
    have hq0 : (0 : Q') ≤ family.localRate base threshold :=
      slice.qS_nonnegative
    have hqQuarter : family.localRate base threshold ≤ quarter :=
      family.localRate_le_quarter base threshold
    have hqOne : family.localRate base threshold ≤ (1 : Q') :=
      Q'.le_trans' _ _ _ hqQuarter (by decide)
    have hdepth : 3 ≤ family.depth base threshold :=
      slice.depth_at_least_three
    have hpowDepth :
        family.localRate base threshold ^ family.depth base threshold ≤
          family.localRate base threshold ^ 3 :=
      YMGap.Continuum.HKConvGen.pow_base_antitone hq0 hqOne hdepth
    have hpowQuarter :
        family.localRate base threshold ^ 3 ≤ quarter ^ 3 :=
      pow_base_mono (family.localRate base threshold) quarter hq0
        hqQuarter 3
    have hquarterPow :
        quarter ^ 3 ≤ Q'.mkPos 1 16 (by decide) := by
      decide
    exact Q'.le_trans' _ _ _ hpowDepth
      (Q'.le_trans' _ _ _ hpowQuarter hquarterPow)

/-- Compile the exact depth-amplified local budget to the corrected
mass-normalized row-distance interface. -/
def toMassNormalizedRowDistance
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing
      w hw half rate) :
    FixedNomeCofinalVacuumSectorMassNormalizedRowDistance
      w hw half rate where
  rate_nonnegative := family.rate_nonnegative
  rate_lt_one := family.rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  rowDistance := by
    intro base threshold source hsource
    let cutoff := family.anchor base threshold
    have hsourcePos : (0 : Q') <
        centralPhysicalFiniteWeight w hw cutoff half source :=
      centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
    have hdensityPower :=
      YMGap.Continuum.BF4PhysicalVacuumSectorLocalPowerBudgetGap.PhysicalBF4VacuumSectorLocalSliceGluing.conditionedDensityCenteredRow_le_localPower
        (family.localSlice base threshold) source hsource
    have hdensity :
        finiteWeightedCenteredRowMass
            (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
            (centralPhysicalFiniteVacuumSectorMassNormalizedWeight
              w hw cutoff half)
            (centralPhysicalFiniteVacuumSectorMassNormalizedDensity
              w hw cutoff half)
            source ≤ rate :=
      Q'.le_trans' _ _ _ hdensityPower (family.powerBudget base threshold)
    have hidentity :=
      finiteCarrierMassNormalizedRowDistance_eqv_densityCenteredRowMass
        (states := centralPhysicalFiniteVacuumSectorIndices
          w hw cutoff half)
        (mass := centralPhysicalFiniteVacuumSectorMass w hw cutoff half)
        (mass_pos := centralPhysicalFiniteVacuumSectorWeightSum_pos
          w hw cutoff half)
        (weight := centralPhysicalFiniteWeight w hw cutoff half)
        (joint := centralPhysicalFiniteKernel w hw cutoff half)
        hsourcePos
        (fun target htarget =>
          centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex htarget)
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hdensity
      (Q'.le_of_lt hsourcePos)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hidentity) ?_
    refine Q'.le_trans' _ _ _ hscaled ?_
    exact Q'.le_of_eqv
      (Q'.mul_comm_eqv
        (centralPhysicalFiniteWeight w hw cutoff half source) rate)

/-- The same depth-amplified local budget reaches the completed same-object
vacuum-sector strict gap at its supplied uniform rate. -/
def toVacuumSectorCenteredStrictGap
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat} {rate : Q'}
    (family : FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing
      w hw half rate) :
    FixedNomeCofinalVacuumSectorCenteredStrictGap w hw half rate :=
  family.toMassNormalizedRowDistance.toVacuumSectorCenteredStrictGap

end FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing

end YMGap.Continuum.BF4PhysicalVacuumSectorLocalPowerBudgetGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorLocalPowerBudgetGap.localPowerCoefficient_eqv_pow
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorLocalPowerBudgetGap.PhysicalBF4VacuumSectorLocalSliceGluing.conditionedDensityCenteredRow_le_localPower
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorLocalPowerBudgetGap.FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing.ofLocalSlice
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorLocalPowerBudgetGap.FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing.toMassNormalizedRowDistance
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorLocalPowerBudgetGap.FixedNomeCofinalVacuumSectorLocalPowerBudgetGluing.toVacuumSectorCenteredStrictGap
