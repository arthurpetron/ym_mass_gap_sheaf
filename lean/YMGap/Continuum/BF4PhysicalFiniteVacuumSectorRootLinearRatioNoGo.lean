/-
# The global minimum-edge root-linear ratio is not cofinal

At half-extent zero, the all-spin cube ray supplies `K` distinct excited
vertices at representation cutoff `K`.  Every vertex has a strictly positive
vacuum-to-spin joint-kernel spoke.  The finite vacuum-sector edge floor lies
below each of those entries, while the sum of all selected spoke entries lies
below the vacuum row mass and hence below one.  Therefore

  edgeFloor_K * K <= 1.

The root-linear cost is at least one.  Consequently any cofinal
`FixedNomeCofinalVacuumRootLinearRatio` with positive `delta` would force

  delta * K <= 1

for every sufficiently large `K`, contradicting the explicit denominator
witness for a positive rational.

This rules out only the compiler that replaces all local edge capacities by
one global minimum edge divided by one global first-moment cost.  It does not
rule out the earlier local root-traffic capacity, the weight-cancelled
spin-ray return/escape route, a multiscale Poincare estimate, or a direct
operator proof.  No spectral gap, continuum theory, or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthNoGo
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
import YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
import YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootLinearRatioNoGo

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleCoercivityGrowthNoGo
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficLinearMoment
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4PhysicalSpinCubeRayFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeVacuumSpokes
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | first :: rest, hterm =>
      Q'.add_le_add
        (hterm first List.mem_cons_self)
        (listQSum_mono_local lower upper rest
          (fun item hitem =>
            hterm item (List.mem_cons_of_mem first hitem)))

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _first :: rest => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat rest.length * constant) _ ?_ ?_
      · exact Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant rest)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat rest.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv rest.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat rest.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat rest.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv
          (Q'.ofNat rest.length * constant) constant)

/-! ## 1. The global edge minimum must decay along the spin ray -/

private theorem zeroState_mem_centralPositiveHalfStates
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    zeroEdgeLabelling ∈
      centralPositiveHalfStates w (Q'.le_of_lt hw) K 0 := by
  obtain ⟨tail, hstates⟩ :=
    centralPositiveHalfStates_starts_vacuum
      w (Q'.le_of_lt hw) K 0
  rw [hstates]
  exact List.mem_cons_self

/-- At cutoff `K`, the finite edge floor times the `K` distinct excited
vacuum spokes is bounded by the total vacuum row mass. -/
theorem centralPhysicalFiniteVacuumSectorEdgeFloor_mul_cutoff_le_vacuumWeight
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          w (Q'.le_of_lt hw) K 0 * Q'.ofNat K ≤
      centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 0 := by
  let ray := centralLowerExcitedSpinCubeIndices
    w (Q'.le_of_lt hw) K
  let sector := centralPhysicalFiniteVacuumSectorIndices
    w (Q'.le_of_lt hw) K 0
  let floor := centralPhysicalFiniteVacuumSectorEdgeFloor
    w (Q'.le_of_lt hw) K 0
  let row := centralPhysicalFiniteKernel
    w (Q'.le_of_lt hw) K 0 0
  have hfloorSum :
      listQSum (fun _index => floor) ray ≤
        listQSum row ray := by
    apply listQSum_mono_local
    intro index hindex
    obtain ⟨offset, hoffsetRange, rfl⟩ := List.mem_map.mp hindex
    have hoffset : offset < K := List.mem_range.mp hoffsetRange
    have hspin : offset + 1 ≤ K := by omega
    have htarget :=
      centralLowerSpinCubeIndex_mem_vacuumSector hw hspin
    have hpositive :=
      centralPhysicalFiniteKernel_zero_spinCubeIndex_pos hw hspin
    exact centralPhysicalFiniteVacuumSectorEdgeFloor_le_positive_entry
      w (Q'.le_of_lt hw) K 0 0
      (centralLowerSpinCubeIndex
        w (Q'.le_of_lt hw) K (offset + 1))
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
      htarget hpositive
  have hraySector : listQSum row ray ≤ listQSum row sector := by
    apply listQSum_le_of_injective
      ray sector row row (fun index => index)
    · exact centralLowerExcitedSpinCubeIndices_nodup hw K
    · exact centralLowerExcitedSpinCubeIndices_subset_vacuumSector hw K
    · intro left _hleft right _hright heq
      exact heq
    · intro index _hindex
      exact Q'.le_refl' _
    · intro index _hindex
      unfold row centralPhysicalFiniteKernel
      exact centralNormalizedPhysicalReflectedKernel_nonnegative
        (Q'.le_of_lt hw) K 0 _ _
  have hrowWeight : listQSum row sector ≈
      centralPhysicalFiniteWeight w (Q'.le_of_lt hw) K 0 0 :=
    centralPhysicalFiniteVacuumSectorKernel_rowSum_eqv_weight
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w (Q'.le_of_lt hw) K 0)
  have hconstant :
      floor * Q'.ofNat K ≈ listQSum (fun _index => floor) ray := by
    refine Q'.eqv_trans _ (Q'.ofNat K * floor) _
      (Q'.mul_comm_eqv floor (Q'.ofNat K)) ?_
    exact Q'.eqv_symm (by
      simpa only [ray, centralLowerExcitedSpinCubeIndices,
        List.length_map, List.length_range] using
        (listQSum_const_local floor ray))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hconstant)
    (Q'.le_trans' _ _ _ hfloorSum
      (Q'.le_trans' _ _ _ hraySector
        (Q'.le_of_eqv hrowWeight)))

/-- The selected vacuum row is a probability row, so the spoke budget is at
most one. -/
theorem centralPhysicalFiniteVacuumSectorEdgeFloor_mul_cutoff_le_one
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          w (Q'.le_of_lt hw) K 0 * Q'.ofNat K ≤ 1 := by
  exact Q'.le_trans' _ _ _
    (centralPhysicalFiniteVacuumSectorEdgeFloor_mul_cutoff_le_vacuumWeight
      hw K)
    (by
      unfold centralPhysicalFiniteWeight
      rw [centralPhysicalFiniteStateAt_zero_eq_vacuum]
      exact centralPhysicalRowMarginal_le_one_on_carrier
        (zeroState_mem_centralPositiveHalfStates hw K))

/-! ## 2. A cofinal positive global-minimum ratio is impossible -/

namespace FixedNomeCofinalVacuumRootLinearRatio

/-- The defining ratio estimate forces `delta` below the finite global edge
minimum at every later cutoff. -/
theorem delta_le_edgeFloor
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalVacuumRootLinearRatio hw 0)
    {K : Nat} (hK : family.start ≤ K) :
    family.delta ≤ centralPhysicalFiniteVacuumSectorEdgeFloor
      w (Q'.le_of_lt hw) K 0 := by
  let cost := centralPhysicalFiniteVacuumSectorRootLinearCost
    w (Q'.le_of_lt hw) K 0
  have hcostOne : (1 : Q') ≤ cost := by
    unfold cost centralPhysicalFiniteVacuumSectorRootLinearCost
    exact Q'.add_le_self_of_nonneg 1 _
      (centralPhysicalFiniteVacuumSectorRootLinearMoment_nonnegative
        w (Q'.le_of_lt hw) K 0)
  have hscaled : family.delta * 1 ≤ family.delta * cost :=
    Q'.mul_le_mul_of_nonneg_left 1 cost family.delta hcostOne
      (Q'.le_of_lt family.delta_pos)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv family.delta)))
    (Q'.le_trans' _ _ _ hscaled (family.ratio_bound K hK))

/-- Every later cutoff would satisfy the impossible linear budget
`delta * K <= 1`. -/
theorem delta_mul_cutoff_le_one
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalVacuumRootLinearRatio hw 0)
    {K : Nat} (hK : family.start ≤ K) :
    family.delta * Q'.ofNat K ≤ 1 := by
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    family.delta
    (centralPhysicalFiniteVacuumSectorEdgeFloor
      w (Q'.le_of_lt hw) K 0)
    (Q'.ofNat K)
    (delta_le_edgeFloor family hK)
    (Q'.ofNat_le_ofNat (Nat.zero_le K))
  exact Q'.le_trans' _ _ _ hscaled
    (centralPhysicalFiniteVacuumSectorEdgeFloor_mul_cutoff_le_one hw K)

/-- A cofinal root-linear ratio at half-extent zero contradicts its own
positive rational denominator at an explicit later cutoff. -/
theorem impossible
    {w : Q'} {hw : (0 : Q') < w}
    (family : FixedNomeCofinalVacuumRootLinearRatio hw 0) : False := by
  let request := (family.delta.den + 1) * (family.delta.den + 1)
  let K := max family.start request
  have hstart : family.start ≤ K := Nat.le_max_left _ _
  have hrequest : request ≤ K := Nat.le_max_right _ _
  have hrequestQ : Q'.ofNat request ≤ Q'.ofNat K :=
    Q'.ofNat_le_ofNat hrequest
  have hscaled :
      family.delta * Q'.ofNat request ≤
        family.delta * Q'.ofNat K :=
    Q'.mul_le_mul_of_nonneg_left _ _ family.delta hrequestQ
      (Q'.le_of_lt family.delta_pos)
  have hle : family.delta * Q'.ofNat request ≤ 1 :=
    Q'.le_trans' _ _ _ hscaled
      (delta_mul_cutoff_le_one family hstart)
  have hlt : (1 : Q') < family.delta * Q'.ofNat request := by
    exact one_lt_mul_den_succ_square family.delta family.delta_pos
  exact (Int.not_lt_of_ge hle) hlt

end FixedNomeCofinalVacuumRootLinearRatio

/-- The global-minimum cofinal ratio interface is empty at half-extent zero
for every positive nome. -/
theorem no_fixedNomeCofinalVacuumRootLinearRatio
    {w : Q'} (hw : (0 : Q') < w) :
    Not (Nonempty (FixedNomeCofinalVacuumRootLinearRatio hw 0)) := by
  intro hfamily
  rcases hfamily with ⟨family⟩
  exact FixedNomeCofinalVacuumRootLinearRatio.impossible family

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootLinearRatioNoGo

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootLinearRatioNoGo.centralPhysicalFiniteVacuumSectorEdgeFloor_mul_cutoff_le_vacuumWeight
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootLinearRatioNoGo.centralPhysicalFiniteVacuumSectorEdgeFloor_mul_cutoff_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootLinearRatioNoGo.FixedNomeCofinalVacuumRootLinearRatio.delta_le_edgeFloor
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootLinearRatioNoGo.FixedNomeCofinalVacuumRootLinearRatio.delta_mul_cutoff_le_one
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootLinearRatioNoGo.FixedNomeCofinalVacuumRootLinearRatio.impossible
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootLinearRatioNoGo.no_fixedNomeCofinalVacuumRootLinearRatio
