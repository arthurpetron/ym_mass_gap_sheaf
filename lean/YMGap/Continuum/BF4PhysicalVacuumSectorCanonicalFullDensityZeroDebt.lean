/-
# Exact zero-cutoff canonical power debt

At cutoff `K = 0`, every bounded edge labelling is the all-zero labelling.
The positive physical carrier and its rooted support component therefore both
reduce constructively to the singleton index `[0]`.  The already-proved
canonical row law then gives the exact two-step power identity required by
`CanonicalFullDensityPowerDebt` at depth `3`.

This is a genuine same-carrier finite witness.  It is not a cofinal producer,
and it supplies no thermodynamic or continuum modulus.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate

namespace YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityZeroDebt

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityCertificate
open YMGap.Continuum.BF4PhysicalVacuumSectorTimeFactorizationAdapter
open YMGap.Continuum.BF4PhysicalVacuumSectorMassNormalizedDensity
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.BF4StationaryDensityBufferSplit
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') :
    (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

private theorem setEdgeLabel_zero_zero (edge : Nat) :
    setEdgeLabel zeroEdgeLabelling edge 0 = zeroEdgeLabelling := by
  funext id
  unfold setEdgeLabel zeroEdgeLabelling
  split <;> rfl

private theorem boundedEdgeLabellings_zero_eq_singleton :
    ∀ ids : List Nat,
      boundedEdgeLabellings 0 ids = [zeroEdgeLabelling]
  | [] => rfl
  | edge :: rest => by
      unfold boundedEdgeLabellings
      rw [boundedEdgeLabellings_zero_eq_singleton rest]
      change (List.range (0 + 1)).flatMap
        (fun spin => [setEdgeLabel zeroEdgeLabelling edge spin]) =
        [zeroEdgeLabelling]
      change [0].flatMap
        (fun spin => [setEdgeLabel zeroEdgeLabelling edge spin]) =
        [zeroEdgeLabelling]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [setEdgeLabel_zero_zero]

theorem centralPositiveHalfStates_zero_eq_singleton
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) :
    centralPositiveHalfStates w hw 0 half = [zeroEdgeLabelling] := by
  unfold centralPositiveHalfStates centralHalfStates
  rw [boundedEdgeLabellings_zero_eq_singleton]
  simp only [List.filter_cons]
  have hvacuum := centralPhysicalRowMarginal_vacuum_pos hw 0 half
  simp only [hvacuum, decide_true, if_true, List.filter_nil]

private theorem list_eq_singleton_of_nodup_mem_unique
    {A : Type} {entries : List A} {target : A}
    (hnodup : entries.Nodup) (htarget : target ∈ entries)
    (hunique : ∀ entry, entry ∈ entries → entry = target) :
    entries = [target] := by
  cases entries with
  | nil => cases htarget
  | cons head tail =>
      have hhead := hunique head List.mem_cons_self
      subst head
      cases tail with
      | nil => rfl
      | cons next rest =>
          have hnext := hunique next
            (List.mem_cons_of_mem target List.mem_cons_self)
          subst next
          exact ((List.nodup_cons.mp hnodup).1 List.mem_cons_self).elim

theorem centralPhysicalFiniteIndexCarrier_zero_eq_singleton
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) :
    centralPhysicalFiniteIndexCarrier w hw 0 half = [0] := by
  unfold centralPhysicalFiniteIndexCarrier centralPhysicalFiniteCarrierSize
  rw [centralPositiveHalfStates_zero_eq_singleton w hw half]
  rfl

theorem centralPhysicalFiniteVacuumSectorIndices_zero_eq_singleton
    (w : Q') (hw : (0 : Q') ≤ w) (half : Nat) :
    centralPhysicalFiniteVacuumSectorIndices w hw 0 half = [0] := by
  let adj := centralPhysicalFiniteSupportAdjacentB w hw 0 half
  have hcarrier :
      centralPhysicalFiniteIndexCarrier w hw 0 half = [0] :=
    centralPhysicalFiniteIndexCarrier_zero_eq_singleton w hw half
  have hroot : (0 : Nat) ∈
      centralPhysicalFiniteIndexCarrier w hw 0 half := by
    rw [hcarrier]
    exact List.mem_cons_self
  have hmem : (0 : Nat) ∈
      centralPhysicalFiniteVacuumSectorIndices w hw 0 half :=
    zero_mem_centralPhysicalFiniteVacuumSectorIndices w hw 0 half
  apply list_eq_singleton_of_nodup_mem_unique
    (centralPhysicalFiniteVacuumSectorIndices_nodup w hw 0 half)
    hmem
  intro entry hentry
  have hsubset := rootComponent_subset adj hroot hentry
  rw [hcarrier] at hsubset
  exact List.mem_singleton.mp hsubset

private theorem singleton_power_eqv_of_row
    {State : Type} (x : State) (weight : State → Q')
    (kernel : State → State → Q')
    (hrow : weight x * kernel x x ≈ 1) :
    ∀ steps, finiteWeightedDensityPower [x] weight kernel steps x x ≈
      kernel x x
  | 0 => Q'.eqv_refl _
  | steps + 1 => by
      simp only [finiteWeightedDensityPower, finiteWeightedDensityCompose,
        YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm.listQSum]
      change (weight x * kernel x x) *
          finiteWeightedDensityPower [x] weight kernel steps x x + 0 ≈
        kernel x x
      have hstep := singleton_power_eqv_of_row x weight kernel hrow steps
      refine Q'.eqv_trans _
          ((weight x * kernel x x) *
            finiteWeightedDensityPower [x] weight kernel steps x x) _ ?_ ?_
      · exact Q'.eqv_of_eq (Q'.add_zero' _)
      refine Q'.eqv_trans _
          (1 * finiteWeightedDensityPower [x] weight kernel steps x x) _
          (Q'.mul_eqv_congr_right _ _ _ hrow) ?_
      refine Q'.eqv_trans _
          (finiteWeightedDensityPower [x] weight kernel steps x x) _
          (Q'.one_mul_eqv _) hstep

private theorem singleton_centered_row_mass_zero
    {State : Type} [DecidableEq State]
    (x : State) (weight : State → Q') (kernel : State → State → Q')
    (hweight : weight x ≈ 1)
    (hrow : weight x * kernel x x ≈ 1) :
    finiteWeightedCenteredRowMass [x] weight kernel x ≤ 0 := by
  have hcentered :
      weight x * (kernel x x + (-1)) ≈ 0 := by
    refine Q'.eqv_trans _
        (weight x * kernel x x + weight x * (-1)) _ ?_ ?_
    · q_ring
    refine Q'.eqv_trans _
        (1 + weight x * (-1)) _
        (Q'.add_eqv_congr_right _ _ _ hrow) ?_
    refine Q'.eqv_trans _
        (1 + (1 : Q') * (-1)) _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_right _ _ _ hweight)) ?_
    q_ring
  have habs : Q'.abs (weight x * (kernel x x + (-1))) ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.abs_eqv_congr hcentered)
      (Q'.eqv_of_eq (by decide))
  unfold finiteWeightedCenteredRowMass finiteL1Norm
    finiteWeightedCenteredTransition finiteCenteredDensity
  simp only [YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm.listQSum]
  change Q'.abs (weight x * (kernel x x + (-1))) + 0 ≤ 0
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ 0 (Q'.le_of_eqv habs))
    (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _)))

def canonicalFullDensityPowerDebt_zero_of_depth
    {w : Q'} {hw : (0 : Q') ≤ w} (half depth : Nat)
    (hdepth : 3 ≤ depth) :
    CanonicalFullDensityPowerDebt w hw 0 half depth := by
  have hcarrier := centralPhysicalFiniteIndexCarrier_zero_eq_singleton
    w hw half
  have hsector := centralPhysicalFiniteVacuumSectorIndices_zero_eq_singleton
    w hw half
  refine {
    depth_at_least_three := hdepth
    full_density_power := ?_ }
  intro source target hsource htarget
  have hsource_zero : source = 0 := by
    rw [hsector] at hsource
    exact List.mem_singleton.mp hsource
  have htarget_zero : target = 0 := by
    rw [hsector] at htarget
    exact List.mem_singleton.mp htarget
  subst source
  subst target
  let weight := centralPhysicalFiniteWeight w hw 0 half
  let kernel := canonicalFullDensityOneStepIndex w hw 0 half
  have hrow := canonicalFullDensityOneStepIndex_row
    (w := w) (hw := hw) (cutoff := 0) (half := half) (row := 0)
  have hrow_single : weight 0 * kernel 0 0 ≈ 1 := by
    rw [hcarrier] at hrow
    change weight 0 * kernel 0 0 + 0 ≈ 1 at hrow
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq (Eq.symm (Q'.add_zero' _))) hrow
  rw [hcarrier]
  change kernel 0 0 ≈ finiteWeightedDensityPower
      [0] weight kernel (depth - 1) 0 0
  exact Q'.eqv_symm
    (singleton_power_eqv_of_row 0 weight kernel hrow_single (depth - 1))

def canonicalFullDensityPowerDebt_zero
    {w : Q'} {hw : (0 : Q') ≤ w} (half : Nat) :
    CanonicalFullDensityPowerDebt w hw 0 half 3 := by
  exact canonicalFullDensityPowerDebt_zero_of_depth half 3 (by decide)

/-! At the zero cutoff the same singleton carrier also discharges the finite
centered-row input to the gluing interface, with the exact rate `qS = 0`.
This is a finite seed only: the carrier has no non-vacuum direction, so it is
not a strict gap and supplies no cofinal or continuum modulus. -/
def canonicalFullDensityVacuumSectorDensityPowerGluing_zero_of_depth
    {w : Q'} {hw : (0 : Q') ≤ w} (half depth : Nat)
    (hdepth : 3 ≤ depth) :
    PhysicalBF4VacuumSectorDensityPowerGluing
      w hw 0 half depth
      (centralPhysicalFiniteVacuumSectorConditionedTimeStep
        w hw 0 half
        (canonicalFullDensityOneStepIndex w hw 0 half)) 0 := by
  let powerDebt :=
    canonicalFullDensityPowerDebt_zero_of_depth
      (w := w) (hw := hw) half depth hdepth
  let data := canonicalFullDensityCompatibleTimeFactorization powerDebt
  refine canonicalFullDensityVacuumSectorDensityPowerGluing
    powerDebt (by decide) ?_
  intro source hsource
  have hsector := centralPhysicalFiniteVacuumSectorIndices_zero_eq_singleton
    w hw half
  have hsource_zero : source = 0 := by
    rw [hsector] at hsource
    exact List.mem_singleton.mp hsource
  subst source
  let weight := centralPhysicalFiniteVacuumSectorMassNormalizedWeight
    w hw 0 half
  let oneStep := centralPhysicalFiniteVacuumSectorConditionedTimeStep
    w hw 0 half (canonicalFullDensityOneStepIndex w hw 0 half)
  have hweight_total :=
    centralPhysicalFiniteVacuumSectorMassNormalizedWeight_total_one
      w hw 0 half
  rw [hsector] at hweight_total
  change weight 0 + 0 ≈ 1 at hweight_total
  have hweight : weight 0 ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Eq.symm (Q'.add_zero' _)))
      hweight_total
  have hrow :=
    PhysicalBF4FiniteVacuumCompatibleTimeFactorization.conditionedOneStep_row
      data 0
  rw [hsector] at hrow
  change weight 0 * oneStep 0 0 + 0 ≈ 1 at hrow
  have hprod : weight 0 * oneStep 0 0 ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Eq.symm (Q'.add_zero' _))) hrow
  rw [hsector]
  exact singleton_centered_row_mass_zero 0 weight oneStep hweight hprod

def canonicalFullDensityVacuumSectorDensityPowerGluing_zero
    {w : Q'} {hw : (0 : Q') ≤ w} (half : Nat) :
    PhysicalBF4VacuumSectorDensityPowerGluing
      w hw 0 half 3
      (centralPhysicalFiniteVacuumSectorConditionedTimeStep
        w hw 0 half
        (canonicalFullDensityOneStepIndex w hw 0 half)) 0 := by
  exact canonicalFullDensityVacuumSectorDensityPowerGluing_zero_of_depth
    half 3 (by decide)

#print axioms boundedEdgeLabellings_zero_eq_singleton
#print axioms centralPositiveHalfStates_zero_eq_singleton
#print axioms centralPhysicalFiniteIndexCarrier_zero_eq_singleton
#print axioms centralPhysicalFiniteVacuumSectorIndices_zero_eq_singleton
#print axioms canonicalFullDensityPowerDebt_zero_of_depth
#print axioms canonicalFullDensityPowerDebt_zero
#print axioms canonicalFullDensityVacuumSectorDensityPowerGluing_zero_of_depth
#print axioms canonicalFullDensityVacuumSectorDensityPowerGluing_zero

end YMGap.Continuum.BF4PhysicalVacuumSectorCanonicalFullDensityZeroDebt
