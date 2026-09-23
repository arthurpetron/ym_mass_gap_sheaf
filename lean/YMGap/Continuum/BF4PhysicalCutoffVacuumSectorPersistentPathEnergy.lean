/-
# Persistent path energy for an arbitrary BF4 sector cylinder

Fix a canonical vacuum-sector carrier and two of its coordinates.  Their
states persist in every later cutoff.  For an arbitrary cylinder presentation
(whose own base may be different), restrict its actual observable to the fixed
old carrier.  The constructed persistent edge floor and canonical positive
path control the squared endpoint difference by the pulled old-old Dirichlet
energy.  Injecting those old-old pairs into the presentation's actual later
carrier then bounds it by the full later Dirichlet energy.

This is a finite, fixed-base estimate intended for a later completed
zero-Dirichlet rigidity argument.  It does not assert a uniform gap or a
completed fixed-vector theorem.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledDirichletEmbedding
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathEnergy
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergy

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_cartesian_eq_nested_local
    {A B : Type} (value : A × B → Q')
    (left : List A) (right : List B) :
    listQSum value (cartesian left right) ≈
      listQSum
        (fun a => listQSum (fun b => value (a, b)) right)
        left := by
  unfold cartesian
  refine Q'.eqv_trans _ _ _
    (listQSum_flatMap value
      (fun a => right.map (fun b => (a, b))) left) ?_
  apply listQSum_congr
  intro a
  rw [listQSum_map]
  exact Q'.eqv_refl _

private theorem square_nonnegative (value : Q') :
    (0 : Q') ≤ value * value :=
  YMGap.Constructive.SumOfSquares.q_mul_self_nonneg value

private theorem square_eqv_congr {left right : Q'}
    (h : left ≈ right) : left * left ≈ right * right :=
  Q'.eqv_trans _ (right * left) _
    (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ h)

/-- The old-old pulled Dirichlet energy of an arbitrary cylinder's restriction
is a sub-sum of that cylinder's actual full Dirichlet energy at every cutoff
containing the fixed old carrier. No presentation-base containment is needed. -/
theorem restrictedPulledDirichlet_le_fullCylinderDirichlet
    {w : Q'} {hw : (0 : Q') ≤ w}
    (base later half : Nat) (hbaseLater : base ≤ later)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half) :
    let restricted := fun index => presentation.toLinearObservable.value
      (centralPhysicalFiniteStateAt w hw base half index)
    finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw base half)
        restricted
        (centralPhysicalFinitePulledKernel w hw base later half) ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw later half)
        (centralPhysicalFiniteCoefficient w hw later half
          presentation.toLinearObservable.value)
        (centralPhysicalFiniteKernel w hw later half) := by
  let sourceStates :=
    centralPhysicalFiniteVacuumSectorIndices w hw base half
  let targetStates :=
    centralPhysicalFiniteVacuumSectorIndices w hw later half
  let indexMap := centralPhysicalFiniteCutoffIndexMap
    w hw base later half
  let restricted := fun index => presentation.toLinearObservable.value
    (centralPhysicalFiniteStateAt w hw base half index)
  let laterCoefficient := centralPhysicalFiniteCoefficient
    w hw later half presentation.toLinearObservable.value
  let sourceTerm : Nat × Nat → Q' := fun pair =>
    centralPhysicalFinitePulledKernel
        w hw base later half pair.1 pair.2 *
      ((restricted pair.1 + -restricted pair.2) *
        (restricted pair.1 + -restricted pair.2))
  let targetTerm : Nat × Nat → Q' := fun pair =>
    centralPhysicalFiniteKernel w hw later half pair.1 pair.2 *
      ((laterCoefficient pair.1 + -laterCoefficient pair.2) *
        (laterCoefficient pair.1 + -laterCoefficient pair.2))
  let pairMap : Nat × Nat → Nat × Nat := fun pair =>
    (indexMap pair.1, indexMap pair.2)
  have hsum :
      listQSum sourceTerm (cartesian sourceStates sourceStates) ≤
        listQSum targetTerm (cartesian targetStates targetStates) := by
    apply listQSum_le_of_injective
      (cartesian sourceStates sourceStates)
      (cartesian targetStates targetStates)
      sourceTerm targetTerm pairMap
    · exact cartesian_nodup sourceStates sourceStates
        (centralPhysicalFiniteVacuumSectorIndices_nodup w hw base half)
        (centralPhysicalFiniteVacuumSectorIndices_nodup w hw base half)
    · intro pair hpair
      have hparts := (mem_cartesian_iff
        sourceStates sourceStates pair).mp hpair
      apply (mem_cartesian_iff targetStates targetStates (pairMap pair)).mpr
      exact
        ⟨centralPhysicalFiniteVacuumSectorIndexMap_mem
            hbaseLater hparts.1,
          centralPhysicalFiniteVacuumSectorIndexMap_mem
            hbaseLater hparts.2⟩
    · intro first hfirst second hsecond heq
      have hfirstParts := (mem_cartesian_iff
        sourceStates sourceStates first).mp hfirst
      have hsecondParts := (mem_cartesian_iff
        sourceStates sourceStates second).mp hsecond
      have hleftMap : indexMap first.1 = indexMap second.1 :=
        congrArg Prod.fst heq
      have hrightMap : indexMap first.2 = indexMap second.2 :=
        congrArg Prod.snd heq
      exact Prod.ext
        (centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector
          hbaseLater hfirstParts.1 hsecondParts.1 hleftMap)
        (centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector
          hbaseLater hfirstParts.2 hsecondParts.2 hrightMap)
    · intro pair hpair
      have hparts := (mem_cartesian_iff
        sourceStates sourceStates pair).mp hpair
      have hleftLt := centralPhysicalFiniteVacuumSectorIndex_lt
        w hw base half hparts.1
      have hrightLt := centralPhysicalFiniteVacuumSectorIndex_lt
        w hw base half hparts.2
      have hleftCoefficient :
          laterCoefficient (indexMap pair.1) ≈ restricted pair.1 := by
        unfold laterCoefficient restricted centralPhysicalFiniteCoefficient
        rw [centralPhysicalFiniteStateAt_cutoffIndexMap_eq
          hbaseLater hleftLt]
        exact Q'.eqv_refl _
      have hrightCoefficient :
          laterCoefficient (indexMap pair.2) ≈ restricted pair.2 := by
        unfold laterCoefficient restricted centralPhysicalFiniteCoefficient
        rw [centralPhysicalFiniteStateAt_cutoffIndexMap_eq
          hbaseLater hrightLt]
        exact Q'.eqv_refl _
      have hdifference :
          laterCoefficient (indexMap pair.1) +
              -laterCoefficient (indexMap pair.2) ≈
            restricted pair.1 + -restricted pair.2 := by
        exact Q'.add_eqv_congr' hleftCoefficient
          (Q'.neg_eqv_congr _ _ hrightCoefficient)
      have htargetSource : targetTerm (pairMap pair) ≈ sourceTerm pair := by
        unfold targetTerm sourceTerm pairMap indexMap
          centralPhysicalFinitePulledKernel
        exact Q'.mul_eqv_congr_left _ _ _
          (square_eqv_congr hdifference)
      exact Q'.ge_of_eqv htargetSource
    · intro pair hpair
      unfold targetTerm
      exact Q'.mul_nonneg _ _
        (by
          unfold centralPhysicalFiniteKernel
          exact centralNormalizedPhysicalReflectedKernel_nonnegative
            hw later half _ _)
        (square_nonnegative _)
  have hsourceCartesian :
      listQSum sourceTerm (cartesian sourceStates sourceStates) ≈
        finiteJointDirichletEnergy sourceStates restricted
          (centralPhysicalFinitePulledKernel w hw base later half) := by
    unfold finiteJointDirichletEnergy sourceTerm
    exact listQSum_cartesian_eq_nested_local _ _ _
  have htargetCartesian :
      listQSum targetTerm (cartesian targetStates targetStates) ≈
        finiteJointDirichletEnergy targetStates laterCoefficient
          (centralPhysicalFiniteKernel w hw later half) := by
    unfold finiteJointDirichletEnergy targetTerm
    exact listQSum_cartesian_eq_nested_local _ _ _
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hsourceCartesian)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv htargetCartesian))

/-- Persistent endpoint energy bound for an arbitrary cylinder presentation.
The floor and path ceiling depend only on the selected fixed base carrier. -/
theorem floor_mul_endpoint_sq_le_fullCylinderDirichlet
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half)
    (later : Nat) (hlater : certificate.start ≤ later)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (left right : Nat)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half) :
    certificate.floor *
        ((presentation.toLinearObservable.value
              (centralPhysicalFiniteStateAt w hw base half left) +
            -presentation.toLinearObservable.value
              (centralPhysicalFiniteStateAt w hw base half right)) *
          (presentation.toLinearObservable.value
              (centralPhysicalFiniteStateAt w hw base half left) +
            -presentation.toLinearObservable.value
              (centralPhysicalFiniteStateAt w hw base half right))) ≤
      centralPhysicalFiniteVacuumSectorPathCeiling w hw base half *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices w hw later half)
          (centralPhysicalFiniteCoefficient w hw later half
            presentation.toLinearObservable.value)
          (centralPhysicalFiniteKernel w hw later half) := by
  have hbaseLater : base ≤ later :=
    Nat.le_trans certificate.start_ge_base hlater
  let restricted := fun index => presentation.toLinearObservable.value
    (centralPhysicalFiniteStateAt w hw base half index)
  have hpath :=
    FixedBasePulledPositiveEdgeFloor.floor_mul_endpoint_sq_le_ceiling_mul_pulledDirichlet
      certificate later hlater restricted left right hleft hright
  have hembed := restrictedPulledDirichlet_le_fullCylinderDirichlet
    base later half hbaseLater presentation
  have hceiling0 : (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorPathCeiling w hw base half :=
    Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorPathCeiling_pos w hw base half)
  exact Q'.le_trans' _ _ _ hpath
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hembed hceiling0)

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergy

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergy.restrictedPulledDirichlet_le_fullCylinderDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPersistentPathEnergy.floor_mul_endpoint_sq_le_fullCylinderDirichlet
