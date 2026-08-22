/-
# One-cutoff Markov closure of BF4 root-sector cylinders

The completed sector-transfer lift requires two ingredients: finite Markov
closure of the canonical root component and a cofinal schedule ensuring that
the action cutoff dominates the selected presentation base.  This module
proves the first ingredient exactly.

If a sector cylinder presentation has base at most `cutoff`, then its realized
coefficient vanishes outside the root component at `cutoff`.  Symmetry and row
closure of the physical kernel imply that its Markov image also vanishes
outside that component.  Reading the image values on the component therefore
constructs a new presentation at `cutoff` whose realization agrees with the
recoded Markov action on the entire positive carrier.

This is a finite-stage support and recoding theorem.  It does not yet prove
that the resulting cutoff-indexed presentations are Cauchy or construct the
completed transfer lift.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSKernelSymmetry

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_eqv_zero_of_pointwise
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≈ 0) →
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_eqv_zero_of_pointwise value tail
            (fun item hitem =>
              hzero item (List.mem_cons_of_mem head hitem)))
      · exact Q'.eqv_of_eq (Q'.zero_add' 0)

/-! ## 1. Kernel separation in finite index form -/

private theorem centralNormalizedPhysicalReflectedKernel_eqv_zero_of_raw
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {source target : EdgeLabelling}
    (hraw : centralPhysicalReflectedKernel w cutoff half
      source target ≈ 0) :
    centralNormalizedPhysicalReflectedKernel w hw cutoff half
        source target ≈ 0 := by
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  refine Q'.eqv_trans _
    (0 * Q'.recipPos
      (slabParametricKPhysicalPartition w cutoff (centralExtent half))
      (slabParametricKPhysicalPartition_pos hw cutoff
        (centralExtent half))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hraw
  · exact Q'.zero_mul_eqv _

private theorem centralPhysicalConditionalKernel_eqv_zero_of_raw
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    {source target : EdgeLabelling}
    (hsource : source ∈ centralPositiveHalfStates w hw cutoff half)
    (hraw : centralPhysicalReflectedKernel w cutoff half
      source target ≈ 0) :
    centralPhysicalConditionalKernel w hw cutoff half
        source target ≈ 0 := by
  have hrow := (mem_centralPositiveHalfStates_iff.mp hsource).2
  rw [centralPhysicalConditionalKernel_eq_divPos hrow]
  unfold Q'.divPos
  refine Q'.eqv_trans _
    (0 * Q'.recipPos
      (centralPhysicalRowMarginal w hw cutoff half source) hrow) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (centralNormalizedPhysicalReflectedKernel_eqv_zero_of_raw hraw)
  · exact Q'.zero_mul_eqv _

/-- A source outside the canonical root component cannot jump into it. -/
theorem centralPhysicalConditionalKernel_outside_vacuumSector_eqv_zero
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half source target : Nat}
    (hsource : source <
      centralPhysicalFiniteCarrierSize w hw cutoff half)
    (hsourceOutside : source ∉
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalConditionalKernel w hw cutoff half
        (centralPhysicalFiniteStateAt w hw cutoff half source)
        (centralPhysicalFiniteStateAt w hw cutoff half target) ≈ 0 := by
  have htargetLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw cutoff half htarget
  have hsourcePositive := centralPhysicalFiniteStateAt_mem_positive
    w hw cutoff half hsource
  apply centralPhysicalConditionalKernel_eqv_zero_of_raw hsourcePositive
  have hsourceHalf :=
    (mem_centralPositiveHalfStates_iff.mp hsourcePositive).1
  have htargetPositive := centralPhysicalFiniteStateAt_mem_positive
    w hw cutoff half htargetLt
  have htargetHalf :=
    (mem_centralPositiveHalfStates_iff.mp htargetPositive).1
  have hsymm := centralPhysicalReflectedKernel_symm w
    hsourceHalf htargetHalf
  refine Q'.eqv_trans _ _ _ hsymm ?_
  exact centralPhysicalFiniteVacuumSector_rowClosed
    w hw cutoff half htarget hsource hsourceOutside

/-! ## 2. Support preservation of the realized Markov action -/

/-- A realized old sector presentation is zero at every current carrier index
outside the current canonical component. -/
theorem centralPhysicalVacuumSectorPresentation_value_eqv_zero_of_outside
    {w : Q'} {hw : (0 : Q') ≤ w} {half cutoff target : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (hbase : presentation.base ≤ cutoff)
    (htarget : target <
      centralPhysicalFiniteCarrierSize w hw cutoff half)
    (houtside : target ∉
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    presentation.toLinearObservable.value
        (centralPhysicalFiniteStateAt w hw cutoff half target) ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalFiniteVacuumSectorLinearObservable_value_eqv_extension
      hbase presentation.coefficient htarget)
    (centralPhysicalFiniteVacuumSectorCoefficientExtension_eqv_zero_of_not_mem
      hbase houtside presentation.coefficient)

/-- The genuine finite Markov image of a realized root-sector presentation
vanishes at every retained source outside the root component. -/
theorem centralPhysicalMarkovApply_vacuumSectorPresentation_eqv_zero_of_outside
    {w : Q'} {hw : (0 : Q') ≤ w} {half cutoff source : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (hbase : presentation.base ≤ cutoff)
    (hsource : source <
      centralPhysicalFiniteCarrierSize w hw cutoff half)
    (hsourceOutside : source ∉
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalMarkovApply w hw cutoff half
        presentation.toLinearObservable.value
        (centralPhysicalFiniteStateAt w hw cutoff half source) ≈ 0 := by
  let states := centralPositiveHalfStates w hw cutoff half
  let sourceState := centralPhysicalFiniteStateAt w hw cutoff half source
  let summand := fun target : EdgeLabelling =>
    centralPhysicalConditionalKernel w hw cutoff half sourceState target *
      presentation.toLinearObservable.value target
  refine Q'.eqv_trans _
    (listQSum
      (fun target => summand
        (finiteListStateAt states zeroEdgeLabelling target))
      (List.range states.length)) _ ?_ ?_
  · unfold centralPhysicalMarkovApply
    exact Q'.eqv_of_eq
      (Eq.symm (finiteIndexSum_eq_listQSum
        states zeroEdgeLabelling summand))
  · apply listQSum_eqv_zero_of_pointwise
    intro target htarget
    have htargetLt : target < states.length := List.mem_range.mp htarget
    change target < centralPhysicalFiniteCarrierSize
      w hw cutoff half at htargetLt
    by_cases htargetSector : target ∈
        centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
    · refine Q'.eqv_trans _ (0 *
        presentation.toLinearObservable.value
          (centralPhysicalFiniteStateAt w hw cutoff half target)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (centralPhysicalConditionalKernel_outside_vacuumSector_eqv_zero
            hsource hsourceOutside htargetSector)
      · exact Q'.zero_mul_eqv _
    · refine Q'.eqv_trans _
        (centralPhysicalConditionalKernel w hw cutoff half
          sourceState
          (centralPhysicalFiniteStateAt w hw cutoff half target) * 0) _ ?_ ?_
      · exact Q'.mul_eqv_congr_left _ _ _
          (centralPhysicalVacuumSectorPresentation_value_eqv_zero_of_outside
            presentation hbase htargetLt htargetSector)
      · exact Q'.mul_zero_eqv _

/-- The globally recoded finite-linear Markov action has the same outside-zero
property on the retained carrier. -/
theorem centralPhysicalLinearMarkovCutoffAction_vacuumSectorPresentation_eqv_zero_of_outside
    {w : Q'} {hw : (0 : Q') ≤ w} {half cutoff source : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (hbase : presentation.base ≤ cutoff)
    (hsource : source <
      centralPhysicalFiniteCarrierSize w hw cutoff half)
    (hsourceOutside : source ∉
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    (centralPhysicalLinearMarkovCutoffAction hw cutoff half
      presentation.toLinearObservable).value
        (centralPhysicalFiniteStateAt w hw cutoff half source) ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalLinearMarkovCutoffAction_value_of_mem
      hw cutoff half presentation.toLinearObservable
      (centralPhysicalFiniteStateAt w hw cutoff half source)
      (centralPhysicalFiniteStateAt_mem_positive
        w hw cutoff half hsource))
    (centralPhysicalMarkovApply_vacuumSectorPresentation_eqv_zero_of_outside
      presentation hbase hsource hsourceOutside)

/-! ## 3. Exact recoding as a new sector presentation -/

/-- At equal source and target cutoffs, the explicit cutoff index map is the
identity on the canonical component. -/
theorem centralPhysicalFiniteCutoffIndexMap_self
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half index : Nat}
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalFiniteCutoffIndexMap
      w hw cutoff cutoff half index = index := by
  have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw cutoff half hindex
  exact centralPhysicalFiniteStateAt_injective_of_lt
    (centralPhysicalFiniteCutoffIndexMap_lt
      (Nat.le_refl cutoff) hindexLt)
    hindexLt
    (centralPhysicalFiniteStateAt_cutoffIndexMap_eq
      (Nat.le_refl cutoff) hindexLt)

/-- At equal cutoffs, coefficient extension is the identity on the canonical
component.  Keeping this fact independent of the large Markov expression
prevents later proofs from unfolding that expression during elaboration. -/
theorem centralPhysicalFiniteVacuumSectorCoefficientExtension_self_of_mem
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half target : Nat}
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw cutoff cutoff half coefficient target ≈
      coefficient target := by
  have honMap :=
    centralPhysicalFiniteVacuumSectorCoefficientExtension_on_map
      (w := w) (hw := hw) (base := cutoff) (later := cutoff)
      (half := half) (index := target) (Nat.le_refl cutoff)
      htarget coefficient
  rw [centralPhysicalFiniteCutoffIndexMap_self htarget] at honMap
  exact honMap

/-- The current-cutoff Markov image, read on one canonical-sector index. -/
def centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (cutoff : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (index : Nat) : Q' :=
  (centralPhysicalLinearMarkovCutoffAction hw cutoff half
    presentation.toLinearObservable).value
    (centralPhysicalFiniteStateAt w hw cutoff half index)

theorem centralPhysicalVacuumSectorMarkovCoefficientAtCutoff_eqv_action
    {w : Q'} {hw : (0 : Q') ≤ w} {half cutoff index : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half) :
    centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
        cutoff presentation index ≈
      (centralPhysicalLinearMarkovCutoffAction hw cutoff half
        presentation.toLinearObservable).value
        (centralPhysicalFiniteStateAt w hw cutoff half index) := by
  unfold centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
  exact Q'.eqv_refl _

/-- Read the finite Markov image on the current root component and package it
as a new sector cylinder presentation at the action cutoff. -/
def centralPhysicalVacuumSectorPresentationMarkovAtCutoff
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (cutoff : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half) :
    CentralPhysicalVacuumSectorCylinderPresentation w hw half where
  base := cutoff
  coefficient :=
    centralPhysicalVacuumSectorMarkovCoefficientAtCutoff cutoff presentation

theorem centralPhysicalVacuumSectorMarkovCoefficientAtCutoff_eqv_zero_of_outside
    {w : Q'} {hw : (0 : Q') ≤ w} {half cutoff target : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (hbase : presentation.base ≤ cutoff)
    (htarget : target <
      centralPhysicalFiniteCarrierSize w hw cutoff half)
    (houtside : target ∉
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half) :
    centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
        cutoff presentation target ≈ 0 := by
  unfold centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
  exact
    centralPhysicalLinearMarkovCutoffAction_vacuumSectorPresentation_eqv_zero_of_outside
      presentation hbase htarget houtside

/-- Zero-extending the sampled sector coefficient at the same cutoff recovers
that coefficient on the entire positive carrier. -/
theorem centralPhysicalVacuumSectorMarkovCoefficientExtension_eqv_self
    {w : Q'} {hw : (0 : Q') ≤ w} {half cutoff target : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (hbase : presentation.base ≤ cutoff)
    (htarget : target <
      centralPhysicalFiniteCarrierSize w hw cutoff half) :
    centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw cutoff cutoff half
        (centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
          cutoff presentation) target ≈
      centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
        cutoff presentation target := by
  by_cases hsector : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half
  · exact centralPhysicalFiniteVacuumSectorCoefficientExtension_self_of_mem
      hsector
      (centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
        cutoff presentation)
  · exact Q'.eqv_trans _ 0 _
      (centralPhysicalFiniteVacuumSectorCoefficientExtension_eqv_zero_of_not_mem
        (Nat.le_refl cutoff) hsector
        (centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
          cutoff presentation))
      (Q'.eqv_symm
        (centralPhysicalVacuumSectorMarkovCoefficientAtCutoff_eqv_zero_of_outside
          presentation hbase htarget hsector))

/-- **Finite sector-action recoding.**  Once the action cutoff dominates the
input base, realizing the sampled sector coefficient agrees with the genuine
recoded Markov action at every index of the entire positive carrier. -/
theorem centralPhysicalVacuumSectorMarkovCylinderRealization_value
    {w : Q'} {hw : (0 : Q') ≤ w} {half cutoff target : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (hbase : presentation.base ≤ cutoff)
    (htarget : target <
      centralPhysicalFiniteCarrierSize w hw cutoff half) :
    (centralPhysicalFiniteVacuumSectorLinearObservable
        w hw cutoff half
        (centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
          cutoff presentation)).value
        (centralPhysicalFiniteStateAt w hw cutoff half target) ≈
      centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
        cutoff presentation target := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalFiniteVacuumSectorLinearObservable_value_eqv_extension
      (w := w) (hw := hw) (base := cutoff) (later := cutoff)
      (half := half) (target := target) (Nat.le_refl cutoff)
      (centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
        cutoff presentation) htarget)
    (centralPhysicalVacuumSectorMarkovCoefficientExtension_eqv_self
      presentation hbase htarget)

/-- The realized sector recoding and the global finite-linear action have zero
finite GNS distance at the action cutoff. -/
theorem centralPhysicalVacuumSectorMarkovCylinder_finiteDistSq_eqv_zero
    {w : Q'} {hw : (0 : Q') ≤ w} {half cutoff : Nat}
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (hbase : presentation.base ≤ cutoff) :
    (centralPhysicalSmulGNS w hw cutoff half).toGNSData.distSqQ
        (centralPhysicalFiniteVacuumSectorLinearObservable
          w hw cutoff half
          (centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
            cutoff presentation)).value
        (centralPhysicalLinearMarkovCutoffAction hw cutoff half
          presentation.toLinearObservable).value ≈ 0 := by
  let size := centralPhysicalFiniteCarrierSize w hw cutoff half
  let weight := centralPhysicalFiniteWeight w hw cutoff half
  let observableDifference := fun state =>
    (centralPhysicalFiniteVacuumSectorLinearObservable
      w hw cutoff half
      (centralPhysicalVacuumSectorMarkovCoefficientAtCutoff
        cutoff presentation)).value state +
      -(centralPhysicalLinearMarkovCutoffAction hw cutoff half
        presentation.toLinearObservable).value state
  let difference := centralPhysicalFiniteCoefficient
    w hw cutoff half observableDifference
  have hdifference : ∀ target, target < size → difference target ≈ 0 := by
    intro target htarget
    have hvalue :=
      centralPhysicalVacuumSectorMarkovCylinderRealization_value
        presentation hbase htarget
    have haction :=
      centralPhysicalVacuumSectorMarkovCoefficientAtCutoff_eqv_action
        (cutoff := cutoff) (index := target) presentation
    have hagree := Q'.eqv_trans _ _ _ hvalue haction
    unfold difference centralPhysicalFiniteCoefficient observableDifference
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hagree)
      (Q'.add_neg_self_eqv _)
  have hfinite : finiteDiagonalQuadratic size weight difference ≈ 0 := by
    unfold finiteDiagonalQuadratic
    apply listQSum_eqv_zero_of_pointwise
    intro target htarget
    have htargetLt : target < size := List.mem_range.mp htarget
    have hzero := hdifference target htargetLt
    have hsquare : difference target * difference target ≈ 0 := by
      refine Q'.eqv_trans _
        (0 * difference target) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _ hzero
      · exact Q'.zero_mul_eqv _
    exact Q'.eqv_trans _ (0 * weight target) _
      (Q'.mul_eqv_congr_right _ _ _ hsquare)
      (Q'.zero_mul_eqv _)
  have hbridge :=
    centralPhysicalFiniteDiagonalQuadratic_eqv_weightedInner
      w hw cutoff half observableDifference
  change centralPhysicalWeightedInner
    w hw cutoff half observableDifference observableDifference ≈ 0
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hbridge) hfinite

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction.centralPhysicalConditionalKernel_outside_vacuumSector_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction.centralPhysicalMarkovApply_vacuumSectorPresentation_eqv_zero_of_outside
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction.centralPhysicalVacuumSectorMarkovCylinderRealization_value
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction.centralPhysicalVacuumSectorMarkovCylinder_finiteDistSq_eqv_zero
