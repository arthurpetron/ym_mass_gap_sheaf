/-
# A cutoff-uniform raw-row ceiling on the central spin-cube ray

The literal positive-carrier row is first enlarged to the complete bounded
target carrier using production-kernel nonnegativity.  The source-spin-free
decorated summand bound is then summed over every boundary and target, finite
Fubini identifies that nested sum with the boundary-target carrier, and the
66-face carrier ceiling finishes the estimate.

This is a cutoff-uniform raw-row estimate on one explicit spin-cube ray.  It
does not establish a full-sector return floor, transfer-operator gap,
thermodynamic or continuum limit, or the Clay theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound
import YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio

namespace YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerSpinCubePositiveRay
open YMGap.Continuum.BF4CentralSpinCubeResidualCarrierSumBound
open YMGap.Continuum.BF4CentralSpinCubeResidualDecoratedFaceBound
open YMGap.Continuum.BF4CentralSpinCubeResidualLinkBound
open YMGap.Continuum.BF4CentralSpinCubeTermDecoratedBound
open YMGap.Continuum.BF4PhysicalSpinCubeRawReturnRatio
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A → Q') : ∀ xs : List A,
      (∀ x, x ∈ xs → left x ≤ right x) →
      listQSum left xs ≤ listQSum right xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun x hx => hle x (List.mem_cons_of_mem head hx)))

private theorem listQSum_filter_le_nonnegative_local {A : Type}
    (weight : A → Q') (hweight : ∀ item, (0 : Q') ≤ weight item)
    (test : A → Bool) (source : List A) :
    listQSum weight (source.filter test) ≤
      listQSum weight source := by
  have hcomplement :
      (0 : Q') ≤
        listQSum weight
          (source.filter (fun item => !(test item))) := by
    apply listQSum_nonnegative_on
    intro item _hitem
    exact hweight item
  have hadd :
      listQSum weight (source.filter test) ≤
        listQSum weight (source.filter test) +
          listQSum weight
            (source.filter (fun item => !(test item))) :=
    Q'.add_le_self_of_nonneg _ _ hcomplement
  exact Q'.le_trans' _ _ _ hadd
    (Q'.ge_of_eqv
      (listQSum_filter_partition weight test source))

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

private theorem centralSpinCubeDecoratedNestedSum_eqv_carrierSum
    (cutoff : Nat) :
    listQSum
        (fun target =>
          listQSum
            (fun boundary =>
              centralSpinCubeResidualDecoratedFaceProduct
                anchorCoupling boundary target)
            (centralBoundaryChannels cutoff 0))
        (centralHalfStates cutoff 0) ≈
      listQSum
        (fun pair =>
          centralSpinCubeResidualDecoratedFaceProduct
            anchorCoupling pair.1 pair.2)
        (centralSpinCubeBoundaryTargetPairs cutoff) := by
  let value := fun pair : EdgeLabelling × EdgeLabelling =>
    centralSpinCubeResidualDecoratedFaceProduct
      anchorCoupling pair.1 pair.2
  refine Q'.eqv_trans _
    (listQSum
      (fun boundary =>
        listQSum
          (fun target =>
            centralSpinCubeResidualDecoratedFaceProduct
              anchorCoupling boundary target)
          (centralHalfStates cutoff 0))
      (centralBoundaryChannels cutoff 0)) _
    (listQSum_swap
      (fun boundary target =>
        centralSpinCubeResidualDecoratedFaceProduct
          anchorCoupling boundary target)
      (centralBoundaryChannels cutoff 0)
      (centralHalfStates cutoff 0)) ?_
  unfold centralSpinCubeBoundaryTargetPairs
  exact Q'.eqv_symm
    (listQSum_cartesian_eq_nested_local value
      (centralBoundaryChannels cutoff 0)
      (centralHalfStates cutoff 0))

/-! ## Literal positive-row estimate -/

/-- The complete unnormalised positive-carrier row of an admitted central
spin-cube source is bounded by its exact six-face source activity times the
fixed 66-face residual-carrier ceiling, uniformly in the cutoff. -/
theorem centralLowerSpinCubePositiveRawRow_le_activity_mul_ceiling
    {cutoff spin : Nat} (hspin : spin ≤ cutoff) :
    centralPhysicalPositiveRawRowMass
        anchorCoupling (by decide) cutoff 0
        (centralLowerSpinCubeState spin) ≤
      (coeffW anchorCoupling spin) ^ 6 *
        centralSpinCubeResidualCarrierCeiling := by
  let activity := (coeffW anchorCoupling spin) ^ 6
  let source := centralLowerSpinCubeState spin
  let kernel := centralPhysicalReflectedKernel
    anchorCoupling cutoff 0 source
  let decorated := fun boundary target =>
    centralSpinCubeResidualDecoratedFaceProduct
      anchorCoupling boundary target
  have hfiltered :
      listQSum kernel
          (centralPositiveHalfStates
            anchorCoupling (by decide) cutoff 0) ≤
        listQSum kernel (centralHalfStates cutoff 0) := by
    unfold centralPositiveHalfStates
    apply listQSum_filter_le_nonnegative_local
    intro target
    unfold kernel
    exact
      BF4PhysicalCutoffKernelSupportPersistence.centralPhysicalReflectedKernel_nonnegative
        (by decide) cutoff 0 source target
  have htarget : ∀ target,
      target ∈ centralHalfStates cutoff 0 →
      kernel target ≤
        activity *
          listQSum (fun boundary => decorated boundary target)
            (centralBoundaryChannels cutoff 0) := by
    intro target htarget
    unfold kernel centralPhysicalReflectedKernel
    have htermwise :
        listQSum
            (fun boundary =>
              slabParametricKPhysicalTerm
                anchorCoupling cutoff (centralExtent 0)
                (assembleReflectedSlabLabelling
                  0 source boundary target))
            (centralBoundaryChannels cutoff 0) ≤
          listQSum
            (fun boundary => activity * decorated boundary target)
            (centralBoundaryChannels cutoff 0) := by
      apply listQSum_le_termwise_local
      intro boundary hboundary
      change
        slabParametricKPhysicalTerm anchorCoupling cutoff 1
            (centralSpinCubeSourcePhysical spin boundary target) ≤
          (coeffW anchorCoupling spin) ^ 6 *
            centralSpinCubeResidualDecoratedFaceProduct
              anchorCoupling boundary target
      exact centralSpinCubePhysicalTerm_le_activity_mul_decorated
        (by decide) hspin boundary target hboundary htarget
    exact Q'.le_trans' _ _ _ htermwise
      (Q'.le_of_eqv
        (listQSum_mul_left activity
          (fun boundary => decorated boundary target)
          (centralBoundaryChannels cutoff 0)))
  have hfull :
      listQSum kernel (centralHalfStates cutoff 0) ≤
        activity *
          listQSum
            (fun pair => decorated pair.1 pair.2)
            (centralSpinCubeBoundaryTargetPairs cutoff) := by
    have houter :
        listQSum kernel (centralHalfStates cutoff 0) ≤
          listQSum
            (fun target =>
              activity *
                listQSum
                  (fun boundary => decorated boundary target)
                  (centralBoundaryChannels cutoff 0))
            (centralHalfStates cutoff 0) := by
      apply listQSum_le_termwise_local
      exact htarget
    have hfactor :
        listQSum
            (fun target =>
              activity *
                listQSum
                  (fun boundary => decorated boundary target)
                  (centralBoundaryChannels cutoff 0))
            (centralHalfStates cutoff 0) ≈
          activity *
            listQSum
              (fun target =>
                listQSum
                  (fun boundary => decorated boundary target)
                  (centralBoundaryChannels cutoff 0))
              (centralHalfStates cutoff 0) :=
      listQSum_mul_left activity
        (fun target =>
          listQSum (fun boundary => decorated boundary target)
            (centralBoundaryChannels cutoff 0))
        (centralHalfStates cutoff 0)
    have hcarrier :
        listQSum
            (fun target =>
              listQSum
                (fun boundary => decorated boundary target)
                (centralBoundaryChannels cutoff 0))
            (centralHalfStates cutoff 0) ≈
          listQSum
            (fun pair => decorated pair.1 pair.2)
            (centralSpinCubeBoundaryTargetPairs cutoff) := by
      unfold decorated
      exact centralSpinCubeDecoratedNestedSum_eqv_carrierSum cutoff
    exact Q'.le_trans' _ _ _ houter
      (Q'.le_of_eqv
        (Q'.eqv_trans _ _ _ hfactor
          (Q'.mul_eqv_congr_left activity _ _ hcarrier)))
  have hactivity0 : (0 : Q') ≤ activity := by
    unfold activity
    exact Q'.pow_nonneg _ (coeffW_nonneg (by decide) spin) 6
  have hceiling := centralSpinCubeResidualCarrierSum_le_ceiling cutoff
  have hmul :
      activity *
          listQSum
            (fun pair => decorated pair.1 pair.2)
            (centralSpinCubeBoundaryTargetPairs cutoff) ≤
        activity * centralSpinCubeResidualCarrierCeiling := by
    apply Q'.mul_le_mul_of_nonneg_left
    · unfold decorated
      exact hceiling
    · exact hactivity0
  unfold centralPhysicalPositiveRawRowMass
  exact Q'.le_trans' _ _ _ hfiltered
    (Q'.le_trans' _ _ _ hfull hmul)

end YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling

/-! ## Dependency gate -/

#print axioms YMGap.Continuum.BF4CentralSpinCubeRawRowCeiling.centralLowerSpinCubePositiveRawRow_le_activity_mul_ceiling
