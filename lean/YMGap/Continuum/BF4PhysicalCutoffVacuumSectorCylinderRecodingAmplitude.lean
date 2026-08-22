/-
# Pointwise amplitude bounds for the BF4 sector recoding

The adaptive recoding-tail estimate splits each later physical carrier into
the action-cutoff core and its stationary source shell.  The core error is
exactly zero.  To multiply the shell mass by a finite envelope, this file
proves that both the global cutoff Markov image and its canonical-sector
recoding are pointwise bounded by the input presentation's coefficient `l1`.

The global bound is an induction through the finite-linear state-cylinder
syntax: the cutoff action sends every unit atom to another unit atom.  The
sector bound additionally uses uniqueness of the finite lower-face cylinder
which can match one arbitrary edge labelling.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingAmplitude

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderBaseControlledCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderFiniteAction
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.TsumDeriv
open YMGap.Continuum.TsumDeriv.Q'
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The cutoff action preserves the cylinder coefficient envelope -/

/-- A cutoff Markov action on a finite state-cylinder combination is bounded
pointwise by the original coefficient `l1`. -/
theorem centralPhysicalStateCylinderLinearCombinationMarkov_abs_le_l1
    {w : Q'} (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (stateAt : Nat → EdgeLabelling)
    (coefficient : Nat → Q') (state : EdgeLabelling) :
    ∀ indices : List Nat,
      Q'.abs
          ((centralPhysicalLinearMarkovCutoffAction hw cutoff half
            (centralPhysicalStateCylinderLinearCombination
              half stateAt coefficient indices)).value state) ≤
        coefficientL1 indices coefficient
  | [] => by
      change Q'.abs (0 : Q') ≤ 0
      decide
  | index :: rest => by
      let unit := centralPhysicalMarkovCutoffUnitObservable
        hw cutoff half
        (centralPhysicalStateCylinderUnitObservable half (stateAt index))
      have hunit0 : (0 : Q') ≤ unit.value state := unit.nonnegative state
      have hunit1 : unit.value state ≤ (1 : Q') := unit.le_one state
      have hunitAbs : Q'.abs (unit.value state) ≤ (1 : Q') := by
        rw [ExpNeg.abs_of_nonneg hunit0]
        exact hunit1
      simp only [centralPhysicalStateCylinderLinearCombination,
        centralPhysicalLinearMarkovCutoffAction,
        CentralPhysicalLinearObservable.value, coefficientL1, listQSum]
      refine Q'.le_trans' _ _ _
        (TsumDeriv.abs_add_le
          (coefficient index * unit.value state)
          ((centralPhysicalLinearMarkovCutoffAction hw cutoff half
            (centralPhysicalStateCylinderLinearCombination
              half stateAt coefficient rest)).value state)) ?_
      apply Q'.add_le_add
      · refine Q'.le_trans' _ _ _
          (TsumDeriv.Q'.abs_mul_le
            (coefficient index) (unit.value state)) ?_
        refine Q'.le_trans' _ (Q'.abs (coefficient index) * 1) _ ?_ ?_
        · exact Q'.mul_le_mul_of_nonneg_left _ _ _ hunitAbs
            (Q'.abs_nonneg (coefficient index))
        · exact Q'.le_of_eqv (Q'.mul_one_eqv _)
      · exact centralPhysicalStateCylinderLinearCombinationMarkov_abs_le_l1
          hw cutoff half stateAt coefficient state rest

/-- The genuine global cutoff action of a sector presentation is bounded by
the presentation's finite coefficient `l1` envelope. -/
theorem centralPhysicalLinearMarkovCutoffAction_vacuumSector_abs_le_l1
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (cutoff : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (state : EdgeLabelling) :
    Q'.abs
        ((centralPhysicalLinearMarkovCutoffAction hw cutoff half
          presentation.toLinearObservable).value state) ≤
      centralPhysicalVacuumSectorPresentationL1 presentation := by
  unfold CentralPhysicalVacuumSectorCylinderPresentation.toLinearObservable
    centralPhysicalFiniteVacuumSectorLinearObservable
    centralPhysicalVacuumSectorPresentationL1
  exact centralPhysicalStateCylinderLinearCombinationMarkov_abs_le_l1
    hw cutoff half
    (centralPhysicalFiniteStateAt w hw presentation.base half)
    presentation.coefficient state
    (centralPhysicalFiniteVacuumSectorIndices
      w hw presentation.base half)

/-! ## 2. At most one finite state cylinder matches any labelling -/

private theorem stateCylinderCombination_value_eqv_zero_of_no_match
    (half : Nat) (stateAt : Nat → EdgeLabelling)
    (coefficient : Nat → Q') (state : EdgeLabelling) :
    ∀ indices : List Nat,
      (∀ index, index ∈ indices →
        labellingsAgreeOnB
          (centralLowerFaceIds half) state (stateAt index) = false) →
      (centralPhysicalStateCylinderLinearCombination
        half stateAt coefficient indices).value state ≈ 0
  | [], _ => Q'.eqv_refl 0
  | index :: rest, hnone => by
      have hhead := hnone index List.mem_cons_self
      have htail : ∀ item, item ∈ rest →
          labellingsAgreeOnB
            (centralLowerFaceIds half) state (stateAt item) = false :=
        fun item hitem =>
          hnone item (List.mem_cons_of_mem index hitem)
      simp only [centralPhysicalStateCylinderLinearCombination,
        CentralPhysicalLinearObservable.value,
        centralPhysicalStateCylinderUnitObservable, hhead,
        Bool.false_eq_true, if_false]
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr'
          (Q'.mul_zero_eqv (coefficient index))
          (stateCylinderCombination_value_eqv_zero_of_no_match
            half stateAt coefficient state rest htail))
        (YMGap.Constructive.Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem stateCylinderCombination_abs_le_of_unique_match
    (half : Nat) (stateAt : Nat → EdgeLabelling)
    (coefficient : Nat → Q') (state : EdgeLabelling)
    (bound : Q') (hbound : (0 : Q') ≤ bound) :
    ∀ indices : List Nat,
      indices.Nodup →
      (∀ index, index ∈ indices → Q'.abs (coefficient index) ≤ bound) →
      (∀ left, left ∈ indices → ∀ right, right ∈ indices →
        labellingsAgreeOnB
          (centralLowerFaceIds half) state (stateAt left) = true →
        labellingsAgreeOnB
          (centralLowerFaceIds half) state (stateAt right) = true →
        left = right) →
      Q'.abs
          ((centralPhysicalStateCylinderLinearCombination
            half stateAt coefficient indices).value state) ≤ bound
  | [], _, _, _ => by
      change Q'.abs (0 : Q') ≤ bound
      change (0 : Q') ≤ bound
      exact hbound
  | index :: rest, hnodup, hcoefficient, hunique => by
      cases hagree : labellingsAgreeOnB
          (centralLowerFaceIds half) state (stateAt index) with
      | false =>
          have htailNodup := (List.nodup_cons.mp hnodup).2
          have htailCoefficient : ∀ item, item ∈ rest →
              Q'.abs (coefficient item) ≤ bound :=
            fun item hitem =>
              hcoefficient item (List.mem_cons_of_mem index hitem)
          have htailUnique : ∀ left, left ∈ rest →
              ∀ right, right ∈ rest →
              labellingsAgreeOnB
                (centralLowerFaceIds half) state (stateAt left) = true →
              labellingsAgreeOnB
                (centralLowerFaceIds half) state (stateAt right) = true →
              left = right := by
            intro left hleft right hright
            exact hunique left (List.mem_cons_of_mem index hleft)
              right (List.mem_cons_of_mem index hright)
          have htail := stateCylinderCombination_abs_le_of_unique_match
            half stateAt coefficient state bound hbound rest htailNodup
            htailCoefficient htailUnique
          have hvalue :
              (centralPhysicalStateCylinderLinearCombination
                half stateAt coefficient (index :: rest)).value state ≈
              (centralPhysicalStateCylinderLinearCombination
                half stateAt coefficient rest).value state := by
            simp only [centralPhysicalStateCylinderLinearCombination,
              CentralPhysicalLinearObservable.value,
              centralPhysicalStateCylinderUnitObservable, hagree,
              Bool.false_eq_true, if_false]
            exact Q'.eqv_trans _ (0 + _)
              _ (Q'.add_eqv_congr_right _ _ _
                (Q'.mul_zero_eqv (coefficient index)))
              (YMGap.Constructive.Q'.eqv_of_eq (Q'.zero_add' _))
          exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr hvalue)) htail
      | true =>
          have hnotmem := (List.nodup_cons.mp hnodup).1
          have htailNoMatch : ∀ item, item ∈ rest →
              labellingsAgreeOnB
                (centralLowerFaceIds half) state (stateAt item) = false := by
            intro item hitem
            cases hitemAgree : labellingsAgreeOnB
                (centralLowerFaceIds half) state (stateAt item) with
            | false => rfl
            | true =>
                have heq := hunique index List.mem_cons_self
                  item (List.mem_cons_of_mem index hitem) hagree hitemAgree
                subst item
                exact False.elim (hnotmem hitem)
          have htailZero :=
            stateCylinderCombination_value_eqv_zero_of_no_match
              half stateAt coefficient state rest htailNoMatch
          have hvalue :
              (centralPhysicalStateCylinderLinearCombination
                half stateAt coefficient (index :: rest)).value state ≈
              coefficient index := by
            simp only [centralPhysicalStateCylinderLinearCombination,
              CentralPhysicalLinearObservable.value,
              centralPhysicalStateCylinderUnitObservable, hagree, if_true]
            exact Q'.eqv_trans _ (coefficient index + 0) _
              (Q'.add_eqv_congr'
                (Q'.mul_one_eqv (coefficient index)) htailZero)
              (YMGap.Constructive.Q'.eqv_of_eq (Q'.add_zero' _))
          exact Q'.le_trans' _ _ _
            (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr hvalue))
            (hcoefficient index List.mem_cons_self)

private theorem centralPhysicalFiniteStateCylinder_match_unique
    {w : Q'} {hw : (0 : Q') ≤ w} {cutoff half : Nat}
    (state : EdgeLabelling)
    {left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    (hleftAgree : labellingsAgreeOnB
      (centralLowerFaceIds half) state
      (centralPhysicalFiniteStateAt w hw cutoff half left) = true)
    (hrightAgree : labellingsAgreeOnB
      (centralLowerFaceIds half) state
      (centralPhysicalFiniteStateAt w hw cutoff half right) = true) :
    left = right := by
  have hleftLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw cutoff half hleft
  have hrightLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw cutoff half hright
  have hleftPositive := centralPhysicalFiniteStateAt_mem_positive
    w hw cutoff half hleftLt
  have hrightPositive := centralPhysicalFiniteStateAt_mem_positive
    w hw cutoff half hrightLt
  have hleftBounded :=
    (mem_centralPositiveHalfStates_iff.mp hleftPositive).1
  have hrightBounded :=
    (mem_centralPositiveHalfStates_iff.mp hrightPositive).1
  have hleftOn :=
    (labellingsAgreeOnB_true_iff
      (centralLowerFaceIds half) state
      (centralPhysicalFiniteStateAt w hw cutoff half left)).1 hleftAgree
  have hrightOn :=
    (labellingsAgreeOnB_true_iff
      (centralLowerFaceIds half) state
      (centralPhysicalFiniteStateAt w hw cutoff half right)).1 hrightAgree
  have hpair : labellingsAgreeOnB
      (centralLowerFaceIds half)
      (centralPhysicalFiniteStateAt w hw cutoff half left)
      (centralPhysicalFiniteStateAt w hw cutoff half right) = true := by
    apply (labellingsAgreeOnB_true_iff _ _ _).2
    intro id hid
    exact (hleftOn id hid).symm.trans (hrightOn id hid)
  have hstates := eq_of_labellingsAgreeOnB_of_bounded
    hleftBounded hrightBounded hpair
  exact centralPhysicalFiniteStateAt_injective_of_lt
    hleftLt hrightLt hstates

/-! ## 3. The sector recoding has the same pointwise envelope -/

/-- The exact current-cutoff sector recoding is globally bounded by the input
presentation's coefficient `l1`, including on arbitrary future labellings. -/
theorem centralPhysicalVacuumSectorMarkovCylinder_abs_le_l1
    {w : Q'} {hw : (0 : Q') ≤ w} {half : Nat}
    (cutoff : Nat)
    (presentation : CentralPhysicalVacuumSectorCylinderPresentation
      w hw half)
    (state : EdgeLabelling) :
    Q'.abs
        ((centralPhysicalVacuumSectorPresentationMarkovAtCutoff
          cutoff presentation).toLinearObservable.value state) ≤
      centralPhysicalVacuumSectorPresentationL1 presentation := by
  let indices := centralPhysicalFiniteVacuumSectorIndices
    w hw cutoff half
  let stateAt := centralPhysicalFiniteStateAt w hw cutoff half
  let outputCoefficient :=
    centralPhysicalVacuumSectorMarkovCoefficientAtCutoff cutoff presentation
  change Q'.abs
      ((centralPhysicalStateCylinderLinearCombination
        half stateAt outputCoefficient indices).value state) ≤
    centralPhysicalVacuumSectorPresentationL1 presentation
  apply stateCylinderCombination_abs_le_of_unique_match
  · unfold centralPhysicalVacuumSectorPresentationL1
    exact coefficientL1_nonnegative_local _ _
  · exact centralPhysicalFiniteVacuumSectorIndices_nodup
      w hw cutoff half
  · intro index hindex
    unfold outputCoefficient
    exact centralPhysicalLinearMarkovCutoffAction_vacuumSector_abs_le_l1
      cutoff presentation
      (centralPhysicalFiniteStateAt w hw cutoff half index)
  · intro left hleft right hright
    exact centralPhysicalFiniteStateCylinder_match_unique
      state hleft hright

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingAmplitude

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingAmplitude.centralPhysicalLinearMarkovCutoffAction_vacuumSector_abs_le_l1
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderRecodingAmplitude.centralPhysicalVacuumSectorMarkovCylinder_abs_le_l1
