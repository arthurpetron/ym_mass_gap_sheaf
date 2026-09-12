/-
# Explicit marginal-sector preimages of every signed cube vector

Choose the computed common admission cutoff 1 + sum of the spins in the
finite list, locate each literal state by the existing faithful finite code,
and sum its signed coefficients at that index. Finite Fubini proves equality
of the observable values on EVERY state, including repeated terms and
negative coefficients. No quotient representative is selected.

The resulting marginal-sector vector maps to the original reflected cube
vector exactly. This supplies a concrete dense source for the existing
conditional transfer; it is not a globally inverse marginal/reflected map,
nor an extension of that transfer, stationary sector vacuum or strict gap.
-/

import YMGap.Continuum.BF4PhysicalCubeSectorComparison
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding

namespace YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCubeGNSData
open YMGap.Continuum.BF4PhysicalCubeCompletion
open YMGap.Continuum.BF4PhysicalCubeObservableRealization
open YMGap.Continuum.BF4PhysicalCubeCompletedReflectedRealization
open YMGap.Continuum.BF4PhysicalCubeReflectedCompletion
open YMGap.Continuum.BF4PhysicalCubeSectorComparison
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedModule
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletion
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalVacuumSectorCubeClassification
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv
local notation "M" => centralPhysicalVacuumSectorCylinderSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0
local notation "G" => centralPhysicalCutoffLinearSquaredSeminorm
  (w := anchorCoupling) (by decide) (by decide) 0

/-- An explicit common admission cutoff, including the empty span. -/
def spanBase (terms : CubeSpan) : Nat := termSpinBound terms + 1

def spanIndex (terms : CubeSpan) (state : CubeSectorState) : Nat :=
  centralPhysicalFiniteIndexOfState anchorCoupling (by decide) (spanBase terms) 0 state.val

theorem spanBase_admits (terms : CubeSpan) {term : CubeSectorState × Q'}
    (ht : term ∈ terms) : stateCutoff term.1 ≤ spanBase terms := by
  have h := termSpinBound_member terms ht
  unfold stateCutoff spanBase
  omega

theorem spanIndex_state (terms : CubeSpan) {term : CubeSectorState × Q'}
    (ht : term ∈ terms) :
    centralPhysicalFiniteStateAt anchorCoupling (by decide) (spanBase terms) 0
      (spanIndex terms term.1) = term.1.val :=
  centralPhysicalFiniteStateAt_indexOfState_eq
    (state_mem_positive (w := anchorCoupling) (by decide) term.1 _ (spanBase_admits terms ht))

/-- The computed index belongs to the SAME canonical physical component. -/
theorem spanIndex_mem (terms : CubeSpan) {term : CubeSectorState × Q'}
    (ht : term ∈ terms) :
    spanIndex terms term.1 ∈
      centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide) (spanBase terms) 0 := by
  have hs := vacuumSector_cutoff_mono (w := anchorCoupling) (by decide)
    (stateCutoff term.1) (spanBase terms) (by unfold stateCutoff; omega)
    (spanBase_admits terms ht) (state_mem_finite_sector (w := anchorCoupling) (by decide) term.1)
  rcases List.mem_map.mp hs with ⟨i, hi, he⟩
  have hlt := centralPhysicalFiniteIndexOfState_lt
    (state_mem_positive (w := anchorCoupling) (by decide) term.1 _ (spanBase_admits terms ht))
  have heq := centralPhysicalFiniteStateAt_injective_of_lt hlt
    (centralPhysicalFiniteVacuumSectorIndex_lt anchorCoupling (by decide) (spanBase terms) 0 hi)
    ((spanIndex_state terms ht).trans he.symm)
  change spanIndex terms term.1 = i at heq
  exact heq.symm ▸ hi

/-- Repeated terms are aggregated; signed coefficients are unrestricted. -/
def spanPresentation (terms : CubeSpan) : SectorPresentation where
  base := spanBase terms
  coefficient i := listQSum (fun term => if i = spanIndex terms term.1 then term.2 else 0) terms

private theorem sum_single (f : Nat → Q') (chosen : Nat) (items : List Nat)
    (hn : items.Nodup) (ht : chosen ∈ items) :
    listQSum (fun i => if i = chosen then f i else 0) items ≈ f chosen := by
  induction items with
  | nil => exact False.elim (List.not_mem_nil ht)
  | cons i rest ih =>
    have hn' := List.nodup_cons.mp hn
    by_cases he : i = chosen
    · subst i
      simp only [listQSum, if_true]
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ ?_)
        (Q'.eqv_of_eq (Q'.add_zero' _))
      refine Q'.eqv_trans _ (listQSum (fun _ => (0 : Q')) rest) _ ?_ (listQSum_zero rest)
      apply listQSum_congr_on
      intro j hj
      have hjne : j ≠ chosen := fun h => hn'.1 (h ▸ hj)
      rw [if_neg hjne]
      exact Q'.eqv_refl _
    · have ht' : chosen ∈ rest := by
        rcases List.mem_cons.mp ht with h | h
        · exact False.elim (he h.symm)
        · exact h
      simp only [listQSum, if_neg he]
      exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) (ih hn'.2 ht')

private theorem combination_value (stateAt : Nat → EdgeLabelling) (coefficient : Nat → Q')
    (state : EdgeLabelling) : ∀ indices : List Nat,
    (centralPhysicalStateCylinderLinearCombination 0 stateAt coefficient indices).value state =
      listQSum (fun i => coefficient i *
        (centralPhysicalStateCylinderUnitObservable 0 (stateAt i)).value state) indices
  | [] => rfl
  | i :: rest => by
    simp only [centralPhysicalStateCylinderLinearCombination, CentralPhysicalLinearObservable.value,
      listQSum, combination_value stateAt coefficient state rest]

private theorem observable_value (terms : CubeSpan) (state : EdgeLabelling) :
    (cubeObservable terms).value state = listQSum (fun term => term.2 *
      (centralPhysicalStateCylinderUnitObservable 0 term.1.val).value state) terms := by
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [cubeObservable, CentralPhysicalLinearObservable.value, listQSum, ih]

private theorem sum_aggregate {A : Type} (terms : List A) (index : A → Nat)
    (coefficient : A → Q') (indicator : Nat → Q') (indices : List Nat)
    (hn : indices.Nodup) (hm : ∀ term, term ∈ terms → index term ∈ indices) :
    listQSum (fun i => listQSum (fun term => if i = index term then coefficient term else 0) terms *
      indicator i) indices ≈ listQSum (fun term => coefficient term * indicator (index term)) terms := by
  refine Q'.eqv_trans _
    (listQSum (fun i => listQSum (fun term => indicator i *
      (if i = index term then coefficient term else 0)) terms) indices) _ ?_ ?_
  · apply listQSum_congr
    intro i
    exact Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _) (Q'.eqv_symm (listQSum_mul_left _ _ terms))
  · refine Q'.eqv_trans _ _ _ (listQSum_swap _ terms indices) ?_
    apply listQSum_congr_on
    intro term ht
    refine Q'.eqv_trans _
      (listQSum (fun i => if i = index term then indicator i * coefficient term else 0) indices) _ ?_ ?_
    · apply listQSum_congr
      intro i
      by_cases hi : i = index term
      · rw [if_pos hi, if_pos hi]; exact Q'.eqv_refl _
      · rw [if_neg hi, if_neg hi]; exact Q'.mul_zero_eqv _
    · exact Q'.eqv_trans _ _ _ (sum_single (fun i => indicator i * coefficient term)
        (index term) indices hn (hm term ht)) (Q'.mul_comm_eqv _ _)

private theorem combination_aggregate (terms : CubeSpan) (index : CubeSectorState → Nat)
    (stateAt : Nat → EdgeLabelling) (indices : List Nat) (hn : indices.Nodup)
    (hm : ∀ term, term ∈ terms → index term.1 ∈ indices)
    (hs : ∀ term, term ∈ terms → stateAt (index term.1) = term.1.val) :
    CentralPhysicalLinearObservable.Equivalent
      (centralPhysicalStateCylinderLinearCombination 0 stateAt
        (fun i => listQSum (fun term => if i = index term.1 then term.2 else 0) terms) indices)
      (cubeObservable terms) := by
  intro state
  let indicator := fun i => (centralPhysicalStateCylinderUnitObservable 0
    (stateAt i)).value state
  rw [combination_value, observable_value]
  refine Q'.eqv_trans _ _ _ (sum_aggregate terms (fun term => index term.1)
    (fun term => term.2) indicator indices hn hm) ?_
  apply listQSum_congr_on
  intro term ht
  dsimp [indicator]
  rw [hs term ht]
  exact Q'.eqv_refl _

/-- Global pointwise equality, not just equality on a finite test ensemble. -/
theorem spanPresentation_observable (terms : CubeSpan) :
    CentralPhysicalLinearObservable.Equivalent
      (spanPresentation terms).toLinearObservable (cubeObservable terms) :=
  combination_aggregate terms (spanIndex terms)
    (centralPhysicalFiniteStateAt anchorCoupling (by decide) (spanBase terms) 0)
    (centralPhysicalFiniteVacuumSectorIndices anchorCoupling (by decide) (spanBase terms) 0)
    (centralPhysicalFiniteVacuumSectorIndices_nodup anchorCoupling (by decide) (spanBase terms) 0)
    (fun _ ht => spanIndex_mem terms ht) (fun _ ht => spanIndex_state terms ht)

/-- The preimage also realizes the same vector in the original marginal space. -/
theorem spanPresentation_global (terms : CubeSpan) :
    centralPhysicalVacuumSectorCylinderCompletionToGlobal ((M).embedRep (spanPresentation terms)) =
      cubeToCompleted (w := anchorCoupling) (by decide) (by decide) terms :=
  (G).embedRep_eq_of_null (physicalLinearDistSq_equiv_czero_of_equivalent
    (w := anchorCoupling) (by decide) (by decide) 0 (spanPresentation_observable terms))

/-- Every finite cube vector has this explicit marginal-sector preimage. -/
theorem spanPresentation_reflected (terms : CubeSpan) :
    sectorToReflected ((M).embedRep (spanPresentation terms)) = cubeReflectedEmbed terms := by
  rw [sectorToReflected_embed]
  apply cubeReflectedSeminorm.embedRep_eq_of_null
  apply cubeObservable_null_of_equivalent
  rw [presentationToCube_observable]
  exact spanPresentation_observable terms

theorem spanPresentation_raw (terms : CubeSpan) :
    sectorToRaw ((M).embedRep (spanPresentation terms)) =
      embedSpan anchorCoupling (by decide) terms := by
  unfold sectorToRaw
  rw [spanPresentation_reflected, reflectedToRaw_embed]

end YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage

#print axioms YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage.spanBase
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage.spanIndex
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage.spanBase_admits
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage.spanIndex_state
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage.spanIndex_mem
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage.spanPresentation
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage.spanPresentation_observable
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage.spanPresentation_global
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage.spanPresentation_reflected
#print axioms YMGap.Continuum.BF4PhysicalCubeSectorDensePreimage.spanPresentation_raw
