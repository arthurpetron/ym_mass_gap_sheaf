/-
# Generic embedded-boundary growth of the physical vacuum sector

For arbitrary `base <= later`, every state in the later new block belongs to
the later rooted vacuum component but lies outside the embedded base vacuum
component.  Constructive recursion over its root path therefore produces a
literal support edge leaving the embedded image.

Consequently, the finite Boolean condition saying that every embedded-to-new
candidate edge is absent is equivalent to the entire new block being empty.
Thus embedded-boundary closure is a no-growth condition, not merely a
no-component-merger condition.  A moving-base construction that allows new
physical states must pay boundary growth quantitatively.

No empty-new-block result at a larger cutoff, cofinal stability, completed
contraction, thermodynamic/continuum construction, or Clay mass gap is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelComponentMergerResidualBudget

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbeddedBoundaryGrowth

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.FiniteWeightedCartesianInjection

/-! ## 1. Generic first exit from a finite Type-level chain -/

private structure ChainListBoundaryExit
    (adjacent : Nat → Nat → Bool)
    (support old : List Nat) : Type where
  source : Nat
  target : Nat
  source_mem_old : source ∈ old
  target_not_mem_old : target ∉ old
  target_mem_support : target ∈ support
  edge : adjacent source target = true

private def chainListBoundaryExit
    (adjacent : Nat → Nat → Bool)
    (support old : List Nat) :
    {start finish : Nat} →
      ChainIn adjacent support start finish →
      start ∈ old → finish ∉ old →
      ChainListBoundaryExit adjacent support old
  | start, _, ChainIn.refl _, hstart, hfinish =>
      False.elim (hfinish hstart)
  | start, _, ChainIn.step (b := next) hedge hnext rest,
      hstart, hfinish => by
      by_cases hnextOld : next ∈ old
      · exact chainListBoundaryExit adjacent support old
          rest hnextOld hfinish
      · exact
          { source := start
            target := next
            source_mem_old := hstart
            target_not_mem_old := hnextOld
            target_mem_support := hnext
            edge := hedge }

/-! ## 2. Every generic new state forces an embedded boundary edge -/

structure CentralPhysicalEmbeddedVacuumBoundaryExit
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Type where
  source : Nat
  target : Nat
  source_mem_embedded : source ∈
    centralPhysicalFiniteEmbeddedVacuumSectorIndices
      w hw base later half
  target_mem_new : target ∈
    centralPhysicalFiniteVacuumSectorNewBlockIndices
      w hw base later half
  source_mem_later_sector : source ∈
    centralPhysicalFiniteVacuumSectorIndices w hw later half
  target_mem_later_sector : target ∈
    centralPhysicalFiniteVacuumSectorIndices w hw later half
  edge : centralPhysicalFiniteSupportAdjacentB
    w hw later half source target = true

def centralPhysicalFiniteNewStateBoundaryExit
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hcutoff : base ≤ later)
    (hnew : index ∈
      centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw base later half) :
    CentralPhysicalEmbeddedVacuumBoundaryExit
      w hw base later half := by
  let old := centralPhysicalFiniteEmbeddedVacuumSectorIndices
    w hw base later half
  let support := centralPhysicalFiniteVacuumSectorIndices
    w hw later half
  let adjacent := centralPhysicalFiniteSupportAdjacentB
    w hw later half
  have hnewParts :=
    (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff).mp hnew
  have hrootOld : 0 ∈ old := by
    unfold old centralPhysicalFiniteEmbeddedVacuumSectorIndices
    apply List.mem_map.mpr
    refine ⟨0,
      zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w hw base half,
      ?_⟩
    exact centralPhysicalFiniteCutoffIndexMap_zero
      w hw base later half
  have hpath : ChainIn adjacent support 0 index := by
    exact rootComponent_connected
      adjacent
      (centralPhysicalFiniteSupportAdjacentB_symmetric
        w hw later half)
      (zero_mem_centralPhysicalFiniteIndexCarrier
        w hw later half)
      0 index
      (zero_mem_centralPhysicalFiniteVacuumSectorIndices
        w hw later half)
      hnewParts.1
  let exit := chainListBoundaryExit
    adjacent support old hpath hrootOld hnewParts.2
  have htargetNew : exit.target ∈
      centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw base later half :=
    (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff).mpr
      ⟨exit.target_mem_support, exit.target_not_mem_old⟩
  exact
    { source := exit.source
      target := exit.target
      source_mem_embedded := exit.source_mem_old
      target_mem_new := htargetNew
      source_mem_later_sector :=
        centralPhysicalFiniteEmbeddedVacuumSectorIndices_mem_later
          hcutoff exit.source_mem_old
      target_mem_later_sector := exit.target_mem_support
      edge := exit.edge }

/-! ## 3. Executable closure is exactly absence of carrier growth -/

def centralPhysicalEmbeddedVacuumBoundaryClosedCheck
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : Bool :=
  (cartesian
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw base later half)
      (centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw base later half)).all
    (fun pair =>
      !(centralPhysicalFiniteSupportAdjacentB
        w hw later half pair.1 pair.2))

private theorem bool_eq_false_of_not_eq_true
    (value : Bool) (hvalue : (!value) = true) : value = false := by
  cases value <;> simp_all

theorem centralPhysicalEmbeddedVacuumBoundaryClosedCheck_sound
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat)
    (hcheck : centralPhysicalEmbeddedVacuumBoundaryClosedCheck
      w hw base later half = true) :
    ∀ source,
      source ∈ centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw base later half →
      ∀ target,
        target ∈ centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half →
        centralPhysicalFiniteSupportAdjacentB
          w hw later half source target = false := by
  unfold centralPhysicalEmbeddedVacuumBoundaryClosedCheck at hcheck
  intro source hsource target htarget
  have hpair : (source, target) ∈
      cartesian
        (centralPhysicalFiniteEmbeddedVacuumSectorIndices
          w hw base later half)
        (centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half) :=
    (mem_cartesian_iff _ _ (source, target)).mpr ⟨hsource, htarget⟩
  exact bool_eq_false_of_not_eq_true _
    (List.all_eq_true.mp hcheck (source, target) hpair)

theorem centralPhysicalEmbeddedVacuumBoundaryClosedCheck_complete
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat)
    (hclosed :
      ∀ source,
        source ∈ centralPhysicalFiniteEmbeddedVacuumSectorIndices
          w hw base later half →
        ∀ target,
          target ∈ centralPhysicalFiniteVacuumSectorNewBlockIndices
            w hw base later half →
          centralPhysicalFiniteSupportAdjacentB
            w hw later half source target = false) :
    centralPhysicalEmbeddedVacuumBoundaryClosedCheck
      w hw base later half = true := by
  unfold centralPhysicalEmbeddedVacuumBoundaryClosedCheck
  apply List.all_eq_true.mpr
  intro pair hpair
  have hparts :=
    (mem_cartesian_iff
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw base later half)
      (centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw base later half) pair).mp hpair
  simp only [hclosed pair.1 hparts.1 pair.2 hparts.2, Bool.not_false]

theorem centralPhysicalEmbeddedVacuumBoundaryClosedCheck_true_iff_new_empty
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later) :
    centralPhysicalEmbeddedVacuumBoundaryClosedCheck
        w hw base later half = true ↔
      centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw base later half = [] := by
  constructor
  · intro hcheck
    cases hstates : centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw base later half with
    | nil => rfl
    | cons head tail =>
        have hhead : head ∈
            centralPhysicalFiniteVacuumSectorNewBlockIndices
              w hw base later half := by
          rw [hstates]
          exact List.mem_cons_self
        let boundary :=
          centralPhysicalFiniteNewStateBoundaryExit hcutoff hhead
        have hedgeFalse :=
          centralPhysicalEmbeddedVacuumBoundaryClosedCheck_sound
            w hw base later half hcheck
            boundary.source boundary.source_mem_embedded
            boundary.target boundary.target_mem_new
        rw [boundary.edge] at hedgeFalse
        exact False.elim
          ((by decide : (true : Bool) ≠ false) hedgeFalse)
  · intro hempty
    apply centralPhysicalEmbeddedVacuumBoundaryClosedCheck_complete
    intro _ _ target htarget
    rw [hempty] at htarget
    exact False.elim (List.not_mem_nil htarget)

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbeddedBoundaryGrowth

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbeddedBoundaryGrowth.centralPhysicalFiniteNewStateBoundaryExit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbeddedBoundaryGrowth.centralPhysicalEmbeddedVacuumBoundaryClosedCheck_sound
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbeddedBoundaryGrowth.centralPhysicalEmbeddedVacuumBoundaryClosedCheck_complete
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbeddedBoundaryGrowth.centralPhysicalEmbeddedVacuumBoundaryClosedCheck_true_iff_new_empty
