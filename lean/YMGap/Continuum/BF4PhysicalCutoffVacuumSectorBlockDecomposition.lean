/-
# Old/new block decomposition of the growing physical vacuum sector

At a later representation cutoff, the canonical root component contains the
explicit image of the old component and may contain genuinely new states.
This file makes that distinction literal by filtering the later component by
membership in the embedded old image.  The full stationary mean and diagonal
quadratic split into old and new terms, while the reflected matrix quadratic
splits into old-old, old-new, new-old, and new-new blocks.

These are exact finite identities, not estimates.  In particular, the
new-state stationary mass and the two cross blocks are now named residuals
whose uniform control is still required before a strict cutoff-uniform gap can
be derived.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The embedded-old and genuinely-new target lists -/

/-- Explicit images in the later carrier of all indices in the old canonical
vacuum component. -/
def centralPhysicalFiniteEmbeddedVacuumSectorIndices
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw base half).map
    (centralPhysicalFiniteCutoffIndexMap w hw base later half)

/-- Boolean test for membership in the explicit embedded old image. -/
def centralPhysicalFiniteEmbeddedVacuumSectorB
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half index : Nat) : Bool :=
  decide (index ∈
    centralPhysicalFiniteEmbeddedVacuumSectorIndices
      w hw base later half)

/-- Target-ordered old block: later component indices which lie in the
explicit image of the old component. -/
def centralPhysicalFiniteVacuumSectorOldBlockIndices
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw later half).filter
    (centralPhysicalFiniteEmbeddedVacuumSectorB
      w hw base later half)

/-- Target-ordered new block: later component indices outside the explicit
image of the old component. -/
def centralPhysicalFiniteVacuumSectorNewBlockIndices
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) : List Nat :=
  (centralPhysicalFiniteVacuumSectorIndices w hw later half).filter
    (fun index =>
      !(centralPhysicalFiniteEmbeddedVacuumSectorB
        w hw base later half index))

/-- Every explicit old image lies in the later canonical component. -/
theorem centralPhysicalFiniteEmbeddedVacuumSectorIndices_mem_later
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hcutoff : base ≤ later)
    (hindex : index ∈
      centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw base later half) :
    index ∈ centralPhysicalFiniteVacuumSectorIndices
      w hw later half := by
  rcases List.mem_map.mp hindex with ⟨source, hsource, hsourceMap⟩
  rw [← hsourceMap]
  exact centralPhysicalFiniteVacuumSectorIndexMap_mem hcutoff hsource

/-- Under cutoff enlargement, the target-ordered old block has exactly the
same members as the explicit embedded image. -/
theorem mem_centralPhysicalFiniteVacuumSectorOldBlockIndices_iff
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hcutoff : base ≤ later) :
    index ∈ centralPhysicalFiniteVacuumSectorOldBlockIndices
        w hw base later half ↔
      index ∈ centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw base later half := by
  unfold centralPhysicalFiniteVacuumSectorOldBlockIndices
    centralPhysicalFiniteEmbeddedVacuumSectorB
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hindex
    exact ⟨
      centralPhysicalFiniteEmbeddedVacuumSectorIndices_mem_later
        hcutoff hindex,
      hindex⟩

/-- New-block membership is exactly later-component membership together with
failure to lie in the explicit old image. -/
theorem mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat} :
    index ∈ centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw base later half ↔
      index ∈ centralPhysicalFiniteVacuumSectorIndices
          w hw later half ∧
        index ∉ centralPhysicalFiniteEmbeddedVacuumSectorIndices
          w hw base later half := by
  unfold centralPhysicalFiniteVacuumSectorNewBlockIndices
    centralPhysicalFiniteEmbeddedVacuumSectorB
  rw [List.mem_filter]
  constructor
  · rintro ⟨hlater, hdecision⟩
    refine ⟨hlater, ?_⟩
    intro himage
    have htrue : decide
        (index ∈ centralPhysicalFiniteEmbeddedVacuumSectorIndices
          w hw base later half) = true :=
      decide_eq_true himage
    rw [htrue] at hdecision
    cases hdecision
  · rintro ⟨hlater, himage⟩
    refine ⟨hlater, ?_⟩
    have hfalse : decide
        (index ∈ centralPhysicalFiniteEmbeddedVacuumSectorIndices
          w hw base later half) = false :=
      decide_eq_false himage
    rw [hfalse]
    rfl

theorem centralPhysicalFiniteVacuumSectorOldBlockIndices_nodup
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      w hw base later half).Nodup := by
  unfold centralPhysicalFiniteVacuumSectorOldBlockIndices
  exact List.filter_sublist.nodup
    (centralPhysicalFiniteVacuumSectorIndices_nodup
      w hw later half)

theorem centralPhysicalFiniteVacuumSectorNewBlockIndices_nodup
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) :
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      w hw base later half).Nodup := by
  unfold centralPhysicalFiniteVacuumSectorNewBlockIndices
  exact List.filter_sublist.nodup
    (centralPhysicalFiniteVacuumSectorIndices_nodup
      w hw later half)

/-! ## 2. Generic two-by-two finite quadratic decomposition -/

/-- A rectangular block of a finite joint quadratic. -/
def finiteJointBlock {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (joint : State → State → Q') : Q' :=
  listQSum
    (fun left => listQSum
      (fun right =>
        (coefficient left * coefficient right) * joint left right)
      rightStates)
    leftStates

/-- Partitioning both coordinates of a finite quadratic gives the exact four
old-old, old-new, new-old, and new-new blocks. -/
theorem finiteJointQuadratic_filter_four_blocks
    {State : Type}
    (states : List State) (test : State → Bool)
    (coefficient : State → Q') (joint : State → State → Q') :
    finiteJointQuadratic states coefficient joint ≈
      (finiteJointBlock
          (states.filter test) (states.filter test)
          coefficient joint +
        finiteJointBlock
          (states.filter test) (states.filter (fun state => !(test state)))
          coefficient joint) +
      (finiteJointBlock
          (states.filter (fun state => !(test state))) (states.filter test)
          coefficient joint +
        finiteJointBlock
          (states.filter (fun state => !(test state)))
          (states.filter (fun state => !(test state)))
          coefficient joint) := by
  let entry := fun left right =>
    (coefficient left * coefficient right) * joint left right
  let row := fun left => listQSum (entry left) states
  have houter := listQSum_filter_partition row test states
  have hold :
      listQSum row (states.filter test) ≈
        finiteJointBlock
            (states.filter test) (states.filter test)
            coefficient joint +
          finiteJointBlock
            (states.filter test)
            (states.filter (fun state => !(test state)))
            coefficient joint := by
    refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          listQSum (entry left) (states.filter test) +
            listQSum (entry left)
              (states.filter (fun state => !(test state))))
        (states.filter test)) _ ?_ ?_
    · apply listQSum_congr_on
      intro left _hleft
      exact listQSum_filter_partition (entry left) test states
    · unfold finiteJointBlock
      exact listQSum_add _ _ _
  have hnew :
      listQSum row (states.filter (fun state => !(test state))) ≈
        finiteJointBlock
            (states.filter (fun state => !(test state)))
            (states.filter test) coefficient joint +
          finiteJointBlock
            (states.filter (fun state => !(test state)))
            (states.filter (fun state => !(test state)))
            coefficient joint := by
    refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          listQSum (entry left) (states.filter test) +
            listQSum (entry left)
              (states.filter (fun state => !(test state))))
        (states.filter (fun state => !(test state)))) _ ?_ ?_
    · apply listQSum_congr_on
      intro left _hleft
      exact listQSum_filter_partition (entry left) test states
    · unfold finiteJointBlock
      exact listQSum_add _ _ _
  unfold finiteJointQuadratic
  exact Q'.eqv_trans _ _ _ houter
    (Q'.add_eqv_congr' hold hnew)

/-! ## 3. Exact physical sector forms and their residual blocks -/

def centralPhysicalFiniteVacuumSectorWeightedMean
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun index => coefficient index *
      centralPhysicalFiniteWeight w hw cutoff half index)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)

def centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun index =>
      (coefficient index * coefficient index) *
        centralPhysicalFiniteWeight w hw cutoff half index)
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)

def centralPhysicalFiniteVacuumSectorMatrixQuadratic
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') : Q' :=
  finiteJointQuadratic
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    coefficient
    (centralPhysicalFiniteKernel w hw cutoff half)

/-- The later canonical-sector weighted mean is exactly its embedded-old term
plus its new-state leakage term. -/
theorem centralPhysicalFiniteVacuumSectorWeightedMean_old_add_new
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorWeightedMean
        w hw later half coefficient ≈
      listQSum
          (fun index => coefficient index *
            centralPhysicalFiniteWeight w hw later half index)
          (centralPhysicalFiniteVacuumSectorOldBlockIndices
            w hw base later half) +
        listQSum
          (fun index => coefficient index *
            centralPhysicalFiniteWeight w hw later half index)
          (centralPhysicalFiniteVacuumSectorNewBlockIndices
            w hw base later half) := by
  unfold centralPhysicalFiniteVacuumSectorWeightedMean
    centralPhysicalFiniteVacuumSectorOldBlockIndices
    centralPhysicalFiniteVacuumSectorNewBlockIndices
  exact listQSum_filter_partition _ _ _

/-- The later canonical-sector diagonal norm is exactly its embedded-old term
plus its new-state leakage term. -/
theorem centralPhysicalFiniteVacuumSectorDiagonalQuadratic_old_add_new
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw later half coefficient ≈
      listQSum
          (fun index =>
            (coefficient index * coefficient index) *
              centralPhysicalFiniteWeight w hw later half index)
          (centralPhysicalFiniteVacuumSectorOldBlockIndices
            w hw base later half) +
        listQSum
          (fun index =>
            (coefficient index * coefficient index) *
              centralPhysicalFiniteWeight w hw later half index)
          (centralPhysicalFiniteVacuumSectorNewBlockIndices
            w hw base later half) := by
  unfold centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    centralPhysicalFiniteVacuumSectorOldBlockIndices
    centralPhysicalFiniteVacuumSectorNewBlockIndices
  exact listQSum_filter_partition _ _ _

/-- The later canonical-sector reflected quadratic is exactly the sum of its
four old/new matrix blocks. -/
theorem centralPhysicalFiniteVacuumSectorMatrixQuadratic_four_blocks
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw later half coefficient ≈
      (finiteJointBlock
          (centralPhysicalFiniteVacuumSectorOldBlockIndices
            w hw base later half)
          (centralPhysicalFiniteVacuumSectorOldBlockIndices
            w hw base later half)
          coefficient
          (centralPhysicalFiniteKernel w hw later half) +
        finiteJointBlock
          (centralPhysicalFiniteVacuumSectorOldBlockIndices
            w hw base later half)
          (centralPhysicalFiniteVacuumSectorNewBlockIndices
            w hw base later half)
          coefficient
          (centralPhysicalFiniteKernel w hw later half)) +
      (finiteJointBlock
          (centralPhysicalFiniteVacuumSectorNewBlockIndices
            w hw base later half)
          (centralPhysicalFiniteVacuumSectorOldBlockIndices
            w hw base later half)
          coefficient
          (centralPhysicalFiniteKernel w hw later half) +
        finiteJointBlock
          (centralPhysicalFiniteVacuumSectorNewBlockIndices
            w hw base later half)
          (centralPhysicalFiniteVacuumSectorNewBlockIndices
            w hw base later half)
          coefficient
          (centralPhysicalFiniteKernel w hw later half)) := by
  unfold centralPhysicalFiniteVacuumSectorMatrixQuadratic
    centralPhysicalFiniteVacuumSectorOldBlockIndices
    centralPhysicalFiniteVacuumSectorNewBlockIndices
  exact finiteJointQuadratic_filter_four_blocks _ _ _ _

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition.centralPhysicalFiniteEmbeddedVacuumSectorIndices_mem_later
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition.mem_centralPhysicalFiniteVacuumSectorOldBlockIndices_iff
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition.centralPhysicalFiniteVacuumSectorWeightedMean_old_add_new
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition.centralPhysicalFiniteVacuumSectorDiagonalQuadratic_old_add_new
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition.centralPhysicalFiniteVacuumSectorMatrixQuadratic_four_blocks
