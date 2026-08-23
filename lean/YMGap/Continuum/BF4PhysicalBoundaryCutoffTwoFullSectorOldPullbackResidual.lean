/-
# Canonical cutoff-two pullback for full-sector block residuals

An arbitrary coefficient on a later canonical vacuum sector restricts
constructively to the embedded cutoff-two component by precomposition with
the explicit cutoff index map.  The old mean, old diagonal, and old-old
matrix block are exactly the corresponding pulled cutoff-two forms.

We then center this pullback at the fixed cutoff-two root and extend it on
the cutoff-two component itself.  This gives a canonical centered core, so a
residual certificate no longer chooses an unspecified recentering map or
proves its centering.  Its remaining fields are the genuine analytic
comparisons: moving-versus-fixed old-old form, both cross blocks, the new-new
block, and the centered-core diagonal inflation.

A constructively cofinal family of these specialized residuals contracts
through the four-block and full-sector compilers to the actual completed
vacuum-sector transfer contraction.  No later-cutoff residual estimate or
cofinal family is constructed here, and no thermodynamic, continuum, or Clay
conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorBlockResidual
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorBlockResidual
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Restrict an arbitrary later coefficient to the old component -/

/-- Pull a later coefficient back along the explicit cutoff-two embedding. -/
def cutoffTwoOldCoefficientPullback
    (later : Nat) (coefficient : Nat → Q') (source : Nat) : Q' :=
  coefficient
    (centralPhysicalFiniteCutoffIndexMap
      cutoffTwoHalfCoupling (by decide) 2 later 0 source)

def cutoffTwoNewWeightedMean
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun index => coefficient index *
      centralPhysicalFiniteWeight
        cutoffTwoHalfCoupling (by decide) later 0 index)
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)

def cutoffTwoNewDiagonal
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun index =>
      (coefficient index * coefficient index) *
        centralPhysicalFiniteWeight
          cutoffTwoHalfCoupling (by decide) later 0 index)
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)

private theorem listQSum_perm_local {A : Type} (value : A → Q') :
    ∀ {left right : List A}, left.Perm right →
      listQSum value left ≈ listQSum value right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ hperm =>
      Q'.add_eqv_congr_left _ _ _ (listQSum_perm_local value hperm)
  | _, _, List.Perm.swap first second rest => by
      change value second + (value first + listQSum value rest) ≈
        value first + (value second + listQSum value rest)
      refine Q'.eqv_trans _
        ((value second + value first) + listQSum value rest) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((value first + value second) + listQSum value rest) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_comm_eqv _ _)) ?_
      exact Q'.add_assoc_eqv _ _ _
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (listQSum_perm_local value hleft)
        (listQSum_perm_local value hright)

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (map : A → B) :
    ∀ items : List A,
      listQSum value (items.map map) =
        listQSum (fun item => value (map item)) items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value map tail]

/-- The old weighted mean of an arbitrary later coefficient is exactly the
moving pulled mean of its cutoff-two restriction. -/
theorem cutoffTwoOldWeightedMean_eqv_pulled
    {later : Nat} (hcutoff : 2 ≤ later) (coefficient : Nat → Q') :
    listQSum
        (fun target => coefficient target *
          centralPhysicalFiniteWeight
            cutoffTwoHalfCoupling (by decide) later 0 target)
        (centralPhysicalFiniteVacuumSectorOldBlockIndices
          cutoffTwoHalfCoupling (by decide) 2 later 0) ≈
      centralPhysicalFinitePulledVacuumSectorWeightedMean
        cutoffTwoHalfCoupling (by decide) 2 later 0
        (cutoffTwoOldCoefficientPullback later coefficient) := by
  let targetValue := fun target => coefficient target *
    centralPhysicalFiniteWeight
      cutoffTwoHalfCoupling (by decide) later 0 target
  refine Q'.eqv_trans _
    (listQSum targetValue
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 later 0)) _ ?_ ?_
  · exact listQSum_perm_local targetValue
      (centralPhysicalFiniteVacuumSectorOldBlockIndices_perm_embedded
        hcutoff)
  · unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
    rw [listQSum_map_local]
    unfold centralPhysicalFinitePulledVacuumSectorWeightedMean
      centralPhysicalFinitePulledWeight cutoffTwoOldCoefficientPullback
    exact Q'.eqv_refl _

/-- The old diagonal of an arbitrary later coefficient is exactly the
moving pulled diagonal of its cutoff-two restriction. -/
theorem cutoffTwoOldDiagonal_eqv_pulled
    {later : Nat} (hcutoff : 2 ≤ later) (coefficient : Nat → Q') :
    listQSum
        (fun target =>
          (coefficient target * coefficient target) *
            centralPhysicalFiniteWeight
              cutoffTwoHalfCoupling (by decide) later 0 target)
        (centralPhysicalFiniteVacuumSectorOldBlockIndices
          cutoffTwoHalfCoupling (by decide) 2 later 0) ≈
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        cutoffTwoHalfCoupling (by decide) 2 later 0
        (cutoffTwoOldCoefficientPullback later coefficient) := by
  let targetValue := fun target =>
    (coefficient target * coefficient target) *
      centralPhysicalFiniteWeight
        cutoffTwoHalfCoupling (by decide) later 0 target
  refine Q'.eqv_trans _
    (listQSum targetValue
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 later 0)) _ ?_ ?_
  · exact listQSum_perm_local targetValue
      (centralPhysicalFiniteVacuumSectorOldBlockIndices_perm_embedded
        hcutoff)
  · unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
    rw [listQSum_map_local]
    unfold centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
      centralPhysicalFinitePulledWeight cutoffTwoOldCoefficientPullback
    exact Q'.eqv_refl _

private theorem finiteJointBlock_perm_local
    {State : Type}
    {leftOld leftNew rightOld rightNew : List State}
    (hleft : leftOld.Perm leftNew) (hright : rightOld.Perm rightNew)
    (coefficient : State → Q') (joint : State → State → Q') :
    finiteJointBlock leftOld rightOld coefficient joint ≈
      finiteJointBlock leftNew rightNew coefficient joint := by
  let entry := fun left right =>
    (coefficient left * coefficient right) * joint left right
  refine Q'.eqv_trans _
    (listQSum
      (fun left => listQSum (entry left) rightOld)
      leftNew) _ ?_ ?_
  · exact listQSum_perm_local _ hleft
  · apply listQSum_congr_on
    intro left _hleft
    exact listQSum_perm_local (entry left) hright

private theorem finiteJointBlock_map_eqv_local
    {Source Target : Type}
    (source : List Source) (map : Source → Target)
    (targetCoefficient : Target → Q')
    (sourceCoefficient : Source → Q')
    (targetJoint : Target → Target → Q')
    (sourceJoint : Source → Source → Q')
    (hentry : ∀ left, left ∈ source → ∀ right, right ∈ source →
      (targetCoefficient (map left) * targetCoefficient (map right)) *
          targetJoint (map left) (map right) ≈
        (sourceCoefficient left * sourceCoefficient right) *
          sourceJoint left right) :
    finiteJointBlock (source.map map) (source.map map)
        targetCoefficient targetJoint ≈
      finiteJointQuadratic source sourceCoefficient sourceJoint := by
  unfold finiteJointBlock finiteJointQuadratic
  rw [listQSum_map_local]
  apply listQSum_congr_on
  intro left hleft
  rw [listQSum_map_local]
  apply listQSum_congr_on
  intro right hright
  exact hentry left hleft right hright

/-- The old-old block of an arbitrary later coefficient is exactly the
moving pulled matrix form of its cutoff-two restriction. -/
theorem cutoffTwoOldOldBlock_eqv_pulled
    {later : Nat} (hcutoff : 2 ≤ later) (coefficient : Nat → Q') :
    cutoffTwoOldOldBlock later coefficient ≈
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        cutoffTwoHalfCoupling (by decide) 2 later 0
        (cutoffTwoOldCoefficientPullback later coefficient) := by
  have hperm :
      (centralPhysicalFiniteVacuumSectorOldBlockIndices
          cutoffTwoHalfCoupling (by decide) 2 later 0).Perm
        (centralPhysicalFiniteEmbeddedVacuumSectorIndices
          cutoffTwoHalfCoupling (by decide) 2 later 0) :=
    centralPhysicalFiniteVacuumSectorOldBlockIndices_perm_embedded
      hcutoff
  unfold cutoffTwoOldOldBlock
  refine Q'.eqv_trans _
    (finiteJointBlock
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 later 0)
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 later 0)
      coefficient
      (centralPhysicalFiniteKernel
        cutoffTwoHalfCoupling (by decide) later 0)) _ ?_ ?_
  · exact finiteJointBlock_perm_local hperm hperm _ _
  · unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
      centralPhysicalFinitePulledKernel cutoffTwoOldCoefficientPullback
    apply finiteJointBlock_map_eqv_local
    intro left _hleft right _hright
    exact Q'.eqv_refl _

/-! ## 2. Exact old/new bookkeeping for centered later vectors -/

/-- The full later mean is the pulled old mean plus the genuinely new mean. -/
theorem cutoffTwoFullSectorWeightedMean_eqv_oldPulled_add_new
    {later : Nat} (hcutoff : 2 ≤ later) (coefficient : Nat → Q') :
    cutoffTwoFullSectorWeightedMean later coefficient ≈
      centralPhysicalFinitePulledVacuumSectorWeightedMean
          cutoffTwoHalfCoupling (by decide) 2 later 0
          (cutoffTwoOldCoefficientPullback later coefficient) +
        cutoffTwoNewWeightedMean later coefficient := by
  refine Q'.eqv_trans _ _ _
    (centralPhysicalFiniteVacuumSectorWeightedMean_old_add_new
      cutoffTwoHalfCoupling (by decide) 2 later 0 coefficient) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (cutoffTwoOldWeightedMean_eqv_pulled hcutoff coefficient)

/-- For a centered later vector, the pulled-old mean is cancelled exactly by
the new-sector leakage. -/
theorem cutoffTwoOldPulled_add_newWeightedMean_eqv_zero
    {later : Nat} (hcutoff : 2 ≤ later) (coefficient : Nat → Q')
    (hcenter : cutoffTwoFullSectorWeightedMean later coefficient ≈ 0) :
    centralPhysicalFinitePulledVacuumSectorWeightedMean
          cutoffTwoHalfCoupling (by decide) 2 later 0
          (cutoffTwoOldCoefficientPullback later coefficient) +
        cutoffTwoNewWeightedMean later coefficient ≈ 0 :=
  Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (cutoffTwoFullSectorWeightedMean_eqv_oldPulled_add_new
        hcutoff coefficient))
    hcenter

/-- The full later diagonal is the pulled old diagonal plus the genuinely
new diagonal. -/
theorem cutoffTwoFullSectorDiagonal_eqv_oldPulled_add_new
    {later : Nat} (hcutoff : 2 ≤ later) (coefficient : Nat → Q') :
    cutoffTwoFullSectorDiagonal later coefficient ≈
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          cutoffTwoHalfCoupling (by decide) 2 later 0
          (cutoffTwoOldCoefficientPullback later coefficient) +
        cutoffTwoNewDiagonal later coefficient := by
  refine Q'.eqv_trans _ _ _
    (centralPhysicalFiniteVacuumSectorDiagonalQuadratic_old_add_new
      cutoffTwoHalfCoupling (by decide) 2 later 0 coefficient) ?_
  exact Q'.add_eqv_congr_right _ _ _
    (cutoffTwoOldDiagonal_eqv_pulled hcutoff coefficient)

/-! ## 3. A canonical centered cutoff-two core -/

/-- Center the old pullback against the fixed cutoff-two weights. -/
def cutoffTwoOldCoefficientHeadCentered
    (later : Nat) (coefficient : Nat → Q') : Nat → Q' :=
  centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
    cutoffTwoHalfCoupling (by decide) 2 2 0
    (cutoffTwoOldCoefficientPullback later coefficient)

/-- Extend the head-centered pullback on the cutoff-two component itself.
Using the existing explicit extension makes all full-sector form identities
available without assuming the cutoff index map is definitionally identity. -/
def cutoffTwoOldCoefficientRecentered
    (later : Nat) (coefficient : Nat → Q') : Nat → Q' :=
  centralPhysicalFiniteVacuumSectorCoefficientExtension
    cutoffTwoHalfCoupling (by decide) 2 2 0
    (cutoffTwoOldCoefficientHeadCentered later coefficient)

/-- The canonical old pullback core is exactly centered at cutoff two. -/
theorem cutoffTwoOldCoefficientRecentered_meanZero
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoFullSectorWeightedMean 2
      (cutoffTwoOldCoefficientRecentered later coefficient) ≈ 0 := by
  unfold cutoffTwoFullSectorWeightedMean
    cutoffTwoOldCoefficientRecentered
    cutoffTwoOldCoefficientHeadCentered
  exact centralPhysicalFiniteVacuumSectorHeadCenteredExtension_meanZero
    (base := 2) (later := 2) (half := 0) (Nat.le_refl 2)
    (cutoffTwoOldCoefficientPullback later coefficient)

/-- The canonical core diagonal is exactly its fixed pulled diagonal. -/
theorem cutoffTwoOldCoefficientRecentered_diagonal_eqv_pulled
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoFullSectorDiagonal 2
        (cutoffTwoOldCoefficientRecentered later coefficient) ≈
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        cutoffTwoHalfCoupling (by decide) 2 2 0
        (cutoffTwoOldCoefficientHeadCentered later coefficient) := by
  unfold cutoffTwoFullSectorDiagonal
    cutoffTwoOldCoefficientRecentered
    cutoffTwoOldCoefficientHeadCentered
  exact centralPhysicalFiniteVacuumSectorHeadCenteredExtensionDiagonal_eqv_pulled
    (base := 2) (later := 2) (half := 0) (Nat.le_refl 2)
    (cutoffTwoOldCoefficientPullback later coefficient)

/-- The canonical core matrix form is exactly its fixed pulled matrix form. -/
theorem cutoffTwoOldCoefficientRecentered_matrix_eqv_pulled
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoFullSectorMatrix 2
        (cutoffTwoOldCoefficientRecentered later coefficient) ≈
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        cutoffTwoHalfCoupling (by decide) 2 2 0
        (cutoffTwoOldCoefficientHeadCentered later coefficient) := by
  unfold cutoffTwoFullSectorMatrix
    cutoffTwoOldCoefficientRecentered
    cutoffTwoOldCoefficientHeadCentered
  exact centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
    (base := 2) (later := 2) (half := 0) (Nat.le_refl 2)
    (cutoffTwoOldCoefficientPullback later coefficient)

/-! ## 4. Residual certificates with the recentering already constructed -/

/-- Four analytic block estimates after the structural pullback and
recentring have been fixed canonically. -/
structure CutoffTwoFullSectorOldPullbackResidualAt
    (later : Nat)
    (oldOldError oldNewError newOldError newNewError diagonalFactor : Q') :
    Type 1 where
  later_ge : 2 ≤ later
  old_old_pulled_comparison : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      Q'.abs
          (centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            cutoffTwoHalfCoupling (by decide) 2 later 0
            (cutoffTwoOldCoefficientPullback later coefficient)) ≤
        Q'.abs
            (centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
              cutoffTwoHalfCoupling (by decide) 2 2 0
              (cutoffTwoOldCoefficientHeadCentered later coefficient)) +
          oldOldError * cutoffTwoFullSectorDiagonal later coefficient
  old_new_bound : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      Q'.abs (cutoffTwoOldNewBlock later coefficient) ≤
        oldNewError * cutoffTwoFullSectorDiagonal later coefficient
  new_old_bound : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      Q'.abs (cutoffTwoNewOldBlock later coefficient) ≤
        newOldError * cutoffTwoFullSectorDiagonal later coefficient
  new_new_bound : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      Q'.abs (cutoffTwoNewNewBlock later coefficient) ≤
        newNewError * cutoffTwoFullSectorDiagonal later coefficient
  pulled_diagonal_comparison : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          cutoffTwoHalfCoupling (by decide) 2 2 0
          (cutoffTwoOldCoefficientHeadCentered later coefficient) ≤
        diagonalFactor * cutoffTwoFullSectorDiagonal later coefficient

namespace CutoffTwoFullSectorOldPullbackResidualAt

/-- Insert the canonical pullback/recentering and exact old-block identities
into the generic four-block residual compiler. -/
def toFullSectorBlockResidualAt
    {later : Nat}
    {oldOldError oldNewError newOldError newNewError diagonalFactor : Q'}
    (residual : CutoffTwoFullSectorOldPullbackResidualAt later
      oldOldError oldNewError newOldError newNewError diagonalFactor) :
    CutoffTwoFullSectorBlockResidualAt later
      oldOldError oldNewError newOldError newNewError diagonalFactor where
  later_ge := residual.later_ge
  recentered := cutoffTwoOldCoefficientRecentered later
  recentered_centered := by
    intro coefficient _hcenter
    exact cutoffTwoOldCoefficientRecentered_meanZero later coefficient
  old_old_comparison := by
    intro coefficient hcenter
    have hold := cutoffTwoOldOldBlock_eqv_pulled
      residual.later_ge coefficient
    have hcore :=
      cutoffTwoOldCoefficientRecentered_matrix_eqv_pulled
        later coefficient
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hold)) ?_
    refine Q'.le_trans' _ _ _
      (residual.old_old_pulled_comparison coefficient hcenter) ?_
    exact Q'.le_of_eqv
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_symm (Q'.abs_eqv_congr hcore)))
  old_new_bound := residual.old_new_bound
  new_old_bound := residual.new_old_bound
  new_new_bound := residual.new_new_bound
  diagonal_comparison := by
    intro coefficient hcenter
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (cutoffTwoOldCoefficientRecentered_diagonal_eqv_pulled
          later coefficient))
      (residual.pulled_diagonal_comparison coefficient hcenter)

end CutoffTwoFullSectorOldPullbackResidualAt

/-! ## 5. Cofinal canonical-pullback residual control -/

structure CutoffTwoCofinalFullSectorOldPullbackResidual
    (oldOldError oldNewError newOldError newNewError diagonalFactor : Q') :
    Type 1 where
  old_old_error_nonnegative : (0 : Q') ≤ oldOldError
  old_new_error_nonnegative : (0 : Q') ≤ oldNewError
  new_old_error_nonnegative : (0 : Q') ≤ newOldError
  new_new_error_nonnegative : (0 : Q') ≤ newNewError
  diagonal_factor_nonnegative : (0 : Q') ≤ diagonalFactor
  full_rate_lt_one :
    cutoffTwoFullSectorRate
        (cutoffTwoBlockMatrixError
          oldOldError oldNewError newOldError newNewError)
        diagonalFactor < (1 : Q')
  anchor : Nat → Nat
  anchor_ge : ∀ request, max 2 request ≤ anchor request
  residual : ∀ request,
    CutoffTwoFullSectorOldPullbackResidualAt (anchor request)
      oldOldError oldNewError newOldError newNewError diagonalFactor

namespace CutoffTwoCofinalFullSectorOldPullbackResidual

def toCofinalFullSectorBlockResidual
    {oldOldError oldNewError newOldError newNewError diagonalFactor : Q'}
    (family : CutoffTwoCofinalFullSectorOldPullbackResidual
      oldOldError oldNewError newOldError newNewError diagonalFactor) :
    CutoffTwoCofinalFullSectorBlockResidual
      oldOldError oldNewError newOldError newNewError diagonalFactor where
  old_old_error_nonnegative := family.old_old_error_nonnegative
  old_new_error_nonnegative := family.old_new_error_nonnegative
  new_old_error_nonnegative := family.new_old_error_nonnegative
  new_new_error_nonnegative := family.new_new_error_nonnegative
  diagonal_factor_nonnegative := family.diagonal_factor_nonnegative
  full_rate_lt_one := family.full_rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  residual := by
    intro request
    exact (family.residual request).toFullSectorBlockResidualAt

def toCompletedStrictContractionData
    {oldOldError oldNewError newOldError newNewError diagonalFactor : Q'}
    (family : CutoffTwoCofinalFullSectorOldPullbackResidual
      oldOldError oldNewError newOldError newNewError diagonalFactor) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalFullSectorBlockResidual.toCompletedStrictContractionData

end CutoffTwoCofinalFullSectorOldPullbackResidual

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual.cutoffTwoOldWeightedMean_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual.cutoffTwoOldDiagonal_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual.cutoffTwoOldOldBlock_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual.cutoffTwoOldPulled_add_newWeightedMean_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual.cutoffTwoFullSectorDiagonal_eqv_oldPulled_add_new
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual.cutoffTwoOldCoefficientRecentered_meanZero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual.cutoffTwoOldCoefficientRecentered_diagonal_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual.cutoffTwoOldCoefficientRecentered_matrix_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual.CutoffTwoFullSectorOldPullbackResidualAt.toFullSectorBlockResidualAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual.CutoffTwoCofinalFullSectorOldPullbackResidual.toCofinalFullSectorBlockResidual
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual.CutoffTwoCofinalFullSectorOldPullbackResidual.toCompletedStrictContractionData
