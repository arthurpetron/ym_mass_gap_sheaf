/-
# Every fixed pulled BF4 energy embeds in the later vacuum-sector deficit

For arbitrary fixed base cutoff and half-extent, the pulled Dirichlet energy
on the old vacuum component is the old-old sub-sum of the Dirichlet energy of
its zero extension to the later canonical vacuum component.  The canonical
index embedding is injective, source summands agree exactly with their images,
and all omitted target summands are nonnegative.

The exact stationary symmetric Dirichlet identity on the later component then
bounds the pulled energy by twice the diagonal-minus-transfer deficit of the
moving head-centered coefficient.  No edge floor or uniform rate is assumed.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathEnergy
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledDirichletEmbedding

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
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

/-! ## 1. The arbitrary old-old Dirichlet sub-sum -/

theorem fixedBasePulledDirichlet_le_fullExtensionDirichlet
    {w : Q'} {hw : (0 : Q') ≤ w}
    (base later half : Nat) (hlater : base ≤ later)
    (coefficient : Nat → Q') :
    finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw base half)
        coefficient
        (centralPhysicalFinitePulledKernel w hw base later half) ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw later half)
        (centralPhysicalFiniteVacuumSectorCoefficientExtension
          w hw base later half coefficient)
        (centralPhysicalFiniteKernel w hw later half) := by
  let sourceStates :=
    centralPhysicalFiniteVacuumSectorIndices w hw base half
  let targetStates :=
    centralPhysicalFiniteVacuumSectorIndices w hw later half
  let indexMap := centralPhysicalFiniteCutoffIndexMap
    w hw base later half
  let extension := centralPhysicalFiniteVacuumSectorCoefficientExtension
    w hw base later half coefficient
  let sourceTerm : Nat × Nat → Q' := fun pair =>
    centralPhysicalFinitePulledKernel
        w hw base later half pair.1 pair.2 *
      ((coefficient pair.1 + -coefficient pair.2) *
        (coefficient pair.1 + -coefficient pair.2))
  let targetTerm : Nat × Nat → Q' := fun pair =>
    centralPhysicalFiniteKernel w hw later half pair.1 pair.2 *
      ((extension pair.1 + -extension pair.2) *
        (extension pair.1 + -extension pair.2))
  let pairMap : Nat × Nat → Nat × Nat := fun pair =>
    (indexMap pair.1, indexMap pair.2)
  have hsourceNodup : sourceStates.Nodup :=
    centralPhysicalFiniteVacuumSectorIndices_nodup w hw base half
  have htargetNodup : targetStates.Nodup :=
    centralPhysicalFiniteVacuumSectorIndices_nodup w hw later half
  have hsum :
      listQSum sourceTerm (cartesian sourceStates sourceStates) ≤
        listQSum targetTerm (cartesian targetStates targetStates) := by
    apply listQSum_le_of_injective
      (cartesian sourceStates sourceStates)
      (cartesian targetStates targetStates)
      sourceTerm targetTerm pairMap
    · exact cartesian_nodup sourceStates sourceStates
        hsourceNodup hsourceNodup
    · intro pair hpair
      have hparts := (mem_cartesian_iff
        sourceStates sourceStates pair).mp hpair
      apply (mem_cartesian_iff targetStates targetStates (pairMap pair)).mpr
      exact
        ⟨centralPhysicalFiniteVacuumSectorIndexMap_mem hlater hparts.1,
          centralPhysicalFiniteVacuumSectorIndexMap_mem hlater hparts.2⟩
    · intro first hfirst second hsecond heq
      have hfirstParts := (mem_cartesian_iff
        sourceStates sourceStates first).mp hfirst
      have hsecondParts := (mem_cartesian_iff
        sourceStates sourceStates second).mp hsecond
      have hleftMap : indexMap first.1 = indexMap second.1 :=
        congrArg Prod.fst heq
      have hrightMap : indexMap first.2 = indexMap second.2 :=
        congrArg Prod.snd heq
      have hleft : first.1 = second.1 :=
        centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector
          hlater hfirstParts.1 hsecondParts.1 hleftMap
      have hright : first.2 = second.2 :=
        centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector
          hlater hfirstParts.2 hsecondParts.2 hrightMap
      exact Prod.ext hleft hright
    · intro pair hpair
      have hparts := (mem_cartesian_iff
        sourceStates sourceStates pair).mp hpair
      have hleftCoefficient :
          extension (indexMap pair.1) ≈ coefficient pair.1 :=
        centralPhysicalFiniteVacuumSectorCoefficientExtension_on_map
          hlater hparts.1 coefficient
      have hrightCoefficient :
          extension (indexMap pair.2) ≈ coefficient pair.2 :=
        centralPhysicalFiniteVacuumSectorCoefficientExtension_on_map
          hlater hparts.2 coefficient
      have hdifference :
          extension (indexMap pair.1) + -extension (indexMap pair.2) ≈
            coefficient pair.1 + -coefficient pair.2 := by
        refine Q'.eqv_trans _
          (coefficient pair.1 + -extension (indexMap pair.2)) _ ?_ ?_
        · exact Q'.add_eqv_congr_right _ _ _ hleftCoefficient
        · exact Q'.add_eqv_congr_left _ _ _
            (Q'.neg_eqv_congr _ _ hrightCoefficient)
      have htargetSource : targetTerm (pairMap pair) ≈ sourceTerm pair := by
        unfold targetTerm sourceTerm pairMap indexMap
          centralPhysicalFinitePulledKernel
        exact Q'.mul_eqv_congr_left _ _ _
          (square_eqv_congr hdifference)
      exact Q'.ge_of_eqv htargetSource
    · intro pair hpair
      have _hparts := (mem_cartesian_iff
        targetStates targetStates pair).mp hpair
      unfold targetTerm
      exact Q'.mul_nonneg _ _
        (by
          unfold centralPhysicalFiniteKernel
          exact centralNormalizedPhysicalReflectedKernel_nonnegative
            hw later half _ _)
        (square_nonnegative _)
  have hsourceCartesian :
      listQSum sourceTerm (cartesian sourceStates sourceStates) ≈
        finiteJointDirichletEnergy sourceStates coefficient
          (centralPhysicalFinitePulledKernel w hw base later half) := by
    unfold finiteJointDirichletEnergy sourceTerm
    exact listQSum_cartesian_eq_nested_local _ _ _
  have htargetCartesian :
      listQSum targetTerm (cartesian targetStates targetStates) ≈
        finiteJointDirichletEnergy targetStates extension
          (centralPhysicalFiniteKernel w hw later half) := by
    unfold finiteJointDirichletEnergy targetTerm
    exact listQSum_cartesian_eq_nested_local _ _ _
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hsourceCartesian)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv htargetCartesian))

/-! ## 2. Exact contraction to the moving pulled deficit -/

theorem fixedBasePulledDirichlet_le_twice_moving_deficit
    {w : Q'} {hw : (0 : Q') ≤ w}
    (base later half : Nat) (hlater : base ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw base half)
        moving
        (centralPhysicalFinitePulledKernel w hw base later half) ≤
      (centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving +
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving) +
        -(centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving +
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving) := by
  let moving :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      w hw base later half coefficient
  let extension := centralPhysicalFiniteVacuumSectorCoefficientExtension
    w hw base later half moving
  have hsubsum := fixedBasePulledDirichlet_le_fullExtensionDirichlet
    (w := w) (hw := hw) base later half hlater moving
  have hfull :=
    centralPhysicalFiniteVacuumSectorDirichlet_eqv_twice_deficit
      w hw later half extension
  have hmatrix :=
    centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
      (w := w) (hw := hw) (base := base) (later := later)
      (half := half) hlater coefficient
  have hdiagonal :=
    centralPhysicalFiniteVacuumSectorHeadCenteredExtensionDiagonal_eqv_pulled
      (w := w) (hw := hw) (base := base) (later := later)
      (half := half) hlater coefficient
  have hdeficit :
      (centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half extension +
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw later half extension) +
        -(centralPhysicalFiniteVacuumSectorMatrixQuadratic
            w hw later half extension +
          centralPhysicalFiniteVacuumSectorMatrixQuadratic
            w hw later half extension) ≈
      (centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving +
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving) +
        -(centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving +
          centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving) := by
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hdiagonal hdiagonal)
      (Q'.neg_eqv_congr _ _
        (Q'.add_eqv_congr' hmatrix hmatrix))
  exact Q'.le_trans' _ _ _ hsubsum
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hfull hdeficit))

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledDirichletEmbedding

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledDirichletEmbedding.fixedBasePulledDirichlet_le_fullExtensionDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledDirichletEmbedding.fixedBasePulledDirichlet_le_twice_moving_deficit
