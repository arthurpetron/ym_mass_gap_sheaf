/-
# The pulled cutoff-two Dirichlet energy embeds in the full later deficit

The fixed cutoff-two pulled Dirichlet sum is the old-old sub-sum of the full
Dirichlet energy of the zero-extended coefficient on the later canonical
vacuum sector.  This module proves that comparison by an explicit injective
map on the two Cartesian index lists.  Every target summand is nonnegative,
and source summands agree with their images through the exact coefficient and
kernel recodings.

The full finite stationary/symmetric Dirichlet identity then identifies the
target energy with twice the later diagonal-minus-matrix deficit.  No uniform
edge floor or strict rate is assumed or asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledDirichletEmbedding

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
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

/-! ## 1. The old-old Dirichlet sub-sum -/

/-- The fixed pulled Dirichlet energy is bounded by the full later Dirichlet
energy of the coefficient extended by zero from the cutoff-two vacuum sector. -/
theorem cutoffTwoPulledDirichlet_le_fullExtensionDirichlet
    (later : Nat) (hlater : 2 ≤ later)
    (coefficient : Nat → Q') :
    finiteJointDirichletEnergy
        cutoffTwoPulledStates coefficient
        (cutoffTwoPulledKernelAt later) ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices
          cutoffTwoHalfCoupling (by decide) later 0)
        (centralPhysicalFiniteVacuumSectorCoefficientExtension
          cutoffTwoHalfCoupling (by decide) 2 later 0 coefficient)
        (centralPhysicalFiniteKernel
          cutoffTwoHalfCoupling (by decide) later 0) := by
  let sourceStates := cutoffTwoPulledStates
  let targetStates := centralPhysicalFiniteVacuumSectorIndices
    cutoffTwoHalfCoupling (by decide) later 0
  let indexMap := centralPhysicalFiniteCutoffIndexMap
    cutoffTwoHalfCoupling (by decide) 2 later 0
  let extension := centralPhysicalFiniteVacuumSectorCoefficientExtension
    cutoffTwoHalfCoupling (by decide) 2 later 0 coefficient
  let sourceTerm : Nat × Nat → Q' := fun pair =>
    cutoffTwoPulledKernelAt later pair.1 pair.2 *
      ((coefficient pair.1 + -coefficient pair.2) *
        (coefficient pair.1 + -coefficient pair.2))
  let targetTerm : Nat × Nat → Q' := fun pair =>
    centralPhysicalFiniteKernel
        cutoffTwoHalfCoupling (by decide) later 0 pair.1 pair.2 *
      ((extension pair.1 + -extension pair.2) *
        (extension pair.1 + -extension pair.2))
  let pairMap : Nat × Nat → Nat × Nat := fun pair =>
    (indexMap pair.1, indexMap pair.2)
  have hsourceNodup : sourceStates.Nodup :=
    centralPhysicalFiniteVacuumSectorIndices_nodup
      cutoffTwoHalfCoupling (by decide) 2 0
  have htargetNodup : targetStates.Nodup :=
    centralPhysicalFiniteVacuumSectorIndices_nodup
      cutoffTwoHalfCoupling (by decide) later 0
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
          cutoffTwoPulledKernelAt centralPhysicalFinitePulledKernel
        exact Q'.mul_eqv_congr_left _ _ _
          (square_eqv_congr hdifference)
      exact Q'.ge_of_eqv htargetSource
    · intro pair hpair
      have hparts := (mem_cartesian_iff
        targetStates targetStates pair).mp hpair
      unfold targetTerm
      exact Q'.mul_nonneg _ _
        (by
          unfold centralPhysicalFiniteKernel
          exact centralNormalizedPhysicalReflectedKernel_nonnegative
            (by decide) later 0 _ _)
        (square_nonnegative _)
  have hsourceCartesian :
      listQSum sourceTerm (cartesian sourceStates sourceStates) ≈
        finiteJointDirichletEnergy sourceStates coefficient
          (cutoffTwoPulledKernelAt later) := by
    unfold finiteJointDirichletEnergy sourceTerm
    exact listQSum_cartesian_eq_nested_local _ _ _
  have htargetCartesian :
      listQSum targetTerm (cartesian targetStates targetStates) ≈
        finiteJointDirichletEnergy targetStates extension
          (centralPhysicalFiniteKernel
            cutoffTwoHalfCoupling (by decide) later 0) := by
    unfold finiteJointDirichletEnergy targetTerm
    exact listQSum_cartesian_eq_nested_local _ _ _
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hsourceCartesian)
    (Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv htargetCartesian))

/-! ## 2. Exact contraction to the pulled diagonal-minus-matrix deficit -/

/-- The pulled old-old energy is bounded by twice the actual moving-form
deficit, because the latter is the full zero-extension Dirichlet energy. -/
theorem cutoffTwoPulledDirichlet_le_twice_moving_deficit
    (later : Nat) (hlater : 2 ≤ later)
    (coefficient : Nat → Q') :
    finiteJointDirichletEnergy cutoffTwoPulledStates
        (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)
        (cutoffTwoPulledKernelAt later) ≤
      (cutoffTwoPulledDiagonalAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) +
        cutoffTwoPulledDiagonalAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)) +
        -(cutoffTwoPulledMatrixAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) +
          cutoffTwoPulledMatrixAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)) := by
  let moving := cutoffTwoPulledMovingCenteredCoefficientAt later coefficient
  let extension := centralPhysicalFiniteVacuumSectorCoefficientExtension
    cutoffTwoHalfCoupling (by decide) 2 later 0 moving
  have hsubsum := cutoffTwoPulledDirichlet_le_fullExtensionDirichlet
    later hlater moving
  have hfull :=
    centralPhysicalFiniteVacuumSectorDirichlet_eqv_twice_deficit
      cutoffTwoHalfCoupling (by decide) later 0 extension
  have hmatrix :=
    centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
      (w := cutoffTwoHalfCoupling) (hw := by decide)
      (base := 2) (later := later) (half := 0)
      hlater coefficient
  have hdiagonal :=
    centralPhysicalFiniteVacuumSectorHeadCenteredExtensionDiagonal_eqv_pulled
      (w := cutoffTwoHalfCoupling) (hw := by decide)
      (base := 2) (later := later) (half := 0)
      hlater coefficient
  have hdeficit :
      (centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          cutoffTwoHalfCoupling (by decide) later 0 extension +
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          cutoffTwoHalfCoupling (by decide) later 0 extension) +
        -(centralPhysicalFiniteVacuumSectorMatrixQuadratic
            cutoffTwoHalfCoupling (by decide) later 0 extension +
          centralPhysicalFiniteVacuumSectorMatrixQuadratic
            cutoffTwoHalfCoupling (by decide) later 0 extension) ≈
      (cutoffTwoPulledDiagonalAt later moving +
        cutoffTwoPulledDiagonalAt later moving) +
        -(cutoffTwoPulledMatrixAt later moving +
          cutoffTwoPulledMatrixAt later moving) := by
    have hdiagonalPulled :
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            cutoffTwoHalfCoupling (by decide) later 0 extension ≈
          cutoffTwoPulledDiagonalAt later moving := by
      exact Q'.eqv_trans _ _ _ hdiagonal (Q'.eqv_refl _)
    have hmatrixPulled :
        centralPhysicalFiniteVacuumSectorMatrixQuadratic
            cutoffTwoHalfCoupling (by decide) later 0 extension ≈
          cutoffTwoPulledMatrixAt later moving := by
      exact Q'.eqv_trans _ _ _ hmatrix (Q'.eqv_refl _)
    exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hdiagonalPulled hdiagonalPulled)
      (Q'.neg_eqv_congr _ _
        (Q'.add_eqv_congr' hmatrixPulled hmatrixPulled))
  exact Q'.le_trans' _ _ _ hsubsum
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hfull hdeficit))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledDirichletEmbedding

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledDirichletEmbedding.cutoffTwoPulledDirichlet_le_fullExtensionDirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledDirichletEmbedding.cutoffTwoPulledDirichlet_le_twice_moving_deficit
