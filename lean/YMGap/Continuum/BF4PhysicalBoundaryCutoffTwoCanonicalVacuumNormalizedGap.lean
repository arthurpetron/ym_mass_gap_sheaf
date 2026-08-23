/-
# Normalized physical gap on the canonical cutoff-two vacuum sector

The checked cutoff-two 65-state theorem is stated for the unnormalized
production reflected kernel and its restricted row sums.  The cofinal
physical construction uses the normalized reflected joint and its canonical
row marginal.  This module proves that these are the same finite sector data
up to the common positive partition factor and transports the strict
`49/50` estimate across that factor.

The load-bearing support statement is also made exact: row closure lets the
full physical marginal sum be filtered to the 65-state sector, whose literal
list is the canonical vacuum communicating component at cutoff two.

This is a nontrivial finite-cutoff theorem.  It does not provide a cofinal
cutoff family, a thermodynamic or continuum limit, or the Clay theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumGap
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorCode
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorCode
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalUpperGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_filter_eq_of_zero_local
    {A : Type} (value : A → Q') (predicate : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → predicate item = false →
        value item ≈ 0) →
      listQSum value (items.filter predicate) ≈ listQSum value items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true, if_false,
            listQSum]
          have hhead := hzero head List.mem_cons_self hp
          have htail := listQSum_filter_eq_of_zero_local
            value predicate tail
            (fun item hitem =>
              hzero item (List.mem_cons_of_mem head hitem))
          exact Q'.eqv_trans _ (listQSum value tail) _ htail
            (Q'.eqv_trans _ (0 + listQSum value tail) _
              (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _)))
              (Q'.add_eqv_congr' (Q'.eqv_symm hhead) (Q'.eqv_refl _)))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_filter_eq_of_zero_local value predicate tail
              (fun item hitem =>
                hzero item (List.mem_cons_of_mem head hitem)))

private theorem perm_of_nodup_mem_iff_local {A : Type} :
    ∀ (left right : List A), left.Nodup → right.Nodup →
      (∀ item, item ∈ left ↔ item ∈ right) → left.Perm right
  | [], [], _, _, _ => List.Perm.nil
  | [], head :: tail, _, _, hmem => by
      have hfalse : head ∈ ([] : List A) :=
        (hmem head).2 List.mem_cons_self
      cases hfalse
  | head :: tail, right, hleft, hright, hmem => by
      have hleftParts := List.nodup_cons.mp hleft
      have hheadRight : head ∈ right := (hmem head).1 List.mem_cons_self
      obtain ⟨before, after, hsplit⟩ := List.append_of_mem hheadRight
      subst right
      have hmiddle : (head :: (before ++ after)).Perm
          (before ++ head :: after) := List.perm_middle.symm
      have hmiddleNodup : (head :: (before ++ after)).Nodup :=
        hmiddle.symm.nodup hright
      have hmiddleParts := List.nodup_cons.mp hmiddleNodup
      have htailMem : ∀ item,
          item ∈ tail ↔ item ∈ before ++ after := by
        intro item
        constructor
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hleftParts.1 hitem
          have hy := (hmem item).1 (List.mem_cons_of_mem head hitem)
          rcases List.mem_append.mp hy with hbefore | hrest
          · exact List.mem_append_left after hbefore
          · exact List.mem_append_right before
              ((List.mem_cons.mp hrest).resolve_left hne)
        · intro hitem
          have hne : item ≠ head := by
            intro heq
            subst item
            exact hmiddleParts.1 hitem
          have hy : item ∈ before ++ head :: after := by
            rcases List.mem_append.mp hitem with hbefore | hafter
            · exact List.mem_append_left (head :: after) hbefore
            · exact List.mem_append_right before
                (List.mem_cons_of_mem head hafter)
          exact (List.mem_cons.mp ((hmem item).2 hy)).resolve_left hne
      have htailPerm := perm_of_nodup_mem_iff_local
        tail (before ++ after) hleftParts.2 hmiddleParts.2 htailMem
      exact (List.Perm.cons head htailPerm).trans hmiddle

private theorem listQSum_perm_local {A : Type} (value : A → Q') :
    ∀ {left right : List A}, left.Perm right →
      listQSum value left ≈ listQSum value right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ hperm =>
      Q'.add_eqv_congr_left _ _ _ (listQSum_perm_local value hperm)
  | _, _, List.Perm.swap first second rest => by
      change value second + (value first + listQSum value rest) ≈
        value first + (value second + listQSum value rest)
      exact Q'.eqv_trans _
        ((value second + value first) + listQSum value rest) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
        (Q'.eqv_trans _
          ((value first + value second) + listQSum value rest) _
          (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _))
          (Q'.add_assoc_eqv _ _ _))
  | _, _, List.Perm.trans first second =>
      Q'.eqv_trans _ _ _
        (listQSum_perm_local value first)
      (listQSum_perm_local value second)

/-! ## 1. The exact normalized 65-state sector data -/

def cutoffTwoPartitionReciprocal : Q' :=
  Q'.recipPos
    (slabParametricKPhysicalPartition cutoffTwoHalfCoupling 2
      (centralExtent 0))
    (slabParametricKPhysicalPartition_pos (by decide) 2
      (centralExtent 0))

theorem cutoffTwoPartitionReciprocal_pos :
    (0 : Q') < cutoffTwoPartitionReciprocal :=
  Q'.recipPos_pos _ _

def cutoffTwoSectorNormalizedKernel (row column : Nat) : Q' :=
  cutoffTwoSectorPhysicalKernel row column *
    cutoffTwoPartitionReciprocal

def cutoffTwoSectorNormalizedRowSum (row : Nat) : Q' :=
  listQSum (fun column => cutoffTwoSectorNormalizedKernel row column)
    (List.range 65)

theorem cutoffTwoSectorNormalizedKernel_eqv_scaled
    {row column : Nat} :
    cutoffTwoSectorNormalizedKernel row column ≈
      cutoffTwoSectorPhysicalKernel row column *
        cutoffTwoPartitionReciprocal := by
  unfold cutoffTwoSectorNormalizedKernel cutoffTwoSectorPhysicalKernel
    cutoffTwoPartitionReciprocal
  exact Q'.eqv_refl _

/-- The compact scaled definition is exactly the production normalized
physical joint entry on the corresponding literal sector states. -/
theorem cutoffTwoSectorNormalizedKernel_eqv_actual
    {row column : Nat} :
    cutoffTwoSectorNormalizedKernel row column ≈
      centralNormalizedPhysicalReflectedKernel cutoffTwoHalfCoupling
        (by decide) 2 0 (cutoffTwoSectorStateAt row)
        (cutoffTwoSectorStateAt column) := by
  unfold cutoffTwoSectorNormalizedKernel cutoffTwoSectorPhysicalKernel
    centralNormalizedPhysicalReflectedKernel Q'.divPos
    cutoffTwoPartitionReciprocal
  exact Q'.eqv_refl _

theorem cutoffTwoSectorNormalizedRowSum_eqv_scaled
    (row : Nat) :
    cutoffTwoSectorNormalizedRowSum row ≈
      cutoffTwoSectorPhysicalRowSum row *
        cutoffTwoPartitionReciprocal := by
  unfold cutoffTwoSectorNormalizedRowSum cutoffTwoSectorPhysicalRowSum
  refine Q'.eqv_trans _
    (listQSum
      (fun column => cutoffTwoSectorPhysicalKernel row column *
        cutoffTwoPartitionReciprocal)
      (List.range 65)) _ ?_ ?_
  · apply listQSum_congr_on
    intro column _
    exact cutoffTwoSectorNormalizedKernel_eqv_scaled
  · exact listQSum_mul_right _ _ _

/-- A sealed dependent package for the common positive normalization scale.
Keeping the value and its two exact transport laws in one package prevents a
downstream checker from unfolding the full partition expression merely to
compare rational representatives. -/
structure CutoffTwoPartitionScaleCertificate where
  scale : Q'
  scale_pos : (0 : Q') < scale
  kernel_scaled : ∀ row column : Nat,
    cutoffTwoSectorNormalizedKernel row column ≈
      cutoffTwoSectorPhysicalKernel row column * scale
  rowSum_scaled : ∀ row : Nat,
    cutoffTwoSectorNormalizedRowSum row ≈
      cutoffTwoSectorPhysicalRowSum row * scale

opaque cutoffTwoPartitionScaleCertificate :
    CutoffTwoPartitionScaleCertificate := {
  scale := cutoffTwoPartitionReciprocal
  scale_pos := cutoffTwoPartitionReciprocal_pos
  kernel_scaled := by
    intro row column
    exact cutoffTwoSectorNormalizedKernel_eqv_scaled
  rowSum_scaled := by
    intro row
    exact cutoffTwoSectorNormalizedRowSum_eqv_scaled row
}

def cutoffTwoPartitionReciprocalSealed : Q' :=
  cutoffTwoPartitionScaleCertificate.scale

theorem cutoffTwoPartitionReciprocalSealed_pos :
    (0 : Q') < cutoffTwoPartitionReciprocalSealed :=
  cutoffTwoPartitionScaleCertificate.scale_pos

theorem cutoffTwoSectorNormalizedKernel_eqv_scaledSealed
    {row column : Nat} :
    cutoffTwoSectorNormalizedKernel row column ≈
      cutoffTwoSectorPhysicalKernel row column *
        cutoffTwoPartitionReciprocalSealed :=
  cutoffTwoPartitionScaleCertificate.kernel_scaled row column

theorem cutoffTwoSectorNormalizedRowSum_eqv_scaledSealed
    (row : Nat) :
    cutoffTwoSectorNormalizedRowSum row ≈
      cutoffTwoSectorPhysicalRowSum row *
        cutoffTwoPartitionReciprocalSealed :=
  cutoffTwoPartitionScaleCertificate.rowSum_scaled row

/-! ## 2. Row closure identifies the restricted and full marginals -/

def cutoffTwoSectorMembershipTest (state : EdgeLabelling) : Bool :=
  decide (bf4StateCode 2 0 state ∈ cutoffTwoCubeSectorCodes)

theorem cutoffTwoSectorMembershipTest_true_iff
    {state : EdgeLabelling} (hstate : state ∈ centralHalfStates 2 0) :
    cutoffTwoSectorMembershipTest state = true ↔
      state ∈ cutoffTwoCubeSectorStates := by
  unfold cutoffTwoSectorMembershipTest
  simp only [decide_eq_true_eq]
  exact cutoffTwoSectorCode_mem_iff_of_halfState hstate

theorem cutoffTwoHalfStates_filter_sector_perm :
    (centralHalfStates 2 0).filter cutoffTwoSectorMembershipTest |>.Perm
      cutoffTwoCubeSectorStates := by
  apply perm_of_nodup_mem_iff_local
  · exact List.filter_sublist.nodup (centralHalfStates_nodup 2 0)
  · exact cutoffTwoCubeSectorStates_nodup
  · intro state
    simp only [List.mem_filter]
    constructor
    · intro hmem
      exact (cutoffTwoSectorMembershipTest_true_iff hmem.1).1 hmem.2
    · intro hsector
      have hhalf := cutoffTwoCubeSectorState_mem_halfStates hsector
      exact ⟨hhalf,
        (cutoffTwoSectorMembershipTest_true_iff hhalf).2 hsector⟩

theorem cutoffTwoSectorNormalizedKernel_eqv_zero_of_outside
    {source target : EdgeLabelling}
    (hsource : source ∈ cutoffTwoCubeSectorStates)
    (htarget : target ∈ centralHalfStates 2 0)
    (houtside : target ∉ cutoffTwoCubeSectorStates) :
    centralNormalizedPhysicalReflectedKernel cutoffTwoHalfCoupling
        (by decide) 2 0 source target ≈ 0 := by
  unfold centralNormalizedPhysicalReflectedKernel Q'.divPos
  refine Q'.eqv_trans _
    (0 * cutoffTwoPartitionReciprocal) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (centralPhysicalReflectedKernel_cutoffTwo_cubeSector_eqv_zero
        source target hsource htarget houtside)
  · exact Q'.zero_mul_eqv _

/-- The restricted normalized row sum is exactly the canonical physical row
marginal, not a separately normalized surrogate. -/
theorem cutoffTwoSectorNormalizedRowSum_eqv_centralPhysicalRowMarginal
    {row : Nat} (hrow : row < 65) :
    cutoffTwoSectorNormalizedRowSum row ≈
      centralPhysicalRowMarginal cutoffTwoHalfCoupling
        (by decide) 2 0 (cutoffTwoSectorStateAt row) := by
  let source := cutoffTwoSectorStateAt row
  let value := centralNormalizedPhysicalReflectedKernel
    cutoffTwoHalfCoupling (by decide) 2 0 source
  have hsource : source ∈ cutoffTwoCubeSectorStates :=
    cutoffTwoSectorStateAt_mem hrow
  have hfiltered :
      listQSum value
          ((centralHalfStates 2 0).filter cutoffTwoSectorMembershipTest) ≈
        listQSum value (centralHalfStates 2 0) := by
    apply listQSum_filter_eq_of_zero_local
    intro target htarget htest
    have houtside : target ∉ cutoffTwoCubeSectorStates := by
      intro hsector
      have htrue :=
        (cutoffTwoSectorMembershipTest_true_iff htarget).2 hsector
      rw [htest] at htrue
      cases htrue
    exact cutoffTwoSectorNormalizedKernel_eqv_zero_of_outside
      hsource htarget houtside
  have hsector :
      listQSum value
          ((centralHalfStates 2 0).filter cutoffTwoSectorMembershipTest) ≈
        listQSum value cutoffTwoCubeSectorStates :=
    listQSum_perm_local value cutoffTwoHalfStates_filter_sector_perm
  have hindexed :
      cutoffTwoSectorNormalizedRowSum row ≈
        listQSum value cutoffTwoCubeSectorStates := by
    refine Q'.eqv_trans _
      (listQSum
        (fun column => value (cutoffTwoSectorStateAt column))
        (List.range 65)) _ ?_ ?_
    · unfold cutoffTwoSectorNormalizedRowSum
      apply listQSum_congr_on
      intro column _
      exact cutoffTwoSectorNormalizedKernel_eqv_actual
    · apply Q'.eqv_of_eq
      rw [← cutoffTwoCubeSectorStates_length]
      exact finiteIndexSum_eq_listQSum
        cutoffTwoCubeSectorStates zeroEdgeLabelling value
  unfold cutoffTwoSectorNormalizedRowSum
    centralPhysicalRowMarginal
  exact Q'.eqv_trans _
    (listQSum value cutoffTwoCubeSectorStates) _
    hindexed
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hsector) hfiltered)

/-! ## 3. Scaling the checked strict gap -/

private theorem normalizedWeightedMean_eqv_scaled
    (coefficient : Nat → Q') :
    finiteWeightedMean 65 cutoffTwoSectorNormalizedRowSum coefficient ≈
      finiteWeightedMean 65 cutoffTwoSectorPhysicalRowSum coefficient *
        cutoffTwoPartitionReciprocal := by
  unfold finiteWeightedMean
  refine Q'.eqv_trans _
    (listQSum
      (fun row =>
        (coefficient row * cutoffTwoSectorPhysicalRowSum row) *
          cutoffTwoPartitionReciprocal)
      (List.range 65)) _ ?_ ?_
  · apply listQSum_congr_on
    intro row _
    refine Q'.eqv_trans _
      (coefficient row *
        (cutoffTwoSectorPhysicalRowSum row *
          cutoffTwoPartitionReciprocal)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (cutoffTwoSectorNormalizedRowSum_eqv_scaled row)
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv (coefficient row)
          (cutoffTwoSectorPhysicalRowSum row)
          cutoffTwoPartitionReciprocal)
  · exact listQSum_mul_right _ _ _

private theorem normalizedDiagonal_eqv_scaled
    (coefficient : Nat → Q') :
    finiteDiagonalQuadratic 65 cutoffTwoSectorNormalizedRowSum coefficient ≈
      finiteDiagonalQuadratic 65 cutoffTwoSectorPhysicalRowSum coefficient *
        cutoffTwoPartitionReciprocal := by
  unfold finiteDiagonalQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun row =>
        ((coefficient row * coefficient row) *
          cutoffTwoSectorPhysicalRowSum row) *
            cutoffTwoPartitionReciprocal)
      (List.range 65)) _ ?_ ?_
  · apply listQSum_congr_on
    intro row _
    refine Q'.eqv_trans _
      ((coefficient row * coefficient row) *
        (cutoffTwoSectorPhysicalRowSum row *
          cutoffTwoPartitionReciprocal)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (cutoffTwoSectorNormalizedRowSum_eqv_scaled row)
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv (coefficient row * coefficient row)
          (cutoffTwoSectorPhysicalRowSum row)
          cutoffTwoPartitionReciprocal)
  · exact listQSum_mul_right _ _ _

private theorem normalizedMatrix_eqv_scaled
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic 65 cutoffTwoSectorNormalizedKernel coefficient ≈
      finiteMatrixQuadratic 65 cutoffTwoSectorPhysicalKernel coefficient *
        cutoffTwoPartitionReciprocal := by
  unfold finiteMatrixQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun row =>
        listQSum
          (fun column =>
            ((coefficient row * coefficient column) *
              cutoffTwoSectorPhysicalKernel row column) *
                cutoffTwoPartitionReciprocal)
          (List.range 65))
      (List.range 65)) _ ?_ ?_
  · apply listQSum_congr_on
    intro row _
    apply listQSum_congr_on
    intro column _
    refine Q'.eqv_trans _
      ((coefficient row * coefficient column) *
        (cutoffTwoSectorPhysicalKernel row column *
          cutoffTwoPartitionReciprocal)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        cutoffTwoSectorNormalizedKernel_eqv_scaled
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv (coefficient row * coefficient column)
          (cutoffTwoSectorPhysicalKernel row column)
          cutoffTwoPartitionReciprocal)
  · refine Q'.eqv_trans _
      (listQSum
        (fun row =>
          listQSum
            (fun column =>
              (coefficient row * coefficient column) *
                cutoffTwoSectorPhysicalKernel row column)
            (List.range 65) * cutoffTwoPartitionReciprocal)
        (List.range 65)) _ ?_ ?_
    · apply listQSum_congr_on
      intro row _
      exact listQSum_mul_right _ _ _
    · exact listQSum_mul_right _ _ _

theorem cutoffTwoSectorNormalizedMeanZeroAbsGapAt49Over50
    (coefficient : Nat → Q')
    (hcenter :
      finiteWeightedMean 65
        cutoffTwoSectorNormalizedRowSum coefficient ≈ 0) :
    Q'.abs
        (finiteMatrixQuadratic 65
          cutoffTwoSectorNormalizedKernel coefficient) ≤
      cutoffTwoSectorRate49Over50 *
        finiteDiagonalQuadratic 65
          cutoffTwoSectorNormalizedRowSum coefficient := by
  let reciprocal := cutoffTwoPartitionReciprocal
  have hscaledMean := normalizedWeightedMean_eqv_scaled coefficient
  have hrawCenter :
      finiteWeightedMean 65
          cutoffTwoSectorPhysicalRowSum coefficient ≈ 0 := by
    apply Q'.mul_eqv_zero_of_pos cutoffTwoPartitionReciprocal_pos
    exact Q'.eqv_trans _
      (finiteWeightedMean 65 cutoffTwoSectorPhysicalRowSum coefficient *
        reciprocal) _
      (Q'.mul_comm_eqv _ _)
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hscaledMean) hcenter)
  have hrawGap := cutoffTwoSectorPhysicalMeanZeroAbsGapAt49Over50
    coefficient hrawCenter
  have hreciprocalNonnegative : (0 : Q') ≤ reciprocal :=
    Q'.le_of_lt cutoffTwoPartitionReciprocal_pos
  have habsScaled := YMGap.Constructive.ExpNeg.abs_mul_le
    (finiteMatrixQuadratic 65 cutoffTwoSectorPhysicalKernel coefficient)
    reciprocal
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
    hreciprocalNonnegative] at habsScaled
  have hrawScaled := Q'.mul_le_mul_of_nonneg_right _ _ reciprocal
    hrawGap hreciprocalNonnegative
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr (normalizedMatrix_eqv_scaled coefficient)))
    (Q'.le_trans' _ _ _ habsScaled
      (Q'.le_trans' _ _ _ hrawScaled
        (Q'.le_of_eqv
          (Q'.eqv_trans _
            (cutoffTwoSectorRate49Over50 *
              (finiteDiagonalQuadratic 65
                cutoffTwoSectorPhysicalRowSum coefficient * reciprocal)) _
            (Q'.mul_assoc_eqv _ _ _)
            (Q'.mul_eqv_congr_left _ _ _
              (Q'.eqv_symm
                (normalizedDiagonal_eqv_scaled coefficient)))))))

/-! ## 4. Statement in the canonical physical marginal language -/

def cutoffTwoSectorCanonicalPhysicalWeight (row : Nat) : Q' :=
  cutoffTwoSectorNormalizedRowSum row

theorem cutoffTwoSectorCanonicalPhysicalWeight_eqv_normalizedRowSum
    (row : Nat) :
    cutoffTwoSectorCanonicalPhysicalWeight row ≈
      cutoffTwoSectorNormalizedRowSum row :=
  Q'.eqv_refl _

/-- The compact canonical weight is the actual physical row marginal. -/
theorem cutoffTwoSectorCanonicalPhysicalWeight_eqv_marginal
    {row : Nat} (hrow : row < 65) :
    cutoffTwoSectorCanonicalPhysicalWeight row ≈
      centralPhysicalRowMarginal cutoffTwoHalfCoupling
        (by decide) 2 0 (cutoffTwoSectorStateAt row) :=
  cutoffTwoSectorNormalizedRowSum_eqv_centralPhysicalRowMarginal hrow

/-- The normalized production joint on the exact canonical cutoff-two vacuum
support has a strict absolute centered gap at rate `49/50`, expressed using
the actual physical row marginal. -/
theorem cutoffTwoCanonicalVacuumNormalized_exact_and_strict_abs_gap :
    (∀ state : EdgeLabelling,
      state ∈ centralPhysicalFiniteVacuumSectorStates
          cutoffTwoHalfCoupling (by decide) 2 0 ↔
        state ∈ cutoffTwoCubeSectorStates) ∧
      cutoffTwoSectorRate49Over50 < (1 : Q') ∧
      ∀ coefficient : Nat → Q',
        finiteWeightedMean 65
            cutoffTwoSectorCanonicalPhysicalWeight coefficient ≈ 0 →
          Q'.abs
              (finiteMatrixQuadratic 65
                cutoffTwoSectorNormalizedKernel coefficient) ≤
            cutoffTwoSectorRate49Over50 *
              finiteDiagonalQuadratic 65
                cutoffTwoSectorCanonicalPhysicalWeight coefficient := by
  refine ⟨centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff,
    cutoffTwoSectorRate49Over50_lt_one, ?_⟩
  intro coefficient hcenter
  have hmean :
      finiteWeightedMean 65
          cutoffTwoSectorNormalizedRowSum coefficient ≈
        finiteWeightedMean 65
          cutoffTwoSectorCanonicalPhysicalWeight coefficient := by
    unfold finiteWeightedMean
    apply listQSum_congr_on
    intro row _hrow
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (cutoffTwoSectorCanonicalPhysicalWeight_eqv_normalizedRowSum
          row))
  have hgap := cutoffTwoSectorNormalizedMeanZeroAbsGapAt49Over50
    coefficient (Q'.eqv_trans _ _ _ hmean hcenter)
  have hdiagonal :
      finiteDiagonalQuadratic 65
          cutoffTwoSectorNormalizedRowSum coefficient ≈
        finiteDiagonalQuadratic 65
          cutoffTwoSectorCanonicalPhysicalWeight coefficient := by
    unfold finiteDiagonalQuadratic
    apply listQSum_congr_on
    intro row _hrow
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (cutoffTwoSectorCanonicalPhysicalWeight_eqv_normalizedRowSum
          row))
  exact Q'.le_trans' _ _ _ hgap
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left cutoffTwoSectorRate49Over50 _ _ hdiagonal))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap.cutoffTwoHalfStates_filter_sector_perm
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap.cutoffTwoSectorNormalizedRowSum_eqv_centralPhysicalRowMarginal
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap.cutoffTwoSectorNormalizedMeanZeroAbsGapAt49Over50
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap.cutoffTwoCanonicalVacuumNormalized_exact_and_strict_abs_gap
