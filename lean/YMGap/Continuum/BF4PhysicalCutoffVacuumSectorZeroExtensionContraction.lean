/-
# Contracting the zero-extended physical vacuum-sector decomposition

The observable coefficient introduced for the embedded old component is
literally zero on every genuinely new target coordinate.  Therefore its new
mean and diagonal terms vanish, as do the old-new, new-old, and new-new
matrix blocks.  Combining these zero identities with the exact pushforward
theorems contracts the full later canonical-sector forms to the previously
constructed pulled old-component forms.

This is an exact statement about the zero-extended finite subspace.  It does
not bound arbitrary later-component coefficients and supplies no strict rate
uniform in the base cutoff.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_eqv_zero_of_pointwise
    {A : Type} (value : A → Q') (items : List A)
    (hzero : ∀ item, item ∈ items → value item ≈ 0) :
    listQSum value items ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum (fun _ => (0 : Q')) items) _ ?_ ?_
  · exact listQSum_congr_on value (fun _ => 0) items hzero
  · exact listQSum_zero items

/-- The observable zero extension is literally zero on each genuinely new
target coordinate. -/
theorem centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_eq_zero_of_mem_new
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw base later half)
    (observable : EdgeLabelling → Q') :
    centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
      w hw base later half observable index = 0 := by
  have hnot :=
    (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp hindex).2
  have htest : centralPhysicalFiniteEmbeddedVacuumSectorB
      w hw base later half index = false := by
    unfold centralPhysicalFiniteEmbeddedVacuumSectorB
    exact decide_eq_false hnot
  unfold centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
  simp only [htest, Bool.false_eq_true, ↓reduceIte]

/-- The new-coordinate contribution to the zero-extended weighted mean
vanishes exactly. -/
theorem centralPhysicalFiniteVacuumSectorZeroExtension_newWeightedMean_eqv_zero
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (observable : EdgeLabelling → Q') :
    listQSum
        (fun index =>
          centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
              w hw base later half observable index *
            centralPhysicalFiniteWeight w hw later half index)
        (centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half) ≈ 0 := by
  apply listQSum_eqv_zero_of_pointwise
  intro index hindex
  rw [centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_eq_zero_of_mem_new
    hindex observable]
  exact Q'.zero_mul_eqv _

/-- The new-coordinate contribution to the zero-extended diagonal norm
vanishes exactly. -/
theorem centralPhysicalFiniteVacuumSectorZeroExtension_newDiagonal_eqv_zero
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (observable : EdgeLabelling → Q') :
    listQSum
        (fun index =>
          (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
              w hw base later half observable index *
            centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
              w hw base later half observable index) *
            centralPhysicalFiniteWeight w hw later half index)
        (centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half) ≈ 0 := by
  apply listQSum_eqv_zero_of_pointwise
  intro index hindex
  rw [centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_eq_zero_of_mem_new
    hindex observable]
  exact Q'.eqv_trans _ (0 *
      centralPhysicalFiniteWeight w hw later half index) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv 0))
    (Q'.zero_mul_eqv _)

private theorem finiteJointBlock_eqv_zero_of_right_coefficient
    {State : Type}
    (left right : List State) (coefficient : State → Q')
    (joint : State → State → Q')
    (hzero : ∀ state, state ∈ right → coefficient state ≈ 0) :
    finiteJointBlock left right coefficient joint ≈ 0 := by
  apply listQSum_eqv_zero_of_pointwise
  intro leftState hleft
  apply listQSum_eqv_zero_of_pointwise
  intro rightState hright
  refine Q'.eqv_trans _
    ((coefficient leftState * 0) * joint leftState rightState) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (hzero rightState hright))
  · exact Q'.eqv_trans _
      (0 * joint leftState rightState) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_zero_eqv (coefficient leftState)))
      (Q'.zero_mul_eqv _)

private theorem finiteJointBlock_eqv_zero_of_left_coefficient
    {State : Type}
    (left right : List State) (coefficient : State → Q')
    (joint : State → State → Q')
    (hzero : ∀ state, state ∈ left → coefficient state ≈ 0) :
    finiteJointBlock left right coefficient joint ≈ 0 := by
  apply listQSum_eqv_zero_of_pointwise
  intro leftState hleft
  apply listQSum_eqv_zero_of_pointwise
  intro rightState hright
  refine Q'.eqv_trans _
    ((0 * coefficient rightState) * joint leftState rightState) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (hzero leftState hleft))
  · exact Q'.eqv_trans _
      (0 * joint leftState rightState) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.zero_mul_eqv (coefficient rightState)))
      (Q'.zero_mul_eqv _)

/-- A quadratic whose coefficient vanishes on the false side of a Boolean
partition contracts exactly to its true-true block. -/
theorem finiteJointQuadratic_filter_eqv_trueBlock_of_zero_false
    {State : Type} (states : List State) (test : State → Bool)
    (coefficient : State → Q') (joint : State → State → Q')
    (hzero : ∀ state,
      state ∈ states.filter (fun item => !(test item)) →
      coefficient state ≈ 0) :
    finiteJointQuadratic states coefficient joint ≈
      finiteJointBlock
        (states.filter test) (states.filter test) coefficient joint := by
  have hfour := finiteJointQuadratic_filter_four_blocks
    states test coefficient joint
  have hon := finiteJointBlock_eqv_zero_of_right_coefficient
    (states.filter test) (states.filter (fun item => !(test item)))
    coefficient joint hzero
  have hno := finiteJointBlock_eqv_zero_of_left_coefficient
    (states.filter (fun item => !(test item))) (states.filter test)
    coefficient joint hzero
  have hnn := finiteJointBlock_eqv_zero_of_left_coefficient
    (states.filter (fun item => !(test item)))
    (states.filter (fun item => !(test item))) coefficient joint hzero
  let oldBlock := finiteJointBlock
    (states.filter test) (states.filter test) coefficient joint
  refine Q'.eqv_trans _ _ _ hfour ?_
  refine Q'.eqv_trans _ ((oldBlock + 0) + (0 + 0)) _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' (Q'.eqv_refl oldBlock) hon)
      (Q'.add_eqv_congr' hno hnn)) ?_
  have hzerozero : (0 : Q') + 0 ≈ 0 :=
    Q'.eqv_of_eq (Q'.zero_add' 0)
  refine Q'.eqv_trans _ ((oldBlock + 0) + 0) _
    (Q'.add_eqv_congr_left (oldBlock + 0) (0 + 0) 0 hzerozero) ?_
  exact Q'.eqv_trans _ (oldBlock + 0) _
    (Q'.eqv_of_eq (Q'.add_zero' (oldBlock + 0)))
    (Q'.eqv_of_eq (Q'.add_zero' oldBlock))

private theorem zeroExtension_new_coefficient_eqv_zero
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (observable : EdgeLabelling → Q') :
    ∀ index,
      index ∈ centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw base later half →
      centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
        w hw base later half observable index ≈ 0 := by
  intro index hindex
  exact Q'.eqv_of_eq
    (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_eq_zero_of_mem_new
      hindex observable)

/-- The old-new block of the zero extension vanishes. -/
theorem centralPhysicalFiniteVacuumSectorZeroExtension_oldNew_eqv_zero
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (observable : EdgeLabelling → Q') :
    finiteJointBlock
        (centralPhysicalFiniteVacuumSectorOldBlockIndices
          w hw base later half)
        (centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half)
        (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
          w hw base later half observable)
        (centralPhysicalFiniteKernel w hw later half) ≈ 0 := by
  exact finiteJointBlock_eqv_zero_of_right_coefficient _ _ _ _
    (zeroExtension_new_coefficient_eqv_zero
      w hw base later half observable)

/-- The new-old block of the zero extension vanishes. -/
theorem centralPhysicalFiniteVacuumSectorZeroExtension_newOld_eqv_zero
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (observable : EdgeLabelling → Q') :
    finiteJointBlock
        (centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half)
        (centralPhysicalFiniteVacuumSectorOldBlockIndices
          w hw base later half)
        (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
          w hw base later half observable)
        (centralPhysicalFiniteKernel w hw later half) ≈ 0 := by
  exact finiteJointBlock_eqv_zero_of_left_coefficient _ _ _ _
    (zeroExtension_new_coefficient_eqv_zero
      w hw base later half observable)

/-- The new-new block of the zero extension vanishes. -/
theorem centralPhysicalFiniteVacuumSectorZeroExtension_newNew_eqv_zero
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (observable : EdgeLabelling → Q') :
    finiteJointBlock
        (centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half)
        (centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half)
        (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
          w hw base later half observable)
        (centralPhysicalFiniteKernel w hw later half) ≈ 0 := by
  exact finiteJointBlock_eqv_zero_of_left_coefficient _ _ _ _
    (zeroExtension_new_coefficient_eqv_zero
      w hw base later half observable)

/-! ## 3. Full later-sector forms contract to the pulled old forms -/

/-- The full later-component mean of a zero-extended base observable equals
the pulled base-component mean. -/
theorem centralPhysicalFiniteVacuumSectorZeroExtensionWeightedMean_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (observable : EdgeLabelling → Q') :
    centralPhysicalFiniteVacuumSectorWeightedMean w hw later half
        (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
          w hw base later half observable) ≈
      centralPhysicalFinitePulledVacuumSectorWeightedMean
        w hw base later half
        (centralPhysicalFiniteCoefficient w hw base half observable) := by
  have hsplit := centralPhysicalFiniteVacuumSectorWeightedMean_old_add_new
    w hw base later half
      (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
        w hw base later half observable)
  have hold := centralPhysicalFiniteVacuumSectorOldBlockWeightedMean_eqv_pulled
    (w := w) (hw := hw) (base := base) (later := later)
    (half := half) hcutoff observable
  have hnew :=
    centralPhysicalFiniteVacuumSectorZeroExtension_newWeightedMean_eqv_zero
      w hw base later half observable
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.eqv_trans _
      (centralPhysicalFinitePulledVacuumSectorWeightedMean
          w hw base later half
          (centralPhysicalFiniteCoefficient w hw base half observable) + 0) _
      (Q'.add_eqv_congr' hold hnew)
      (Q'.eqv_of_eq (Q'.add_zero' _)))

/-- The full later-component diagonal norm of a zero-extended base observable
equals the pulled base-component diagonal norm. -/
theorem centralPhysicalFiniteVacuumSectorZeroExtensionDiagonal_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (observable : EdgeLabelling → Q') :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw later half
        (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
          w hw base later half observable) ≈
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w hw base later half
        (centralPhysicalFiniteCoefficient w hw base half observable) := by
  have hsplit := centralPhysicalFiniteVacuumSectorDiagonalQuadratic_old_add_new
    w hw base later half
      (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
        w hw base later half observable)
  have hold := centralPhysicalFiniteVacuumSectorOldBlockDiagonal_eqv_pulled
    (w := w) (hw := hw) (base := base) (later := later)
    (half := half) hcutoff observable
  have hnew :=
    centralPhysicalFiniteVacuumSectorZeroExtension_newDiagonal_eqv_zero
      w hw base later half observable
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.eqv_trans _
      (centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half
          (centralPhysicalFiniteCoefficient w hw base half observable) + 0) _
      (Q'.add_eqv_congr' hold hnew)
      (Q'.eqv_of_eq (Q'.add_zero' _)))

/-- The full later-component reflected form of a zero-extended base observable
equals the pulled base-component reflected form. -/
theorem centralPhysicalFiniteVacuumSectorZeroExtensionMatrix_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (observable : EdgeLabelling → Q') :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic w hw later half
        (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
          w hw base later half observable) ≈
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w hw base later half
        (centralPhysicalFiniteCoefficient w hw base half observable) := by
  refine Q'.eqv_trans _
    (finiteJointBlock
      (centralPhysicalFiniteVacuumSectorOldBlockIndices
        w hw base later half)
      (centralPhysicalFiniteVacuumSectorOldBlockIndices
        w hw base later half)
      (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
        w hw base later half observable)
      (centralPhysicalFiniteKernel w hw later half)) _ ?_ ?_
  · unfold centralPhysicalFiniteVacuumSectorMatrixQuadratic
      centralPhysicalFiniteVacuumSectorOldBlockIndices
    apply finiteJointQuadratic_filter_eqv_trueBlock_of_zero_false
    intro index hindex
    exact Q'.eqv_of_eq
      (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_eq_zero_of_mem_new
        (w := w) (hw := hw) (base := base) (later := later)
        (half := half) hindex observable)
  · exact centralPhysicalFiniteVacuumSectorOldOldBlock_eqv_pulled
      (w := w) (hw := hw) (base := base) (later := later)
      (half := half) hcutoff observable

/-! ## 4. Arbitrary base coefficients contract in the same way -/

/-- An arbitrary base coefficient extended by the explicit finite inverse sum
vanishes on every genuinely new target coordinate. -/
theorem centralPhysicalFiniteVacuumSectorCoefficientExtension_eqv_zero_of_mem_new
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half target : Nat}
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorNewBlockIndices
        w hw base later half)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorCoefficientExtension
      w hw base later half coefficient target ≈ 0 := by
  have hnotEmbedded :=
    (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff.mp
      htarget).2
  unfold centralPhysicalFiniteVacuumSectorCoefficientExtension
  apply listQSum_eqv_zero_of_pointwise
  intro source hsource
  have hne : centralPhysicalFiniteCutoffIndexMap
      w hw base later half source ≠ target := by
    intro heq
    apply hnotEmbedded
    unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
    exact List.mem_map.mpr ⟨source, hsource, heq⟩
  rw [if_neg hne]
  exact Q'.eqv_refl 0

/-- The new-coordinate weighted mean of an arbitrary coefficient extension
vanishes. -/
theorem centralPhysicalFiniteVacuumSectorCoefficientExtension_newMean_eqv_zero
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') :
    listQSum
        (fun index =>
          centralPhysicalFiniteVacuumSectorCoefficientExtension
              w hw base later half coefficient index *
            centralPhysicalFiniteWeight w hw later half index)
        (centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half) ≈ 0 := by
  apply listQSum_eqv_zero_of_pointwise
  intro index hindex
  refine Q'.eqv_trans _ (0 *
      centralPhysicalFiniteWeight w hw later half index) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (centralPhysicalFiniteVacuumSectorCoefficientExtension_eqv_zero_of_mem_new
        hindex coefficient)
  · exact Q'.zero_mul_eqv _

/-- The new-coordinate diagonal contribution of an arbitrary coefficient
extension vanishes. -/
theorem centralPhysicalFiniteVacuumSectorCoefficientExtension_newDiagonal_eqv_zero
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat) (coefficient : Nat → Q') :
    listQSum
        (fun index =>
          (centralPhysicalFiniteVacuumSectorCoefficientExtension
              w hw base later half coefficient index *
            centralPhysicalFiniteVacuumSectorCoefficientExtension
              w hw base later half coefficient index) *
            centralPhysicalFiniteWeight w hw later half index)
        (centralPhysicalFiniteVacuumSectorNewBlockIndices
          w hw base later half) ≈ 0 := by
  apply listQSum_eqv_zero_of_pointwise
  intro index hindex
  have hzero :=
    centralPhysicalFiniteVacuumSectorCoefficientExtension_eqv_zero_of_mem_new
      hindex coefficient
  refine Q'.eqv_trans _ (0 *
      centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half coefficient index *
      centralPhysicalFiniteWeight w hw later half index) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hzero)
  · exact Q'.eqv_trans _
      (0 * centralPhysicalFiniteWeight w hw later half index) _
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.zero_mul_eqv _))
      (Q'.zero_mul_eqv _)

/-- The full later-component mean of an arbitrary coefficient extension is
exactly its pulled base-component mean. -/
theorem centralPhysicalFiniteVacuumSectorCoefficientExtensionMean_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorWeightedMean w hw later half
        (centralPhysicalFiniteVacuumSectorCoefficientExtension
          w hw base later half coefficient) ≈
      centralPhysicalFinitePulledVacuumSectorWeightedMean
        w hw base later half coefficient := by
  have hsplit := centralPhysicalFiniteVacuumSectorWeightedMean_old_add_new
    w hw base later half
      (centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half coefficient)
  have hold :=
    centralPhysicalFiniteVacuumSectorCoefficientExtension_oldMean_eqv_pulled
      (w := w) (hw := hw) (base := base) (later := later)
      (half := half) hcutoff coefficient
  have hnew :=
    centralPhysicalFiniteVacuumSectorCoefficientExtension_newMean_eqv_zero
      w hw base later half coefficient
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.eqv_trans _
      (centralPhysicalFinitePulledVacuumSectorWeightedMean
        w hw base later half coefficient + 0) _
      (Q'.add_eqv_congr' hold hnew)
      (Q'.eqv_of_eq (Q'.add_zero' _)))

/-- The full later-component diagonal form of an arbitrary coefficient
extension is exactly its pulled base-component diagonal form. -/
theorem centralPhysicalFiniteVacuumSectorCoefficientExtensionDiagonal_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw later half
        (centralPhysicalFiniteVacuumSectorCoefficientExtension
          w hw base later half coefficient) ≈
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w hw base later half coefficient := by
  have hsplit := centralPhysicalFiniteVacuumSectorDiagonalQuadratic_old_add_new
    w hw base later half
      (centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half coefficient)
  have hold :=
    centralPhysicalFiniteVacuumSectorCoefficientExtension_oldDiagonal_eqv_pulled
      (w := w) (hw := hw) (base := base) (later := later)
      (half := half) hcutoff coefficient
  have hnew :=
    centralPhysicalFiniteVacuumSectorCoefficientExtension_newDiagonal_eqv_zero
      w hw base later half coefficient
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.eqv_trans _
      (centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w hw base later half coefficient + 0) _
      (Q'.add_eqv_congr' hold hnew)
      (Q'.eqv_of_eq (Q'.add_zero' _)))

/-- The full later-component reflected form of an arbitrary coefficient
extension is exactly its pulled base-component reflected form. -/
theorem centralPhysicalFiniteVacuumSectorCoefficientExtensionMatrix_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic w hw later half
        (centralPhysicalFiniteVacuumSectorCoefficientExtension
          w hw base later half coefficient) ≈
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w hw base later half coefficient := by
  refine Q'.eqv_trans _
    (finiteJointBlock
      (centralPhysicalFiniteVacuumSectorOldBlockIndices
        w hw base later half)
      (centralPhysicalFiniteVacuumSectorOldBlockIndices
        w hw base later half)
      (centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half coefficient)
      (centralPhysicalFiniteKernel w hw later half)) _ ?_ ?_
  · unfold centralPhysicalFiniteVacuumSectorMatrixQuadratic
      centralPhysicalFiniteVacuumSectorOldBlockIndices
    apply finiteJointQuadratic_filter_eqv_trueBlock_of_zero_false
    intro index hindex
    exact centralPhysicalFiniteVacuumSectorCoefficientExtension_eqv_zero_of_mem_new
      hindex coefficient
  · exact centralPhysicalFiniteVacuumSectorCoefficientExtension_oldMatrix_eqv_pulled
      (w := w) (hw := hw) (base := base) (later := later)
      (half := half) hcutoff coefficient

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction.centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_eq_zero_of_mem_new
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction.centralPhysicalFiniteVacuumSectorZeroExtension_oldNew_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction.centralPhysicalFiniteVacuumSectorZeroExtension_newOld_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction.centralPhysicalFiniteVacuumSectorZeroExtension_newNew_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction.centralPhysicalFiniteVacuumSectorZeroExtensionWeightedMean_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction.centralPhysicalFiniteVacuumSectorZeroExtensionDiagonal_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction.centralPhysicalFiniteVacuumSectorZeroExtensionMatrix_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction.centralPhysicalFiniteVacuumSectorCoefficientExtension_eqv_zero_of_mem_new
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction.centralPhysicalFiniteVacuumSectorCoefficientExtensionMean_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction.centralPhysicalFiniteVacuumSectorCoefficientExtensionDiagonal_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction.centralPhysicalFiniteVacuumSectorCoefficientExtensionMatrix_eqv_pulled
