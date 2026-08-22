/-
# Contracting vacuum-sector coefficients inside the full physical carrier

The canonical LDL certificates act on every index of the finite positive-row
carrier, while the growing-sector construction first expressed its forms on
the canonical vacuum component.  The explicit coefficient extension is zero
away from the embedded base component.  Hence it is also zero outside the
later vacuum component, and the full indexed mean, diagonal form, and matrix
quadratic contract exactly to the already constructed pulled forms.

This file supplies that missing exact carrier bridge.  It constructs no LDL
family, no strict rate, no thermodynamic or continuum limit, and no Clay
conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorZeroExtensionContraction
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive finite-list extension algebra -/

private theorem rangeNodupLocal :
    ∀ bound : Nat, (List.range bound).Nodup
  | 0 => List.nodup_nil
  | bound + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine
        ⟨rangeNodupLocal bound,
          List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩,
          ?_⟩
      intro left hleft right hright heq
      have hrightEq := List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl bound) (List.mem_range.mp hleft)

private theorem listQSum_perm_local {A : Type}
    (value : A → Q') :
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
        (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)) ?_
      exact Q'.add_assoc_eqv _ _ _
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (listQSum_perm_local value hleft)
        (listQSum_perm_local value hright)

private theorem listQSum_eq_filter_of_zero_local
    {A : Type} (value : A → Q') (test : A → Bool) :
    ∀ source : List A,
      (∀ item, item ∈ source → test item = false →
        value item ≈ 0) →
      listQSum value source ≈
        listQSum value (source.filter test)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      have htail :
          ∀ item, item ∈ tail → test item = false →
            value item ≈ 0 := by
        intro item hitem htest
        exact hzero item (List.mem_cons_of_mem head hitem) htest
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum value (tail.filter test)) _
            (Q'.add_eqv_congr'
              (hzero head List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero_local
                value test tail htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local
              value test tail htail)

private theorem listQSum_eqv_zero_of_pointwise_local
    {A : Type} (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → value item ≈ 0) →
      listQSum value items ≈ 0
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      refine Q'.eqv_trans _ (0 + 0) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (hzero head List.mem_cons_self)
          (listQSum_eqv_zero_of_pointwise_local value tail
            (fun item hitem =>
              hzero item (List.mem_cons_of_mem head hitem)))
      · exact Q'.eqv_of_eq (Q'.zero_add' 0)

private theorem mul_eqv_congr_local
    {a b c d : Q'} (hac : a ≈ c) (hbd : b ≈ d) :
    a * b ≈ c * d :=
  Q'.eqv_trans _ (c * b) _
    (Q'.mul_eqv_congr_right _ _ _ hac)
    (Q'.mul_eqv_congr_left _ _ _ hbd)

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
      have hheadRight : head ∈ right :=
        (hmem head).1 List.mem_cons_self
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
          have hy := (hmem item).1
            (List.mem_cons_of_mem head hitem)
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

private theorem listQSum_extension_eq
    {A : Type} [DecidableEq A]
    (value : A → Q') (small large : List A)
    (hsmall : small.Nodup) (hlarge : large.Nodup)
    (hsubset : ∀ item, item ∈ small → item ∈ large)
    (hzero : ∀ item, item ∈ large → item ∉ small →
      value item ≈ 0) :
    listQSum value large ≈ listQSum value small := by
  let oldTest : A → Bool := fun item => decide (item ∈ small)
  refine Q'.eqv_trans _
    (listQSum value (large.filter oldTest)) _ ?_ ?_
  · apply listQSum_eq_filter_of_zero_local
    intro item hitem htest
    apply hzero item hitem
    simpa only [oldTest, decide_eq_false_iff_not] using htest
  · apply listQSum_perm_local
    apply perm_of_nodup_mem_iff_local
    · exact List.filter_sublist.nodup hlarge
    · exact hsmall
    · intro item
      simp only [List.mem_filter, oldTest, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨hsubset item h, h⟩

private theorem finiteJointBlock_perm_local
    {State : Type} (coefficient : State → Q')
    (joint : State → State → Q')
    {left left' right right' : List State}
    (hleft : left.Perm left') (hright : right.Perm right') :
    finiteJointBlock left right coefficient joint ≈
      finiteJointBlock left' right' coefficient joint := by
  let entry := fun leftState rightState =>
    (coefficient leftState * coefficient rightState) *
      joint leftState rightState
  refine Q'.eqv_trans _
    (finiteJointBlock left' right coefficient joint) _ ?_ ?_
  · unfold finiteJointBlock
    exact listQSum_perm_local
      (fun leftState => listQSum (entry leftState) right) hleft
  · unfold finiteJointBlock
    apply listQSum_congr_on
    intro leftState _hleftState
    exact listQSum_perm_local (entry leftState) hright

/-! ## 2. The exact full-carrier contraction -/

/-- The arbitrary base coefficient extension is zero at every target outside
the later canonical vacuum component. -/
theorem centralPhysicalFiniteVacuumSectorCoefficientExtension_eqv_zero_of_not_mem
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half target : Nat} (hcutoff : base ≤ later)
    (htarget : target ∉
      centralPhysicalFiniteVacuumSectorIndices w hw later half)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorCoefficientExtension
      w hw base later half coefficient target ≈ 0 := by
  unfold centralPhysicalFiniteVacuumSectorCoefficientExtension
  apply listQSum_eqv_zero_of_pointwise_local
  intro source hsource
  have hne : centralPhysicalFiniteCutoffIndexMap
      w hw base later half source ≠ target := by
    intro heq
    apply htarget
    rw [← heq]
    exact centralPhysicalFiniteVacuumSectorIndexMap_mem hcutoff hsource
  rw [if_neg hne]
  exact Q'.eqv_refl 0

/-- The full positive-carrier indexed mean of the coefficient extension is
exactly the pulled base-component mean. -/
theorem centralPhysicalFiniteFullCarrierCoefficientExtensionMean_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (coefficient : Nat → Q') :
    finiteWeightedMean
        (centralPhysicalFiniteCarrierSize w hw later half)
        (centralPhysicalFiniteWeight w hw later half)
        (centralPhysicalFiniteVacuumSectorCoefficientExtension
          w hw base later half coefficient) ≈
      centralPhysicalFinitePulledVacuumSectorWeightedMean
        w hw base later half coefficient := by
  refine Q'.eqv_trans _
    (centralPhysicalFiniteVacuumSectorWeightedMean w hw later half
      (centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half coefficient)) _ ?_ ?_
  · unfold finiteWeightedMean
      centralPhysicalFiniteVacuumSectorWeightedMean
    apply listQSum_extension_eq
    · exact centralPhysicalFiniteVacuumSectorIndices_nodup
        w hw later half
    · exact rangeNodupLocal _
    · intro index hindex
      exact List.mem_range.mpr
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w hw later half hindex)
    · intro index _hindex hnot
      refine Q'.eqv_trans _ (0 *
        centralPhysicalFiniteWeight w hw later half index) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (centralPhysicalFiniteVacuumSectorCoefficientExtension_eqv_zero_of_not_mem
            hcutoff hnot coefficient)
      · exact Q'.zero_mul_eqv _
  · exact
      centralPhysicalFiniteVacuumSectorCoefficientExtensionMean_eqv_pulled
        hcutoff coefficient

/-- The full positive-carrier indexed diagonal form of the coefficient
extension is exactly the pulled base-component diagonal form. -/
theorem centralPhysicalFiniteFullCarrierCoefficientExtensionDiagonal_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (coefficient : Nat → Q') :
    finiteDiagonalQuadratic
        (centralPhysicalFiniteCarrierSize w hw later half)
        (centralPhysicalFiniteWeight w hw later half)
        (centralPhysicalFiniteVacuumSectorCoefficientExtension
          w hw base later half coefficient) ≈
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w hw base later half coefficient := by
  refine Q'.eqv_trans _
    (centralPhysicalFiniteVacuumSectorDiagonalQuadratic w hw later half
      (centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half coefficient)) _ ?_ ?_
  · unfold finiteDiagonalQuadratic
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    apply listQSum_extension_eq
    · exact centralPhysicalFiniteVacuumSectorIndices_nodup
        w hw later half
    · exact rangeNodupLocal _
    · intro index hindex
      exact List.mem_range.mpr
        (centralPhysicalFiniteVacuumSectorIndex_lt
          w hw later half hindex)
    · intro index _hindex hnot
      have hzero :=
        centralPhysicalFiniteVacuumSectorCoefficientExtension_eqv_zero_of_not_mem
          hcutoff hnot coefficient
      refine Q'.eqv_trans _
        ((0 * 0) * centralPhysicalFiniteWeight w hw later half index) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (mul_eqv_congr_local hzero hzero)
      · exact Q'.eqv_trans _
          (0 * centralPhysicalFiniteWeight w hw later half index) _
          (Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv 0))
          (Q'.zero_mul_eqv _)
  · exact
      centralPhysicalFiniteVacuumSectorCoefficientExtensionDiagonal_eqv_pulled
        hcutoff coefficient

/-- The full positive-carrier indexed matrix quadratic of the coefficient
extension is exactly the pulled base-component reflected form. -/
theorem centralPhysicalFiniteFullCarrierCoefficientExtensionMatrix_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic
        (centralPhysicalFiniteCarrierSize w hw later half)
        (centralPhysicalFiniteKernel w hw later half)
        (centralPhysicalFiniteVacuumSectorCoefficientExtension
          w hw base later half coefficient) ≈
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w hw base later half coefficient := by
  let carrier := List.range
    (centralPhysicalFiniteCarrierSize w hw later half)
  let sector := centralPhysicalFiniteVacuumSectorIndices w hw later half
  let sectorB : Nat → Bool := fun index => decide (index ∈ sector)
  let extended := centralPhysicalFiniteVacuumSectorCoefficientExtension
    w hw base later half coefficient
  have hzero : ∀ index,
      index ∈ carrier.filter (fun item => !(sectorB item)) →
      extended index ≈ 0 := by
    intro index hindex
    have hparts := List.mem_filter.mp hindex
    apply centralPhysicalFiniteVacuumSectorCoefficientExtension_eqv_zero_of_not_mem
      hcutoff
    have hfalse : decide (index ∈ sector) = false := by
      have hnotDecision := hparts.2
      change (!decide (index ∈ sector)) = true at hnotDecision
      cases hdecision : decide (index ∈ sector) with
      | false => rfl
      | true =>
          rw [hdecision] at hnotDecision
          cases hnotDecision
    simpa only [sector, decide_eq_false_iff_not] using hfalse
  have hfilteredPerm : (carrier.filter sectorB).Perm sector := by
    apply perm_of_nodup_mem_iff_local
    · exact List.filter_sublist.nodup (rangeNodupLocal _)
    · exact centralPhysicalFiniteVacuumSectorIndices_nodup
        w hw later half
    · intro index
      simp only [List.mem_filter, sectorB, decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · intro hsector
        exact ⟨List.mem_range.mpr
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w hw later half hsector), hsector⟩
  refine Q'.eqv_trans _
    (finiteJointBlock
      (carrier.filter sectorB) (carrier.filter sectorB)
      extended (centralPhysicalFiniteKernel w hw later half)) _ ?_ ?_
  · unfold finiteMatrixQuadratic carrier
    exact finiteJointQuadratic_filter_eqv_trueBlock_of_zero_false
      _ _ _ _ hzero
  · refine Q'.eqv_trans _
      (centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw later half extended) _ ?_ ?_
    · unfold centralPhysicalFiniteVacuumSectorMatrixQuadratic
      exact finiteJointBlock_perm_local extended
        (centralPhysicalFiniteKernel w hw later half)
        hfilteredPerm hfilteredPerm
    · exact
        centralPhysicalFiniteVacuumSectorCoefficientExtensionMatrix_eqv_pulled
          hcutoff coefficient

/-! ## 3. The moving head-centered specialization -/

/-- The moving head-centered coefficient, extended by zero, is exactly
centered on the full positive carrier seen by the LDL certificate. -/
theorem centralPhysicalFiniteFullCarrierHeadCenteredExtension_meanZero
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (coefficient : Nat → Q') :
    finiteWeightedMean
        (centralPhysicalFiniteCarrierSize w hw later half)
        (centralPhysicalFiniteWeight w hw later half)
        (centralPhysicalFiniteVacuumSectorCoefficientExtension
          w hw base later half
          (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
            w hw base later half coefficient)) ≈ 0 := by
  exact Q'.eqv_trans _ _ _
    (centralPhysicalFiniteFullCarrierCoefficientExtensionMean_eqv_pulled
      hcutoff
      (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient))
    (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_meanZero
      w hw base later half coefficient)

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction.centralPhysicalFiniteVacuumSectorCoefficientExtension_eqv_zero_of_not_mem
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction.centralPhysicalFiniteFullCarrierCoefficientExtensionMean_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction.centralPhysicalFiniteFullCarrierCoefficientExtensionDiagonal_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction.centralPhysicalFiniteFullCarrierCoefficientExtensionMatrix_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction.centralPhysicalFiniteFullCarrierHeadCenteredExtension_meanZero
