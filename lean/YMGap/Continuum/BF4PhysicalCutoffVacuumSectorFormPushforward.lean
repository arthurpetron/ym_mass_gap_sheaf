/-
# Exact pushforward of embedded physical vacuum-sector forms

The target-ordered old block from the old/new decomposition is shown here to
be a literal permutation of the explicit image of the base vacuum component.
The key constructive fact is injectivity of the cutoff index map on the old
component, obtained from preservation of literal states and duplicate-freeness
of the positive carrier.

For a coefficient defined by a physical observable, an explicit target
zero-extension agrees with the base coefficient on every embedded image.
Consequently the old-block mean, diagonal form, and old-old matrix block are
exactly the source-indexed pulled forms whose cutoff limits were constructed
previously.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive injectivity and the old-block permutation -/

private theorem nodup_map_of_injective_on_local
    {A B : Type} (map : A → B) :
    ∀ (items : List A), items.Nodup →
      (∀ left, left ∈ items → ∀ right, right ∈ items →
        map left = map right → left = right) →
      (items.map map).Nodup
  | [], _, _ => List.nodup_nil
  | head :: tail, hnodup, hinjective => by
      have hparts := List.nodup_cons.mp hnodup
      refine List.nodup_cons.mpr ⟨?_,
        nodup_map_of_injective_on_local map tail hparts.2
          (fun left hleft right hright =>
            hinjective left (List.mem_cons_of_mem head hleft)
              right (List.mem_cons_of_mem head hright))⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨other, hother, hmap⟩
      have heq := hinjective head List.mem_cons_self other
        (List.mem_cons_of_mem head hother) hmap.symm
      exact hparts.1 (heq ▸ hother)

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
      obtain ⟨before, after, hsplit⟩ :=
        List.append_of_mem hheadRight
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

/-- The explicit cutoff index map is injective when restricted to the old
canonical component. -/
theorem centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half left right : Nat}
    (hcutoff : base ≤ later)
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (hmap : centralPhysicalFiniteCutoffIndexMap
        w hw base later half left =
      centralPhysicalFiniteCutoffIndexMap
        w hw base later half right) :
    left = right := by
  have hleftLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw base half hleft
  have hrightLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw base half hright
  have hstate :
      centralPhysicalFiniteStateAt w hw base half left =
        centralPhysicalFiniteStateAt w hw base half right := by
    calc
      centralPhysicalFiniteStateAt w hw base half left =
          centralPhysicalFiniteStateAt w hw later half
            (centralPhysicalFiniteCutoffIndexMap
              w hw base later half left) :=
        (centralPhysicalFiniteStateAt_cutoffIndexMap_eq
          hcutoff hleftLt).symm
      _ = centralPhysicalFiniteStateAt w hw later half
            (centralPhysicalFiniteCutoffIndexMap
              w hw base later half right) := by rw [hmap]
      _ = centralPhysicalFiniteStateAt w hw base half right :=
        centralPhysicalFiniteStateAt_cutoffIndexMap_eq
          hcutoff hrightLt
  let states := centralPositiveHalfStates w hw base half
  have hoptions : states[left]? = states[right]? := by
    rw [List.getElem?_eq_getElem hleftLt,
      List.getElem?_eq_getElem hrightLt]
    apply congrArg some
    change states.getD left zeroEdgeLabelling =
      states.getD right zeroEdgeLabelling at hstate
    rw [← List.getElem_eq_getD
        (l := states) (i := left) (h := hleftLt) zeroEdgeLabelling,
      ← List.getElem_eq_getD
        (l := states) (i := right) (h := hrightLt) zeroEdgeLabelling]
      at hstate
    exact hstate
  exact List.getElem?_inj hleftLt
    (centralPositiveHalfStates_nodup w hw base half) hoptions

/-- The explicit image of the old canonical component has no duplicate
target indices. -/
theorem centralPhysicalFiniteEmbeddedVacuumSectorIndices_nodup
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later) :
    (centralPhysicalFiniteEmbeddedVacuumSectorIndices
      w hw base later half).Nodup := by
  unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
  apply nodup_map_of_injective_on_local
  · exact centralPhysicalFiniteVacuumSectorIndices_nodup
      w hw base half
  · intro left hleft right hright hmap
    exact centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector
      hcutoff hleft hright hmap

/-- The target-ordered old block is a literal permutation of the explicit
mapped base component. -/
theorem centralPhysicalFiniteVacuumSectorOldBlockIndices_perm_embedded
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later) :
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
        w hw base later half).Perm
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw base later half) := by
  apply perm_of_nodup_mem_iff_local
  · exact centralPhysicalFiniteVacuumSectorOldBlockIndices_nodup
      w hw base later half
  · exact centralPhysicalFiniteEmbeddedVacuumSectorIndices_nodup hcutoff
  · intro index
    exact mem_centralPhysicalFiniteVacuumSectorOldBlockIndices_iff
      hcutoff

/-! ## 2. Observable coefficients and exact old-block pushforward -/

/-- A physical observable on the later component, set to zero away from the
embedded image of the base component. -/
def centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
    (w : Q') (hw : (0 : Q') ≤ w)
    (base later half : Nat)
    (observable : EdgeLabelling → Q') (index : Nat) : Q' :=
  if centralPhysicalFiniteEmbeddedVacuumSectorB
      w hw base later half index then
    observable (centralPhysicalFiniteStateAt w hw later half index)
  else 0

/-- The zero extension agrees exactly with the base observable coefficient on
each embedded base-component index. -/
theorem centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_on_map
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hcutoff : base ≤ later)
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half)
    (observable : EdgeLabelling → Q') :
    centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
        w hw base later half observable
        (centralPhysicalFiniteCutoffIndexMap
          w hw base later half index) =
      centralPhysicalFiniteCoefficient
        w hw base half observable index := by
  have himage : centralPhysicalFiniteCutoffIndexMap
      w hw base later half index ∈
      centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw base later half := by
    unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
    exact List.mem_map.mpr ⟨index, hindex, rfl⟩
  have htest : centralPhysicalFiniteEmbeddedVacuumSectorB
      w hw base later half
        (centralPhysicalFiniteCutoffIndexMap
          w hw base later half index) = true := by
    unfold centralPhysicalFiniteEmbeddedVacuumSectorB
    exact decide_eq_true himage
  unfold centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
    centralPhysicalFiniteCoefficient
  rw [htest]
  exact congrArg observable
    (centralPhysicalFiniteStateAt_cutoffIndexMap_eq hcutoff
      (centralPhysicalFiniteVacuumSectorIndex_lt
        w hw base half hindex))

/-- The target old-block weighted mean of the zero extension is exactly the
source-indexed pulled vacuum-sector mean. -/
theorem centralPhysicalFiniteVacuumSectorOldBlockWeightedMean_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (observable : EdgeLabelling → Q') :
    listQSum
        (fun target =>
          centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
              w hw base later half observable target *
            centralPhysicalFiniteWeight w hw later half target)
        (centralPhysicalFiniteVacuumSectorOldBlockIndices
          w hw base later half) ≈
      centralPhysicalFinitePulledVacuumSectorWeightedMean
        w hw base later half
        (centralPhysicalFiniteCoefficient w hw base half observable) := by
  let targetValue := fun target =>
    centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
        w hw base later half observable target *
      centralPhysicalFiniteWeight w hw later half target
  let sourceIndices :=
    centralPhysicalFiniteVacuumSectorIndices w hw base half
  let map := centralPhysicalFiniteCutoffIndexMap
    w hw base later half
  refine Q'.eqv_trans _
    (listQSum targetValue
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw base later half)) _ ?_ ?_
  · exact listQSum_perm_local targetValue
      (centralPhysicalFiniteVacuumSectorOldBlockIndices_perm_embedded
        hcutoff)
  · unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
    rw [listQSum_map_local]
    unfold centralPhysicalFinitePulledVacuumSectorWeightedMean
    apply listQSum_congr_on
    intro index hindex
    dsimp [targetValue]
    rw [centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_on_map
      hcutoff hindex observable]
    unfold centralPhysicalFinitePulledWeight
    exact Q'.eqv_refl _

/-- The target old-block diagonal norm of the zero extension is exactly the
source-indexed pulled vacuum-sector diagonal quadratic. -/
theorem centralPhysicalFiniteVacuumSectorOldBlockDiagonal_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (observable : EdgeLabelling → Q') :
    listQSum
        (fun target =>
          (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
              w hw base later half observable target *
            centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
              w hw base later half observable target) *
            centralPhysicalFiniteWeight w hw later half target)
        (centralPhysicalFiniteVacuumSectorOldBlockIndices
          w hw base later half) ≈
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w hw base later half
        (centralPhysicalFiniteCoefficient w hw base half observable) := by
  let targetValue := fun target =>
    (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
        w hw base later half observable target *
      centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
        w hw base later half observable target) *
      centralPhysicalFiniteWeight w hw later half target
  refine Q'.eqv_trans _
    (listQSum targetValue
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw base later half)) _ ?_ ?_
  · exact listQSum_perm_local targetValue
      (centralPhysicalFiniteVacuumSectorOldBlockIndices_perm_embedded
        hcutoff)
  · unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
    rw [listQSum_map_local]
    unfold centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
    apply listQSum_congr_on
    intro index hindex
    dsimp [targetValue]
    rw [centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_on_map
      hcutoff hindex observable]
    unfold centralPhysicalFinitePulledWeight
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

/-- The target old-old reflected block of the zero extension is exactly the
source-indexed pulled vacuum-sector matrix quadratic. -/
theorem centralPhysicalFiniteVacuumSectorOldOldBlock_eqv_pulled
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (observable : EdgeLabelling → Q') :
    finiteJointBlock
        (centralPhysicalFiniteVacuumSectorOldBlockIndices
          w hw base later half)
        (centralPhysicalFiniteVacuumSectorOldBlockIndices
          w hw base later half)
        (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
          w hw base later half observable)
        (centralPhysicalFiniteKernel w hw later half) ≈
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w hw base later half
        (centralPhysicalFiniteCoefficient w hw base half observable) := by
  have hperm :
      (centralPhysicalFiniteVacuumSectorOldBlockIndices
          w hw base later half).Perm
        (centralPhysicalFiniteEmbeddedVacuumSectorIndices
          w hw base later half) :=
    centralPhysicalFiniteVacuumSectorOldBlockIndices_perm_embedded
      (w := w) (hw := hw) (base := base) (later := later)
      (half := half) hcutoff
  refine Q'.eqv_trans _
    (finiteJointBlock
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw base later half)
      (centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw base later half)
      (centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient
        w hw base later half observable)
      (centralPhysicalFiniteKernel w hw later half)) _ ?_ ?_
  · exact finiteJointBlock_perm_local hperm hperm _ _
  · unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
    unfold centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
    apply finiteJointBlock_map_eqv_local
    intro left hleft right hright
    rw [centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_on_map
        hcutoff hleft observable,
      centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_on_map
        hcutoff hright observable]
    exact Q'.eqv_refl _

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward.centralPhysicalFiniteCutoffIndexMap_injective_on_vacuumSector
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward.centralPhysicalFiniteVacuumSectorOldBlockIndices_perm_embedded
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward.centralPhysicalFiniteVacuumSectorZeroExtensionCoefficient_on_map
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward.centralPhysicalFiniteVacuumSectorOldBlockWeightedMean_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward.centralPhysicalFiniteVacuumSectorOldBlockDiagonal_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward.centralPhysicalFiniteVacuumSectorOldOldBlock_eqv_pulled
