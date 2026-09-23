/-
# Finite BF4 sector tests read persistent coordinates

Pairing an arbitrary physical observable with a fixed canonical-sector
cylinder is a finite weighted sum of the observable's retained coordinates.
This is a same-cutoff algebraic identity; it introduces no limiting or
spectral hypothesis.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFiniteTestPairing

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFullCarrierContraction
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] centralPhysicalFiniteCarrierSize
  centralPhysicalFiniteIndexCarrier centralPhysicalFiniteVacuumSectorIndices
  centralPositiveHalfStates

private theorem rangeNodupLocal :
    ∀ bound : Nat, (List.range bound).Nodup
  | 0 => List.nodup_nil
  | bound + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine ⟨rangeNodupLocal bound,
        List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro left hleft right hright heq
      have hrightEq := List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl bound) (List.mem_range.mp hleft)

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (map : A → B) :
    ∀ items : List A,
      listQSum value (items.map map) =
        listQSum (fun item => value (map item)) items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value map tail]

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
      (∀ item, item ∈ source → test item = false → value item ≈ 0) →
      listQSum value source ≈ listQSum value (source.filter test)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      have htail : ∀ item, item ∈ tail → test item = false →
          value item ≈ 0 := by
        intro item hitem htest
        exact hzero item (List.mem_cons_of_mem head hitem) htest
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _ (0 + listQSum value (tail.filter test)) _
            (Q'.add_eqv_congr'
              (hzero head List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero_local value test tail htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local value test tail htail)

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
            (fun item hitem => hzero item (List.mem_cons_of_mem head hitem)))
      · exact Q'.eqv_of_eq (Q'.zero_add' 0)

private theorem perm_of_nodup_mem_iff_local {A : Type} :
    ∀ (left right : List A), left.Nodup → right.Nodup →
      (∀ item, item ∈ left ↔ item ∈ right) → left.Perm right
  | [], [], _, _, _ => List.Perm.nil
  | [], head :: tail, _, _, hmem => by
      have hfalse : head ∈ ([] : List A) := (hmem head).2 List.mem_cons_self
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
      have htailMem : ∀ item, item ∈ tail ↔ item ∈ before ++ after := by
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

private theorem listQSum_extension_eq
    {A : Type} [DecidableEq A]
    (value : A → Q') (small large : List A)
    (hsmall : small.Nodup) (hlarge : large.Nodup)
    (hsubset : ∀ item, item ∈ small → item ∈ large)
    (hzero : ∀ item, item ∈ large → item ∉ small → value item ≈ 0) :
    listQSum value large ≈ listQSum value small := by
  let oldTest : A → Bool := fun item => decide (item ∈ small)
  refine Q'.eqv_trans _ (listQSum value (large.filter oldTest)) _ ?_ ?_
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

private theorem extension_eqv_zero_of_not_mem_embedded
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half target : Nat}
    (hnot : target ∉ centralPhysicalFiniteEmbeddedVacuumSectorIndices
      w hw base later half)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorCoefficientExtension
        w hw base later half coefficient target ≈ 0 := by
  unfold centralPhysicalFiniteVacuumSectorCoefficientExtension
  apply listQSum_eqv_zero_of_pointwise_local
  intro source hsource
  have hne : centralPhysicalFiniteCutoffIndexMap
      w hw base later half source ≠ target := by
    intro heq
    apply hnot
    unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
    apply List.mem_map.mpr
    exact ⟨source, hsource, heq⟩
  rw [if_neg hne]
  exact Q'.eqv_refl 0

/-- At every common later cutoff, an arbitrary left observable paired with a
fixed sector presentation is exactly the finite sum of its retained
coordinates times the test coefficients and pulled stationary weights. -/
theorem weightedInner_linearObservable_eqv_coordinateSum
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half : Nat} (hcutoff : base ≤ later)
    (left : EdgeLabelling → Q') (testCoefficient : Nat → Q') :
    centralPhysicalWeightedInner w hw later half left
        (centralPhysicalFiniteVacuumSectorLinearObservable
          w hw base half testCoefficient).value ≈
      listQSum
        (fun index =>
          (left (centralPhysicalFiniteStateAt w hw base half index) *
              testCoefficient index) *
            centralPhysicalFinitePulledWeight
              w hw base later half index)
        (centralPhysicalFiniteVacuumSectorIndices w hw base half) := by
  let size := centralPhysicalFiniteCarrierSize w hw later half
  let leftCoefficient := centralPhysicalFiniteCoefficient
    w hw later half left
  let extended := centralPhysicalFiniteVacuumSectorCoefficientExtension
    w hw base later half testCoefficient
  let term := fun target =>
    (leftCoefficient target * extended target) *
      centralPhysicalFiniteWeight w hw later half target
  refine Q'.eqv_trans _ (listQSum term (List.range size)) _ ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
        (fun target =>
          centralPhysicalFiniteWeight w hw later half target *
            (leftCoefficient target *
              (centralPhysicalFiniteVacuumSectorLinearObservable
                w hw base half testCoefficient).value
                  (centralPhysicalFiniteStateAt w hw later half target)))
        (List.range size)) _ ?_ ?_
    · unfold centralPhysicalWeightedInner size leftCoefficient
        centralPhysicalFiniteCarrierSize centralPhysicalFiniteWeight centralPhysicalFiniteCoefficient
        centralPhysicalFiniteStateAt
      exact Q'.eqv_of_eq (Eq.symm (finiteIndexSum_eq_listQSum
        (centralPositiveHalfStates w hw later half) zeroEdgeLabelling
        (fun state => centralPhysicalRowMarginal w hw later half state *
          (left state *
            (centralPhysicalFiniteVacuumSectorLinearObservable
              w hw base half testCoefficient).value state))))
    apply listQSum_congr_on
    intro target htarget
    have htargetLt : target < size := List.mem_range.mp htarget
    have htest := centralPhysicalFiniteCoefficient_linearObservable_eqv_extension
      hcutoff testCoefficient htargetLt
    refine Q'.eqv_trans _
      (centralPhysicalFiniteWeight w hw later half target *
        (leftCoefficient target * extended target)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ htest)
    · exact Q'.mul_comm_eqv _ _
  · refine Q'.eqv_trans _
      (listQSum term
        (centralPhysicalFiniteEmbeddedVacuumSectorIndices
          w hw base later half)) _ ?_ ?_
    · apply listQSum_extension_eq
      · exact centralPhysicalFiniteEmbeddedVacuumSectorIndices_nodup hcutoff
      · exact rangeNodupLocal _
      · intro target htarget
        unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices at htarget
        rcases List.mem_map.mp htarget with ⟨source, hsource, hsourceMap⟩
        subst target
        have htargetLt := centralPhysicalFiniteCutoffIndexMap_lt hcutoff
          (centralPhysicalFiniteVacuumSectorIndex_lt
            w hw base half hsource)
        exact List.mem_range.mpr htargetLt
      · intro target _htarget hnot
        refine Q'.eqv_trans _
          ((leftCoefficient target * 0) *
            centralPhysicalFiniteWeight w hw later half target) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_left _ _ _
              (extension_eqv_zero_of_not_mem_embedded
                hnot testCoefficient))
        · exact Q'.eqv_trans _
            (0 * centralPhysicalFiniteWeight w hw later half target) _
            (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _))
            (Q'.zero_mul_eqv _)
    · unfold centralPhysicalFiniteEmbeddedVacuumSectorIndices
      rw [listQSum_map_local]
      apply listQSum_congr_on
      intro index hindex
      unfold term leftCoefficient extended
      have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
        w hw base half hindex
      refine Q'.eqv_trans _
        ((centralPhysicalFiniteCoefficient w hw later half left
            (centralPhysicalFiniteCutoffIndexMap w hw base later half index) *
          testCoefficient index) *
          centralPhysicalFiniteWeight w hw later half
            (centralPhysicalFiniteCutoffIndexMap w hw base later half index)) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _
            (centralPhysicalFiniteVacuumSectorCoefficientExtension_on_map
              hcutoff hindex testCoefficient))
      · unfold centralPhysicalFiniteCoefficient centralPhysicalFinitePulledWeight
        rw [centralPhysicalFiniteStateAt_cutoffIndexMap_eq hcutoff hindexLt]
        exact Q'.eqv_refl _

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFiniteTestPairing

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFiniteTestPairing.weightedInner_linearObservable_eqv_coordinateSum
