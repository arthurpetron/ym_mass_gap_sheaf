/-
# Canonical finite-form presentation of the cutoff-two vacuum gap

The exact normalized cutoff-two gap is initially stated in the stored
65-state table ordering.  The cutoff-limit architecture instead uses the
canonical root-component index list and its named weighted mean, diagonal,
and reflected matrix forms.  This module proves that the two finite
presentations are related by an exact permutation and transports the strict
`49/50` estimate to the canonical forms for every literal physical
observable.

This is a coordinate bridge at cutoff two only.  It constructs no cofinal
all-cutoff certificate, thermodynamic or continuum limit, or Clay theorem.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumNormalizedGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteListIndexQuadraticBridge
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private abbrev cutoffTwoStrictRate : Q' :=
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap.cutoffTwoSectorRate49Over50

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

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (map : A → B) :
    ∀ items : List A,
      listQSum value (items.map map) =
        listQSum (fun item => value (map item)) items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value map tail]

private theorem listQSum_ite_single_local
    {A : Type} [DecidableEq A] (selected : A) (value : A → Q') :
    ∀ items : List A,
      items.Nodup → selected ∈ items →
      listQSum
          (fun item => if item = selected then value item else 0)
          items ≈
        value selected
  | [], _hnodup, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum]
        have htailZero :
            listQSum
                (fun item => if item = selected then value item else 0)
                tail ≈ 0 := by
          refine Q'.eqv_trans _
            (listQSum (fun _item => (0 : Q')) tail) _ ?_ ?_
          · apply listQSum_congr_on
            intro item hitem
            rw [if_neg]
            · exact Q'.eqv_refl 0
            intro heq
            exact hparts.1 (heq ▸ hitem)
          · exact listQSum_zero tail
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr_left _ _ _ htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hne : head ≠ selected := by
          intro heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, if_neg hne]
        exact Q'.eqv_trans _ (0 + value selected) _
          (Q'.add_eqv_congr_left _ _ _
            (listQSum_ite_single_local selected value tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' _))

private theorem mul_eqv_congr_local {a b c d : Q'}
    (hac : a ≈ c) (hbd : b ≈ d) : a * b ≈ c * d :=
  Q'.eqv_trans _ (c * b) _
    (Q'.mul_eqv_congr_right _ _ b hac)
    (Q'.mul_eqv_congr_left c _ _ hbd)

private theorem finiteJointQuadratic_perm_local
    {State : Type} (coefficient : State → Q')
    (joint : State → State → Q') {left right : List State}
    (hperm : left.Perm right) :
    finiteJointQuadratic left coefficient joint ≈
      finiteJointQuadratic right coefficient joint := by
  unfold finiteJointQuadratic
  let row := fun source => listQSum
    (fun target =>
      (coefficient source * coefficient target) * joint source target)
    left
  refine Q'.eqv_trans _
    (listQSum
      (fun source => listQSum
        (fun target =>
          (coefficient source * coefficient target) * joint source target)
        right)
      left) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _hsource
    exact listQSum_perm_local _ hperm
  · exact listQSum_perm_local _ hperm

private theorem finiteJointQuadratic_map_local
    {A B : Type} (items : List A) (map : A → B)
    (coefficient : B → Q') (joint : B → B → Q') :
    finiteJointQuadratic (items.map map) coefficient joint =
      finiteJointQuadratic items
        (fun item => coefficient (map item))
        (fun left right => joint (map left) (map right)) := by
  unfold finiteJointQuadratic
  rw [listQSum_map_local]
  apply congrArg (listQSum · items)
  funext left
  rw [listQSum_map_local]

/-! ## 1. Exact permutation of the two canonical presentations -/

theorem centralPhysicalFiniteStateAt_injective_on_vacuumSector
    {w : Q'} {hw : (0 : Q') ≤ w} {K half left right : Nat}
    (hleft : left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (hright : right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K half)
    (hstate : centralPhysicalFiniteStateAt w hw K half left =
      centralPhysicalFiniteStateAt w hw K half right) :
    left = right := by
  have hleftLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw K half hleft
  have hrightLt := centralPhysicalFiniteVacuumSectorIndex_lt
    w hw K half hright
  let states := centralPositiveHalfStates w hw K half
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
    (centralPositiveHalfStates_nodup w hw K half) hoptions

theorem centralPhysicalFiniteVacuumSectorStates_nodup
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat) :
    (centralPhysicalFiniteVacuumSectorStates w hw K half).Nodup := by
  unfold centralPhysicalFiniteVacuumSectorStates
  apply nodup_map_of_injective_on_local
  · exact centralPhysicalFiniteVacuumSectorIndices_nodup w hw K half
  · intro left hleft right hright hstate
    exact centralPhysicalFiniteStateAt_injective_on_vacuumSector
      hleft hright hstate

/-- The canonical root-component state list and the stored 65-state table
have the same entries with multiplicity one. -/
theorem cutoffTwoCanonicalVacuumSectorStates_perm :
    (centralPhysicalFiniteVacuumSectorStates cutoffTwoHalfCoupling
        (by decide) 2 0).Perm cutoffTwoCubeSectorStates := by
  apply perm_of_nodup_mem_iff_local
  · exact centralPhysicalFiniteVacuumSectorStates_nodup
      cutoffTwoHalfCoupling (by decide) 2 0
  · exact cutoffTwoCubeSectorStates_nodup
  · exact centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff

/-! ## 2. Observable coefficients in the two coordinate systems -/

def cutoffTwoSectorObservableCoefficient
    (observable : EdgeLabelling → Q') (row : Nat) : Q' :=
  observable (cutoffTwoSectorStateAt row)

def cutoffTwoCanonicalVacuumObservableCoefficient
    (observable : EdgeLabelling → Q') (index : Nat) : Q' :=
  observable (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
    (by decide) 2 0 index)

private def cutoffTwoPhysicalWeightOnState
    (state : EdgeLabelling) : Q' :=
  centralPhysicalRowMarginal cutoffTwoHalfCoupling
    (by decide) 2 0 state

private def cutoffTwoPhysicalJointOnStates
    (left right : EdgeLabelling) : Q' :=
  centralNormalizedPhysicalReflectedKernel cutoffTwoHalfCoupling
    (by decide) 2 0 left right

theorem cutoffTwoSectorObservableWeightedMean_eqv_canonical
    (observable : EdgeLabelling → Q') :
    finiteWeightedMean 65 cutoffTwoSectorCanonicalPhysicalWeight
        (cutoffTwoSectorObservableCoefficient observable) ≈
      centralPhysicalFiniteVacuumSectorWeightedMean
        cutoffTwoHalfCoupling (by decide) 2 0
        (cutoffTwoCanonicalVacuumObservableCoefficient observable) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun row => observable (cutoffTwoSectorStateAt row) *
        cutoffTwoPhysicalWeightOnState (cutoffTwoSectorStateAt row))
      (List.range 65)) _ ?_ ?_
  · unfold finiteWeightedMean cutoffTwoSectorObservableCoefficient
    apply listQSum_congr_on
    intro row hrow
    exact Q'.mul_eqv_congr_left _ _ _
      (cutoffTwoSectorCanonicalPhysicalWeight_eqv_marginal
        (List.mem_range.mp hrow))
  · refine Q'.eqv_trans _
      (listQSum
        (fun state => observable state * cutoffTwoPhysicalWeightOnState state)
        cutoffTwoCubeSectorStates) _ ?_ ?_
    · exact Q'.eqv_of_eq
        (by
          have h := finiteIndexSum_eq_listQSum
            cutoffTwoCubeSectorStates zeroEdgeLabelling
            (fun state => observable state * cutoffTwoPhysicalWeightOnState state)
          rw [cutoffTwoCubeSectorStates_length] at h
          exact h)
    · refine Q'.eqv_trans _
        (listQSum
          (fun state => observable state * cutoffTwoPhysicalWeightOnState state)
          (centralPhysicalFiniteVacuumSectorStates cutoffTwoHalfCoupling
            (by decide) 2 0)) _
        (listQSum_perm_local _ cutoffTwoCanonicalVacuumSectorStates_perm.symm)
        ?_
      exact Q'.eqv_of_eq
        (by
          unfold centralPhysicalFiniteVacuumSectorWeightedMean
            centralPhysicalFiniteVacuumSectorStates
            cutoffTwoCanonicalVacuumObservableCoefficient
            cutoffTwoPhysicalWeightOnState centralPhysicalFiniteWeight
          exact listQSum_map_local
            (fun state => observable state *
              centralPhysicalRowMarginal cutoffTwoHalfCoupling
                (by decide) 2 0 state)
            (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
              (by decide) 2 0)
            (centralPhysicalFiniteVacuumSectorIndices
              cutoffTwoHalfCoupling (by decide) 2 0))

theorem cutoffTwoSectorObservableDiagonal_eqv_canonical
    (observable : EdgeLabelling → Q') :
    finiteDiagonalQuadratic 65 cutoffTwoSectorCanonicalPhysicalWeight
        (cutoffTwoSectorObservableCoefficient observable) ≈
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        cutoffTwoHalfCoupling (by decide) 2 0
        (cutoffTwoCanonicalVacuumObservableCoefficient observable) := by
  let value := fun state : EdgeLabelling =>
    (observable state * observable state) * cutoffTwoPhysicalWeightOnState state
  refine Q'.eqv_trans _
    (listQSum (fun row => value (cutoffTwoSectorStateAt row))
      (List.range 65)) _ ?_ ?_
  · unfold finiteDiagonalQuadratic cutoffTwoSectorObservableCoefficient value
    apply listQSum_congr_on
    intro row hrow
    exact Q'.mul_eqv_congr_left _ _ _
      (cutoffTwoSectorCanonicalPhysicalWeight_eqv_marginal
        (List.mem_range.mp hrow))
  · refine Q'.eqv_trans _ (listQSum value cutoffTwoCubeSectorStates) _ ?_ ?_
    · exact Q'.eqv_of_eq
        (by
          have h := finiteIndexSum_eq_listQSum
            cutoffTwoCubeSectorStates zeroEdgeLabelling value
          rw [cutoffTwoCubeSectorStates_length] at h
          exact h)
    · refine Q'.eqv_trans _
        (listQSum value
          (centralPhysicalFiniteVacuumSectorStates cutoffTwoHalfCoupling
            (by decide) 2 0)) _
        (listQSum_perm_local value
          cutoffTwoCanonicalVacuumSectorStates_perm.symm) ?_
      exact Q'.eqv_of_eq
        (by
          unfold centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            centralPhysicalFiniteVacuumSectorStates
            cutoffTwoCanonicalVacuumObservableCoefficient value
            cutoffTwoPhysicalWeightOnState centralPhysicalFiniteWeight
          exact listQSum_map_local
            (fun state => (observable state * observable state) *
              centralPhysicalRowMarginal cutoffTwoHalfCoupling
                (by decide) 2 0 state)
            (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
              (by decide) 2 0)
            (centralPhysicalFiniteVacuumSectorIndices
              cutoffTwoHalfCoupling (by decide) 2 0))

theorem cutoffTwoSectorObservableMatrix_eqv_canonical
    (observable : EdgeLabelling → Q') :
    finiteMatrixQuadratic 65 cutoffTwoSectorNormalizedKernel
        (cutoffTwoSectorObservableCoefficient observable) ≈
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
        cutoffTwoHalfCoupling (by decide) 2 0
        (cutoffTwoCanonicalVacuumObservableCoefficient observable) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun row => listQSum
        (fun column =>
          (observable (cutoffTwoSectorStateAt row) *
              observable (cutoffTwoSectorStateAt column)) *
            cutoffTwoPhysicalJointOnStates
              (cutoffTwoSectorStateAt row)
              (cutoffTwoSectorStateAt column))
        (List.range 65))
      (List.range 65)) _ ?_ ?_
  · unfold finiteMatrixQuadratic cutoffTwoSectorObservableCoefficient
    apply listQSum_congr_on
    intro row _hrow
    apply listQSum_congr_on
    intro column _hcolumn
    exact Q'.mul_eqv_congr_left _ _ _
      (by
        unfold cutoffTwoPhysicalJointOnStates
        exact cutoffTwoSectorNormalizedKernel_eqv_actual)
  · refine Q'.eqv_trans _
      (finiteJointQuadratic cutoffTwoCubeSectorStates observable
        cutoffTwoPhysicalJointOnStates) _ ?_ ?_
    · exact finiteIndexDoubleSum_eqv_listQSum
        cutoffTwoCubeSectorStates zeroEdgeLabelling
        (fun left right =>
          (observable left * observable right) *
            cutoffTwoPhysicalJointOnStates left right)
      |> fun h => by
        rw [cutoffTwoCubeSectorStates_length] at h
        exact h
    · refine Q'.eqv_trans _
        (finiteJointQuadratic
          (centralPhysicalFiniteVacuumSectorStates cutoffTwoHalfCoupling
            (by decide) 2 0)
          observable cutoffTwoPhysicalJointOnStates) _
        (finiteJointQuadratic_perm_local observable
          cutoffTwoPhysicalJointOnStates
          cutoffTwoCanonicalVacuumSectorStates_perm.symm) ?_
      exact Q'.eqv_of_eq
        (by
          unfold centralPhysicalFiniteVacuumSectorMatrixQuadratic
            centralPhysicalFiniteVacuumSectorStates
            cutoffTwoCanonicalVacuumObservableCoefficient
            cutoffTwoPhysicalJointOnStates centralPhysicalFiniteKernel
          exact finiteJointQuadratic_map_local
            (centralPhysicalFiniteVacuumSectorIndices
              cutoffTwoHalfCoupling (by decide) 2 0)
            (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
              (by decide) 2 0)
            observable
            (centralNormalizedPhysicalReflectedKernel
              cutoffTwoHalfCoupling (by decide) 2 0))

/-! ## 3. The normalized gap in the standard canonical finite forms -/

/-- The nontrivial normalized cutoff-two table theorem, now expressed in the
same canonical vacuum-sector finite forms used by the cutoff-limit modules. -/
theorem cutoffTwoCanonicalVacuumObservable_abs_gap
    (observable : EdgeLabelling → Q')
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        cutoffTwoHalfCoupling (by decide) 2 0
        (cutoffTwoCanonicalVacuumObservableCoefficient observable) ≈ 0) :
    Q'.abs
        (centralPhysicalFiniteVacuumSectorMatrixQuadratic
          cutoffTwoHalfCoupling (by decide) 2 0
          (cutoffTwoCanonicalVacuumObservableCoefficient observable)) ≤
      cutoffTwoStrictRate *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          cutoffTwoHalfCoupling (by decide) 2 0
          (cutoffTwoCanonicalVacuumObservableCoefficient observable) := by
  have htableCenter :
      finiteWeightedMean 65 cutoffTwoSectorCanonicalPhysicalWeight
          (cutoffTwoSectorObservableCoefficient observable) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (cutoffTwoSectorObservableWeightedMean_eqv_canonical observable)
      hcenter
  have htableGap :=
    cutoffTwoCanonicalVacuumNormalized_exact_and_strict_abs_gap.2.2
      (cutoffTwoSectorObservableCoefficient observable) htableCenter
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (Q'.eqv_symm
          (cutoffTwoSectorObservableMatrix_eqv_canonical observable))))
    (Q'.le_trans' _ _ _ htableGap
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left cutoffTwoStrictRate _ _
          (cutoffTwoSectorObservableDiagonal_eqv_canonical observable))))

/-! ## 4. Removal of the observable-coordinate restriction -/

/-- A finite state observable encoding an arbitrary coefficient on the
canonical vacuum-sector index list.  Duplicate-freeness makes exactly one
summand survive when the state is represented by the component. -/
def cutoffTwoCanonicalCoefficientObservable
    (coefficient : Nat → Q') (state : EdgeLabelling) : Q' :=
  listQSum
    (fun index =>
      if bf4StateCode 2 0
          (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
            (by decide) 2 0 index) =
          bf4StateCode 2 0 state then
        coefficient index
      else 0)
    (centralPhysicalFiniteVacuumSectorIndices cutoffTwoHalfCoupling
      (by decide) 2 0)

theorem cutoffTwoCanonicalCoefficientObservable_recovers
    (coefficient : Nat → Q') {index : Nat}
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices cutoffTwoHalfCoupling
        (by decide) 2 0) :
    cutoffTwoCanonicalCoefficientObservable coefficient
        (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) 2 0 index) ≈
      coefficient index := by
  let indices := centralPhysicalFiniteVacuumSectorIndices
    cutoffTwoHalfCoupling (by decide) 2 0
  refine Q'.eqv_trans _
    (listQSum
      (fun candidate =>
        if candidate = index then coefficient candidate else 0)
      indices) _ ?_ ?_
  · unfold cutoffTwoCanonicalCoefficientObservable
    apply listQSum_congr_on
    intro candidate hcandidate
    by_cases heq : candidate = index
    · subst candidate
      simp only [if_pos rfl]
      exact Q'.eqv_refl _
    · have hcodeNe :
          bf4StateCode 2 0
              (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                (by decide) 2 0 candidate) ≠
            bf4StateCode 2 0
              (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
                (by decide) 2 0 index) := by
        intro hcode
        have hcandidateLt := centralPhysicalFiniteVacuumSectorIndex_lt
          cutoffTwoHalfCoupling (by decide) 2 0 hcandidate
        have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
          cutoffTwoHalfCoupling (by decide) 2 0 hindex
        have hstate := bf4StateCode_injective_on_positive
          (centralPhysicalFiniteStateAt_mem_positive
            cutoffTwoHalfCoupling (by decide) 2 0 hcandidateLt)
          (centralPhysicalFiniteStateAt_mem_positive
            cutoffTwoHalfCoupling (by decide) 2 0 hindexLt)
          hcode
        exact heq
          (centralPhysicalFiniteStateAt_injective_on_vacuumSector
            hcandidate hindex hstate)
      simp only [if_neg heq, if_neg hcodeNe]
      exact Q'.eqv_refl 0
  · exact listQSum_ite_single_local index coefficient indices
      (centralPhysicalFiniteVacuumSectorIndices_nodup
        cutoffTwoHalfCoupling (by decide) 2 0)
      hindex

theorem cutoffTwoCanonicalEncodedWeightedMean_eqv
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorWeightedMean
        cutoffTwoHalfCoupling (by decide) 2 0
        (cutoffTwoCanonicalVacuumObservableCoefficient
          (cutoffTwoCanonicalCoefficientObservable coefficient)) ≈
      centralPhysicalFiniteVacuumSectorWeightedMean
        cutoffTwoHalfCoupling (by decide) 2 0 coefficient := by
  unfold centralPhysicalFiniteVacuumSectorWeightedMean
  apply listQSum_congr_on
  intro index hindex
  exact Q'.mul_eqv_congr_right _ _ _
    (cutoffTwoCanonicalCoefficientObservable_recovers
      coefficient hindex)

theorem cutoffTwoCanonicalEncodedDiagonal_eqv
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        cutoffTwoHalfCoupling (by decide) 2 0
        (cutoffTwoCanonicalVacuumObservableCoefficient
          (cutoffTwoCanonicalCoefficientObservable coefficient)) ≈
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        cutoffTwoHalfCoupling (by decide) 2 0 coefficient := by
  unfold centralPhysicalFiniteVacuumSectorDiagonalQuadratic
  apply listQSum_congr_on
  intro index hindex
  have hrecover := cutoffTwoCanonicalCoefficientObservable_recovers
    coefficient hindex
  exact Q'.mul_eqv_congr_right _ _ _
    (mul_eqv_congr_local hrecover hrecover)

theorem cutoffTwoCanonicalEncodedMatrix_eqv
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
        cutoffTwoHalfCoupling (by decide) 2 0
        (cutoffTwoCanonicalVacuumObservableCoefficient
          (cutoffTwoCanonicalCoefficientObservable coefficient)) ≈
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
        cutoffTwoHalfCoupling (by decide) 2 0 coefficient := by
  unfold centralPhysicalFiniteVacuumSectorMatrixQuadratic
    finiteJointQuadratic
  apply listQSum_congr_on
  intro left hleft
  apply listQSum_congr_on
  intro right hright
  have hleftRecover := cutoffTwoCanonicalCoefficientObservable_recovers
    coefficient hleft
  have hrightRecover := cutoffTwoCanonicalCoefficientObservable_recovers
    coefficient hright
  exact Q'.mul_eqv_congr_right _ _ _
    (mul_eqv_congr_local hleftRecover hrightRecover)

/-- The fully coordinate-free finite conclusion: every exactly centered
coefficient on the canonical cutoff-two vacuum component obeys the normalized
physical absolute form contraction at rate `49/50`. -/
theorem cutoffTwoCanonicalVacuumFinite_abs_gap
    (coefficient : Nat → Q')
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        cutoffTwoHalfCoupling (by decide) 2 0 coefficient ≈ 0) :
    Q'.abs
        (centralPhysicalFiniteVacuumSectorMatrixQuadratic
          cutoffTwoHalfCoupling (by decide) 2 0 coefficient) ≤
      cutoffTwoStrictRate *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          cutoffTwoHalfCoupling (by decide) 2 0 coefficient := by
  let observable := cutoffTwoCanonicalCoefficientObservable coefficient
  have hencodedCenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
          cutoffTwoHalfCoupling (by decide) 2 0
          (cutoffTwoCanonicalVacuumObservableCoefficient observable) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (cutoffTwoCanonicalEncodedWeightedMean_eqv coefficient) hcenter
  have hencodedGap := cutoffTwoCanonicalVacuumObservable_abs_gap
    observable hencodedCenter
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (Q'.eqv_symm
          (cutoffTwoCanonicalEncodedMatrix_eqv coefficient))))
    (Q'.le_trans' _ _ _ hencodedGap
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left cutoffTwoStrictRate _ _
          (cutoffTwoCanonicalEncodedDiagonal_eqv coefficient))))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap.cutoffTwoCanonicalVacuumSectorStates_perm
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap.cutoffTwoSectorObservableWeightedMean_eqv_canonical
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap.cutoffTwoSectorObservableMatrix_eqv_canonical
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap.cutoffTwoCanonicalVacuumObservable_abs_gap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap.cutoffTwoCanonicalCoefficientObservable_recovers
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap.cutoffTwoCanonicalEncodedMatrix_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap.cutoffTwoCanonicalVacuumFinite_abs_gap
