/-
# Vacuum-diagonal fence for the exact/physical BF4 same-action seam

The literal corrected-slab Haar kernel and the positive multiplicity-product
law cannot define the same normalized quadratic form, already at cutoff one.
The separating observable is the exact code delta at the vacuum.

On the signed Haar side its quadratic is the vacuum--vacuum entry, which is
exactly one by exposed-link Peter--Weyl annihilation.  On the positive side it
is the normalized vacuum diagonal.  That diagonal is bounded by the vacuum
row marginal, while the explicit non-vacuum cube row has strictly positive
marginal and the two marginals sum to at most one.  Hence the physical value
is strictly below one at every positive coupling.

Consequently `ExactHaarPhysicalPerronSameActionAt` is uninhabited at cutoff
one for positive coupling.  The Perron reroute must therefore compare the
two actions with a nonzero error, or derive a different positive
representation of the signed Haar network; exact equality to the current
multiplicity-product law is not an available frontier theorem.

## Axiom gate

Finite lists, faithful natural-number state codes, and exact `Q'` order only.
No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CentralLowerCubeRowDomination
import YMGap.Continuum.BF4ExactPhysicalPerronReroute
import YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison

namespace YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CentralLowerCubeRowDomination
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison
open YMGap.Continuum.BF4ExactSlabGroupedAFComparison
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The faithful vacuum code delta -/

/-- Exact point observable at the vacuum on the bounded BF4 lower carrier. -/
def vacuumCodeDelta (K : Nat) (state : EdgeLabelling) : Q' :=
  if bf4StateCode K 0 state =
      bf4StateCode K 0 zeroEdgeLabelling then 1 else 0

private theorem listQSum_codeDelta_zero_of_not_mem
    (K : Nat) (selected : EdgeLabelling)
    (hselected : selected ∈ centralHalfStates K 0)
    (value : EdgeLabelling → Q') :
    ∀ items : List EdgeLabelling,
      (∀ item, item ∈ items → item ∈ centralHalfStates K 0) →
      selected ∉ items →
      listQSum
          (fun item =>
            value item *
              (if bf4StateCode K 0 item = bf4StateCode K 0 selected
                then (1 : Q') else 0))
          items ≈
        0
  | [], _, _ => Q'.eqv_refl 0
  | head :: tail, hcarrier, hnot => by
      have hhead := hcarrier head List.mem_cons_self
      have htail :
          ∀ item, item ∈ tail → item ∈ centralHalfStates K 0 :=
        fun item hitem =>
          hcarrier item (List.mem_cons_of_mem head hitem)
      have hselectedTail : selected ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      have hcode :
          bf4StateCode K 0 head ≠ bf4StateCode K 0 selected := by
        intro heq
        have hsame := bf4StateCode_injective_on_centralHalfStates
          hhead hselected heq
        subst head
        exact hnot List.mem_cons_self
      simp only [listQSum, if_neg hcode]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_zero_eqv (value head))
          (listQSum_codeDelta_zero_of_not_mem
            K selected hselected value tail htail hselectedTail))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_codeDelta_of_mem_nodup
    (K : Nat) (selected : EdgeLabelling)
    (hselected : selected ∈ centralHalfStates K 0)
    (value : EdgeLabelling → Q') :
    ∀ items : List EdgeLabelling,
      (∀ item, item ∈ items → item ∈ centralHalfStates K 0) →
      items.Nodup →
      selected ∈ items →
      listQSum
          (fun item =>
            value item *
              (if bf4StateCode K 0 item = bf4StateCode K 0 selected
                then (1 : Q') else 0))
          items ≈
        value selected
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hcarrier, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum, if_true]
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr'
            (Q'.mul_one_eqv (value selected))
            (listQSum_codeDelta_zero_of_not_mem
              K selected hselected value tail
              (fun item hitem =>
                hcarrier item
                  (List.mem_cons_of_mem selected hitem))
              hparts.1))
          (Q'.eqv_of_eq (Q'.add_zero' (value selected)))
      · have hheadCarrier := hcarrier head List.mem_cons_self
        have hcode :
            bf4StateCode K 0 head ≠ bf4StateCode K 0 selected := by
          intro heq
          have hsame := bf4StateCode_injective_on_centralHalfStates
            hheadCarrier hselected heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, if_neg hcode]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.mul_zero_eqv (value head))
            (listQSum_codeDelta_of_mem_nodup
              K selected hselected value tail
              (fun item hitem =>
                hcarrier item (List.mem_cons_of_mem head hitem))
              hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' (value selected)))

private theorem listQSum_value_mul_vacuumCodeDelta
    (K : Nat) (value : EdgeLabelling → Q') :
    listQSum
        (fun state => value state * vacuumCodeDelta K state)
        (centralHalfStates K 0) ≈
      value zeroEdgeLabelling := by
  unfold vacuumCodeDelta
  exact listQSum_codeDelta_of_mem_nodup
    K zeroEdgeLabelling
    (zeroEdgeLabelling_mem_centralHalfStates K 0)
    value (centralHalfStates K 0)
    (fun item hitem => hitem)
    (centralHalfStates_nodup K 0)
    (zeroEdgeLabelling_mem_centralHalfStates K 0)

/-- The same point-evaluation collapse on the strictly positive physical
carrier.  The physical vacuum row is always retained. -/
theorem listQSum_value_mul_vacuumCodeDelta_positive
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K : Nat) (value : EdgeLabelling → Q') :
    listQSum
        (fun state => value state * vacuumCodeDelta K state)
        (centralPositiveHalfStates w hw K 0) ≈
      value zeroEdgeLabelling := by
  unfold vacuumCodeDelta
  exact listQSum_codeDelta_of_mem_nodup
    K zeroEdgeLabelling
    (zeroEdgeLabelling_mem_centralHalfStates K 0)
    value (centralPositiveHalfStates w hw K 0)
    (fun item hitem =>
      (mem_centralPositiveHalfStates_iff.mp hitem).1)
    (centralPositiveHalfStates_nodup w hw K 0)
    (zeroEdgeLabelling_mem_centralPositiveHalfStates hw K 0)

private theorem mul3_swap_last (A B C : Q') :
    (A * B) * C ≈ (A * C) * B := by
  exact Q'.eqv_trans _ (A * (B * C)) _
    (Q'.mul_assoc_eqv A B C)
    (Q'.eqv_trans _ (A * (C * B)) _
      (Q'.mul_eqv_congr_left A (B * C) (C * B)
        (Q'.mul_comm_eqv B C))
      (Q'.eqv_symm (Q'.mul_assoc_eqv A C B)))

private theorem finiteJointQuadratic_vacuumCodeDelta
    (K : Nat) (joint : EdgeLabelling → EdgeLabelling → Q') :
    finiteJointQuadratic
        (centralHalfStates K 0)
        (vacuumCodeDelta K) joint ≈
      joint zeroEdgeLabelling zeroEdgeLabelling := by
  unfold finiteJointQuadratic
  have hinner : ∀ left,
      listQSum
          (fun right =>
            (vacuumCodeDelta K left * vacuumCodeDelta K right) *
              joint left right)
          (centralHalfStates K 0) ≈
        vacuumCodeDelta K left *
          joint left zeroEdgeLabelling := by
    intro left
    refine Q'.eqv_trans _
      (listQSum
        (fun right =>
          (vacuumCodeDelta K left * joint left right) *
            vacuumCodeDelta K right)
        (centralHalfStates K 0)) _ ?_ ?_
    · apply listQSum_congr_on
      intro right _
      exact mul3_swap_last
        (vacuumCodeDelta K left)
        (vacuumCodeDelta K right)
        (joint left right)
    · exact listQSum_value_mul_vacuumCodeDelta K
        (fun right => vacuumCodeDelta K left * joint left right)
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        vacuumCodeDelta K left * joint left zeroEdgeLabelling)
      (centralHalfStates K 0)) _ ?_ ?_
  · apply listQSum_congr_on
    intro left _
    exact hinner left
  · refine Q'.eqv_trans _
      (listQSum
        (fun left =>
          joint left zeroEdgeLabelling * vacuumCodeDelta K left)
        (centralHalfStates K 0)) _ ?_ ?_
    · apply listQSum_congr_on
      intro left _
      exact Q'.mul_comm_eqv
        (vacuumCodeDelta K left)
        (joint left zeroEdgeLabelling)
    · exact listQSum_value_mul_vacuumCodeDelta K
        (fun left => joint left zeroEdgeLabelling)

theorem vacuumCodeDelta_nonnegative
    (K : Nat) (state : EdgeLabelling) :
    (0 : Q') ≤ vacuumCodeDelta K state := by
  unfold vacuumCodeDelta
  split <;> decide

/-- The vacuum point observable has exact coefficient `l¹` norm one on the
full bounded carrier. -/
theorem coefficientL1_vacuumCodeDelta_eqv_one (K : Nat) :
    coefficientL1
        (centralHalfStates K 0) (vacuumCodeDelta K) ≈ 1 := by
  unfold coefficientL1
  refine Q'.eqv_trans _
    (listQSum
      (fun state => (1 : Q') * vacuumCodeDelta K state)
      (centralHalfStates K 0)) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    unfold Q'.abs
    rw [if_pos (vacuumCodeDelta_nonnegative K state)]
    exact Q'.eqv_symm
      (Q'.one_mul_eqv (vacuumCodeDelta K state))
  · exact listQSum_value_mul_vacuumCodeDelta K (fun _ => 1)

/-! ## 2. Exact and physical evaluations of the separator -/

/-- The signed exact-Haar vacuum code delta has quadratic value one at every
cutoff. -/
theorem exactSlabAllCutoffQuadratic_vacuumCodeDelta_eqv_one
    (w : Q') (K : Nat) :
    exactSlabAllCutoffQuadratic w K (vacuumCodeDelta K) ≈ 1 := by
  exact Q'.eqv_trans _ _ _
    (finiteJointQuadratic_vacuumCodeDelta K
      (exactCorrectedSlabReflectedKernel w K 0))
    (exactSlabVacuumPartition_eqv_one_allCutoffs w K)

/-- The normalized positive physical quadratic of the same point observable
is its normalized vacuum diagonal. -/
theorem centralNormalizedFull_vacuumCodeDelta_eqv_diagonal
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) :
    centralNormalizedFullPhysicalReflectionQuadratic
        w hw K 0 (vacuumCodeDelta K) ≈
      centralNormalizedPhysicalReflectedKernel
        w hw K 0 zeroEdgeLabelling zeroEdgeLabelling := by
  unfold centralNormalizedFullPhysicalReflectionQuadratic
    centralNormalizedPhysicalReflectedKernel Q'.divPos
  apply Q'.mul_eqv_congr_right
  refine Q'.eqv_trans _
    (centralPhysicalReflectionQuadratic
      w K 0 (vacuumCodeDelta K)) _ ?_ ?_
  · exact Q'.eqv_symm
      (centralPhysicalReflectionQuadratic_eq_full
        w K 0 (vacuumCodeDelta K))
  · change finiteJointQuadratic
        (centralHalfStates K 0)
        (vacuumCodeDelta K)
        (centralPhysicalReflectedKernel w K 0) ≈ _
    exact finiteJointQuadratic_vacuumCodeDelta K
      (centralPhysicalReflectedKernel w K 0)

private theorem listQSum_nonnegative
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ items : List A, (0 : Q') ≤ listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _
        (hvalue head)
        (listQSum_nonnegative value hvalue tail)

private theorem listQSum_member_le
    {A : Type} (value : A → Q')
    (hvalue : ∀ item, (0 : Q') ≤ value item) :
    ∀ (items : List A) {item : A}, item ∈ items →
      value item ≤ listQSum value items
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact Q'.add_le_self_of_nonneg _ _
          (listQSum_nonnegative value hvalue tail)
      · have ih := listQSum_member_le value hvalue tail htail
        have hmono :
            listQSum value tail ≤
              value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head)
            (listQSum value tail) (hvalue head)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ ih hmono

private theorem lt_add_of_pos_right
    (a b : Q') (hb : (0 : Q') < b) : a < a + b := by
  show a.num * ((a + b).den : Int) <
    (a + b).num * (a.den : Int)
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int) <
    (a.num * (b.den : Int) + b.num * (a.den : Int)) *
      (a.den : Int)
  have hcast :
      ((a.den * b.den : Nat) : Int) =
        (a.den : Int) * (b.den : Int) := by
    push_cast
    rfl
  rw [hcast]
  have hadenpos : (0 : Int) < (a.den : Int) := by
    exact_mod_cast a.den_pos
  have hpositive :
      (0 : Int) < b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hadenpos) hadenpos
  have hexpand :
      (a.num * (b.den : Int) + b.num * (a.den : Int)) *
          (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) +
          b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have hfirst :
        a.num * (b.den : Int) * (a.den : Int) =
          a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc,
        Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [hfirst]
  rw [hexpand]
  omega

/-- Positive coupling forces the normalized physical vacuum diagonal to be
strictly below one: the explicit cube row carries additional positive mass. -/
theorem centralNormalizedFull_vacuumCodeDelta_lt_one
    {w : Q'} (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K) :
    centralNormalizedFullPhysicalReflectionQuadratic
        w (Q'.le_of_lt hw) K 0 (vacuumCodeDelta K) < 1 := by
  let hw0 := Q'.le_of_lt hw
  have hdiagonalLe :
      centralNormalizedPhysicalReflectedKernel
          w hw0 K 0 zeroEdgeLabelling zeroEdgeLabelling ≤
        centralPhysicalRowMarginal
          w hw0 K 0 zeroEdgeLabelling := by
    unfold centralPhysicalRowMarginal
    exact listQSum_member_le
      (centralNormalizedPhysicalReflectedKernel
        w hw0 K 0 zeroEdgeLabelling)
      (fun target =>
        centralNormalizedPhysicalReflectedKernel_nonnegative
          hw0 K 0 zeroEdgeLabelling target)
      (centralHalfStates K 0)
      (zeroEdgeLabelling_mem_centralHalfStates K 0)
  have hcube :
      (0 : Q') <
        centralPhysicalRowMarginal
          w hw0 K 0 centralLowerCubeState :=
    centralLowerCubeRowMarginal_pos hw hK
  have hvacuumGrow :
      centralPhysicalRowMarginal
          w hw0 K 0 zeroEdgeLabelling <
        centralPhysicalRowMarginal
            w hw0 K 0 zeroEdgeLabelling +
          centralPhysicalRowMarginal
            w hw0 K 0 centralLowerCubeState :=
    lt_add_of_pos_right _ _ hcube
  have hvacuumLt :
      centralPhysicalRowMarginal
          w hw0 K 0 zeroEdgeLabelling < 1 :=
    YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
      hvacuumGrow
      (centralVacuum_add_cube_marginal_le_one hw0 hK)
  exact Q'.lt_of_le_of_lt
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (centralNormalizedFull_vacuumCodeDelta_eqv_diagonal
          w hw0 K))
    hdiagonalLe)
    hvacuumLt

/-! ## 3. Quantitative AF-window defect -/

/-- Natural `l¹`-quadratic error interface for comparing the identity
observable transport between the signed exact Haar action and the current
positive physical action. -/
structure ExactHaarPhysicalQuadraticL1ErrorAt
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (epsilon : Q') : Type where
  error : ∀ observable,
    Q'.abs
        (exactSlabAllCutoffQuadratic w K observable +
          (-centralNormalizedFullPhysicalReflectionQuadratic
            w hw K 0 observable)) ≤
      epsilon *
        (coefficientL1 (centralHalfStates K 0) observable *
          coefficientL1 (centralHalfStates K 0) observable)

/-- Once the heat nome is at least `8/9`, the normalized positive physical
quadratic of the vacuum code delta is at most `1/8`. -/
theorem centralNormalizedFull_vacuumCodeDelta_le_oneEighth_of_eightNinths_le
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : cubeActivitySevenWeightFloor ≤ w)
    (K : Nat) (hK : 1 ≤ K) :
    centralNormalizedFullPhysicalReflectionQuadratic
        w hw0 K 0 (vacuumCodeDelta K) ≤
      Q'.mkPos 1 8 (by decide) := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (centralNormalizedFull_vacuumCodeDelta_eqv_diagonal
        w hw0 K))
    (Q'.le_trans' _ _ _
      (listQSum_member_le
        (centralNormalizedPhysicalReflectedKernel
          w hw0 K 0 zeroEdgeLabelling)
        (fun target =>
          centralNormalizedPhysicalReflectedKernel_nonnegative
            hw0 K 0 zeroEdgeLabelling target)
        (centralHalfStates K 0)
        (zeroEdgeLabelling_mem_centralHalfStates K 0))
      (centralVacuumRowMarginal_le_oneEighth_of_eightNinths_le
        hw0 hw hK))

/-- In the same AF window, the vacuum code delta separates the signed exact
Haar action from the current positive multiplicity-product action by at
least `7/8` in absolute quadratic value. -/
theorem exactPhysical_vacuumCodeDelta_abs_defect_ge_sevenEighths
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : cubeActivitySevenWeightFloor ≤ w)
    (K : Nat) (hK : 1 ≤ K) :
    Q'.mkPos 7 8 (by decide) ≤
      Q'.abs
        (exactSlabAllCutoffQuadratic w K (vacuumCodeDelta K) +
          (-centralNormalizedFullPhysicalReflectionQuadratic
            w hw0 K 0 (vacuumCodeDelta K))) := by
  let physical :=
    centralNormalizedFullPhysicalReflectionQuadratic
      w hw0 K 0 (vacuumCodeDelta K)
  have hphysical :
      physical ≤ Q'.mkPos 1 8 (by decide) :=
    centralNormalizedFull_vacuumCodeDelta_le_oneEighth_of_eightNinths_le
      hw0 hw K hK
  have hnegative :
      -(Q'.mkPos 1 8 (by decide)) ≤ -physical :=
    Q'.neg_le_neg hphysical
  have honeSubtract :
      (1 : Q') + (-(Q'.mkPos 1 8 (by decide))) ≤
        1 + (-physical) :=
    Q'.add_le_add_left 1 _ _ hnegative
  have hsigned :
      Q'.mkPos 7 8 (by decide) ≤
        exactSlabAllCutoffQuadratic w K (vacuumCodeDelta K) +
          (-physical) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by decide))
      (Q'.le_trans' _ _ _ honeSubtract
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.add_eqv_congr_right
              (exactSlabAllCutoffQuadratic
                w K (vacuumCodeDelta K))
              1 (-physical)
              (exactSlabAllCutoffQuadratic_vacuumCodeDelta_eqv_one
                w K)))))
  exact Q'.le_trans' _ _ _ hsigned
    (Q'.le_abs_self
      (exactSlabAllCutoffQuadratic w K (vacuumCodeDelta K) +
        (-physical)))

/-- Any identity-on-observables `l¹` quadratic comparison with the current
positive physical law has error rate at least `7/8` in the high-nome AF
window. -/
theorem sevenEighths_le_exactHaarPhysicalQuadraticL1Error
    {w epsilon : Q'} {hw0 : (0 : Q') ≤ w}
    (hw : cubeActivitySevenWeightFloor ≤ w)
    {K : Nat} (hK : 1 ≤ K)
    (comparison :
      ExactHaarPhysicalQuadraticL1ErrorAt
        w hw0 K epsilon) :
    Q'.mkPos 7 8 (by decide) ≤ epsilon := by
  let norm := coefficientL1
    (centralHalfStates K 0) (vacuumCodeDelta K)
  have hlower :=
    exactPhysical_vacuumCodeDelta_abs_defect_ge_sevenEighths
      hw0 hw K hK
  have hupper := comparison.error (vacuumCodeDelta K)
  have hnorm : norm ≈ 1 :=
    coefficientL1_vacuumCodeDelta_eqv_one K
  have hnormSquare : norm * norm ≈ 1 := by
    exact Q'.eqv_trans _ (1 * norm) _
      (Q'.mul_eqv_congr_right norm 1 norm hnorm)
      (Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 norm 1 hnorm)
        (Q'.one_mul_eqv 1))
  have hright : epsilon * (norm * norm) ≈ epsilon :=
    Q'.eqv_trans _ (epsilon * 1) _
      (Q'.mul_eqv_congr_left epsilon (norm * norm) 1 hnormSquare)
      (Q'.mul_one_eqv epsilon)
  exact Q'.le_trans' _ _ _ hlower
    (Q'.le_trans' _ _ _ hupper (Q'.le_of_eqv hright))

/-- In particular, no quarter-error identity comparison exists once
`w ≥ 8/9`. -/
theorem no_exactHaarPhysicalQuadraticL1QuarterError
    {w : Q'} {hw0 : (0 : Q') ≤ w}
    (hw : cubeActivitySevenWeightFloor ≤ w)
    {K : Nat} (hK : 1 ≤ K)
    (comparison :
      ExactHaarPhysicalQuadraticL1ErrorAt
        w hw0 K (Q'.mkPos 1 4 (by decide))) : False := by
  have hbound :=
    sevenEighths_le_exactHaarPhysicalQuadraticL1Error
      hw hK comparison
  exact (by decide :
    ¬ (Q'.mkPos 7 8 (by decide) ≤ Q'.mkPos 1 4 (by decide))) hbound

/-! ## 4. The cutoff-one same-action obstruction -/

/-- At every positive coupling the proposed exact equality between the
signed Haar action and the current positive multiplicity-product action has
no cutoff-one witness. -/
theorem exactHaarPhysicalPerronSameActionAt_cutoffOne_uninhabited
    {w : Q'} (hw : (0 : Q') < w) :
    ExactHaarPhysicalPerronSameActionAt
      w (Q'.le_of_lt hw) 1 → False := by
  intro identification
  have hsame := identification.same_action (vacuumCodeDelta 1)
  have hexact :=
    exactSlabAllCutoffQuadratic_vacuumCodeDelta_eqv_one w 1
  have hphysical :
      centralNormalizedFullPhysicalReflectionQuadratic
          w (Q'.le_of_lt hw) 1 0 (vacuumCodeDelta 1) < 1 :=
    centralNormalizedFull_vacuumCodeDelta_lt_one hw 1 (by decide)
  have hphysicalEqOne :
      centralNormalizedFullPhysicalReflectionQuadratic
          w (Q'.le_of_lt hw) 1 0 (vacuumCodeDelta 1) ≈ 1 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hsame) hexact
  have honeLtOne : (1 : Q') < 1 :=
    Q'.lt_of_le_of_lt (Q'.ge_of_eqv hphysicalEqOne) hphysical
  exact (by decide : ¬ ((1 : Q') < 1)) honeLtOne

end YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence.listQSum_value_mul_vacuumCodeDelta_positive
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence.exactSlabAllCutoffQuadratic_vacuumCodeDelta_eqv_one
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence.coefficientL1_vacuumCodeDelta_eqv_one
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence.centralNormalizedFull_vacuumCodeDelta_eqv_diagonal
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence.centralNormalizedFull_vacuumCodeDelta_lt_one
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence.centralNormalizedFull_vacuumCodeDelta_le_oneEighth_of_eightNinths_le
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence.exactPhysical_vacuumCodeDelta_abs_defect_ge_sevenEighths
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence.sevenEighths_le_exactHaarPhysicalQuadraticL1Error
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence.no_exactHaarPhysicalQuadraticL1QuarterError
#print axioms YMGap.Continuum.BF4ExactPhysicalPerronSameActionFence.exactHaarPhysicalPerronSameActionAt_cutoffOne_uninhabited
