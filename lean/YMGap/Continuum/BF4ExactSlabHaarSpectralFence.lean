/-
# Exact Haar-diagonal spectral fence for the grouped BF4 endpoint

The exact-slab AF comparison currently asks the grouped Mehler reference for
a `1/8` spectral bound on the hyperplane centered by the exact geometric
Haar diagonal.  This file gives a finite, kernel-checked test of that choice.

At cutoff one, the vacuum and a single-face label both have exact Haar weight
one.  Their signed code-delta observable is therefore Haar-diagonal mean
zero and has weighted square two.  At the first diagonal/empty-cross grouped
endpoint its quadratic is exactly one.  Consequently every compatible rate
is at least `1/2`; in particular the requested `1/8` datum is uninhabited at
this endpoint.

This fence does not rule out higher grouped orders.  It does show that the
spectral producer cannot start at the lowest endpoint and that the current
Haar centering is analytically distinct from the grouped kernel's natural
Perron centering.
-/

import YMGap.Continuum.BF4ExactSlabAllCutoffAFComparison

namespace YMGap.Continuum.BF4ExactSlabHaarSpectralFence

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabGroupedAFComparison
open YMGap.Continuum.BF4FiveHolonomyNormalizedKernel
open YMGap.Continuum.BF4GeometricAllSpinHaarGram
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_codeDelta_zero_of_not_mem
    {A : Type} (code : A → Nat) (valid : A → Prop)
    (hinjective :
      ∀ {left right}, valid left → valid right →
        code left = code right → left = right)
    (selected : A) (hselected : valid selected) (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → valid item) →
      selected ∉ items →
      listQSum
          (fun item =>
            value item *
              (if code item = code selected then (1 : Q') else 0))
          items ≈
        0
  | [], _, _ => Q'.eqv_refl 0
  | head :: tail, hvalid, hnot => by
      have hheadValid := hvalid head List.mem_cons_self
      have htailValid : ∀ item, item ∈ tail → valid item :=
        fun item hitem => hvalid item (List.mem_cons_of_mem head hitem)
      have htailNot : selected ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      have hcode : code head ≠ code selected := by
        intro heq
        have hsame := hinjective hheadValid hselected heq
        subst head
        exact hnot List.mem_cons_self
      simp only [listQSum, if_neg hcode]
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr'
          (Q'.mul_zero_eqv (value head))
          (listQSum_codeDelta_zero_of_not_mem
            code valid hinjective selected hselected value
            tail htailValid htailNot))
        (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem listQSum_codeDelta_of_mem_nodup
    {A : Type} (code : A → Nat) (valid : A → Prop)
    (hinjective :
      ∀ {left right}, valid left → valid right →
        code left = code right → left = right)
    (selected : A) (hselected : valid selected) (value : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → valid item) →
      items.Nodup →
      selected ∈ items →
      listQSum
          (fun item =>
            value item *
              (if code item = code selected then (1 : Q') else 0))
          items ≈
        value selected
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hvalid, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum, if_true]
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr'
            (Q'.mul_one_eqv (value selected))
            (listQSum_codeDelta_zero_of_not_mem
              code valid hinjective selected hselected value
              tail
              (fun item hitem =>
                hvalid item (List.mem_cons_of_mem selected hitem))
              hparts.1))
          (Q'.eqv_of_eq (Q'.add_zero' (value selected)))
      · have hheadValid := hvalid head List.mem_cons_self
        have hcode : code head ≠ code selected := by
          intro heq
          have hsame := hinjective hheadValid hselected heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, if_neg hcode]
        exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr'
            (Q'.mul_zero_eqv (value head))
            (listQSum_codeDelta_of_mem_nodup
              code valid hinjective selected hselected value
              tail
              (fun item hitem =>
                hvalid item (List.mem_cons_of_mem head hitem))
              hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' (value selected)))

def oneFaceState : EdgeLabelling :=
  setEdgeLabel zeroEdgeLabelling 0 1

theorem oneFaceState_mem_centralHalfStates :
    oneFaceState ∈ centralHalfStates 1 0 := by
  unfold centralHalfStates
  apply boundedEdgeLabellings_complete
  · intro edge hedge
    unfold oneFaceState setEdgeLabel zeroEdgeLabelling
    split
    · omega
    · omega
  · intro edge hnot
    unfold oneFaceState setEdgeLabel zeroEdgeLabelling
    rw [if_neg]
    intro hedge
    subst edge
    exact hnot (by decide)

theorem oneFaceState_weight_eqv_one :
    exactSlabBoundaryHaarDiagonalWeight oneFaceState ≈ 1 := by
  decide

theorem oneFaceState_mem_positive :
    oneFaceState ∈ exactSlabPositiveHaarStates 1 := by
  exact mem_exactSlabPositiveHaarStates_iff.mpr
    ⟨oneFaceState_mem_centralHalfStates,
      Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
        (Q'.ge_of_eqv oneFaceState_weight_eqv_one)⟩

def boundaryCode (state : EdgeLabelling) : Nat :=
  bf4StateCode 1 0 state

def boundaryCodeDelta
    (selected state : EdgeLabelling) : Q' :=
  if boundaryCode state = boundaryCode selected then 1 else 0

def twoStateObservable (state : EdgeLabelling) : Q' :=
  boundaryCodeDelta zeroEdgeLabelling state +
    (-boundaryCodeDelta oneFaceState state)

private theorem boundaryCode_injective_on_carrier
    {left right : EdgeLabelling}
    (hleft : left ∈ exactSlabPositiveHaarStates 1)
    (hright : right ∈ exactSlabPositiveHaarStates 1)
    (hcode : boundaryCode left = boundaryCode right) :
    left = right := by
  exact bf4StateCode_injective_on_centralHalfStates
    (mem_exactSlabPositiveHaarStates_iff.mp hleft).1
    (mem_exactSlabPositiveHaarStates_iff.mp hright).1
    hcode

private theorem positiveCarrier_nodup :
    (exactSlabPositiveHaarStates 1).Nodup := by
  unfold exactSlabPositiveHaarStates
  exact List.filter_sublist.nodup (centralHalfStates_nodup 1 0)

theorem listQSum_value_mul_boundaryCodeDelta
    (selected : EdgeLabelling)
    (hselected : selected ∈ exactSlabPositiveHaarStates 1)
    (value : EdgeLabelling → Q') :
    listQSum
        (fun state =>
          value state * boundaryCodeDelta selected state)
        (exactSlabPositiveHaarStates 1) ≈
      value selected := by
  unfold boundaryCodeDelta
  exact listQSum_codeDelta_of_mem_nodup
    boundaryCode
    (fun state => state ∈ exactSlabPositiveHaarStates 1)
    boundaryCode_injective_on_carrier
    selected hselected value
    (exactSlabPositiveHaarStates 1)
    (fun item hitem => hitem)
    positiveCarrier_nodup hselected

theorem listQSum_value_mul_twoStateObservable
    (value : EdgeLabelling → Q') :
    listQSum
        (fun state => value state * twoStateObservable state)
        (exactSlabPositiveHaarStates 1) ≈
      value zeroEdgeLabelling + (-value oneFaceState) := by
  have hpointwise :
      listQSum
          (fun state => value state * twoStateObservable state)
          (exactSlabPositiveHaarStates 1) ≈
        listQSum
          (fun state =>
            value state * boundaryCodeDelta zeroEdgeLabelling state +
              (-value state) * boundaryCodeDelta oneFaceState state)
          (exactSlabPositiveHaarStates 1) := by
    apply listQSum_congr_on
    intro state _
    unfold twoStateObservable
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv
        (value state)
        (boundaryCodeDelta zeroEdgeLabelling state)
        (-boundaryCodeDelta oneFaceState state)) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_refl
        (value state * boundaryCodeDelta zeroEdgeLabelling state))
      (Q'.eqv_trans _ _ _
        (Q'.mul_neg_eqv
          (value state)
          (boundaryCodeDelta oneFaceState state))
        (Q'.eqv_symm
          (Q'.neg_mul_eqv
            (value state)
            (boundaryCodeDelta oneFaceState state))))
  exact Q'.eqv_trans _ _ _ hpointwise
    (Q'.eqv_trans _ _ _
      (listQSum_add
        (fun state =>
          value state * boundaryCodeDelta zeroEdgeLabelling state)
        (fun state =>
          (-value state) * boundaryCodeDelta oneFaceState state)
        (exactSlabPositiveHaarStates 1))
      (Q'.add_eqv_congr'
        (listQSum_value_mul_boundaryCodeDelta
          zeroEdgeLabelling
          (zeroEdgeLabelling_mem_exactSlabPositiveHaarStates 1)
          value)
        (listQSum_value_mul_boundaryCodeDelta
          oneFaceState oneFaceState_mem_positive
          (fun state => -value state))))

theorem twoStateObservable_meanZero :
    ExactSlabBoundaryMeanZero 1 twoStateObservable := by
  unfold ExactSlabBoundaryMeanZero
  exact Q'.eqv_trans _ _ _
    (listQSum_value_mul_twoStateObservable
      exactSlabBoundaryHaarDiagonalWeight)
    (by decide)

theorem twoStateObservable_weightedSquare_eqv_two :
    exactSlabBoundaryWeightedSquare 1 twoStateObservable ≈ 2 := by
  unfold exactSlabBoundaryWeightedSquare finiteWeightedSquare
  have hrewrite :
      listQSum
          (fun state =>
            exactSlabBoundaryHaarDiagonalWeight state *
              (twoStateObservable state * twoStateObservable state))
          (exactSlabPositiveHaarStates 1) ≈
        listQSum
          (fun state =>
            (exactSlabBoundaryHaarDiagonalWeight state *
              twoStateObservable state) * twoStateObservable state)
          (exactSlabPositiveHaarStates 1) := by
    apply listQSum_congr_on
    intro state _
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (exactSlabBoundaryHaarDiagonalWeight state)
        (twoStateObservable state)
        (twoStateObservable state))
  refine Q'.eqv_trans _ _ _ hrewrite ?_
  refine Q'.eqv_trans _
    ((exactSlabBoundaryHaarDiagonalWeight zeroEdgeLabelling *
        twoStateObservable zeroEdgeLabelling) +
      (-(exactSlabBoundaryHaarDiagonalWeight oneFaceState *
        twoStateObservable oneFaceState))) _ ?_ ?_
  · exact listQSum_value_mul_twoStateObservable
      (fun state =>
        exactSlabBoundaryHaarDiagonalWeight state *
          twoStateObservable state)
  · decide

private theorem mul3_swap_last_local (A B C : Q') :
    (A * B) * C ≈ (A * C) * B := by
  exact Q'.eqv_trans _ (A * (B * C)) _
    (Q'.mul_assoc_eqv A B C)
    (Q'.eqv_trans _ (A * (C * B)) _
      (Q'.mul_eqv_congr_left A (B * C) (C * B)
        (Q'.mul_comm_eqv B C))
      (Q'.eqv_symm (Q'.mul_assoc_eqv A C B)))

private theorem finiteJointQuadratic_eqv_twoStateCompression
    {State : Type} (states : List State)
    (observable : State → Q') (joint : State → State → Q')
    (first second : State)
    (hsum : ∀ value : State → Q',
      listQSum (fun state => value state * observable state) states ≈
        value first + (-value second)) :
    finiteJointQuadratic states observable joint ≈
      (joint first first + (-joint first second)) +
        (-(joint second first + (-joint second second))) := by
  unfold finiteJointQuadratic
  have hinner :
      ∀ left,
        listQSum
            (fun right =>
              (observable left * observable right) * joint left right)
            states ≈
          observable left * joint left first +
            (-(observable left * joint left second)) := by
    intro left
    have hrewrite :
        listQSum
            (fun right =>
              (observable left * observable right) * joint left right)
            states ≈
          listQSum
            (fun right =>
              (observable left * joint left right) * observable right)
            states := by
      apply listQSum_congr_on
      intro right _
      exact mul3_swap_last_local
        (observable left) (observable right) (joint left right)
    exact Q'.eqv_trans _ _ _ hrewrite
      (hsum (fun right => observable left * joint left right))
  have houter :
      listQSum
          (fun left =>
            listQSum
              (fun right =>
                (observable left * observable right) * joint left right)
              states)
          states ≈
        listQSum
          (fun left =>
            (joint left first + (-joint left second)) * observable left)
          states := by
    apply listQSum_congr_on
    intro left _
    refine Q'.eqv_trans _ _ _ (hinner left) ?_
    refine Q'.eqv_trans _
      (joint left first * observable left +
        (-joint left second) * observable left) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (Q'.mul_comm_eqv (observable left) (joint left first))
        (Q'.eqv_trans _ (-(joint left second * observable left)) _
          (Q'.neg_eqv_congr _ _
            (Q'.mul_comm_eqv
              (observable left) (joint left second)))
          (Q'.eqv_symm
            (Q'.neg_mul_eqv (joint left second) (observable left))))
    · exact Q'.eqv_symm
        (Q'.add_mul_eqv
          (joint left first) (-joint left second) (observable left))
  exact Q'.eqv_trans _ _ _ houter
    (hsum (fun left => joint left first + (-joint left second)))

theorem twoStateObservable_grouped00_quadratic_eqv_one :
    finiteJointQuadratic
        (exactSlabPositiveHaarStates 1)
        twoStateObservable
        (normalizedGroupedMehlerKernel 0 0) ≈
      1 := by
  exact Q'.eqv_trans _ _ _
    (finiteJointQuadratic_eqv_twoStateCompression
      (exactSlabPositiveHaarStates 1)
      twoStateObservable
      (normalizedGroupedMehlerKernel 0 0)
      zeroEdgeLabelling oneFaceState
      listQSum_value_mul_twoStateObservable)
    (by decide)

private theorem half_le_rate_of_unit_over_two_test
    (quadratic norm rate : Q')
    (hquadratic : Q'.abs quadratic ≈ 1)
    (hnorm : norm ≈ 2)
    (hbound : Q'.abs quadratic ≤ rate * norm) :
    Q'.mkPos 1 2 (by decide) ≤ rate := by
  have hone_le_rateTwo : (1 : Q') ≤ rate * 2 := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hquadratic)
      (Q'.le_trans' _ _ _ hbound
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left rate norm 2 hnorm)))
  let half := Q'.mkPos 1 2 (by decide)
  have hscaled :
      half * 1 ≤ half * (rate * 2) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      hone_le_rateTwo (by decide)
  have hright : half * (rate * 2) ≈ rate := by
    refine Q'.eqv_trans _ ((half * rate) * 2) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv half rate 2)) ?_
    refine Q'.eqv_trans _ ((rate * half) * 2) _
      (Q'.mul_eqv_congr_right
        (half * rate) (rate * half) 2
        (Q'.mul_comm_eqv half rate)) ?_
    refine Q'.eqv_trans _ (rate * (half * 2)) _
      (Q'.mul_assoc_eqv rate half 2) ?_
    refine Q'.eqv_trans _ (rate * 1) _
      (Q'.mul_eqv_congr_left rate (half * 2) 1 (by decide)) ?_
    exact Q'.mul_one_eqv rate
  exact Q'.le_trans' _ (half * 1) _
    (Q'.ge_of_eqv (Q'.mul_one_eqv half))
    (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

/-- Every spectral rate compatible with the exact cutoff-one two-state test
at the lowest grouped endpoint is at least `1/2`. -/
theorem half_le_grouped00_HaarBoundary_spectral_rate
    (spectral : GroupedMehlerHaarBoundarySpectralData 1 0 0) :
    Q'.mkPos 1 2 (by decide) ≤ spectral.rate := by
  apply half_le_rate_of_unit_over_two_test
    (finiteJointQuadratic
      (exactSlabPositiveHaarStates 1)
      twoStateObservable
      (normalizedGroupedMehlerKernel 0 0))
    (exactSlabBoundaryWeightedSquare 1 twoStateObservable)
    spectral.rate
  · exact Q'.eqv_trans _ _ _
      (Q'.abs_eqv_congr
        twoStateObservable_grouped00_quadratic_eqv_one)
      (by decide)
  · exact twoStateObservable_weightedSquare_eqv_two
  · exact spectral.meanZero_quadratic
      twoStateObservable twoStateObservable_meanZero

private theorem no_eighth_of_unit_over_two_test
    (quadratic norm rate : Q')
    (hquadratic : Q'.abs quadratic ≈ 1)
    (hnorm : norm ≈ 2)
    (hbound : Q'.abs quadratic ≤ rate * norm)
    (hrate : rate ≤ Q'.mkPos 1 8 (by decide)) : False := by
  have hone_le_rateTwo : (1 : Q') ≤ rate * 2 := by
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv hquadratic)
      (Q'.le_trans' _ _ _ hbound
        (Q'.le_of_eqv
          (Q'.mul_eqv_congr_left rate norm 2 hnorm)))
  have hrateTwo_le_quarter :
      rate * 2 ≤ Q'.mkPos 1 4 (by decide) := by
    exact Q'.le_trans' _
      (Q'.mkPos 1 8 (by decide) * 2) _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hrate (by decide))
      (Q'.le_of_eqv (by decide))
  have hone_le_quarter :
      (1 : Q') ≤ Q'.mkPos 1 4 (by decide) :=
    Q'.le_trans' _ _ _ hone_le_rateTwo hrateTwo_le_quarter
  exact (by decide :
    ¬ ((1 : Q') ≤ Q'.mkPos 1 4 (by decide))) hone_le_quarter

/-- The grouped endpoint at the first diagonal/empty-cross order cannot
satisfy the requested Haar-diagonal spectral eighth. -/
theorem no_grouped00_HaarBoundary_spectral_eighth :
    ¬ ∃ spectral : GroupedMehlerHaarBoundarySpectralData 1 0 0,
        spectral.rate ≤ Q'.mkPos 1 8 (by decide) := by
  intro hexists
  rcases hexists with ⟨spectral, hrate⟩
  apply no_eighth_of_unit_over_two_test
    (finiteJointQuadratic
      (exactSlabPositiveHaarStates 1)
      twoStateObservable
      (normalizedGroupedMehlerKernel 0 0))
    (exactSlabBoundaryWeightedSquare 1 twoStateObservable)
    spectral.rate
  · exact Q'.eqv_trans _ _ _
      (Q'.abs_eqv_congr
        twoStateObservable_grouped00_quadratic_eqv_one)
      (by decide)
  · exact twoStateObservable_weightedSquare_eqv_two
  · exact spectral.meanZero_quadratic
      twoStateObservable twoStateObservable_meanZero
  · exact hrate

end YMGap.Continuum.BF4ExactSlabHaarSpectralFence

#print axioms YMGap.Continuum.BF4ExactSlabHaarSpectralFence.oneFaceState_weight_eqv_one
#print axioms YMGap.Continuum.BF4ExactSlabHaarSpectralFence.twoStateObservable_meanZero
#print axioms YMGap.Continuum.BF4ExactSlabHaarSpectralFence.twoStateObservable_weightedSquare_eqv_two
#print axioms YMGap.Continuum.BF4ExactSlabHaarSpectralFence.twoStateObservable_grouped00_quadratic_eqv_one
#print axioms YMGap.Continuum.BF4ExactSlabHaarSpectralFence.half_le_grouped00_HaarBoundary_spectral_rate
#print axioms YMGap.Continuum.BF4ExactSlabHaarSpectralFence.no_grouped00_HaarBoundary_spectral_eighth
