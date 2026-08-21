/-
# The fixed-nome cutoff limit is the physical stationary functional

`BF4PhysicalCutoffProbFunctional` removes the representation cutoff from the
actual corrected-slab BF4 expectation.  The physical GNS construction is
instead phrased using the lower-row marginal of the normalized reflected
joint law.  This module proves that these are the same finite expectation,
modulo `Q'.eqv`, for every bounded lower observable.

The proof uses the existing ordered bilinear full-slab reindex theorem with
the upper coefficient set to one.  Zero-marginal rows are removed exactly,
finite sums are reassociated, and the common partition normalization is
preserved.  The resulting Bishop real is represented by the literal physical
stationary means at every cutoff.  Thus the cutoff-removed functional below
and the finite physical GNS refer to the same moments.

Only the Peter--Weyl cutoff is removed.  The nome and finite half-extent remain
fixed.  The unit-interval carrier is multiplicative, not additive, so no
linearity, thermodynamic limit, spacing limit, OS reconstruction, or mass gap
is claimed.

Axiom gate: constructive finite-list and rational algebra plus Bishop `CReal`.
No `Classical`, `sorry`, `native_decide`, choice, functional extensionality,
noncomputable declaration, or custom axiom.
-/

import YMGap.Continuum.BF4PhysicalCutoffProbFunctional
import YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
import YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw

namespace YMGap.Continuum.BF4PhysicalCutoffStationaryBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffProbFunctional
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.ContinuumFunctional
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4HalfTimeReflectionSupportPairConditionalLaw

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Lower unit observables and their full-slab pullback -/

/-- A globally `[0,1]`-valued rational observable on the physical lower
edge-labelling carrier. -/
structure CentralPhysicalUnitObservable : Type where
  value : EdgeLabelling → Q'
  nonnegative : ∀ state, (0 : Q') ≤ value state
  le_one : ∀ state, value state ≤ (1 : Q')

/-- Constant unit lower observable. -/
def centralPhysicalUnitObservable : CentralPhysicalUnitObservable where
  value := fun _ => 1
  nonnegative := fun _ => Q'.zero_le_one
  le_one := fun _ => Q'.le_refl' 1

/-- Pointwise product of lower unit observables. -/
def centralPhysicalUnitObservableMul
    (left right : CentralPhysicalUnitObservable) :
    CentralPhysicalUnitObservable where
  value state := left.value state * right.value state
  nonnegative := fun state => Q'.mul_nonneg _ _
    (left.nonnegative state) (right.nonnegative state)
  le_one := by
    intro state
    refine Q'.le_trans' _ ((1 : Q') * 1) _ ?_ ?_
    · exact Q'.mul_le_mul_of_nonneg
        (left.le_one state) (right.le_one state)
        Q'.zero_le_one (right.nonnegative state)
    · exact Q'.le_of_eqv (Q'.one_mul_eqv 1)

/-- Minimal multiplicative algebra of bounded lower physical observables. -/
def centralPhysicalUnitObsAlg : ObsAlg where
  carrier := CentralPhysicalUnitObservable
  one := centralPhysicalUnitObservable
  mul := centralPhysicalUnitObservableMul
  star := fun observable => observable

/-- Pull a lower observable back to the complete corrected slab through the
literal lower-restriction map. -/
def centralLowerSlabUnitObservable
    (half : Nat) (observable : CentralPhysicalUnitObservable) :
    CutoffStableSlabUnitObservable (centralExtent half) where
  value _ physical :=
    observable.value (centralLowerRestriction half physical)
  nonnegative := by
    intro _ physical _
    exact observable.nonnegative
      (centralLowerRestriction half physical)
  le_one := by
    intro _ physical _
    exact observable.le_one
      (centralLowerRestriction half physical)
  cutoff_stable := by
    intro _ _ physical _ _
    exact Q'.eqv_refl
      (observable.value (centralLowerRestriction half physical))

@[simp] theorem centralLowerSlabUnitObservable_value
    (half cutoff : Nat) (observable : CentralPhysicalUnitObservable)
    (physical : EdgeLabelling) :
    (centralLowerSlabUnitObservable half observable).value cutoff physical =
      observable.value (centralLowerRestriction half physical) := rfl

/-! ## 2. Removing zero rows from the stationary mean -/

private theorem q_nonpositive_of_not_positive_local
    {q : Q'} (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  exact Int.not_lt.mp (fun hnum =>
    hnot (CReal.pos_of_num_pos hnum))

private theorem q_eqv_zero_of_nonnegative_of_nonpositive_local
    {q : Q'} (hnonnegative : (0 : Q') ≤ q)
    (hnonpositive : q ≤ 0) : q ≈ 0 := by
  show q.num * ((0 : Q').den : Int) =
    (0 : Q').num * (q.den : Int)
  exact Int.le_antisymm hnonpositive hnonnegative

private theorem centralPhysicalRowMarginal_eqv_zero_of_not_positive
    {w : Q'} {hw : (0 : Q') ≤ w}
    {cutoff half : Nat} {state : EdgeLabelling}
    (hnot : ¬ (0 : Q') <
      centralPhysicalRowMarginal w hw cutoff half state) :
    centralPhysicalRowMarginal w hw cutoff half state ≈ 0 :=
  q_eqv_zero_of_nonnegative_of_nonpositive_local
    (centralPhysicalRowMarginal_nonnegative hw cutoff half state)
    (q_nonpositive_of_not_positive_local hnot)

private theorem listQSum_filter_eq_of_zero_local
    {A : Type} (value : A → Q') (predicate : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → predicate item = false →
        value item ≈ 0) →
      listQSum value (items.filter predicate) ≈
        listQSum value items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true,
            if_false, listQSum]
          have hhead := hzero head List.mem_cons_self hp
          have htail :=
            listQSum_filter_eq_of_zero_local value predicate tail
              (fun item hitem =>
                hzero item (List.mem_cons_of_mem head hitem))
          exact Q'.eqv_trans _ (listQSum value tail) _ htail
            (Q'.eqv_trans _ (0 + listQSum value tail) _
              (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _)))
              (Q'.add_eqv_congr'
                (Q'.eqv_symm hhead) (Q'.eqv_refl _)))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_filter_eq_of_zero_local
              value predicate tail
              (fun item hitem =>
                hzero item (List.mem_cons_of_mem head hitem)))

/-- The retained stationary mean equals the sum over every lower state;
discarded rows have exactly zero marginal. -/
theorem centralPhysicalStationaryMean_eq_unfiltered
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (observable : EdgeLabelling → Q') :
    centralPhysicalStationaryMean w hw cutoff half observable ≈
      listQSum
        (fun state =>
          centralPhysicalRowMarginal w hw cutoff half state *
            observable state)
        (centralHalfStates cutoff half) := by
  unfold centralPhysicalStationaryMean centralPositiveHalfStates
  apply listQSum_filter_eq_of_zero_local
  intro state hstate hfalse
  have hnot : ¬ (0 : Q') <
      centralPhysicalRowMarginal w hw cutoff half state := by
    simpa only [decide_eq_false_iff_not] using hfalse
  exact Q'.eqv_trans _ (0 * observable state) _
    (Q'.mul_eqv_congr_right _ _ _
      (centralPhysicalRowMarginal_eqv_zero_of_not_positive hnot))
    (Q'.zero_mul_eqv _)

/-! ## 3. One-sided normalized bilinear reindexing -/

/-- Partition-normalized ordered physical reflection bilinear. -/
def centralNormalizedPhysicalReflectionBilinear
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (left right : EdgeLabelling → Q') : Q' :=
  Q'.divPos
    (centralPhysicalReflectionBilinear
      w cutoff half left right)
    (slabParametricKPhysicalPartition
      w cutoff (centralExtent half))
    (slabParametricKPhysicalPartition_pos
      hw cutoff (centralExtent half))

private theorem mul_mul_swap_last
    (first second third : Q') :
    (first * second) * third ≈
      (first * third) * second := by
  exact Q'.eqv_trans _ (first * (second * third)) _
    (Q'.mul_assoc_eqv first second third)
    (Q'.eqv_trans _ (first * (third * second)) _
      (Q'.mul_eqv_congr_left first _ _
        (Q'.mul_comm_eqv second third))
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv first third second)))

private theorem kernel_mul_observable_eq_bilinear_term
    (kernel observable : Q') :
    kernel * observable ≈
      (observable * 1) * kernel := by
  exact Q'.eqv_trans _ (observable * kernel) _
    (Q'.mul_comm_eqv kernel observable)
    (Q'.eqv_symm
      (Q'.mul_eqv_congr_right
        (observable * 1) observable kernel
        (Q'.mul_one_eqv observable)))

/-- The row-marginal expectation is the normalized reflected bilinear with
the upper observable equal to one. -/
theorem centralPhysicalStationaryMean_eq_normalizedBilinear
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (observable : EdgeLabelling → Q') :
    centralPhysicalStationaryMean w hw cutoff half observable ≈
      centralNormalizedPhysicalReflectionBilinear
        w hw cutoff half observable (fun _ => 1) := by
  let states := centralHalfStates cutoff half
  let partition :=
    slabParametricKPhysicalPartition
      w cutoff (centralExtent half)
  let hpartition :=
    slabParametricKPhysicalPartition_pos
      hw cutoff (centralExtent half)
  let reciprocal := Q'.recipPos partition hpartition
  let kernel := centralPhysicalReflectedKernel w cutoff half
  let term := fun left right =>
    (observable left * 1) * kernel left right
  have hrow : ∀ left,
      centralPhysicalRowMarginal w hw cutoff half left *
          observable left ≈
        listQSum
          (fun right => term left right * reciprocal)
          states := by
    intro left
    refine Q'.eqv_trans _
      ((listQSum (kernel left) states * reciprocal) *
        observable left) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (listQSum_mul_right (kernel left) reciprocal states)
    · refine Q'.eqv_trans _
        ((listQSum (kernel left) states * observable left) *
          reciprocal) _
        (mul_mul_swap_last
          (listQSum (kernel left) states)
          reciprocal (observable left)) ?_
      refine Q'.eqv_trans _
        (listQSum (term left) states * reciprocal) _ ?_ ?_
      · apply Q'.mul_eqv_congr_right
        refine Q'.eqv_trans _
          (listQSum
            (fun right => kernel left right * observable left)
            states) _
          (Q'.eqv_symm
            (listQSum_mul_right
              (kernel left) (observable left) states)) ?_
        apply listQSum_congr
        intro right
        exact kernel_mul_observable_eq_bilinear_term
          (kernel left right) (observable left)
      · exact Q'.eqv_symm
          (listQSum_mul_right
            (term left) reciprocal states)
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        centralPhysicalRowMarginal w hw cutoff half left *
          observable left)
      states) _
    (centralPhysicalStationaryMean_eq_unfiltered
      w hw cutoff half observable) ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        listQSum
          (fun right => term left right * reciprocal)
          states)
      states) _ ?_ ?_
  · exact listQSum_congr hrow states
  · refine Q'.eqv_trans _
      (listQSum
        (fun left => listQSum (term left) states * reciprocal)
        states) _ ?_ ?_
    · apply listQSum_congr
      intro left
      exact listQSum_mul_right
        (term left) reciprocal states
    · refine Q'.eqv_trans _
        (listQSum
          (fun left => listQSum (term left) states)
          states * reciprocal) _
        (listQSum_mul_right
          (fun left => listQSum (term left) states)
          reciprocal states) ?_
      unfold centralNormalizedPhysicalReflectionBilinear
        centralPhysicalReflectionBilinear Q'.divPos
        term kernel reciprocal partition hpartition states
      exact Q'.eqv_refl _

/-- The normalized bilinear with unit upper insertion is exactly the finite
corrected-slab bounded-observable expectation of the lower pullback. -/
theorem centralNormalizedPhysicalReflectionBilinear_eq_slabExpectation
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (observable : CentralPhysicalUnitObservable) :
    centralNormalizedPhysicalReflectionBilinear
        w hw cutoff half observable.value (fun _ => 1) ≈
      slabNomeCutoffBoundedObservableExpectation
        w hw cutoff (centralExtent half)
        (centralLowerSlabUnitObservable half observable) := by
  unfold centralNormalizedPhysicalReflectionBilinear
    slabNomeCutoffBoundedObservableExpectation Q'.divPos
  apply Q'.mul_eqv_congr_right
  refine Q'.eqv_trans _
    (centralFullPhysicalReflectionBilinear
      w cutoff half observable.value (fun _ => 1)) _
    (centralPhysicalReflectionBilinear_eq_full
      w cutoff half observable.value (fun _ => 1)) ?_
  unfold centralFullPhysicalReflectionBilinear
    slabBoundedObservableNumerator
  apply listQSum_congr
  intro physical
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.mul_one_eqv
      (observable.value
        (centralLowerRestriction half physical)))

/-- **Finite one-sided bridge.**  The stationary row-marginal expectation
used by the physical BF4 GNS is the exact corrected-slab expectation of the
lower pullback, at every cutoff. -/
theorem centralPhysicalStationaryMean_eq_slabExpectation
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (observable : CentralPhysicalUnitObservable) :
    centralPhysicalStationaryMean
        w hw cutoff half observable.value ≈
      slabNomeCutoffBoundedObservableExpectation
        w hw cutoff (centralExtent half)
        (centralLowerSlabUnitObservable half observable) :=
  Q'.eqv_trans _ _ _
    (centralPhysicalStationaryMean_eq_normalizedBilinear
      w hw cutoff half observable.value)
    (centralNormalizedPhysicalReflectionBilinear_eq_slabExpectation
      w hw cutoff half observable)

/-! ## 4. The cutoff limit represented by literal stationary means -/

/-- The cutoff-removed physical stationary expectation, with approximation
`K` definitionally equal to the finite row-marginal mean at cutoff `K`. -/
def centralPhysicalStationaryCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalUnitObservable) : CReal where
  approx cutoff :=
    centralPhysicalStationaryMean
      w (Q'.le_of_lt hw0) cutoff half observable.value
  cauchy := by
    intro epsilon hepsilon
    refine ⟨slabNomeBoundedObservableModulus
        w (centralExtent half) epsilon,
      fun first second hfirst hsecond => ?_⟩
    have hslab :=
      slabNomeCutoffBoundedObservableExpectation_twoSided_of_modulus
        hw0 hw1 (centralExtent half)
        (centralLowerSlabUnitObservable half observable)
        hepsilon hfirst hsecond
    have hfirstBridge :=
      centralPhysicalStationaryMean_eq_slabExpectation
        w (Q'.le_of_lt hw0) first half observable
    have hsecondBridge :=
      centralPhysicalStationaryMean_eq_slabExpectation
        w (Q'.le_of_lt hw0) second half observable
    constructor
    · exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hfirstBridge)
        (Q'.le_trans' _ _ _ hslab.1
          (Q'.le_of_eqv
            (Q'.add_eqv_congr_right _ _ epsilon
              (Q'.eqv_symm hsecondBridge))))
    · exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hsecondBridge)
        (Q'.le_trans' _ _ _ hslab.2
          (Q'.le_of_eqv
            (Q'.add_eqv_congr_right _ _ epsilon
              (Q'.eqv_symm hfirstBridge))))

@[simp] theorem centralPhysicalStationaryCutoffLimit_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) (observable : CentralPhysicalUnitObservable) :
    (centralPhysicalStationaryCutoffLimit
      hw0 hw1 half observable).approx cutoff =
      centralPhysicalStationaryMean
        w (Q'.le_of_lt hw0) cutoff half observable.value := rfl

theorem centralPhysicalStationaryMean_nonnegative_of_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (observable : EdgeLabelling → Q')
    (hnonnegative : ∀ state, (0 : Q') ≤ observable state) :
    (0 : Q') ≤
      centralPhysicalStationaryMean
        w hw cutoff half observable := by
  unfold centralPhysicalStationaryMean
  apply listQSum_nonnegative_on
  intro state _
  exact Q'.mul_nonneg _ _
    (centralPhysicalRowMarginal_nonnegative
      hw cutoff half state)
    (hnonnegative state)

/-- The fixed-nome, fixed-volume, cutoff-removed probability functional whose
rational approximations are literally the physical stationary GNS moments. -/
def centralPhysicalStationaryCutoffProbFunctional
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) : CRealProbFunctional centralPhysicalUnitObsAlg where
  E := centralPhysicalStationaryCutoffLimit hw0 hw1 half
  normalized := by
    apply Equiv_of_approx_eqv
    intro cutoff
    exact centralPhysicalStationaryMean_one
      w (Q'.le_of_lt hw0) cutoff half
  positive := by
    intro observable
    apply CReal.ofQ'_le_of_approx_ge
    intro cutoff
    exact centralPhysicalStationaryMean_nonnegative_of_nonnegative
      (Q'.le_of_lt hw0) cutoff half
      (centralPhysicalUnitObservableMul
        observable observable).value
      (centralPhysicalUnitObservableMul
        observable observable).nonnegative

/-- Every approximation is exactly the physical row-marginal expectation
used by the finite GNS at the same cutoff. -/
@[simp] theorem centralPhysicalStationaryCutoffProbFunctional_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) (observable : CentralPhysicalUnitObservable) :
    ((centralPhysicalStationaryCutoffProbFunctional
        hw0 hw1 half).E observable).approx cutoff =
      centralPhysicalStationaryMean
        w (Q'.le_of_lt hw0) cutoff half observable.value := rfl

/-- The functional's finite `a* b` approximations are definitionally the
weighted pairings used by the physical BF4 GNS construction. -/
@[simp] theorem
    centralPhysicalStationaryCutoffProbFunctional_approx_starMul_eq_weightedInner
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left right : CentralPhysicalUnitObservable) :
    ((centralPhysicalStationaryCutoffProbFunctional hw0 hw1 half).E
      (centralPhysicalUnitObsAlg.mul
        (centralPhysicalUnitObsAlg.star left) right)).approx cutoff =
      centralPhysicalWeightedInner
        w (Q'.le_of_lt hw0) cutoff half left.value right.value := rfl

/-! ## Axiom audit -/

#print axioms CentralPhysicalUnitObservable
#print axioms centralLowerSlabUnitObservable
#print axioms centralPhysicalStationaryMean_eq_slabExpectation
#print axioms centralPhysicalStationaryCutoffLimit
#print axioms centralPhysicalStationaryCutoffProbFunctional
#print axioms centralPhysicalStationaryCutoffProbFunctional_approx
#print axioms
  centralPhysicalStationaryCutoffProbFunctional_approx_starMul_eq_weightedInner

end YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
