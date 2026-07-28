/-
# Corrected-slab tails for cutoff-stable [0,1]-valued observables

A Markov pullback of a coarse Boolean event is generally rational-valued,
not Boolean-valued.  This module extends the literal corrected-slab
outer-cutoff tail from Boolean events to a cutoff-indexed observable family
whose values lie in `[0,1]` and agree on every retained old state.

The coherence law is explicit Type-level data.  In particular this module
does not assert that a proposed stochastic BF4 kernel supplies such a law.
Once supplied, the normalized expectation changes by at most the complete
new-label mass.  The ambient supported-subset bridge then pays that mass with
the arbitrary-nome degree-thirteen schedule for every rational `0 < w < 1`.

No stochastic exponent-Gram convergence is claimed here; that conclusion
requires a separately proved coherence instance for the actual conditional
kernel observable.

## Axiom gate

Finite `List`, `Nat`, and `Q'` algebra only.  No `Classical.*`, `Real`,
`native_decide`, `sorry`, custom axiom, functional extensionality, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
import YMGap.Continuum.SU2PhysicalOuterCutoffNomeInteractingTolerance

namespace YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeInteractingTolerance
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The minimal cutoff-stable unit-observable carrier -/

/-- A rational corrected-slab observable that may be represented differently
at different cutoffs, but is stable on every state already present at the
smaller cutoff and lies in `[0,1]` on each literal finite carrier. -/
structure CutoffStableSlabUnitObservable
    (extent : Nat) : Type where
  value : Nat → EdgeLabelling → Q'
  nonnegative :
    ∀ K state,
      state ∈
          boundedEdgeLabellings K
            (slabPhysicalFaceEdges extent) →
        (0 : Q') ≤ value K state
  le_one :
    ∀ K state,
      state ∈
          boundedEdgeLabellings K
            (slabPhysicalFaceEdges extent) →
        value K state ≤ (1 : Q')
  cutoff_stable :
    ∀ K L state,
      K ≤ L →
      state ∈
          boundedEdgeLabellings K
            (slabPhysicalFaceEdges extent) →
        value K state ≈ value L state

/-- Unnormalized expectation numerator on the literal corrected slab. -/
def slabBoundedObservableNumerator
    (w : Q') (K extent : Nat)
    (observable :
      CutoffStableSlabUnitObservable extent) : Q' :=
  listQSum
    (fun state =>
      observable.value K state *
        slabParametricKPhysicalTerm
          w K extent state)
    (boundedEdgeLabellings K
      (slabPhysicalFaceEdges extent))

/-- Portion of the later unnormalized expectation carried by genuinely new
labels. -/
def slabBoundedObservableCutoffIncrement
    (w : Q') (K L extent : Nat)
    (observable :
      CutoffStableSlabUnitObservable extent) : Q' :=
  listQSum
    (fun state =>
      observable.value L state *
        slabParametricKPhysicalTerm
          w L extent state)
    ((boundedEdgeLabellings L
      (slabPhysicalFaceEdges extent)).filter
        (fun state =>
          !(labelWithinB K
            (slabPhysicalFaceEdges extent) state)))

private theorem listQSum_nonnegative_local
    {A : Type} (weight : A → Q')
    (hweight : ∀ item, (0 : Q') ≤ weight item) :
    ∀ source : List A,
      (0 : Q') ≤ listQSum weight source
  | [] => Q'.le_refl' 0
  | head :: tail =>
      Q'.zero_le_add _ _
        (hweight head)
        (listQSum_nonnegative_local
          weight hweight tail)

private theorem listQSum_mono_local
    {A : Type} (lower upper : A → Q') :
    ∀ source : List A,
      (∀ item, item ∈ source →
        lower item ≤ upper item) →
      listQSum lower source ≤
        listQSum upper source
  | [], _ => Q'.le_refl' 0
  | head :: tail, hpointwise =>
      Q'.add_le_add
        (hpointwise head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem =>
            hpointwise item
              (List.mem_cons_of_mem head hitem)))

theorem slabBoundedObservableNumerator_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K extent : Nat)
    (observable :
      CutoffStableSlabUnitObservable extent) :
    (0 : Q') ≤
      slabBoundedObservableNumerator
        w K extent observable := by
  unfold slabBoundedObservableNumerator
  apply listQSum_nonnegative_on
  intro state hstate
  exact Q'.mul_nonneg _ _
    (observable.nonnegative K state hstate)
    (slabParametricKPhysicalTerm_nonnegative
      hw K extent state)

theorem slabBoundedObservableNumerator_le_partition
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K extent : Nat)
    (observable :
      CutoffStableSlabUnitObservable extent) :
    slabBoundedObservableNumerator
        w K extent observable ≤
      slabParametricKPhysicalPartition
        w K extent := by
  unfold slabBoundedObservableNumerator
    slabParametricKPhysicalPartition
  apply listQSum_mono_local
  intro state hstate
  have hterm :
      (0 : Q') ≤
        slabParametricKPhysicalTerm
          w K extent state :=
    slabParametricKPhysicalTerm_nonnegative
      hw K extent state
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right
      _ _ _
      (observable.le_one K state hstate)
      hterm)
    (Q'.le_of_eqv
      (Q'.one_mul_eqv
        (slabParametricKPhysicalTerm
          w K extent state)))

theorem slabBoundedObservableCutoffIncrement_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K L extent : Nat)
    (observable :
      CutoffStableSlabUnitObservable extent) :
    (0 : Q') ≤
      slabBoundedObservableCutoffIncrement
        w K L extent observable := by
  unfold slabBoundedObservableCutoffIncrement
  apply listQSum_nonnegative_on
  intro state hfiltered
  have hstate := (List.mem_filter.mp hfiltered).1
  exact Q'.mul_nonneg _ _
    (observable.nonnegative L state hstate)
    (slabParametricKPhysicalTerm_nonnegative
      hw L extent state)

theorem slabBoundedObservableCutoffIncrement_le_total
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K L extent : Nat)
    (observable :
      CutoffStableSlabUnitObservable extent) :
    slabBoundedObservableCutoffIncrement
        w K L extent observable ≤
      slabParametricKCutoffIncrement
        w K L extent := by
  unfold slabBoundedObservableCutoffIncrement
    slabParametricKCutoffIncrement
  apply listQSum_mono_local
  intro state hstate
  have hbounded := (List.mem_filter.mp hstate).1
  have hterm :
      (0 : Q') ≤
        slabParametricKPhysicalTerm
          w L extent state :=
    slabParametricKPhysicalTerm_nonnegative
      hw L extent state
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right
      _ _ _
      (observable.le_one L state hbounded)
      hterm)
    (Q'.le_of_eqv
      (Q'.one_mul_eqv
        (slabParametricKPhysicalTerm
          w L extent state)))

/-! ## 2. Exact retained-plus-new decomposition -/

private theorem range_nodup_local :
    ∀ N : Nat, (List.range N).Nodup
  | 0 => List.nodup_nil
  | N + 1 => by
      rw [List.range_succ]
      apply List.nodup_append.mpr
      refine
        ⟨range_nodup_local N,
          List.nodup_cons.mpr
            ⟨List.not_mem_nil, List.nodup_nil⟩,
          ?_⟩
      intro left hleft right hright heq
      have hrightEq := List.mem_singleton.mp hright
      subst right
      rw [hrightEq] at hleft
      exact (Nat.lt_irrefl N)
        (List.mem_range.mp hleft)

private theorem slabPhysicalFaceEdges_nodup
    (extent : Nat) :
    (slabPhysicalFaceEdges extent).Nodup := by
  unfold slabPhysicalFaceEdges
  exact range_nodup_local _

/-- Every cutoff-stable unit-observable numerator splits exactly into its
old numerator and its later-cutoff new-label contribution. -/
theorem slabBoundedObservableNumerator_eq_base_add_increment
    {w : Q'} {K L extent : Nat}
    (hKL : K ≤ L)
    (observable :
      CutoffStableSlabUnitObservable extent) :
    slabBoundedObservableNumerator
        w L extent observable ≈
      slabBoundedObservableNumerator
          w K extent observable +
        slabBoundedObservableCutoffIncrement
          w K L extent observable := by
  let faces := slabPhysicalFaceEdges extent
  let oldTest := labelWithinB K faces
  let largeSupport := boundedEdgeLabellings L faces
  let smallSupport := boundedEdgeLabellings K faces
  let largeWeight : EdgeLabelling → Q' :=
    fun state =>
      observable.value L state *
        slabParametricKPhysicalTerm
          w L extent state
  let smallWeight : EdgeLabelling → Q' :=
    fun state =>
      observable.value K state *
        slabParametricKPhysicalTerm
          w K extent state
  have hfilter :
      largeSupport.filter oldTest = smallSupport := by
    dsimp only [largeSupport, smallSupport, oldTest, faces]
    exact boundedEdgeLabellings_filter_cutoff
      hKL _ (slabPhysicalFaceEdges_nodup extent)
  have hcommon :
      listQSum largeWeight
          (largeSupport.filter oldTest) ≈
        listQSum smallWeight smallSupport := by
    rw [hfilter]
    apply listQSum_congr_on
    intro state hstate
    dsimp only [largeWeight, smallWeight]
    exact Q'.eqv_trans _
      (observable.value K state *
        slabParametricKPhysicalTerm
          w L extent state) _
      (Q'.mul_eqv_congr_right
        (observable.value L state)
        (observable.value K state)
        (slabParametricKPhysicalTerm
          w L extent state)
        (Q'.eqv_symm
          (observable.cutoff_stable
            K L state hKL hstate)))
      (Q'.mul_eqv_congr_left
        (observable.value K state) _ _
        (slabParametricKPhysicalTerm_cutoff_stable
          hKL hstate))
  have hsplit :
      listQSum largeWeight largeSupport ≈
        listQSum largeWeight
            (largeSupport.filter oldTest) +
          slabBoundedObservableCutoffIncrement
            w K L extent observable := by
    have hpartition :=
      listQSum_filter_partition
        largeWeight oldTest largeSupport
    simpa [slabBoundedObservableCutoffIncrement,
      largeWeight, largeSupport, oldTest, faces]
      using hpartition
  unfold slabBoundedObservableNumerator
  dsimp only [largeWeight, smallWeight,
    largeSupport, smallSupport, faces]
    at hcommon hsplit ⊢
  exact Q'.eqv_trans _ _ _ hsplit
    (Q'.add_eqv_congr'
      hcommon (Q'.eqv_refl _))

/-! ## 3. Sharp normalized bounded-observable tail -/

/-- Normalized expectation of a cutoff-stable unit observable at arbitrary
nonnegative nome. -/
def slabNomeCutoffBoundedObservableExpectation
    (w : Q') (hw : (0 : Q') ≤ w)
    (K extent : Nat)
    (observable :
      CutoffStableSlabUnitObservable extent) : Q' :=
  Q'.divPos
    (slabBoundedObservableNumerator
      w K extent observable)
    (slabParametricKPhysicalPartition
      w K extent)
    (slabParametricKPhysicalPartition_pos
      hw K extent)

private theorem positive_of_one_le_local
    {q : Q'} (hq : (1 : Q') ≤ q) :
    (0 : Q') < q :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (by decide) hq

private theorem one_le_add_nonnegative_local
    {d n : Q'} (hd : (1 : Q') ≤ d)
    (hn : (0 : Q') ≤ n) :
    (1 : Q') ≤ d + n :=
  Q'.le_trans' _ _ _ hd
    (Q'.add_le_self_of_nonneg d n hn)

private theorem qeqv_of_le_of_ge_local
    {a b : Q'} (hab : a ≤ b) (hba : b ≤ a) :
    a ≈ b := by
  show a.num * (b.den : Int) =
    b.num * (a.den : Int)
  exact Int.le_antisymm hab hba

private theorem divPos_eqv_congr_local
    {a a' b b' : Q'}
    (hb : (0 : Q') < b)
    (hb' : (0 : Q') < b')
    (ha : a ≈ a') (hden : b ≈ b') :
    Q'.divPos a b hb ≈
      Q'.divPos a' b' hb' := by
  apply qeqv_of_le_of_ge_local
  · apply Q'.le_divPos_of_mul_le
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos a b hb) b' b
          (Q'.eqv_symm hden))
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv a b hb) ha))
  · apply Q'.le_divPos_of_mul_le
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (Q'.divPos a' b' hb') b b' hden)
        (Q'.eqv_trans _ _ _
          (Q'.divPos_mul_eqv a' b' hb')
          (Q'.eqv_symm ha)))

/-- Sharp arbitrary-nome normalized tail: a cutoff-stable `[0,1]` observable
changes by at most the complete new corrected-slab mass. -/
theorem slabNomeCutoffBoundedObservableExpectation_abs_le_increment
    {w : Q'} (hw : (0 : Q') ≤ w)
    {K L extent : Nat} (hKL : K ≤ L)
    (observable :
      CutoffStableSlabUnitObservable extent) :
    absQ
        (slabNomeCutoffBoundedObservableExpectation
            w hw K extent observable +
          -slabNomeCutoffBoundedObservableExpectation
            w hw L extent observable) ≤
      slabParametricKCutoffIncrement
        w K L extent := by
  let a :=
    slabBoundedObservableNumerator
      w K extent observable
  let b :=
    slabBoundedObservableCutoffIncrement
      w K L extent observable
  let d :=
    slabParametricKPhysicalPartition
      w K extent
  let n :=
    slabParametricKCutoffIncrement
      w K L extent
  let A :=
    slabBoundedObservableNumerator
      w L extent observable
  let D :=
    slabParametricKPhysicalPartition
      w L extent
  have ha : (0 : Q') ≤ a := by
    dsimp only [a]
    exact slabBoundedObservableNumerator_nonnegative
      hw K extent observable
  have hb : (0 : Q') ≤ b := by
    dsimp only [b]
    exact
      slabBoundedObservableCutoffIncrement_nonnegative
        hw K L extent observable
  have hn : (0 : Q') ≤ n := by
    dsimp only [n]
    exact slabParametricKCutoffIncrement_nonnegative
      hw K L extent
  have hd1 : (1 : Q') ≤ d := by
    dsimp only [d]
    exact slabParametricKPhysicalPartition_one_le
      hw K extent
  have had : a ≤ d := by
    dsimp only [a, d]
    exact slabBoundedObservableNumerator_le_partition
      hw K extent observable
  have hbn : b ≤ n := by
    dsimp only [b, n]
    exact slabBoundedObservableCutoffIncrement_le_total
      hw K L extent observable
  have hbase :=
    nested_normalized_event_abs_le_newMass
      ha hb hn hd1 had hbn
  have hd : (0 : Q') < d :=
    positive_of_one_le_local hd1
  have hdn : (0 : Q') < d + n :=
    positive_of_one_le_local
      (one_le_add_nonnegative_local hd1 hn)
  have hA : A ≈ a + b := by
    dsimp only [A, a, b]
    exact
      slabBoundedObservableNumerator_eq_base_add_increment
        hKL observable
  have hD : D ≈ d + n := by
    dsimp only [D, d, n]
    exact
      slabParametricKPhysicalPartition_eq_base_add_increment
        hKL
  have hDactual : (0 : Q') < D := by
    dsimp only [D]
    exact slabParametricKPhysicalPartition_pos
      hw L extent
  have hlarge :
      Q'.divPos A D hDactual ≈
        Q'.divPos (a + b) (d + n) hdn :=
    divPos_eqv_congr_local hDactual hdn hA hD
  unfold slabNomeCutoffBoundedObservableExpectation
  dsimp only [a, b, d, n, A, D] at hbase hlarge ⊢
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (YMGap.Continuum.ContinuumYMStack.absQ_eqv_congr
        (Q'.add_eqv_congr_left
          (Q'.divPos
            (slabBoundedObservableNumerator
              w K extent observable)
            (slabParametricKPhysicalPartition
              w K extent)
            (slabParametricKPhysicalPartition_pos
              hw K extent))
          _
          (-(Q'.divPos
            (slabBoundedObservableNumerator
                w K extent observable +
              slabBoundedObservableCutoffIncrement
                w K L extent observable)
            (slabParametricKPhysicalPartition
                w K extent +
              slabParametricKCutoffIncrement
                w K L extent)
            hdn))
          (Q'.neg_eqv_congr _ _ hlarge))))
    hbase

/-! ## 4. Arbitrary-nome total-tolerance schedule -/

/-- The corrected-slab increment inherits the arbitrary-nome ambient
degree-thirteen total-tolerance schedule through the supported zero-extension
subset. -/
theorem slabPhysicalNomeCutoffIncrement_le_tolerance
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (extent : Nat) {ε : Q'} (hε : (0 : Q') < ε)
    {L : Nat}
    (hL :
      physicalNomeTensorToleranceRetainedCutoff
          w
          (plaquetteEdgeCount (extent + 1))
          ε ≤ L) :
    slabParametricKCutoffIncrement
        w
        (physicalNomeTensorToleranceRetainedCutoff
          w
          (plaquetteEdgeCount (extent + 1))
          ε)
        L extent ≤
      ε := by
  exact Q'.le_trans' _ _ _
    (slabParametricKCutoffIncrement_le_ambient
      (w := w) (Q'.le_of_lt hw0))
    (physicalNomeCutoffIncrement_le_tolerance
      hw0 hw1 (extent + 1) hε hL)

/-- Executable Cauchy modulus for every cutoff-stable corrected-slab unit
observable at a fixed nome and finite extent. -/
def slabNomeBoundedObservableModulus
    (w : Q') (extent : Nat) (ε : Q') : Nat :=
  physicalNomeTensorToleranceRetainedCutoff
    w
    (plaquetteEdgeCount (extent + 1))
    (HalfPow.half * ε)

private theorem
    slabNomeBoundedObservableExpectation_from_modulus_abs_le_half
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (extent : Nat)
    (observable :
      CutoffStableSlabUnitObservable extent)
    {ε : Q'} (hε : (0 : Q') < ε)
    {L : Nat}
    (hL :
      slabNomeBoundedObservableModulus
          w extent ε ≤ L) :
    absQ
        (slabNomeCutoffBoundedObservableExpectation
            w (Q'.le_of_lt hw0)
            (slabNomeBoundedObservableModulus
              w extent ε)
            extent observable +
          -slabNomeCutoffBoundedObservableExpectation
            w (Q'.le_of_lt hw0)
            L extent observable) ≤
      HalfPow.half * ε := by
  have hhalf :
      (0 : Q') < HalfPow.half * ε :=
    YMGap.Constructive.ExpNeg.half_mul_pos ε hε
  exact Q'.le_trans' _ _ _
    (slabNomeCutoffBoundedObservableExpectation_abs_le_increment
      (Q'.le_of_lt hw0) hL observable)
    (slabPhysicalNomeCutoffIncrement_le_tolerance
      hw0 hw1 extent hhalf hL)

private theorem twoSided_of_absQ_sub_le
    {a b ε : Q'} (h : absQ (a + (-b)) ≤ ε) :
    a ≤ b + ε ∧ b ≤ a + ε := by
  have habs : Q'.abs (a + (-b)) ≤ ε :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (YMGap.Continuum.ContinuumYMStack.absQ_eqv_abs
            (a + (-b)))))
      h
  constructor
  · exact YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
      habs
  · apply YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm b a))
      habs

private theorem add_two_halves_le
    (x ε : Q') :
    (x + HalfPow.half * ε) +
        HalfPow.half * ε ≤
      x + ε := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.add_assoc_eqv
        x (HalfPow.half * ε)
        (HalfPow.half * ε))) ?_
  exact Q'.le_of_eqv
    (Q'.add_eqv_congr_left
      x
      (HalfPow.half * ε +
        HalfPow.half * ε)
      ε
      (YMGap.Constructive.ExpNeg.two_halves ε))

/-- Every two cutoffs beyond the executable modulus give two-sided
`ε`-close normalized expectations for every supplied coherent unit
observable. -/
theorem
    slabNomeCutoffBoundedObservableExpectation_twoSided_of_modulus
    {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q'))
    (extent : Nat)
    (observable :
      CutoffStableSlabUnitObservable extent)
    {ε : Q'} (hε : (0 : Q') < ε)
    {first second : Nat}
    (hfirst :
      slabNomeBoundedObservableModulus
          w extent ε ≤ first)
    (hsecond :
      slabNomeBoundedObservableModulus
          w extent ε ≤ second) :
    slabNomeCutoffBoundedObservableExpectation
          w (Q'.le_of_lt hw0)
          first extent observable ≤
        slabNomeCutoffBoundedObservableExpectation
            w (Q'.le_of_lt hw0)
            second extent observable + ε ∧
      slabNomeCutoffBoundedObservableExpectation
          w (Q'.le_of_lt hw0)
          second extent observable ≤
        slabNomeCutoffBoundedObservableExpectation
            w (Q'.le_of_lt hw0)
            first extent observable + ε := by
  let halfTolerance := HalfPow.half * ε
  have hfirstHalf :=
    twoSided_of_absQ_sub_le
      (slabNomeBoundedObservableExpectation_from_modulus_abs_le_half
        hw0 hw1 extent observable hε hfirst)
  have hsecondHalf :=
    twoSided_of_absQ_sub_le
      (slabNomeBoundedObservableExpectation_from_modulus_abs_le_half
        hw0 hw1 extent observable hε hsecond)
  constructor
  · have hchain :
      slabNomeCutoffBoundedObservableExpectation
            w (Q'.le_of_lt hw0)
            first extent observable ≤
          (slabNomeCutoffBoundedObservableExpectation
              w (Q'.le_of_lt hw0)
              second extent observable +
              halfTolerance) +
            halfTolerance :=
        Q'.le_trans' _ _ _
          hfirstHalf.2
          (Q'.add_le_add_right _ _ halfTolerance
            hsecondHalf.1)
    exact Q'.le_trans' _ _ _ hchain
      (add_two_halves_le
        (slabNomeCutoffBoundedObservableExpectation
          w (Q'.le_of_lt hw0)
          second extent observable) ε)
  · have hchain :
      slabNomeCutoffBoundedObservableExpectation
            w (Q'.le_of_lt hw0)
            second extent observable ≤
          (slabNomeCutoffBoundedObservableExpectation
              w (Q'.le_of_lt hw0)
              first extent observable +
              halfTolerance) +
            halfTolerance :=
        Q'.le_trans' _ _ _
          hsecondHalf.2
          (Q'.add_le_add_right _ _ halfTolerance
            hfirstHalf.1)
    exact Q'.le_trans' _ _ _ hchain
      (add_two_halves_le
        (slabNomeCutoffBoundedObservableExpectation
          w (Q'.le_of_lt hw0)
          first extent observable) ε)

#print axioms CutoffStableSlabUnitObservable
#print axioms slabBoundedObservableNumerator_eq_base_add_increment
#print axioms
  slabNomeCutoffBoundedObservableExpectation_abs_le_increment
#print axioms slabPhysicalNomeCutoffIncrement_le_tolerance
#print axioms slabNomeBoundedObservableModulus
#print axioms
  slabNomeCutoffBoundedObservableExpectation_twoSided_of_modulus

end YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
