/-
# Coarse corrected-slab exponent-Gram tail along cutoff `4K`

An ordinary coarse SU(2) exponent-Gram coordinate is exactly the normalized
probability of one cutoff-independent Boolean exponent event on the
corrected slab.  Packaging that event as a cutoff-stable `[0,1]` observable
allows the arbitrary-nome corrected-slab tail theorem to be applied at the
induced physical cutoff `4K`.

This module converts the slab-cutoff modulus to a modulus in the base outer
cutoff `K` with a constructive quarter-ceiling recursion.  It also combines
the resulting coarse coordinate estimate with the independently supplied
stochastic blocked-coordinate modulus to expose a conditional
blocked-minus-coarse coordinate Cauchy theorem.

Everything is pointwise at fixed rational nomes, fixed finite corrected-slab
geometry, and a supplied stochastic Markov contract for the optional final
join.  No contract inhabitant, spacing limit, continuum limit, or
infinite-volume limit is constructed.

## Axiom gate

No `Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, choice,
functional extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
import YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract
import YMGap.Continuum.BF4SU2StochasticBlockedGramObservableTail

namespace YMGap.Continuum.BF4SU2CoarseOuterExponentGramTail

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract
open YMGap.Continuum.BF4SU2StochasticBlockedGramObservableTail
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Boolean exponent events as stable slab observables -/

/-- A cutoff-independent Boolean event, embedded as a coherent rational
unit observable on one corrected-slab extent. -/
def slabBooleanEventUnitObservable
    (extent : Nat)
    (event : EdgeLabelling → Bool) :
    CutoffStableSlabUnitObservable extent where
  value _ state := if event state then 1 else 0
  nonnegative := by
    intro K state hstate
    cases hevent : event state
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact Q'.le_refl' 0
    · simp only [↓reduceIte]
      exact Q'.zero_le_one
  le_one := by
    intro K state hstate
    cases hevent : event state
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact Q'.zero_le_one
    · simp only [↓reduceIte]
      exact Q'.le_refl' 1
  cutoff_stable := by
    intro K L state hKL hstate
    exact Q'.eqv_refl _

private theorem normalizedSlabListExpectation_eq_boundedExpectation
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K extent : Nat)
    (observable :
      CutoffStableSlabUnitObservable extent) :
    listQSum
        (fun state =>
          Q'.divPos
              (slabParametricKPhysicalTerm
                w K extent state)
              (slabParametricKPhysicalPartition
                w K extent)
              (slabParametricKPhysicalPartition_pos
                hw K extent) *
            observable.value K state)
        (boundedEdgeLabellings K
          (slabPhysicalFaceEdges extent)) ≈
      slabNomeCutoffBoundedObservableExpectation
        w hw K extent observable := by
  let reciprocal :=
    Q'.recipPos
      (slabParametricKPhysicalPartition
        w K extent)
      (slabParametricKPhysicalPartition_pos
        hw K extent)
  let weightedTerm : EdgeLabelling → Q' :=
    fun state =>
      observable.value K state *
        slabParametricKPhysicalTerm
          w K extent state
  refine Q'.eqv_trans _
    (listQSum
      (fun state => weightedTerm state * reciprocal)
      (boundedEdgeLabellings K
        (slabPhysicalFaceEdges extent))) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    unfold Q'.divPos
    dsimp only [weightedTerm, reciprocal]
    refine Q'.eqv_trans _
      (observable.value K state *
        (slabParametricKPhysicalTerm
            w K extent state * reciprocal)) _ ?_ ?_
    · exact Q'.mul_comm_eqv _ _
    · exact Q'.eqv_symm
        (Q'.mul_assoc_eqv _ _ _)
  · refine Q'.eqv_trans _
      (listQSum weightedTerm
          (boundedEdgeLabellings K
            (slabPhysicalFaceEdges extent)) *
        reciprocal) _ ?_ ?_
    · exact listQSum_mul_right
        weightedTerm reciprocal _
    · unfold
        slabNomeCutoffBoundedObservableExpectation
        slabBoundedObservableNumerator Q'.divPos
      dsimp only [weightedTerm, reciprocal]
      exact Q'.eqv_refl _

/-- The coarse corrected-slab Boolean law is exactly the generic normalized
slab expectation of its indicator, at the induced cutoff `4K`. -/
theorem su2CoarseOuterEventProbability_eq_slabExpectation
    (G : CutoffOneGeometry)
    (candidate : Q')
    (hcandidate : (0 : Q') < candidate)
    (K : Nat)
    (event : OuterSlabLabelling → Bool) :
    su2CoarseOuterEventProbability
        G candidate hcandidate K event ≈
      slabNomeCutoffBoundedObservableExpectation
        candidate (Q'.le_of_lt hcandidate)
        (4 * K) (centralExtent G.coarseHalf)
        (slabBooleanEventUnitObservable
          (centralExtent G.coarseHalf) event) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        Q'.divPos
            (slabParametricKPhysicalTerm
              candidate (4 * K)
              (centralExtent G.coarseHalf) state)
            (slabParametricKPhysicalPartition
              candidate (4 * K)
              (centralExtent G.coarseHalf))
            (slabParametricKPhysicalPartition_pos
              (Q'.le_of_lt hcandidate)
              (4 * K)
              (centralExtent G.coarseHalf)) *
          (slabBooleanEventUnitObservable
            (centralExtent G.coarseHalf)
            event).value (4 * K) state)
      (boundedEdgeLabellings (4 * K)
        (slabPhysicalFaceEdges
          (centralExtent G.coarseHalf)))) _ ?_ ?_
  · unfold su2CoarseOuterEventProbability
      su2CoarseOuterData
      SlabPhysicalData.normalizedMass
      SlabPhysicalData.physicalTerm
      SlabPhysicalData.physicalPartition
      SlabPhysicalData.physicalLabellings
      SlabPhysicalData.faceEdges
      SlabPhysicalData.extent
    apply listQSum_congr_on
    intro state _
    cases hevent : event state
    · simp only [hevent, Bool.false_eq_true,
        ↓reduceIte, slabBooleanEventUnitObservable]
      exact Q'.eqv_symm
        (Q'.mul_zero_eqv _)
    · simp only [hevent, ↓reduceIte,
        slabBooleanEventUnitObservable]
      exact Q'.eqv_symm
        (Q'.mul_one_eqv _)
  · exact
      normalizedSlabListExpectation_eq_boundedExpectation
        (Q'.le_of_lt hcandidate)
        (4 * K) (centralExtent G.coarseHalf)
        (slabBooleanEventUnitObservable
          (centralExtent G.coarseHalf) event)

/-- The ordinary coarse exponent-Gram coordinate is exactly the normalized
expectation of its cutoff-independent exponent-event indicator. -/
theorem su2CoarseOuterExponentGramEntry_eq_slabExpectation
    (G : CutoffOneGeometry)
    (candidate : Q')
    (hcandidate : (0 : Q') < candidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate) :
    su2CoarseOuterExponentGramEntry
        G candidate hcandidate K coordinate ≈
      slabNomeCutoffBoundedObservableExpectation
        candidate (Q'.le_of_lt hcandidate)
        (4 * K) (centralExtent G.coarseHalf)
        (slabBooleanEventUnitObservable
          (centralExtent G.coarseHalf)
          (su2ExponentGramEvent
            G.coarseHalf coordinate)) := by
  exact Q'.eqv_trans _ _ _
    (su2CoarseOuterExponentGramEntry_eq_eventProbability
      G candidate hcandidate K coordinate)
    (su2CoarseOuterEventProbability_eq_slabExpectation
      G candidate hcandidate K
      (su2ExponentGramEvent
        G.coarseHalf coordinate))

/-! ## 2. Constructive conversion from slab cutoff to base cutoff -/

/-- Ceiling of division by four, implemented by structural recursion rather
than integer or real division. -/
def quarterCeil : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | n + 4 => quarterCeil n + 1

theorem le_four_mul_quarterCeil :
    ∀ cutoff : Nat,
      cutoff ≤ 4 * quarterCeil cutoff
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | cutoff + 4 => by
      have ih :=
        le_four_mul_quarterCeil cutoff
      simp only [quarterCeil]
      omega

/-- Executable coarse-coordinate modulus stated in the base outer cutoff
`K`; its image `4K` dominates the corrected-slab modulus. -/
def su2CoarseOuterExponentGramModulus
    (G : CutoffOneGeometry)
    (candidate ε : Q') : Nat :=
  quarterCeil
    (slabNomeBoundedObservableModulus
      candidate
      (centralExtent G.coarseHalf)
      ε)

theorem slabModulus_le_four_mul_of_coarseModulus_le
    (G : CutoffOneGeometry)
    (candidate ε : Q')
    {K : Nat}
    (hK :
      su2CoarseOuterExponentGramModulus
          G candidate ε ≤ K) :
    slabNomeBoundedObservableModulus
        candidate
        (centralExtent G.coarseHalf)
        ε ≤
      4 * K := by
  exact Nat.le_trans
    (le_four_mul_quarterCeil
      (slabNomeBoundedObservableModulus
        candidate
        (centralExtent G.coarseHalf)
        ε))
    (Nat.mul_le_mul_left 4 hK)

/-! ## 3. Coarse exponent-Gram Cauchy theorem in `K` -/

theorem
    su2CoarseOuterExponentGramEntry_twoSided_of_modulus
    (G : CutoffOneGeometry)
    {candidate : Q'}
    (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε)
    {first second : Nat}
    (hfirst :
      su2CoarseOuterExponentGramModulus
          G candidate ε ≤ first)
    (hsecond :
      su2CoarseOuterExponentGramModulus
          G candidate ε ≤ second)
    (coordinate : ExponentGramCoordinate) :
    su2CoarseOuterExponentGramEntry
          G candidate hcandidate0 first coordinate ≤
        su2CoarseOuterExponentGramEntry
            G candidate hcandidate0 second coordinate + ε ∧
      su2CoarseOuterExponentGramEntry
          G candidate hcandidate0 second coordinate ≤
        su2CoarseOuterExponentGramEntry
            G candidate hcandidate0 first coordinate + ε := by
  let observable :=
    slabBooleanEventUnitObservable
      (centralExtent G.coarseHalf)
      (su2ExponentGramEvent
        G.coarseHalf coordinate)
  have hfirstCutoff :
      slabNomeBoundedObservableModulus
          candidate
          (centralExtent G.coarseHalf)
          ε ≤
        4 * first :=
    slabModulus_le_four_mul_of_coarseModulus_le
      G candidate ε hfirst
  have hsecondCutoff :
      slabNomeBoundedObservableModulus
          candidate
          (centralExtent G.coarseHalf)
          ε ≤
        4 * second :=
    slabModulus_le_four_mul_of_coarseModulus_le
      G candidate ε hsecond
  have hbounded :=
    slabNomeCutoffBoundedObservableExpectation_twoSided_of_modulus
      hcandidate0 hcandidate1
      (centralExtent G.coarseHalf)
      observable hε hfirstCutoff hsecondCutoff
  have hfirstEq :=
    su2CoarseOuterExponentGramEntry_eq_slabExpectation
      G candidate hcandidate0 first coordinate
  have hsecondEq :=
    su2CoarseOuterExponentGramEntry_eq_slabExpectation
      G candidate hcandidate0 second coordinate
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hfirstEq)
      (Q'.le_trans' _ _ _ hbounded.1
        (Q'.le_of_eqv
          (Q'.add_eqv_congr_right
            (slabNomeCutoffBoundedObservableExpectation
              candidate (Q'.le_of_lt hcandidate0)
              (4 * second)
              (centralExtent G.coarseHalf)
              observable)
            (su2CoarseOuterExponentGramEntry
              G candidate hcandidate0
              second coordinate)
            ε
            (Q'.eqv_symm hsecondEq))))
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hsecondEq)
      (Q'.le_trans' _ _ _ hbounded.2
        (Q'.le_of_eqv
          (Q'.add_eqv_congr_right
            (slabNomeCutoffBoundedObservableExpectation
              candidate (Q'.le_of_lt hcandidate0)
              (4 * first)
              (centralExtent G.coarseHalf)
              observable)
            (su2CoarseOuterExponentGramEntry
              G candidate hcandidate0
              first coordinate)
            ε
            (Q'.eqv_symm hfirstEq))))

/-! ## 4. Optional stochastic blocked-minus-coarse coordinate join -/

/-- Signed blocked-minus-coarse coordinate residual for a supplied
source-indexed stochastic physical contract. -/
def stochasticBlockedMinusCoarseCoordinateDifference
    {G : CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate) : Q' :=
  stochasticContractBlockedExponentGramEntry
      contract K coordinate +
    -su2CoarseOuterExponentGramEntry
      G candidate hcandidate K coordinate

/-- Combined half-tolerance modulus for one stochastic blocked-minus-coarse
coordinate. -/
def stochasticBlockedMinusCoarseCoordinateModulus
    (G : CutoffOneGeometry)
    (g candidate ε : Q') : Nat :=
  Nat.max
    (stochasticContractBlockedExponentGramModulus
      G g (HalfPow.half * ε))
    (su2CoarseOuterExponentGramModulus
      G candidate (HalfPow.half * ε))

private theorem twoSided_to_absQ_sub_le
    {a b ε : Q'}
    (h : a ≤ b + ε ∧ b ≤ a + ε) :
    absQ (a + (-b)) ≤ ε := by
  have hupper :
      a + (-b) ≤ ε :=
    Q'.sub_le_of_le_add h.1
  have hreverse :
      b + (-a) ≤ ε :=
    Q'.sub_le_of_le_add h.2
  have hnegative :
      -ε ≤ a + (-b) := by
    have hneg :
        -ε ≤ -(b + (-a)) :=
      Q'.neg_le_neg hreverse
    refine Q'.le_trans' _ _ _ hneg
      (Q'.le_of_eqv ?_)
    refine Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv b (-a)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left
        (-b) (-(-a)) a
        (Q'.neg_neg_eqv a)) ?_
    exact Q'.add_comm_eqv (-b) a
  exact
    YMGap.Continuum.FusionResidualBound.absQ_le
      hnegative hupper

private theorem pair_difference_rearrange
    (blocked coarse blockedLater coarseLater : Q') :
    ((blocked + (-coarse)) +
        (-(blockedLater + (-coarseLater)))) ≈
      (blocked + (-blockedLater)) +
        (coarseLater + (-coarse)) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left
      (blocked + (-coarse)) _ _
      (Q'.neg_add_eqv
        blockedLater (-coarseLater))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left
      (blocked + (-coarse))
      (-blockedLater + -(-coarseLater))
      (-blockedLater + coarseLater)
      (Q'.add_eqv_congr_left
        (-blockedLater)
        (-(-coarseLater)) coarseLater
        (Q'.neg_neg_eqv coarseLater))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_swap_inner
      blocked (-coarse)
      (-blockedLater) coarseLater) ?_
  exact Q'.add_eqv_congr_left
    (blocked + (-blockedLater))
    (-coarse + coarseLater)
    (coarseLater + (-coarse))
    (Q'.add_comm_eqv (-coarse) coarseLater)

private theorem twoSided_of_absQ_sub_le
    {a b ε : Q'}
    (h : absQ (a + (-b)) ≤ ε) :
    a ≤ b + ε ∧ b ≤ a + ε := by
  have habs : Q'.abs (a + (-b)) ≤ ε :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (YMGap.Continuum.ContinuumYMStack.absQ_eqv_abs
            (a + (-b)))))
      h
  constructor
  · exact
      YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
        habs
  · apply
      YMGap.Constructive.ExpNeg.le_add_of_abs_sub_le
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.TsumDeriv.Q'.abs_sub_comm
          b a))
      habs

/-- Conditional coordinate-wise Cauchy theorem for the signed stochastic
blocked-minus-coarse residual.  It composes the independent blocked and
coarse moduli and does not strengthen the open Markov-contract interface. -/
theorem
    stochasticBlockedMinusCoarseCoordinateDifference_twoSided_of_modulus
    {G : CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'}
    (hcandidate0 : (0 : Q') < candidate)
    (hcandidate1 : candidate < (1 : Q'))
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0)
        candidate hcandidate0)
    {ε : Q'} (hε : (0 : Q') < ε)
    {first second : Nat}
    (hfirst :
      stochasticBlockedMinusCoarseCoordinateModulus
          G g candidate ε ≤ first)
    (hsecond :
      stochasticBlockedMinusCoarseCoordinateModulus
          G g candidate ε ≤ second)
    (coordinate : ExponentGramCoordinate) :
    stochasticBlockedMinusCoarseCoordinateDifference
          contract first coordinate ≤
        stochasticBlockedMinusCoarseCoordinateDifference
            contract second coordinate + ε ∧
      stochasticBlockedMinusCoarseCoordinateDifference
          contract second coordinate ≤
        stochasticBlockedMinusCoarseCoordinateDifference
            contract first coordinate + ε := by
  let halfTolerance := HalfPow.half * ε
  have hhalf :
      (0 : Q') < halfTolerance :=
    YMGap.Constructive.ExpNeg.half_mul_pos ε hε
  have hblockedFirst :
      stochasticContractBlockedExponentGramModulus
          G g halfTolerance ≤ first :=
    Nat.le_trans
      (Nat.le_max_left _ _) hfirst
  have hblockedSecond :
      stochasticContractBlockedExponentGramModulus
          G g halfTolerance ≤ second :=
    Nat.le_trans
      (Nat.le_max_left _ _) hsecond
  have hcoarseFirst :
      su2CoarseOuterExponentGramModulus
          G candidate halfTolerance ≤ first :=
    Nat.le_trans
      (Nat.le_max_right _ _) hfirst
  have hcoarseSecond :
      su2CoarseOuterExponentGramModulus
          G candidate halfTolerance ≤ second :=
    Nat.le_trans
      (Nat.le_max_right _ _) hsecond
  have hblocked :=
    stochasticContractBlockedExponentGramEntry_twoSided_of_modulus
      hg0 hg1 contract hhalf
      hblockedFirst hblockedSecond coordinate
  have hcoarse :=
    su2CoarseOuterExponentGramEntry_twoSided_of_modulus
      G hcandidate0 hcandidate1 hhalf
      hcoarseFirst hcoarseSecond coordinate
  have hblockedAbs :
      absQ
          (stochasticContractBlockedExponentGramEntry
              contract first coordinate +
            -stochasticContractBlockedExponentGramEntry
              contract second coordinate) ≤
        halfTolerance :=
    twoSided_to_absQ_sub_le hblocked
  have hcoarseAbs :
      absQ
          (su2CoarseOuterExponentGramEntry
              G candidate hcandidate0
              second coordinate +
            -su2CoarseOuterExponentGramEntry
              G candidate hcandidate0
              first coordinate) ≤
        halfTolerance :=
    twoSided_to_absQ_sub_le
      ⟨hcoarse.2, hcoarse.1⟩
  have hresidualAbs :
      absQ
          (stochasticBlockedMinusCoarseCoordinateDifference
              contract first coordinate +
            -stochasticBlockedMinusCoarseCoordinateDifference
              contract second coordinate) ≤
        ε := by
    have hrearrange :=
      pair_difference_rearrange
        (stochasticContractBlockedExponentGramEntry
          contract first coordinate)
        (su2CoarseOuterExponentGramEntry
          G candidate hcandidate0
          first coordinate)
        (stochasticContractBlockedExponentGramEntry
          contract second coordinate)
        (su2CoarseOuterExponentGramEntry
          G candidate hcandidate0
          second coordinate)
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (YMGap.Continuum.ContinuumYMStack.absQ_eqv_congr
          hrearrange)) ?_
    refine Q'.le_trans' _ _ _
      (YMGap.Continuum.ContinuumYMStack.absQ_add_le _ _) ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add hblockedAbs hcoarseAbs) ?_
    exact Q'.le_of_eqv
      (YMGap.Constructive.ExpNeg.two_halves ε)
  exact twoSided_of_absQ_sub_le hresidualAbs

/-! ## Axiom audit -/

#print axioms slabBooleanEventUnitObservable
#print axioms
  su2CoarseOuterEventProbability_eq_slabExpectation
#print axioms
  su2CoarseOuterExponentGramEntry_eq_slabExpectation
#print axioms quarterCeil
#print axioms le_four_mul_quarterCeil
#print axioms su2CoarseOuterExponentGramModulus
#print axioms
  su2CoarseOuterExponentGramEntry_twoSided_of_modulus
#print axioms
  stochasticBlockedMinusCoarseCoordinateDifference_twoSided_of_modulus

end YMGap.Continuum.BF4SU2CoarseOuterExponentGramTail
