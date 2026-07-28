/-
# Stochastic blocked exponent-Gram tails on the corrected slab

This join module connects the source-indexed stochastic outer-cutoff
contract to the cutoff-stable `[0,1]` corrected-slab observable theorem.
The conditional exponent event probability is packaged as the required
observable, and the existing stochastic Fubini identity is identified
exactly with its normalized corrected-slab expectation.

For every fixed rational `0 < g < 1`, the result is a quantitative
new-label tail and an executable two-sided Cauchy modulus for each blocked
exponent-Gram coordinate.

This is conditional on an inhabitant of `SU2OuterPhysicalMarkovContract`.
That structure still contains the open physical recoupling construction and
its lossless old-source/no-new-target support law.  No such inhabitant, no
continuum limit, and no Clay-level conclusion are constructed here.

## Axiom gate

Finite `List`, `Nat`, and `Q'` algebra only.  No classical principle,
native decision shortcut, custom axiom, hidden proof hole, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
import YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract

namespace YMGap.Continuum.BF4SU2StochasticBlockedGramObservableTail

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2CorrectedSlabOuterCutoffTail
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PhysicalOuterCutoffNomeTolerance
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The concrete cutoff-stable conditional observable -/

/-- The conditional exponent-event probability supplied by a stochastic
physical Markov contract, packaged on the literal fine corrected slab. -/
def stochasticContractExponentSlabUnitObservable
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (coordinate : ExponentGramCoordinate) :
    CutoffStableSlabUnitObservable
      (centralExtent G.fineHalf) where
  value K source :=
    stochasticContractExponentEventProbability
      contract K coordinate source
  nonnegative := by
    intro K source hsource
    exact
      stochasticContractExponentEventProbability_nonnegative
        contract K coordinate hsource
  le_one := by
    intro K source hsource
    exact
      stochasticContractExponentEventProbability_le_one
        contract K coordinate hsource
  cutoff_stable := by
    intro K L source hKL hsource
    exact
      stochasticContractExponentEventProbability_cutoff_stable
        contract hKL coordinate hsource

/-! ## 2. Exact identification of the two normalized expectations -/

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
    · exact listQSum_mul_right weightedTerm reciprocal _
    · unfold slabNomeCutoffBoundedObservableExpectation
        slabBoundedObservableNumerator Q'.divPos
      dsimp only [weightedTerm, reciprocal]
      exact Q'.eqv_refl _

/-- Exact join: the stochastic blocked exponent-Gram coordinate is the
normalized corrected-slab expectation of its concrete conditional event
observable. -/
theorem
    stochasticContractBlockedExponentGramEntry_eq_slabExpectation
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} {hg : (0 : Q') ≤ g}
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate) :
    stochasticContractBlockedExponentGramEntry
        contract K coordinate ≈
      slabNomeCutoffBoundedObservableExpectation
        g hg K
        (centralExtent G.fineHalf)
        (stochasticContractExponentSlabUnitObservable
          contract coordinate) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        (su2FineOuterData G g hg K).normalizedMass source *
          stochasticContractExponentEventProbability
            contract K coordinate source)
      (su2FineOuterData
        G g hg K).physicalLabellings) _ ?_ ?_
  · exact
      stochasticContractBlockedExponentGramEntry_eq_fineBoundedExpectation
        contract K coordinate
  · change
      listQSum
          (fun state =>
            Q'.divPos
                (slabParametricKPhysicalTerm
                  g K (centralExtent G.fineHalf) state)
                (slabParametricKPhysicalPartition
                  g K (centralExtent G.fineHalf))
                (slabParametricKPhysicalPartition_pos
                  hg K (centralExtent G.fineHalf)) *
              (stochasticContractExponentSlabUnitObservable
                contract coordinate).value K state)
          (boundedEdgeLabellings K
            (slabPhysicalFaceEdges
              (centralExtent G.fineHalf))) ≈
        slabNomeCutoffBoundedObservableExpectation
          g hg K (centralExtent G.fineHalf)
          (stochasticContractExponentSlabUnitObservable
            contract coordinate)
    exact normalizedSlabListExpectation_eq_boundedExpectation
      hg K (centralExtent G.fineHalf)
      (stochasticContractExponentSlabUnitObservable
        contract coordinate)

/-! ## 3. Fixed-nome quantitative tails -/

/-- At arbitrary nonnegative nome, changing the outer cutoff changes one
stochastic blocked exponent-Gram entry by at most the complete corrected-slab
new-label mass. -/
theorem
    stochasticContractBlockedExponentGramEntry_abs_le_increment
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg : (0 : Q') ≤ g)
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    {K L : Nat} (hKL : K ≤ L)
    (coordinate : ExponentGramCoordinate) :
    absQ
        (stochasticContractBlockedExponentGramEntry
            contract K coordinate +
          -stochasticContractBlockedExponentGramEntry
            contract L coordinate) ≤
      slabParametricKCutoffIncrement
        g K L (centralExtent G.fineHalf) := by
  have hK :=
    stochasticContractBlockedExponentGramEntry_eq_slabExpectation
      contract K coordinate
  have hL :=
    stochasticContractBlockedExponentGramEntry_eq_slabExpectation
      contract L coordinate
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (YMGap.Continuum.ContinuumYMStack.absQ_eqv_congr
        (Q'.add_eqv_congr'
          hK (Q'.neg_eqv_congr _ _ hL))))
    (slabNomeCutoffBoundedObservableExpectation_abs_le_increment
      hg hKL
      (stochasticContractExponentSlabUnitObservable
        contract coordinate))

/-- The explicit degree-thirteen retained cutoff pays the stochastic blocked
Gram-entry tail for every fixed rational `0 < g < 1`. -/
theorem
    stochasticContractBlockedExponentGramEntry_abs_le_tolerance
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0) candidate hcandidate)
    {ε : Q'} (hε : (0 : Q') < ε)
    {L : Nat}
    (hL :
      physicalNomeTensorToleranceRetainedCutoff
          g
          (plaquetteEdgeCount
            (centralExtent G.fineHalf + 1))
          ε ≤ L)
    (coordinate : ExponentGramCoordinate) :
    absQ
        (stochasticContractBlockedExponentGramEntry
            contract
            (physicalNomeTensorToleranceRetainedCutoff
              g
              (plaquetteEdgeCount
                (centralExtent G.fineHalf + 1))
              ε)
            coordinate +
          -stochasticContractBlockedExponentGramEntry
            contract L coordinate) ≤
      ε := by
  exact Q'.le_trans' _ _ _
    (stochasticContractBlockedExponentGramEntry_abs_le_increment
      (Q'.le_of_lt hg0) contract hL coordinate)
    (slabPhysicalNomeCutoffIncrement_le_tolerance
      hg0 hg1 (centralExtent G.fineHalf) hε hL)

/-! ## 4. Executable two-sided Cauchy modulus -/

/-- Executable cutoff modulus for one fixed-name stochastic blocked
exponent-Gram family.  It is independent of the coordinate because the
complete new-label mass pays every `[0,1]` observable simultaneously. -/
def stochasticContractBlockedExponentGramModulus
    (G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry)
    (g : Q') (ε : Q') : Nat :=
  slabNomeBoundedObservableModulus
    g (centralExtent G.fineHalf) ε

/-- Two stochastic blocked exponent-Gram entries beyond the executable
modulus are mutually within `ε`. -/
theorem
    stochasticContractBlockedExponentGramEntry_twoSided_of_modulus
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0) candidate hcandidate)
    {ε : Q'} (hε : (0 : Q') < ε)
    {first second : Nat}
    (hfirst :
      stochasticContractBlockedExponentGramModulus
          G g ε ≤ first)
    (hsecond :
      stochasticContractBlockedExponentGramModulus
          G g ε ≤ second)
    (coordinate : ExponentGramCoordinate) :
    stochasticContractBlockedExponentGramEntry
          contract first coordinate ≤
        stochasticContractBlockedExponentGramEntry
            contract second coordinate + ε ∧
      stochasticContractBlockedExponentGramEntry
          contract second coordinate ≤
        stochasticContractBlockedExponentGramEntry
            contract first coordinate + ε := by
  let observable :=
    stochasticContractExponentSlabUnitObservable
      contract coordinate
  have hbounded :=
    slabNomeCutoffBoundedObservableExpectation_twoSided_of_modulus
      hg0 hg1 (centralExtent G.fineHalf)
      observable hε hfirst hsecond
  have hfirstEq :=
    stochasticContractBlockedExponentGramEntry_eq_slabExpectation
      contract first coordinate
  have hsecondEq :=
    stochasticContractBlockedExponentGramEntry_eq_slabExpectation
      contract second coordinate
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hfirstEq)
      (Q'.le_trans' _ _ _ hbounded.1
        (Q'.le_of_eqv
          (Q'.add_eqv_congr_right
            (slabNomeCutoffBoundedObservableExpectation
              g (Q'.le_of_lt hg0) second
              (centralExtent G.fineHalf) observable)
            (stochasticContractBlockedExponentGramEntry
              contract second coordinate)
            ε
            (Q'.eqv_symm hsecondEq))))
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv hsecondEq)
      (Q'.le_trans' _ _ _ hbounded.2
        (Q'.le_of_eqv
          (Q'.add_eqv_congr_right
            (slabNomeCutoffBoundedObservableExpectation
              g (Q'.le_of_lt hg0) first
              (centralExtent G.fineHalf) observable)
            (stochasticContractBlockedExponentGramEntry
              contract first coordinate)
            ε
            (Q'.eqv_symm hfirstEq))))

#print axioms stochasticContractExponentSlabUnitObservable
#print axioms
  stochasticContractBlockedExponentGramEntry_eq_slabExpectation
#print axioms
  stochasticContractBlockedExponentGramEntry_abs_le_increment
#print axioms
  stochasticContractBlockedExponentGramEntry_abs_le_tolerance
#print axioms stochasticContractBlockedExponentGramModulus
#print axioms
  stochasticContractBlockedExponentGramEntry_twoSided_of_modulus

end YMGap.Continuum.BF4SU2StochasticBlockedGramObservableTail
