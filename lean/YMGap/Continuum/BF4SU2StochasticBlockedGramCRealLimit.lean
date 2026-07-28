/-
# Constructive-real stochastic blocked exponent-Gram limits

For one fixed geometry, one fixed rational nome `0 < g < 1`, one supplied
source-indexed physical Markov contract, and one exponent-Gram coordinate,
the explicit outer-cutoff modulus defines a Bishop constructive real.

The real's approximations are exactly the finite rational stochastic blocked
Gram entries.  The embedded rational sequence converges to it with the same
computable modulus, and any other constructive-real limit is constructively
equivalent.  The finite entries and the resulting limit lie in `[0,1]`.

This remains conditional on the supplied `SU2OuterPhysicalMarkovContract`.
It is pointwise in the fixed nome and coordinate; it supplies neither a
contract inhabitant nor uniformity in nome, geometry, volume, or spacing.

## Axiom gate

Exact `Q'` algebra and Bishop `CReal` data only.  No classical principle,
native decision shortcut, custom axiom, hidden proof hole, functional
extensionality, or noncomputable declaration.
-/

import YMGap.Continuum.BF4SU2StochasticBlockedGramObservableTail
import YMGap.Constructive.CRealAbs

namespace YMGap.Continuum.BF4SU2StochasticBlockedGramCRealLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.ExpPos
open YMGap.Continuum.BF4ExponentGramMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2OuterCutoffBlockGramContract
open YMGap.Continuum.BF4SU2StochasticBlockedGramObservableTail
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite rational unit-interval bounds -/

/-- Every finite stochastic blocked exponent-Gram coordinate is
nonnegative. -/
theorem stochasticContractBlockedExponentGramEntry_nonnegative
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg : (0 : Q') ≤ g)
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate) :
    (0 : Q') ≤
      stochasticContractBlockedExponentGramEntry
        contract K coordinate := by
  let observable :=
    stochasticContractExponentSlabUnitObservable
      contract coordinate
  have hnumerator :
      (0 : Q') ≤
        slabBoundedObservableNumerator
          g K (centralExtent G.fineHalf) observable :=
    slabBoundedObservableNumerator_nonnegative
      hg K (centralExtent G.fineHalf) observable
  have hexpectation :
      (0 : Q') ≤
        slabNomeCutoffBoundedObservableExpectation
          g hg K (centralExtent G.fineHalf)
          observable := by
    unfold slabNomeCutoffBoundedObservableExpectation
      Q'.divPos
    exact Q'.mul_nonneg _ _
      hnumerator
      (Q'.le_of_lt
        (Q'.recipPos_pos
          (slabParametricKPhysicalPartition
            g K (centralExtent G.fineHalf))
          (slabParametricKPhysicalPartition_pos
            hg K (centralExtent G.fineHalf))))
  have hjoin :=
    stochasticContractBlockedExponentGramEntry_eq_slabExpectation
      contract K coordinate
  exact Q'.le_trans' _ _ _
    hexpectation (Q'.ge_of_eqv hjoin)

/-- Every finite stochastic blocked exponent-Gram coordinate is at most
one. -/
theorem stochasticContractBlockedExponentGramEntry_le_one
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg : (0 : Q') ≤ g)
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate) :
    stochasticContractBlockedExponentGramEntry
        contract K coordinate ≤
      (1 : Q') := by
  let observable :=
    stochasticContractExponentSlabUnitObservable
      contract coordinate
  have hnumerator :
      slabBoundedObservableNumerator
          g K (centralExtent G.fineHalf) observable ≤
        slabParametricKPhysicalPartition
          g K (centralExtent G.fineHalf) :=
    slabBoundedObservableNumerator_le_partition
      hg K (centralExtent G.fineHalf) observable
  have hexpectation :
      slabNomeCutoffBoundedObservableExpectation
            g hg K (centralExtent G.fineHalf)
            observable ≤
        (1 : Q') := by
    unfold slabNomeCutoffBoundedObservableExpectation
    apply Q'.divPos_le_of_le_mul
    exact Q'.le_trans' _ _ _
      hnumerator
      (Q'.ge_of_eqv
        (Q'.one_mul_eqv
          (slabParametricKPhysicalPartition
            g K (centralExtent G.fineHalf))))
  have hjoin :=
    stochasticContractBlockedExponentGramEntry_eq_slabExpectation
      contract K coordinate
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hjoin) hexpectation

/-- The exact finite rational unit-interval certificate. -/
theorem stochasticContractBlockedExponentGramEntry_unitInterval
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg : (0 : Q') ≤ g)
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g hg candidate hcandidate)
    (K : Nat)
    (coordinate : ExponentGramCoordinate) :
    (0 : Q') ≤
        stochasticContractBlockedExponentGramEntry
          contract K coordinate ∧
      stochasticContractBlockedExponentGramEntry
          contract K coordinate ≤
        (1 : Q') :=
  ⟨stochasticContractBlockedExponentGramEntry_nonnegative
      hg contract K coordinate,
    stochasticContractBlockedExponentGramEntry_le_one
      hg contract K coordinate⟩

/-! ## 2. Exact rational sequence and Bishop limit -/

/-- The finite rational blocked Gram entries embedded as constant
constructive reals. -/
def stochasticContractBlockedExponentGramSeq
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0) candidate hcandidate)
    (coordinate : ExponentGramCoordinate) :
    Nat → CReal :=
  fun K =>
    CReal.ofQ'
      (stochasticContractBlockedExponentGramEntry
        contract K coordinate)

/-- Exact rational approximation identity for every embedded sequence
stage. -/
@[simp] theorem stochasticContractBlockedExponentGramSeq_approx
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0) candidate hcandidate)
    (coordinate : ExponentGramCoordinate)
    (K approximation : Nat) :
    (stochasticContractBlockedExponentGramSeq
        hg0 contract coordinate K).approx approximation =
      stochasticContractBlockedExponentGramEntry
        contract K coordinate :=
  rfl

/-- The pointwise fixed-nome stochastic blocked Gram limit as a Bishop real.
Its Cauchy witness is the executable degree-thirteen outer-cutoff modulus. -/
def stochasticContractBlockedExponentGramLimit
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0) candidate hcandidate)
    (coordinate : ExponentGramCoordinate) : CReal where
  approx K :=
    stochasticContractBlockedExponentGramEntry
      contract K coordinate
  cauchy := by
    intro ε hε
    refine
      ⟨stochasticContractBlockedExponentGramModulus
          G g ε,
        fun K L hK hL => ?_⟩
    exact
      stochasticContractBlockedExponentGramEntry_twoSided_of_modulus
        hg0 hg1 contract hε hK hL coordinate

/-- The Bishop real has exactly the finite rational blocked Gram entry as its
`K`-th approximation. -/
@[simp] theorem stochasticContractBlockedExponentGramLimit_approx
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0) candidate hcandidate)
    (coordinate : ExponentGramCoordinate)
    (K : Nat) :
    (stochasticContractBlockedExponentGramLimit
      hg0 hg1 contract coordinate).approx K =
        stochasticContractBlockedExponentGramEntry
          contract K coordinate :=
  rfl

/-! ## 3. Quantitative convergence and constructive uniqueness -/

/-- The constant-real embedding of the rational cutoff sequence converges to
the constructed Bishop real with the same explicit outer-cutoff modulus. -/
theorem stochasticContractBlockedExponentGramSeq_converges
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0) candidate hcandidate)
    (coordinate : ExponentGramCoordinate) :
    CReal.ConvergesTo
      (stochasticContractBlockedExponentGramSeq
        hg0 contract coordinate)
      (stochasticContractBlockedExponentGramLimit
        hg0 hg1 contract coordinate) := by
  intro ε hε
  let M :=
    stochasticContractBlockedExponentGramModulus
      G g ε
  refine ⟨M, fun K hK => ⟨M, fun n hn => ?_⟩⟩
  change
    stochasticContractBlockedExponentGramEntry
          contract K coordinate ≤
        stochasticContractBlockedExponentGramEntry
            contract n coordinate + ε ∧
      stochasticContractBlockedExponentGramEntry
          contract n coordinate ≤
        stochasticContractBlockedExponentGramEntry
            contract K coordinate + ε
  exact
    stochasticContractBlockedExponentGramEntry_twoSided_of_modulus
      hg0 hg1 contract hε hK hn coordinate

private theorem crealEquiv_refl (x : CReal) :
    CReal.Equiv x x :=
  fun ε hε =>
    ⟨0, fun n _ =>
      ⟨Q'.add_le_self_of_nonneg
          (x.approx n) ε (Q'.le_of_lt hε),
        Q'.add_le_self_of_nonneg
          (x.approx n) ε (Q'.le_of_lt hε)⟩⟩

/-- Constructive uniqueness: every other constructive-real limit of the same
embedded rational cutoff sequence is equivalent to the explicitly constructed
blocked Gram limit. -/
theorem
    stochasticContractBlockedExponentGramLimit_equiv_of_converges
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0) candidate hcandidate)
    (coordinate : ExponentGramCoordinate)
    (other : CReal)
    (hother :
      CReal.ConvergesTo
        (stochasticContractBlockedExponentGramSeq
          hg0 contract coordinate)
        other) :
    CReal.Equiv
      (stochasticContractBlockedExponentGramLimit
        hg0 hg1 contract coordinate)
      other := by
  exact CReal.Equiv_of_limit_of_equal
    (fun K =>
      crealEquiv_refl
        (stochasticContractBlockedExponentGramSeq
          hg0 contract coordinate K))
    (stochasticContractBlockedExponentGramSeq_converges
      hg0 hg1 contract coordinate)
    hother

/-! ## 4. Unit-interval bounds inherited by the limit -/

/-- The limit is nonnegative in the direct Bishop one-slack order. -/
theorem stochasticContractBlockedExponentGramLimit_nonnegative
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0) candidate hcandidate)
    (coordinate : ExponentGramCoordinate) :
    CReal.ofQ' 0 ≤
      stochasticContractBlockedExponentGramLimit
        hg0 hg1 contract coordinate :=
  CReal.ofQ'_le_of_approx_ge
    (fun K =>
      stochasticContractBlockedExponentGramEntry_nonnegative
        (Q'.le_of_lt hg0) contract K coordinate)

/-- The limit is at most one in the direct Bishop one-slack order. -/
theorem stochasticContractBlockedExponentGramLimit_le_one
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0) candidate hcandidate)
    (coordinate : ExponentGramCoordinate) :
    stochasticContractBlockedExponentGramLimit
        hg0 hg1 contract coordinate ≤
      CReal.ofQ' 1 :=
  CReal.le_ofQ'_of_approx_le
    (fun K =>
      stochasticContractBlockedExponentGramEntry_le_one
        (Q'.le_of_lt hg0) contract K coordinate)

/-- Regularity-free lower bound: the limit is at least zero. -/
theorem stochasticContractBlockedExponentGramLimit_geRat_zero
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0) candidate hcandidate)
    (coordinate : ExponentGramCoordinate) :
    ExpPos.geRat
      (stochasticContractBlockedExponentGramLimit
        hg0 hg1 contract coordinate)
      0 :=
  ExpPos.geRat_of_eventually
    ⟨0, fun K _ =>
      stochasticContractBlockedExponentGramEntry_nonnegative
        (Q'.le_of_lt hg0) contract K coordinate⟩

/-- Regularity-free upper bound: the limit is at most one. -/
theorem stochasticContractBlockedExponentGramLimit_leRat_one
    {G :
      YMGap.Continuum.BF4ObservableMatchedOneStep.CutoffOneGeometry}
    {g : Q'} (hg0 : (0 : Q') < g)
    (hg1 : g < (1 : Q'))
    {candidate : Q'} {hcandidate : (0 : Q') < candidate}
    (contract :
      SU2OuterPhysicalMarkovContract
        G g (Q'.le_of_lt hg0) candidate hcandidate)
    (coordinate : ExponentGramCoordinate) :
    CReal.leRat
      (stochasticContractBlockedExponentGramLimit
        hg0 hg1 contract coordinate)
      1 :=
  CReal.leRat_of_eventually
    ⟨0, fun K _ =>
      stochasticContractBlockedExponentGramEntry_le_one
        (Q'.le_of_lt hg0) contract K coordinate⟩

#print axioms stochasticContractBlockedExponentGramEntry_unitInterval
#print axioms stochasticContractBlockedExponentGramSeq_approx
#print axioms stochasticContractBlockedExponentGramLimit
#print axioms stochasticContractBlockedExponentGramLimit_approx
#print axioms stochasticContractBlockedExponentGramSeq_converges
#print axioms
  stochasticContractBlockedExponentGramLimit_equiv_of_converges
#print axioms stochasticContractBlockedExponentGramLimit_nonnegative
#print axioms stochasticContractBlockedExponentGramLimit_le_one
#print axioms stochasticContractBlockedExponentGramLimit_geRat_zero
#print axioms stochasticContractBlockedExponentGramLimit_leRat_one

end YMGap.Continuum.BF4SU2StochasticBlockedGramCRealLimit
