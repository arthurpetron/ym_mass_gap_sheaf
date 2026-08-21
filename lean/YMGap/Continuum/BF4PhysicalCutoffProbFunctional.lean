/-
# Fixed-nome cutoff-removed BF4 probability functional

The corrected-slab BF4 cutoff tail already proves an executable two-sided
Cauchy modulus for every cutoff-stable `[0,1]`-valued observable at a fixed
rational nome `0 < w < 1` and fixed finite slab extent.  This module packages
that result as one positive normalized `CReal`-valued functional.

The observable carrier is deliberately minimal.  It contains coherent unit
observables and is closed under pointwise product; star is identity.  This is
enough for the repository's `ObsAlg` and `CRealProbFunctional` interfaces.
It is not an additive algebra, because the unit interval is not closed under
addition.  Accordingly no linearity is claimed.

This removes only the Peter--Weyl representation cutoff.  The nome, lattice
geometry, and physical volume remain fixed.  No thermodynamic limit, spacing
limit, OS reconstruction, non-triviality, or mass-gap conclusion is claimed.

Axiom gate: finite `List`, `Nat`, `Q'`, and the Bishop `CReal` completion.
There is no `Classical`, `sorry`, `native_decide`, choice, functional
extensionality, noncomputable declaration, or custom axiom.
-/

import YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
import YMGap.Continuum.ContinuumFunctional
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.BF4PhysicalCutoffProbFunctional

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.ContinuumFunctional
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The multiplicative cutoff-stable observable algebra -/

/-- The constant-one coherent slab observable. -/
def slabUnitObservable (extent : Nat) :
    CutoffStableSlabUnitObservable extent where
  value _ _ := 1
  nonnegative := by
    intro _ _ _
    exact Q'.zero_le_one
  le_one := by
    intro _ _ _
    exact Q'.le_refl' 1
  cutoff_stable := by
    intro _ _ _ _ _
    exact Q'.eqv_refl 1

/-- Pointwise product of coherent unit-interval slab observables. -/
def slabObservableMul {extent : Nat}
    (left right : CutoffStableSlabUnitObservable extent) :
    CutoffStableSlabUnitObservable extent where
  value cutoff state :=
    left.value cutoff state * right.value cutoff state
  nonnegative := by
    intro cutoff state hstate
    exact Q'.mul_nonneg _ _
      (left.nonnegative cutoff state hstate)
      (right.nonnegative cutoff state hstate)
  le_one := by
    intro cutoff state hstate
    refine Q'.le_trans' _ ((1 : Q') * 1) _ ?_ ?_
    · exact Q'.mul_le_mul_of_nonneg
        (left.le_one cutoff state hstate)
        (right.le_one cutoff state hstate)
        Q'.zero_le_one
        (right.nonnegative cutoff state hstate)
    · exact Q'.le_of_eqv (Q'.one_mul_eqv 1)
  cutoff_stable := by
    intro cutoff later state hcutoff hstate
    exact Q'.eqv_trans _
      (left.value later state * right.value cutoff state) _
      (Q'.mul_eqv_congr_right _ _ _
        (left.cutoff_stable cutoff later state hcutoff hstate))
      (Q'.mul_eqv_congr_left _ _ _
        (right.cutoff_stable cutoff later state hcutoff hstate))

/-- Minimal multiplicative observable algebra on the fixed corrected slab. -/
def slabCutoffObsAlg (extent : Nat) : ObsAlg where
  carrier := CutoffStableSlabUnitObservable extent
  one := slabUnitObservable extent
  mul := slabObservableMul
  star := fun observable => observable

@[simp] theorem slabUnitObservable_value
    (extent cutoff : Nat) (state : EdgeLabelling) :
    (slabUnitObservable extent).value cutoff state = 1 := rfl

@[simp] theorem slabObservableMul_value
    {extent : Nat}
    (left right : CutoffStableSlabUnitObservable extent)
    (cutoff : Nat) (state : EdgeLabelling) :
    (slabObservableMul left right).value cutoff state =
      left.value cutoff state * right.value cutoff state := rfl

/-! ## 2. Exact finite expectations and their Bishop limits -/

/-- Every finite normalized bounded-observable expectation is nonnegative. -/
theorem slabNomeCutoffBoundedObservableExpectation_nonnegative
    {w : Q'} (hw : (0 : Q') ≤ w)
    (cutoff extent : Nat)
    (observable : CutoffStableSlabUnitObservable extent) :
    (0 : Q') ≤
      slabNomeCutoffBoundedObservableExpectation
        w hw cutoff extent observable := by
  unfold slabNomeCutoffBoundedObservableExpectation Q'.divPos
  exact Q'.mul_nonneg _ _
    (slabBoundedObservableNumerator_nonnegative
      hw cutoff extent observable)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (slabParametricKPhysicalPartition_pos
          hw cutoff extent)))

/-- The constant-one numerator is equivalent to the exact finite partition. -/
theorem slabBoundedObservableNumerator_unit_eqv_partition
    (w : Q') (cutoff extent : Nat) :
    slabBoundedObservableNumerator
        w cutoff extent (slabUnitObservable extent) ≈
      slabParametricKPhysicalPartition w cutoff extent := by
  unfold slabBoundedObservableNumerator
    slabParametricKPhysicalPartition
  exact listQSum_congr
    (fun state =>
      Q'.one_mul_eqv
        (slabParametricKPhysicalTerm
          w cutoff extent state))
    (boundedEdgeLabellings cutoff
      (slabPhysicalFaceEdges extent))

/-- At each finite cutoff, the coherent unit has normalized expectation one
modulo the intended rational equivalence. -/
theorem slabNomeCutoffBoundedObservableExpectation_unit_eqv_one
    {w : Q'} (hw : (0 : Q') ≤ w)
    (cutoff extent : Nat) :
    slabNomeCutoffBoundedObservableExpectation
        w hw cutoff extent (slabUnitObservable extent) ≈
      (1 : Q') := by
  unfold slabNomeCutoffBoundedObservableExpectation Q'.divPos
  refine Q'.eqv_trans _
    (slabParametricKPhysicalPartition w cutoff extent *
      Q'.recipPos
        (slabParametricKPhysicalPartition w cutoff extent)
        (slabParametricKPhysicalPartition_pos hw cutoff extent)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (slabBoundedObservableNumerator_unit_eqv_partition
        w cutoff extent)
  · exact Q'.mul_recipPos_eqv
      (slabParametricKPhysicalPartition w cutoff extent)
      (slabParametricKPhysicalPartition_pos hw cutoff extent)

/-- The exact cutoff expectations, embedded as constant constructive reals. -/
def slabNomeCutoffObservableSeq
    {w : Q'} (hw : (0 : Q') ≤ w)
    (extent : Nat)
    (observable : CutoffStableSlabUnitObservable extent) :
    Nat → CReal :=
  fun cutoff => CReal.ofQ'
    (slabNomeCutoffBoundedObservableExpectation
      w hw cutoff extent observable)

/-- The representation-cutoff-removed expectation of one coherent bounded
observable.  Its Cauchy witness is the existing executable degree-thirteen
nome-dependent cutoff modulus. -/
def slabNomeCutoffObservableLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat)
    (observable : CutoffStableSlabUnitObservable extent) : CReal where
  approx cutoff :=
    slabNomeCutoffBoundedObservableExpectation
      w (Q'.le_of_lt hw0) cutoff extent observable
  cauchy := by
    intro epsilon hepsilon
    refine ⟨slabNomeBoundedObservableModulus w extent epsilon,
      fun first second hfirst hsecond => ?_⟩
    exact
      slabNomeCutoffBoundedObservableExpectation_twoSided_of_modulus
        hw0 hw1 extent observable hepsilon hfirst hsecond

@[simp] theorem slabNomeCutoffObservableLimit_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat)
    (observable : CutoffStableSlabUnitObservable extent)
    (cutoff : Nat) :
    (slabNomeCutoffObservableLimit
      hw0 hw1 extent observable).approx cutoff =
      slabNomeCutoffBoundedObservableExpectation
        w (Q'.le_of_lt hw0) cutoff extent observable := rfl

/-! ## 3. The actual cutoff-removed positive normalized functional -/

/-- At fixed `0 < w < 1` and fixed finite extent, the actual corrected-slab
BF4 expectations define a positive normalized `CReal` functional after the
Peter--Weyl cutoff is removed. -/
def slabNomeCutoffProbFunctional
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) :
    CRealProbFunctional (slabCutoffObsAlg extent) where
  E := slabNomeCutoffObservableLimit hw0 hw1 extent
  normalized := by
    apply Equiv_of_approx_eqv
    intro cutoff
    exact
      slabNomeCutoffBoundedObservableExpectation_unit_eqv_one
        (Q'.le_of_lt hw0) cutoff extent
  positive := by
    intro observable
    apply CReal.ofQ'_le_of_approx_ge
    intro cutoff
    exact
      slabNomeCutoffBoundedObservableExpectation_nonnegative
        (Q'.le_of_lt hw0) cutoff extent
        (slabObservableMul observable observable)

/-- Every approximation of the cutoff-removed functional is exactly the
finite corrected-slab BF4 expectation at that representation cutoff. -/
@[simp] theorem slabNomeCutoffProbFunctional_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent cutoff : Nat)
    (observable : CutoffStableSlabUnitObservable extent) :
    ((slabNomeCutoffProbFunctional hw0 hw1 extent).E
      observable).approx cutoff =
      slabNomeCutoffBoundedObservableExpectation
        w (Q'.le_of_lt hw0) cutoff extent observable := rfl

/-! ## Axiom audit -/

#print axioms slabUnitObservable
#print axioms slabObservableMul
#print axioms slabCutoffObsAlg
#print axioms slabNomeCutoffObservableLimit
#print axioms slabNomeCutoffProbFunctional
#print axioms slabNomeCutoffProbFunctional_approx

end YMGap.Continuum.BF4PhysicalCutoffProbFunctional
