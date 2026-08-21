/-
# Fixed-nome cutoff limit of the physical BF4 autocorrelation form

The stationary cutoff functional controls ordinary product moments.  The next
same-object datum is the one-step physical transfer autocorrelation
`<a, P a>`.  At every finite cutoff this is the quadratic of the normalized
reflected joint law.  The existing full-slab reindex identifies that quadratic
with the corrected-slab expectation of

  `a(lower restriction) * a(reflected upper restriction)`.

For a `[0,1]` lower observable this is again a cutoff-stable `[0,1]` slab
observable, so the executable fixed-nome outer-cutoff modulus applies.  We
therefore construct a Bishop-real cutoff limit whose approximations are
definitionally the actual physical Markov forms.  Positivity and the identity
form upper bound pass pointwise to the limit.

This is a form-level limit, not a cutoff limit of the transfer operator or its
Hilbert carrier.  Nome, half-extent, and finite physical volume remain fixed;
no centered strict contraction, thermodynamic/spacing limit, or Clay theorem
is claimed.

Axiom gate: constructive finite-list and rational algebra plus Bishop `CReal`.
No `Classical`, `sorry`, `native_decide`, choice, functional extensionality,
noncomputable declaration, or custom axiom.
-/

import YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
import YMGap.Continuum.BF4PhysicalMarkovTransferLaws

namespace YMGap.Continuum.BF4PhysicalCutoffAutocorrelationLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4ExactPhysicalPerronReroute
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4SU2CorrectedSlabBoundedObservableTail
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The same-object two-sided slab observable -/

/-- Product of the lower insertion and its reflected upper copy on the full
corrected slab. -/
def centralAutocorrelationSlabUnitObservable
    (half : Nat) (observable : CentralPhysicalUnitObservable) :
    CutoffStableSlabUnitObservable (centralExtent half) where
  value _ physical :=
    observable.value (centralLowerRestriction half physical) *
      observable.value
        (centralReflectedUpperRestriction half physical)
  nonnegative := by
    intro _ physical _
    exact Q'.mul_nonneg _ _
      (observable.nonnegative
        (centralLowerRestriction half physical))
      (observable.nonnegative
        (centralReflectedUpperRestriction half physical))
  le_one := by
    intro _ physical _
    refine Q'.le_trans' _ ((1 : Q') * 1) _ ?_ ?_
    · exact Q'.mul_le_mul_of_nonneg
        (observable.le_one
          (centralLowerRestriction half physical))
        (observable.le_one
          (centralReflectedUpperRestriction half physical))
        Q'.zero_le_one
        (observable.nonnegative
          (centralReflectedUpperRestriction half physical))
    · exact Q'.le_of_eqv (Q'.one_mul_eqv 1)
  cutoff_stable := by
    intro _ _ physical _ _
    exact Q'.eqv_refl _

@[simp] theorem centralAutocorrelationSlabUnitObservable_value
    (half cutoff : Nat) (observable : CentralPhysicalUnitObservable)
    (physical : EdgeLabelling) :
    (centralAutocorrelationSlabUnitObservable
      half observable).value cutoff physical =
      observable.value (centralLowerRestriction half physical) *
        observable.value
          (centralReflectedUpperRestriction half physical) := rfl

/-! ## 2. Exact finite Markov-form identification -/

/-- The normalized full physical reflection quadratic is exactly the
corrected-slab bounded-observable expectation of the same-object insertion. -/
theorem
    centralNormalizedFullPhysicalReflectionQuadratic_eq_slabExpectation
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (observable : CentralPhysicalUnitObservable) :
    centralNormalizedFullPhysicalReflectionQuadratic
        w hw cutoff half observable.value ≈
      slabNomeCutoffBoundedObservableExpectation
        w hw cutoff (centralExtent half)
        (centralAutocorrelationSlabUnitObservable half observable) := by
  unfold centralNormalizedFullPhysicalReflectionQuadratic
    slabNomeCutoffBoundedObservableExpectation Q'.divPos
    centralFullPhysicalReflectionQuadratic
    slabBoundedObservableNumerator
  exact Q'.eqv_refl _

/-- **Finite same-object bridge.**  The physical weighted Markov form is the
exact corrected-slab expectation of the reflected same-object insertion. -/
theorem centralPhysicalMarkovAutocorrelation_eq_slabExpectation
    (w : Q') (hw : (0 : Q') ≤ w)
    (cutoff half : Nat) (observable : CentralPhysicalUnitObservable) :
    centralPhysicalWeightedInner
        w hw cutoff half observable.value
        (centralPhysicalMarkovApply
          w hw cutoff half observable.value) ≈
      slabNomeCutoffBoundedObservableExpectation
        w hw cutoff (centralExtent half)
        (centralAutocorrelationSlabUnitObservable half observable) :=
  Q'.eqv_trans _ _ _
    (centralPhysicalWeightedMarkovQuadratic_eq_joint
      w hw cutoff half observable.value)
    (Q'.eqv_trans _ _ _
      (centralPhysicalJointQuadratic_eq_normalizedFull
        w hw cutoff half observable.value)
      (centralNormalizedFullPhysicalReflectionQuadratic_eq_slabExpectation
        w hw cutoff half observable))

/-! ## 3. Bishop limit of the actual physical autocorrelation form -/

/-- Cutoff-removed one-step same-object physical autocorrelation.  Its
`cutoff`-th rational approximation is definitionally the finite GNS transfer
form at that cutoff. -/
def centralPhysicalAutocorrelationCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalUnitObservable) : CReal where
  approx cutoff :=
    centralPhysicalWeightedInner
      w (Q'.le_of_lt hw0) cutoff half observable.value
      (centralPhysicalMarkovApply
        w (Q'.le_of_lt hw0) cutoff half observable.value)
  cauchy := by
    intro epsilon hepsilon
    refine ⟨slabNomeBoundedObservableModulus
        w (centralExtent half) epsilon,
      fun first second hfirst hsecond => ?_⟩
    have hslab :=
      slabNomeCutoffBoundedObservableExpectation_twoSided_of_modulus
        hw0 hw1 (centralExtent half)
        (centralAutocorrelationSlabUnitObservable half observable)
        hepsilon hfirst hsecond
    have hfirstBridge :=
      centralPhysicalMarkovAutocorrelation_eq_slabExpectation
        w (Q'.le_of_lt hw0) first half observable
    have hsecondBridge :=
      centralPhysicalMarkovAutocorrelation_eq_slabExpectation
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

@[simp] theorem centralPhysicalAutocorrelationCutoffLimit_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) (observable : CentralPhysicalUnitObservable) :
    (centralPhysicalAutocorrelationCutoffLimit
      hw0 hw1 half observable).approx cutoff =
      centralPhysicalWeightedInner
        w (Q'.le_of_lt hw0) cutoff half observable.value
        (centralPhysicalMarkovApply
          w (Q'.le_of_lt hw0) cutoff half observable.value) := rfl

/-! ## 4. Limiting positive identity-form interval -/

/-- Positivity of the finite physical transfer form survives the cutoff
limit. -/
theorem centralPhysicalAutocorrelationCutoffLimit_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalUnitObservable) :
    CReal.czero ≤
      centralPhysicalAutocorrelationCutoffLimit
        hw0 hw1 half observable := by
  apply CReal.ofQ'_le_of_approx_ge
  intro cutoff
  exact centralPhysicalMarkovApply_positive
    w (Q'.le_of_lt hw0) cutoff half observable.value

/-- The cutoff-limit autocorrelation is bounded by the limiting stationary
norm square of the same observable. -/
theorem centralPhysicalAutocorrelationCutoffLimit_le_norm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalUnitObservable) :
    centralPhysicalAutocorrelationCutoffLimit
        hw0 hw1 half observable ≤
      (centralPhysicalStationaryCutoffProbFunctional
        hw0 hw1 half).E
        (centralPhysicalUnitObsAlg.mul
          (centralPhysicalUnitObsAlg.star observable) observable) := by
  intro cutoff
  change
    centralPhysicalWeightedInner
          w (Q'.le_of_lt hw0) cutoff half observable.value
          (centralPhysicalMarkovApply
            w (Q'.le_of_lt hw0) cutoff half observable.value) ≤
      centralPhysicalWeightedInner
          w (Q'.le_of_lt hw0) cutoff half
          observable.value observable.value +
        Q'.invSucc cutoff
  exact Q'.le_trans' _ _ _
    (centralPhysicalMarkovApply_form_interval
      w (Q'.le_of_lt hw0) cutoff half observable.value).2
    (Q'.add_le_self_of_nonneg _ _
      (Q'.invSucc_nonneg cutoff))

/-! ## Axiom audit -/

#print axioms centralAutocorrelationSlabUnitObservable
#print axioms centralPhysicalMarkovAutocorrelation_eq_slabExpectation
#print axioms centralPhysicalAutocorrelationCutoffLimit
#print axioms centralPhysicalAutocorrelationCutoffLimit_nonnegative
#print axioms centralPhysicalAutocorrelationCutoffLimit_le_norm

end YMGap.Continuum.BF4PhysicalCutoffAutocorrelationLimit
