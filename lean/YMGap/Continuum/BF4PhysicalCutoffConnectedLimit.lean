/-
# Fixed-nome connected physical BF4 cutoff limits

The ordinary stationary moment and the same-object one-step Markov moment now
have actual representation-cutoff limits.  This module contracts those two
limits into the connected quantities

  norm(a)      - mean(a)^2,
  <a, P a>     - mean(a)^2.

Because `CReal.add`, `CReal.neg`, and `CReal.mul` act pointwise on rational
approximations, the resulting Bishop reals have exactly those finite centered
expressions at every cutoff.  The existing finite centering identities then
identify them with the norm and Markov form of the literal marginal-centered
observable.  Positivity and the identity-form upper bound survive the cutoff
limit.

This is still a form-level, fixed-nome, fixed-finite-volume result.  It does
not construct a cutoff-independent transfer operator or Hilbert carrier, and
does not prove a strict centered contraction uniform in physical scale.

Axiom gate: constructive rational and Bishop-real algebra only.  No
`Classical`, `sorry`, `native_decide`, choice, functional extensionality,
noncomputable declaration, or custom axiom.
-/

import YMGap.Continuum.BF4PhysicalCutoffAutocorrelationLimit
import YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum.BF4PhysicalCutoffConnectedLimit

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCutoffAutocorrelationLimit
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Connected norm and autocorrelation Bishop reals -/

/-- Cutoff-removed stationary mean of one bounded physical observable. -/
def centralPhysicalMeanCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalUnitObservable) : CReal :=
  centralPhysicalStationaryCutoffLimit hw0 hw1 half observable

/-- Cutoff-removed stationary norm square before centering. -/
def centralPhysicalNormCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalUnitObservable) : CReal :=
  (centralPhysicalStationaryCutoffProbFunctional
    hw0 hw1 half).E
    (centralPhysicalUnitObsAlg.mul
      (centralPhysicalUnitObsAlg.star observable) observable)

/-- Connected stationary norm `E(a^2) - E(a)^2` after cutoff removal. -/
def centralPhysicalConnectedNormCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalUnitObservable) : CReal :=
  CReal.add
    (centralPhysicalNormCutoffLimit hw0 hw1 half observable)
    (CReal.neg
      (CReal.mul
        (centralPhysicalMeanCutoffLimit hw0 hw1 half observable)
        (centralPhysicalMeanCutoffLimit hw0 hw1 half observable)))

/-- Connected one-step same-object autocorrelation
`<a,P a> - E(a)^2` after cutoff removal. -/
def centralPhysicalConnectedAutocorrelationCutoffLimit
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalUnitObservable) : CReal :=
  CReal.add
    (centralPhysicalAutocorrelationCutoffLimit
      hw0 hw1 half observable)
    (CReal.neg
      (CReal.mul
        (centralPhysicalMeanCutoffLimit hw0 hw1 half observable)
        (centralPhysicalMeanCutoffLimit hw0 hw1 half observable)))

@[simp] theorem centralPhysicalMeanCutoffLimit_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) (observable : CentralPhysicalUnitObservable) :
    (centralPhysicalMeanCutoffLimit
      hw0 hw1 half observable).approx cutoff =
      centralPhysicalStationaryMean
        w (Q'.le_of_lt hw0) cutoff half observable.value := rfl

@[simp] theorem centralPhysicalConnectedNormCutoffLimit_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) (observable : CentralPhysicalUnitObservable) :
    (centralPhysicalConnectedNormCutoffLimit
      hw0 hw1 half observable).approx cutoff =
      centralPhysicalWeightedInner
          w (Q'.le_of_lt hw0) cutoff half
          observable.value observable.value +
        -(centralPhysicalStationaryMean
            w (Q'.le_of_lt hw0) cutoff half observable.value *
          centralPhysicalStationaryMean
            w (Q'.le_of_lt hw0) cutoff half observable.value) := rfl

@[simp] theorem
    centralPhysicalConnectedAutocorrelationCutoffLimit_approx
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) (observable : CentralPhysicalUnitObservable) :
    (centralPhysicalConnectedAutocorrelationCutoffLimit
      hw0 hw1 half observable).approx cutoff =
      centralPhysicalWeightedInner
          w (Q'.le_of_lt hw0) cutoff half observable.value
          (centralPhysicalMarkovApply
            w (Q'.le_of_lt hw0) cutoff half observable.value) +
        -(centralPhysicalStationaryMean
            w (Q'.le_of_lt hw0) cutoff half observable.value *
          centralPhysicalStationaryMean
            w (Q'.le_of_lt hw0) cutoff half observable.value) := rfl

/-! ## 2. Exact identification with finite centered forms -/

/-- Every connected-norm approximation is the exact norm of the literal
marginal-centered finite observable. -/
theorem centralPhysicalConnectedNormCutoffLimit_approx_eqv_centeredNorm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) (observable : CentralPhysicalUnitObservable) :
    (centralPhysicalConnectedNormCutoffLimit
        hw0 hw1 half observable).approx cutoff ≈
      centralPhysicalWeightedInner
        w (Q'.le_of_lt hw0) cutoff half
        (centralPhysicalCenteredObservable
          w (Q'.le_of_lt hw0) cutoff half observable.value)
        (centralPhysicalCenteredObservable
          w (Q'.le_of_lt hw0) cutoff half observable.value) := by
  exact Q'.eqv_symm
    (centralPhysicalCenteredObservable_norm_identity
      w (Q'.le_of_lt hw0) cutoff half observable.value)

/-- Every connected-autocorrelation approximation is the exact Markov form
of the literal marginal-centered finite observable. -/
theorem
    centralPhysicalConnectedAutocorrelationCutoffLimit_approx_eqv_centeredForm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat) (observable : CentralPhysicalUnitObservable) :
    (centralPhysicalConnectedAutocorrelationCutoffLimit
        hw0 hw1 half observable).approx cutoff ≈
      centralPhysicalWeightedInner
        w (Q'.le_of_lt hw0) cutoff half
        (centralPhysicalMarkovApply
          w (Q'.le_of_lt hw0) cutoff half
          (centralPhysicalCenteredObservable
            w (Q'.le_of_lt hw0) cutoff half observable.value))
        (centralPhysicalCenteredObservable
          w (Q'.le_of_lt hw0) cutoff half observable.value) := by
  let D :=
    (centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) cutoff half).toGNSData
  let mean :=
    centralPhysicalStationaryMean
      w (Q'.le_of_lt hw0) cutoff half observable.value
  refine Q'.eqv_trans _
    (centralPhysicalWeightedInner
          w (Q'.le_of_lt hw0) cutoff half
          (centralPhysicalMarkovApply
            w (Q'.le_of_lt hw0) cutoff half observable.value)
          observable.value +
        -(mean * mean)) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (D.B_symm observable.value
        (centralPhysicalMarkovApply
          w (Q'.le_of_lt hw0) cutoff half observable.value))
      (Q'.eqv_refl _)
  · exact Q'.eqv_symm
      (centralPhysicalCenteredObservable_markovForm_identity
        w (Q'.le_of_lt hw0) cutoff half observable.value)

/-! ## 3. Limiting centered form interval -/

/-- The connected stationary norm remains nonnegative after cutoff removal. -/
theorem centralPhysicalConnectedNormCutoffLimit_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalUnitObservable) :
    CReal.czero ≤
      centralPhysicalConnectedNormCutoffLimit
        hw0 hw1 half observable := by
  apply CReal.ofQ'_le_of_approx_ge
  intro cutoff
  let centered := centralPhysicalCenteredObservable
    w (Q'.le_of_lt hw0) cutoff half observable.value
  exact Q'.le_trans' _ _ _
    (centralPhysicalWeightedSquare_nonnegative
      w (Q'.le_of_lt hw0) cutoff half centered)
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (centralPhysicalConnectedNormCutoffLimit_approx_eqv_centeredNorm
          hw0 hw1 half cutoff observable)))

/-- The connected one-step autocorrelation remains nonnegative after cutoff
removal. -/
theorem centralPhysicalConnectedAutocorrelationCutoffLimit_nonnegative
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalUnitObservable) :
    CReal.czero ≤
      centralPhysicalConnectedAutocorrelationCutoffLimit
        hw0 hw1 half observable := by
  apply CReal.ofQ'_le_of_approx_ge
  intro cutoff
  let centered := centralPhysicalCenteredObservable
    w (Q'.le_of_lt hw0) cutoff half observable.value
  let D :=
    (centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) cutoff half).toGNSData
  have hpositive := centralPhysicalMarkovApply_positive
    w (Q'.le_of_lt hw0) cutoff half centered
  have hsymm := D.B_symm centered
    (centralPhysicalMarkovApply
      w (Q'.le_of_lt hw0) cutoff half centered)
  have hbridge :=
    centralPhysicalConnectedAutocorrelationCutoffLimit_approx_eqv_centeredForm
      hw0 hw1 half cutoff observable
  exact Q'.le_trans' _ _ _ hpositive
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hsymm (Q'.eqv_symm hbridge)))

/-- The connected autocorrelation is bounded by the connected stationary
norm at the cutoff limit. -/
theorem centralPhysicalConnectedAutocorrelationCutoffLimit_le_norm
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat) (observable : CentralPhysicalUnitObservable) :
    centralPhysicalConnectedAutocorrelationCutoffLimit
        hw0 hw1 half observable ≤
      centralPhysicalConnectedNormCutoffLimit
        hw0 hw1 half observable := by
  intro cutoff
  let centered := centralPhysicalCenteredObservable
    w (Q'.le_of_lt hw0) cutoff half observable.value
  let D :=
    (centralPhysicalSmulGNS
      w (Q'.le_of_lt hw0) cutoff half).toGNSData
  have hconnected :=
    centralPhysicalConnectedAutocorrelationCutoffLimit_approx_eqv_centeredForm
      hw0 hw1 half cutoff observable
  have hsymm := D.B_symm
    (centralPhysicalMarkovApply
      w (Q'.le_of_lt hw0) cutoff half centered) centered
  have hfinite :=
    (centralPhysicalMarkovApply_form_interval
      w (Q'.le_of_lt hw0) cutoff half centered).2
  have hnorm :=
    centralPhysicalConnectedNormCutoffLimit_approx_eqv_centeredNorm
      hw0 hw1 half cutoff observable
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv hconnected)
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv hsymm)
      (Q'.le_trans' _ _ _ hfinite
        (Q'.le_trans' _ _ _
          (Q'.le_of_eqv (Q'.eqv_symm hnorm))
          (Q'.add_le_self_of_nonneg _ _
            (Q'.invSucc_nonneg cutoff)))))

/-! ## Axiom audit -/

#print axioms centralPhysicalConnectedNormCutoffLimit
#print axioms centralPhysicalConnectedAutocorrelationCutoffLimit
#print axioms
  centralPhysicalConnectedAutocorrelationCutoffLimit_approx_eqv_centeredForm
#print axioms centralPhysicalConnectedNormCutoffLimit_nonnegative
#print axioms
  centralPhysicalConnectedAutocorrelationCutoffLimit_nonnegative
#print axioms centralPhysicalConnectedAutocorrelationCutoffLimit_le_norm

end YMGap.Continuum.BF4PhysicalCutoffConnectedLimit
