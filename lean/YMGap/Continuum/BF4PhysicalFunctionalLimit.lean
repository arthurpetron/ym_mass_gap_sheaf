/-
# Direct cross-scale limit of the finite physical BF4 functionals

`BF4PhysicalFiniteProbFunctional` constructs the actual positive normalized
`Q'`-valued functional at every matched physical scale.  The next causal edge
is analytic: prove that each observable's sequence of those expectations has
a uniform two-sided tail modulus.

This module isolates that edge and compiles it.  The input modulus carries an
explicit rate function in `Type`; its sequence is pinned to the actual BF4
functional at every scale.  From it we construct a positive normalized
`CRealProbFunctional` whose approximations are exactly those finite-stage
expectations.  Exact one-step Kolmogorov equality is not assumed: convergence
is sufficient for this direct functional limit.

The modulus is not inhabited here.  Nor does the resulting positive
functional by itself supply Euclidean covariance, reflection positivity,
regularity, OS reconstruction, non-triviality, or a mass gap.  Those remain
separate downstream obligations.

Axiom gate: the load-bearing declarations below remain within the repository
gate `[propext, Quot.sound]`; no `Classical`, `sorry`, `native_decide`, or
custom axiom is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteProbFunctional
import YMGap.Continuum.ContinuumFunctional

namespace YMGap.Continuum.BF4PhysicalFunctionalLimit

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteProbFunctional
open YMGap.Continuum.ContinuumFunctional
open YMGap.Continuum.ObservableMeasure

/-! ## 1. Constant-real lift of a rational probability functional -/

/-- Embed a `Q'`-valued probability functional pointwise into `CReal`.
Normalization and positivity are inherited from the finite functional. -/
def cRealOfProbFunctional {A : ObsAlg} (mu : ProbFunctional A) :
    CRealProbFunctional A where
  E := fun observable => CReal.ofQ' (mu.E observable)
  normalized := by
    rw [mu.normalized]
    intro epsilon hepsilon
    refine ⟨0, fun n _ => ⟨?_, ?_⟩⟩
    · exact Q'.add_le_self_of_nonneg
        1 epsilon (Q'.le_of_lt hepsilon)
    · exact Q'.add_le_self_of_nonneg
        1 epsilon (Q'.le_of_lt hepsilon)
  positive := by
    intro observable
    show CReal.ofQ' 0 ≤ CReal.ofQ' (mu.E (A.mul (A.star observable) observable))
    exact CReal.ofQ'_le_ofQ' (mu.positive observable)

@[simp] theorem cRealOfProbFunctional_approx
    {A : ObsAlg} (mu : ProbFunctional A) (observable : A.carrier)
    (n : Nat) :
    ((cRealOfProbFunctional mu).E observable).approx n = mu.E observable :=
  rfl

/-! ## 2. An explicit, Type-level tail modulus -/

/-- A rational sequence with a two-sided tail bound and an explicit rate at
which that tail is below any positive tolerance.  Unlike an existential-only
convergence statement, `rate` is retained as constructive data. -/
structure ExplicitObservableLimitModulus where
  seq : Nat → Q'
  tail : Nat → Q'
  upper : ∀ n d, seq (n + d) ≤ seq n + tail n
  lower : ∀ n d, seq n ≤ seq (n + d) + tail n
  rate : Q' → Nat
  tail_at_rate : ∀ epsilon : Q', (0 : Q') < epsilon →
    ∀ n : Nat, rate epsilon ≤ n → tail n ≤ epsilon

/-- Forget only the selected rate witness, producing the existing
`ObservableLimitModulus` consumed by the `CReal` limit engine. -/
def ExplicitObservableLimitModulus.toObservableLimitModulus
    (modulus : ExplicitObservableLimitModulus) : ObservableLimitModulus where
  seq := modulus.seq
  tail := modulus.tail
  up := modulus.upper
  lo := modulus.lower
  mod := by
    intro epsilon hepsilon
    exact ⟨modulus.rate epsilon,
      modulus.tail_at_rate epsilon hepsilon⟩

@[simp] theorem ExplicitObservableLimitModulus.toObservableLimitModulus_seq
    (modulus : ExplicitObservableLimitModulus) (n : Nat) :
    modulus.toObservableLimitModulus.seq n = modulus.seq n := rfl

/-- A constant rational sequence has the explicit zero-tail modulus. -/
def explicitConstantModulus (value : Q') :
    ExplicitObservableLimitModulus where
  seq := fun _ => value
  tail := fun _ => 0
  upper := by
    intro _ _
    rw [Q'.add_zero' value]
    exact Q'.le_refl' value
  lower := by
    intro _ _
    rw [Q'.add_zero' value]
    exact Q'.le_refl' value
  rate := fun _ => 0
  tail_at_rate := by
    intro epsilon hepsilon _ _
    exact Q'.le_of_lt hepsilon

@[simp] theorem explicitConstantModulus_seq
    (value : Q') (n : Nat) :
    (explicitConstantModulus value).seq n = value := rfl

/-! ## 3. The exact BF4 cross-scale input and its contraction -/

/-- The remaining direct functional-limit input for one matched BF4 family.
For every strictified observable it supplies an explicit tail modulus, and
`reads_stage` prevents the modulus from describing any sequence other than
the actual finite physical BF4 expectations. -/
structure MatchedPhysicalExpectationLimitModulus
    (family : MatchedBlockFamily) (coupling : Nat → Q') : Type where
  modOf : CentralPhysicalObservable → ExplicitObservableLimitModulus
  reads_stage : ∀ observable scale,
    (modOf observable).seq scale =
      (matchedPhysicalProbFunctional family coupling scale).E observable

/-- The genuinely analytic input can be restricted to literal edge
observables.  The tagged unit needs no estimate: its finite expectation is
definitionally the constant sequence `1`. -/
structure MatchedPhysicalFunctionLimitModulus
    (family : MatchedBlockFamily) (coupling : Nat → Q') : Type where
  modOf :
    (YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling → Q') →
      ExplicitObservableLimitModulus
  reads_stage : ∀ observable scale,
    (modOf observable).seq scale =
      (matchedPhysicalProbFunctional family coupling scale).E
        (.ofFunction observable)

/-- Add the automatic constant-unit modulus to a modulus on literal
functions. -/
def MatchedPhysicalFunctionLimitModulus.toExpectationLimitModulus
    {family : MatchedBlockFamily} {coupling : Nat → Q'}
    (limit : MatchedPhysicalFunctionLimitModulus family coupling) :
    MatchedPhysicalExpectationLimitModulus family coupling where
  modOf := fun observable =>
    match observable with
    | .one => explicitConstantModulus 1
    | .ofFunction value => limit.modOf value
  reads_stage := by
    intro observable scale
    cases observable with
    | one => rfl
    | ofFunction observable => exact limit.reads_stage observable scale

/-- Regard the finite matched functionals and their explicit rational modulus
as an instance of the repository's spacing-limit interface. -/
def MatchedPhysicalExpectationLimitModulus.toScalingLimitModulus
    {family : MatchedBlockFamily} {coupling : Nat → Q'}
    (limit : MatchedPhysicalExpectationLimitModulus family coupling) :
    ScalingLimitModulus centralPhysicalObsAlg where
  atSpacing := fun scale =>
    cRealOfProbFunctional
      (matchedPhysicalProbFunctional family coupling scale)
  spacingModOf := fun observable =>
    (limit.modOf observable).toObservableLimitModulus
  reads_atSpacing := by
    intro observable scale
    exact limit.reads_stage observable scale

/-- The direct cross-scale limit is a genuine positive normalized constructive
real functional.  Its only analytic input is the explicit, actual-expectation
modulus above; positivity and normalization are inherited automatically from
the constructed finite BF4 functionals. -/
def matchedPhysicalLimitFunctional
    {family : MatchedBlockFamily} {coupling : Nat → Q'}
    (limit : MatchedPhysicalExpectationLimitModulus family coupling) :
    CRealProbFunctional centralPhysicalObsAlg :=
  scalingFunctional_of_modulus limit.toScalingLimitModulus
    (by
      intro scale
      change (limit.modOf centralPhysicalObsAlg.one).seq scale = 1
      rw [limit.reads_stage]
      exact (matchedPhysicalProbFunctional
        family coupling scale).normalized)
    (by
      intro observable scale
      change (0 : Q') ≤
        (limit.modOf
          (centralPhysicalObsAlg.mul
            (centralPhysicalObsAlg.star observable) observable)).seq scale
      rw [limit.reads_stage]
      exact (matchedPhysicalProbFunctional
        family coupling scale).positive observable)

/-- Public literal-function endpoint: cross-scale moduli are requested only
for actual edge observables; unit convergence is discharged internally. -/
def matchedPhysicalFunctionLimitFunctional
    {family : MatchedBlockFamily} {coupling : Nat → Q'}
    (limit : MatchedPhysicalFunctionLimitModulus family coupling) :
    CRealProbFunctional centralPhysicalObsAlg :=
  matchedPhysicalLimitFunctional limit.toExpectationLimitModulus

/-- The continuum functional is pinned approximation-by-approximation to the
actual finite BF4 expectation sequence. -/
@[simp] theorem matchedPhysicalLimitFunctional_approx
    {family : MatchedBlockFamily} {coupling : Nat → Q'}
    (limit : MatchedPhysicalExpectationLimitModulus family coupling)
    (observable : CentralPhysicalObservable) (scale : Nat) :
    ((matchedPhysicalLimitFunctional limit).E observable).approx scale =
      (matchedPhysicalProbFunctional family coupling scale).E observable :=
  limit.reads_stage observable scale

/-- On literal rational edge observables, the constructed limit's
approximations are exactly the stationary finite BF4 means. -/
@[simp] theorem matchedPhysicalLimitFunctional_ofFunction_approx
    {family : MatchedBlockFamily} {coupling : Nat → Q'}
    (limit : MatchedPhysicalExpectationLimitModulus family coupling)
    (observable :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling → Q')
    (scale : Nat) :
    ((matchedPhysicalLimitFunctional limit).E
        (.ofFunction observable)).approx scale =
      YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov.centralPhysicalStationaryMean
        (YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative.matchedAllSpinWeight
          family coupling scale)
        (YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative.matchedAllSpinWeight_nonnegative
          family coupling scale)
        (YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative.matchedAllSpinCutoff
          family coupling scale) 0 observable := by
  rw [matchedPhysicalLimitFunctional_approx]
  rfl

/-- The literal-function endpoint retains the same exact finite-stage
approximation law. -/
@[simp] theorem matchedPhysicalFunctionLimitFunctional_ofFunction_approx
    {family : MatchedBlockFamily} {coupling : Nat → Q'}
    (limit : MatchedPhysicalFunctionLimitModulus family coupling)
    (observable :
      YMGap.Continuum.SU2FundamentalPentagonFiniteGraph.EdgeLabelling → Q')
    (scale : Nat) :
    ((matchedPhysicalFunctionLimitFunctional limit).E
        (.ofFunction observable)).approx scale =
      (matchedPhysicalProbFunctional family coupling scale).E
        (.ofFunction observable) :=
  limit.reads_stage observable scale

end YMGap.Continuum.BF4PhysicalFunctionalLimit

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalFunctionalLimit.cRealOfProbFunctional
#print axioms YMGap.Continuum.BF4PhysicalFunctionalLimit.ExplicitObservableLimitModulus.toObservableLimitModulus
#print axioms YMGap.Continuum.BF4PhysicalFunctionalLimit.explicitConstantModulus
#print axioms YMGap.Continuum.BF4PhysicalFunctionalLimit.MatchedPhysicalFunctionLimitModulus.toExpectationLimitModulus
#print axioms YMGap.Continuum.BF4PhysicalFunctionalLimit.MatchedPhysicalExpectationLimitModulus.toScalingLimitModulus
#print axioms YMGap.Continuum.BF4PhysicalFunctionalLimit.matchedPhysicalLimitFunctional
#print axioms YMGap.Continuum.BF4PhysicalFunctionalLimit.matchedPhysicalFunctionLimitFunctional
#print axioms YMGap.Continuum.BF4PhysicalFunctionalLimit.matchedPhysicalLimitFunctional_approx
