/-
# The finite physical BF4 probability functional

The exact finite BF4 row marginal already gives a positive normalized
expectation on rational observables.  Its normalization theorem is stated in
the mathematically appropriate relation `Q'.eqv`, whereas the older generic
`ObservableMeasure.ProbFunctional` interface asks for literal equality at the
unit.  Since `Q'` deliberately stores unreduced fractions, those statements
are not interchangeable.

This module supplies the smallest honest strictification.  A finite observable
is either the distinguished unit or a literal rational function on edge
labellings.  The distinguished unit has expectation definitionally equal to
`1`; a literal function has exactly the stationary BF4 expectation.  The two
representations of the constant-one function have equivalent expectations,
as proved below.  Multiplication treats the distinguished unit as a genuine
unit, and otherwise is pointwise multiplication.  Thus positivity is exactly
the already-proved nonnegativity of the physical stationary weighted square.

The result is an actual `ProbFunctional` at every finite BF4 stage, including
the matched AF stages used by the transfer construction.  This is finite
volume only.  No coarse-to-fine observable homomorphism, cross-scale
consistency, thermodynamic limit, or continuum Yang--Mills measure is produced
here.

Axiom gate: the load-bearing declarations below use only `propext` (and the
transitive imports' accepted `Quot.sound` where reported).  There is no
`Classical`, `sorry`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.ObservableMeasure
import YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
import YMGap.Continuum.BF4WeightedJointPerronPerturbation

namespace YMGap.Continuum.BF4PhysicalFiniteProbFunctional

open YMGap.Constructive
open YMGap.Continuum.ObservableMeasure
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A unit-strictified carrier of physical rational observables -/

/-- Rational functions on the BF4 edge-labelling carrier, with a separately
tagged unit.  The tag is needed only because `Q'` stores unreduced fractions:
the physical expectation of the literal constant-one function is equivalent
to one, but need not be structurally equal to the chosen `Q'` value `1`. -/
inductive CentralPhysicalObservable : Type
  | one : CentralPhysicalObservable
  | ofFunction : (EdgeLabelling → Q') → CentralPhysicalObservable

/-- The pointwise rational function represented by a strictified observable. -/
def CentralPhysicalObservable.realize :
    CentralPhysicalObservable → EdgeLabelling → Q'
  | .one => fun _ => 1
  | .ofFunction observable => observable

/-- Product with a strict unit; two literal functions multiply pointwise. -/
def CentralPhysicalObservable.mul :
    CentralPhysicalObservable → CentralPhysicalObservable →
      CentralPhysicalObservable
  | .one, observable => observable
  | observable, .one => observable
  | .ofFunction left, .ofFunction right =>
      .ofFunction (fun state => left state * right state)

/-- The finite physical observables here are real-valued, so star is identity. -/
def CentralPhysicalObservable.star
    (observable : CentralPhysicalObservable) : CentralPhysicalObservable :=
  observable

/-- The minimal observable algebra carried by finite physical BF4 functions. -/
def centralPhysicalObsAlg : ObsAlg where
  carrier := CentralPhysicalObservable
  one := .one
  mul := CentralPhysicalObservable.mul
  star := CentralPhysicalObservable.star

@[simp] theorem CentralPhysicalObservable.one_mul
    (observable : CentralPhysicalObservable) :
    CentralPhysicalObservable.mul .one observable = observable := by
  cases observable <;> rfl

@[simp] theorem CentralPhysicalObservable.mul_one
    (observable : CentralPhysicalObservable) :
    CentralPhysicalObservable.mul observable .one = observable := by
  cases observable <;> rfl

@[simp] theorem CentralPhysicalObservable.star_eq
    (observable : CentralPhysicalObservable) :
    CentralPhysicalObservable.star observable = observable := rfl

/-- Realization respects multiplication at the rational-value level.  The
statement uses `Q'.eqv`, because multiplication by the represented constant
one is not necessarily literal equality on unreduced `Q'` values. -/
theorem CentralPhysicalObservable.realize_mul
    (left right : CentralPhysicalObservable) (state : EdgeLabelling) :
    (CentralPhysicalObservable.mul left right).realize state ≈
      left.realize state * right.realize state := by
  cases left with
  | one =>
      exact Q'.eqv_symm (Q'.one_mul_eqv (right.realize state))
  | ofFunction left =>
      cases right with
      | one => exact Q'.eqv_symm (Q'.mul_one_eqv (left state))
      | ofFunction right => exact Q'.eqv_refl _

/-! ## 2. The exact finite physical probability functional -/

/-- Expectation at one finite physical BF4 stage.  Literal functions use the
actual normalized stationary row marginal; the tagged unit is strictly `1`. -/
def centralPhysicalExpectation
    (w : Q') (hw : (0 : Q') ≤ w) (K halfExtent : Nat) :
    CentralPhysicalObservable → Q'
  | .one => 1
  | .ofFunction observable =>
      centralPhysicalStationaryMean w hw K halfExtent observable

/-- The actual finite physical BF4 probability functional. -/
def centralPhysicalProbFunctional
    (w : Q') (hw : (0 : Q') ≤ w) (K halfExtent : Nat) :
    ProbFunctional centralPhysicalObsAlg where
  E := centralPhysicalExpectation w hw K halfExtent
  normalized := rfl
  positive := by
    intro observable
    cases observable with
    | one =>
        change (0 : Q') ≤ 1
        decide
    | ofFunction observable =>
        change (0 : Q') ≤
          centralPhysicalWeightedInner
            w hw K halfExtent observable observable
        exact centralPhysicalWeightedSquare_nonnegative
          w hw K halfExtent observable

@[simp] theorem centralPhysicalProbFunctional_E_one
    (w : Q') (hw : (0 : Q') ≤ w) (K halfExtent : Nat) :
    (centralPhysicalProbFunctional w hw K halfExtent).E
        centralPhysicalObsAlg.one = 1 := rfl

@[simp] theorem centralPhysicalProbFunctional_E_ofFunction
    (w : Q') (hw : (0 : Q') ≤ w) (K halfExtent : Nat)
    (observable : EdgeLabelling → Q') :
    (centralPhysicalProbFunctional w hw K halfExtent).E
        (.ofFunction observable) =
      centralPhysicalStationaryMean w hw K halfExtent observable := rfl

/-- Strictification changes no expectation value modulo rational equivalence:
the tagged unit agrees with the stationary expectation of its realization,
and literal functions agree definitionally. -/
theorem centralPhysicalProbFunctional_E_eqv_stationaryMean
    (w : Q') (hw : (0 : Q') ≤ w) (K halfExtent : Nat)
    (observable : CentralPhysicalObservable) :
    (centralPhysicalProbFunctional w hw K halfExtent).E observable ≈
      centralPhysicalStationaryMean w hw K halfExtent observable.realize := by
  cases observable with
  | one =>
      exact Q'.eqv_symm
        (centralPhysicalStationaryMean_one w hw K halfExtent)
  | ofFunction observable => exact Q'.eqv_refl _

/-- In particular, the literal constant-one observable and the tagged unit
have equivalent expectations, even though only the tagged unit is required to
be structurally normalized by `ProbFunctional`. -/
theorem centralPhysicalProbFunctional_literal_one_eqv_unit
    (w : Q') (hw : (0 : Q') ≤ w) (K halfExtent : Nat) :
    (centralPhysicalProbFunctional w hw K halfExtent).E
        (.ofFunction (fun _ => 1)) ≈
      (centralPhysicalProbFunctional w hw K halfExtent).E
        centralPhysicalObsAlg.one :=
  centralPhysicalStationaryMean_one w hw K halfExtent

/-! ## 3. Compatibility with the already-constructed physical GNS transfer -/

/-- On two literal observables, the probability functional's `a* b` moment
is exactly the stationary weighted pairing used by the physical GNS
construction.  Thus the measure-functional and transfer/GNS routes refer to
the same finite object. -/
theorem centralPhysicalProbFunctional_starMul_eq_weightedInner
    (w : Q') (hw : (0 : Q') ≤ w) (K halfExtent : Nat)
    (left right : EdgeLabelling → Q') :
    (centralPhysicalProbFunctional w hw K halfExtent).E
        (centralPhysicalObsAlg.mul
          (centralPhysicalObsAlg.star (.ofFunction left))
          (.ofFunction right)) =
      centralPhysicalWeightedInner w hw K halfExtent left right := rfl

/-- The physical Markov action on the strictified observable carrier.  The
distinguished unit stays distinguished; literal functions are acted on by
the exact row-conditional BF4 kernel. -/
def centralPhysicalObservableMarkovApply
    (w : Q') (hw : (0 : Q') ≤ w) (K halfExtent : Nat) :
    CentralPhysicalObservable → CentralPhysicalObservable
  | .one => .one
  | .ofFunction observable =>
      .ofFunction
        (centralPhysicalMarkovApply w hw K halfExtent observable)

/-- Stationarity of the actual finite BF4 probability functional under its
physical Markov action.  Equality is correctly stated as `Q'.eqv`, the value
equality of the unreduced rational representation. -/
theorem centralPhysicalProbFunctional_markov_stationary
    (w : Q') (hw : (0 : Q') ≤ w) (K halfExtent : Nat)
    (observable : CentralPhysicalObservable) :
    (centralPhysicalProbFunctional w hw K halfExtent).E
        (centralPhysicalObservableMarkovApply
          w hw K halfExtent observable) ≈
      (centralPhysicalProbFunctional w hw K halfExtent).E observable := by
  cases observable with
  | one => exact Q'.eqv_refl 1
  | ofFunction observable =>
      exact centralPhysicalStationaryMean_markovApply
        w hw K halfExtent observable

/-! ## 4. The exact matched-stage family used by the BF4 transfer path -/

/-- The finite probability functional at the same matched scale, weight,
cutoff, and half-extent used by the physical dense-stage transfer route. -/
def matchedPhysicalProbFunctional
    (family : MatchedBlockFamily) (coupling : Nat → Q') (scale : Nat) :
    ProbFunctional centralPhysicalObsAlg :=
  centralPhysicalProbFunctional
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0

@[simp] theorem matchedPhysicalProbFunctional_E_ofFunction
    (family : MatchedBlockFamily) (coupling : Nat → Q') (scale : Nat)
    (observable : EdgeLabelling → Q') :
    (matchedPhysicalProbFunctional family coupling scale).E
        (.ofFunction observable) =
      centralPhysicalStationaryMean
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 observable := rfl

/-- The remaining cross-scale consistency law, stated at value level for the
identity observable embedding.  It is deliberately not inhabited here: for
the actual varying BF4 family it is precisely a finite-volume RG/measure
comparison theorem, not a consequence of per-stage normalization. -/
def MatchedPhysicalIdentityConsistency
    (family : MatchedBlockFamily) (coupling : Nat → Q') : Prop :=
  ∀ scale observable,
    (matchedPhysicalProbFunctional family coupling (scale + 1)).E observable =
      (matchedPhysicalProbFunctional family coupling scale).E observable

end YMGap.Continuum.BF4PhysicalFiniteProbFunctional

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalFiniteProbFunctional.CentralPhysicalObservable.realize_mul
#print axioms YMGap.Continuum.BF4PhysicalFiniteProbFunctional.centralPhysicalProbFunctional
#print axioms YMGap.Continuum.BF4PhysicalFiniteProbFunctional.centralPhysicalProbFunctional_E_eqv_stationaryMean
#print axioms YMGap.Continuum.BF4PhysicalFiniteProbFunctional.centralPhysicalProbFunctional_starMul_eq_weightedInner
#print axioms YMGap.Continuum.BF4PhysicalFiniteProbFunctional.centralPhysicalProbFunctional_markov_stationary
#print axioms YMGap.Continuum.BF4PhysicalFiniteProbFunctional.matchedPhysicalProbFunctional
