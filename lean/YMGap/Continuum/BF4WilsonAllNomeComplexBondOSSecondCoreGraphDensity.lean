/-
# Simultaneous graph approximation by actual represented second-core points

The original derivative graph supplies a source stream with an explicit
two-coordinate modulus.  At one source, a second finite inverse sum produces
an actual second-core point.  Its input and output errors are defect-power
tails of `T x` and `A x`, respectively; both have supplied range witnesses.
Thus this is graph-norm, not merely input, approximation.  The Type-valued
certificate is attached to a supplied physical domain point, never obtained
by choosing a representative of its quotient class.

This remains fixed-nome and fixed-width. It does not identify a physical
clock, a continuum Hamiltonian, or a positive physical mass.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCoreDensity
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphEquation
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSGraphNorm

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCoreGraphDensity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (Completion)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime (completedTime)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (completedTime_sub)
open YMGap.Continuum.BF4WilsonAllNomeDistance
  (completedDist completedDist_triangle)
open YMGap.Continuum.BF4WilsonAllNomeTimeDefectMoments (time_defectPower)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeInverseSum
  (inverseSumRepresentative inverseSumRepresentative_pin
    derivativeAction_inverseSum time_inverseSum_sub)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosure
  (RangeLimit quarter quarter_positive four_quarters defectModulus defect_small)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph (GraphLimit)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphEquation (sub_error)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "dist" => completedDist hw0 hw1
local notation "Sub" => BF4WilsonAllNomeLinear.completedSub hw0 hw1
local notation "DP" => BF4WilsonAllNomeTimeDefectMoments.defectPower hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)
local notation "Point" => BF4WilsonAllNomeComplexSectorDerivative.DomainPoint
  hw0 hw1 (width := width)
local notation "H" => BF4WilsonAllNomeComplexBondOSCompletion.ComplexBondCompletion
  hw0 hw1 (width := width)
local notation "CDomain" => BF4WilsonAllNomeComplexBondOSDerivative.Domain
  hw0 hw1 (width := width)

/-- At a represented core source, the second-core input differs from the
first core input by exactly the defect tail of that first input. -/
theorem second_input_tail (X : (D).Cauchy) (k : Nat) :
    T 1 (T 1 (Class (inverseSumRepresentative hw0 hw1 k X))) =
      Sub (T 1 (Class X)) (DP k (T 1 (Class X))) := by
  rw [inverseSumRepresentative_pin, time_inverseSum_sub,
    completedTime_sub, time_defectPower]

/-- The second-core output has the matching tail of the ORIGINAL derivative
output.  This is where finite inverse sums must commute with `A`. -/
theorem second_output_tail (X : (D).Cauchy) (k : Nat) :
    T 1 (A (Class (inverseSumRepresentative hw0 hw1 k X))) =
      Sub (A (Class X)) (DP k (A (Class X))) := by
  rw [inverseSumRepresentative_pin, derivativeAction_inverseSum,
    time_inverseSum_sub]

def coreInputRange (X : (D).Cauchy) :
    RangeLimit hw0 hw1 (T 1 (Class X)) :=
  BF4WilsonAllNomeTimeRangeClosure.fromTime hw0 hw1 X

def coreOutputRange (X : (D).Cauchy) :
    RangeLimit hw0 hw1 (A (Class X)) :=
  (BF4WilsonAllNomeSectorDerivative.corePoint hw0 hw1 X).output.range

/-- A source-dependent finite depth controls BOTH defect tails. -/
def coreDepth (X : (D).Cauchy) (e : Q') : Nat :=
  max (defectModulus hw0 hw1 (coreInputRange hw0 hw1 X) e)
    (defectModulus hw0 hw1 (coreOutputRange hw0 hw1 X) e)

theorem core_input_error (X : (D).Cauchy) (e : Q') (he : (0 : Q') < e) :
    RCle (dist
      (T 1 (T 1 (Class (inverseSumRepresentative hw0 hw1
        (coreDepth hw0 hw1 X e) X)))) (T 1 (Class X))) (rat e) := by
  rw [second_input_tail, sub_error]
  exact defect_small hw0 hw1 (coreInputRange hw0 hw1 X) e he _
    (Nat.le_max_left _ _)

theorem core_output_error (X : (D).Cauchy) (e : Q') (he : (0 : Q') < e) :
    RCle (dist
      (T 1 (A (Class (inverseSumRepresentative hw0 hw1
        (coreDepth hw0 hw1 X e) X)))) (A (Class X))) (rat e) := by
  rw [second_output_tail, sub_error]
  exact defect_small hw0 hw1 (coreOutputRange hw0 hw1 X) e he _
    (Nat.le_max_right _ _)

/-- The original graph itself chooses the outer source index; no graph datum
is manufactured from an input-only approximation. -/
def graphSource {u v : V} (G : GraphLimit hw0 hw1 u v)
    (X : Nat → (D).Cauchy) (e : Q') : (D).Cauchy :=
  X (G.modulus (quarter e))

def graphSecondSource {u v : V} (G : GraphLimit hw0 hw1 u v)
    (X : Nat → (D).Cauchy) (e : Q') : (D).Cauchy :=
  let Y := graphSource hw0 hw1 G X e
  inverseSumRepresentative hw0 hw1 (coreDepth hw0 hw1 Y (quarter e)) Y

theorem graph_second_input_bound {u v : V} (G : GraphLimit hw0 hw1 u v)
    (X : Nat → (D).Cauchy)
    (hX : ∀ n, Class (X n) = G.source n)
    (e : Q') (he : (0 : Q') < e) :
    RCle (dist (T 1 (T 1 (Class (graphSecondSource hw0 hw1 G X e)))) u)
      (rat e) := by
  let d := quarter e
  let n := G.modulus d
  let Y := X n
  have hd : (0 : Q') < d := quarter_positive he
  have hcore := core_input_error hw0 hw1 Y d hd
  have hgraph := (G.bound d hd n (Nat.le_refl _)).1
  rw [← hX n] at hgraph
  have h := RCle_trans
    (completedDist_triangle hw0 hw1
      (T 1 (T 1 (Class (graphSecondSource hw0 hw1 G X e))))
      (T 1 (Class Y)) u)
    (RCadd_le_add (RCadd_le_add hcore hcore)
      (RCadd_le_add hgraph hgraph))
  change RCle _ (RCadd (RCadd (rat d) (rat d))
    (RCadd (rat d) (rat d))) at h
  rwa [show d = quarter e by rfl, four_quarters] at h

theorem graph_second_output_bound {u v : V} (G : GraphLimit hw0 hw1 u v)
    (X : Nat → (D).Cauchy)
    (hX : ∀ n, Class (X n) = G.source n)
    (e : Q') (he : (0 : Q') < e) :
    RCle (dist (T 1 (A (Class (graphSecondSource hw0 hw1 G X e)))) v)
      (rat e) := by
  let d := quarter e
  let n := G.modulus d
  let Y := X n
  have hd : (0 : Q') < d := quarter_positive he
  have hcore := core_output_error hw0 hw1 Y d hd
  have hgraph := (G.bound d hd n (Nat.le_refl _)).2
  rw [← hX n] at hgraph
  have h := RCle_trans
    (completedDist_triangle hw0 hw1
      (T 1 (A (Class (graphSecondSource hw0 hw1 G X e))))
      (A (Class Y)) v)
    (RCadd_le_add (RCadd_le_add hcore hcore)
      (RCadd_le_add hgraph hgraph))
  change RCle _ (RCadd (RCadd (rat d) (rat d))
    (RCadd (rat d) (rat d))) at h
  rwa [show d = quarter e by rfl, four_quarters] at h

/-- A supplied physical domain point carries both graph witnesses and their
original source representatives; no quotient-class representative is chosen. -/
def physicalSecondSource (p : Point) (e : Q') : (D).Cauchy × (D).Cauchy :=
  (graphSecondSource hw0 hw1 (BF4WilsonAllNomeSectorDerivative.graph hw0 hw1 p.1)
    (BF4WilsonAllNomeSectorDerivative.sourceRepresentative hw0 hw1 p.1)
    (HalfPow.half * e),
   graphSecondSource hw0 hw1 (BF4WilsonAllNomeSectorDerivative.graph hw0 hw1 p.2)
    (BF4WilsonAllNomeSectorDerivative.sourceRepresentative hw0 hw1 p.2)
    (HalfPow.half * e))

private theorem two_halves (e : Q') :
    RCadd (rat (HalfPow.half * e)) (rat (HalfPow.half * e)) = rat e :=
  Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun _ => ExpNeg.two_halves e))

/-- The actual second-core point approximates BOTH coordinates of the same
original physical derivative graph, at one computed source-dependent rate. -/
theorem physical_second_input_bound (p : Point) (e : Q') (he : (0 : Q') < e) :
    RCle (BF4WilsonAllNomeComplexBondOSCompletion.distance hw0 hw1
      (BF4WilsonAllNomeComplexBondOSDerivative.input hw0 hw1
        (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1
          (physicalSecondSource hw0 hw1 p e)))
      (BF4WilsonAllNomeComplexBondOSDerivative.input hw0 hw1
        (BF4WilsonAllNomeComplexBondOSDerivative.ofPoint hw0 hw1 p)))
      (rat e) := by
  have hd : (0 : Q') < HalfPow.half * e :=
    ExpNeg.half_mul_pos _ he
  have h₁ := graph_second_input_bound hw0 hw1
    (BF4WilsonAllNomeSectorDerivative.graph hw0 hw1 p.1)
    (BF4WilsonAllNomeSectorDerivative.sourceRepresentative hw0 hw1 p.1)
    (BF4WilsonAllNomeSectorDerivative.sourceRepresentative_pin hw0 hw1 p.1)
    _ hd
  have h₂ := graph_second_input_bound hw0 hw1
    (BF4WilsonAllNomeSectorDerivative.graph hw0 hw1 p.2)
    (BF4WilsonAllNomeSectorDerivative.sourceRepresentative hw0 hw1 p.2)
    (BF4WilsonAllNomeSectorDerivative.sourceRepresentative_pin hw0 hw1 p.2)
    _ hd
  have h := RCadd_le_add h₁ h₂
  rw [two_halves] at h
  rw [BF4WilsonAllNomeComplexBondOSCompletion.distance_value,
    BF4WilsonAllNomeComplexBondOSSecondCore.first_input_value,
    BF4WilsonAllNomeComplexBondOSDerivative.value_input_ofPoint]
  change RCle
    (RCadd
      (dist (T 1 (T 1 (Class (physicalSecondSource hw0 hw1 p e).1))) p.1.input.val)
      (dist (T 1 (T 1 (Class (physicalSecondSource hw0 hw1 p e).2))) p.2.input.val))
    (rat e)
  exact h

theorem physical_second_output_bound (p : Point) (e : Q') (he : (0 : Q') < e) :
    RCle (BF4WilsonAllNomeComplexBondOSCompletion.distance hw0 hw1
      (BF4WilsonAllNomeComplexBondOSDerivative.output hw0 hw1
        (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1
          (physicalSecondSource hw0 hw1 p e)))
      (BF4WilsonAllNomeComplexBondOSDerivative.output hw0 hw1
        (BF4WilsonAllNomeComplexBondOSDerivative.ofPoint hw0 hw1 p)))
      (rat e) := by
  have hd : (0 : Q') < HalfPow.half * e :=
    ExpNeg.half_mul_pos _ he
  have h₁ := graph_second_output_bound hw0 hw1
    (BF4WilsonAllNomeSectorDerivative.graph hw0 hw1 p.1)
    (BF4WilsonAllNomeSectorDerivative.sourceRepresentative hw0 hw1 p.1)
    (BF4WilsonAllNomeSectorDerivative.sourceRepresentative_pin hw0 hw1 p.1)
    _ hd
  have h₂ := graph_second_output_bound hw0 hw1
    (BF4WilsonAllNomeSectorDerivative.graph hw0 hw1 p.2)
    (BF4WilsonAllNomeSectorDerivative.sourceRepresentative hw0 hw1 p.2)
    (BF4WilsonAllNomeSectorDerivative.sourceRepresentative_pin hw0 hw1 p.2)
    _ hd
  have h := RCadd_le_add h₁ h₂
  rw [two_halves] at h
  rw [BF4WilsonAllNomeComplexBondOSCompletion.distance_value,
    BF4WilsonAllNomeComplexBondOSSecondCore.first_output_value,
    BF4WilsonAllNomeComplexBondOSDerivative.value_output_ofPoint]
  change RCle
    (RCadd
      (dist (T 1 (A (Class (physicalSecondSource hw0 hw1 p e).1))) p.1.output.val)
      (dist (T 1 (A (Class (physicalSecondSource hw0 hw1 p e).2))) p.2.output.val))
    (rat e)
  exact h

/-- Computed second-core preimage together with simultaneous original graph
errors. This is the graph approximation consumed by the existing second-core
Cayley tangent theorem; its modulus belongs to the supplied represented point. -/
def physicalGraphCertificate (p : Point) (e : Q') (he : (0 : Q') < e) :
    Σ' Y : (D).Cauchy × (D).Cauchy,
      RCle (BF4WilsonAllNomeComplexBondOSCompletion.distance hw0 hw1
        (BF4WilsonAllNomeComplexBondOSDerivative.input hw0 hw1
          (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y))
        (BF4WilsonAllNomeComplexBondOSDerivative.input hw0 hw1
          (BF4WilsonAllNomeComplexBondOSDerivative.ofPoint hw0 hw1 p)))
        (rat e) ×'
      RCle (BF4WilsonAllNomeComplexBondOSCompletion.distance hw0 hw1
        (BF4WilsonAllNomeComplexBondOSDerivative.output hw0 hw1
          (BF4WilsonAllNomeComplexBondOSSecondCore.first hw0 hw1 Y))
        (BF4WilsonAllNomeComplexBondOSDerivative.output hw0 hw1
          (BF4WilsonAllNomeComplexBondOSDerivative.ofPoint hw0 hw1 p)))
        (rat e) :=
  ⟨physicalSecondSource hw0 hw1 p e,
    physical_second_input_bound hw0 hw1 p e he,
    physical_second_output_bound hw0 hw1 p e he⟩

#print axioms second_input_tail
#print axioms second_output_tail
#print axioms coreInputRange
#print axioms coreOutputRange
#print axioms coreDepth
#print axioms core_input_error
#print axioms core_output_error
#print axioms graphSecondSource
#print axioms graph_second_input_bound
#print axioms graph_second_output_bound
#print axioms physicalSecondSource
#print axioms physical_second_input_bound
#print axioms physical_second_output_bound
#print axioms physicalGraphCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSecondCoreGraphDensity
