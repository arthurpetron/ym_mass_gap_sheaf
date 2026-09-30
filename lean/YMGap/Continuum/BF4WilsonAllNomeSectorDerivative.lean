/-
# Dense original derivative graph and its intrinsic sector adjoint

The carrier is the witnessed original time-range sector, with equality of
underlying vectors (not equality of range witnesses). Every core pair has
BOTH coordinates in this sector. Each sector point supplies a sequence of
these domain points converging to it with its own explicit modulus.

The adjoint tests below quantify only over this actual domain, not over an
assumed whole-carrier operator. Testing its represented core recovers the
original equation Au=T(1)v; the existing graph constructor supplies the
graph and its sources. Conversely graph symmetry gives all the adjoint
tests. Thus the densely defined graph equals its intrinsic real adjoint
on the presented sector. Its original fixed-parameter form gap is retained.

This is a setoid/presented construction. It does not identify the sector
with a physical OS space, extend the old quotient Domain's witness content,
construct a resolvent, or supply physical calibration or a continuum gap.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeSector
import YMGap.Continuum.BF4WilsonAllNomeDerivativeAdjointTests
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphRealLinear
import YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphGap

namespace YMGap.Continuum.BF4WilsonAllNomeSectorDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeDistance
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime (completedTime_additive)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivative (derivativeAction)
open YMGap.Continuum.BF4WilsonAllNomeDyadicDerivativeLaws (derivativeAction_add)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraph (GraphLimit)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphEquation (graphOfEquation)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphForm
  (graph_symmetric graph_nonnegative)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeAdjointTests (corePairings_iff_equation)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeInverseSum
  (inverseSumRepresentative inverseSumRepresentative_pin)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State CauchySequence)
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphReal (realRemainder)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue realValue)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "D" => seminorm hw0 hw1 (width := width)
local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "A" => derivativeAction hw0 hw1
local notation "Sector" => State hw0 hw1 (width := width)
local notation "dist" => completedDist hw0 hw1
local notation "Class" => Quotient.mk
  (CRealSeminormCompletion.SquaredSeminorm.completionSetoid
    (seminorm hw0 hw1 (width := width)))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- An actual domain point, retaining both sector witnesses. Equality is
specified by `domainSetoid`, not by literal equality of these witnesses. -/
structure DomainPoint where
  input : Sector
  output : Sector
  equation : A input.val = T 1 output.val

/-- Every domain point constructs the original derivative graph. -/
def graph (p : DomainPoint hw0 hw1 (width := width)) :
    GraphLimit hw0 hw1 p.input.val p.output.val :=
  graphOfEquation hw0 hw1 p.input.range p.output.range p.equation

/-- Explicit original sources for every domain point; no stream of
quotient representatives is selected. -/
def sourceRepresentative (p : DomainPoint hw0 hw1 (width := width))
    (n : Nat) : (D).Cauchy :=
  inverseSumRepresentative hw0 hw1 n (representative hw0 hw1 p.input.range)

theorem sourceRepresentative_pin (p : DomainPoint hw0 hw1 (width := width)) (n : Nat) :
    Class (sourceRepresentative hw0 hw1 p n) = (graph hw0 hw1 p).source n := by
  unfold sourceRepresentative
  rw [inverseSumRepresentative_pin,representative_pin]
  rfl

/-- The represented graph maps into, but does not redefine, the old domain. -/
def toOriginalDomain (p : DomainPoint hw0 hw1 (width := width)) :
    BF4WilsonAllNomeDerivativeGraph.Domain hw0 hw1 (width := width) :=
  Quotient.mk (BF4WilsonAllNomeDerivativeGraph.inputSetoid hw0 hw1)
    ⟨p.input.val,p.output.val,graph hw0 hw1 p⟩

theorem original_input_pin (p : DomainPoint hw0 hw1 (width := width)) :
    BF4WilsonAllNomeDerivativeGraph.input hw0 hw1 (toOriginalDomain hw0 hw1 p) =
      p.input.val := rfl

theorem original_action_pin (p : DomainPoint hw0 hw1 (width := width)) :
    BF4WilsonAllNomeDerivativeGraph.action hw0 hw1 (toOriginalDomain hw0 hw1 p) =
      p.output.val := rfl

def domainSetoid : Setoid (DomainPoint hw0 hw1 (width := width)) where
  r p q := p.input.val = q.input.val
  iseqv := ⟨fun _ => rfl,fun h => h.symm,fun h k => h.trans k⟩

/-- The operator output respects exactly the original input equality. -/
theorem output_congr (p q : DomainPoint hw0 hw1 (width := width))
    (h : p.input.val = q.input.val) : p.output.val = q.output.val := by
  have H := graph hw0 hw1 q
  rw [← h] at H
  exact BF4WilsonAllNomeDerivativeGraph.graph_single_valued hw0 hw1 (graph hw0 hw1 p) H

theorem originalDomain_eq_iff (p q : DomainPoint hw0 hw1 (width := width)) :
    toOriginalDomain hw0 hw1 p = toOriginalDomain hw0 hw1 q ↔ p.input.val = q.input.val :=
  ⟨fun h => congrArg (BF4WilsonAllNomeDerivativeGraph.input hw0 hw1) h,
    fun h => BF4WilsonAllNomeDerivativeGraph.input_injective hw0 hw1 _ _ h⟩

/-- Addition is an actual operation on this domain, with original carrier
input and output addition. No bounded total Hamiltonian is postulated. -/
def add (p q : DomainPoint hw0 hw1 (width := width)) : DomainPoint hw0 hw1 (width := width) where
  input := BF4WilsonAllNomeTimeSector.add hw0 hw1 p.input q.input
  output := BF4WilsonAllNomeTimeSector.add hw0 hw1 p.output q.output
  equation := by
    change A (BF4WilsonAllNomeLinear.completedAdd hw0 hw1 p.input.val q.input.val) =
      T 1 (BF4WilsonAllNomeLinear.completedAdd hw0 hw1 p.output.val q.output.val)
    rw [derivativeAction_add,completedTime_additive,p.equation,q.equation]

def realSmul (s : CReal) (cs : QCauchy s.approx)
    (p : DomainPoint hw0 hw1 (width := width)) : DomainPoint hw0 hw1 (width := width) where
  input := BF4WilsonAllNomeTimeSector.realSmul hw0 hw1 s cs p.input
  output := BF4WilsonAllNomeTimeSector.realSmul hw0 hw1 s cs p.output
  equation := BF4WilsonAllNomeDerivativeGraphRealLinear.realScale_equation hw0 hw1 s cs p.equation

/-- BOTH coordinates of every represented core pair belong to the sector. -/
def corePoint (X : (D).Cauchy) : DomainPoint hw0 hw1 (width := width) where
  input := BF4WilsonAllNomeTimeSector.fromTime hw0 hw1 X
  output := ⟨A (Class X),BF4WilsonAllNomeDerivativeGraphRange.outputRange hw0 hw1
    (BF4WilsonAllNomeDerivativeGraph.core hw0 hw1 (Class X)) (fun _ => X) (fun _ => rfl)⟩
  equation := BF4WilsonAllNomeDerivativeCore.derivativeAction_commutes_time hw0 hw1 1 (Class X)

/-- A computed sequence of actual domain points, dense at every sector state. -/
def coreApproximation (x : Sector) (n : Nat) : DomainPoint hw0 hw1 (width := width) :=
  corePoint hw0 hw1 (x.range.preimage n)

theorem coreApproximation_bound (x : Sector) (e : Q') (he : (0 : Q') < e)
    (n : Nat) (hn : x.range.modulus e ≤ n) :
    RCle (dist (coreApproximation hw0 hw1 x n).input.val x.val) (rat e) :=
  x.range.bound e he n hn

/-- Domain density returns its approximating points and its all-tail modulus. -/
def coreDensityCertificate (x : Sector) :
    Σ' points : Nat → DomainPoint hw0 hw1 (width := width), Σ' modulus : Q' → Nat,
      ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
        RCle (dist (points n).input.val x.val) (rat e) :=
  ⟨coreApproximation hw0 hw1 x,x.range.modulus,coreApproximation_bound hw0 hw1 x⟩

/-- Intrinsic real adjoint tests against this domain in this SAME sector.
No output, continuity modulus or graph conclusion is assumed. -/
def AdjointPair (u v : Sector) : Prop :=
  ∀ p : DomainPoint hw0 hw1 (width := width), B u.val p.output.val = B v.val p.input.val

theorem domain_adjoint (p : DomainPoint hw0 hw1 (width := width)) :
    AdjointPair hw0 hw1 p.input p.output :=
  fun q => (graph_symmetric hw0 hw1 (graph hw0 hw1 p) (graph hw0 hw1 q)).symm

/-- Testing only the represented core, which is actually in this domain,
recovers the original equation. Quotient induction is used only into Prop. -/
theorem adjoint_equation (u v : Sector) (h : AdjointPair hw0 hw1 u v) :
    A u.val = T 1 v.val := by
  apply (corePairings_iff_equation hw0 hw1 u.val v.val).mp
  intro x
  refine Quotient.inductionOn x ?_
  intro X
  exact h (corePoint hw0 hw1 X)

/-- Every intrinsic adjoint pair constructs a point of this SAME domain. -/
def ofAdjoint (u v : Sector) (h : AdjointPair hw0 hw1 u v) : DomainPoint hw0 hw1 (width := width) :=
  ⟨u,v,adjoint_equation hw0 hw1 u v h⟩

/-- Equality of the densely defined real graph and its intrinsic adjoint,
with the constructive converse given by `ofAdjoint`. -/
theorem equation_iff_adjoint (u v : Sector) :
    A u.val = T 1 v.val ↔ AdjointPair hw0 hw1 u v :=
  ⟨fun h => domain_adjoint hw0 hw1 ⟨u,v,h⟩,adjoint_equation hw0 hw1 u v⟩

/-- Constructive closedness in the sector's graph norm: the two state
sequences carry all their own representatives and Cauchy moduli. -/
def closedLimit (inputs outputs : CauchySequence hw0 hw1 (width := width))
    (equations : ∀ n, A (inputs.seq n).val = T 1 (outputs.seq n).val) :
    DomainPoint hw0 hw1 (width := width) where
  input := BF4WilsonAllNomeTimeSector.limit hw0 hw1 inputs
  output := BF4WilsonAllNomeTimeSector.limit hw0 hw1 outputs
  equation := by
    let graphs (n : Nat) := graphOfEquation hw0 hw1
      (inputs.seq n).range (outputs.seq n).range (equations n)
    let modulus (e : Q') := max
      (BF4WilsonAllNomeTimeSector.limitRate hw0 hw1 inputs e)
      (BF4WilsonAllNomeTimeSector.limitRate hw0 hw1 outputs e)
    have bound (e : Q') (he : (0 : Q') < e) (n : Nat) (hn : modulus e ≤ n) :
        RCle (dist (inputs.seq n).val
          (BF4WilsonAllNomeTimeSector.limit hw0 hw1 inputs).val) (rat e) ∧
        RCle (dist (outputs.seq n).val
          (BF4WilsonAllNomeTimeSector.limit hw0 hw1 outputs).val) (rat e) :=
      ⟨BF4WilsonAllNomeTimeSector.limit_bound hw0 hw1 inputs e he n
        (Nat.le_trans (Nat.le_max_left _ _) hn),
       BF4WilsonAllNomeTimeSector.limit_bound hw0 hw1 outputs e he n
        (Nat.le_trans (Nat.le_max_right _ _) hn)⟩
    exact (BF4WilsonAllNomeDerivativeGraph.graph_time_pin hw0 hw1
      (BF4WilsonAllNomeDerivativeGraph.diagonal hw0 hw1
        (fun n => (inputs.seq n).val) (fun n => (outputs.seq n).val)
        graphs modulus bound)).symm

/-- The intrinsic domain action is the derivative of the ORIGINAL real-time
semigroup, with an explicit Taylor radius in original lattice time units. -/
def realTaylorCertificate (p : DomainPoint hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ t : PositiveTime, RCle (realValue (timeValue t)) (rat r) →
        RCle (B (realRemainder hw0 hw1 t p.input.val p.output.val)
          (realRemainder hw0 hw1 t p.input.val p.output.val))
          (RCmul (RCmul (realValue (timeValue t)) (realValue (timeValue t))) (rat e))) := by
  let U := representative hw0 hw1 p.input.range
  let W := representative hw0 hw1 p.output.range
  have hU : Class U = p.input.val := representative_pin hw0 hw1 p.input.range
  have hW : Class W = p.output.val := representative_pin hw0 hw1 p.output.range
  have data := BF4WilsonAllNomeDerivativeGraphEquation.equationRealTaylorCertificate
    hw0 hw1 U W (by rw [hU]; exact p.input.range)
      (by rw [hW]; exact p.output.range) (by rw [hU,hW]; exact p.equation) e he
  simpa only [hU,hW] using data

theorem domain_nonnegative (p : DomainPoint hw0 hw1 (width := width)) :
    RCnonneg (B p.input.val p.output.val) := graph_nonnegative hw0 hw1 (graph hw0 hw1 p)

theorem domain_form_gap (p : DomainPoint hw0 hw1 (width := width))
    (h : B (unitState hw0 hw1 width) p.input.val = RCzero) :
    RCle (RCscale (BF4WilsonAllNomeLogCoreGap.coreMargin hw0 hw1 width)
      (B p.input.val p.input.val)) (B p.input.val p.output.val) :=
  BF4WilsonAllNomeDerivativeGraphGap.graph_form_gap hw0 hw1 (graph hw0 hw1 p) h

#print axioms graph
#print axioms sourceRepresentative
#print axioms sourceRepresentative_pin
#print axioms toOriginalDomain
#print axioms original_input_pin
#print axioms original_action_pin
#print axioms domainSetoid
#print axioms output_congr
#print axioms originalDomain_eq_iff
#print axioms add
#print axioms realSmul
#print axioms corePoint
#print axioms coreApproximation
#print axioms coreApproximation_bound
#print axioms coreDensityCertificate
#print axioms AdjointPair
#print axioms domain_adjoint
#print axioms adjoint_equation
#print axioms ofAdjoint
#print axioms equation_iff_adjoint
#print axioms closedLimit
#print axioms realTaylorCertificate
#print axioms domain_nonnegative
#print axioms domain_form_gap

end YMGap.Continuum.BF4WilsonAllNomeSectorDerivative
