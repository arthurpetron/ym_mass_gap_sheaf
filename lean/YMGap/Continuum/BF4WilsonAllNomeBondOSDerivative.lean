/-
The original sector derivative on the completed odd-window bond sources.
Domain points retain their original two range witnesses until the final
input-equality quotient. Taylor radii are computed only from represented
points, never by selecting a representative of an arbitrary quotient.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorDerivative
import YMGap.Continuum.BF4WilsonAllNomeBondOSRealTime
import YMGap.Continuum.BF4WilsonAllNomeBondOSLinear

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.PositiveRealDyadicTimeData (PositiveTime)
open YMGap.Continuum.BF4ExactSlabThermodynamicPositiveTimePins (timeValue realValue)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (completedInner unitState)
open YMGap.Continuum.BF4WilsonAllNomeDistance (completedDist)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion Rows rowSetoid toSectorRep bondCompletedDistance bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_distance bondValue_inner bondAction
    bondAction_value vacuum bondValue_ofSource)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (ofState bondValue_ofState ofState_congr bondValue_sub bondValue_realSmul)
open YMGap.Continuum.BF4WilsonAllNomeBondOSRealization (image_unit)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative
  (DomainPoint domainSetoid output_congr coreApproximation coreApproximation_bound
    domain_nonnegative domain_form_gap graph)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphForm (graph_symmetric)
open YMGap.Continuum.BF4WilsonAllNomeDerivativeGraphReal (realRemainder)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "B" => bondCompletedInner hw0 hw1
local notation "Class" => Quotient.mk (domainSetoid hw0 hw1 (width := width))
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

/-- The actual sector derivative domain, modulo equality of its input vector. -/
def Domain : Type := Quotient (domainSetoid hw0 hw1 (width := width))

def input : Domain hw0 hw1 (width := width) → H :=
  Quotient.lift (fun p => ofState hw0 hw1 p.input)
    (fun _ _ h => ofState_congr hw0 hw1 h)

def output : Domain hw0 hw1 (width := width) → H :=
  Quotient.lift (fun p => ofState hw0 hw1 p.output)
    (fun p q h => ofState_congr hw0 hw1 (output_congr hw0 hw1 p q h))

theorem input_mk (p : DomainPoint hw0 hw1 (width := width)) :
    input hw0 hw1 (Class p) = ofState hw0 hw1 p.input := rfl

theorem output_mk (p : DomainPoint hw0 hw1 (width := width)) :
    output hw0 hw1 (Class p) = ofState hw0 hw1 p.output := rfl

theorem bondValue_input_mk (p : DomainPoint hw0 hw1 (width := width)) :
    bondValue hw0 hw1 (input hw0 hw1 (Class p)) = p.input.val :=
  bondValue_ofState hw0 hw1 p.input

theorem bondValue_output_mk (p : DomainPoint hw0 hw1 (width := width)) :
    bondValue hw0 hw1 (output hw0 hw1 (Class p)) = p.output.val :=
  bondValue_ofState hw0 hw1 p.output

/-- There is no domain witness choice: equal physical inputs give equal classes. -/
theorem input_injective {d e : Domain hw0 hw1 (width := width)}
    (h : input hw0 hw1 d = input hw0 hw1 e) : d = e := by
  revert h
  refine Quotient.inductionOn₂ d e ?_
  intro p q
  intro h
  apply Quotient.sound
  have hv := congrArg (bondValue hw0 hw1) h
  simpa only [bondValue_input_mk] using hv

theorem nonnegative (d : Domain hw0 hw1 (width := width)) :
    RCnonneg (B (input hw0 hw1 d) (output hw0 hw1 d)) := by
  refine Quotient.inductionOn d ?_
  intro p
  rw [bondValue_inner, bondValue_input_mk, bondValue_output_mk]
  exact domain_nonnegative hw0 hw1 p

theorem symmetric (d e : Domain hw0 hw1 (width := width)) :
    B (output hw0 hw1 d) (input hw0 hw1 e) =
      B (input hw0 hw1 d) (output hw0 hw1 e) := by
  refine Quotient.inductionOn₂ d e ?_
  intro p q
  rw [bondValue_inner, bondValue_inner, bondValue_input_mk,
    bondValue_output_mk, bondValue_input_mk, bondValue_output_mk]
  exact graph_symmetric hw0 hw1 (graph hw0 hw1 p) (graph hw0 hw1 q)

private theorem bondValue_vacuum :
    bondValue hw0 hw1 (vacuum hw0 hw1 (width := width)) =
      unitState hw0 hw1 width := by
  rw [vacuum, bondValue_ofSource, image_unit]

theorem form_gap (d : Domain hw0 hw1 (width := width))
    (h : B (vacuum hw0 hw1 (width := width)) (input hw0 hw1 d) = RCzero) :
    RCle (RCscale (BF4WilsonAllNomeLogCoreGap.coreMargin hw0 hw1 width)
      (B (input hw0 hw1 d) (input hw0 hw1 d)))
      (B (input hw0 hw1 d) (output hw0 hw1 d)) := by
  revert h
  refine Quotient.inductionOn d ?_
  intro p h
  rw [bondValue_inner, bondValue_inner, bondValue_vacuum,
    bondValue_input_mk, bondValue_output_mk] at *
  exact domain_form_gap hw0 hw1 p h

/-- Supplied bond rows determine both domain approximants and their rate. -/
def densityCertificate (X : Rows hw0 hw1 (width := width)) :
    Σ' points : Nat → Domain hw0 hw1 (width := width), Σ' modulus : Q' → Nat,
      ∀ e : Q', (0 : Q') < e → ∀ n, modulus e ≤ n →
        RCle (bondCompletedDistance hw0 hw1 (input hw0 hw1 (points n))
          (Quotient.mk (rowSetoid hw0 hw1) X)) (rat e) := by
  let x := toSectorRep hw0 hw1 X
  refine ⟨fun n => Class (coreApproximation hw0 hw1 x n), x.range.modulus, ?_⟩
  intro e he n hn
  rw [bondValue_distance, bondValue_input_mk]
  change RCle (completedDist hw0 hw1
    (coreApproximation hw0 hw1 x n).input.val x.val) (rat e)
  exact coreApproximation_bound hw0 hw1 x e he n hn

def bondRemainder (t : PositiveTime) (u v : H) : H :=
  BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
    (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 u (bondAction hw0 hw1 t u))
    (BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 t.real t.cauchy v)

theorem bondValue_remainder (t : PositiveTime) (u v : H) :
    bondValue hw0 hw1 (bondRemainder hw0 hw1 t u v) =
      realRemainder hw0 hw1 t (bondValue hw0 hw1 u) (bondValue hw0 hw1 v) := by
  unfold bondRemainder realRemainder
  rw [bondValue_sub, bondValue_sub, bondValue_realSmul, bondAction_value]
  rw [BF4WilsonAllNomePositiveTimePins.realTimeAction_pin]

/-- Original represented graph Taylor control on the actual physical bond
action; the radius is computed from the supplied domain point. -/
def realTaylorCertificate (p : DomainPoint hw0 hw1 (width := width))
    (e : Q') (he : (0 : Q') < e) :
    Σ' r : Q', ((0 : Q') < r) ×'
      (∀ t : PositiveTime, RCle (realValue (timeValue t)) (rat r) →
        RCle (B (bondRemainder hw0 hw1 t (input hw0 hw1 (Class p))
            (output hw0 hw1 (Class p)))
          (bondRemainder hw0 hw1 t (input hw0 hw1 (Class p))
            (output hw0 hw1 (Class p))))
          (RCmul (RCmul (realValue (timeValue t)) (realValue (timeValue t)))
            (rat e))) := by
  let C := BF4WilsonAllNomeSectorDerivative.realTaylorCertificate hw0 hw1 p e he
  refine ⟨C.1, C.2.1, ?_⟩
  intro t ht
  rw [bondValue_inner, bondValue_remainder, bondValue_input_mk,
    bondValue_output_mk]
  exact C.2.2 t ht

#print axioms Domain
#print axioms input
#print axioms output
#print axioms input_mk
#print axioms output_mk
#print axioms bondValue_input_mk
#print axioms bondValue_output_mk
#print axioms input_injective
#print axioms nonnegative
#print axioms symmetric
#print axioms form_gap
#print axioms densityCertificate
#print axioms bondValue_remainder
#print axioms realTaylorCertificate

end YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative
