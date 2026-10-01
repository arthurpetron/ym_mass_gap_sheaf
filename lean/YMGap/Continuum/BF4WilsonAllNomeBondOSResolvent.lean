/-
# Positive resolvent on the completed physical bond sources

The original sector resolvent consumes the time-range witness carried by each
physical bond row.  Its domain point retains both original range witnesses
until the derivative's input-equality quotient is formed.  There is no
representative choice on either quotient.  The inverse and norm laws are in
fixed-nome, fixed-width lattice-time units, not a physical scaling claim.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative
import YMGap.Continuum.BF4WilsonAllNomeSectorResolvent

namespace YMGap.Continuum.BF4WilsonAllNomeBondOSResolvent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedAdd completedSmul)
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint domainSetoid)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion Rows rowSetoid toSectorRep close_iff_limit_eq bondCompletedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (ofState bondValue_ofState ofState_congr bondValue_add bondValue_smul)
open YMGap.Continuum.BF4WilsonAllNomeBondOSDerivative
  (Domain input output input_mk output_mk bondValue_input_mk bondValue_output_mk
    input_injective)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => BondCompletion hw0 hw1 (width := width)
local notation "D" => Domain hw0 hw1 (width := width)
local notation "Sector" => State hw0 hw1 (width := width)
local notation "Point" => DomainPoint hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "R" => BF4WilsonAllNomeResolventLimit.resolvent hw0 hw1
local notation "Class" => Quotient.mk (domainSetoid hw0 hw1 (width := width))

/-- The original positive resolvent on every completed physical bond class.
Each row first constructs its own witnessed sector state. -/
def resolvent (lambda : Q') (hl : (0 : Q') < lambda) : H → H :=
  Quotient.lift
    (fun X => ofState hw0 hw1
      (BF4WilsonAllNomeSectorResolvent.state hw0 hw1 lambda hl
        (toSectorRep hw0 hw1 X)))
    (fun X Y h => ofState_congr hw0 hw1
      (BF4WilsonAllNomeSectorResolvent.state_congr hw0 hw1 lambda hl
        (toSectorRep hw0 hw1 X) (toSectorRep hw0 hw1 Y)
        ((close_iff_limit_eq hw0 hw1 X Y).mp h)))

/-- The range witness is returned as an actual represented derivative-domain
point before quotienting by equality of its original input vector. -/
def resolventDomain (lambda : Q') (hl : (0 : Q') < lambda) : H → D :=
  Quotient.lift
    (fun X => Class (BF4WilsonAllNomeSectorResolvent.domainPoint hw0 hw1
      lambda hl (toSectorRep hw0 hw1 X)))
    (fun X Y h => Quotient.sound
      (BF4WilsonAllNomeSectorResolvent.state_congr hw0 hw1 lambda hl
        (toSectorRep hw0 hw1 X) (toSectorRep hw0 hw1 Y)
        ((close_iff_limit_eq hw0 hw1 X Y).mp h)))

/-- The completed physical bond vector is exactly the previously constructed
original resolvent applied to that same completed vector. -/
theorem bondValue_resolvent (lambda : Q') (hl : (0 : Q') < lambda) (x : H) :
    bondValue hw0 hw1 (resolvent hw0 hw1 lambda hl x) =
      R lambda hl (bondValue hw0 hw1 x) := by
  induction x using Quotient.inductionOn with
  | h X =>
      change bondValue hw0 hw1
        (ofState hw0 hw1 (BF4WilsonAllNomeSectorResolvent.state hw0 hw1
          lambda hl (toSectorRep hw0 hw1 X))) =
        R lambda hl (toSectorRep hw0 hw1 X).val
      rw [bondValue_ofState]
      exact BF4WilsonAllNomeSectorResolvent.state_pin hw0 hw1 lambda hl
        (toSectorRep hw0 hw1 X)

theorem input_resolventDomain (lambda : Q') (hl : (0 : Q') < lambda) (x : H) :
    input hw0 hw1 (resolventDomain hw0 hw1 lambda hl x) =
      resolvent hw0 hw1 lambda hl x := by
  apply bondValue_injective hw0 hw1
  induction x using Quotient.inductionOn with
  | h X => rfl

/-- The original shifted graph action, expressed only with the constructed
linear operations on the same completed physical bond carrier. -/
def shifted (lambda : Q') (p : D) : H :=
  BF4WilsonAllNomeBondOSLinear.add hw0 hw1
    (BF4WilsonAllNomeBondOSLinear.smul hw0 hw1 lambda (input hw0 hw1 p))
    (output hw0 hw1 p)

theorem bondValue_shifted_mk (lambda : Q') (p : Point) :
    bondValue hw0 hw1 (shifted hw0 hw1 lambda (Class p)) =
      (BF4WilsonAllNomeSectorResolvent.shifted hw0 hw1 lambda p).val := by
  unfold shifted
  rw [bondValue_add, bondValue_smul, bondValue_input_mk, bondValue_output_mk]
  rfl

/-- Every completed bond class is attained by its constructed domain point. -/
theorem inverse_right (lambda : Q') (hl : (0 : Q') < lambda) (x : H) :
    shifted hw0 hw1 lambda (resolventDomain hw0 hw1 lambda hl x) = x := by
  apply bondValue_injective hw0 hw1
  induction x using Quotient.inductionOn with
  | h X =>
      change bondValue hw0 hw1
        (shifted hw0 hw1 lambda
          (Class (BF4WilsonAllNomeSectorResolvent.domainPoint hw0 hw1
            lambda hl (toSectorRep hw0 hw1 X)))) =
        (toSectorRep hw0 hw1 X).val
      rw [bondValue_shifted_mk]
      exact BF4WilsonAllNomeSectorResolvent.inverse_right hw0 hw1 lambda hl
        (toSectorRep hw0 hw1 X)

/-- On every witnessed physical derivative-domain point, the constructed
resolvent is a left inverse of its positive shifted graph action. -/
theorem inverse_left (lambda : Q') (hl : (0 : Q') < lambda) (p : D) :
    resolventDomain hw0 hw1 lambda hl (shifted hw0 hw1 lambda p) = p := by
  apply input_injective hw0 hw1
  rw [input_resolventDomain]
  apply bondValue_injective hw0 hw1
  rw [bondValue_resolvent]
  induction p using Quotient.inductionOn with
  | h q =>
      rw [bondValue_shifted_mk, bondValue_input_mk]
      exact BF4WilsonAllNomeSectorResolvent.inverse_left hw0 hw1 lambda hl q

/-- The original squared-norm ceiling, now on the same completed physical
bond sources; no new norm or inverse outside this represented sector. -/
theorem norm_bound (lambda : Q') (hl : (0 : Q') < lambda) (x : H) :
    RCle (bondCompletedInner hw0 hw1
      (resolvent hw0 hw1 lambda hl x) (resolvent hw0 hw1 lambda hl x))
      (RCscale (Q'.recipPos lambda hl * Q'.recipPos lambda hl)
        (bondCompletedInner hw0 hw1 x x)) := by
  rw [bondValue_inner, bondValue_inner, bondValue_resolvent]
  induction x using Quotient.inductionOn with
  | h X =>
      have h := BF4WilsonAllNomeSectorResolvent.norm_bound hw0 hw1 lambda hl
        (toSectorRep hw0 hw1 X)
      rw [BF4WilsonAllNomeSectorResolvent.state_pin] at h
      exact h

#print axioms resolvent
#print axioms resolventDomain
#print axioms bondValue_resolvent
#print axioms input_resolventDomain
#print axioms shifted
#print axioms bondValue_shifted_mk
#print axioms inverse_right
#print axioms inverse_left
#print axioms norm_bound

end YMGap.Continuum.BF4WilsonAllNomeBondOSResolvent
