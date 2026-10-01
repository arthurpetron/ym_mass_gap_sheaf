/-
# Constructed positive-parameter resolvent of the original sector derivative

The actual dyadic limit returns a point of the EXISTING derivative domain
for every witnessed sector input. Its two-sided inverse laws are equality
of original vectors, not equality of presentation witnesses. Every range
modulus and output representative is computed from supplied data.

This is the original fixed-nome, fixed-width sector derivative, in original
lattice-time units. It is not an identification with a physical reflected
OS Hamiltonian or a continuum/scaling theorem. The ambient time kernel is
unchanged; the inverse laws are asserted only on the witnessed sector.
-/

import YMGap.Continuum.BF4WilsonAllNomeResolventEquation
import YMGap.Continuum.BF4WilsonAllNomeResolventRange
import YMGap.Continuum.BF4WilsonAllNomeSectorShiftInjective

namespace YMGap.Continuum.BF4WilsonAllNomeSectorResolvent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeLinear
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws
open YMGap.Continuum.BF4WilsonAllNomeTimeSector (State)
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint output_congr)
open YMGap.Continuum.BF4WilsonAllNomeTimeRangeClosed (representative representative_pin)
open YMGap.Continuum.BF4WilsonAllNomeResolventLimit (resolvent)
open YMGap.Continuum.BF4WilsonAllNomeResolventRange (resolventRange)
open YMGap.Continuum.BF4WilsonAllNomeResolventEquation
  (resolvent_equation resolvent_norm_bound)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "V" => Completion hw0 hw1 width
local notation "Sector" => State hw0 hw1 (width := width)
local notation "Point" => DomainPoint hw0 hw1 (width := width)
local notation "B" => completedInner hw0 hw1
local notation "A" => completedAdd hw0 hw1
local notation "S" => completedSmul hw0 hw1
local notation "Sub" => completedSub hw0 hw1
local notation "R" => resolvent hw0 hw1

/-- The existing range witness supplies a representative; no choice on
arbitrary completion classes is used to build this sector witness. -/
def state (lambda : Q') (hl : (0 : Q') < lambda) (x : Sector) : Sector where
  val := R lambda hl x.val
  range := by
    have H := resolventRange hw0 hw1 lambda hl (representative hw0 hw1 x.range)
    rw [representative_pin] at H
    exact H

theorem state_pin (lambda : Q') (hl : (0 : Q') < lambda) (x : Sector) :
    (state hw0 hw1 lambda hl x).val = R lambda hl x.val := rfl

/-- Actual surjectivity witness for lambda I plus the original sector
derivative. Both coordinates carry their original range data. -/
def domainPoint (lambda : Q') (hl : (0 : Q') < lambda) (x : Sector) : Point where
  input := state hw0 hw1 lambda hl x
  output := ⟨Sub x.val (S lambda (state hw0 hw1 lambda hl x).val),
    BF4WilsonAllNomeTimeRangeLinear.subtract hw0 hw1 x.range
      (BF4WilsonAllNomeTimeRangeLinear.rationalSmul hw0 hw1 lambda
        (state hw0 hw1 lambda hl x).range)⟩
  equation := resolvent_equation hw0 hw1 lambda hl x.val

/-- The positive-shifted value of any existing domain point stays in the
same sector; it is not a total extension of the derivative. -/
def shifted (lambda : Q') (p : Point) : Sector where
  val := A (S lambda p.input.val) p.output.val
  range := BF4WilsonAllNomeTimeRangeLinear.add hw0 hw1
    (BF4WilsonAllNomeTimeRangeLinear.rationalSmul hw0 hw1 lambda p.input.range)
    p.output.range

/-- Every sector value is attained by the constructed domain point. -/
theorem inverse_right (lambda : Q') (hl : (0 : Q') < lambda) (x : Sector) :
    (shifted hw0 hw1 lambda (domainPoint hw0 hw1 lambda hl x)).val = x.val := by
  change A (S lambda (R lambda hl x.val))
    (Sub x.val (S lambda (R lambda hl x.val))) = x.val
  rw [completedAdd_comm]
  unfold completedSub
  rw [completedAdd_assoc, completedNeg_add, completedAdd_zero]

/-- Applying the resolvent to the positive-shifted value of EVERY existing
domain point recovers its original input, not just a newly built core. -/
theorem inverse_left (lambda : Q') (hl : (0 : Q') < lambda) (p : Point) :
    (domainPoint hw0 hw1 lambda hl (shifted hw0 hw1 lambda p)).input.val =
      p.input.val := by
  apply BF4WilsonAllNomeSectorShiftInjective.input_injective hw0 hw1 lambda hl
  exact inverse_right hw0 hw1 lambda hl (shifted hw0 hw1 lambda p)

theorem inverse_left_output (lambda : Q') (hl : (0 : Q') < lambda) (p : Point) :
    (domainPoint hw0 hw1 lambda hl (shifted hw0 hw1 lambda p)).output.val =
      p.output.val :=
  output_congr hw0 hw1 _ p (inverse_left hw0 hw1 lambda hl p)

/-- The inverse has the original 1/lambda norm ceiling, with lambda explicit. -/
theorem norm_bound (lambda : Q') (hl : (0 : Q') < lambda) (x : Sector) :
    RCle (B (state hw0 hw1 lambda hl x).val (state hw0 hw1 lambda hl x).val)
      (RCscale (Q'.recipPos lambda hl * Q'.recipPos lambda hl) (B x.val x.val)) :=
  resolvent_norm_bound hw0 hw1 lambda hl x.val

/-- Equality is the original-vector setoid equality, independent of the
range witnesses chosen to present the input. -/
theorem state_congr (lambda : Q') (hl : (0 : Q') < lambda) (x y : Sector)
    (h : x.val = y.val) :
    (state hw0 hw1 lambda hl x).val = (state hw0 hw1 lambda hl y).val :=
  congrArg (R lambda hl) h

/-- Constructive existence returns the actual domain point and its two
original-vector identities, with all range data retained in that point. -/
def certificate (lambda : Q') (hl : (0 : Q') < lambda) (x : Sector) :
    {p : Point // p.input.val = R lambda hl x.val ∧
      (shifted hw0 hw1 lambda p).val = x.val} :=
  ⟨domainPoint hw0 hw1 lambda hl x, rfl, inverse_right hw0 hw1 lambda hl x⟩

#print axioms state
#print axioms state_pin
#print axioms domainPoint
#print axioms shifted
#print axioms inverse_right
#print axioms inverse_left
#print axioms inverse_left_output
#print axioms norm_bound
#print axioms state_congr
#print axioms certificate

end YMGap.Continuum.BF4WilsonAllNomeSectorResolvent
