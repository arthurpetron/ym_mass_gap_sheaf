/-
# Original centered Wilson inputs and gauge-invariant representatives

The original finite-mean subtraction preserves the existing gauge predicate.
A supplied represented gauge vector that is already orthogonal to the
original constant therefore has a representative whose EVERY term is both
gauge-invariant and exactly centered, in the same completion. The existing
centering construction keeps the input Cauchy modulus.

Lower and upper plaquette expressions supply concrete dense inputs. No
nonzero norm, survival under scaling, strict estimate or OS identification
is asserted.
-/

import YMGap.Continuum.BF4ExactSlabGaugeSweep
import YMGap.Continuum.BF4ExactSlabConditionalCenteredCompletion

namespace YMGap.Continuum.BF4ExactSlabGaugeCenteredWitness

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSRepresentedSector
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabVertexGaugeAction
open YMGap.Continuum.BF4ExactSlabGaugeRepresentedCompletion
open YMGap.Continuum.BF4ExactSlabConditionalCovariance
open YMGap.Continuum.BF4ExactSlabConditionalCenteredCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (extent stage : Nat)

local notation "K" => headCutoff w + stage
local notation "hK" => Nat.le_add_right (headCutoff w) stage
local notation "F" => fullData hw0 hw1 K extent hK
local notation "GP" => GaugePolynomial hw0 hw1 K extent hK
local notation "W" => Witness hw0 hw1 K extent hK

/-- Uses the ACTUAL original finite mean, not a free or floor normalization. -/
theorem centered_polynomial (p : (F).V) (hp : GP p) :
    GP (centered hw0 hw1 extent stage p) :=
  fun tags => (hp tags).add
    ((Invariant.one extent tags).smul (-(mean hw0 hw1 extent stage p)))

/-- The original centered polynomial is an explicit dense sector input. -/
def centered_input (p : (F).V) (hp : GP p) :
    W (embedV F (centered hw0 hw1 extent stage p)) :=
  ofPolynomial hw0 hw1 K extent hK _ (centered_polynomial hw0 hw1 extent stage p hp)

/-- Both predicates hold termwise, while the pin remains the supplied x. -/
def centered_rep {x : GNSCompletionSpace F} (a : W x)
    (hx : BF4ExactSlabSweepChebyshev.Centered hw0 hw1 K extent hK x) :
    Representative F (fun p => GP p ∧
      Q'.eqv ((F).B p (unit hw0 hw1 extent stage)) 0) x where
  rep := centeredCauchy hw0 hw1 extent stage a.rep
  terms n := ⟨centered_polynomial hw0 hw1 extent stage _ (a.terms n),
    centeredCauchy_term_centered hw0 hw1 extent stage a.rep n⟩
  pin := (centeredCauchy_same_class hw0 hw1 extent stage a.rep (by
    rw [a.pin]
    exact hx)).trans a.pin

/-- Exact centering does not worsen the supplied gauge representative modulus. -/
theorem centered_rep_modulus {x : GNSCompletionSpace F} (a : W x)
    (hx : BF4ExactSlabSweepChebyshev.Centered hw0 hw1 K extent hK x) :
    (centered_rep hw0 hw1 extent stage a hx).rep.modulus = a.rep.modulus := rfl

/-- The actual auxiliary states admit simultaneously centered and invariant
polynomial approximants, not two unrelated representatives. -/
def coupled_centered_reps (c : Q') {x : GNSCompletionSpace F} (a : W x)
    (hx : BF4ExactSlabSweepChebyshev.Centered hw0 hw1 K extent hK x) (n : Nat) :
    Representative F (fun p => GP p ∧ Q'.eqv ((F).B p (unit hw0 hw1 extent stage)) 0)
      (BF4ExactSlabSweepChebyshev.coupled hw0 hw1 K extent hK c x n).1 ×
    Representative F (fun p => GP p ∧ Q'.eqv ((F).B p (unit hw0 hw1 extent stage)) 0)
      (BF4ExactSlabSweepChebyshev.coupled hw0 hw1 K extent hK c x n).2 :=
  let hg := BF4ExactSlabGaugeSweep.coupled hw0 hw1 K extent hK c a n
  let hc := BF4ExactSlabSweepChebyshev.coupled_centered hw0 hw1 K extent hK c x hx n
  ⟨centered_rep hw0 hw1 extent stage hg.1 hc.1,
    centered_rep hw0 hw1 extent stage hg.2 hc.2⟩

/-- Original lower Wilson/plaquette expressions, not temporal-gauge surrogates. -/
def lower_input (half : Nat) (e : PlaquetteExpression half) :
    Witness hw0 hw1 K (centralExtent half) hK
      (embedV (fullData hw0 hw1 K (centralExtent half) hK)
        (centered hw0 hw1 (centralExtent half) stage ⟨lower e, lower_supported e⟩)) :=
  centered_input hw0 hw1 (centralExtent half) stage _ (fun tags => lower_invariant tags e)

/-- The reflected upper insertion is still an original full-action polynomial. -/
def upper_input (half : Nat) (e : PlaquetteExpression half) :
    Witness hw0 hw1 K (centralExtent half) hK
      (embedV (fullData hw0 hw1 K (centralExtent half) hK)
        (centered hw0 hw1 (centralExtent half) stage ⟨upper e, upper_supported e⟩)) :=
  centered_input hw0 hw1 (centralExtent half) stage _ (fun tags => upper_invariant tags e)

#print axioms centered_polynomial
#print axioms centered_input
#print axioms centered_rep
#print axioms centered_rep_modulus
#print axioms coupled_centered_reps
#print axioms lower_input
#print axioms upper_input

end YMGap.Continuum.BF4ExactSlabGaugeCenteredWitness
