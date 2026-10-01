/-
# Actual zero-shift inverse on the original sector's vacuum complement

The positive-shift resolvents converge with an explicit modulus. Their
limit supplies an actual original derivative-domain point with prescribed
vacuum-orthogonal output. The original form margin gives uniqueness, so
both inverse identities hold on this same presented vacuum complement.
The range witnesses, action and original time unit are unchanged.

The bound depends on nome and width through `coreMargin`. This is neither
a spacing-uniform physical mass bound nor an identification with a
continuum OS Hamiltonian, and it makes no full-carrier inverse claim.
-/

import YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventEquation
import YMGap.Continuum.BF4WilsonAllNomeSectorZeroInjective

namespace YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolvent

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
open YMGap.Continuum.BF4WilsonAllNomeSectorDerivative (DomainPoint graph)
open YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventLimit
  (zeroShift zeroShift_orthogonal)
open YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolventEquation (domainPoint)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "B" => completedInner hw0 hw1
local notation "U" => unitState hw0 hw1 width
local notation "Sector" => BF4WilsonAllNomeTimeSector.State hw0 hw1 (width := width)
local notation "Point" => DomainPoint hw0 hw1 (width := width)

/-- Every actual domain output is orthogonal to the original vacuum,
whether or not its input is centered. -/
theorem output_orthogonal (p : Point) : B U p.output.val = RCzero := by
  have h := BF4WilsonAllNomeDerivativeGraphForm.graph_symmetric hw0 hw1
    (graph hw0 hw1 p) (BF4WilsonAllNomeDerivativeGraph.core hw0 hw1 U)
  rw [BF4WilsonAllNomeCompletedTime.completedUnit_fixed hw0 hw1 1,
    BF4WilsonAllNomeDerivativeCore.derivativeAction_unit_zero hw0 hw1,
    completedInner_zero_right] at h
  exact (completedInner_symm hw0 hw1 U p.output.val).trans h

/-- The constructed point has exactly the requested original sector output. -/
theorem inverse_right (x : Sector) (hx : B U x.val = RCzero) :
    (domainPoint hw0 hw1 x hx).output.val = x.val := rfl

/-- The same zero-shift construction recovers every centered original
domain input from its output. No new graph or operator is substituted. -/
theorem inverse_left (p : Point) (hp : B U p.input.val = RCzero) :
    (domainPoint hw0 hw1 p.output (output_orthogonal hw0 hw1 p)).input.val =
      p.input.val :=
  BF4WilsonAllNomeSectorZeroInjective.input_injective hw0 hw1
    (domainPoint hw0 hw1 p.output (output_orthogonal hw0 hw1 p)) p
    (zeroShift_orthogonal hw0 hw1 p.output (output_orthogonal hw0 hw1 p)) hp rfl

/-- The computed inverse depends only on the original completed input,
not on the presentation of its supplied range witness. -/
theorem inverse_congr (x y : Sector) (hx : B U x.val = RCzero)
    (hy : B U y.val = RCzero) (h : x.val = y.val) :
    (zeroShift hw0 hw1 x hx).val = (zeroShift hw0 hw1 y hy).val :=
  BF4WilsonAllNomeSectorZeroInjective.input_injective hw0 hw1
    (domainPoint hw0 hw1 x hx) (domainPoint hw0 hw1 y hy)
    (zeroShift_orthogonal hw0 hw1 x hx) (zeroShift_orthogonal hw0 hw1 y hy) h

/-- The inverse's symmetry is inherited from the SAME derivative graph. -/
theorem inverse_symmetric (x y : Sector) (hx : B U x.val = RCzero)
    (hy : B U y.val = RCzero) :
    B (zeroShift hw0 hw1 x hx).val y.val =
      B x.val (zeroShift hw0 hw1 y hy).val :=
  (BF4WilsonAllNomeDerivativeGraphForm.graph_symmetric hw0 hw1
    (graph hw0 hw1 (domainPoint hw0 hw1 x hx))
    (graph hw0 hw1 (domainPoint hw0 hw1 y hy))).symm

/-- Nonnegativity concerns the constructed inverse, with its actual output. -/
theorem inverse_nonnegative (x : Sector) (hx : B U x.val = RCzero) :
    RCnonneg (B (zeroShift hw0 hw1 x hx).val x.val) :=
  BF4WilsonAllNomeDerivativeGraphForm.graph_nonnegative hw0 hw1
    (graph hw0 hw1 (domainPoint hw0 hw1 x hx))

/-- Explicit original-domain inverse witness and uniqueness on the
vacuum complement. The associated approximation modulus is `zeroShiftRate`.
The witness lives in Type and retains both sector range witnesses. -/
def inverseCertificate (x : Sector) (hx : B U x.val = RCzero) :
    Σ' p : Point,
      (p.output.val = x.val) ∧ (B U p.input.val = RCzero) ∧
        ∀ q : Point, B U q.input.val = RCzero → q.output.val = x.val →
          q.input.val = p.input.val :=
  ⟨domainPoint hw0 hw1 x hx, rfl, zeroShift_orthogonal hw0 hw1 x hx,
    fun q hq ho => BF4WilsonAllNomeSectorZeroInjective.input_injective hw0 hw1
      q (domainPoint hw0 hw1 x hx) hq (zeroShift_orthogonal hw0 hw1 x hx) ho⟩

#print axioms output_orthogonal
#print axioms inverse_right
#print axioms inverse_left
#print axioms inverse_congr
#print axioms inverse_symmetric
#print axioms inverse_nonnegative
#print axioms inverseCertificate

end YMGap.Continuum.BF4WilsonAllNomeSectorZeroResolvent
