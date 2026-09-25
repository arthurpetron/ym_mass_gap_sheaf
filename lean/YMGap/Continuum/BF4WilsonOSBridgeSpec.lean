/-
# Minimal same-object bridge certificate

The concrete all-nome Wilson completion and the strict OS completion currently
live in different carrier constructions.  This file isolates the exact typed
data needed to transport a two-step form bound from the latter to the former.
It is deliberately independent of either construction, so it can be checked
while one heavy reflected-face object is unavailable.

An inhabitant must supply the map, pairing preservation, time compatibility,
vacuum preservation, and preservation of the chosen vacuum-complement
predicate.  No inhabitant is asserted here.  The consumer theorem below is the
kernel-checked consequence once those fields and an OS form bound are supplied.
-/

namespace YMGap.Continuum.BF4WilsonOSBridgeSpec

set_option autoImplicit false

universe uW uO uR

/-- The exact data needed to identify one Wilson carrier with one OS carrier.

`pairingW` and `pairingO` may later be instantiated with the completed
`CReal.RC` pairings.  Keeping the codomain abstract makes the missing bridge
explicit rather than importing one carrier and silently treating it as the
other.
-/
structure SameObjectBridge (W : Type uW) (O : Type uO) (R : Type uR) where
  pairingW : W → W → R
  pairingO : O → O → R
  stepW : Nat → W → W
  stepO : Nat → O → O
  toOS : W → O
  vacuumW : W
  vacuumO : O
  orthogonalW : W → Prop
  orthogonalO : O → Prop
  pairing_preserved : ∀ x y, pairingO (toOS x) (toOS y) = pairingW x y
  step_preserved : ∀ n x, stepO n (toOS x) = toOS (stepW n x)
  vacuum_preserved : toOS vacuumW = vacuumO
  orthogonal_preserved : ∀ x, orthogonalW x → orthogonalO (toOS x)

/-- A form bound proved on the OS carrier, expressed using the bridge's
pairing/step data.  This is the only analytic field needed by the transport
consumer; positivity, self-adjointness, and density remain separate inputs.
-/
def OSFormGap {W : Type uW} {O : Type uO} {R : Type uR}
    (B : SameObjectBridge W O R) (leR : R → R → Prop)
    (scale : R → R → R) (rate : R) : Prop :=
  ∀ y, B.orthogonalO y →
    leR (B.pairingO y (B.stepO 2 y))
      (scale rate (B.pairingO y y))

/-- Transport the OS two-step form bound to every Wilson vector certified
orthogonal by the bridge.

This is constructive transport by the supplied equalities alone.  It does not
construct the carrier map or prove the OS bound; those remain the explicit
bridge obligations represented by `SameObjectBridge` and `OSFormGap`.
-/
theorem transfer_twoStep_form_gap
    {W : Type uW} {O : Type uO} {R : Type uR}
    (B : SameObjectBridge W O R) (leR : R → R → Prop)
    (scale : R → R → R) (rate : R) (hOS : OSFormGap B leR scale rate)
    (x : W) (hx : B.orthogonalW x) :
    leR (B.pairingW x (B.stepW 2 x))
      (scale rate (B.pairingW x x)) := by
  have h := hOS (B.toOS x) (B.orthogonal_preserved x hx)
  rw [B.step_preserved 2 x,
    B.pairing_preserved x (B.stepW 2 x),
    B.pairing_preserved x x] at h
  exact h

#print axioms transfer_twoStep_form_gap

end YMGap.Continuum.BF4WilsonOSBridgeSpec
