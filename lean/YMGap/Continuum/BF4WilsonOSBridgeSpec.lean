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

/-- An OS-side family of same-object form bounds indexed by discrete lag.

`bound n` is intentionally a parameter: an eventual concrete instantiation
can choose `twoStepRate ^ n` times the zero-lag form, or a different certified
coefficient.  The bridge transport below therefore does not smuggle in a
particular decay law.
-/
def OSFormFamily {W : Type uW} {O : Type uO} {R : Type uR}
    (B : SameObjectBridge W O R) (leR : R → R → Prop)
    (bound : Nat → R → R) : Prop :=
  ∀ n y, B.orthogonalO y →
    leR (B.pairingO y (B.stepO n y))
      (bound n (B.pairingO y y))

/-- An OS-side family of relative same-object loss bounds.

`subR` is left abstract so the certificate can later be instantiated with the
completed `CReal.RC` subtraction.  This is the exact shape needed by the
relative-energy survival compiler: a lagged defect is bounded by a scalar
fraction of the same vector's norm.
-/
def OSRelativeLossFamily {W : Type uW} {O : Type uO} {R : Type uR}
    (B : SameObjectBridge W O R) (leR : R → R → Prop)
    (subR : R → R → R) (scale : R → R → R)
    (delta : Nat → R) : Prop :=
  ∀ n y, B.orthogonalO y →
    leR (subR (B.pairingO y y) (B.pairingO y (B.stepO n y)))
      (scale (delta n) (B.pairingO y y))

/- A lag-two relative-loss input is the exact shape supplied by the current
   completed complex Wilson consumer.  Keeping this separate from the
   all-lag family avoids demanding unproved interpolation merely to transport
   the two-step physical estimate. -/
def OSRelativeLossGap {W : Type uW} {O : Type uO} {R : Type uR}
    (B : SameObjectBridge W O R) (leR : R → R → Prop)
    (subR : R → R → R) (scale : R → R → R) (delta : R) : Prop :=
  ∀ y, B.orthogonalO y →
    leR (subR (B.pairingO y y) (B.pairingO y (B.stepO 2 y)))
      (scale delta (B.pairingO y y))

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

/-- Transport every member of an OS form family to the Wilson carrier.

This is the same equality-only argument as the two-step consumer, with the
lag left explicit.  It is the bridge-facing shape required before a
same-object correlator decay estimate can be compared across carriers.
-/
theorem transfer_form_family
    {W : Type uW} {O : Type uO} {R : Type uR}
    (B : SameObjectBridge W O R) (leR : R → R → Prop)
    (bound : Nat → R → R) (hOS : OSFormFamily B leR bound)
    (x : W) (hx : B.orthogonalW x) (n : Nat) :
    leR (B.pairingW x (B.stepW n x))
      (bound n (B.pairingW x x)) := by
  have h := hOS n (B.toOS x) (B.orthogonal_preserved x hx)
  rw [B.step_preserved n x,
    B.pairing_preserved x (B.stepW n x),
    B.pairing_preserved x x] at h
  exact h

/-- Transport every member of an OS relative-loss family to the Wilson
carrier.  The subtraction and scalar operations are used only through the
same pairing-preservation equalities, so no algebraic law is hidden here.
-/
theorem transfer_relative_loss_family
    {W : Type uW} {O : Type uO} {R : Type uR}
    (B : SameObjectBridge W O R) (leR : R → R → Prop)
    (subR : R → R → R) (scale : R → R → R)
    (delta : Nat → R) (hOS : OSRelativeLossFamily B leR subR scale delta)
    (x : W) (hx : B.orthogonalW x) (n : Nat) :
    leR (subR (B.pairingW x x) (B.pairingW x (B.stepW n x)))
      (scale (delta n) (B.pairingW x x)) := by
  have h := hOS n (B.toOS x) (B.orthogonal_preserved x hx)
  rw [B.step_preserved n x,
    B.pairing_preserved x (B.stepW n x),
    B.pairing_preserved x x] at h
  exact h

/-- Transport the exact lag-two relative-loss inequality without inventing
an all-lag interpolation hypothesis. -/
theorem transfer_twoStep_relative_loss
    {W : Type uW} {O : Type uO} {R : Type uR}
    (B : SameObjectBridge W O R) (leR : R → R → Prop)
    (subR : R → R → R) (scale : R → R → R) (delta : R)
    (hOS : OSRelativeLossGap B leR subR scale delta)
    (x : W) (hx : B.orthogonalW x) :
    leR (subR (B.pairingW x x) (B.pairingW x (B.stepW 2 x)))
      (scale delta (B.pairingW x x)) := by
  have h := hOS (B.toOS x) (B.orthogonal_preserved x hx)
  rw [B.step_preserved 2 x,
    B.pairing_preserved x (B.stepW 2 x),
    B.pairing_preserved x x] at h
  exact h

#print axioms transfer_twoStep_form_gap
#print axioms transfer_form_family
#print axioms transfer_relative_loss_family
#print axioms transfer_twoStep_relative_loss

end YMGap.Continuum.BF4WilsonOSBridgeSpec
