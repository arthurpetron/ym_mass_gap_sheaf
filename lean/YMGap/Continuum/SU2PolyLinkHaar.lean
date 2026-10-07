/-
# A constructed SU(2) single-link Haar functional on polynomials, and why
# `SU2TorusWilsonGibbs.LinkHaar SU2` cannot be instantiated as stated

J04 / Group Realizer.  ADDITIVE; does not edit `SU2TorusWilsonGibbs`.

## Obstruction for `LinkHaar SU2` (documented, not formalized)

`LinkHaar G` asks for `h : (G.Carrier → Q') → Q'` on **all** functions, additive,
positive, normalized and left-invariant.  Restricting to `{0,1}`-valued `F`
gives a finitely additive, left-invariant probability mean on all subsets of
`G = RationalQuaternion.UnitNorm`.  That group contains a free subgroup of rank
two modulo `±1` (the rational rotation group `SO(3, ℚ)` contains free
subgroups of rank two — Świerczkowski 1958; this classical fact is cited, not
checked here), hence
is non-amenable, hence admits **no** such mean.  So `LinkHaar SU2` is empty
(classically); no construction — from `quaternionHaar` or otherwise — can
inhabit it, and every theorem with a `LinkHaar SU2` hypothesis is vacuous.
Formalizing the paradoxical decomposition is not done here.

Fix (needs the Prover's file): state the link Haar on the polynomial
coordinate algebra (or on the span of characters), as `PolyLinkHaar` below.

## What is constructed here

* `PolyLinkHaar`: functional on `RatPoly` in the four coordinates of one link,
  additive, `Q'`-homogeneous, normalized.
* `quaternionPolyLinkHaar` — **instance by construction** from the exact
  `S³` Haar functional `quaternionHaar 1`.
* `quaternionPolyLinkHaar2` (two blocks) with `polyHaarAgrees` — the
  polynomial analogue of the Prover's OPEN `HaarAgreesUpTo H 2`, proved by
  definition — and `polyLinkSchurUpTo2` (reusing `polySchurUpTo2`).
* Consequently: `HaarAgreesUpTo H 2` for a `LinkHaar SU2` `H` is not provable
  because no such `H` exists (above); the Gibbs layer should consume
  `PolyLinkHaar` (or a class-function-span domain) instead.
* `eval_linkCharacter`: `χ_s` evaluates to the Gibbs file's `chi s x` at the
  rational coordinates of `x`.

Still open: polynomial left/right invariance as a field (the repo's
translation-degree modules are not wired in), positivity on squares,
and Schur for general `s`.
-/

import YMGap.Continuum.SU2TorusWilsonGibbs
import YMGap.Continuum.BF4CompactActionCPOrder
import YMGap.Continuum.BF4GeometricSpinNetworkMehler
import YMGap.Continuum.SU2QuaternionWilsonWeightSOS
import YMGap.Continuum.SU2TorusSchurSmall

namespace YMGap.Continuum.SU2PolyLinkHaar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection

/-- A single-link Haar functional on the polynomial coordinate algebra. -/
structure PolyLinkHaar where
  h : RatPoly → Q'
  add : ∀ p q, (h (polyAdd p q)).eqv (h p + h q)
  smul : ∀ (c : Q') p, (h (polySmul c p)).eqv (c * h p)
  norm : (h polyOne).eqv 1

/-- **Instance by construction** from the exact `S³` Haar functional. -/
def quaternionPolyLinkHaar : PolyLinkHaar where
  h := quaternionHaar 1
  add := fun p q => YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_append 1 p q
  smul := fun c p => YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polySmul 1 c p
  norm := by decide

/-- Single-link spin character `χ_s = U_s(x₀)`. -/
def linkCharacter (s : Nat) : RatPoly := characterPolynomial (polyVar 0) s

/-- Two-link (relative) version: exact Haar on two quaternion blocks. -/
def quaternionPolyLinkHaar2 : PolyLinkHaar where
  h := quaternionHaar 2
  add := fun p q => YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_append 2 p q
  smul := fun c p => YMGap.Continuum.BF4CompactActionCPOrder.quaternionHaar_polySmul 2 c p
  norm := by decide

/-- **Polynomial analogue of `HaarAgreesUpTo H 2`, proved**: the constructed
functional reproduces the Prover's `pairing s t` on relative-character
products (by definition), so `polySchurUpTo2` applies to it. -/
theorem polyHaarAgrees (s t : Nat) :
    quaternionPolyLinkHaar2.h (polyMul (relativeCharacter s) (relativeCharacter t)) =
      YMGap.Continuum.SU2TorusSchurSmall.pairing s t := rfl

/-- Schur `s, t ≤ 2` on the constructed polynomial link Haar (Prover's
evaluations, reused). -/
theorem polyLinkSchurUpTo2 (s t : Nat) (hs : s ≤ 2) (ht : t ≤ 2) :
    (quaternionPolyLinkHaar2.h (polyMul (relativeCharacter s) (relativeCharacter t))).eqv
      (if s = t then 1 else 0) := by
  rw [polyHaarAgrees]; exact YMGap.Continuum.SU2TorusSchurSmall.polySchurUpTo2 s t hs ht

/-- `χ_s` evaluates to the Gibbs file's class function `chi s` at the
coordinates of a rational unit quaternion. -/
theorem eval_linkCharacter (s : Nat) (x : SU2TorusWilsonGibbs.SU2.Carrier) :
    (evalRatPoly (fun i => if i = 0 then x.val.r else 0) (linkCharacter s)).eqv
      (SU2TorusWilsonGibbs.chi s x) := by
  refine Q'.eqv_trans _ _ _ (eval_characterPolynomial _ (polyVar 0) s) ?_
  exact SU2TorusWilsonGibbs.chebU_congr (evalRatPoly_var _ 0) s

end YMGap.Continuum.SU2PolyLinkHaar

#print axioms YMGap.Continuum.SU2PolyLinkHaar.quaternionPolyLinkHaar
#print axioms YMGap.Continuum.SU2PolyLinkHaar.polyLinkSchurUpTo2
#print axioms YMGap.Continuum.SU2PolyLinkHaar.eval_linkCharacter
