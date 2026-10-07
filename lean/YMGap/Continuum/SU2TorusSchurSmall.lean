/-
# Schur orthonormality of SU(2) spin characters for spins s, t ≤ 2

First concrete non-abelian input for `SU2TorusWilsonGibbs`.  ADDITIVE.

* `polySchurUpTo2` (PROVED, exact evaluation): on the exact two-block S³ Haar
  functional `quaternionHaar 2`, the relative characters
  `relativeCharacter s` (`= χ_s(g₀g₁⁻¹)` by `SU2Realized.relativeCharacter_eq_spinCharacter`)
  satisfy `∫ χ_s χ_t = δ_{st}` for all `s, t ≤ 2`.  The diagonal `s = 1, 2`
  cases are YM Group Realizer's `SU2Realized.selfPairing_one/_two` (read-only
  import); the rest are new exact evaluations.
* `SU2SchurUpTo H J` (restricted hypothesis), `SU2Schur.toUpTo`.
* `HaarAgreesUpTo H J` (**OPEN bridge**): the link functional `H` reproduces
  `quaternionHaar 2` on products of characters up to spin `J`.
* `su2SchurUpTo2_of_agrees`: agreement + `polySchurUpTo2` give `SU2SchurUpTo H 2`.

Proved for small `s` only; general Schur orthonormality stays OPEN.
U(1) contrast: the dimensions `χ_s(1) = s+1` and the spin-1 = adjoint channel
are SU(2) data; U(1) characters are one-dimensional.
-/

import YMGap.Continuum.SU2TorusWilsonGibbs
import YMGap.RepTheory.SU2RealizedRow

namespace YMGap.Continuum.SU2TorusSchurSmall

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.SU2TorusWilsonGibbs
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionRelativeCharacterSelection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.RepTheory

/-- `∫ χ_s χ_t` on the exact two-block Haar functional. -/
def pairing (s t : Nat) : Q' :=
  quaternionHaar 2 (polyMul (relativeCharacter s) (relativeCharacter t))

theorem pairing_eq_selfPairing (s : Nat) : pairing s s = SU2Realized.selfPairing s := rfl

set_option maxRecDepth 100000 in
theorem pairing_00 : (pairing 0 0).eqv 1 := by decide
set_option maxRecDepth 100000 in
theorem pairing_01 : (pairing 0 1).eqv 0 := by decide
set_option maxRecDepth 100000 in
theorem pairing_02 : (pairing 0 2).eqv 0 := by decide
set_option maxRecDepth 100000 in
theorem pairing_10 : (pairing 1 0).eqv 0 := by decide
set_option maxRecDepth 100000 in
theorem pairing_12 : (pairing 1 2).eqv 0 := by decide
set_option maxRecDepth 100000 in
theorem pairing_20 : (pairing 2 0).eqv 0 := by decide
set_option maxRecDepth 100000 in
theorem pairing_21 : (pairing 2 1).eqv 0 := by decide

theorem pairing_11 : (pairing 1 1).eqv 1 := SU2Realized.selfPairing_one
theorem pairing_22 : (pairing 2 2).eqv 1 := SU2Realized.selfPairing_two

/-- **Schur orthonormality for `s, t ≤ 2`** (exact, proved). -/
theorem polySchurUpTo2 : ∀ s t, s ≤ 2 → t ≤ 2 →
    (pairing s t).eqv (if s = t then 1 else 0)
  | 0, 0, _, _ => pairing_00
  | 0, 1, _, _ => pairing_01
  | 0, 2, _, _ => pairing_02
  | 1, 0, _, _ => pairing_10
  | 1, 1, _, _ => pairing_11
  | 1, 2, _, _ => pairing_12
  | 2, 0, _, _ => pairing_20
  | 2, 1, _, _ => pairing_21
  | 2, 2, _, _ => pairing_22
  | s + 3, _, h, _ => absurd h (by omega)
  | _, t + 3, _, h => absurd h (by omega)

/-- Restricted Schur hypothesis on a link Haar functional. -/
structure SU2SchurUpTo (H : LinkHaar SU2) (J : Nat) : Prop where
  orth : ∀ s t, s ≤ J → t ≤ J →
    (H.h (fun x => chi s x * chi t x)).eqv (if s = t then 1 else 0)

theorem SU2Schur.toUpTo {H : LinkHaar SU2} (hS : SU2Schur H) (J : Nat) :
    SU2SchurUpTo H J := ⟨fun s t _ _ => hS.orth s t⟩

/-- **OPEN bridge**: `H` agrees with the exact polynomial S³ Haar functional on
character products up to spin `J`. -/
structure HaarAgreesUpTo (H : LinkHaar SU2) (J : Nat) : Prop where
  agree : ∀ s t, s ≤ J → t ≤ J → (H.h (fun x => chi s x * chi t x)).eqv (pairing s t)

/-- Agreement with `quaternionHaar` and the proved small-spin evaluations give
the restricted Schur hypothesis consumed by the Gibbs layer. -/
theorem su2SchurUpTo2_of_agrees {H : LinkHaar SU2} (hA : HaarAgreesUpTo H 2) :
    SU2SchurUpTo H 2 :=
  ⟨fun s t hs ht => Q'.eqv_trans _ _ _ (hA.agree s t hs ht) (polySchurUpTo2 s t hs ht)⟩

end YMGap.Continuum.SU2TorusSchurSmall
