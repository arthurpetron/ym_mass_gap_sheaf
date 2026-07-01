/-
# `sin π ≃ 0` via the double-angle reconstruction — a GREEN reduction to one atom

## Context

The companion module `Continuum.ArctanTanInversion` reduces `sin π ≃ 0` to the
existence of a `CircleModel` — i.e. to (ADD) a CReal-angle sine/cosine **addition
law** and (LINK) the transcendental arctan↔trig **base link**.  Both of those are
genuinely open infrastructure in this development: the trig layer proves only the
`Q'`-angle *nonnegative cosine* addition law `TrigAdd.cos_add_equiv_nonneg`; there
is no sine addition law, no signed cosine addition, and no CReal-angle lift.  So
the Gaussian-integer `CircleModel` route cannot yet be inhabited.

## What this module DELIVERS (fully green)

An INDEPENDENT reduction of the `k = 1` core `sin π ≃ 0` that uses only the
repo's own double-angle reconstruction (`CRealTrigFull`) plus the already-present
`CReal` congruence API — no addition law needed.  Concretely, with
`(bs, bc) = (sin(π/4), cos(π/4))` the Type-level base pair, `sin π` is two
double-angle steps up (`CRealTrigFull.sinPi bs bc = sinFullC bs bc 2`) and

    sin π ≃ 2·sin(π/2)·cos(π/2),        cos(π/2) = 1 − 2·sin²(π/4).

Hence `sin π ≃ 0` follows from `cos(π/2) ≃ 0`, and `cos(π/2) ≃ 0` follows from the
single sharp atom `2·sin²(π/4) ≃ 1`.  Both implications are proved here as genuine
`CReal.Equiv`s:

  * `sinPi_eqv_zero_of_cosHalfPi_zero` — `cos(π/2) ≃ 0  ⟹  sin π ≃ 0`
    (the `π` double-angle law `piDoubleAngle` composed with `mul` congruence and
    `A·0 ≃ 0`).
  * `cosHalfPi_eqv_zero_of_atom` — `2·bs² ≃ 1  ⟹  cos(π/2) ≃ 0`
    (definitional unfolding of `cosFullC bs bc 1 = 1 − 2·bs²`, then `1 − 1 ≃ 0`).
  * `sinPi_eqv_zero_of_atom` — the composite: `2·sin²(π/4) ≃ 1  ⟹  sin π ≃ 0`.

`SinQuarterAtom bs` names the residual `2·bs² ≃ 1` (intended `bs = sin(π/4)`,
i.e. `sin(π/4) = 1/√2`), the single transcendental series↔value input of THIS
route.

## Honest scope

This discharges only the `k = 1` instance `sin π ≃ 0` (feeding `J 1` of
`HaarClassIntegral.AngleCosineIntegral`).  The full family `sin((k+1)π) ≃ 0`
(needed for `J_succ` at all `k`) still requires the general multiple-angle /
addition law — the `CircleModel` residual — since only *dyadic* multiples of `π`
are reachable by iterated double-angle steps.  Nothing here is faked: the atom
`SinQuarterAtom` is a non-vacuous `CReal.Equiv` over the genuine `bs`.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only (the latter via reused `Q'`/`Nat`
helpers).  No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
The base pair `(bs, bc)` is `Type`-level data (Rule 8).
-/

import YMGap.Constructive.CRealTrigFull

namespace YMGap.Continuum.SinPiDoubleAngle

open YMGap.Constructive

/-! ## 1. Local `CReal` product helpers (pointwise / from the congruence API) -/

/-- `A·0 ≃ 0` (pointwise). -/
theorem mul_czero (A : CReal) : CReal.Equiv (CReal.mul A CReal.czero) CReal.czero :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.mul_zero_eqv (A.approx n))

/-- Right multiplicative congruence: `B ≃ B' ⇒ A·B ≃ A·B'`
(via commutativity + the left congruence `CReal.mul_congr_left`). -/
theorem cmul_congr_right {A B B' : CReal} (h : CReal.Equiv B B') :
    CReal.Equiv (CReal.mul A B) (CReal.mul A B') :=
  CReal.Equiv.trans (CRealAlg.cmul_comm A B)
    (CReal.Equiv.trans (CReal.mul_congr_left h) (CRealAlg.cmul_comm B' A))

/-! ## 2. The sharp residual atom -/

/-- **The single transcendental atom of the double-angle route:** `2·bs² ≃ 1`,
intended with `bs = sin(π/4)` (equivalently `sin(π/4) = 1/√2`).  This is the one
series↔value bridge; everything else below is algebra on `CReal`. -/
def SinQuarterAtom (bs : CReal) : Prop :=
  CReal.Equiv (CReal.mul (CReal.ofQ' (2 : Q')) (CReal.mul bs bs)) (CReal.ofQ' (1 : Q'))

/-! ## 3. `cos(π/2) ≃ 0` from the atom -/

/-- **`cos(π/2) ≃ 0` from `2·bs² ≃ 1`.**  `cosHalfPi bs bc = cosFullC bs bc 1 =
1 − 2·bs²` definitionally; the atom collapses `1 − (that) ≃ 1 − 1 ≃ 0`. -/
theorem cosHalfPi_eqv_zero_of_atom (bs bc : CReal) (h : SinQuarterAtom bs) :
    CReal.Equiv (CRealTrigFull.cosHalfPi bs bc) CReal.czero := by
  -- `cosHalfPi bs bc` unfolds (defeq) to `1 − 2·bs²`.
  show CReal.Equiv
      (CReal.sub (CReal.ofQ' (1 : Q'))
        (CReal.mul (CReal.ofQ' (2 : Q')) (CReal.mul bs bs))) CReal.czero
  refine CReal.Equiv.trans (CReal.sub_congr_right h) ?_
  -- `(1 − 1) ≃ 0`, pointwise.
  refine SumOfSquares.Equiv_of_approx_eqv (fun n => ?_)
  show ((1 : Q') + -(1 : Q')).eqv (0 : Q')
  decide

/-! ## 4. `sin π ≃ 0` from `cos(π/2) ≃ 0` -/

/-- **`sin π ≃ 0` from `cos(π/2) ≃ 0`.**  Uses the `π` double-angle law
`sin π ≃ 2·sin(π/2)·cos(π/2)`; with `cos(π/2) ≃ 0` both products collapse via
`A·0 ≃ 0`. -/
theorem sinPi_eqv_zero_of_cosHalfPi_zero (bs bc : CReal)
    (h : CReal.Equiv (CRealTrigFull.cosHalfPi bs bc) CReal.czero) :
    CReal.Equiv (CRealTrigFull.sinPi bs bc) CReal.czero := by
  have h1 : CReal.Equiv
      (CReal.mul (CRealTrigFull.sinFullC bs bc 1) (CRealTrigFull.cosHalfPi bs bc))
      CReal.czero :=
    CReal.Equiv.trans (cmul_congr_right h) (mul_czero _)
  exact CReal.Equiv.trans (CRealTrigFull.piDoubleAngle bs bc)
    (CReal.Equiv.trans (cmul_congr_right h1) (mul_czero _))

/-! ## 5. The composite reduction -/

/-- **`sin π ≃ 0` from the single atom `2·sin²(π/4) ≃ 1`.**  The genuine green
reduction of the `k = 1` cosine-integral core to one transcendental input. -/
theorem sinPi_eqv_zero_of_atom (bs bc : CReal) (h : SinQuarterAtom bs) :
    CReal.Equiv (CRealTrigFull.sinPi bs bc) CReal.czero :=
  sinPi_eqv_zero_of_cosHalfPi_zero bs bc (cosHalfPi_eqv_zero_of_atom bs bc h)

end YMGap.Continuum.SinPiDoubleAngle

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SinPiDoubleAngle.mul_czero
#print axioms YMGap.Continuum.SinPiDoubleAngle.cmul_congr_right
#print axioms YMGap.Continuum.SinPiDoubleAngle.cosHalfPi_eqv_zero_of_atom
#print axioms YMGap.Continuum.SinPiDoubleAngle.sinPi_eqv_zero_of_cosHalfPi_zero
#print axioms YMGap.Continuum.SinPiDoubleAngle.sinPi_eqv_zero_of_atom
