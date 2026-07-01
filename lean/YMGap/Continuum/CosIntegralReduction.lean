/-
Sharpening the `AngleCosineIntegral` primitive: peel the proven `(2/π)`
normalization off, leaving only the **un-normalized** definite cosine integrals.

# The reduction

`Continuum.HaarClassIntegral.AngleCosineIntegral` bundles the `(2/π)`-normalized
integrals `J_k = (2/π)·∫_0^π cos(kθ)dθ` with the two computed values
`J_0 ≃ 2`, `J_{k+1} ≃ 0`.  The `2` in `J_0 ≃ 2` is `(2/π)·π`, i.e. it silently
carries the reciprocal-of-π arithmetic.

Here we isolate that arithmetic.  A `CosIntegralFamily` carries the RAW integrals
`I_k = ∫_0^π cos(kθ)dθ` with the un-normalized values

    I_0 ≃ π           ( = ∫_0^π 1 dθ )
    I_{k+1} ≃ 0       ( = [sin((k+1)θ)/(k+1)]_0^π = sin((k+1)π)/(k+1) )

and we CONSTRUCT an `AngleCosineIntegral` from it by multiplying through by the
constructive real `2/π` (`Constructive.Pi.twoOverPi`).  The `J_0 ≃ 2` field is
then discharged NOT by an axiom but by the already-proven reciprocal law
`Constructive.Pi.twoOverPi_mul_pi : (2/π)·π ≃ 2`; the `J_{k+1} ≃ 0` field by
`(2/π)·0 ≃ 0`.

Net effect: the honest residual for core ③ is tightened from "the normalized
integrals `J_k`" to "the raw integrals `I_k`", with the `(2/π)` normalization
fully discharged from repo-proven facts.  The genuinely-irreducible analytic
content is unchanged and unhidden: `I_0 ≃ π` and `I_{k+1} ≃ 0` (the latter
`≡ sin((k+1)π) = 0`), the definite cosine integral over the irrational angle.

# What is delivered (axiom-clean, no fakes)

  * `CosIntegralFamily` — the raw definite cosine integral family with the two
    un-normalized values, carried Type-level (AGENTS.md Rule 8).
  * `toAngleCosineIntegral` — the constructor discharging the `(2/π)`
    normalization via `twoOverPi_mul_pi`.
  * `charOrtho_orthonormal_of_family`, `haarUnit_eq_one_of_family`,
    `physical_reflection_diagonal_of_family` — core ③'s continuous character
    orthogonality, Haar normalization, and physical Wilson reflection
    diagonalization, re-derived FROM a `CosIntegralFamily` (i.e. the full
    consumer chain goes through the sharpened residual).

# Honest verdict

This is a genuine reduction, NOT a closure: `CosIntegralFamily` is not inhabited
here.  Its two fields are exactly the definite integral evaluations
`∫_0^π cos(kθ)dθ = πδ_{k0}`, whose `k ≥ 1` case is `sin(kπ) = 0` for the
Machin-defined `π` — a `cos`/`sin` of an irrational multiple-of-π angle, outside
the `[0,1]`-restricted `CReal`-argument trig substrate.  What IS newly discharged
is the `(2/π)` normalization arithmetic, from the proven `twoOverPi_mul_pi`.

# Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only (via reused `CReal`/`Q'` helpers).
No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
-/

import YMGap.Continuum.HaarClassIntegral
import YMGap.Constructive.Pi

namespace YMGap.Continuum.CosIntegralReduction

open YMGap.Continuum.HaarClassIntegral
open YMGap.Continuum.ReflectionPositivity
open YMGap.Constructive

/-! ## 1. The raw (un-normalized) definite cosine integral family -/

/-- **The raw definite cosine integrals** `I_k = ∫_0^π cos(kθ)dθ` over `[0,π]`,
with the two un-normalized computed values `I_0 ≃ π` and `I_{k+1} ≃ 0`
(`= sin((k+1)π)/(k+1)`).  Carried Type-level (AGENTS.md Rule 8). -/
structure CosIntegralFamily where
  /-- `I_k = ∫_0^π cos(kθ)dθ`. -/
  I : Nat → CReal
  /-- `I_0 = ∫_0^π 1 dθ = π`. -/
  I_zero : CReal.Equiv (I 0) Pi.pi
  /-- `I_{k+1} = [sin((k+1)θ)/(k+1)]_0^π = sin((k+1)π)/(k+1) = 0`. -/
  I_succ : ∀ k, CReal.Equiv (I (k + 1)) CReal.czero

/-! ## 2. The constructor: discharge the `(2/π)` normalization -/

/-- **The `(2/π)` normalization, discharged.**  From the raw integrals `I_k` we
build the normalized primitive `J_k = (2/π)·I_k`.  The two computed values are
recovered from repo-proven facts:

  * `J_0 = (2/π)·I_0 ≃ (2/π)·π ≃ 2`  — the second `≃` is `Pi.twoOverPi_mul_pi`;
  * `J_{k+1} = (2/π)·I_{k+1} ≃ (2/π)·0 ≃ 0`. -/
def toAngleCosineIntegral (F : CosIntegralFamily) : AngleCosineIntegral where
  J := fun k => CReal.mul Pi.twoOverPi (F.I k)
  J_zero :=
    CReal.Equiv.trans (cmul_congr_right F.I_zero) Pi.twoOverPi_mul_pi
  J_succ := fun k =>
    CReal.Equiv.trans (cmul_congr_right (F.I_succ k)) (mul_czero Pi.twoOverPi)

/-! ## 3. Core ③ consumers, re-derived from a `CosIntegralFamily`

Everything `HaarClassIntegral` proves from an `AngleCosineIntegral` now flows
from the sharpened residual `CosIntegralFamily`, via `toAngleCosineIntegral`. -/

/-- **Continuous second-kind Chebyshev (character) orthogonality**
`haarClass(U_m·U_n) ≃ δ_{mn}`, from a raw cosine integral family. -/
theorem charOrtho_orthonormal_of_family (F : CosIntegralFamily) (m n : Nat) :
    CReal.Equiv (charOrtho (toAngleCosineIntegral F) m n)
      (if m = n then CReal.ofQ' (1 : Q') else CReal.czero) :=
  charOrtho_orthonormal (toAngleCosineIntegral F) m n

/-- **Haar normalization** `haarClass(1) ≃ 1`, from a raw cosine integral family. -/
theorem haarUnit_eq_one_of_family (F : CosIntegralFamily) :
    CReal.Equiv (haarUnit (toAngleCosineIntegral F)) (CReal.ofQ' (1 : Q')) :=
  haarUnit_eq_one (toAngleCosineIntegral F)

/-- **The physical Wilson reflection diagonalization** `reflWeight·δ_{mn}`,
from a raw cosine integral family (the headline consumer of core ③). -/
theorem physical_reflection_diagonal_of_family (F : CosIntegralFamily)
    (t : Q') (ht : (0 : Q') ≤ t) (N m n : Nat) (hm : m < N) (hn : n < N) :
    (physical_bridge_of_primitive (toAngleCosineIntegral F) t ht N).Rphys m n
      = if m = n then Quotient.mk CReal.crealSetoid (reflWeight t ht (m + 1))
        else Quotient.mk CReal.crealSetoid CReal.czero :=
  physical_reflection_diagonal_from_primitive (toAngleCosineIntegral F) t ht N m n hm hn

end YMGap.Continuum.CosIntegralReduction

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CosIntegralReduction.toAngleCosineIntegral
#print axioms YMGap.Continuum.CosIntegralReduction.charOrtho_orthonormal_of_family
#print axioms YMGap.Continuum.CosIntegralReduction.haarUnit_eq_one_of_family
#print axioms YMGap.Continuum.CosIntegralReduction.physical_reflection_diagonal_of_family
