/-
# The UNDIFFERENTIATED limit-level Jacobi identity as a `CReal.Equiv`
  (Wall-2, Route A: ϑ₃^series ≃ ϑ₃^product as constructive reals)

This module assembles the `N → ∞` limit of the ALREADY-PROVEN finite Gauss
q-binomial identity `GaussQBinom.gauss_qbinom_all`
(`qProd z q N ≈ gaussSum z q N` for all finite `N`) into the equality of the two
`CReal` limits, via the generic limit-of-equal-sequences engine
`CReal.Equiv_of_limit_of_equal` of `Constructive/CRealAbs.lean`.

## What is GENUINELY closed here (new, axiom-clean, reusable)

* **`gauss_qbinom_creal_equiv`** — for ANY two `CReal`s `P`, `S` whose `N`-th
  approximations are EXACTLY the Gauss product / sum partials
  (`P.approx N = qProd z q N`, `S.approx N = gaussSum z q N`), their limits are
  `Equiv`: `CReal.Equiv P S`.  This is the genuine `N → ∞` limit of
  `gauss_qbinom_all`, with the matched-at-each-`N` rational identity lifted through
  `convergesTo_self` on both sides — the two limits coincide even though the
  product and sum partials converge at DIFFERENT rates (the rates never enter; only
  the per-`N` equality does).  This is precisely the structural fact the
  closure-progress notes named as the route's step (1): making both finite-
  difference families differentiate the SAME limit function `F = ϑ₃`.

* **`Equiv_ofQ'_of_eqv`** — the small bridge `a ≈ b → Equiv (ofQ' a) (ofQ' b)`
  used to feed the per-`N` rational identity into the engine.

## The honest residual (AGENTS.md Rule 6)

What this module does NOT do: identify the Gauss `(z, q)`-parametrised
`qProd`/`gaussSum` with the CONCRETE theta-product / theta-series partials in the
`(a, θ)`-parametrisation carried by `dSeriesCReal` / `Rhalf` (the substitution
`z = z(θ)`, `q = a`, and the `cos`-weighting that turns `1 + z·q^{2j−1}` into
`1 + 2a^{2j−1}cos2θ + a^{4j−2}`).  Supplying that identification — i.e. a `P`, `S`
with `P.approx N = qProd …`, `S.approx N = gaussSum …` that ARE the theta CReals —
is the remaining packaging step.  Once supplied, `gauss_qbinom_creal_equiv` yields
the common limit function the Route-A derivative-uniqueness assembly
(`JTPInstance.ThetaUniqAssembly`) needs.  The engine that consumes it is fully
discharged here; the residual is the concrete parametrisation match.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (`Quot.sound` only via reused
`Nat`/`Int`/`omega`/`pow` helpers).  No `Classical.*`, no `native_decide`, no
`sorry`.
-/

import YMGap.Constructive.CRealAbs
import YMGap.Constructive.SumOfSquares
import YMGap.Continuum.GaussQBinom

namespace YMGap.Continuum.ThetaLimit

open YMGap.Constructive
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The rational-identity bridge `a ≈ b → Equiv (ofQ' a) (ofQ' b)` -/

/-- **`Equiv (ofQ' a) (ofQ' b)` from `a ≈ b`.**  The two constant `CReal`s have
approximations `a` and `b` respectively, so the termwise-equality lift
(`SumOfSquares.Equiv_of_approx_eqv`) applies. -/
theorem Equiv_ofQ'_of_eqv {a b : Q'} (h : a ≈ b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) :=
  SumOfSquares.Equiv_of_approx_eqv (fun _ => h)

/-! ## 2. The `N → ∞` limit of the finite Gauss q-binomial identity

The finite identity `qProd z q N ≈ gaussSum z q N` (proved for all `N` in
`GaussQBinom.gauss_qbinom_all`) lifts to the equality of the two `CReal` limits,
through the generic limit-of-equal-sequences engine: with `aSeq N = ofQ' (qProd
z q N)`, `bSeq N = ofQ' (gaussSum z q N)`, each converging to its `CReal` (`P`, `S`
respectively, by `convergesTo_self`), and the termwise `Equiv` from
`gauss_qbinom_all`, uniqueness of limits gives `Equiv P S`. -/

/-- **THE UNDIFFERENTIATED LIMIT-LEVEL JACOBI IDENTITY (general form).**
Let `P`, `S` be `CReal`s realising the Gauss product / sum partials at parameters
`(z, q)`: `P.approx N = qProd z q N` and `S.approx N = gaussSum z q N` for every
`N`.  Then their limits are equal: `CReal.Equiv P S`.

This is the genuine `N → ∞` limit of the finite Gauss q-binomial identity
`GaussQBinom.gauss_qbinom_all`, assembled through the generic
`CReal.Equiv_of_limit_of_equal` (limit of equal sequences).  The product and sum
partials converge at DIFFERENT rates, but the rates play no role — only the
matched-at-each-`N` rational equality `qProd z q N ≈ gaussSum z q N` is used.
Specialised to the theta substitution, this makes the theta-SERIES and
theta-PRODUCT `CReal`s the SAME limit function `F = ϑ₃`, which is exactly what the
Route-A derivative-uniqueness assembly requires (its common-`F` field). -/
theorem gauss_qbinom_creal_equiv (z q : Q') {P S : CReal}
    (hP : ∀ N : Nat, P.approx N = GaussQBinom.qProd z q N)
    (hS : ∀ N : Nat, S.approx N = GaussQBinom.gaussSum z q N) :
    CReal.Equiv P S := by
  -- aSeq N = ofQ' (P.approx N), bSeq N = ofQ' (S.approx N).
  -- termwise: ofQ' (qProd N) ≈ ofQ' (gaussSum N) from gauss_qbinom_all.
  refine CReal.Equiv_of_limit_of_equal (aSeq := fun N => CReal.ofQ' (P.approx N))
    (bSeq := fun N => CReal.ofQ' (S.approx N)) ?_ ?_ ?_
  · intro N
    -- Equiv (ofQ' (P.approx N)) (ofQ' (S.approx N)) from P_N ≈ S_N.
    have hPN : P.approx N = GaussQBinom.qProd z q N := hP N
    have hSN : S.approx N = GaussQBinom.gaussSum z q N := hS N
    have heq : P.approx N ≈ S.approx N := by
      rw [hPN, hSN]; exact GaussQBinom.gauss_qbinom_all z q N
    exact Equiv_ofQ'_of_eqv heq
  · exact CReal.convergesTo_self P
  · exact CReal.convergesTo_self S

end YMGap.Continuum.ThetaLimit

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ThetaLimit.Equiv_ofQ'_of_eqv
#print axioms YMGap.Continuum.ThetaLimit.gauss_qbinom_creal_equiv
