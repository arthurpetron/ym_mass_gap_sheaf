/-
# The engine route to the interchange: `dSeriesCReal ≈ Rhalf` from the two C¹ witnesses

This module assembles, from the in-tree signatures, the composite

    interchangeViaEngine : CReal.Equiv (dSeriesCReal …) (Rhalf …)

which is exactly `JTPIdentity.DiffJTP`'s conclusion, produced by feeding the
finite-product truncation family to the CReal C¹-limit engine and pairing it,
across the SAME common `F = ϑ₃`, with the unconditional series-side witness.  The
two witnesses are

  * `Dprod := ThetaProdDprodClose.thetaProdDprod … Hdconv`
        : `FDDerivDataC F (Rhalf …) x`      (product side, engine-produced)
  * `Dser  := ThetaSeriesFDDeriv.thetaSeriesFDDeriv … Hser`
        : `FDDerivDataC F (dSeriesCReal …) x`  (series side, UNCONDITIONAL)

and the conclusion is the two-witness derivative-uniqueness

  * `TsumDeriv.fdDeriv_uniqueC Dser Dprod : Equiv (dSeriesCReal …) (Rhalf …)`.

## The honest verdict this module encodes

`interchangeViaEngine` is CLOSED **given `Hdconv`**, but the engine is a *consumer*,
not a *producer*, of the interchange.  `Hdconv : UnifDerivConvC (prodDeriv …) Rhalf x`
is content-equal to `JTPIdentity.DiffJTP` — the double-limit interchange
`lim_h lim_M = lim_M lim_h`.  The engine (`fdDeriv_uniqueC`) genuinely discharges the
four-piece telescope, the `q/4` bookkeeping, and the two-witness uniqueness —
everything **except `Hdconv` itself**.

To make the residual explicit and relocatable, the module also exposes the
`HdconvClose` split of `Hdconv` into

  * `ProdLimitConv`     — the convergence half `ofQ'(prodDeriv …) → L`, `L = Θ·Σσ`
                          (the honest home of the double-limit interchange), and
  * `ProdLimitIsRhalf`  — the pure identity `L ≈ Rhalf` (no modulus).

`interchangeViaEngineOfSplit` runs the whole route from these two residuals via
`HdconvClose.hdconvOfSplit`, showing precisely that the engine relocates — but does
NOT close — the interchange, whose home is `ProdLimitConv.conv`.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  `Hdconv` (or, in the split form, the two named
`Type`-level residuals) is a hypothesis, never `sorry`.
-/

import YMGap.Continuum.ThetaProdDprodClose
import YMGap.Continuum.ThetaSeriesFDDeriv
import YMGap.Continuum.HdconvClose
import YMGap.Continuum.FiniteProductFDDeriv
import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.JTPIdentity

namespace YMGap.Continuum.InterchangeViaEngine

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. The composite `interchangeViaEngine` (CLOSED given `Hdconv`) -/

/-- **THE ENGINE-ROUTE INTERCHANGE (CLOSED given `Hdconv`).**  The product-side
witness `Dprod` (engine-produced from `Hdconv`) and the unconditional series-side
witness `Dser`, over the SAME common `F`, feed the two-witness derivative-uniqueness
`TsumDeriv.fdDeriv_uniqueC` to yield the interchange conclusion

    Equiv (dSeriesCReal …) (Rhalf …)   ( = `JTPIdentity.DiffJTP`'s statement).

Everything here is genuine engine bookkeeping; the *only* content-bearing input is
`Hdconv`, which is content-equal to the double-limit interchange itself. -/
theorem interchangeViaEngine {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal)
    (fk : Nat → Q' → Q') (dk : Nat → Q')
    (Dk : ∀ k, TsumDeriv.FDDerivData (fun t => fk k t) (dk k) x)
    (C  : FiniteProductFDDeriv.MulCombinator)
    (Hpt : ThetaProdDprodClose.PtwiseProdData F fk)
    (Huni : ThetaProdDprodClose.UniformProdModulus C fk dk Dk)
    (Hdconv : ThetaSeriesFDDeriv.UnifDerivConvC
                (fun M t => FiniteProductFDDeriv.prodDeriv fk dk t M)
                (JTPIdentity.Rhalf ha0 ha1 hx hx1) x)
    (Hser : ThetaSeriesFDDeriv.ThetaSeriesC1Inputs ha0 ha1 hx hx1 F) :
    CReal.Equiv (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1)
                (JTPIdentity.Rhalf ha0 ha1 hx hx1) :=
  -- Dser : FDDerivDataC F dSeriesCReal x   (series side, unconditional)
  -- Dprod : FDDerivDataC F Rhalf x         (product side, engine-produced from Hdconv)
  -- fdDeriv_uniqueC Dser Dprod : Equiv dSeriesCReal Rhalf
  TsumDeriv.fdDeriv_uniqueC
    (ThetaSeriesFDDeriv.thetaSeriesFDDeriv ha0 ha1 hx hx1 F Hser)
    (ThetaProdDprodClose.thetaProdDprod ha0 ha1 hx hx1 F fk dk Dk C Hpt Huni Hdconv)

/-! ## 2. The same route from the `HdconvClose` split (relocates the interchange) -/

/-- **THE ENGINE ROUTE FROM THE SPLIT (CLOSED given the two named residuals).**
Feeding the convergence half `P : ProdLimitConv` and the pure identity half
`hId : ProdLimitIsRhalf … P` through `HdconvClose.hdconvOfSplit` reconstructs
`Hdconv`, then runs `interchangeViaEngine`.  This makes explicit that the engine
route reduces the interchange conclusion to `ProdLimitConv.conv` (the honest home of
the double-limit interchange) plus the modulus-free identity `ProdLimitIsRhalf`.  The
engine consumes both but produces neither. -/
theorem interchangeViaEngineOfSplit {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal)
    (fk : Nat → Q' → Q') (dk : Nat → Q')
    (Dk : ∀ k, TsumDeriv.FDDerivData (fun t => fk k t) (dk k) x)
    (C  : FiniteProductFDDeriv.MulCombinator)
    (Hpt : ThetaProdDprodClose.PtwiseProdData F fk)
    (Huni : ThetaProdDprodClose.UniformProdModulus C fk dk Dk)
    (P : HdconvClose.ProdLimitConv fk dk x)
    (hId : HdconvClose.ProdLimitIsRhalf ha0 ha1 hx hx1 P)
    (Hser : ThetaSeriesFDDeriv.ThetaSeriesC1Inputs ha0 ha1 hx hx1 F) :
    CReal.Equiv (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1)
                (JTPIdentity.Rhalf ha0 ha1 hx hx1) :=
  interchangeViaEngine ha0 ha1 hx hx1 F fk dk Dk C Hpt Huni
    (HdconvClose.hdconvOfSplit ha0 ha1 hx hx1 P hId) Hser

/-! ## 3. The `DiffJTP`-shaped corollary : the interchange, symmetrized -/

/-- **The `DiffJTP`-oriented interchange (CLOSED given `Hdconv`).**  The
`Rhalf ≈ dSeriesCReal` orientation (as opposed to §1's `dSeriesCReal ≈ Rhalf`),
obtained by swapping the two witnesses in `fdDeriv_uniqueC`.  This is the orientation
that `JTPIdentity.DiffJTP` / the `K_t ≥ 0` capstone consume when they need the
manifestly-nonneg `Rhalf` on the right. -/
theorem interchangeViaEngine' {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal)
    (fk : Nat → Q' → Q') (dk : Nat → Q')
    (Dk : ∀ k, TsumDeriv.FDDerivData (fun t => fk k t) (dk k) x)
    (C  : FiniteProductFDDeriv.MulCombinator)
    (Hpt : ThetaProdDprodClose.PtwiseProdData F fk)
    (Huni : ThetaProdDprodClose.UniformProdModulus C fk dk Dk)
    (Hdconv : ThetaSeriesFDDeriv.UnifDerivConvC
                (fun M t => FiniteProductFDDeriv.prodDeriv fk dk t M)
                (JTPIdentity.Rhalf ha0 ha1 hx hx1) x)
    (Hser : ThetaSeriesFDDeriv.ThetaSeriesC1Inputs ha0 ha1 hx hx1 F) :
    CReal.Equiv (JTPIdentity.Rhalf ha0 ha1 hx hx1)
                (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) :=
  CReal.Equiv.symm
    (interchangeViaEngine ha0 ha1 hx hx1 F fk dk Dk C Hpt Huni Hdconv Hser)

end YMGap.Continuum.InterchangeViaEngine

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.InterchangeViaEngine.interchangeViaEngine
#print axioms YMGap.Continuum.InterchangeViaEngine.interchangeViaEngineOfSplit
#print axioms YMGap.Continuum.InterchangeViaEngine.interchangeViaEngine'
