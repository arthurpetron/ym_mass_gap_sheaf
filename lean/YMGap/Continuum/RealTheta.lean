/-
# The per-`N` REAL theta product-regrouping identity (Wall-2, Route A, route (i))

This module discharges the per-`N` REAL content the named residual
`ThetaParam.RealThetaPerN` carries — WITHOUT introducing any complex `z = e^{iθ}`,
keeping everything over the project's REAL rationals `Q'`.

## What is GENUINELY closed here (new, axiom-clean, fully real)

The repo's theta partial product `ThetaConv.Ppart a x N = ∏_{k<N} gFac a x k` has
each factor

    gFac a x k = (1 − a^{2k+2}) · factor(a^{2k+1}, x)          (`ThetaConv.gFac`)

a PRODUCT of the Euler prefactor `(1 − a^{2k+2})` and the heat-kernel factor
`factor(a^{2k+1}, x) = 1 + 2·a^{2k+1}·x + a^{4k+2}`
(`HeatKernelPos.factor`).  The genuine per-`N` real identity is the trivial
product-REGROUPING

    Ppart a x N  ≈  (∏_{k<N} (1 − a^{2k+2})) · (∏_{k<N} factor(a^{2k+1}, x)),   (REG)

separating the Euler factors from the heat-kernel factors.  This is `(LEIBNIZ)`'s
positivity-free cousin: a pure `Q'.eqv` product-regrouping induction, NO smallness,
NO complex `z`, NO q-series theory.  It is the real diagonal of the two-sided Gauss
product (B1) that `ThetaParam.lean` named but did not supply.

`eulerProd a N = ∏_{k<N}(1 − a^{2k+2})` and `factorProd a x N = ∏_{k<N} factor(…)`
are the two one-sided real products; `prodRegroup a x N = eulerProd · factorProd`
is the regrouped partial.  `Ppart_eqv_prodRegroup` is `(REG)`.

## What this DOES and does NOT buy (AGENTS.md Rule 6 — honest scope)

`(REG)` is exactly the per-`N` `Q'.eqv` identity that `ThetaParam.RealThetaPerN`
abstracts.  Feeding it to `ThetaParam.common_F_of_realThetaPerN` yields the
common-limit `CReal.Equiv` between the product realisation `thetaConvCRealGen`
(whose `approx N = Ppart a x N`) and ANY series-side realisation whose
`approx N = prodRegroup a x N` — i.e. it discharges the UNDIFFERENTIATED
common-`F` identity the Route-A derivative-uniqueness assembly needs as ONE of its
two ingredients.

It does NOT by itself produce `K_t ≥ 0`: the downstream consumer
`DiffProduct.C1UniqInputsCRealDeriv` needs two `TsumDeriv.FDDerivDataC` — the
finite-difference DERIVATIVE data (modulus + cleared bound) of the common `F` at
`θ`, for the series side and the product side — which is the genuine analytic
content (the C¹ double-limit), NOT supplied by `(REG)`.  `(REG)` closes the
common-`F` identity; the derivative moduli remain the open Wall-2 obligation.  This
module does not fake that — it lands `(REG)` and the common-`F` `CReal.Equiv`
honestly, and names the residual sharply.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (`Quot.sound` only via reused `Nat`/`finSum`
helpers).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.ThetaConv
import YMGap.Continuum.ThetaConvGen
import YMGap.Continuum.ThetaParam

namespace YMGap.Continuum.RealTheta

open YMGap.Constructive
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two one-sided REAL products and their regrouping

`eulerProd a N = ∏_{k<N} (1 − a^{2k+2})` — the Euler prefactors.
`factorProd a x N = ∏_{k<N} factor(a^{2k+1}, x)` — the heat-kernel factors.
Both are plain ascending finite products over the REAL `Q'` factor sequences. -/

/-- The Euler partial product `∏_{k<N} (1 − a^{2k+2})` (the `(1 − uAmp)` factors of
`gFac`). -/
def eulerProd (a : Q') : Nat → Q'
  | 0 => 1
  | N + 1 => eulerProd a N * (1 + (-(ThetaConv.uAmp a N)))

@[simp] theorem eulerProd_succ (a : Q') (N : Nat) :
    eulerProd a (N + 1) = eulerProd a N * (1 + (-(ThetaConv.uAmp a N))) := rfl

/-- The heat-kernel partial product `∏_{k<N} factor(a^{2k+1}, x)` (the `factor`
pieces of `gFac`). -/
def factorProd (a x : Q') : Nat → Q'
  | 0 => 1
  | N + 1 => factorProd a x N * HKPos.factor (HKPos.geoAmp a N) x

@[simp] theorem factorProd_succ (a x : Q') (N : Nat) :
    factorProd a x (N + 1)
      = factorProd a x N * HKPos.factor (HKPos.geoAmp a N) x := rfl

/-- The regrouped partial `prodRegroup a x N = eulerProd a N · factorProd a x N`
(the SERIES-side real realisation's `N`-th approximation). -/
def prodRegroup (a x : Q') (N : Nat) : Q' := eulerProd a N * factorProd a x N

@[simp] theorem prodRegroup_zero (a x : Q') : prodRegroup a x 0 = 1 * 1 := rfl

/-! ## 2. The per-`N` real product-regrouping identity `(REG)`

`Ppart a x N ≈ prodRegroup a x N`, by induction on `N`.  Each step separates the
new `gFac = (1 − uAmp)·factor` into its two pieces and rebrackets — pure `Q'.eqv`
ring algebra (`mul_assoc`, `mul_comm`, congruence), NO positivity, NO smallness. -/

/-- **`(REG)` — the per-`N` REAL theta product-regrouping identity.**
`Ppart a x N ≈ (∏_{k<N}(1 − a^{2k+2}))·(∏_{k<N} factor(a^{2k+1}, x))`.  This is the
real diagonal of the two-sided Gauss product that `ThetaParam.RealThetaPerN`
abstracts; it is a trivial product-regrouping induction (no complex `z`, no
q-series, no positivity). -/
theorem Ppart_eqv_prodRegroup (a x : Q') :
    ∀ N, ThetaConv.Ppart a x N ≈ prodRegroup a x N
  | 0 => by
      -- Ppart 0 = 1 ; prodRegroup 0 = 1·1 ≈ 1
      show (1 : Q') ≈ (1 : Q') * (1 : Q')
      exact Q'.eqv_symm (Q'.mul_one_eqv 1)
  | N + 1 => by
      -- Ppart (N+1) = Ppart N · gFac a x N
      --             = Ppart N · ((1 − uAmp N)·factor N)
      -- target      = (eulerProd N · (1 − uAmp N)) · (factorProd N · factor N)
      rw [ThetaConv.Ppart_succ]
      -- Names (literal terms; the substrate's restricted tactic set has no `set`).
      -- P = Ppart a x N, E = eulerProd a N, Fp = factorProd a x N,
      -- u = 1 + (−uAmp a N), f = factor (geoAmp a N) x.
      -- gFac a x N = u · f (definitional), prodRegroup (N+1) = (E·u)·(Fp·f).
      show ThetaConv.Ppart a x N
            * ((1 + (-(ThetaConv.uAmp a N))) * HKPos.factor (HKPos.geoAmp a N) x)
          ≈ (eulerProd a N * (1 + (-(ThetaConv.uAmp a N))))
            * (factorProd a x N * HKPos.factor (HKPos.geoAmp a N) x)
      -- IH : Ppart N ≈ eulerProd N · factorProd N
      have ih : ThetaConv.Ppart a x N ≈ eulerProd a N * factorProd a x N :=
        Ppart_eqv_prodRegroup a x N
      -- LHS = P·(u·f) ≈ (E·Fp)·(u·f)
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _
          ((1 + (-(ThetaConv.uAmp a N))) * HKPos.factor (HKPos.geoAmp a N) x) ih) ?_
      -- (E·Fp)·(u·f) ≈ E·(Fp·(u·f))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv (eulerProd a N) (factorProd a x N)
          ((1 + (-(ThetaConv.uAmp a N))) * HKPos.factor (HKPos.geoAmp a N) x)) ?_
      -- Fp·(u·f) ≈ u·(Fp·f) : Fp·(u·f) ≈ Fp·(f·u) ≈ (Fp·f)·u ≈ u·(Fp·f)
      have hinner :
          (factorProd a x N
            * ((1 + (-(ThetaConv.uAmp a N))) * HKPos.factor (HKPos.geoAmp a N) x))
          ≈ ((1 + (-(ThetaConv.uAmp a N)))
            * (factorProd a x N * HKPos.factor (HKPos.geoAmp a N) x)) := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (factorProd a x N) _ _
            (Q'.mul_comm_eqv (1 + (-(ThetaConv.uAmp a N)))
              (HKPos.factor (HKPos.geoAmp a N) x))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv (factorProd a x N)
            (HKPos.factor (HKPos.geoAmp a N) x) (1 + (-(ThetaConv.uAmp a N))))) ?_
        exact Q'.mul_comm_eqv
          (factorProd a x N * HKPos.factor (HKPos.geoAmp a N) x)
          (1 + (-(ThetaConv.uAmp a N)))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (eulerProd a N) _ _ hinner) ?_
      -- E·(u·(Fp·f)) ≈ (E·u)·(Fp·f)
      exact Q'.eqv_symm
        (Q'.mul_assoc_eqv (eulerProd a N) (1 + (-(ThetaConv.uAmp a N)))
          (factorProd a x N * HKPos.factor (HKPos.geoAmp a N) x))

/-! ## 3. Discharging `ThetaParam.RealThetaPerN` from `(REG)`

Given the canonical PRODUCT realisation `Pprod` (whose `approx N = Ppart a x N`,
e.g. `ThetaConvGen.thetaConvCRealGen`) and ANY SERIES realisation `Pser` (whose
`approx N = prodRegroup a x N`), `(REG)` supplies the per-`N` real equality the
residual carries.  Then `ThetaParam.common_F_of_realThetaPerN` yields the
common-limit `CReal.Equiv` — the UNDIFFERENTIATED `F = ϑ₃` both finite-difference
families must share. -/

/-- **`RealThetaPerN` discharged by `(REG)`.**  For ANY two `CReal`s `Pser`,
`Pprod` whose `N`-th approximations are exactly the regrouped series partial
`prodRegroup a x N` and the product partial `Ppart a x N` respectively, the per-`N`
real identity `RealThetaPerN Pser Pprod` holds — supplied by the product-regrouping
`(REG)`.  This is the genuine, axiom-clean discharge of the previously-named
residual (no complex `z`, no q-series). -/
def realThetaPerN_of_regroup {a x : Q'} {Pser Pprod : CReal}
    (hser : ∀ N : Nat, Pser.approx N = prodRegroup a x N)
    (hprod : ∀ N : Nat, Pprod.approx N = ThetaConv.Ppart a x N) :
    ThetaParam.RealThetaPerN Pser Pprod where
  perN N := by
    rw [hser N, hprod N]
    -- prodRegroup a x N ≈ Ppart a x N  (symm of REG)
    exact Q'.eqv_symm (Ppart_eqv_prodRegroup a x N)

/-- **The common limit `F = ϑ₃` from `(REG)` (the undifferentiated identity).**
The product realisation `Pprod` (`approx N = Ppart a x N`) and any series
realisation `Pser` (`approx N = prodRegroup a x N`) have the SAME `CReal` limit.
This is the `N → ∞` collapse of `(REG)`, the common-`F` field the Route-A
derivative-uniqueness assembly requires — discharged genuinely over the REAL
substrate, with NO complex `z` and NO q-series theory. -/
theorem common_F_of_regroup {a x : Q'} {Pser Pprod : CReal}
    (hser : ∀ N : Nat, Pser.approx N = prodRegroup a x N)
    (hprod : ∀ N : Nat, Pprod.approx N = ThetaConv.Ppart a x N) :
    CReal.Equiv Pser Pprod :=
  ThetaParam.common_F_of_realThetaPerN (realThetaPerN_of_regroup hser hprod)

/-- **Specialisation to the canonical product `CReal` `thetaConvCRealGen`.**  The
product side is fixed to `ThetaConvGen.thetaConvCRealGen` (the genuine convergent
`ϑ₃` `CReal`, `approx N = Ppart a x N`); ANY series realisation `Pser` with
`approx N = prodRegroup a x N` shares its limit.  Records that the common `F = ϑ₃`
is the actual converged theta product, not an abstract placeholder. -/
theorem common_F_thetaConvCRealGen {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    {Pser : CReal} (hser : ∀ N : Nat, Pser.approx N = prodRegroup a x N) :
    CReal.Equiv Pser (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1) :=
  common_F_of_regroup hser
    (fun N => ThetaConvGen.thetaConvCRealGen_approx ha0 ha1 hx hx1 N)

end YMGap.Continuum.RealTheta

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RealTheta.Ppart_eqv_prodRegroup
#print axioms YMGap.Continuum.RealTheta.realThetaPerN_of_regroup
#print axioms YMGap.Continuum.RealTheta.common_F_of_regroup
#print axioms YMGap.Continuum.RealTheta.common_F_thetaConvCRealGen
