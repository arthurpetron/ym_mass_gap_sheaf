/-
# The Q'→CReal finite-difference-derivative BRIDGE (Wall-2, Route A, CReal layer)

This module supplies the missing structural link between the two halves of the
Wall-2 differentiation engine:

* the **Q'-valued** Bishop C¹-uniform-limit theorem
  `TsumDeriv.fdDeriv_of_unif : C1Inputs f f' F g θ → FDDerivData F (g θ) θ`
  (which the per-factor moduli of `JTPInstance.perFactorModuli` feed), and
* the **CReal-valued** derivative-uniqueness engine
  `TsumDeriv.fdDeriv_uniqueC : FDDerivDataC F d₁ θ → FDDerivDataC F d₂ θ →
  CReal.Equiv d₁ d₂`
  (which closes `DiffProduct.C1UniqInputsCRealDeriv`, hence `DiffJTP`, hence
  `K_t ≥ 0`).

The engine produces a `FDDerivData` (a `Q'`-valued finite-difference derivative);
the uniqueness closure consumes a `FDDerivDataC` (a `CReal`-valued one).  These two
types were never connected.  This module closes that gap.

## What is GENUINELY closed here (new, axiom-clean, fully reusable content)

* **`ofQ'FDDerivDataC`** — THE BRIDGE.  Any `Q'`-valued finite-difference
  derivative `FDDerivData f d θ` lifts to a `CReal`-valued
  `FDDerivDataC (fun t => ofQ' (f t)) (ofQ' d) θ`, with the SAME modulus.  This is
  genuine: `fdRemC` is index-wise (`TsumDeriv.fdRemC_approx`), so the `CReal`
  remainder of the LIFTED data is, at every approximation index, exactly the `Q'`
  remainder `fdRem f d θ h`; the `CReal.leRat` bound is then the `Q'` bound
  `D.bound` verbatim (via `CReal.leRat_of_eventually`, the sequence being constant
  in the index).

* **`fdDerivDataC_of_c1`** — the composite engine: `C1Inputs → FDDerivDataC` for a
  `Q'`-valued limit `F`, obtained by `ofQ'FDDerivDataC ∘ fdDeriv_of_unif`.  This is
  the CReal-level C¹-limit theorem for LIFTED (rational) function families — the
  Bishop engine now landing directly in the uniqueness-engine's input type.

* **`linFDDerivData`** — a genuine, non-trivial `Q'` witness: the linear function
  `t ↦ b·t` has finite-difference derivative `b` at every `θ` (the cleared
  remainder is exactly `0`).  Non-vacuous (the derivative value `b` is arbitrary).

* **`linProductDerivativeLimit`** — the WHOLE closure pipeline fired end-to-end on a
  concrete pair: `ofQ'FDDerivDataC (linFDDerivData …)` is fed (twice) into
  `DiffProduct.C1UniqInputsCRealDeriv`, and
  `productDerivativeLimit_of_uniq_creal_deriv` produces a genuine
  `ProductDerivativeLimit`.  This certifies the `C1UniqInputsCRealDeriv → DiffJTP`
  reduction is NOT vacuous: the interface is inhabited and the uniqueness engine
  genuinely runs on lifted data.

## The honest residual (AGENTS.md Rule 6)

`ofQ'FDDerivDataC` lifts `Q'`-valued derivatives.  The heat-kernel target `F = ϑ₃`
is a genuine `CReal` LIMIT (the `N → ∞` limit of the product truncations, delivered
as a common `F` by `RealTheta.common_F_of_regroup` / `ThetaLimit`), NOT of the form
`ofQ' ∘ (Q' function)`.  So `fdDerivDataC_of_c1` produces a `FDDerivDataC` for each
FINITE truncation `f_M = ofQ' ∘ (rational truncation)`, but NOT for the limit `ϑ₃`.
The sharp remaining obligation is therefore ONE named analytic engine: a
**CReal-valued** C¹-uniform-limit theorem — the uniform limit (in `M`) of the lifted
truncation derivatives `ofQ'FDDerivDataC (fdDeriv_of_unif …)` is a `FDDerivDataC` of
the CReal limit `ϑ₃` — equivalently the two theta `FDDerivDataC` (series side +
product side) of the common `F` that `DiffProduct.C1UniqInputsCRealDeriv` demands.
This module does NOT fake that limit interchange; it lands the bridge and the
finite-level composite engine honestly, and names the residual sharply.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` (`Quot.sound` only via reused
`Nat`/`Int`/`omega` helpers).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.DiffProduct
import YMGap.Continuum.JTPIdentity
import YMGap.Constructive.Reals
import YMGap.Constructive.CRealLe
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.RationalsMul

namespace YMGap.Continuum.ThetaFDDerivAssembly

open YMGap.Constructive
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. THE BRIDGE: `FDDerivData` (over `Q'`) ⟶ `FDDerivDataC` (over `CReal`)

`fdRemC` is index-wise (`TsumDeriv.fdRemC_approx`): for `F = ofQ' ∘ f` and value
`ofQ' d`, every approximation of the cleared `CReal` remainder equals the `Q'`
remainder `fdRem f d θ h`.  The `CReal.leRat` bound then reduces, via
`CReal.leRat_of_eventually` on a sequence that is CONSTANT in the index, to the
`Q'` bound `D.bound`. -/

/-- **THE BRIDGE.**  A `Q'`-valued finite-difference derivative lifts to a
`CReal`-valued one over the embedded function `fun t => ofQ' (f t)`, with value
`ofQ' d` and the SAME modulus `δ`.  Genuine and axiom-clean: the lifted `CReal`
remainder is, index-wise, exactly the `Q'` remainder, so the `leRat` bound IS the
`Q'` bound. -/
def ofQ'FDDerivDataC {f : Q' → Q'} {d θ : Q'}
    (D : TsumDeriv.FDDerivData f d θ) :
    TsumDeriv.FDDerivDataC (fun t => CReal.ofQ' (f t)) (CReal.ofQ' d) θ where
  δ := D.δ
  δ_pos := D.δ_pos
  bound := by
    intro ε hε h hpos hle
    -- leRat (abs (fdRemC (ofQ'∘f) (ofQ' d) θ h)) (ε·|h|) via a CONSTANT-in-index bound.
    apply CReal.leRat_of_eventually
    refine ⟨0, fun n _ => ?_⟩
    -- (abs (fdRemC …)).approx n = Q'.abs ((fdRemC …).approx n)
    --                           = Q'.abs (fdRem f d θ h)   [fdRemC is index-wise]
    show Q'.abs ((TsumDeriv.fdRemC (fun t => CReal.ofQ' (f t)) (CReal.ofQ' d) θ h).approx n)
        ≤ ε * Q'.abs h
    rw [TsumDeriv.fdRemC_approx]
    -- goal is now `Q'.abs (fdRem f d θ h) ≤ ε·|h|` (defeq: ofQ'-approx is `rfl`)
    exact D.bound ε hε h hpos hle

/-- **The composite CReal-level C¹-limit engine for LIFTED families.**  From the
`Q'`-valued Bishop inputs `C1Inputs f f' F g θ`, the LIFTED limit `fun t => ofQ' (F t)`
has `CReal`-valued finite-difference derivative `ofQ' (g θ)` at `θ`, with explicit
modulus.  This is `ofQ'FDDerivDataC ∘ fdDeriv_of_unif`: the genuine analytic engine
(the part that commutes `d/dθ` with the limit) now landing directly in the
uniqueness-engine's input type `FDDerivDataC`. -/
def fdDerivDataC_of_c1 {f f' : Nat → Q' → Q'} {F g : Q' → Q'} {θ : Q'}
    (H : TsumDeriv.C1Inputs f f' F g θ) :
    TsumDeriv.FDDerivDataC (fun t => CReal.ofQ' (F t)) (CReal.ofQ' (g θ)) θ :=
  ofQ'FDDerivDataC (TsumDeriv.fdDeriv_of_unif H)

/-! ## 2. A genuine, non-trivial `Q'` witness: the linear finite-difference derivative

The linear function `t ↦ b·t` has finite-difference derivative `b` at every `θ`:
the cleared remainder `fdRem (·b·) b θ h = b·(θ+h) − b·θ − b·h` is exactly `0`
(pure `Q'` ring cancellation).  Non-vacuous — `b` is arbitrary. -/

/-- **The linear finite-difference derivative** `FDDerivData (fun t => b·t) b θ`.
The cleared remainder is exactly `0`, so the bound holds for ANY modulus (`δ := 1`).
A genuine, non-trivial witness (arbitrary derivative value `b`). -/
def linFDDerivData (b θ : Q') : TsumDeriv.FDDerivData (fun t => b * t) b θ where
  δ := fun _ => 1
  δ_pos := fun _ _ => CReal.pos_of_num_pos (by decide)
  bound := by
    intro ε hε h _ _
    -- fdRem (fun t => b·t) b θ h = ((b·(θ+h)) + (−(b·θ))) + (−(b·h))  ≈  0
    show Q'.abs (((b * (θ + h)) + (-(b * θ))) + (-(b * h))) ≤ ε * Q'.abs h
    -- (b·(θ+h)) + (−(b·θ)) ≈ b·h   [distribute then cancel b·θ]
    have hcancel : ((b * (θ + h)) + (-(b * θ))) ≈ (b * h) := by
      -- b·(θ+h) ≈ b·θ + b·h
      have hdist : (b * (θ + h)) ≈ ((b * θ) + (b * h)) := Q'.mul_add_eqv b θ h
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (-(b * θ)) hdist) ?_
      -- ((b·θ) + (b·h)) + (−(b·θ)) ≈ b·h
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (-(b * θ)) (Q'.add_comm_eqv (b * θ) (b * h))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (b * h) (b * θ) (-(b * θ))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (b * h) _ _ (Q'.add_neg_self_eqv (b * θ))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' (b * h))
    -- remainder ≈ b·h + (−(b·h)) ≈ 0
    have hzero : (((b * (θ + h)) + (-(b * θ))) + (-(b * h))) ≈ (0 : Q') := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (-(b * h)) hcancel) ?_
      exact Q'.add_neg_self_eqv (b * h)
    -- |remainder| ≈ |0| = 0 ≤ ε·|h|
    have habs0 : Q'.abs (((b * (θ + h)) + (-(b * θ))) + (-(b * h))) ≈ (0 : Q') := by
      refine Q'.eqv_trans _ _ _
        (YMGap.Continuum.TsumDeriv.Q'.abs_eqv_congr hzero) ?_
      exact YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg (Q'.le_refl' 0)
    have hnn : (0 : Q') ≤ ε * Q'.abs h :=
      Q'.mul_nonneg _ _ (Q'.le_of_lt hε) (Q'.abs_nonneg h)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv habs0) hnn

/-! ## 3. NON-VACUITY: the whole closure pipeline fires end-to-end

Feeding the lifted linear derivative (twice) into
`DiffProduct.C1UniqInputsCRealDeriv` and firing
`productDerivativeLimit_of_uniq_creal_deriv` produces a genuine
`ProductDerivativeLimit`.  This certifies the reduction
`C1UniqInputsCRealDeriv → DiffJTP` is inhabited and the CReal uniqueness engine
`fdDeriv_uniqueC` genuinely runs on lifted data (not a vacuous obligation). -/

/-- The concrete `C1UniqInputsCRealDeriv` for the lifted linear function
`fun t => ofQ' (b·t)`: both the "series" and "product" sides are the SAME lifted
linear derivative (value `ofQ' b`).  Inhabits the closure interface with genuine,
non-trivial `FDDerivDataC` data. -/
def linUniqInputs (b θ : Q') :
    DiffProduct.C1UniqInputsCRealDeriv (CReal.ofQ' b) (CReal.ofQ' b) where
  F := fun t => CReal.ofQ' (b * t)
  θ := θ
  Dprod := ofQ'FDDerivDataC (linFDDerivData b θ)
  Dser := ofQ'FDDerivDataC (linFDDerivData b θ)

/-- **The full closure pipeline, fired end-to-end.**  The CReal derivative-uniqueness
engine `fdDeriv_uniqueC` (through
`DiffProduct.productDerivativeLimit_of_uniq_creal_deriv`) genuinely produces a
`ProductDerivativeLimit (ofQ' b) (ofQ' b)` from the lifted linear finite-difference
derivatives.  Certifies the `C1UniqInputsCRealDeriv` reduction is non-vacuous. -/
theorem linProductDerivativeLimit (b θ : Q') :
    DiffProduct.ProductDerivativeLimit (CReal.ofQ' b) (CReal.ofQ' b) :=
  DiffProduct.productDerivativeLimit_of_uniq_creal_deriv (linUniqInputs b θ)

/-! ## 4. The sharp theta residual, named through the bridge

The heat-kernel obligation, at the sharpest (CReal-uniqueness) layer, is exactly a
`DiffProduct.C1UniqInputsCRealDeriv (dSeriesCReal) (Rhalf)` — two `FDDerivDataC` of
one common `F = ϑ₃` at `θ`.  We name it and re-expose the closure to `K_t ≥ 0`, and
record honestly what the bridge above does and does NOT reduce it to. -/

/-- **The sharp CReal-derivative theta residual** (named `Type`, NOT discharged):
the two common-`F` `CReal` finite-difference derivatives that
`DiffProduct.C1UniqInputsCRealDeriv` demands for the heat-kernel series
`dSeriesCReal` and the halved product `Rhalf`.  Supplying it closes `DiffJTP` (hence
`K_t ≥ 0`).  The bridge `ofQ'FDDerivDataC` reduces EACH finite-truncation derivative
to the `Q'` Bishop engine; the residual is the `M → ∞` CReal limit interchange that
turns those lifted truncation derivatives into `FDDerivDataC` of the LIMIT `ϑ₃`. -/
def ThetaCRealDerivResidual {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    Type :=
  DiffProduct.C1UniqInputsCRealDeriv
    (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1)
    (JTPIdentity.Rhalf ha0 ha1 hx hx1)

/-- **`ThetaCRealDerivResidual → K_t ≥ 0`.**  Given the two common-`F` `CReal`
finite-difference derivatives, the heat-kernel series `K_t = dSeriesCReal ≥ 0`, via
the already-proven `JTPIdentity.Kt_geRat_zero_of_uniq_creal_deriv` (whose positivity
flows through the genuine `TsumDeriv.fdDeriv_uniqueC` engine).  The sole open input
is the residual. -/
theorem Kt_geRat_zero_of_theta_creal_deriv {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (H : ThetaCRealDerivResidual ha0 ha1 hx hx1) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  JTPIdentity.Kt_geRat_zero_of_uniq_creal_deriv ha0 ha1 hx hx1 H

end YMGap.Continuum.ThetaFDDerivAssembly

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing declaration reports `[propext]` or `[propext, Quot.sound]`
(`Quot.sound` only via reused `Nat`/`Int`/`omega`/`finSum` helpers).  No
`Classical.*`, no `native_decide`, no `sorry`.  `ThetaCRealDerivResidual` is a named
`Type`-obligation (the sole outstanding analytic input), NOT a `sorry`. -/

#print axioms YMGap.Continuum.ThetaFDDerivAssembly.ofQ'FDDerivDataC
#print axioms YMGap.Continuum.ThetaFDDerivAssembly.fdDerivDataC_of_c1
#print axioms YMGap.Continuum.ThetaFDDerivAssembly.linFDDerivData
#print axioms YMGap.Continuum.ThetaFDDerivAssembly.linUniqInputs
#print axioms YMGap.Continuum.ThetaFDDerivAssembly.linProductDerivativeLimit
#print axioms YMGap.Continuum.ThetaFDDerivAssembly.Kt_geRat_zero_of_theta_creal_deriv
