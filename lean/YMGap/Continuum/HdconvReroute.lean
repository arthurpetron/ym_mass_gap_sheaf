/-
# Rerouting `ProdLimitIsRhalf` : cancel the shared `Θ`, isolate the coefficient identity

`HdconvClose` peels `Hdconv` into two residuals:

* `ProdLimitConv` — the convergence/modulus half (`ofQ'(prodDeriv …) → L`), and
* `ProdLimitIsRhalf P` — the pure algebraic CReal equation `Equiv P.L (Rhalf …)`,
  i.e. `(−sin2θ)·Θ·S' ≈ (½)·Θ·S`.

The differentiated-Jacobi product factor `Θ = thetaConvCRealGen` is the **same**
Euler-carrying object on BOTH sides:

    P.L      = Θ · A                    (log-derivative side, `A = (−sin2θ)·S'`)
    Rhalf    = (½) · (Θ · S)            (`= Θ · ((½)·S)` after regrouping)

so the `Θ`-factor is never a separate obligation — it cancels by `CReal.mul`
congruence.  This module performs that cancellation **in Lean** and thereby reduces
`ProdLimitIsRhalf` to the single static **coefficient identity**

    A ≈ (½)·S                                                         (COEFF)

with `Θ` gone and NO limit / modulus remaining.  This is strictly the
differentiated-JTP scalar/grading content (`Σ n a^{n²} sin nθ = (sinθ/2)·ϑ₃·S`),
already stripped of the double-limit interchange (which lives in `ProdLimitConv`).

## What is GENUINELY closed here (new, axiom-clean content)

* **`regroup_half_theta_S` (CLOSED)** — the pure `CReal` ring identity
  `Θ · ((½)·S) ≈ (½)·(Θ·S) = Rhalf`, assembled from `CRealAlg.cmul_assoc`,
  `CRealAlg.cmul_comm`, `CReal.mul_congr_left`.  No limits: this is the algebra
  that moves the `½` past `Θ`.
* **`prodLimitIsRhalf_of_factor_coeff` (CLOSED given the two residuals)** — the
  reduction proper: from the factorisation `P.L ≈ Θ·A` and the coefficient identity
  `A ≈ (½)·S`, conclude `ProdLimitIsRhalf P`.  The `Θ`-cancellation is
  `TrigSignedAdd.mul_congr_right` on the shared `Θ`, then `regroup_half_theta_S`.
* **`hdconv_of_factor_coeff` / `Kt_geRat_zero_of_factor_coeff` (CLOSED given the
  residuals + upstream inputs)** — the reduced residuals fire `Hdconv` and
  `K_t = dSeriesCReal ≥ 0` through `HdconvClose.hdconvOfSplit` /
  `HdconvClose.Kt_geRat_zero_of_split`.

## The honest residual ledger (AGENTS.md Rule 6 / Rule 8)

Two `Type`/`Prop`-level residuals, neither faked:

* `LProductFactor P` — the coefficient CReal `A` together with the product
  factorisation `Equiv P.L (Θ·A)` (the "log-derivative side factors through the
  shared `Θ`" datum; this is what the `ThetaDerivDriverClose` driver
  `g = −sin2θ·Θ·S'` supplies at the CReal level).
* `CoeffHalfIdentity A` — the single static identity `Equiv A ((½)·S)`, `Θ` and the
  `jFac`-denominators already shared/cancelled.  This is `(COEFF)` — the isolated
  differentiated-Jacobi coefficient match, strictly sharper than
  `ProdLimitIsRhalf` / `JTPIdentity.DiffJTP` (which additionally bundle `Θ`, the
  convergence, and the uniformity).  It is the single lemma to target next; it is
  genuinely closeable (a per-`n` coefficient match of `n·a^{n²}·U_{n−1}` against the
  sin·log-derivative expansion, modulo the U-vs-T grading fold) but provably not
  free — it carries exactly `DiffJTP`-minus-interchange.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.  The two residuals are named `Type`/`Prop`-level data,
never `sorry`.
-/

import YMGap.Continuum.HdconvClose
import YMGap.Continuum.JTPIdentity
import YMGap.Continuum.ThetaConvGen
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Constructive.CRealAlg
import YMGap.Constructive.TrigSignedAdd
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.HdconvReroute

open YMGap.Constructive
open YMGap.Continuum

/-! ## 1. The pure `CReal` regrouping: move the `½` past the shared `Θ` -/

/-- **`regroup_half_theta_S` (CLOSED).**  The pure `CReal` ring identity that moves
the `½` past the shared product factor `Θ`:

    Θ · ((½)·S)  ≈  (½)·(Θ·S)  =  Rhalf.

No limits or modulus — three `CRealAlg` regroupings (`cmul_assoc` twice,
`cmul_comm` under `mul_congr_left`).  The RHS is `JTPIdentity.Rhalf` verbatim
(`Rhalf = (½)·(Θ·S)`, `Rproduct = Θ·S`). -/
theorem regroup_half_theta_S {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.Equiv
      (CReal.mul (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1)
        (CReal.mul (CReal.ofQ' HalfPow.half) (HKConvGen.sConvCReal_general ha0 ha1 hx)))
      (JTPIdentity.Rhalf ha0 ha1 hx hx1) :=
  let Θ := ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1
  let halfC := CReal.ofQ' HalfPow.half
  let S := HKConvGen.sConvCReal_general ha0 ha1 hx
  -- Θ·(½·S) ≈ (Θ·½)·S ≈ (½·Θ)·S ≈ ½·(Θ·S) = Rhalf
  ((CRealAlg.cmul_assoc Θ halfC S).symm.trans
    ((CReal.mul_congr_left (CRealAlg.cmul_comm Θ halfC)).trans
      (CRealAlg.cmul_assoc halfC Θ S)))

/-! ## 2. The two named residuals of the reroute -/

/-- **The product-factorisation residual (Type-level).**  A coefficient CReal `A`
together with the factorisation `Equiv P.L (Θ·A)` of the log-derivative side through
the shared differentiated-Jacobi product factor `Θ = thetaConvCRealGen`.  This is
what the `ThetaDerivDriverClose` driver `g = −sin2θ·Θ·S'` supplies at the `CReal`
level (`A = (−sin2θ)·S'`); it carries no modulus. -/
structure LProductFactor {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    {fk : Nat → Q' → Q'} {dk : Nat → Q'}
    (P : HdconvClose.ProdLimitConv fk dk x) : Type where
  /-- The coefficient CReal `A` (`= (−sin2θ)·S'`). -/
  A : CReal
  /-- The factorisation of the log-derivative limit through the shared `Θ`. -/
  factor : CReal.Equiv P.L
    (CReal.mul (ThetaConvGen.thetaConvCRealGen ha0 ha1 hx hx1) A)

/-- **The coefficient identity residual (Prop-level, no modulus) — `(COEFF)`.**  The
single static CReal equation `A ≈ (½)·S` with `Θ` and the `jFac`-denominators
already shared/cancelled.  This is the isolated differentiated-Jacobi coefficient
match — strictly sharper than `ProdLimitIsRhalf` / `JTPIdentity.DiffJTP`.  It is the
single named obligation to target next; NOT discharged here. -/
def CoeffHalfIdentity {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (_hx1 : x ≤ (1 : Q'))
    (A : CReal) : Prop :=
  CReal.Equiv A
    (CReal.mul (CReal.ofQ' HalfPow.half) (HKConvGen.sConvCReal_general ha0 ha1 hx))

/-! ## 3. The reduction: `LProductFactor` + `CoeffHalfIdentity` ⟹ `ProdLimitIsRhalf` -/

/-- **`prodLimitIsRhalf_of_factor_coeff` (CLOSED given the two residuals).**  From the
product factorisation `P.L ≈ Θ·A` (`F.factor`) and the coefficient identity
`A ≈ (½)·S` (`hCoeff`), the shared `Θ` cancels — `mul_congr_right` on `Θ` turns
`Θ·A` into `Θ·((½)·S)`, and `regroup_half_theta_S` moves the `½` out to land on
`Rhalf` — proving `HdconvClose.ProdLimitIsRhalf P`.  The `Θ`-factor is NEVER a
separate obligation: it is shared and cancels here. -/
theorem prodLimitIsRhalf_of_factor_coeff {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    {fk : Nat → Q' → Q'} {dk : Nat → Q'}
    (P : HdconvClose.ProdLimitConv fk dk x)
    (F : LProductFactor ha0 ha1 hx hx1 P)
    (hCoeff : CoeffHalfIdentity ha0 ha1 hx hx1 F.A) :
    HdconvClose.ProdLimitIsRhalf ha0 ha1 hx hx1 P :=
  -- P.L ≈ Θ·A ≈ Θ·(½·S) ≈ Rhalf
  F.factor.trans
    ((TrigSignedAdd.mul_congr_right hCoeff).trans
      (regroup_half_theta_S ha0 ha1 hx hx1))

/-! ## 4. Firing `Hdconv` and `K_t ≥ 0` through the reroute -/

/-- **`Hdconv` from the reroute (CLOSED given the residuals).**  The reduced residuals
`F : LProductFactor` and `hCoeff : CoeffHalfIdentity` assemble — via the reduction
and `HdconvClose.hdconvOfSplit` — into the `UnifDerivConvC (prodDeriv …) Rhalf x`
that `ThetaProdDprodClose.prodC1Inputs` consumes as `Hdconv`. -/
def hdconv_of_factor_coeff {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    {fk : Nat → Q' → Q'} {dk : Nat → Q'}
    (P : HdconvClose.ProdLimitConv fk dk x)
    (F : LProductFactor ha0 ha1 hx hx1 P)
    (hCoeff : CoeffHalfIdentity ha0 ha1 hx hx1 F.A) :
    ThetaSeriesFDDeriv.UnifDerivConvC
      (fun M t => FiniteProductFDDeriv.prodDeriv fk dk t M)
      (JTPIdentity.Rhalf ha0 ha1 hx hx1) x :=
  HdconvClose.hdconvOfSplit ha0 ha1 hx hx1 P
    (prodLimitIsRhalf_of_factor_coeff ha0 ha1 hx hx1 P F hCoeff)

/-- **`K_t ≥ 0` through the reroute (CLOSED given the residuals + upstream inputs).**
With `Hdconv` supplied by `hdconv_of_factor_coeff`, the heat-kernel series
`K_t = dSeriesCReal ≥ 0` fires through the already-closed
`HdconvClose.Kt_geRat_zero_of_split`.  Every non-reroute input is the same upstream
datum that route already carries. -/
theorem Kt_geRat_zero_of_factor_coeff {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F0 : Q' → CReal)
    (fk : Nat → Q' → Q') (dk : Nat → Q')
    (Dk : ∀ k, TsumDeriv.FDDerivData (fun t => fk k t) (dk k) x)
    (C  : FiniteProductFDDeriv.MulCombinator)
    (Hpt : ThetaProdDprodClose.PtwiseProdData F0 fk)
    (Huni : ThetaProdDprodClose.UniformProdModulus C fk dk Dk)
    (P : HdconvClose.ProdLimitConv fk dk x)
    (F : LProductFactor ha0 ha1 hx hx1 P)
    (hCoeff : CoeffHalfIdentity ha0 ha1 hx hx1 F.A)
    (Hser : ThetaSeriesFDDeriv.ThetaSeriesC1Inputs ha0 ha1 hx hx1 F0) :
    ExpPos.geRat (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) 0 :=
  HdconvClose.Kt_geRat_zero_of_split ha0 ha1 hx hx1 F0 fk dk Dk C Hpt Huni P
    (prodLimitIsRhalf_of_factor_coeff ha0 ha1 hx hx1 P F hCoeff) Hser

end YMGap.Continuum.HdconvReroute

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HdconvReroute.regroup_half_theta_S
#print axioms YMGap.Continuum.HdconvReroute.prodLimitIsRhalf_of_factor_coeff
#print axioms YMGap.Continuum.HdconvReroute.hdconv_of_factor_coeff
#print axioms YMGap.Continuum.HdconvReroute.Kt_geRat_zero_of_factor_coeff
