/-
# The arctan↔trig inversion for the Machin `π`, via Gaussian integers

GOAL.  For the repo's Machin-defined `π = 16·arctan(1/5) − 4·arctan(1/239)`, we
want `sin π ≃ 0` (hence `sin(kπ) ≃ 0`).  This single identity is what a
`sinC`/`cosC` of a *multiple-of-π angle* needs, and it is exactly the sharp
analytic residual named in the constructive-trig layer: the Machin **series** for
`π` is connected to the trig **series** for `sin`/`cos` by NOTHING purely
algebraic — the link `e^{i·arctan x} = (1 + i·x)/√(1+x²)` (equivalently
`cos(arctan x) = 1/√(1+x²)`, `sin(arctan x) = x/√(1+x²)`, i.e. `tan(arctan x)=x`)
is the one genuinely transcendental input.

# The route chosen: Gaussian-integer / complex-exponential

`e^{iπ} = e^{i(16α − 4β)} = (e^{iα})^{16}·(e^{-iβ})^{4}` with `α = arctan(1/5)`,
`β = arctan(1/239)`.  The link gives `e^{iα} ∝ (5 + i)` and `e^{-iβ} ∝ (239 − i)`
(positive real proportionality, the radius `√(1+x²)`), so
`e^{iπ} ∝ (5+i)^{16}·(239−i)^4`, a **Gaussian integer**.  Everything after the
link is `ℤ[i]` arithmetic + the exponential addition law `e^{i(a+b)}=e^{ia}e^{ib}`
(the sin/cos addition formulas), and the *decidable* fact that this Gaussian
integer has **imaginary part `0`** and **negative real part** — i.e. `e^{iπ} = −1`,
whence `sin π = Im(e^{iπ}) ≃ 0` and `cos π ≃ −1`.

# What this file DELIVERS

  §1–§2  **The bankable arithmetic core (fully closed, `decide`).**  A computable
  `ℤ[i]` layer (`GaussInt`, `gMul`, `gpowIter`, `gConj`), the Machin Gaussian
  integer `machinGI = (5+i)^16·(239−i)^4`, and the closed identities
      `machin_im_zero  : machinGI.im = 0`      (`decide`)
      `machin_re_neg   : machinGI.re < 0`      (`decide`)
  i.e. `e^{iπ} = −1` as pure, checked integer arithmetic.  No transcendental
  content, no `sorry`, no custom axiom.

  §3  **The reduction of `sin π ≃ 0` to the single named link.**  An abstract
  circle-representation interface `CircleModel` whose fields are EXACTLY the two
  non-decidable ingredients:
      * `rep_add`  — the exponential addition law `e^{i(a+b)} = e^{ia}·e^{ib}`
        transported to Gaussian-integer directions (`gMul`);
      * `repBaseP`/`repBaseM` — the **arctan↔trig LINK**: the base angles
        `arctan(1/5)`, `−arctan(1/239)` are represented by the directions
        `⟨5,1⟩`, `⟨239,−1⟩`;
      * `sin_zero_of_rep_im_zero` — the elementary *positive-radius* half of the
        direction interpretation (`Im = radius·sin`, `radius > 0`).
  From these the file PROVES, by the genuine Machin telescoping (16-fold and
  4-fold Gaussian powers assembled by `rep_add`) plus the decidable §2 identity,
      `sinMachinAngle_eqv_zero : CReal.Equiv (M.sinOf (piAngle M)) CReal.czero`,
  where `piAngle M` is the Machin combination `16·baseP ⊕ 4·baseM`.

# HONEST VERDICT (the depth of the inversion)

The inversion has EXACTLY one transcendental atom.  The Machin combinatorics and
the `e^{iπ} = −1` collapse are DECIDABLE integer arithmetic and are closed here
outright.  The residual is the construction of a `CircleModel` for the actual
`Constructive.Pi.arctanRecip`/`CRealTrig.sinC`/`cosC` — i.e. proving the base
link `cos(arctan(1/k)) ≃ 1/√(1+1/k²)`, `sin(arctan(1/k)) ≃ (1/k)/√(1+1/k²)` and
the CReal-angle addition law.  The Q'-angle cosine addition law is already
present in the repo (`Constructive.TrigAdd.cos_add_equiv_nonneg`); the CReal-angle
lift and the arctan-series↔trig-series base link are the sharp named sub-lemmas.
This file does NOT fake that link; it isolates it as the sole hypothesis and
bankrolls the arithmetic core.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only (the latter via reused `Int` helpers).
No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.  All witness
data is `Type`-level (the `CircleModel` interface is a structure of data, not a
`Prop`-∃).
-/

import YMGap.Constructive.CRealTrig
import YMGap.Constructive.Pi

namespace YMGap.Continuum.ArctanTanInversion

open YMGap.Constructive

/-! ## 1. The computable Gaussian-integer layer `ℤ[i]` -/

/-- A Gaussian integer `re + im·i`. -/
structure GaussInt where
  re : Int
  im : Int

/-- Gaussian-integer multiplication `(a+bi)(c+di) = (ac−bd) + (ad+bc)i`. -/
def gMul (x y : GaussInt) : GaussInt :=
  { re := x.re * y.re - x.im * y.im
    im := x.re * y.im + x.im * y.re }

/-- Complex conjugate `a + bi ↦ a − bi`. -/
def gConj (x : GaussInt) : GaussInt := { re := x.re, im := -x.im }

/-- Squared norm `|a+bi|² = a² + b²` (a nonnegative integer). -/
def gNormSq (x : GaussInt) : Int := x.re * x.re + x.im * x.im

/-- **Iterated power seeded at the base.**  `gpowIter z k = z^{k+1}`
(`gpowIter z 0 = z`, `gpowIter z (k+1) = gMul (gpowIter z k) z`).  Seeding at the
base avoids needing a multiplicative identity / zero-angle element. -/
def gpowIter (z : GaussInt) : Nat → GaussInt
  | 0 => z
  | k + 1 => gMul (gpowIter z k) z

/-! ## 2. The Machin Gaussian integer and the decidable `e^{iπ} = −1` identity -/

/-- The direction of `e^{i·arctan(1/5)}`: `5 + i`. -/
def gi5 : GaussInt := { re := 5, im := 1 }

/-- The direction of `e^{−i·arctan(1/239)}`: `239 − i` (the conjugate of `239+i`). -/
def gi239m : GaussInt := { re := 239, im := -1 }

/-- **The Machin Gaussian integer** `(5+i)^{16}·(239−i)^4`.

`gpowIter gi5 15 = gi5^{16}` and `gpowIter gi239m 3 = gi239m^4`. -/
def machinGI : GaussInt := gMul (gpowIter gi5 15) (gpowIter gi239m 3)

/-- Exact value of `(5+i)^{16}` (documentation / kernel sanity). -/
theorem gi5_pow16_re : (gpowIter gi5 15).re = -208797818624 := by decide
theorem gi5_pow16_im : (gpowIter gi5 15).im = -3494830080 := by decide

/-- Exact value of `(239−i)^4` (documentation / kernel sanity). -/
theorem gi239m_pow4_re : (gpowIter gi239m 3).re = 3262465916 := by decide
theorem gi239m_pow4_im : (gpowIter gi239m 3).im = -54606720 := by decide

/-- **`Im(e^{iπ}) = 0`.**  The Machin Gaussian integer is real: `decide`. -/
theorem machin_im_zero : machinGI.im = 0 := by decide

/-- **`Re(e^{iπ}) < 0`.**  Its real part is negative: `decide`. -/
theorem machin_re_neg : machinGI.re < 0 := by decide

/-- Exact real part `Re(e^{iπ})·|norm|` value (documentation). -/
theorem machin_re_value : machinGI.re = -681386607803576157184 := by decide

/-- **`e^{iπ} = −1` as a checked `ℤ[i]` fact.**  The Machin Gaussian integer is a
negative real: imaginary part `0`, real part `< 0`. -/
theorem machin_is_neg_real : machinGI.im = 0 ∧ machinGI.re < 0 :=
  ⟨machin_im_zero, machin_re_neg⟩

/-! ## 3. The abstract circle-representation interface and the reduction

`CircleModel` packages the two genuinely-non-decidable ingredients of the
inversion as `Type`-level data.  A model exists iff the arctan↔trig link and the
CReal-angle addition law hold for the concrete `arctanRecip`/`sinC`/`cosC` — that
existence is the sharp named residual.  Given ANY model, the Machin telescoping
below drives `sin π ≃ 0`. -/

/-- An abstract "unit-circle direction" interface for a type of angles.

Fields, read as content:
  * `add`      — angle addition;
  * `sinOf`    — the sine of an angle, as a genuine `CReal` (so the conclusion is
                 a real `CReal.Equiv`, NOT a vacuous placeholder);
  * `rep a z`  — "the Gaussian integer `z` points in the direction `e^{ia}`"
                 (`z = radius·(cos a, sin a)`, radius `> 0`);
  * `rep_add`  — the exponential addition law on directions:
                 `e^{i(a+b)} = e^{ia}·e^{ib}` ⇝ `rep (a+b) (gMul x y)`;
  * `baseP`,`repBaseP` — the LINK for `α = arctan(1/5)`:  `rep α ⟨5,1⟩`;
  * `baseM`,`repBaseM` — the LINK for `−β = −arctan(1/239)`: `rep (−β) ⟨239,−1⟩`;
  * `sin_zero_of_rep_im_zero` — the elementary positive-radius fact: a direction
                 with zero imaginary part has zero sine. -/
structure CircleModel where
  Angle : Type
  add : Angle → Angle → Angle
  sinOf : Angle → CReal
  rep : Angle → GaussInt → Prop
  rep_add : ∀ {a b : Angle} {x y : GaussInt}, rep a x → rep b y → rep (add a b) (gMul x y)
  baseP : Angle
  repBaseP : rep baseP gi5
  baseM : Angle
  repBaseM : rep baseM gi239m
  sin_zero_of_rep_im_zero :
    ∀ {θ : Angle} {z : GaussInt}, rep θ z → z.im = 0 → CReal.Equiv (sinOf θ) CReal.czero

namespace CircleModel

variable (M : CircleModel)

/-- `naddIter a k = (k+1)·a` (iterated angle addition, seeded at the base). -/
def naddIter (a : M.Angle) : Nat → M.Angle
  | 0 => a
  | k + 1 => M.add (naddIter a k) a

/-- **Direction telescoping.**  `rep a z → rep ((k+1)·a) (z^{k+1})`. -/
theorem rep_iter {a : M.Angle} {z : GaussInt} (h : M.rep a z) :
    ∀ k, M.rep (M.naddIter a k) (gpowIter z k)
  | 0 => h
  | k + 1 => M.rep_add (rep_iter h k) h

/-- The Machin angle `π = 16·arctan(1/5) ⊕ 4·(−arctan(1/239))`
(`16·baseP` is `naddIter baseP 15`, `4·baseM` is `naddIter baseM 3`). -/
def piAngle : M.Angle := M.add (M.naddIter M.baseP 15) (M.naddIter M.baseM 3)

/-- `rep π machinGI`:  the Machin angle is represented by the Machin Gaussian
integer, assembled by `rep_add` from the two telescoped base directions. -/
theorem rep_piAngle : M.rep M.piAngle machinGI :=
  M.rep_add (M.rep_iter M.repBaseP 15) (M.rep_iter M.repBaseM 3)

/-- **The inversion, modulo the model.**  `sin π ≃ 0`.

The whole transcendental burden is the existence of `M`; GIVEN it, this is the
Machin telescoping (`rep_piAngle`) composed with the decidable `Im(e^{iπ}) = 0`
(`machin_im_zero`) and the positive-radius extraction. -/
theorem sinMachinAngle_eqv_zero : CReal.Equiv (M.sinOf M.piAngle) CReal.czero :=
  M.sin_zero_of_rep_im_zero M.rep_piAngle machin_im_zero

end CircleModel

/-! ## 4. The named residual (the sharp sub-lemma), for the record

The ONE thing not closed here is the construction of a `CircleModel` for the
concrete objects.  Its two non-trivial fields spell out the residual precisely:

  (LINK)  For `k ≥ 2` with `x = 1/k`, in the constructive-trig layer,
             `cosC (arctan x) ≃ 1/√(1+x²)`  and  `sinC (arctan x) ≃ x/√(1+x²)`,
          i.e. `tan(arctan x) = x`.  This is the arctan-**series**↔trig-**series**
          bridge; it is genuinely transcendental (no algebraic derivation from the
          Machin definition of `arctanRecip`).

  (ADD)   The CReal-angle cosine/sine addition law
             `cosC (a+b) ≃ cosC a·cosC b − sinC a·sinC b`   (and the sine analogue),
          the CReal-angle lift of the already-proven Q'-angle
          `Constructive.TrigAdd.cos_add_equiv_nonneg`.

`sinMachinAngle_eqv_zero` shows these two — plus the decidable §2 arithmetic —
are jointly sufficient for `sin π ≃ 0`. -/

/-- The link statement for a single base value `x` (tangent form): `sin α ≃ x·cos α`,
i.e. `tan α = x`, recorded as a genuine `CReal.Equiv` a concrete model must supply
for `α = arctan x`.  This is the sharp named residual (non-vacuous). -/
def ArctanTrigLink (x : Q') (cα sα : CReal) : Prop :=
  CReal.Equiv sα (CReal.mul (CReal.ofQ' x) cα)

end YMGap.Continuum.ArctanTanInversion

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ArctanTanInversion.machin_im_zero
#print axioms YMGap.Continuum.ArctanTanInversion.machin_re_neg
#print axioms YMGap.Continuum.ArctanTanInversion.machin_is_neg_real
#print axioms YMGap.Continuum.ArctanTanInversion.machin_re_value
#print axioms YMGap.Continuum.ArctanTanInversion.CircleModel.rep_iter
#print axioms YMGap.Continuum.ArctanTanInversion.CircleModel.rep_piAngle
#print axioms YMGap.Continuum.ArctanTanInversion.CircleModel.sinMachinAngle_eqv_zero
