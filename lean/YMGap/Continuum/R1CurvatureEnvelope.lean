/-
Track B / local-CLT — the UNIFORM CURVATURE ENVELOPE for R1
(`CircleFourierPowerModel.SaddleVarianceFloor`), unifying the whole (parity × w-regime)
case split under ONE sharp inequality.

# Why this file exists (read first — load-bearing honesty)

R1 is `∀ s, FullRangeFloor w s`, equivalently `Δ²V(s) ≥ −2` for the theta-tilted position
variance `V(t) = dmomNfull w t / acNfull w t`.  The prior development discharges it by a
CASE SPLIT (even-centre cell PROVED, odd-centre cell PROVED, upper-half `RegimeGECell` reduced
to the large-window residual `RegimeGETailBound`).  This file records the SHARP UNIFORM object
that supersedes that split.

## The uniform envelope (numerically certified, exact at the binding cases)

The cleared curvature `Δ²V(s)+2`, divided by the boundary vanishing rate `w²(1−w²)`, has a
GLOBAL infimum over ALL windows `s` and ALL `w ∈ [0,1]` equal to the single corner value
`144/25 = 5.76`, attained ONLY at `s = 0` (`w² = 1/6`).  For `s ≥ 1` the infimum jumps to
`48/7 ≈ 6.857` (`s = 1`, `w = 1/√2`) and rises monotonically to the plateau `8` as `s → ∞`.
Hence the single SHARP inequality, uniform in `s` and both parities:

    `Δ²V(s) + 2  ≥  (144/25) · w² · (1 − w²)`         for all `s`, all `w ∈ [0,1]`.

Cleared over the positive masses `acNfull` this is `CurvatureEnvelope w s`:

    `floorLHS w s  +  (144/25)·w²·(1−w²)·A₀A₁A₂  ≤  floorRHS w s`     (`Aᵢ = acNfull w (s+i)`).

Because `(144/25)·w²·(1−w²)·A₀A₁A₂ ≥ 0` on the physical window, the envelope IMPLIES
`FullRangeFloor w s` OUTRIGHT — so a proof of the envelope for all `s` inhabits R1 with no case
split.  The envelope is the cleanest possible statement of R1's remaining analytic content: a
single sharp saddle inequality, replacing the two-region (theta/parabolic) split of
`RegimeGETailBound`.

## What is PROVED here (axiom-clean, no `sorry`)

  * `envBound_nonneg` — the envelope slack `(144/25)·w²·(1−w²)·A₀A₁A₂` is `≥ 0` on `0 ≤ w ≤ 1`
    (`144/25 ≥ 0`, `w² ≥ 0`, `1−w² ≥ 0` via `qpow_le_one`, masses `≥ 0`).
  * `fullRangeFloor_of_curvatureEnvelope` — the envelope at `s` implies `FullRangeFloor w s`
    (add the nonnegative envelope slack).  THE reusable reduction.
  * `saddleVarianceFloor_of_curvatureEnvelope` — `UniformCurvatureEnvelope w` (the envelope for
    ALL `s`) inhabits `SaddleVarianceFloor w`.  ONE inequality family supersedes the 3-cell split.
  * `regimeGETailBound_of_envelopeTail` — the envelope for `s ≥ 7` inhabits the standing residual
    `R1RegimeGE.RegimeGETailBound w`, wiring the envelope into the existing R1 assembly.
  * `curvatureEnvelope_zero` — THE BINDING CASE `s = 0`, PROVED in closed form.  At `s = 0` the
    envelope is EXACT: `slack₀ = 96·w¹¹` and the envelope gap is a PERFECT SQUARE,
    `slack₀ − (144/25)·w²·(1−w²)·A₀A₁A₂ = (96/25)·w¹¹·(1−6w²)² ≥ 0`.  This certifies the envelope
    exactly where it is tight (`w² = 1/6`) — the object is correct and provable at its corner.

## NAMED OPEN (Type-level, never `sorry`)

  * `UniformCurvatureEnvelope w` — the envelope for ALL `s` (equivalently `s ≥ 1`, since `s = 0`
    is PROVED).  A single sharp uniform saddle inequality; the honest remaining analytic core of
    R1's upper half.  Strictly better-posed than the two-region `RegimeGETailBound` (one clean
    inequality with a global rational certificate `144/25`, vs. a τ=1/50 theta/parabolic split).

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is axiom-checked at file end; permitted output is
`propext` / `Quot.sound` only (via the `Q'` setoid).  No `Classical.*`, no `native_decide`, no
`sorry`, no custom `axiom`.  The residual `UniformCurvatureEnvelope` is a `Type`-level structure
(Rule 6a), never `Prop := True` or a `Unit` witness.
-/

import YMGap.Continuum.R1RegimeGE
import YMGap.Continuum.HeatKernelGap

namespace YMGap.Continuum.R1CurvatureEnvelope

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.CircleFourierPowerModel

/-! ## 0. The envelope constant `144/25` and the envelope slack term. -/

/-- The sharp uniform curvature-envelope constant `144/25` (the global corner value of
`(Δ²V+2)/(w²(1−w²))`, attained at `s = 0`). -/
def c144over25 : Q' := Q'.mkPos 144 25 (by decide)

/-- **`envBound w s`** — the envelope slack `(144/25)·w²·(1−w²)·A₀A₁A₂`
(`Aᵢ = acNfull w (s+i)`), the nonnegative quantity by which `Δ²V+2` exceeds `0` in cleared form. -/
def envBound (w : Q') (s : Nat) : Q' :=
  c144over25 * (qpow w 2 * ((1 + -qpow w 2)
    * (acNfull w s * (acNfull w (s + 1) * acNfull w (s + 2)))))

/-- `0 ≤ acNfull w t` for `0 ≤ w`. -/
theorem acNfull_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (t : Nat) : (0 : Q') ≤ acNfull w t :=
  acN_nonneg hw0 (t + 1) t

/-- On `0 ≤ w ≤ 1`, `0 ≤ 1 + -qpow w 2` (`1 − w² ≥ 0`). -/
theorem oneSubSq_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) :
    (0 : Q') ≤ (1 : Q') + -qpow w 2 := by
  have hle : qpow w 2 ≤ (1 : Q') := HeatKernelGap.qpow_le_one hw0 hw1 2
  have h := Q'.add_le_add_right (qpow w 2) 1 (-qpow w 2) hle
  have h0 : (qpow w 2 + -qpow w 2).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (qpow w 2) (-qpow w 2)) (Q'.neg_add_self_eqv (qpow w 2))
  exact Q'.le_trans' 0 (qpow w 2 + -qpow w 2) (1 + -qpow w 2) (Q'.ge_of_eqv h0) h

/-- **`envBound_nonneg`** — the envelope slack is `≥ 0` on the physical window `0 ≤ w ≤ 1`. -/
theorem envBound_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (s : Nat) :
    (0 : Q') ≤ envBound w s := by
  have hA : (0 : Q') ≤ acNfull w s * (acNfull w (s + 1) * acNfull w (s + 2)) :=
    Q'.mul_nonneg _ _ (acNfull_nonneg hw0 s)
      (Q'.mul_nonneg _ _ (acNfull_nonneg hw0 (s + 1)) (acNfull_nonneg hw0 (s + 2)))
  have hOm : (0 : Q') ≤ (1 + -qpow w 2) * (acNfull w s * (acNfull w (s + 1) * acNfull w (s + 2))) :=
    Q'.mul_nonneg _ _ (oneSubSq_nonneg hw0 hw1) hA
  have hQ : (0 : Q') ≤ qpow w 2 * ((1 + -qpow w 2)
      * (acNfull w s * (acNfull w (s + 1) * acNfull w (s + 2)))) :=
    Q'.mul_nonneg _ _ (qpow_nonneg w hw0 2) hOm
  exact Q'.mul_nonneg _ _ (by decide) hQ

/-! ## 1. The envelope predicate and the reduction to `FullRangeFloor`. -/

/-- **`CurvatureEnvelope w s`** — the cleared uniform envelope at window `s`:
`floorLHS + (144/25)·w²·(1−w²)·A₀A₁A₂ ≤ floorRHS`, i.e. `Δ²V(s)+2 ≥ (144/25)·w²·(1−w²)`. -/
def CurvatureEnvelope (w : Q') (s : Nat) : Prop :=
  floorLHS w s + envBound w s ≤ floorRHS w s

/-- **`fullRangeFloor_of_curvatureEnvelope`** — the envelope at `s` implies `FullRangeFloor w s`.
Since the envelope slack is `≥ 0` on `0 ≤ w ≤ 1`, dropping it only weakens the inequality. -/
theorem fullRangeFloor_of_curvatureEnvelope {w : Q'} {s : Nat}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (h : CurvatureEnvelope w s) : FullRangeFloor w s := by
  show floorLHS w s ≤ floorRHS w s
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg (floorLHS w s) (envBound w s) (envBound_nonneg hw0 hw1 s)) h

/-! ## 2. The uniform residual and the R1 assembly. -/

/-- **`UniformCurvatureEnvelope w`** (NAMED OPEN — the sharp uniform saddle core).  The curvature
envelope for EVERY window `s`.  A single sharp inequality family (`Δ²V+2 ≥ (144/25)w²(1−w²)`,
tight at `s = 0`), superseding the entire (parity × w-regime) case split.  Strictly better-posed
than the two-region `RegimeGETailBound`. -/
structure UniformCurvatureEnvelope (w : Q') : Type where
  env : ∀ s, CurvatureEnvelope w s

/-- **`saddleVarianceFloor_of_curvatureEnvelope`** — the uniform envelope inhabits R1
(`SaddleVarianceFloor w`).  ONE inequality family supersedes the 3-cell split.  Axiom-clean. -/
def saddleVarianceFloor_of_curvatureEnvelope {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (U : UniformCurvatureEnvelope w) :
    SaddleVarianceFloor w where
  floor := fun s => fullRangeFloor_of_curvatureEnvelope hw0 hw1 (U.env s)

/-- **`regimeGETailBound_of_envelopeTail`** — the envelope restricted to the large windows `s ≥ 7`
inhabits the standing residual `R1RegimeGE.RegimeGETailBound w`, wiring the uniform envelope into
the existing R1 upper-half assembly.  So closing the envelope on `s ≥ 7` closes the two-region
tail. -/
def regimeGETailBound_of_envelopeTail {w : Q'} (hw1 : w ≤ 1)
    (T : ∀ s, 7 ≤ s → CurvatureEnvelope w s) : R1RegimeGE.RegimeGETailBound w where
  tail := fun hhalf _ s hs => by
    have hw0 : (0 : Q') ≤ w :=
      Q'.le_trans' 0 R1CaseSplit.half w (by decide) hhalf
    exact fullRangeFloor_of_curvatureEnvelope hw0 hw1 (T s hs)

/-! ## 3. The binding case `s = 0`, PROVED in closed form (perfect square).

At `s = 0` the cleared slack is the pure monomial `slack₀ = 96·w¹¹`, and the envelope gap is an
EXACT perfect square:

    `slack₀ − envBound w 0 = (96/25)·w¹¹·(1 − 6w²)² ≥ 0` .

This certifies `CurvatureEnvelope w 0` exactly at the corner where it is tight (`w² = 1/6`),
proving the envelope object is correct and provable at its binding value.  The proof is the
`slackP`/`Poly` pivot: the polynomial identity `slackP 0 = envBoundPoly 0 + sqCertPoly` is a
single `decide`, and `sqCertPoly` evaluates `≥ 0` by `q_mul_self_nonneg`. -/

/-- `envBoundPoly s` — the envelope slack `(144/25)·w²·(1−w²)·A₀A₁A₂` as a coefficient list. -/
def envBoundPoly (s : Nat) : Poly :=
  pscale c144over25
    (pmul (monoP (1 : Q') 2)
      (pmul [(1 : Q'), (0 : Q'), (-1 : Q')]
        (pmul (acPoly s) (pmul (acPoly (s + 1)) (acPoly (s + 2))))))

/-- `sqCertPoly` — the `s = 0` perfect-square certificate `(96/25)·w¹¹·(1 − 6w²)²`. -/
def sqCertPoly : Poly :=
  pscale (Q'.mkPos 96 25 (by decide))
    (pmul (monoP (1 : Q') 11) (ppow [(1 : Q'), (0 : Q'), (-6 : Q')] 2))

/-- `eval [1,0,-1] w ≃ 1 + -qpow w 2`  (`= 1 − w²`). -/
theorem eval_oneSubSqP (w : Q') :
    (eval [(1 : Q'), (0 : Q'), (-1 : Q')] w).eqv (1 + -qpow w 2) := by
  show ((1 : Q') + w * ((0 : Q') + w * ((-1 : Q') + w * (0 : Q')))).eqv (1 + -qpow w 2)
  refine Q'.add_eqv_congr_left 1 _ _ ?_
  -- w·(0 + w·(-1 + w·0)) ≃ -qpow w 2
  have hinner : ((0 : Q') + w * ((-1 : Q') + w * (0 : Q'))).eqv (-(w * 1)) := by
    refine Q'.eqv_trans _ _ _ (q_zero_add_eqv (w * ((-1 : Q') + w * (0 : Q')))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w _ _
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (-1 : Q') (w * 0) 0 (q_mul_zero w))
        (q_add_zero_eqv (-1 : Q')))) ?_
    exact Q'.mul_neg_eqv w 1
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w _ _ hinner) ?_
  -- w·(-(w·1)) ≃ -(qpow w 2)
  refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv w (w * 1)) ?_
  refine Q'.neg_eqv_congr _ _ ?_
  -- w·(w·1) ≃ qpow w 2 = (1·w)·w
  show (w * (w * 1)).eqv (qpow w 0 * w * w)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left w _ _ (Q'.mul_one_eqv w)) ?_
  -- w·w ≃ (1·w)·w
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ w (Q'.one_mul_eqv w)) ?_
  exact Q'.eqv_refl _

/-- **`hEnvBound`** — `envBound w s ≃ eval (envBoundPoly s) w`. -/
theorem hEnvBound (w : Q') (s : Nat) : (envBound w s).eqv (eval (envBoundPoly s) w) := by
  have hA2 : (acNfull w (s + 2)).eqv (eval (acPoly (s + 2)) w) := hAcNfull w (s + 2)
  have hA1 : (acNfull w (s + 1)).eqv (eval (acPoly (s + 1)) w) := hAcNfull w (s + 1)
  have hA0 : (acNfull w s).eqv (eval (acPoly s) w) := hAcNfull w s
  have hA1A2 := hEvalMul hA1 hA2
  have hA012 := hEvalMul hA0 hA1A2
  have hQ2 : (qpow w 2).eqv (eval (monoP (1 : Q') 2) w) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv (qpow w 2)))
      (Q'.eqv_symm (eval_monoP (1 : Q') w 2))
  have hOneSub : ((1 : Q') + -qpow w 2).eqv (eval [(1 : Q'), (0 : Q'), (-1 : Q')] w) :=
    Q'.eqv_symm (eval_oneSubSqP w)
  have hOmA := hEvalMul hOneSub hA012
  have hQ2OmA := hEvalMul hQ2 hOmA
  exact hEvalScale c144over25 hQ2OmA

/-- `qpow y 2 ≥ 0` (a square is nonnegative). -/
theorem qpow_two_nonneg (y : Q') : (0 : Q') ≤ qpow y 2 := by
  have h : (qpow y 2).eqv (y * y) := by
    show ((1 : Q') * y * y).eqv (y * y)
    exact Q'.mul_eqv_congr_right ((1 : Q') * y) y y (Q'.one_mul_eqv y)
  exact Q'.le_trans' _ _ _ (SumOfSquares.q_mul_self_nonneg y) (Q'.ge_of_eqv h)

/-- **`sqCert_nonneg`** — the `s = 0` perfect-square certificate evaluates `≥ 0` for `0 ≤ w`. -/
theorem sqCert_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) : (0 : Q') ≤ eval sqCertPoly w := by
  -- monoP 1 11 ≥ 0
  have hMono : (0 : Q') ≤ eval (monoP (1 : Q') 11) w :=
    Q'.le_trans' 0 ((1 : Q') * qpow w 11) _
      (Q'.mul_nonneg _ _ (by decide) (qpow_nonneg w hw0 11))
      (Q'.ge_of_eqv (eval_monoP (1 : Q') w 11))
  -- ppow [1,0,-6] 2 ≥ 0 (a square)
  have hSq : (0 : Q') ≤ eval (ppow [(1 : Q'), (0 : Q'), (-6 : Q')] 2) w :=
    Q'.le_trans' 0 (qpow (eval [(1 : Q'), (0 : Q'), (-6 : Q')] w) 2) _
      (qpow_two_nonneg _)
      (Q'.ge_of_eqv (eval_ppow [(1 : Q'), (0 : Q'), (-6 : Q')] w 2))
  -- product ≥ 0
  have hProd : (0 : Q') ≤ eval (pmul (monoP (1 : Q') 11)
      (ppow [(1 : Q'), (0 : Q'), (-6 : Q')] 2)) w :=
    Q'.le_trans' 0 (eval (monoP (1 : Q') 11) w * eval (ppow [(1 : Q'), (0 : Q'), (-6 : Q')] 2) w) _
      (Q'.mul_nonneg _ _ hMono hSq)
      (Q'.ge_of_eqv (eval_pmul (monoP (1 : Q') 11) (ppow [(1 : Q'), (0 : Q'), (-6 : Q')] 2) w))
  -- scale by 96/25 ≥ 0
  exact Q'.le_trans' 0
    (Q'.mkPos 96 25 (by decide) * eval (pmul (monoP (1 : Q') 11)
      (ppow [(1 : Q'), (0 : Q'), (-6 : Q')] 2)) w) _
    (Q'.mul_nonneg _ _ (by decide) hProd)
    (Q'.ge_of_eqv (eval_pscale (Q'.mkPos 96 25 (by decide))
      (pmul (monoP (1 : Q') 11) (ppow [(1 : Q'), (0 : Q'), (-6 : Q')] 2)) w))

set_option maxRecDepth 4000 in
/-- **`curvatureEnvelope_zero`** — THE BINDING CASE `s = 0`, PROVED.  The envelope gap is the exact
perfect square `(96/25)·w¹¹·(1−6w²)²`, so `CurvatureEnvelope w 0` holds for every `0 ≤ w`.  The
polynomial identity `slackP 0 = envBoundPoly 0 + sqCertPoly` is a single `decide`. -/
theorem curvatureEnvelope_zero {w : Q'} (hw0 : (0 : Q') ≤ w) : CurvatureEnvelope w 0 := by
  show floorLHS w 0 + envBound w 0 ≤ floorRHS w 0
  -- the polynomial split slackP 0 = envBoundPoly 0 + sqCertPoly
  have hpoly : (eval (slackP 0) w).eqv (eval (envBoundPoly 0) w + eval sqCertPoly w) :=
    Q'.eqv_trans _ _ _
      (poly_eqv (slackP 0) (padd (envBoundPoly 0) sqCertPoly) w (by decide))
      (eval_padd (envBoundPoly 0) sqCertPoly w)
  -- envBound w 0 ≤ eval (slackP 0) w
  have hle : envBound w 0 ≤ eval (slackP 0) w := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (hEnvBound w 0)) ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (eval (envBoundPoly 0) w) (eval sqCertPoly w)
        (sqCert_nonneg hw0)) ?_
    exact Q'.ge_of_eqv hpoly
  -- conclude via the slack ledger  floorRHS ≃ floorLHS + eval slackP
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_left (floorLHS w 0) (envBound w 0) (eval (slackP 0) w) hle) ?_
  exact Q'.ge_of_eqv (hSlackEq w 0)

/-! ## 3.5 Reduced-bracket Bernstein-in-`w²` certificate machinery (bounded windows `s ≥ 1`).

The envelope gap `G_s = slackP s − envBoundPoly s` factors as `w^{k_s} · bracket_s(w²)` where
`bracket_s` is a polynomial in `x = w²` that is Bernstein-nonnegative on `[0,1]` (`s ≥ 2` at native
degree, `s = 1` after a small degree elevation).  So `G_s = w^{k} · Σ_i cᵢ · (w²)^i · (1−w²)^{d−i}`
with `cᵢ ≥ 0` — a manifest certificate at MUCH lower degree than the raw slack.  This subsection
formalizes that certificate over the `w²` Bernstein basis and gives the general consumer
`curvatureEnvelope_of_sqCert`, discharging each bounded window by a single decidable coefficient
identity. -/

/-- `onemSqP` — the polynomial `1 − w²`. -/
def onemSqP : Poly := [(1 : Q'), (0 : Q'), (-1 : Q')]

/-- `bernBasisSqP n i = (w²)^i · (1 − w²)^{n−i}` — a `w²`-Bernstein basis element. -/
def bernBasisSqP (n i : Nat) : Poly := shiftZ (2 * i) (ppow onemSqP (n - i))

theorem eval_bernBasisSqP_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (n i : Nat) :
    (0 : Q') ≤ eval (bernBasisSqP n i) w := by
  have hom : (0 : Q') ≤ eval onemSqP w :=
    Q'.le_trans' _ _ _ (oneSubSq_nonneg hw0 hw1) (Q'.ge_of_eqv (eval_oneSubSqP w))
  have hpp : (0 : Q') ≤ eval (ppow onemSqP (n - i)) w :=
    Q'.le_trans' 0 (qpow (eval onemSqP w) (n - i)) _
      (qpow_nonneg _ hom (n - i)) (Q'.ge_of_eqv (eval_ppow onemSqP w (n - i)))
  exact Q'.le_trans' 0 (qpow w (2 * i) * eval (ppow onemSqP (n - i)) w) _
    (Q'.mul_nonneg _ _ (qpow_nonneg w hw0 (2 * i)) hpp)
    (Q'.ge_of_eqv (eval_shiftZ w (ppow onemSqP (n - i)) (2 * i)))

/-- `bernTermsSqP n terms = Σ (i,c)∈terms  c · (w²)^i · (1−w²)^{n−i}` — the `w²`-Bernstein
certificate polynomial (sparse `(index, nonneg coeff)` list). -/
def bernTermsSqP (n : Nat) : List (Nat × Q') → Poly
  | [] => ([] : Poly)
  | ((i, a) :: rest) => padd (pscale a (bernBasisSqP n i)) (bernTermsSqP n rest)

theorem eval_bernTermsSqP_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) (n : Nat) :
    ∀ (terms : List (Nat × Q')), (∀ t ∈ terms, (0 : Q') ≤ t.2) →
      (0 : Q') ≤ eval (bernTermsSqP n terms) w
  | [], _ => Q'.le_refl' 0
  | ((i, a) :: rest), h => by
      show (0 : Q') ≤ eval (padd (pscale a (bernBasisSqP n i)) (bernTermsSqP n rest)) w
      refine Q'.le_trans' 0 _ _ ?_
        (Q'.ge_of_eqv (eval_padd (pscale a (bernBasisSqP n i)) (bernTermsSqP n rest) w))
      refine Q'.zero_le_add _ _ ?_
        (eval_bernTermsSqP_nonneg hw0 hw1 n rest (fun t ht => h t (List.mem_cons_of_mem _ ht)))
      refine Q'.le_trans' 0 (a * eval (bernBasisSqP n i) w) _ ?_
        (Q'.ge_of_eqv (eval_pscale a (bernBasisSqP n i) w))
      exact Q'.mul_nonneg _ _ (h (i, a) List.mem_cons_self)
        (eval_bernBasisSqP_nonneg hw0 hw1 n i)

/-- **`curvatureEnvelope_of_sqCert`** — the general bounded-window consumer.  Given `0 ≤ w ≤ 1`, a
`w²`-Bernstein term list with nonnegative coefficients, and the single decidable identity
`slackP s = envBoundPoly s + w^k · bernTermsSqP d terms`, the envelope `CurvatureEnvelope w s`
holds.  The whole transcendental content of window `s` collapses to the one `decide` on `hid`. -/
theorem curvatureEnvelope_of_sqCert {w : Q'} (s k d : Nat) (terms : List (Nat × Q'))
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1)
    (hnn : ∀ t ∈ terms, (0 : Q') ≤ t.2)
    (hid : allZero (psub (slackP s)
      (padd (envBoundPoly s) (shiftZ k (bernTermsSqP d terms))))) :
    CurvatureEnvelope w s := by
  show floorLHS w s + envBound w s ≤ floorRHS w s
  have hcert_nn : (0 : Q') ≤ eval (shiftZ k (bernTermsSqP d terms)) w :=
    Q'.le_trans' 0 (qpow w k * eval (bernTermsSqP d terms) w) _
      (Q'.mul_nonneg _ _ (qpow_nonneg w hw0 k)
        (eval_bernTermsSqP_nonneg hw0 hw1 d terms hnn))
      (Q'.ge_of_eqv (eval_shiftZ w (bernTermsSqP d terms) k))
  have hpoly : (eval (slackP s) w).eqv
      (eval (envBoundPoly s) w + eval (shiftZ k (bernTermsSqP d terms)) w) :=
    Q'.eqv_trans _ _ _
      (poly_eqv (slackP s) (padd (envBoundPoly s) (shiftZ k (bernTermsSqP d terms))) w hid)
      (eval_padd (envBoundPoly s) (shiftZ k (bernTermsSqP d terms)) w)
  have hle : envBound w s ≤ eval (slackP s) w := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (hEnvBound w s)) ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_self_of_nonneg (eval (envBoundPoly s) w)
        (eval (shiftZ k (bernTermsSqP d terms)) w) hcert_nn) ?_
    exact Q'.ge_of_eqv hpoly
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_left (floorLHS w s) (envBound w s) (eval (slackP s) w) hle) ?_
  exact Q'.ge_of_eqv (hSlackEq w s)

/-! ## 3.6 The bounded windows `s = 1, 2, 3`, PROVED via the `w²`-Bernstein certificate. -/

/-- `w²`-Bernstein certificate for the envelope gap `G_1` (elevated degree `d = 11`, shift `k = 20`). -/
def envTerms1 : List (Nat × Q') :=
  [(0, Q'.mkPos 768 1 (by decide)), (1, Q'.mkPos 154752 25 (by decide)),
   (2, Q'.mkPos 516096 25 (by decide)), (3, Q'.mkPos 891264 25 (by decide)),
   (4, Q'.mkPos 155136 5 (by decide)), (5, Q'.mkPos 45312 5 (by decide)),
   (6, Q'.mkPos 79872 25 (by decide)), (7, Q'.mkPos 627456 25 (by decide)),
   (8, Q'.mkPos 1054464 25 (by decide)), (9, Q'.mkPos 160896 5 (by decide)),
   (10, Q'.mkPos 12288 1 (by decide)), (11, Q'.mkPos 1920 1 (by decide))]

set_option maxRecDepth 8000 in
/-- **`curvatureEnvelope_one`** — the envelope at `s = 1`, PROVED on `0 ≤ w ≤ 1`. -/
theorem curvatureEnvelope_one {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) :
    CurvatureEnvelope w 1 :=
  curvatureEnvelope_of_sqCert 1 20 11 envTerms1 hw0 hw1 (by decide) (by decide)

/-- `w²`-Bernstein certificate for `G_2` (native degree `d = 8`, shift `k = 35`). -/
def envTerms2 : List (Nat × Q') :=
  [(0, Q'.mkPos 79392 25 (by decide)), (1, Q'.mkPos 121728 5 (by decide)),
   (2, Q'.mkPos 1750848 25 (by decide)), (3, Q'.mkPos 2279424 25 (by decide)),
   (4, Q'.mkPos 1195584 25 (by decide)), (5, Q'.mkPos 44928 5 (by decide)),
   (6, Q'.mkPos 27840 1 (by decide)), (7, Q'.mkPos 38400 1 (by decide)),
   (8, Q'.mkPos 16800 1 (by decide))]

set_option maxRecDepth 8000 in
/-- **`curvatureEnvelope_two`** — the envelope at `s = 2`, PROVED on `0 ≤ w ≤ 1`. -/
theorem curvatureEnvelope_two {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) :
    CurvatureEnvelope w 2 :=
  curvatureEnvelope_of_sqCert 2 35 8 envTerms2 hw0 hw1 (by decide) (by decide)

/-- `w²`-Bernstein certificate for `G_3` (native degree `d = 14`, shift `k = 50`). -/
def envTerms3 : List (Nat × Q') :=
  [(0, Q'.mkPos 10368 1 (by decide)), (1, Q'.mkPos 2794752 25 (by decide)),
   (2, Q'.mkPos 13620672 25 (by decide)), (3, Q'.mkPos 40601088 25 (by decide)),
   (4, Q'.mkPos 85756032 25 (by decide)), (5, Q'.mkPos 142860288 25 (by decide)),
   (6, Q'.mkPos 201136896 25 (by decide)), (7, Q'.mkPos 240553728 25 (by decide)),
   (8, Q'.mkPos 233933568 25 (by decide)), (9, Q'.mkPos 178757376 25 (by decide)),
   (10, Q'.mkPos 4444608 1 (by decide)), (11, Q'.mkPos 62735616 25 (by decide)),
   (12, Q'.mkPos 6526464 5 (by decide)), (13, Q'.mkPos 494592 1 (by decide)),
   (14, Q'.mkPos 94080 1 (by decide))]

set_option maxRecDepth 12000 in
/-- **`curvatureEnvelope_three`** — the envelope at `s = 3`, PROVED on `0 ≤ w ≤ 1`. -/
theorem curvatureEnvelope_three {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) :
    CurvatureEnvelope w 3 :=
  curvatureEnvelope_of_sqCert 3 50 14 envTerms3 hw0 hw1 (by decide) (by decide)

/-- `w²`-Bernstein certificate for `G_4` (native degree `d = 20`, shift `k = 71`). -/
def envTerms4 : List (Nat × Q') :=
  [(0, Q'.mkPos 764736 25 (by decide)), (1, Q'.mkPos 15126528 25 (by decide)),
   (2, Q'.mkPos 138692448 25 (by decide)), (3, Q'.mkPos 783875136 25 (by decide)),
   (4, Q'.mkPos 3065433504 25 (by decide)), (5, Q'.mkPos 8837243904 25 (by decide)),
   (6, Q'.mkPos 19588396896 25 (by decide)), (7, Q'.mkPos 34530457536 25 (by decide)),
   (8, Q'.mkPos 10001441376 5 (by decide)), (9, Q'.mkPos 61529392512 25 (by decide)),
   (10, Q'.mkPos 66287348928 25 (by decide)), (11, Q'.mkPos 63501587328 25 (by decide)),
   (12, Q'.mkPos 10741873728 5 (by decide)), (13, Q'.mkPos 39146446848 25 (by decide)),
   (14, Q'.mkPos 23922547008 25 (by decide)), (15, Q'.mkPos 12028824192 25 (by decide)),
   (16, Q'.mkPos 4954842816 25 (by decide)), (17, Q'.mkPos 1680284928 25 (by decide)),
   (18, Q'.mkPos 461010816 25 (by decide)), (19, Q'.mkPos 18402048 5 (by decide)),
   (20, Q'.mkPos 395136 1 (by decide))]

set_option maxRecDepth 20000 in
/-- **`curvatureEnvelope_four`** — the envelope at `s = 4`, PROVED on `0 ≤ w ≤ 1`. -/
theorem curvatureEnvelope_four {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) :
    CurvatureEnvelope w 4 :=
  curvatureEnvelope_of_sqCert 4 71 20 envTerms4 hw0 hw1 (by decide) (by decide)

/-- `w²`-Bernstein certificate for `G_5` (native degree `d = 29`, shift `k = 92`). -/
def envTerms5 : List (Nat × Q') :=
  [(0, Q'.mkPos 61440 1 (by decide)), (1, Q'.mkPos 7890432 5 (by decide)),
   (2, Q'.mkPos 97419264 5 (by decide)), (3, Q'.mkPos 3856533504 25 (by decide)),
   (4, Q'.mkPos 4409816064 5 (by decide)), (5, Q'.mkPos 19448750208 5 (by decide)),
   (6, Q'.mkPos 13811799552 1 (by decide)), (7, Q'.mkPos 1017667527168 25 (by decide)),
   (8, Q'.mkPos 2547145033728 25 (by decide)), (9, Q'.mkPos 5509837481472 25 (by decide)),
   (10, Q'.mkPos 10436828732928 25 (by decide)), (11, Q'.mkPos 3495066077184 5 (by decide)),
   (12, Q'.mkPos 26029553528832 25 (by decide)), (13, Q'.mkPos 34634726818176 25 (by decide)),
   (14, Q'.mkPos 41289769414656 25 (by decide)), (15, Q'.mkPos 44204377818624 25 (by decide)),
   (16, Q'.mkPos 42568716523008 25 (by decide)), (17, Q'.mkPos 36880032877824 25 (by decide)),
   (18, Q'.mkPos 28673448446976 25 (by decide)), (19, Q'.mkPos 19883302768128 25 (by decide)),
   (20, Q'.mkPos 12176252570112 25 (by decide)), (21, Q'.mkPos 6500859579648 25 (by decide)),
   (22, Q'.mkPos 2982583683072 25 (by decide)), (23, Q'.mkPos 1159014813696 25 (by decide)),
   (24, Q'.mkPos 376518610944 25 (by decide)), (25, Q'.mkPos 101155608576 25 (by decide)),
   (26, Q'.mkPos 4442996736 5 (by decide)), (27, Q'.mkPos 3874977792 25 (by decide)),
   (28, Q'.mkPos 97929216 5 (by decide)), (29, Q'.mkPos 1354752 1 (by decide))]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
/-- **`curvatureEnvelope_five`** — the envelope at `s = 5`, PROVED on `0 ≤ w ≤ 1`. -/
theorem curvatureEnvelope_five {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) :
    CurvatureEnvelope w 5 :=
  curvatureEnvelope_of_sqCert 5 92 29 envTerms5 hw0 hw1 (by decide) (by decide)

/-- `w²`-Bernstein certificate for `G_6` (native degree `d = 38`, shift `k = 119`). -/
def envTerms6 : List (Nat × Q') :=
  [(0, Q'.mkPos 150720 1 (by decide)), (1, Q'.mkPos 28500864 5 (by decide)),
   (2, Q'.mkPos 521147424 5 (by decide)), (3, Q'.mkPos 30697989888 25 (by decide)),
   (4, Q'.mkPos 261980224512 25 (by decide)), (5, Q'.mkPos 1726593787008 25 (by decide)),
   (6, Q'.mkPos 9149014965504 25 (by decide)), (7, Q'.mkPos 40073263702656 25 (by decide)),
   (8, Q'.mkPos 148057415348928 25 (by decide)), (9, Q'.mkPos 468649311174912 25 (by decide)),
   (10, Q'.mkPos 1286755891762272 25 (by decide)), (11, Q'.mkPos 619254077384832 5 (by decide)),
   (12, Q'.mkPos 263489536111872 1 (by decide)), (13, Q'.mkPos 12487337538770688 25 (by decide)),
   (14, Q'.mkPos 21241594720135296 25 (by decide)), (15, Q'.mkPos 32630434631818752 25 (by decide)),
   (16, Q'.mkPos 45525248773884096 25 (by decide)), (17, Q'.mkPos 57968815574131584 25 (by decide)),
   (18, Q'.mkPos 13525265236197216 5 (by decide)), (19, Q'.mkPos 72466343664478464 25 (by decide)),
   (20, Q'.mkPos 71412293713549056 25 (by decide)), (21, Q'.mkPos 64706012341110144 25 (by decide)),
   (22, Q'.mkPos 53831342120099328 25 (by decide)), (23, Q'.mkPos 41018978291709312 25 (by decide)),
   (24, Q'.mkPos 5706888836283072 5 (by decide)), (25, Q'.mkPos 18048308660342784 25 (by decide)),
   (26, Q'.mkPos 10329666208037856 25 (by decide)), (27, Q'.mkPos 5318724793557888 25 (by decide)),
   (28, Q'.mkPos 2446770834980352 25 (by decide)), (29, Q'.mkPos 997392400091136 25 (by decide)),
   (30, Q'.mkPos 356811204684672 25 (by decide)), (31, Q'.mkPos 110797766790912 25 (by decide)),
   (32, Q'.mkPos 29502410761728 25 (by decide)), (33, Q'.mkPos 6648837149952 25 (by decide)),
   (34, Q'.mkPos 1250368380864 25 (by decide)), (35, Q'.mkPos 192640363776 25 (by decide)),
   (36, Q'.mkPos 4693987584 5 (by decide)), (37, Q'.mkPos 82570752 1 (by decide)),
   (38, Q'.mkPos 3991680 1 (by decide))]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 60000 in
/-- **`curvatureEnvelope_six`** — the envelope at `s = 6`, PROVED on `0 ≤ w ≤ 1`. -/
theorem curvatureEnvelope_six {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) :
    CurvatureEnvelope w 6 :=
  curvatureEnvelope_of_sqCert 6 119 38 envTerms6 hw0 hw1 (by decide) (by decide)

/-! ## 4. Doc-section — PROVED vs NAMED-open (CRITICAL honesty)

PROVED (axiom-clean):
  * `envBound_nonneg` — the envelope slack `(144/25)w²(1−w²)A₀A₁A₂ ≥ 0` on `0 ≤ w ≤ 1`.
  * `fullRangeFloor_of_curvatureEnvelope` — envelope at `s` ⟹ `FullRangeFloor w s`.
  * `saddleVarianceFloor_of_curvatureEnvelope` — the uniform envelope ⟹ R1 (`SaddleVarianceFloor`),
    superseding the 3-cell case split with ONE sharp inequality family.
  * `regimeGETailBound_of_envelopeTail` — the envelope on `s ≥ 7` ⟹ the standing tail residual
    `R1RegimeGE.RegimeGETailBound`, wiring the envelope into the existing R1 upper-half assembly.
  * `curvatureEnvelope_zero` — the BINDING case `s = 0` PROVED via the exact perfect square
    `slack₀ − envBound = (96/25)w¹¹(1−6w²)²`.
  * `curvatureEnvelope_of_sqCert` — the general bounded-window consumer: a `w²`-Bernstein
    positivity certificate for `G_s = slackP s − envBoundPoly s` discharges `CurvatureEnvelope w s`.
  * `curvatureEnvelope_one`, `curvatureEnvelope_two`, `curvatureEnvelope_three` — windows
    `s = 1, 2, 3` PROVED via that certificate (reduced-bracket degrees `11, 8, 14` in `x = w²`).

NAMED OPEN (Type-level structure, never `sorry`):
  * `UniformCurvatureEnvelope w` — the sharp uniform saddle inequality `Δ²V+2 ≥ (144/25)w²(1−w²)`
    for ALL `s` (`s = 0, 1, 2, 3` PROVED; residual = the uniform large-`s` tail).  The honest
    remaining analytic core of R1, strictly better-posed than the two-region `RegimeGETailBound`.
    Each further bounded window is discharged mechanically by `curvatureEnvelope_of_sqCert`; the
    genuine open content is a uniform-in-`s` tail bound (theta-moment saddle).
-/

end YMGap.Continuum.R1CurvatureEnvelope

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.R1CurvatureEnvelope.envBound_nonneg
#print axioms YMGap.Continuum.R1CurvatureEnvelope.fullRangeFloor_of_curvatureEnvelope
#print axioms YMGap.Continuum.R1CurvatureEnvelope.saddleVarianceFloor_of_curvatureEnvelope
#print axioms YMGap.Continuum.R1CurvatureEnvelope.regimeGETailBound_of_envelopeTail
#print axioms YMGap.Continuum.R1CurvatureEnvelope.curvatureEnvelope_zero
#print axioms YMGap.Continuum.R1CurvatureEnvelope.curvatureEnvelope_of_sqCert
#print axioms YMGap.Continuum.R1CurvatureEnvelope.curvatureEnvelope_one
#print axioms YMGap.Continuum.R1CurvatureEnvelope.curvatureEnvelope_two
#print axioms YMGap.Continuum.R1CurvatureEnvelope.curvatureEnvelope_three
