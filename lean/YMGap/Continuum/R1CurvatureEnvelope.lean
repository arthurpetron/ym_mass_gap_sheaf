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

NAMED OPEN (Type-level structure, never `sorry`):
  * `UniformCurvatureEnvelope w` — the sharp uniform saddle inequality `Δ²V+2 ≥ (144/25)w²(1−w²)`
    for ALL `s` (equivalently `s ≥ 1`; `s = 0` PROVED).  The honest remaining analytic core of R1,
    strictly better-posed than the two-region `RegimeGETailBound`.
-/

end YMGap.Continuum.R1CurvatureEnvelope

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.R1CurvatureEnvelope.envBound_nonneg
#print axioms YMGap.Continuum.R1CurvatureEnvelope.fullRangeFloor_of_curvatureEnvelope
#print axioms YMGap.Continuum.R1CurvatureEnvelope.saddleVarianceFloor_of_curvatureEnvelope
#print axioms YMGap.Continuum.R1CurvatureEnvelope.regimeGETailBound_of_envelopeTail
#print axioms YMGap.Continuum.R1CurvatureEnvelope.curvatureEnvelope_zero
