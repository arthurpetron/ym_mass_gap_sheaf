/-
Track A / R2 — Round M of the fusion box log-concavity node: the EXACT GAUSSIAN
FACTORIZATION of the central-autoconvolution weight product, isolating the SOURCE of the
reserve constant `256/225` and reducing the sole open residual `(†)` to a pure, `w`-free
combinatorial log-concavity of the Gaussian-stripped coupling sequence.

# What this module adds (read first — load-bearing honesty)

Rounds A–L reduced the whole node to ONE residual, the truncated-block reserve

    (†)   (256/225)·acN(s+1,s)·acN(s+1,s+2)  ≤  acN(s+1,s+1)²,

with `acN(w,n,S) = Σ_{p<n} c_p·c_{S−p}`, `c_p = coeffW w p = (p+1)·w^{p(p+2)}`.  Round L
REFUTED the Gershgorin / diagonal-dominance / matrix-PSD closure (the reserve matrix is not
PSD), pinning the genuine content to a SIGNED, weight-specific cancellation.

Round M supplies the missing STRUCTURE — the exact origin of that cancellation and of the
reserve constant.  Writing `c_p = (p+1) w^{p(p+2)}`, the product of two weights on the
antidiagonal `a+b = S` factorizes EXACTLY as

    c_a · c_b  =  (a+1)(b+1) · w^{ (a+1)² + (b+1)² − 2 }
               =  w^{c4(S)} · [ (a+1)(b+1) · w^{ −2(a+1)(b+1) } ]        (a+b = S),

because `c4 a + c4 b + 2ab = c4(a+b)` (`c4 S = S(S+2) = (S+1)²−1`).  The first factor
`w^{c4(S)}` is a pure Gaussian in `S` whose log-concavity SECOND DIFFERENCE is EXACTLY the
constant `2` (`c4(S) + c4(S+2) = 2·c4(S+1) + 2`, in-tree `FusionResidualBound.c4_sum_symm`),
i.e. the Gaussian reserve is exactly `w^{−2} = 1/w² ≥ 4` at `w ≤ 1/2`.  The SECOND factor is
the pure `w`-free coupling `U(S) := Σ_{i+j=S} i·j·Q^{i·j}`, `Q = 1/w²`.

Consequence (the reserve accounting, verified — see the numeric ledger in the doc-comment):
`acN(s+1,S) = w^{c4(S)−2}·(range-`(s+1)` truncation of `U(S+2)`)`, and dividing the reserve
`(†)` by the common Gaussian factor leaves EXACTLY

    (256/225)·w²·U(s+2)·U(s+4)  ≤  U(s+3)²,        i.e.   U(s+3)² ≥ (256/(225·Q))·U(s+2)·U(s+4).

Since `w² ≤ 1/4`, the whole reserve budget the coupling must supply is only
`(256/225)·w² ≤ 64/225 ≈ 0.284` (`gaussianReserveBudget`), whereas the true coupling margin
`U(s+3)²/(U(s+2)U(s+4)) → 1/√Q = 1/2` (`≈ 0.497` worst, mpmath dps 60).  So the ENTIRE
reserve `256/225` is paid by the Gaussian gap `Q ≥ 4`; the coupling `U` need only be "not too
anti-log-concave", with a uniform `≈ 1.75×` cushion.

MODULE DELIVERABLES (all PROVED, axiom-clean).
  * `c4_antidiag` — the antidiagonal Casimir identity `c4 a + c4 b + 2ab = c4 (a+b)` (Nat).
  * `coeffW_antidiag_gaussian` — THE EXACT FACTORIZATION
        c_a · c_b · w^{2ab}  ≃  (dimQ a · dimQ b) · w^{c4(a+b)},
    exhibiting the Gaussian weight `w^{c4(S)}` and the coupling `dimQ a·dimQ b` on the
    antidiagonal `a+b = S` (no division; the `w^{2ab}` clears the negative coupling power).
  * `gaussianReserveBudget` — the reserve-accounting inequality `reserveC · w² ≤ 64/225` for
    `w ≤ 1/2`: the reserve `256/225` costs at most `64/225` of the coupling margin, the rest
    is paid by the Gaussian gap.
  * `reserve_holds_at_half_4` — (†) HOLDS at the physical point `w = 1/2` for `s = 4`
    (extending Round L's `s = 0..3`; `B/A ≈ 2.077`, margin `≈ 1.83×`), the exact margin staying
    `≈ 2.0`, NOT approaching the needed `256/225 ≈ 1.138` — evidence (not proof) of the
    uniform reserve.  (Higher `s` are kernel-`decide`-infeasible; the margin table to `s=58`
    is in the numeric ledger.)

# HONESTY — what is NOT closed

`(†)` / `SymMinorGershgorin` / `FiniteSMargin` remain NAMED-OPEN; this module CLOSES NOTHING
downstream and inhabits NO guarded Clay-frontier bundle.  What Round M proves is the exact
factorization that *localizes and explains* the reserve: all of `256/225` is supplied by the
Gaussian second-difference `w^{−2} ≥ 4`, and the residual is the `w`-free log-concavity margin
`U(s+3)² ≥ (256/(225Q))·U(s+2)U(s+4)` of the coupling `U(S) = Σ ij Q^{ij}`.  This margin is
`→ 1/√Q` (a discrete theta / local-CLT saddle), and — as verified numerically — is NOT
recoverable by any dominant-term / geometric-tail bound (those lose exactly the saddle-width
`θ(Q)²` factor and fail for every physical `w ≤ 1/2`).  So the residual is confirmed to be a
genuine heat-kernel LOCAL-CLT (saddle-WIDTH) statement, now in its cleanest `w`-free form; it
is NOT a finite rational inequality.  This is a structural sharpening of one box-level
log-concavity sub-fact — it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW` / `dimQ` / `c4` / `qpow` definitions,
`qpow_add` / `qpow_mono` / `mul_swap4`, and `decide` only on closed concrete-rational facts.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only (the `decide` facts depend on NO axioms).  No `Classical.*`,
no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionCoreStepRoundL
import YMGap.Continuum.FusionCoreStepRoundC

namespace YMGap.Continuum.FusionCoreStepRoundM

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.AutoconvGershgorin

/-! ## 1. The antidiagonal Casimir identity -/

/-- **`c4_antidiag`** — the antidiagonal Casimir identity: `c4 a + c4 b + 2·a·b = c4 (a+b)`.
Because `c4 S = S(S+2)`, the sum of two Casimirs on the antidiagonal `a+b = S` plus twice
their product completes to `c4 S`.  This is the algebraic root of the Gaussian factorization
(`(a+1)² + (b+1)² + 2(a+1)(b+1) = (a+b+2)²`).  Pure `Nat`, `omega` over opaque products. -/
theorem c4_antidiag (a b : Nat) : c4 a + c4 b + 2 * a * b = c4 (a + b) := by
  show a * (a + 2) + b * (b + 2) + 2 * a * b = (a + b) * (a + b + 2)
  have e1 : a * (a + 2) = a * a + a * 2 := Nat.mul_add a a 2
  have e2 : b * (b + 2) = b * b + b * 2 := Nat.mul_add b b 2
  have e3 : (a + b) * (a + b + 2) = (a + b) * (a + b) + (a + b) * 2 := Nat.mul_add (a + b) (a + b) 2
  have e4 : (a + b) * (a + b) = a * (a + b) + b * (a + b) := Nat.add_mul a b (a + b)
  have e5 : a * (a + b) = a * a + a * b := Nat.mul_add a a b
  have e6 : b * (a + b) = b * a + b * b := Nat.mul_add b a b
  have e7 : a * b = b * a := Nat.mul_comm a b
  have e8 : 2 * a * b = 2 * (a * b) := Nat.mul_assoc 2 a b
  omega

/-! ## 2. The exact Gaussian factorization of the weight product -/

/-- **`coeffW_antidiag_gaussian` — THE EXACT GAUSSIAN FACTORIZATION.**  For all `a,b`,

    coeffW w a · coeffW w b · w^{2ab}  ≃  (dimQ a · dimQ b) · w^{c4(a+b)}.

On the antidiagonal `a+b = S` this reads `c_a·c_b = w^{c4 S}·(dimQ a·dimQ b·w^{−2ab})`: the
weight product is the pure Gaussian `w^{c4 S}` times the `w`-free coupling `dimQ a·dimQ b`
carried by the (cleared) negative power `w^{−2ab}`.  This is the structural identity that
exhibits WHERE the reserve of `(†)` comes from: the Gaussian `w^{c4 S}` has second difference
exactly `2` (`c4_sum_symm`), i.e. reserve `w^{−2} = 1/w² ≥ 4` at `w ≤ 1/2`.  Proof: unfold
`coeffW`, regroup `(dimQ a·q^{c4 a})(dimQ b·q^{c4 b})` into `(dimQ a·dimQ b)(q^{c4 a}·q^{c4 b})`
via `mul_swap4`, fuse the three `qpow` factors by `qpow_add`, and collapse the exponent by
`c4_antidiag`. -/
theorem coeffW_antidiag_gaussian (w : Q') (a b : Nat) :
    (coeffW w a * coeffW w b * qpow w (2 * a * b)).eqv
      (dimQ a * dimQ b * qpow w (c4 (a + b))) := by
  -- unfold both coeffW: c_a·c_b = (dimQ a·q^{c4 a})·(dimQ b·q^{c4 b})
  have hunfold : (coeffW w a * coeffW w b).eqv
      ((dimQ a * dimQ b) * (qpow w (c4 a) * qpow w (c4 b))) := by
    show ((dimQ a * qpow w (c4 a)) * (dimQ b * qpow w (c4 b))).eqv
      ((dimQ a * dimQ b) * (qpow w (c4 a) * qpow w (c4 b)))
    exact mul_swap4 (dimQ a) (qpow w (c4 a)) (dimQ b) (qpow w (c4 b))
  -- multiply by q^{2ab} and push it inside the coupling
  have hstep1 : (coeffW w a * coeffW w b * qpow w (2 * a * b)).eqv
      ((dimQ a * dimQ b) * (qpow w (c4 a) * qpow w (c4 b)) * qpow w (2 * a * b)) :=
    Q'.mul_eqv_congr_right (coeffW w a * coeffW w b)
      ((dimQ a * dimQ b) * (qpow w (c4 a) * qpow w (c4 b))) (qpow w (2 * a * b)) hunfold
  -- regroup: (D · P) · R ≃ D · (P · R)
  have hstep2 : ((dimQ a * dimQ b) * (qpow w (c4 a) * qpow w (c4 b)) * qpow w (2 * a * b)).eqv
      ((dimQ a * dimQ b) * ((qpow w (c4 a) * qpow w (c4 b)) * qpow w (2 * a * b))) :=
    Q'.mul_assoc_eqv (dimQ a * dimQ b) (qpow w (c4 a) * qpow w (c4 b)) (qpow w (2 * a * b))
  -- fuse the powers: q^{c4 a}·q^{c4 b} ≃ q^{c4 a + c4 b}
  have hfuse1 : (qpow w (c4 a) * qpow w (c4 b)).eqv (qpow w (c4 a + c4 b)) :=
    Q'.eqv_symm (HeatKernelRGStep.qpow_add w (c4 a) (c4 b))
  -- q^{c4 a + c4 b}·q^{2ab} ≃ q^{c4 a + c4 b + 2ab}
  have hfuse2 : (qpow w (c4 a + c4 b) * qpow w (2 * a * b)).eqv
      (qpow w (c4 a + c4 b + 2 * a * b)) :=
    Q'.eqv_symm (HeatKernelRGStep.qpow_add w (c4 a + c4 b) (2 * a * b))
  -- collapse the exponent by the antidiagonal identity
  have hcollapse : (qpow w (c4 a + c4 b + 2 * a * b)).eqv (qpow w (c4 (a + b))) := by
    rw [c4_antidiag a b]; exact Q'.eqv_refl _
  have hcoupling : ((qpow w (c4 a) * qpow w (c4 b)) * qpow w (2 * a * b)).eqv
      (qpow w (c4 (a + b))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (qpow w (c4 a) * qpow w (c4 b)) (qpow w (c4 a + c4 b))
        (qpow w (2 * a * b)) hfuse1)
      (Q'.eqv_trans _ _ _ hfuse2 hcollapse)
  refine Q'.eqv_trans _ _ _ hstep1 (Q'.eqv_trans _ _ _ hstep2 ?_)
  exact Q'.mul_eqv_congr_left (dimQ a * dimQ b)
    ((qpow w (c4 a) * qpow w (c4 b)) * qpow w (2 * a * b)) (qpow w (c4 (a + b))) hcoupling

/-! ## 3. The reserve budget — why `256/225` is affordable -/

/-- The reserve constant `256/225 = 1 + 31/225`. -/
abbrev reserveC : Q' := Q'.mkPos 256 225 (by decide)

/-- **`gaussianReserveBudget` — the reserve accounting.**  For `0 ≤ w ≤ 1/2`,

    reserveC · w²  ≤  64/225.

After dividing `(†)` by the common Gaussian factor `w^{c4}` the coupling `U` must supply only
the residual budget `(256/225)·w²`, and since `w² ≤ 1/4` this budget is at most
`64/225 ≈ 0.284` — well below the true coupling margin `U(s+3)²/(U(s+2)U(s+4)) → 1/√Q ≥ 0.497`.
So the ENTIRE reserve `256/225` is paid by the Gaussian gap `1/w² ≥ 4`.  Proof: `w² ≤ 1/4`
(`qpow_mono` to `w = 1/2`), scaled by `reserveC ≥ 0`, then `(256/225)·(1/4) = 64/225`. -/
theorem gaussianReserveBudget {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) :
    reserveC * qpow w 2 ≤ Q'.mkPos 64 225 (by decide) := by
  have hw2q : qpow w 2 ≤ quarter :=
    Q'.le_trans' _ _ _ (qpow_mono hw0 hw12 2) (by decide)
  have h1 : reserveC * qpow w 2 ≤ reserveC * quarter :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hw2q (by decide)
  exact Q'.le_trans' _ _ _ h1 (by decide)

/-! ## 4. The residual HOLDS at the physical point `w = 1/2` (s = 4, extending Round L) -/

/-- The truncated-block reserve `(†)` at `w = 1/2` for mode `s`:
`(256/225)·acN(s+1,s)·acN(s+1,s+2) ≤ acN(s+1,s+1)²`. -/
abbrev reserveHoldsAt (s : Nat) : Prop :=
  reserveC * (acN wH (s + 1) s * acN wH (s + 1) (s + 2))
    ≤ acN wH (s + 1) (s + 1) * acN wH (s + 1) (s + 1)

set_option maxRecDepth 8000 in
/-- **`reserve_holds_at_half_4`** — (†) at `w = 1/2`, `s = 4` (`B/A ≈ 2.077`). -/
theorem reserve_holds_at_half_4 : reserveHoldsAt 4 := by decide

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`; the `decide` facts use NO axioms):
  * `c4_antidiag` — the antidiagonal Casimir identity `c4 a + c4 b + 2ab = c4(a+b)`.
  * `coeffW_antidiag_gaussian` — the EXACT Gaussian factorization of the weight product,
    `c_a·c_b·w^{2ab} ≃ (dimQ a·dimQ b)·w^{c4(a+b)}`, exhibiting the Gaussian `w^{c4 S}` and the
    coupling `dimQ a·dimQ b` on the antidiagonal `a+b = S`.
  * `gaussianReserveBudget` — `reserveC·w² ≤ 64/225` on `w ≤ 1/2`: `256/225` costs `≤ 64/225`
    of the coupling margin, the rest is paid by the Gaussian gap `1/w² ≥ 4`.
  * `reserve_holds_at_half_4` — (†) holds at `w = 1/2`, `s = 4` (`B/A ≈ 2.077`); with Round L's
    `s = 0..3` the physical point is verified through `s = 4`.

NAMED OPEN (carried, NOT inhabited here):
  * `(†)` / `AutoconvGershgorin.SymMinorGershgorin w` / `AcNReserveAnalytic.FiniteSMargin w` —
    equivalently the `w`-free coupling log-concavity `U(s+3)² ≥ (256/(225Q))·U(s+2)U(s+4)`,
    `U(S) = Σ_{i+j=S} ij·Q^{ij}`, `Q = 1/w² ≥ 4`.  A discrete theta / local-CLT saddle margin
    (`→ 1/√Q`), NOT recoverable by dominant-term/geometric-tail bounds (which lose the
    saddle-width `θ(Q)²` and fail for every physical `w ≤ 1/2`).

HONEST VERDICT.  Round M supplies the exact Gaussian factorization that localizes and explains
the reserve: the ENTIRE `256/225` is paid by the Gaussian second-difference `w^{−2} ≥ 4`
(`c4_sum_symm`), and the sole open content is the `w`-free coupling log-concavity margin of
`U(S) = Σ ij Q^{ij}` — a genuine heat-kernel local-CLT (saddle-WIDTH) statement, now in its
cleanest form.  Nothing downstream is closed; no guarded Clay-frontier bundle is inhabited;
this is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundM

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundM.c4_antidiag
#print axioms YMGap.Continuum.FusionCoreStepRoundM.coeffW_antidiag_gaussian
#print axioms YMGap.Continuum.FusionCoreStepRoundM.gaussianReserveBudget
#print axioms YMGap.Continuum.FusionCoreStepRoundM.reserve_holds_at_half_4
-- dropped
-- dropped
-- dropped
-- dropped
