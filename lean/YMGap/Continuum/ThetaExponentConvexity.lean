/-
Track A / R2 (track: 1-convexity) — the THETA-EXPONENT (Cauchy–Schwarz / Lagrange) engine
of the autoconvolution log-concavity node, and the HONEST relocation of its target away
from the (refuted) diagonal "variance / Cauchy–Schwarz on the exponent measure" pairing
onto the already-proved off-diagonal Gram Cauchy–Binet (`lagCorrTP2_common`), with the sole
remaining content named as the moving-window truncation edge.

# What this module adds (read first — load-bearing honesty)

The scalar target behind `FiniteSMargin` / `CrossRatioMonotone` is an *s*-log-concavity with
reserve of the diagonal-band autoconvolution `acN`.  Two framings compete:

  * FRAME A ("theta exponent convexity"): each polynomial `A_s(w)`, `M_s(w)` is a moment sum
    `Σ_k a_k w^{e_k}`, and Cauchy–Schwarz on the exponent measure makes each SEPARATELY
    log-convex in `w`.  This is a genuine, unconditional fact — proved here as the general
    discrete Cauchy–Schwarz / Lagrange identity `cauchy_schwarz` and its two-evaluation-point
    theta form `theta_two_point_CS`.
  * FRAME B (the correct object): the target is the OFF-DIAGONAL MLR / TP₂ ordering BETWEEN the
    two different arrays `A_s` and `M_s`.  Cauchy–Schwarz on exponent moments addresses the wrong
    pairing (diagonal, not off-diagonal), so Frame A CANNOT reach the target — a mis-diagnosis
    already machine-refuted for the naive pairwise `ArrayMLR` in the tree.  The correct positivity
    is the Cauchy–Binet 2×2 minor of the Gram/Hankel lag-correlation, whose per-summand atom
    (`coeffMinorProd_nonneg`) and whose full common-range total positivity (`lagCorrTP2_common`)
    are ALREADY PROVED.

So this module (i) proves the honest Frame-A engine at full generality, (ii) instantiates it to the
theta weight to recover the DIAGONAL Gram positivity (`lagCorrCR_cauchy_schwarz` — Cauchy–Schwarz
for the lag-correlation), and (iii) records, as sharply-named Type-level residuals, exactly what is
left after the proved off-diagonal common-range TP₂: the MOVING-WINDOW truncation edge (the sole
gap between the common-range `lagCorrCR` and the growing-range `lagCorr`) and the line-sum
log-concavity seed (which, per the tree's rank-1 counterexample, does NOT follow from bare TP₂).

# What this module proves (all axiom-clean)

PROVED (`[propext]` / `[propext, Quot.sound]` only):
  * `lagTerm`, `csMinor`, `lagTerm_swap` — the pointwise Lagrange/Plücker half-sum identity
    `lagTerm(i,j) + lagTerm(j,i) ≃ csMinor(i,j)²` (reusing the generic `plucker8`).
  * `csDet`, `csDet_eq_termSum`, `csDet_double_eq` — the Andréief/Lagrange expansion
    `2·[(Σf²)(Σg²) − (Σfg)²] ≃ Σ_i Σ_j csMinor(i,j)²`.
  * `csDet_nonneg`, `cauchy_schwarz` — THE ENGINE: the general discrete Cauchy–Schwarz
    `(Σ_i f_i g_i)² ≤ (Σ_i f_i²)(Σ_i g_i²)`, per-summand a square (`q_mul_self_nonneg`).
  * `lagCorrCR_cauchy_schwarz` — the theta corollary: the diagonal Gram positivity
    `lagCorrCR(p,q)² ≤ lagCorrCR(p,p)·lagCorrCR(q,q)` (Cauchy–Schwarz for the theta
    lag-correlation at a common range).
  * `theta_two_point_CS` — the two-evaluation-point theta form: on the exponent grid `e`,
    `(Σ_k u^{e_k} v^{e_k})² ≤ (Σ_k u^{2e_k})(Σ_k v^{2e_k})` (Frame-A "exponent-measure" CS).
  * `gramTP2_common` — a thin re-export of the PROVED off-diagonal common-range total positivity
    `FusionCoreStepRoundF.lagCorrTP2_common` (the correct Frame-B object; NOT reproved here).

REDUCTION (Type-level, honest):
  * `MovingWindowEdge w` — the sole residual bridging the common-range TP₂ to the growing-range
    `lagCorr` TP₂ (the moving-truncation-window boundary defect).  `lagCorrTP2_of_movingWindowEdge`
    shows an edge witness inhabits the pipeline residual `FusionCoreStepRoundD.LagCorrTP2 w`.
  * `LineSumLogConcaveCR w` — the antidiagonal line-sum log-concavity at a common range (the A3
    seed).  Per the tree's rank-1 counterexample this does NOT follow from bare TP₂; its honest
    seed is the per-summand Gram positivity `csMinor(i,j)² ≥ 0` supplied here.

# HONESTY — what is NOT closed

`MovingWindowEdge` and `LineSumLogConcaveCR` are NAMED-OPEN (never `sorry`); this module does not
inhabit them.  The Frame-A Cauchy–Schwarz engine is fully proved but is the WRONG pairing for the
off-diagonal target (documented, not a defect of effort); the off-diagonal content is discharged at
a common range by the reused `lagCorrTP2_common`, leaving only the moving-window truncation edge.
This is a representation/relocation advance on one box-level log-concavity sub-fact; it is NOT a 4D
Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `plucker8`/`fsum`/`coeffW`/`qpow`/`lagCorrCR` lemmas, the
`fsum_mul_fsum`/`fsum_swap`/`q2_add`/`q2_neg` finite-sum algebra, and the square-nonneg atom
`q_mul_self_nonneg`.  Every load-bearing declaration is gated with `#print axioms`; permitted output
is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses
are `Type`-level data.
-/

import YMGap.Continuum.FusionCoreStepRoundF
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.ThetaExponentConvexity

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundF

/-! ## 1. The pointwise Lagrange/Plücker half-sum identity -/

/-- **`lagTerm`** — the `(i,j)` summand of the Cauchy–Schwarz defect `(Σf²)(Σg²) − (Σfg)²`,
`lagTerm(i,j) = (f_i·f_i)·(g_j·g_j) − (f_i·g_i)·(f_j·g_j)`. -/
def lagTerm (f g : Nat → Q') (i j : Nat) : Q' :=
  (f i * f i) * (g j * g j) + -((f i * g i) * (f j * g j))

/-- **`csMinor`** — the `2×2` Cauchy–Schwarz minor `csMinor(i,j) = f_i·g_j − f_j·g_i`. -/
def csMinor (f g : Nat → Q') (i j : Nat) : Q' :=
  f i * g j + -(f j * g i)

/-- **`lagTerm_swap` — THE POINTWISE LAGRANGE IDENTITY.**  The symmetrized defect summand is the
square of the Cauchy–Schwarz minor,

    lagTerm(i,j) + lagTerm(j,i)  ≃  csMinor(i,j) · csMinor(i,j).

The generic bilinear-minor identity `plucker8` at the diagonal substitution `α=γ=f_i`, `α'=γ'=f_j`,
`β=δ=g_i`, `β'=δ'=g_j`, after two `mul_comm_eqv` adjustments matching the negated products. -/
theorem lagTerm_swap (f g : Nat → Q') (i j : Nat) :
    (lagTerm f g i j + lagTerm f g j i).eqv (csMinor f g i j * csMinor f g i j) := by
  unfold lagTerm csMinor
  have hp := plucker8 (f i) (f j) (g i) (g j) (f i) (f j) (g i) (g j)
  refine Q'.eqv_trans _ _ _ ?_ hp
  refine Q'.add_eqv_congr' ?_ ?_
  · refine Q'.add_eqv_congr_left _ _ _ ?_
    exact Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left (f i * g i) _ _ (Q'.mul_comm_eqv (f j) (g j)))
  · refine Q'.add_eqv_congr_left _ _ _ ?_
    exact Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_left (f j * g j) _ _ (Q'.mul_comm_eqv (f i) (g i)))

/-! ## 2. The Andréief/Lagrange expansion of the Cauchy–Schwarz defect -/

/-- **`csDet`** — the Cauchy–Schwarz determinant `(Σf²)(Σg²) − (Σfg)²`. -/
def csDet (f g : Nat → Q') (n : Nat) : Q' :=
  fsum (fun i => f i * f i) n * fsum (fun i => g i * g i) n
    + -(fsum (fun i => f i * g i) n * fsum (fun i => f i * g i) n)

/-- **`csDet_eq_termSum`** — `csDet ≃ Σ_i Σ_j lagTerm(i,j)`.  `fsum_mul_fsum` opens each product
of column sums into a double sum; the two double sums combine.  (The clone of `Mdet_eq_termSum`.) -/
theorem csDet_eq_termSum (f g : Nat → Q') (n : Nat) :
    (csDet f g n).eqv (fsum (fun i => fsum (fun j => lagTerm f g i j) n) n) := by
  unfold csDet lagTerm
  have hAB : (fsum (fun i => f i * f i) n * fsum (fun i => g i * g i) n).eqv
      (fsum (fun i => fsum (fun j => (f i * f i) * (g j * g j)) n) n) :=
    fsum_mul_fsum (fun i => f i * f i) (fun j => g j * g j) n n
  have hCD : (fsum (fun i => f i * g i) n * fsum (fun i => f i * g i) n).eqv
      (fsum (fun i => fsum (fun j => (f i * g i) * (f j * g j)) n) n) :=
    fsum_mul_fsum (fun i => f i * g i) (fun j => f j * g j) n n
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hAB (Q'.neg_eqv_congr _ _ hCD)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
    (q2_neg (fun i j => (f i * g i) * (f j * g j)) n)) ?_
  exact q2_add
    (fun i j => (f i * f i) * (g j * g j))
    (fun i j => -((f i * g i) * (f j * g j)))
    n

/-- **`csDet_double_eq` — THE LAGRANGE HALF-SUM IDENTITY.**  Twice the Cauchy–Schwarz determinant
is the double sum of the squared minors:

    csDet + csDet  ≃  Σ_i Σ_j csMinor(i,j)².

(`csDet ≃ Σ lagTerm(i,j) ≃ Σ lagTerm(j,i)` by the `i↔j` swap; add and apply `lagTerm_swap`.) -/
theorem csDet_double_eq (f g : Nat → Q') (n : Nat) :
    (csDet f g n + csDet f g n).eqv
      (fsum (fun i => fsum (fun j => csMinor f g i j * csMinor f g i j) n) n) := by
  have hS := csDet_eq_termSum f g n
  have hSwap : (fsum (fun i => fsum (fun j => lagTerm f g i j) n) n).eqv
      (fsum (fun i => fsum (fun j => lagTerm f g j i) n) n) :=
    fsum_swap (fun i j => lagTerm f g i j) n n
  have hS' : (csDet f g n).eqv (fsum (fun i => fsum (fun j => lagTerm f g j i) n) n) :=
    Q'.eqv_trans _ _ _ hS hSwap
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hS hS') ?_
  refine Q'.eqv_trans _ _ _
    (q2_add (fun i j => lagTerm f g i j) (fun i j => lagTerm f g j i) n) ?_
  exact fsum_eqv_congr _ _
    (fun i => fsum_eqv_congr _ _ (fun j => lagTerm_swap f g i j) n) n

/-! ## 3. The engine: the general discrete Cauchy–Schwarz -/

/-- **`csDet_nonneg`** — the Cauchy–Schwarz determinant is `≥ 0`.  The doubled determinant is
`Σ_i Σ_j csMinor² ≥ 0` (`fsum_nonneg` twice, `q_mul_self_nonneg` per summand); cancel the positive
factor `2`.  (The clone of `Mdet_nonneg`, with a bare square in place of the minor product.) -/
theorem csDet_nonneg (f g : Nat → Q') (n : Nat) : (0 : Q') ≤ csDet f g n := by
  have hsum : (0 : Q') ≤ fsum (fun i => fsum (fun j => csMinor f g i j * csMinor f g i j) n) n :=
    fsum_nonneg (fun i =>
      fsum_nonneg (fun j =>
        YMGap.Constructive.SumOfSquares.q_mul_self_nonneg (csMinor f g i j)) n) n
  have hdouble : (0 : Q') ≤ csDet f g n + csDet f g n :=
    Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (csDet_double_eq f g n))
  have h2pos : (0 : Q') < Q'.ofNat 2 := Q'.ofNat_succ_pos 1
  have hmul : (0 : Q') ≤ Q'.ofNat 2 * csDet f g n :=
    Q'.le_trans' _ _ _ hdouble (Q'.ge_of_eqv (ofNat_two_mul_eqv (csDet f g n)))
  have hmul0 : Q'.ofNat 2 * (0 : Q') ≤ Q'.ofNat 2 * csDet f g n :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (q_mul_zero (Q'.ofNat 2))) hmul
  exact le_of_mul_le_mul_left_pos h2pos hmul0

/-- **`cauchy_schwarz` — THE ENGINE.**  The general discrete Cauchy–Schwarz inequality over `Q'`,
for arbitrary finite sequences `f, g` and length `n`:

    (Σ_{i<n} f_i·g_i)²  ≤  (Σ_{i<n} f_i²)·(Σ_{i<n} g_i²).

`Q'.le_of_sub_nonneg` on `csDet_nonneg`.  This is the honest Frame-A "Cauchy–Schwarz on the exponent
measure" engine (no positivity hypothesis is needed — the inequality is unconditional). -/
theorem cauchy_schwarz (f g : Nat → Q') (n : Nat) :
    (fsum (fun i => f i * g i) n) * (fsum (fun i => f i * g i) n)
      ≤ (fsum (fun i => f i * f i) n) * (fsum (fun i => g i * g i) n) :=
  Q'.le_of_sub_nonneg (csDet_nonneg f g n)

/-! ## 4. Theta corollaries -/

/-- **`lagCorrCR_cauchy_schwarz` — the diagonal Gram positivity of the theta lag-correlation.**
For any common cutoff `n`,

    lagCorrCR(p,q)²  ≤  lagCorrCR(p,p) · lagCorrCR(q,q).

`cauchy_schwarz` with `f_r = c_{p+r}`, `g_r = c_{q+r}` (definitionally `Σ f g = lagCorrCR(p,q)`,
`Σ f² = lagCorrCR(p,p)`, `Σ g² = lagCorrCR(q,q)`).  This is the DIAGONAL slice of the Gram
Cauchy–Binet — Cauchy–Schwarz — recovered from the general engine. -/
theorem lagCorrCR_cauchy_schwarz (w : Q') (n p q : Nat) :
    lagCorrCR w n p q * lagCorrCR w n p q
      ≤ lagCorrCR w n p p * lagCorrCR w n q q :=
  cauchy_schwarz (fun r => coeffW w (p + r)) (fun r => coeffW w (q + r)) n

/-- **`theta_two_point_CS` — the two-evaluation-point theta (exponent-measure) Cauchy–Schwarz.**
On any exponent grid `e` and any two evaluation points `u, v`,

    (Σ_{k<n} u^{e_k}·v^{e_k})²  ≤  (Σ_{k<n} u^{2e_k})·(Σ_{k<n} v^{2e_k})

(where `u^{2e_k} = u^{e_k}·u^{e_k}`).  `cauchy_schwarz` with `f_k = u^{e_k}`, `g_k = v^{e_k}`.  This
is the precise Frame-A "variance / Cauchy–Schwarz on the exponent measure" object — genuine and
unconditional, but the DIAGONAL pairing (see the honest verdict). -/
theorem theta_two_point_CS (u v : Q') (e : Nat → Nat) (n : Nat) :
    (fsum (fun k => qpow u (e k) * qpow v (e k)) n)
        * (fsum (fun k => qpow u (e k) * qpow v (e k)) n)
      ≤ (fsum (fun k => qpow u (e k) * qpow u (e k)) n)
        * (fsum (fun k => qpow v (e k) * qpow v (e k)) n) :=
  cauchy_schwarz (fun k => qpow u (e k)) (fun k => qpow v (e k)) n

/-! ## 5. The correct object (re-export) and the honest residuals -/

/-- **`gramTP2_common` — the PROVED off-diagonal common-range total positivity** (Frame B, the
CORRECT object; NOT reproved here — a thin re-export of `FusionCoreStepRoundF.lagCorrTP2_common`).
For `0 < w ≤ 1` and any shared cutoff `n`,

    p ≤ p',  q ≤ q'   ⟹   lagCorrCR(p,q')·lagCorrCR(p',q) ≤ lagCorrCR(p,q)·lagCorrCR(p',q').

This is the FULL off-diagonal Cauchy–Binet minor of the Gram/Hankel lag-correlation, of which
`lagCorrCR_cauchy_schwarz` is only the diagonal slice; the Frame-A exponent-measure CS cannot reach
it (wrong pairing). -/
theorem gramTP2_common {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (hwpos : (0 : Q') < w) {p q p' q' : Nat} (hpp' : p ≤ p') (hqq' : q ≤ q') (n : Nat) :
    lagCorrCR w n p q' * lagCorrCR w n p' q ≤ lagCorrCR w n p q * lagCorrCR w n p' q' :=
  FusionCoreStepRoundF.lagCorrTP2_common hw0 hw1 hwpos hpp' hqq' n

/-- **`MovingWindowEdge w`** — the SOLE remaining residual after the proved common-range TP₂: the
moving-truncation-window boundary defect.  `gramTP2_common` closes total positivity at any FIXED
common cutoff `n`; the growing-range `lagCorr` (RoundD) uses the pair-dependent cutoff
`N+1−max p q`, so its four `2×2` entries live at DIFFERENT ranges.  This structure packages the
reconciliation — that the growing-range `lagCorr` satisfies the same TP₂, the range mismatch being
dominated by the proved super-geometric reserve `coeffW_superLogConcave_wsq`.  NAMED-OPEN (never
`sorry`). -/
structure MovingWindowEdge (w : Q') : Type where
  /-- Total positivity of the growing-range (moving-window) lag-correlation. -/
  edge : ∀ N p q p' q', p ≤ p' → q ≤ q' →
    lagCorr w N p q' * lagCorr w N p' q ≤ lagCorr w N p q * lagCorr w N p' q'

/-- **`lagCorrTP2_of_movingWindowEdge` — the pipeline wiring.**  A `MovingWindowEdge` witness
inhabits the pipeline residual `FusionCoreStepRoundD.LagCorrTP2 w` (which the strand route consumes
as its analytic core A2).  This exhibits that the ONLY thing between the proved common-range Gram
Cauchy–Binet TP₂ and the mass-gap pipeline's `LagCorrTP2` is the moving-window truncation edge. -/
def lagCorrTP2_of_movingWindowEdge {w : Q'} (e : MovingWindowEdge w) :
    FusionCoreStepRoundD.LagCorrTP2 w where
  tp2 := e.edge

/-- **`LineSumLogConcaveCR w`** — the antidiagonal line-sum log-concavity at a fixed common range
(the A3 seed), for the common-range Gram lag-correlation `lagCorrCR w n`:

    lineSum(s)·lineSum(s+2)  ≤  lineSum(s+1)².

Per the tree's rank-1 counterexample (`f=(1,0,1) → L=(1,0,2,0,1)`) this does NOT follow from bare
TP₂; its honest seed is the line-sum-level Cauchy–Binet, whose per-summand Gram positivity
`csMinor(i,j)² ≥ 0` this module supplies (`csDet_nonneg`).  NAMED-OPEN (never `sorry`). -/
structure LineSumLogConcaveCR (w : Q') : Type where
  /-- Antidiagonal line-sum log-concavity of the common-range Gram lag-correlation. -/
  llc : ∀ n s,
    lineSum (lagCorrCR w n) s * lineSum (lagCorrCR w n) (s + 2)
      ≤ lineSum (lagCorrCR w n) (s + 1) * lineSum (lagCorrCR w n) (s + 1)

/-! ## 6. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `lagTerm_swap` — the pointwise Lagrange/Plücker half-sum identity (`plucker8` at the diagonal).
  * `csDet_eq_termSum`, `csDet_double_eq` — the Andréief/Lagrange expansion of the CS defect.
  * `csDet_nonneg`, `cauchy_schwarz` — the general discrete Cauchy–Schwarz engine (Frame A).
  * `lagCorrCR_cauchy_schwarz` — the diagonal Gram positivity of the theta lag-correlation.
  * `theta_two_point_CS` — the two-point exponent-measure Cauchy–Schwarz (the exact Frame-A object).
  * `gramTP2_common` — re-export of the PROVED off-diagonal common-range Gram TP₂ (Frame B).

NAMED OPEN (Type-level structure, never `sorry`):
  * `MovingWindowEdge w` — the moving-truncation-window boundary defect (the sole gap between the
    proved common-range TP₂ and the growing-range `lagCorr` TP₂); `lagCorrTP2_of_movingWindowEdge`
    wires it to the pipeline residual `LagCorrTP2`.
  * `LineSumLogConcaveCR w` — the A3 line-sum log-concavity seed (NOT implied by bare TP₂; seeded by
    the proved per-summand square positivity `csDet_nonneg`).

HONEST VERDICT.  This module proves the Frame-A "theta exponent convexity" (Cauchy–Schwarz on the
exponent measure) at full generality and instantiates it to the theta weight, then RELOCATES the
actual off-diagonal target onto the already-proved Gram Cauchy–Binet common-range TP₂
(`lagCorrTP2_common`), leaving exactly the finite moving-window truncation edge and the line-sum
seed as sharply-named residuals.  The Frame-A engine is unconditional but is the WRONG (diagonal)
pairing for the off-diagonal MLR target — this is documented, not a defect of effort.  This is a
representation/relocation advance on one box-level log-concavity sub-fact; it is NOT a 4D
Yang–Mills mass gap. -/

end YMGap.Continuum.ThetaExponentConvexity

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ThetaExponentConvexity.lagTerm_swap
#print axioms YMGap.Continuum.ThetaExponentConvexity.csDet_eq_termSum
#print axioms YMGap.Continuum.ThetaExponentConvexity.csDet_double_eq
#print axioms YMGap.Continuum.ThetaExponentConvexity.csDet_nonneg
#print axioms YMGap.Continuum.ThetaExponentConvexity.cauchy_schwarz
#print axioms YMGap.Continuum.ThetaExponentConvexity.lagCorrCR_cauchy_schwarz
#print axioms YMGap.Continuum.ThetaExponentConvexity.theta_two_point_CS
#print axioms YMGap.Continuum.ThetaExponentConvexity.gramTP2_common
#print axioms YMGap.Continuum.ThetaExponentConvexity.lagCorrTP2_of_movingWindowEdge
