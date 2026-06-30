/-
Track A / R2 — Round B of the fusion box log-concavity node.

# What this module adds (read first — load-bearing honesty)

`FusionCoreStepRoundA` proved the DIRECT box Cauchy–Binet
`boxSum N s · boxSum N (s+2) ≤ boxSum N (s+1)²` at `w = 1/2` for `N = 3, 4`, named the
unsatisfiability of the additive `CoreStep`, and packaged the corrected uniform-in-`N`
residual `UniformBoxLogConcave w`.  Round B pushes that data and refines the residual:

ROUND-B DELIVERABLE 1 (concrete, green).  The direct box Cauchy–Binet core lifted TWO
further levels at `w = 1/2`:
  * `boxSum5_tail`, `boxSum6_tail` — the mode tails (`a + b ≤ 2N` kills high modes).
  * `core_N5_half`, `core_N6_half` — `FusionConvLogConcaveCore {5,6} (1/2)` INHABITED
    unconditionally at `w = 1/2` (every excited channel a closed `Q'` `decide`; the
    tails by `boxSum{5,6}_tail`).  The genuine `N = 4 → 5 → 6` push of the box core,
    done DIRECTLY (never through the false `CoreStep`).
  * `s1Dom_N5_half`, `s1Dom_N6_half` — wired to `S1Dominance {5,6} (1/2) 2`.

ROUND-B DELIVERABLE 2 (structural, general-`N`, green).  THE CAUCHY–BINET / TOTAL-
POSITIVITY STRUCTURE of the box log-concavity, made explicit and uniform in `N`:
  * `boxSum_mul_eq_quad` — the product of two box sums is the FULL quadruple Clebsch
    sum `Σ_{a,a',b,b'} K(a,b,s)·K(a',b',t)` (`K(a,b,s) = fusionInd a b s · c_a c_b`).
    Pure `(Σ)(Σ) = ΣΣ` distributivity, axiom-clean, every `N`.
  * `quadDiff` / `boxDiff_eq_quadDiff` — the box cross-difference
    `boxSum(s+1)² − boxSum(s)·boxSum(s+2)` expanded as the SINGLE symmetric quadruple
    sum of the Cauchy–Binet kernel `W_s(a,b,a',b') = fusionInd a b (s+1)·fusionInd a' b'
    (s+1) − fusionInd a b s·fusionInd a' b' (s+2)`, weighted by `c_a c_b c_{a'} c_{b'}`.
  * `UniformBoxQuadCertificate` / `uniformOfQuad` — the SHARPER named residual: the
    aggregate nonnegativity of `quadDiff` (the Cauchy–Binet quadruple form) for all `N`,
    `s`, which IMPLIES `UniformBoxLogConcave` and hence the whole `N`-tower of cores and
    `S1Dominance`.  This is the exact TP₂ / Karlin total-positivity content.

ROUND-B DELIVERABLE 3 (the Gaussian magnitude input for the symbolic route).
  * `coeffW1_le_quarter` — `coeffW w 1 ≤ 1/4` on `0 ≤ w ≤ 1/2` (`c₁ = 2w³ ≤ 2·(1/8)`).
    This is the Gaussian magnitude fact BEYOND log-concavity that the symbolic
    channel certificates need (the `c₁ ≤ 1/4` and the super-geometric ratio decay are
    exactly where generic-log-concave counterexamples bite); proved here for reuse.

# HONESTY — what is NOT closed

The certificate `quadDiff ≥ 0` is NOT pointwise (per-summand) true: the Cauchy–Binet
kernel `W_s` is NOT pointwise `≥ 0`, and generic (even Pólya-frequency) log-concave
weights make the truncated box sum FAIL log-concavity.  The certificate MUST consume the
Gaussian magnitude decay of `c_i = (i+1) w^{i(i+2)}` (hence `coeffW1_le_quarter` and the
ratio decay).  So `quadDiff ≥ 0` for all `N` is the genuine open content — the heat-
kernel `(r,d)` local-CLT — NOT a finite rational inequality.  It is inhabited POINTWISE
at `N = 0,…,6` (`w = 1/2`, this module and `FusionCoreStepRoundA`); the open content is
the all-`N`, symbolic-`w` statement.  The symbolic `N = 3, 4` per-channel SOS
certificates remain NAMED-OPEN; the magnitude input they require is now available.

This is NOT a 4D Yang–Mills mass gap; it is the honest two-level push of the box core
and the explicit Cauchy–Binet/total-positivity refinement of the uniform residual.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the proved `fsum` algebra, structural inductions, and
`decide` only on closed concrete-rational / finite-index facts.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level.
-/

import YMGap.Continuum.FusionCoreStepRoundA
import YMGap.Continuum.HeatKernelGap

namespace YMGap.Continuum.FusionCoreStepRoundB

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.FusionCoreInduction
open YMGap.Continuum.FusionCoreStepRoundA

/-! ## 1. Box-sum mode tails at `N = 5, 6` -/

/-- **`boxSum w 5 (k+11) ≃ 0`** — no `(a,b) ≤ 5` reaches mode `s = k+11` (`a+b ≤ 10`). -/
theorem boxSum5_tail (w : Q') (k : Nat) : (boxSum w 5 (k + 11)).eqv 0 := by
  unfold boxSum
  refine fsum_zero_below (5 + 1) (fun a ha => ?_)
  refine fsum_zero_below (5 + 1) (fun b hb => ?_)
  have hind : fusionInd a b (k + 11) = (0 : Q') := by
    unfold fusionInd
    have hok : fusionOK a b (k + 11) = false := by
      rw [fusionOK_eq_false_iff]; rintro ⟨_, h2, _⟩; omega
    rw [hok]; rfl
  rw [hind]; exact Q'.zero_mul_eqv _

/-- **`boxSum w 6 (k+13) ≃ 0`** — no `(a,b) ≤ 6` reaches mode `s = k+13` (`a+b ≤ 12`). -/
theorem boxSum6_tail (w : Q') (k : Nat) : (boxSum w 6 (k + 13)).eqv 0 := by
  unfold boxSum
  refine fsum_zero_below (6 + 1) (fun a ha => ?_)
  refine fsum_zero_below (6 + 1) (fun b hb => ?_)
  have hind : fusionInd a b (k + 13) = (0 : Q') := by
    unfold fusionInd
    have hok : fusionOK a b (k + 13) = false := by
      rw [fusionOK_eq_false_iff]; rintro ⟨_, h2, _⟩; omega
    rw [hok]; rfl
  rw [hind]; exact Q'.zero_mul_eqv _

/-- The degenerate Cauchy–Binet tail at `N = 5`: for `s = k+9`, the right factor
`boxSum 5 (s+2) ≃ 0`. -/
private theorem cauchyBinet_tail5 {w : Q'} (hw0 : (0 : Q') ≤ w) (k : Nat) :
    boxSum w 5 (k + 9) * boxSum w 5 (k + 9 + 2)
      ≤ boxSum w 5 (k + 9 + 1) * boxSum w 5 (k + 9 + 1) := by
  have hz : (boxSum w 5 (k + 9 + 2)).eqv 0 := boxSum5_tail w k
  have hLHS0 : (boxSum w 5 (k + 9) * boxSum w 5 (k + 9 + 2)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (q_mul_zero _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS0)
    (Q'.mul_nonneg _ _ (boxSum_nonneg hw0 5 (k + 9 + 1)) (boxSum_nonneg hw0 5 (k + 9 + 1)))

/-- The degenerate Cauchy–Binet tail at `N = 6`: for `s = k+11`, the right factor
`boxSum 6 (s+2) ≃ 0`. -/
private theorem cauchyBinet_tail6 {w : Q'} (hw0 : (0 : Q') ≤ w) (k : Nat) :
    boxSum w 6 (k + 11) * boxSum w 6 (k + 11 + 2)
      ≤ boxSum w 6 (k + 11 + 1) * boxSum w 6 (k + 11 + 1) := by
  have hz : (boxSum w 6 (k + 11 + 2)).eqv 0 := boxSum6_tail w k
  have hLHS0 : (boxSum w 6 (k + 11) * boxSum w 6 (k + 11 + 2)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (q_mul_zero _)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS0)
    (Q'.mul_nonneg _ _ (boxSum_nonneg hw0 6 (k + 11 + 1)) (boxSum_nonneg hw0 6 (k + 11 + 1)))

/-! ## 2. The DIRECT box Cauchy–Binet core, lifted to `N = 5` and `N = 6` (`w = 1/2`) -/

/-- **`core_N5_half` — `FusionConvLogConcaveCore 5 (1/2)` INHABITED at `w = 1/2`.**
Excited channels `s = 0,…,8` by `decide`; the high modes `s ≥ 9` are degenerate
(`boxSum5_tail`).  The genuine direct lift of the box core past `core_N4_half`. -/
def core_N5_half : FusionConvLogConcaveCore 5 wH (by decide) (by decide) where
  strongCoupling := by decide
  cauchyBinet := by
    intro s
    match s with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | 6 => decide
    | 7 => decide
    | 8 => decide
    | (k + 9) => exact cauchyBinet_tail5 (by decide) k

/-- **`core_N6_half` — `FusionConvLogConcaveCore 6 (1/2)` INHABITED at `w = 1/2`.**
Excited channels `s = 0,…,10` by `decide`; `s ≥ 11` by `boxSum6_tail`. -/
def core_N6_half : FusionConvLogConcaveCore 6 wH (by decide) (by decide) where
  strongCoupling := by decide
  cauchyBinet := by
    intro s
    match s with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | 6 => decide
    | 7 => decide
    | 8 => decide
    | 9 => decide
    | 10 => decide
    | (k + 11) => exact cauchyBinet_tail6 (by decide) k

/-! ## 3. Wiring to `S1Dominance` at `w = 1/2` -/

/-- The first-excited edge `bmc 2 ≤ bmc 1` at `N = 5`, `w = 1/2` (`decide`). -/
theorem edge5_half : bondMovedCoeff 5 wH 2 2 ≤ bondMovedCoeff 5 wH 2 1 := by decide

/-- The first-excited edge `bmc 2 ≤ bmc 1` at `N = 6`, `w = 1/2` (`decide`). -/
theorem edge6_half : bondMovedCoeff 6 wH 2 2 ≤ bondMovedCoeff 6 wH 2 1 := by decide

/-- **`s1Dom_N5_half` — `S1Dominance 5 (1/2) 2`, wired from `core_N5_half`.** -/
def s1Dom_N5_half : YMGap.Continuum.S1Dominance.S1Dominance 5 wH 2 :=
  YMGap.Continuum.FusionLogConcave.s1Dominance_of_p2 (by decide) core_N5_half edge5_half

/-- **`s1Dom_N6_half` — `S1Dominance 6 (1/2) 2`, wired from `core_N6_half`.** -/
def s1Dom_N6_half : YMGap.Continuum.S1Dominance.S1Dominance 6 wH 2 :=
  YMGap.Continuum.FusionLogConcave.s1Dominance_of_p2 (by decide) core_N6_half edge6_half

/-! ## 4. The Cauchy–Binet / total-positivity structure (general `N`, axiom-clean)

The box log-concavity is, modally, the TP₂ minor positivity of the theta-weighted
Clebsch kernel.  We make this explicit and uniform in `N`: expand the box cross-
difference as the FULL symmetric quadruple sum of the Cauchy–Binet kernel.  This is the
structural backbone of the LGV/total-positivity route — pure `(Σ)(Σ)=ΣΣ` algebra. -/

/-- The single Clebsch summand `K(a,b,s) = fusionInd a b s · (c_a · c_b)`. -/
def boxKer (w : Q') (s a b : Nat) : Q' := fusionInd a b s * (coeffW w a * coeffW w b)

/-- `boxSum` is the double `fsum` of `boxKer` (definitional). -/
theorem boxSum_eq_ker (w : Q') (N s : Nat) :
    boxSum w N s = fsum (fun a => fsum (fun b => boxKer w s a b) (N + 1)) (N + 1) := rfl

/-- **Single-sum product law** `(Σ f)(Σ g) ≃ Σᵢ Σⱼ f i · g j`. -/
theorem fsum_mul_fsum (f g : Nat → Q') (m n : Nat) :
    (fsum f m * fsum g n).eqv (fsum (fun i => fsum (fun j => f i * g j) n) m) :=
  Q'.eqv_trans _ _ _ (fsum_mul_const f (fsum g n) m)
    (fsum_eqv_congr _ _ (fun i => fsum_const_mul (f i) g n) m)

/-- The Cauchy–Binet quadruple sum `Σ_{a,a',b,b'} K(a,b,s)·K(a',b',t)`. -/
def quadProd (w : Q') (N s t : Nat) : Q' :=
  fsum (fun a => fsum (fun a' => fsum (fun b => fsum (fun b' =>
    boxKer w s a b * boxKer w t a' b') (N + 1)) (N + 1)) (N + 1)) (N + 1)

/-- **The product of two box sums is the Cauchy–Binet quadruple sum.**
`boxSum N s · boxSum N t ≃ quadProd N s t`, uniformly in `N`. -/
theorem boxSum_mul_eq_quad (w : Q') (N s t : Nat) :
    (boxSum w N s * boxSum w N t).eqv (quadProd w N s t) := by
  -- Outer product over `a, a'`.
  have h1 :
      (boxSum w N s * boxSum w N t).eqv
        (fsum (fun a => fsum (fun a' =>
          fsum (fun b => boxKer w s a b) (N + 1) * fsum (fun b' => boxKer w t a' b') (N + 1))
          (N + 1)) (N + 1)) :=
    fsum_mul_fsum (fun a => fsum (fun b => boxKer w s a b) (N + 1))
      (fun a' => fsum (fun b' => boxKer w t a' b') (N + 1)) (N + 1) (N + 1)
  -- Inner product over `b, b'`, threaded through the two outer sums.
  refine Q'.eqv_trans _ _ _ h1 ?_
  refine fsum_eqv_congr _ _ (fun a => ?_) (N + 1)
  refine fsum_eqv_congr _ _ (fun a' => ?_) (N + 1)
  exact fsum_mul_fsum (fun b => boxKer w s a b) (fun b' => boxKer w t a' b') (N + 1) (N + 1)

/-! ### 4a. Generic quadruple-sum `add`/`neg` combinators -/

/-- Depth-1 reverse-add `Σ f + Σ g ≃ Σ (f + g)`. -/
private theorem q1_add (f g : Nat → Q') (n : Nat) :
    (fsum f n + fsum g n).eqv (fsum (fun i => f i + g i) n) :=
  Q'.eqv_symm (fsum_add f g n)

/-- Depth-1 reverse-neg `-(Σ f) ≃ Σ (-f)`. -/
private theorem q1_neg (f : Nat → Q') (n : Nat) :
    (-(fsum f n)).eqv (fsum (fun i => -(f i)) n) :=
  Q'.eqv_symm (fsum_neg f n)

private theorem q2_add (F G : Nat → Nat → Q') (n : Nat) :
    (fsum (fun a => fsum (F a) n) n + fsum (fun a => fsum (G a) n) n).eqv
      (fsum (fun a => fsum (fun b => F a b + G a b) n) n) :=
  Q'.eqv_trans _ _ _ (q1_add (fun a => fsum (F a) n) (fun a => fsum (G a) n) n)
    (fsum_eqv_congr _ _ (fun a => q1_add (F a) (G a) n) n)

private theorem q2_neg (F : Nat → Nat → Q') (n : Nat) :
    (-(fsum (fun a => fsum (F a) n) n)).eqv
      (fsum (fun a => fsum (fun b => -(F a b)) n) n) :=
  Q'.eqv_trans _ _ _ (q1_neg (fun a => fsum (F a) n) n)
    (fsum_eqv_congr _ _ (fun a => q1_neg (F a) n) n)

private theorem q3_add (F G : Nat → Nat → Nat → Q') (n : Nat) :
    (fsum (fun a => fsum (fun b => fsum (F a b) n) n) n
      + fsum (fun a => fsum (fun b => fsum (G a b) n) n) n).eqv
      (fsum (fun a => fsum (fun b => fsum (fun c => F a b c + G a b c) n) n) n) :=
  Q'.eqv_trans _ _ _
    (q1_add (fun a => fsum (fun b => fsum (F a b) n) n)
      (fun a => fsum (fun b => fsum (G a b) n) n) n)
    (fsum_eqv_congr _ _ (fun a => q2_add (F a) (G a) n) n)

private theorem q3_neg (F : Nat → Nat → Nat → Q') (n : Nat) :
    (-(fsum (fun a => fsum (fun b => fsum (F a b) n) n) n)).eqv
      (fsum (fun a => fsum (fun b => fsum (fun c => -(F a b c)) n) n) n) :=
  Q'.eqv_trans _ _ _ (q1_neg (fun a => fsum (fun b => fsum (F a b) n) n) n)
    (fsum_eqv_congr _ _ (fun a => q2_neg (F a) n) n)

private theorem q4_add (F G : Nat → Nat → Nat → Nat → Q') (n : Nat) :
    (fsum (fun a => fsum (fun b => fsum (fun c => fsum (F a b c) n) n) n) n
      + fsum (fun a => fsum (fun b => fsum (fun c => fsum (G a b c) n) n) n) n).eqv
      (fsum (fun a => fsum (fun b => fsum (fun c => fsum (fun d =>
        F a b c d + G a b c d) n) n) n) n) :=
  Q'.eqv_trans _ _ _
    (q1_add (fun a => fsum (fun b => fsum (fun c => fsum (F a b c) n) n) n)
      (fun a => fsum (fun b => fsum (fun c => fsum (G a b c) n) n) n) n)
    (fsum_eqv_congr _ _ (fun a => q3_add (F a) (G a) n) n)

private theorem q4_neg (F : Nat → Nat → Nat → Nat → Q') (n : Nat) :
    (-(fsum (fun a => fsum (fun b => fsum (fun c => fsum (F a b c) n) n) n) n)).eqv
      (fsum (fun a => fsum (fun b => fsum (fun c => fsum (fun d => -(F a b c d)) n) n) n) n) :=
  Q'.eqv_trans _ _ _
    (q1_neg (fun a => fsum (fun b => fsum (fun c => fsum (F a b c) n) n) n) n)
    (fsum_eqv_congr _ _ (fun a => q3_neg (F a) n) n)

/-! ### 4b. The box cross-difference as a single Cauchy–Binet quadruple sum -/

/-- The Cauchy–Binet kernel summand at channel `s`:
`K(a,b,s+1)·K(a',b',s+1) − K(a,b,s)·K(a',b',s+2)`. -/
def quadW (w : Q') (s a a' b b' : Nat) : Q' :=
  boxKer w (s + 1) a b * boxKer w (s + 1) a' b'
    + -(boxKer w s a b * boxKer w (s + 2) a' b')

/-- The Cauchy–Binet quadruple difference: the box cross-difference as ONE quadruple
sum of the kernel `quadW`. -/
def quadDiff (w : Q') (N s : Nat) : Q' :=
  fsum (fun a => fsum (fun a' => fsum (fun b => fsum (fun b' =>
    quadW w s a a' b b') (N + 1)) (N + 1)) (N + 1)) (N + 1)

/-- **`boxDiff_eq_quadDiff` — the box cross-difference IS the Cauchy–Binet quadruple
sum.**  `boxSum(s+1)² − boxSum(s)·boxSum(s+2) ≃ quadDiff N s`, uniformly in `N`.  This
is the explicit total-positivity form: log-concavity ⇔ nonnegativity of the weighted
`2×2` Cauchy–Binet minor sum. -/
theorem boxDiff_eq_quadDiff (w : Q') (N s : Nat) :
    (boxSum w N (s + 1) * boxSum w N (s + 1)
      + -(boxSum w N s * boxSum w N (s + 2))).eqv (quadDiff w N s) := by
  -- Expand both products as quadruple sums.
  have hP : (boxSum w N (s + 1) * boxSum w N (s + 1)).eqv (quadProd w N (s + 1) (s + 1)) :=
    boxSum_mul_eq_quad w N (s + 1) (s + 1)
  have hN : (boxSum w N s * boxSum w N (s + 2)).eqv (quadProd w N s (s + 2)) :=
    boxSum_mul_eq_quad w N s (s + 2)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' hP (Q'.neg_eqv_congr _ _ hN)) ?_
  -- Distribute the negation into the second quadruple sum.
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (quadProd w N (s + 1) (s + 1)) _ _
      (q4_neg (fun a a' b => fun b' => boxKer w s a b * boxKer w (s + 2) a' b') (N + 1))) ?_
  -- Merge the two quadruple sums into one.
  exact q4_add
    (fun a a' b => fun b' => boxKer w (s + 1) a b * boxKer w (s + 1) a' b')
    (fun a a' b => fun b' => -(boxKer w s a b * boxKer w (s + 2) a' b')) (N + 1)

/-! ### 4c. The sharper uniform residual — aggregate Cauchy–Binet positivity -/

/-- **`UniformBoxQuadCertificate w`** — the SHARPER uniform-in-`N` residual: the
aggregate nonnegativity of the Cauchy–Binet quadruple difference for every truncation
`N` and channel `s`, plus the strong-coupling hypothesis.  This is the exact TP₂ /
Karlin total-positivity content of the box log-concavity.

HONESTY.  `quadDiff` is NOT a sum of nonnegative terms — the kernel `quadW` is not
pointwise `≥ 0` — so this residual genuinely requires the Gaussian magnitude decay of
`coeffW` (`coeffW1_le_quarter` and the super-geometric ratio decay), not log-concavity
of the inputs alone.  It is the same heat-kernel local-CLT content as
`UniformBoxLogConcave`, recast in the explicit Cauchy–Binet quadruple form. -/
structure UniformBoxQuadCertificate (w : Q') : Type where
  /-- The strong-coupling hypothesis (`c² ≤ 3`, `c = coeffW w 1`; holds for `w ≤ 1/2`). -/
  strongCoupling : coeffW w 1 * coeffW w 1 ≤ (3 : Q')
  /-- Aggregate nonnegativity of the Cauchy–Binet quadruple difference, for all `N`, `s`. -/
  quadNonneg : ∀ N s, (0 : Q') ≤ quadDiff w N s

/-- **`uniformOfQuad` — the Cauchy–Binet certificate IMPLIES the uniform box log-
concavity residual.**  Aggregate `quadDiff ≥ 0` transports across `boxDiff_eq_quadDiff`
to the box cross-difference, hence `boxSum(s)·boxSum(s+2) ≤ boxSum(s+1)²` for every `N`,
`s`.  A single `UniformBoxQuadCertificate` therefore yields the whole `N`-tower of
`FusionConvLogConcaveCore` (via `coreOfUniform`) and `S1Dominance` (via
`s1DominanceOfUniform`). -/
def uniformOfQuad {w : Q'} (cert : UniformBoxQuadCertificate w) : UniformBoxLogConcave w where
  strongCoupling := cert.strongCoupling
  cauchyBinet := fun N s => by
    have hD : (0 : Q') ≤ boxSum w N (s + 1) * boxSum w N (s + 1)
        + -(boxSum w N s * boxSum w N (s + 2)) :=
      Q'.le_trans' _ _ _ (cert.quadNonneg N s)
        (Q'.ge_of_eqv (boxDiff_eq_quadDiff w N s))
    exact Q'.le_of_sub_nonneg hD

/-! ### 4d. Small-`N` evidence (`w = 1/2`): the certificate fires from the proved cores -/

/-- The Cauchy–Binet quadruple difference is nonnegative at `w = 1/2` for any `N`-core.
From `FusionConvLogConcaveCore N (1/2)` (`cauchyBinet` field), the box cross-difference
is `≥ 0`, and transports to `quadDiff` via `boxDiff_eq_quadDiff`.  Demonstrates the
sharper residual is satisfied wherever the box core is inhabited. -/
theorem quadDiff_nonneg_of_core {N : Nat}
    (core : FusionConvLogConcaveCore N wH (by decide) (by decide)) (s : Nat) :
    (0 : Q') ≤ quadDiff wH N s :=
  Q'.le_trans' _ _ _ (Q'.sub_nonneg_of_le (core.cauchyBinet s))
    (Q'.le_of_eqv (boxDiff_eq_quadDiff wH N s))

/-- Cauchy–Binet positivity witnessed at `N = 5`, `w = 1/2` (all channels), from
`core_N5_half`. -/
theorem quadDiff_nonneg_N5_half (s : Nat) : (0 : Q') ≤ quadDiff wH 5 s :=
  quadDiff_nonneg_of_core core_N5_half s

/-- Cauchy–Binet positivity witnessed at `N = 6`, `w = 1/2` (all channels), from
`core_N6_half`. -/
theorem quadDiff_nonneg_N6_half (s : Nat) : (0 : Q') ≤ quadDiff wH 6 s :=
  quadDiff_nonneg_of_core core_N6_half s

/-! ## 5. The Gaussian magnitude input for the symbolic route -/

/-- **`coeffW1_le_quarter` — `coeffW w 1 ≤ 1/4` on `0 ≤ w ≤ 1/2`.**  Since
`c₁ = coeffW w 1 = dimQ 1 · w^{C₄(1)} = 2·w³` and `w³ ≤ (1/2)³ = 1/8` (`qpow_mono`),
`c₁ ≤ 2·(1/8) = 1/4`.  This is the Gaussian magnitude fact BEYOND log-concavity that the
symbolic high-channel box certificates require (the regime where generic log-concave
counterexamples bite); proved here for reuse by the symbolic `N ≥ 3` certificates. -/
theorem coeffW1_le_quarter {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) :
    coeffW w 1 ≤ Q'.mkPos 1 4 (by decide) := by
  have hstep : coeffW w 1 ≤ dimQ 1 * qpow wH (c4 1) := by
    show dimQ 1 * qpow w (c4 1) ≤ dimQ 1 * qpow wH (c4 1)
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_mono hw0 hw12 (c4 1)) (dimQ_nonneg 1)
  exact Q'.le_trans' _ _ _ hstep (by decide)

/-! ## 6. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `boxSum5_tail`, `boxSum6_tail` — the mode tails.
  * `core_N5_half`, `core_N6_half` — the DIRECT box Cauchy–Binet core INHABITED at
    `w = 1/2` for `N = 5` and `N = 6` (the genuine `N = 4 → 5 → 6` lift).
  * `edge5_half`, `edge6_half`, `s1Dom_N5_half`, `s1Dom_N6_half` — wired to
    `S1Dominance {5,6} (1/2) 2`.
  * `fsum_mul_fsum`, `boxSum_mul_eq_quad` — the product-of-box-sums = Cauchy–Binet
    quadruple sum (uniform in `N`).
  * `quadDiff`, `boxDiff_eq_quadDiff` — the box cross-difference as ONE symmetric
    quadruple sum of the Cauchy–Binet kernel `quadW` (the explicit TP₂ minor form).
  * `UniformBoxQuadCertificate`, `uniformOfQuad` — the sharper uniform residual
    (aggregate Cauchy–Binet positivity) and the proof that it implies
    `UniformBoxLogConcave` (hence the whole `N`-tower of cores and `S1Dominance`).
  * `quadDiff_nonneg_of_core`, `quadDiff_nonneg_N5_half`, `quadDiff_nonneg_N6_half` —
    the certificate is SATISFIED at `w = 1/2`, `N = 0,…,6` (small-`N` evidence).
  * `coeffW1_le_quarter` — the Gaussian magnitude input `c₁ ≤ 1/4` for the symbolic route.

NAMED OPEN:
  * Inhabitation of `UniformBoxQuadCertificate w` (equivalently `UniformBoxLogConcave w`)
    for the symbolic strong-coupling family `0 < w ≤ 1/2` — the aggregate Cauchy–Binet
    positivity `quadDiff ≥ 0` for ALL `N` and `s`.  This is NOT pointwise (the kernel
    `quadW` is not `≥ 0`); it requires the Gaussian magnitude decay (`coeffW1_le_quarter`
    + ratio decay), i.e. the heat-kernel `(r,d)` local-CLT, NOT a finite rational
    inequality.  Inhabited pointwise at `N = 0,…,6` (`w = 1/2`).
  * The symbolic `N = 3, 4` per-channel SOS certificates (the analogues of the proved
    `polyI0`/`polyI1`/`polyI2` at `N = 2`).  Their required Gaussian magnitude input
    `coeffW1_le_quarter` is now available; the high-channel certificates remain open.

HONEST VERDICT.  Round B pushes the direct box Cauchy–Binet core two further levels
(`N = 5, 6` at `w = 1/2`), makes the LGV/total-positivity structure of the box log-
concavity EXPLICIT and uniform in `N` (the box cross-difference IS a single weighted
Cauchy–Binet quadruple sum), and packages the sharper residual `UniformBoxQuadCertificate`
with the proof that it drives the whole `N`-tower — plus the Gaussian magnitude input
`coeffW1_le_quarter` for the symbolic route.  This is a structural advance on one box-
level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundB

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundB.boxSum5_tail
#print axioms YMGap.Continuum.FusionCoreStepRoundB.boxSum6_tail
#print axioms YMGap.Continuum.FusionCoreStepRoundB.core_N5_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.core_N6_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.edge5_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.edge6_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.s1Dom_N5_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.s1Dom_N6_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.fsum_mul_fsum
#print axioms YMGap.Continuum.FusionCoreStepRoundB.boxSum_mul_eq_quad
#print axioms YMGap.Continuum.FusionCoreStepRoundB.boxDiff_eq_quadDiff
#print axioms YMGap.Continuum.FusionCoreStepRoundB.uniformOfQuad
#print axioms YMGap.Continuum.FusionCoreStepRoundB.quadDiff_nonneg_of_core
#print axioms YMGap.Continuum.FusionCoreStepRoundB.quadDiff_nonneg_N5_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.quadDiff_nonneg_N6_half
#print axioms YMGap.Continuum.FusionCoreStepRoundB.coeffW1_le_quarter
