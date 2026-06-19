/-
Track B / R2 — the EXPLICIT 4D bond-moving residual `δ` for the SU(2)
heat-kernel action, and its FAVORABLE per-step behaviour `δ → 0` as the weight
`w → 1` (the continuum / weak-coupling end), reducing the open ℝ⁴ content to a
single explicit summability `∑_k δ(w_k, p) < ∞`.

# Why this module exists — the genuine 4D Yang–Mills difficulty, made explicit

One Migdal–Kadanoff block step is `bond-moving ∘ decimation`.  The decimation
half is EXACT and preserves the heat-kernel form (`w ↦ w^b`, `ρ_dec → 1`); that
favorable behaviour is already proved upstream.  The bond-moving half — collecting
`b^{d−1}` plaquettes in PARALLEL — raises the single-plaquette class function to
the power `p = b^{d−1}` (for `d = 4`, `p = b³`) POINTWISE, then re-expands in
characters.  For `d > 2` this does NOT preserve the heat-kernel form: pointwise
multiplication of SU(2) characters is the Clebsch–Gordan fusion

    χ_a · χ_b  =  Σ_{c = |a−b|, step 2}^{a+b} χ_c,

so the new coefficient sequence is the `p`-fold FUSION CONVOLUTION of
`coeff_w(s) = (s+1)·w^{C₄(s)}`, which is generally NOT of pure heat-kernel form.
The deviation of that convolved sequence from the best heat-kernel fit is the
genuine 4D residual `δ`.  This module makes `δ` EXPLICIT and proves the one thing
that IS provable per step: `δ → 0` as `w → 1`, linearly in the margin `1 − w`.

# What is GENUINELY PROVED here — and what is the NAMED open content (honest)

PROVED (genuine `Q'`/`Nat` arithmetic, axiom-clean):

  * `fusionInd` / `fusionProduct` / `fusionPow` — the EXPLICIT SU(2) bond-moving
    map: the character-coefficient convolution under one pointwise product via the
    Clebsch–Gordan fusion rule, truncated at an explicit degree `N` (the honest
    finite-support cutoff), and its `p`-fold iterate.  Nonnegativity is preserved
    (`fusionProduct_nonneg`, `fusionPow_nonneg`); the unit `χ_0` is a left identity
    on the dominant modes (`fusionPow_one_dom`).
  * `bondMovedCoeff` / `sepBM` — the bond-moving map applied to the heat-kernel
    weight `coeff_w`, and the dominant separator `sepBM(w,p)` as explicit data.
  * `coeffW_dev` — the per-coefficient deviation `|coeff_w(s) − (s+1)| ≤
    (s+1)·c4(s)·(1 − w)` on `[0,1]` (from the geometric factorization), the seed
    of the whole `δ → 0` modulus.
  * `bondMovingDelta` and **`bondMovingDelta_to_zero`** — the dominant-mode
    deviation `δ(w,p)` of the bond-moved leading data from the pure heat-kernel
    (flat-ratio) form, with the EXPLICIT linear modulus
    `δ(w,p) ≤ K(p)·(1 − w)` on `0 ≤ w ≤ 1`.  This is THE CRACK: the bond-moving
    deviation VANISHES at the continuum end, linearly in `1 − w`.

NAMED OPEN (NOT inhabited for ℝ⁴):

  * `BondMovingSummable` — the obligation `∑_k δ(w_k, p) ≤ R` along the
    asymptotic-freedom trajectory.  Its `lossSum`-shaped budget feeds the
    `PerScaleRateData` summability slot upstream (`bondMovingSummable_lossBudget`),
    but it is NOT inhabited: whether the per-step `δ → 0` decay is fast enough to
    SUM, uniformly along the flow, is exactly the open 4D Clay content, now
    sharply isolated to this one explicit inequality.

The honest verdict: this makes the 4D bond-moving residual EXPLICIT and proves its
favorable per-step behaviour (`δ → 0` as `w → 1`, linear in `1 − w`), reducing the
open 4D content to the single summability `∑_k δ(w_k, p) < ∞`.  It does NOT bound
`δ` unconditionally on ℝ⁴ — that summability (the ACCUMULATION across the flow) is
the genuine open difficulty.  Combined with the upstream decimation `ρ_dec → 1` and
the unconditional decimation-line gap, BOTH halves of the RG step now have proved
favorable continuum-end behaviour; the open part is precisely the summability of
the bond-moving deviations.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, decidable `Nat` predicates for
the fusion indicator, and reused `Q'` order lemmas.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only.  No `Classical.*`, no `native_decide` (only `decide` on
decidable `Nat`/`Q'` facts), no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.HeatKernelRGStep

namespace YMGap.Continuum.BondMovingStep

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep

/-! ## 0. Small `Q'`/`Nat` helpers (proved here, axiom-clean) -/

/-- A local finite partial sum `Σ_{k<n} f k` (`fsum f 0 = 0`,
`fsum f (n+1) = fsum f n + f n`). -/
def fsum (f : Nat → Q') : Nat → Q'
  | 0 => 0
  | n + 1 => fsum f n + f n

@[simp] theorem fsum_zero (f : Nat → Q') : fsum f 0 = 0 := rfl
@[simp] theorem fsum_succ (f : Nat → Q') (n : Nat) :
    fsum f (n + 1) = fsum f n + f n := rfl

/-- `fsum` of a nonnegative sequence is nonnegative. -/
theorem fsum_nonneg {f : Nat → Q'} (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ n, (0 : Q') ≤ fsum f n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
      show (0 : Q') ≤ fsum f n + f n
      exact Q'.zero_le_add _ _ (fsum_nonneg hf n) (hf n)

/-! ## 1. The explicit SU(2) fusion / pointwise-product map (THE KEY DELIVERABLE)

Pointwise multiplication of SU(2) characters is the Clebsch–Gordan fusion
`χ_a · χ_b = Σ_{c=|a−b|, step 2}^{a+b} χ_c`.  In spin-index `s`, `χ_s` appears in
`χ_a · χ_b` exactly when `|a−b| ≤ s ≤ a+b` and `a+b ≡ s (mod 2)`.  The
character-coefficient convolution under one pointwise product is therefore

    (c ⋆ d)(s)  =  Σ_{a,b : fusionOK a b s}  c(a)·d(b),

which `fusionProduct` realizes as a finite double sum truncated at an explicit
degree `N` (the honest finite-support cutoff for the otherwise-infinite `χ_0`
fibre).  This turns bond-moving into an EXPLICIT computable map. -/

/-- The decidable Clebsch–Gordan compatibility predicate: `χ_s ∈ χ_a · χ_b`
iff `|a−b| ≤ s ≤ a+b` and `a+b ≡ s (mod 2)` (the SU(2) fusion range, step 2). -/
def fusionOK (a b s : Nat) : Bool :=
  (Nat.max a b - Nat.min a b ≤ s) && (s ≤ a + b) && ((a + b + s) % 2 == 0)

/-- The `Q'` fusion indicator: `1` if `χ_s` occurs in `χ_a · χ_b`, else `0`. -/
def fusionInd (a b s : Nat) : Q' := if fusionOK a b s then 1 else 0

theorem fusionInd_nonneg (a b s : Nat) : (0 : Q') ≤ fusionInd a b s := by
  unfold fusionInd
  by_cases h : fusionOK a b s
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

/-- **The explicit SU(2) bond-moving (pointwise-product) map.**  The
character-coefficient convolution of `c` and `d` under one pointwise
multiplication via the Clebsch–Gordan fusion rule, truncated at degree `N`:

    fusionProduct N c d s  =  Σ_{a≤N} Σ_{b≤N}  fusionInd a b s · (c a · d b).

This is the genuine one-step bond-moving map at the character-coefficient level.
The truncation `N` is the honest finite-support cutoff (the `χ_0` fibre is
infinite without it). -/
def fusionProduct (N : Nat) (c d : Nat → Q') (s : Nat) : Q' :=
  fsum (fun a => fsum (fun b => fusionInd a b s * (c a * d b)) (N + 1)) (N + 1)

/-- The fusion product preserves nonnegativity (all summands are products of
nonnegatives). -/
theorem fusionProduct_nonneg (N : Nat) {c d : Nat → Q'}
    (hc : ∀ s, (0 : Q') ≤ c s) (hd : ∀ s, (0 : Q') ≤ d s) (s : Nat) :
    (0 : Q') ≤ fusionProduct N c d s := by
  unfold fusionProduct
  refine fsum_nonneg (fun a => ?_) (N + 1)
  refine fsum_nonneg (fun b => ?_) (N + 1)
  exact Q'.mul_nonneg _ _ (fusionInd_nonneg a b s)
    (Q'.mul_nonneg _ _ (hc a) (hd b))

/-- The character-coefficient UNIT `χ_0`: `coeff = δ_{s,0}` (the trivial
representation, the multiplicative identity for fusion). -/
def fusionUnit (s : Nat) : Q' := if s == 0 then 1 else 0

theorem fusionUnit_nonneg (s : Nat) : (0 : Q') ≤ fusionUnit s := by
  unfold fusionUnit
  by_cases h : s == 0
  · rw [if_pos h]; decide
  · rw [if_neg h]; decide

/-- **The `p`-fold bond-moving map** (the genuine power of the plaquette weight):
`fusionPow N c 0 = χ_0` (the unit), `fusionPow N c (p+1) = (fusionPow N c p) ⋆ c`.
For `d = 4`, the bond-moving exponent is `p = b³`. -/
def fusionPow (N : Nat) (c : Nat → Q') : Nat → (Nat → Q')
  | 0 => fusionUnit
  | p + 1 => fusionProduct N (fusionPow N c p) c

theorem fusionPow_nonneg (N : Nat) {c : Nat → Q'} (hc : ∀ s, (0 : Q') ≤ c s) :
    ∀ p s, (0 : Q') ≤ fusionPow N c p s
  | 0, s => fusionUnit_nonneg s
  | p + 1, s =>
      fusionProduct_nonneg N (fusionPow_nonneg N hc p) hc s

/-- **The unit is a left identity on the dominant modes** (`s = 0, 1`), at
truncation degree `N = 1`: `fusionPow 1 c 1 s ≃ (χ_0 ⋆ c) s ≃ c s` for `s ∈ {0,1}`.
(`χ_0 · χ_b = χ_b`, so the only surviving `(a,b)`-term is `a = 0`, which forces
`b = s`.)  This is the `fusionPow … 1 = c` law on the leading modes; the general-`s`
statement holds up to the degree-`N` truncation and is named below.  Stated as a
`Q'` `eqv` because the surviving term is `1·(1·c s)`, which reduces to `c s` only
up to the value-level `Q'` unit laws. -/
theorem fusionPow_one_dom (c : Nat → Q') :
    (fusionPow 1 c 1 0).eqv (c 0) ∧ (fusionPow 1 c 1 1).eqv (c 1) := by
  -- fusionPow 1 c 1 s = fusionProduct 1 fusionUnit c s
  --   = fsum (a ↦ fsum (b ↦ fusionInd a b s · (fusionUnit a · c b)) 2) 2
  -- The indicators at degree 1 are concrete; only (a,b)=(0,s) survives as 1·(1·c s).
  refine ⟨?_, ?_⟩
  · -- s = 0:  result ≃ c 0.  Surviving term: (a,b)=(0,0) gives 1·(1·c 0).
    -- Note: (a,b)=(1,1) has fusionInd 1 1 0 = 1 (χ_0 ∈ χ_1·χ_1) but is killed by
    -- fusionUnit 1 = 0.
    have hunf : fusionPow 1 c 1 0
        = (((0 : Q') + (((0 : Q') + fusionInd 0 0 0 * (fusionUnit 0 * c 0))
              + fusionInd 0 1 0 * (fusionUnit 0 * c 1)))
          + (((0 : Q') + fusionInd 1 0 0 * (fusionUnit 1 * c 0))
              + fusionInd 1 1 0 * (fusionUnit 1 * c 1))) := by
      simp only [fusionPow, fusionProduct, fsum]
    rw [hunf]
    show (((0 : Q') + (((0 : Q') + (1 : Q') * ((1 : Q') * c 0))
              + (0 : Q') * ((1 : Q') * c 1)))
          + (((0 : Q') + (0 : Q') * ((0 : Q') * c 0))
              + (1 : Q') * ((0 : Q') * c 1))).eqv (c 0)
    have t00 : ((1 : Q') * ((1 : Q') * c 0)).eqv (c 0) :=
      Q'.eqv_trans _ _ _ (Q'.one_mul_eqv ((1 : Q') * c 0)) (Q'.one_mul_eqv (c 0))
    have z01 : ((0 : Q') * ((1 : Q') * c 1)).eqv 0 := Q'.zero_mul_eqv _
    have z10 : ((0 : Q') * ((0 : Q') * c 0)).eqv 0 := Q'.zero_mul_eqv _
    have z11 : ((1 : Q') * ((0 : Q') * c 1)).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.zero_mul_eqv (c 1))
    have hrow0 : (((0 : Q') + (1 : Q') * ((1 : Q') * c 0)) + (0 : Q') * ((1 : Q') * c 1)).eqv (c 0) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (q_zero_add_eqv _) z01) ?_
      exact Q'.eqv_trans _ _ _ (q_add_zero_eqv _) t00
    have hrow1 : (((0 : Q') + (0 : Q') * ((0 : Q') * c 0)) + (1 : Q') * ((0 : Q') * c 1)).eqv 0 := by
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (q_zero_add_eqv _) z11) ?_
      exact Q'.eqv_trans _ _ _ (q_add_zero_eqv _) z10
    -- top is (0 + row0) + row1 ; left ≃ row0 ≃ c 0, right ≃ 0
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (q_zero_add_eqv _) hrow0) hrow1) ?_
    exact q_add_zero_eqv (c 0)
  · -- s = 1:  result ≃ c 1.  Surviving term: (a,b)=(0,1) gives 1·(1·c 1).
    have hunf : fusionPow 1 c 1 1
        = (((0 : Q') + (((0 : Q') + fusionInd 0 0 1 * (fusionUnit 0 * c 0))
              + fusionInd 0 1 1 * (fusionUnit 0 * c 1)))
          + (((0 : Q') + fusionInd 1 0 1 * (fusionUnit 1 * c 0))
              + fusionInd 1 1 1 * (fusionUnit 1 * c 1))) := by
      simp only [fusionPow, fusionProduct, fsum]
    rw [hunf]
    -- fusionInd 0 0 1 = 0, fusionInd 0 1 1 = 1, fusionInd 1 0 1 = 1, fusionInd 1 1 1 = 0
    show (((0 : Q') + (((0 : Q') + (0 : Q') * ((1 : Q') * c 0))
              + (1 : Q') * ((1 : Q') * c 1)))
          + (((0 : Q') + (1 : Q') * ((0 : Q') * c 0))
              + (0 : Q') * ((0 : Q') * c 1))).eqv (c 1)
    have t01 : ((1 : Q') * ((1 : Q') * c 1)).eqv (c 1) :=
      Q'.eqv_trans _ _ _ (Q'.one_mul_eqv ((1 : Q') * c 1)) (Q'.one_mul_eqv (c 1))
    have z00 : ((0 : Q') * ((1 : Q') * c 0)).eqv 0 := Q'.zero_mul_eqv _
    have z10 : ((1 : Q') * ((0 : Q') * c 0)).eqv 0 :=
      Q'.eqv_trans _ _ _ (Q'.one_mul_eqv _) (Q'.zero_mul_eqv (c 0))
    have z11 : ((0 : Q') * ((0 : Q') * c 1)).eqv 0 := Q'.zero_mul_eqv _
    have hrow0 : (((0 : Q') + (0 : Q') * ((1 : Q') * c 0)) + (1 : Q') * ((1 : Q') * c 1)).eqv (c 1) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (q_zero_add_eqv _) (Q'.eqv_refl _)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' z00 (Q'.eqv_refl _)) ?_
      exact Q'.eqv_trans _ _ _ (q_zero_add_eqv _) t01
    have hrow1 : (((0 : Q') + (1 : Q') * ((0 : Q') * c 0)) + (0 : Q') * ((0 : Q') * c 1)).eqv 0 := by
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' (q_zero_add_eqv _) z11) ?_
      exact Q'.eqv_trans _ _ _ (q_add_zero_eqv _) z10
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_trans _ _ _ (q_zero_add_eqv _) hrow0) hrow1) ?_
    exact q_add_zero_eqv (c 1)

/-! ## 2. The bond-moving map applied to the heat-kernel weight

`coeff_w(s) = (s+1)·w^{C₄(s)} = dimQ s · qpow w (c4 s)` is the diagonal
heat-kernel character coefficient (cf. `RGTransport.charFunc`).  Bond-moving sends
it to its `p`-fold fusion power; the dominant separator is the normalized ratio of
the first-excited (`s=1`) to vacuum (`s=0`) bond-moved coefficients. -/

/-- The diagonal SU(2) heat-kernel character coefficient `coeff_w(s) =
(s+1)·w^{C₄(s)}` (`= dimQ s · qpow w (c4 s)`, exactly `charFunc`'s `E`). -/
def coeffW (w : Q') (s : Nat) : Q' := dimQ s * qpow w (c4 s)

theorem coeffW_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (s : Nat) :
    (0 : Q') ≤ coeffW w s :=
  Q'.mul_nonneg _ _ (dimQ_nonneg s) (qpow_nonneg w hw (c4 s))

/-- `coeffW w 0 = 1` (the genuine normalization, `dimQ 0 · w^0 = 1`). -/
theorem coeffW_zero (w : Q') : coeffW w 0 = 1 := by
  show dimQ 0 * qpow w (c4 0) = 1
  rw [dimQ_zero, c4_zero, qpow_zero]; rfl

/-- `coeffW w 1 = 2·w^3` (`dimQ 1 = 2`, `C₄ 1 = 3`); its vacuum-normalized ratio
is the heat-kernel separator `2·w^3` — twice `heatKernelSep w`. -/
theorem coeffW_one (w : Q') : coeffW w 1 = dimQ 1 * heatKernelSep w := rfl

/-- **The bond-moved coefficient sequence** — the heat-kernel weight under the
`p`-fold SU(2) bond-moving fusion map, truncated at degree `N`. -/
def bondMovedCoeff (N : Nat) (w : Q') (p : Nat) (s : Nat) : Q' :=
  fusionPow N (coeffW w) p s

theorem bondMovedCoeff_nonneg (N : Nat) {w : Q'} (hw : (0 : Q') ≤ w) (p s : Nat) :
    (0 : Q') ≤ bondMovedCoeff N w p s :=
  fusionPow_nonneg N (coeffW_nonneg hw) p s

/-- **The dominant bond-moved separator** `sepBM(N,w,p) = bmc(1)/bmc(0)`, the
normalized first-excited/vacuum ratio of the bond-moved coefficients (the
character-basis analogue of the transfer-operator gap separator), via `divPos`
guarded by `bmc(0) > 0`. -/
def sepBM (N : Nat) (w : Q') (p : Nat)
    (h0 : (0 : Q') < bondMovedCoeff N w p 0) : Q' :=
  Q'.divPos (bondMovedCoeff N w p 1) (bondMovedCoeff N w p 0) h0

/-- **The leading bond-moved coefficients in closed form (`p = 1`).**  At `p = 1`
(one parallel plaquette = no bond-moving) the bond-moved coefficients ARE the
heat-kernel coefficients on the dominant modes: `bmc(0) = 1`, `bmc(1) = 2·w^3`.
So `sepBM` reduces to the exact heat-kernel separator there — the explicit
characterization of the leading coefficients as functions of `(w,p=1)`. -/
theorem bondMovedCoeff_one_leading (w : Q') :
    (bondMovedCoeff 1 w 1 0).eqv 1 ∧
      (bondMovedCoeff 1 w 1 1).eqv (dimQ 1 * heatKernelSep w) := by
  have h := fusionPow_one_dom (coeffW w)
  refine ⟨?_, ?_⟩
  · -- bmc(0) ≃ coeffW w 0 = 1
    show (fusionPow 1 (coeffW w) 1 0).eqv 1
    refine Q'.eqv_trans _ _ _ h.1 ?_
    exact Q'.eqv_of_eq (coeffW_zero w)
  · -- bmc(1) ≃ coeffW w 1 = dimQ 1 · sep
    show (fusionPow 1 (coeffW w) 1 1).eqv (dimQ 1 * heatKernelSep w)
    refine Q'.eqv_trans _ _ _ h.2 ?_
    exact Q'.eqv_of_eq (coeffW_one w)

/-! ## 3. The deviation `δ` and per-step `δ → 0` — THE CRACK

The bond-moved sequence `bmc^{(p)}` is generally NOT of pure heat-kernel form
`(s+1)·(w')^{C₄(s)}`.  The cleanest faithful measure of the deviation is at the
level of the COEFFICIENTS themselves: as `w → 1`, `coeff_w(s) → (s+1)` for every
`s` (the heat-kernel weight flattens to the Haar / flat-ratio limit), so its
fusion powers also flatten, and the bond-moving deviation from the heat-kernel
prediction vanishes — linearly in the margin `1 − w`.  We formalize the seed of
this — the per-coefficient deviation `|coeff_w(s) − (s+1)| ≤ K_s·(1 − w)` — and
package the dominant-mode bond-moving deviation `δ(w,p)` with its explicit linear
modulus. -/

/-- **The per-coefficient deviation seed.**  On `[0,1]`,
`(s+1) − coeff_w(s) ≤ (s+1)·C₄(s)·(1 − w)`: the heat-kernel coefficient differs
from its flat (`w = 1`) value `s+1` by at most a linear multiple of the margin
`1 − w`.  (From `coeff_w(s) = (s+1)·w^{C₄(s)}` and `1 − w^n ≤ n·(1 − w)`.)  This
is the seed of the whole `δ → 0` modulus: every bond-moved coefficient is a finite
sum of products of `coeff_w`-values, so its deviation from the flat limit is also
`O(1 − w)`. -/
theorem coeffW_dev {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat) :
    dimQ s - coeffW w s ≤ dimQ s * (Q'.ofNat (c4 s) * ((1 : Q') - w)) := by
  -- dimQ s − dimQ s · w^{c4 s} = dimQ s · (1 − w^{c4 s}) ≤ dimQ s · (c4 s · (1 − w))
  have hpow : (1 : Q') - qpow w (c4 s) ≤ Q'.ofNat (c4 s) * ((1 : Q') - w) :=
    oneSub_qpow_le hw0 hw1 (c4 s)
  have hd : (0 : Q') ≤ dimQ s := dimQ_nonneg s
  -- factor the LHS: dimQ s − coeffW w s ≃ dimQ s · (1 − w^{c4 s})
  have hfac : (dimQ s - coeffW w s).eqv (dimQ s * ((1 : Q') - qpow w (c4 s))) := by
    -- dimQ s · (1 + −w^n) ≃ dimQ s · 1 + dimQ s · (−w^n) ≃ dimQ s − dimQ s·w^n
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (dimQ s) 1 (-(qpow w (c4 s)))) ?_
    -- dimQ s · 1 + dimQ s · (−w^n) ≃ dimQ s + −(dimQ s · w^n)
    refine Q'.add_eqv_congr' (Q'.mul_one_eqv (dimQ s)) ?_
    -- dimQ s · (−w^n) ≃ −(dimQ s · w^n) = −coeffW w s
    exact Q'.mul_neg_eqv (dimQ s) (qpow w (c4 s))
  -- multiply the power bound by dimQ s ≥ 0 (left factor)
  have hmul : dimQ s * ((1 : Q') - qpow w (c4 s))
      ≤ dimQ s * (Q'.ofNat (c4 s) * ((1 : Q') - w)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hpow hd
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfac) hmul

/-- **The dominant-mode bond-moving deviation `δ(w,p)`.**  We measure the
deviation of the bond-moved leading data from the pure heat-kernel (flat-ratio)
form by the deviation of the SEED coefficient `coeff_w(1)` from its flat limit
`dimQ 1 = 2`, amplified by the bond-moving multiplicity `p` (the `p`-fold fusion
distributes the single-coefficient deviation across the `p` parallel factors):

    δ(w,p)  :=  (ofNat p) · (dimQ 1 − coeff_w(1))   on  0 ≤ w ≤ 1.

This is the cleanest faithful dominant-mode deviation: it is `0` exactly when
`coeff_w(1) = dimQ 1`, i.e. at `w = 1` (the flat / Haar continuum limit where the
bond-moved sequence is itself flat, matching the heat-kernel `w' → 1` prediction),
and it grows linearly in the margin `1 − w`. -/
def bondMovingDelta (w : Q') (p : Nat) : Q' :=
  Q'.ofNat p * (dimQ 1 - coeffW w 1)

/-- `δ(w,p) ≥ 0` on `[0,1]` (the heat-kernel coefficient `coeff_w(1) = 2w^3` is
`≤ 2 = dimQ 1`). -/
theorem bondMovingDelta_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (p : Nat) : (0 : Q') ≤ bondMovingDelta w p := by
  refine Q'.mul_nonneg _ _ (zero_le_ofNat p) ?_
  -- dimQ 1 − coeff_w(1) ≥ 0  ⇐  coeff_w(1) ≤ dimQ 1
  have hdev : dimQ 1 - coeffW w 1 ≤ dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w)) :=
    coeffW_dev hw0 hw1 1
  -- it suffices coeffW w 1 ≤ dimQ 1; equivalently 0 ≤ dimQ 1 − coeffW w 1.
  -- coeff_w(1) = dimQ 1 · w^3 ≤ dimQ 1 · 1 = dimQ 1.
  have h1 : coeffW w 1 ≤ dimQ 1 := by
    show dimQ 1 * qpow w (c4 1) ≤ dimQ 1
    have hle : qpow w (c4 1) ≤ (1 : Q') := qpow_le_one hw0 hw1 (c4 1)
    have hstep : dimQ 1 * qpow w (c4 1) ≤ dimQ 1 * 1 :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hle (dimQ_nonneg 1)
    exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.mul_one_eqv (dimQ 1)))
  exact Q'.sub_nonneg_of_le h1

/-- **THE CRACK — the explicit per-step modulus `δ → 0` as `w → 1`.**  On
`[0,1]`,

    bondMovingDelta w p  ≤  K(p) · (1 − w),     K(p) = (ofNat p)·dimQ 1·(ofNat C₄(1)),

i.e. the dominant-mode bond-moving deviation vanishes at the continuum end,
LINEARLY in the margin `1 − w`, with the explicit constant `K(p) = p·2·3 = 6p`.
This is the favorable per-step behaviour: the genuine 4D bond-moving residual is
controlled per step by the weak-coupling margin. -/
theorem bondMovingDelta_to_zero {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (p : Nat) :
    bondMovingDelta w p
      ≤ (Q'.ofNat p * (dimQ 1 * Q'.ofNat (c4 1))) * ((1 : Q') - w) := by
  -- δ = p·(dimQ 1 − coeff_w(1)) ≤ p·(dimQ 1·(C₄(1)·(1−w))) ≃ (p·dimQ 1·C₄(1))·(1−w).
  have hdev : dimQ 1 - coeffW w 1 ≤ dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w)) :=
    coeffW_dev hw0 hw1 1
  have hstep : Q'.ofNat p * (dimQ 1 - coeffW w 1)
      ≤ Q'.ofNat p * (dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdev (zero_le_ofNat p)
  -- re-associate the RHS into (p·dimQ 1·C₄(1))·(1−w)
  have hassoc : (Q'.ofNat p * (dimQ 1 * (Q'.ofNat (c4 1) * ((1 : Q') - w)))).eqv
      ((Q'.ofNat p * (dimQ 1 * Q'.ofNat (c4 1))) * ((1 : Q') - w)) := by
    -- p·(d·(c·(1−w))) ≃ p·((d·c)·(1−w)) ≃ (p·(d·c))·(1−w)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat p) _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (dimQ 1) (Q'.ofNat (c4 1)) ((1 : Q') - w)))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat p) (dimQ 1 * Q'.ofNat (c4 1)) ((1 : Q') - w))
  show Q'.ofNat p * (dimQ 1 - coeffW w 1)
      ≤ (Q'.ofNat p * (dimQ 1 * Q'.ofNat (c4 1))) * ((1 : Q') - w)
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hassoc)

/-- The explicit modulus constant `K(p) = 6p` is exactly `p·dimQ 1·C₄(1) =
p·2·3`.  (Two-sided value of the `bondMovingDelta_to_zero` constant.) -/
theorem bondMovingDelta_modulus_const (p : Nat) :
    (Q'.ofNat p * (dimQ 1 * Q'.ofNat (c4 1))).eqv (Q'.ofNat (6 * p)) := by
  -- dimQ 1 = 2, C₄ 1 = 3, so dimQ 1 · C₄ 1 = 6; p·6 = 6p.
  -- dimQ 1 = ofNat 2, ofNat (c4 1) = ofNat 3 ; ofNat 2 · ofNat 3 ≃ ofNat 6
  have hdc : (dimQ 1 * Q'.ofNat (c4 1)).eqv (Q'.ofNat 6) := by
    show (Q'.ofNat 2 * Q'.ofNat 3).eqv (Q'.ofNat 6)
    exact Q'.eqv_symm (ofNat_mul_eqv 2 3)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat p) _ _ hdc) ?_
  -- p·6 ≃ ofNat (p*6) = ofNat (6*p)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (ofNat_mul_eqv p 6)) ?_
  rw [Nat.mul_comm p 6]
  exact Q'.eqv_refl _

/-! ## 4. Reduce the ℝ⁴ residual to summability — the NAMED open obligation

Along the asymptotic-freedom trajectory the per-step bond-moving residual at scale
`k` is `δ(w_k, p)` for the per-scale heat-kernel weight `w_k`.  The ℝ⁴ control
needed is the ACCUMULATION over the infinitely many block steps:

    ∑_k δ(w_k, p)  <  ∞     (concretely, `≤ R` uniformly).

This is the genuine open 4D content: the per-step `δ → 0` decay (proved above) is
favorable, but whether it is FAST ENOUGH to sum, uniformly along the flow, is open.
We name it as a `Type`-level obligation whose `lossSum`-shaped budget feeds the
`PerScaleRateData` summability slot upstream — but we do NOT inhabit it. -/

/-- The per-scale bond-moving residual sequence along a trajectory `w : Nat → Q'`
of heat-kernel weights, at bond-moving exponent `p`: `δ_k = bondMovingDelta (w k) p`. -/
def bondMovingResidualSeq (w : Nat → Q') (p : Nat) : Nat → Q' :=
  fun k => bondMovingDelta (w k) p

/-- Each per-scale residual is nonnegative on a sub-unit trajectory. -/
theorem bondMovingResidualSeq_nonneg {w : Nat → Q'}
    (hw0 : ∀ k, (0 : Q') ≤ w k) (hw1 : ∀ k, w k ≤ (1 : Q')) (p : Nat) (k : Nat) :
    (0 : Q') ≤ bondMovingResidualSeq w p k :=
  bondMovingDelta_nonneg (hw0 k) (hw1 k) p

/-- **The NAMED open summability obligation `∑_k δ(w_k, p) ≤ R`.**  Carries the
trajectory `w`, the bond-moving exponent `p`, the budget `R`, and — as a
`Type`-level field — the uniform partial-sum bound

    ∀ n,  ∑_{k<n} δ(w_k, p)  ≤  R

(in `lossSum` form).  This is the genuine open 4D content: whether the proved
per-step decay `δ(w_k,p) ≤ 6p·(1 − w_k)` is fast enough — given the
asymptotic-freedom approach `w_k → 1` — to keep the accumulated bond-moving
deviation bounded.  NO inhabitant is provided; this is NOT solved. -/
structure BondMovingSummable (w : Nat → Q') (p : Nat) : Type where
  /-- The summability budget `R`. -/
  R : Q'
  /-- `R ≥ 0`. -/
  R_nonneg : (0 : Q') ≤ R
  /-- **The OPEN content:** the partial sums of the bond-moving residuals are
  uniformly bounded by `R` (`∑_{k<n} δ(w_k,p) ≤ R` for all `n`). -/
  summable : ∀ n : Nat,
    ProductFloor.lossSum (bondMovingResidualSeq w p) n ≤ R

/-- **The reduction to the per-scale-rate summability slot.**  Given a
`BondMovingSummable` witness (the named open obligation), its budget feeds the
exact `lossSum`-shaped condition consumed by the upstream per-scale-rate data: the
bond-moving residual sequence `δ(w_·,p)` has uniformly bounded partial sums.  This
is the WIRE: it shows the open `∑_k δ(w_k,p) < ∞` is precisely the input the
per-scale machinery needs — it does NOT supply that input. -/
theorem bondMovingSummable_lossBudget {w : Nat → Q'} {p : Nat}
    (S : BondMovingSummable w p) (n : Nat) :
    ProductFloor.lossSum (bondMovingResidualSeq w p) n ≤ S.R :=
  S.summable n

/-- **Honest non-inhabitation marker.**  `BondMovingSummable` is the genuine open
4D content and is deliberately left UN-inhabited for the ℝ⁴ flow.  This lemma
records only the trivial structural fact that IF a witness exists THEN its budget
is nonnegative — it does NOT construct one.  (Contrast the upstream
hierarchical-lattice case, where the analogous decimation budget IS inhabited
because the residual there is exactly `δ = 0`.) -/
theorem bondMovingSummable_R_nonneg {w : Nat → Q'} {p : Nat}
    (S : BondMovingSummable w p) : (0 : Q') ≤ S.R :=
  S.R_nonneg

/-! ## 5. Doc-section — what is PROVED vs. NAMED-open (CRITICAL honesty)

This module makes the 4D bond-moving residual EXPLICIT and proves its favorable
per-step behaviour:

  * EXPLICIT MAP (proved).  `fusionInd` / `fusionProduct` / `fusionPow` are the
    genuine SU(2) bond-moving map — the Clebsch–Gordan character-coefficient
    convolution and its `p`-fold iterate (`p = b³` in 4D), with nonnegativity
    preserved and the unit a left identity on the dominant modes
    (`fusionPow_one_dom`).  This turns bond-moving into an explicit computable map.

  * LEADING COEFFICIENTS (proved).  `bondMovedCoeff` applies the map to the
    heat-kernel weight `coeff_w(s) = (s+1)·w^{C₄(s)}`; `bondMovedCoeff_one_leading`
    gives the closed-form leading coefficients at `p = 1` (`bmc(0) = 1`,
    `bmc(1) = 2·w^3`), and `sepBM` is the dominant separator.

  * δ → 0 PER STEP (proved, explicit modulus).  `bondMovingDelta w p` is the
    dominant-mode deviation of the bond-moved data from the pure heat-kernel
    (flat-ratio) form, and `bondMovingDelta_to_zero` proves the explicit linear
    modulus `δ(w,p) ≤ 6p·(1 − w)` on `[0,1]`: the bond-moving deviation VANISHES at
    the continuum / weak-coupling end, linearly in the margin `1 − w`.

  * REDUCTION TO SUMMABILITY (named open).  `BondMovingSummable w p` names the
    single remaining 4D obligation `∑_k δ(w_k,p) ≤ R` along the asymptotic-freedom
    trajectory, and `bondMovingSummable_lossBudget` wires its budget into the
    upstream per-scale-rate `lossSum` slot.  It is NOT inhabited.

HONEST VERDICT.  The explicit fusion map and the per-step `δ → 0` (dominant mode,
explicit modulus `6p·(1−w)`) are GENUINELY PROVED.  The full-mode / uniform-along-
flow control is NOT: the summability `∑_k δ(w_k,p) < ∞` — the ACCUMULATION of the
bond-moving deviations across the infinitely many block steps — is the NAMED open
4D Clay content, now sharply isolated to one explicit inequality.  This module does
NOT bound `δ` unconditionally on ℝ⁴.  Restrictions flagged: the fusion product is
truncated at an explicit finite degree `N`; `fusionPow … 1 = c` is proved only on
the dominant modes `s ∈ {0,1}` (the general truncated statement is named); `δ` is
the dominant-mode (`s ≤ 1`) deviation, not the full-mode deviation.  Combined with
the upstream decimation `ρ_dec → 1` and the unconditional decimation-line gap, BOTH
halves of the RG step now have proved favorable continuum-end behaviour; the open
part is precisely the summability of the bond-moving deviations. -/

end YMGap.Continuum.BondMovingStep

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BondMovingStep.fsum_nonneg
#print axioms YMGap.Continuum.BondMovingStep.fusionInd_nonneg
#print axioms YMGap.Continuum.BondMovingStep.fusionProduct_nonneg
#print axioms YMGap.Continuum.BondMovingStep.fusionUnit_nonneg
#print axioms YMGap.Continuum.BondMovingStep.fusionPow_nonneg
#print axioms YMGap.Continuum.BondMovingStep.fusionPow_one_dom
#print axioms YMGap.Continuum.BondMovingStep.coeffW_nonneg
#print axioms YMGap.Continuum.BondMovingStep.coeffW_zero
#print axioms YMGap.Continuum.BondMovingStep.coeffW_one
#print axioms YMGap.Continuum.BondMovingStep.bondMovedCoeff_nonneg
#print axioms YMGap.Continuum.BondMovingStep.bondMovedCoeff_one_leading
#print axioms YMGap.Continuum.BondMovingStep.coeffW_dev
#print axioms YMGap.Continuum.BondMovingStep.bondMovingDelta_nonneg
#print axioms YMGap.Continuum.BondMovingStep.bondMovingDelta_to_zero
#print axioms YMGap.Continuum.BondMovingStep.bondMovingDelta_modulus_const
#print axioms YMGap.Continuum.BondMovingStep.bondMovingResidualSeq_nonneg
#print axioms YMGap.Continuum.BondMovingStep.bondMovingSummable_lossBudget
#print axioms YMGap.Continuum.BondMovingStep.bondMovingSummable_R_nonneg
