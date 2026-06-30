/-
Track B / R2 — the LOG-CONCAVITY (Pólya-frequency / unimodality) route to
`s = 1`-DOMINANCE of the bond-moved spectrum, and its HONEST wiring to the genuine
heat-kernel-specific log-concavity core.

# Why this module exists — the unimodality half of the `s = 1`-dominance node

`S1Dominance` (the sibling module) proves `s = 1`-dominance at `p = 1` and reduces
the genuine `p = b^{d−1} ≥ 2` case to: the bond-moved excited coefficients are
maximized at `s = 1`.  The classical structural mechanism for "maximized at a low
mode" is LOG-CONCAVITY (Pólya-frequency-2): a strictly-positive log-concave
sequence is UNIMODAL, and if its FIRST excited step is non-increasing the peak sits
at or below `s = 1`, so it dominates every excited mode.  This module proves THAT
implication ("log-concave + positive + first-step edge ⇒ `s = 1`-dominant") from
scratch, truncation-aware, and assembles it into the `S1Dominance` datum.

# CRITICAL HONESTY — what log-concavity of the bond-moved tower is, and is NOT

It is TEMPTING to source the tower's log-concavity from the classical "convolution
preserves log-concavity / ultra-log-concavity" theorem (Karlin 1968; Brändén–Huh,
"Lorentzian polynomials", 2019).  THAT IS FALSE HERE, on two counts established by
explicit computation in the sibling module `SelfFusionLogConcave`:

  (1) The character truncation at `N` breaks it: for `w → 1` the dominant Clebsch
      scale exceeds any fixed cutoff and the box `{a,b ≤ N}` clips the convolution
      ASYMMETRICALLY across modes; the smallest witness is `N = 1`, `s = 0`, `w = 1`
      (`boxSum = 20 > 16`, `SelfFusionLogConcave.boxSum1_logConcave_FALSE_at_one`).
  (2) The SU(2) Clebsch–Gordan fusion does NOT preserve log-concavity for GENERIC
      positive log-concave inputs; the heat-kernel case is true (untruncated) only
      because of the SPECIFIC `(r,d)` Gaussian-theta structure of
      `coeff_w(a) = (a+1)·w^{a(a+2)}`, NOT because of mere log-concavity.

So a generic "fusion preserves log-concavity" obligation would be FALSE and is NOT
introduced here.  The genuinely-true, heat-kernel-specific content is the box
log-concavity core `SelfFusionLogConcave.FusionConvLogConcaveCore` (strong-coupling
conditional, inhabited at `N = 1`, general `N` open = the `(r,d)` local-CLT).  This
module consumes THAT true core, not a false generic claim.

# What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat`)

  * `LogConcave` — the discrete PF₂ predicate `∀ s, c s · c (s+2) ≤ c (s+1)²`.
  * `coeffW_logConcave_pred`, `fusionUnit_logConcave` — `coeff_w` and the fusion
    unit `χ_0` are log-concave (the former wraps the unconditional upstream lemma).
  * `lc_step`, `antitone_excited_bounded` — **THE UNIMODALITY HALF (from scratch),**
    truncation-aware: a log-concave sequence, strictly positive UP TO the cutoff `N`,
    whose first excited step is non-increasing (`c 2 ≤ c 1`), is monotone
    non-increasing on the excited modes `1 ≤ s` with `s + 1 ≤ N`.  (Ratio-
    monotonicity of PF₂ via the cross-multiplied cancellation
    `c(s)·c(s+2) ≤ c(s+1)² ≤ c(s)·c(s+1) ⇒ c(s+2) ≤ c(s+1)`.)
  * `head_dominates_bounded`, `s1_dominates_bounded` — the non-increase telescopes
    to `c s ≤ c 1` for every excited `1 ≤ s ≤ N`.
  * `s1Dominance_of_logConcave` — **THE ASSEMBLY (GREEN).**  Log-concavity +
    positivity-on-cutoff + first-step edge INHABIT the `S1Dominance N w p` datum for
    ANY `p`.
  * `bmc2_logConcave_of_core` / `s1Dominance_of_p2` — **THE HONEST `p = 2` WIRING.**
    From the genuine box-level core `FusionConvLogConcaveCore` (which gives the
    `p = 2` tower's log-concavity, `SelfFusionLogConcave.bondMovedCoeff_logConcave_of_core`)
    and the proved positivity `bondMovedCoeff_p2_pos`, plus the first-step edge,
    INHABIT `S1Dominance N w 2`.  Since the core is inhabited at `N = 1`
    (`SelfFusionLogConcave.fusionConvLogConcaveCore_N1`), this is a TRUE reduction,
    not a vacuous one.

# Honest verdict and scope

The previously opaque "fusion preserves `s = 1`-dominance" node is reduced to its
two genuine ingredients: the heat-kernel-specific log-concavity of the bond-moved
tower (the box-level `(r,d)` core, NOT a false generic convolution-closure) and the
elementary first-step edge, with the entire "log-concave ⇒ unimodal ⇒
`s = 1`-dominant" implication PROVED GREEN from scratch and wired to the existing
true core at `p = 2`.  This is NOT a 4D Yang–Mills mass-gap proof; it is the clean
unimodality reduction of the `S1Dominance` node, honestly sourced.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, positive-factor cancellation
(`Q'.le_of_mul_le_mul_left`), and reused order/log-concavity lemmas.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
All witnesses are `Type`-level data.
-/

import YMGap.Continuum.BondMovingStep
import YMGap.Continuum.CharacterWindowCeiling
import YMGap.Continuum.S1Dominance
import YMGap.Continuum.FusionResidualBound
import YMGap.Continuum.SelfFusionLogConcave

namespace YMGap.Continuum.FusionLogConcave

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.S1Dominance
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SelfFusionLogConcave

/-! ## 1. The discrete log-concavity predicate -/

/-- **Discrete log-concavity (Pólya-frequency-2).**  A `Nat → Q'` sequence `c` is
log-concave when

    c s · c (s + 2)  ≤  c (s + 1) · c (s + 1)     for every `s`.

(`Type`-level datum, mirroring `S1Dominance`.)  For strictly-positive `c` this is
equivalent to the ratio `c (s+1) / c s` being non-increasing — the engine of
unimodality. -/
structure LogConcave (c : Nat → Q') : Type where
  /-- The PF₂ inequality at every centre. -/
  logConcave : ∀ s, c s * c (s + 2) ≤ c (s + 1) * c (s + 1)

/-- **`coeff_w` is log-concave (PROVED).**  The heat-kernel coefficient sequence
`coeff_w(s) = (s+1)·w^{C₄(s)}` is unconditionally log-concave on `0 ≤ w ≤ 1`
(`FusionResidualBound.coeffW_logConcave`: dimension surplus `(s+1)² ≥ s(s+2)` and
the Casimir convexity `C₄(s)+C₄(s+2) = 2·C₄(s+1)+2` with `w² ≤ 1`). -/
def coeffW_logConcave_pred {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    LogConcave (coeffW w) where
  logConcave := fun s => FusionResidualBound.coeffW_logConcave hw0 hw1 s

/-- **The fusion unit `χ_0` (`δ_{s,0}`) is log-concave.**  `fusionUnit s ·
fusionUnit (s+2)` is always `0` (the index `s+2 ≥ 2` is never `0`, so the second
factor vanishes), and `fusionUnit (s+1)²` is nonnegative. -/
def fusionUnit_logConcave : LogConcave fusionUnit where
  logConcave := fun s => by
    have h2 : fusionUnit (s + 2) = 0 := by
      show (if (s + 2 == 0) then (1 : Q') else 0) = 0
      rfl
    rw [h2]
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_zero_eqv (fusionUnit s))) ?_
    exact Q'.mul_nonneg _ _ (fusionUnit_nonneg (s + 1)) (fusionUnit_nonneg (s + 1))

/-! ## 2. Log-concave + positive (on cutoff) + first-step edge ⟹ non-increasing

The unimodality half, proved from scratch and TRUNCATION-AWARE.  Log-concavity
`c(s)·c(s+2) ≤ c(s+1)²` with strict positivity makes the per-step ratio
non-increasing; with the first excited step `c 2 ≤ c 1` it forces non-increase on
every excited mode within the cutoff.  Positivity is required only up to `N`
because the truncated bond-moved tower vanishes past its (finite) support — exactly
the PF₂ "support is an interval, no internal zeros" structure. -/

/-- **One ratio-monotonicity step.**  For a log-concave `c` with `0 < c (k+1)` and
`0 ≤ c (k+2)`, if `c (k+2) ≤ c (k+1)` then `c (k+3) ≤ c (k+2)`.  PROOF: log-concavity
at centre `k+1` gives `c(k+1)·c(k+3) ≤ c(k+2)²`; the hypothesis gives `c(k+2)² ≤
c(k+1)·c(k+2)`; chaining and cancelling the positive factor `c(k+1)` yields
`c(k+3) ≤ c(k+2)`. -/
theorem lc_step {c : Nat → Q'} (hlc : LogConcave c) {k : Nat}
    (hp1 : (0 : Q') < c (k + 1)) (hnn2 : (0 : Q') ≤ c (k + 2))
    (hik : c (k + 2) ≤ c (k + 1)) : c (k + 3) ≤ c (k + 2) := by
  -- log-concavity at centre k+1 : c(k+1)·c(k+3) ≤ c(k+2)·c(k+2)
  have hlck : c (k + 1) * c (k + 3) ≤ c (k + 2) * c (k + 2) := hlc.logConcave (k + 1)
  -- c(k+2)·c(k+2) ≤ c(k+1)·c(k+2)
  have hrhs : c (k + 2) * c (k + 2) ≤ c (k + 1) * c (k + 2) :=
    Q'.mul_le_mul_of_nonneg_right (c (k + 2)) (c (k + 1)) (c (k + 2)) hik hnn2
  -- chain to c(k+1)·c(k+3) ≤ c(k+1)·c(k+2), then cancel c(k+1) > 0
  have hchain : c (k + 1) * c (k + 3) ≤ c (k + 1) * c (k + 2) :=
    Q'.le_trans' _ _ _ hlck hrhs
  exact Q'.le_of_mul_le_mul_left hchain hp1

/-- **The excited non-increase, truncation-aware (PROVED).**  A log-concave `c`,
strictly positive on the excited cutoff (`1 ≤ s → s ≤ N → 0 < c s`), with
first-step edge `c 2 ≤ c 1`, is monotone non-increasing on the excited modes within
the cutoff: `c (k+2) ≤ c (k+1)` whenever `k + 2 ≤ N`.  Induction on the centre `k`
via `lc_step`. -/
theorem antitone_excited_bounded {c : Nat → Q'} (hlc : LogConcave c) (N : Nat)
    (hpos : ∀ s, 1 ≤ s → s ≤ N → (0 : Q') < c s) (hedge : c 2 ≤ c 1) :
    ∀ k, k + 2 ≤ N → c (k + 2) ≤ c (k + 1) := by
  intro k
  induction k with
  | zero => intro _; exact hedge
  | succ j ih =>
      intro hk3
      have hk2 : j + 2 ≤ N := by omega
      have hstep : c (j + 2) ≤ c (j + 1) := ih hk2
      exact lc_step hlc (hpos (j + 1) (by omega) (by omega))
        (Q'.le_of_lt (hpos (j + 2) (by omega) (by omega))) hstep

/-- The excited non-increase in `s`-form: `c (s+1) ≤ c s` for `1 ≤ s`, `s + 1 ≤ N`.
Re-index of `antitone_excited_bounded`. -/
theorem antitone_s_form {c : Nat → Q'} (hlc : LogConcave c) (N : Nat)
    (hpos : ∀ s, 1 ≤ s → s ≤ N → (0 : Q') < c s) (hedge : c 2 ≤ c 1) :
    ∀ s, 1 ≤ s → s + 1 ≤ N → c (s + 1) ≤ c s := by
  have hker := antitone_excited_bounded hlc N hpos hedge
  intro s hs hsN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  have e1 : ((1 + k) + 1 : Nat) = k + 2 := by omega
  have e2 : (1 + k : Nat) = k + 1 := by omega
  rw [e1, e2]
  exact hker k (by omega)

/-- **The non-increase telescopes to the head.**  Given the excited non-increase
(`c (s+1) ≤ c s` for `1 ≤ s`, `s + 1 ≤ N`), every excited coefficient within the
cutoff is dominated by the head: `c (1 + k) ≤ c 1` whenever `1 + k ≤ N`. -/
theorem head_dominates_bounded {c : Nat → Q'} (N : Nat)
    (hanti : ∀ s, 1 ≤ s → s + 1 ≤ N → c (s + 1) ≤ c s) :
    ∀ k, 1 + k ≤ N → c (1 + k) ≤ c 1 := by
  intro k
  induction k with
  | zero => intro _; exact Q'.le_refl' (c 1)
  | succ j ih =>
      intro hk
      have hidx : (1 + (j + 1) : Nat) = (1 + j) + 1 := by omega
      rw [hidx]
      have hjN : 1 + j ≤ N := by omega
      exact Q'.le_trans' _ _ _ (hanti (1 + j) (by omega) (by omega)) (ih hjN)

/-- **`s = 1`-dominance from log-concavity (PROVED, truncation-aware).**  A
log-concave sequence, strictly positive on the excited cutoff, with first-step edge
`c 2 ≤ c 1`, is `s = 1`-dominant among the excited modes within the cutoff:
`c s ≤ c 1` for every `1 ≤ s ≤ N`. -/
theorem s1_dominates_bounded {c : Nat → Q'} (hlc : LogConcave c) (N : Nat)
    (hpos : ∀ s, 1 ≤ s → s ≤ N → (0 : Q') < c s) (hedge : c 2 ≤ c 1) :
    ∀ s, 1 ≤ s → s ≤ N → c s ≤ c 1 := by
  have hanti := antitone_s_form hlc N hpos hedge
  have hhead := head_dominates_bounded N hanti
  intro s hs hsN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
  exact hhead k (by omega)

/-! ## 3. The assembly — log-concavity of the bond-moved tower ⟹ `S1Dominance` -/

/-- **`s1Dominance_of_logConcave` — THE ASSEMBLY (GREEN).**  Given that the
bond-moved tower `bondMovedCoeff N w p` is log-concave, strictly positive on the
excited cutoff `1 ≤ s ≤ N`, and non-increasing at the first excited step
(`bmc 2 ≤ bmc 1`), the bond-moved spectrum is `s = 1`-dominant: this INHABITS the
`S1Dominance N w p` datum for ANY `p`, via the unimodality chain
`s1_dominates_bounded`.

The three hypotheses are the honest inputs: log-concavity (the heat-kernel-specific
content — NOT generic convolution closure, see the module header), strict positivity
on the support, and the first-step edge. -/
def s1Dominance_of_logConcave (N : Nat) (w : Q') (p : Nat)
    (hlc : LogConcave (bondMovedCoeff N w p))
    (hpos : ∀ s, 1 ≤ s → s ≤ N → (0 : Q') < bondMovedCoeff N w p s)
    (hedge : bondMovedCoeff N w p 2 ≤ bondMovedCoeff N w p 1) :
    S1Dominance N w p where
  dominates := fun s hs hsN => s1_dominates_bounded hlc N hpos hedge s hs hsN

/-! ## 4. The honest `p = 2` wiring to the genuine heat-kernel core

The log-concavity of the `p = 2` bond-moved tower is the genuine heat-kernel-specific
content carried by `SelfFusionLogConcave.FusionConvLogConcaveCore` (the box-level
`(r,d)` core, strong-coupling conditional, inhabited at `N = 1`).  We package it as a
`LogConcave` datum and feed it through the assembly. -/

/-- **`bmc2_logConcave_of_core` — the `p = 2` tower is log-concave, from the genuine
core.**  Given a `FusionConvLogConcaveCore N w` witness (the heat-kernel-specific box
log-concavity, NOT a generic convolution claim), the `p = 2` bond-moved tower is
log-concave in the mode index (`SelfFusionLogConcave.bondMovedCoeff_logConcave_of_core`). -/
def bmc2_logConcave_of_core {N : Nat} {w : Q'} {hw0 : (0 : Q') ≤ w} {hw1 : w ≤ (1 : Q')}
    (core : FusionConvLogConcaveCore N w hw0 hw1) :
    LogConcave (bondMovedCoeff N w 2) where
  logConcave := fun s =>
    SelfFusionLogConcave.bondMovedCoeff_logConcave_of_core core s

/-- **`s1Dominance_of_p2` — THE HONEST `p = 2` CAPSTONE.**  Given the genuine box-level
core `FusionConvLogConcaveCore N w` (heat-kernel-specific log-concavity), strict
positivity of the weight (`0 < w`, giving the proved fused-tower positivity
`bondMovedCoeff_p2_pos`), and the first-step edge `bmc 2 ≤ bmc 1`, the `p = 2`
bond-moved spectrum is `s = 1`-dominant — INHABITING `S1Dominance N w 2`.

This is a TRUE reduction: the core is inhabited at `N = 1`
(`SelfFusionLogConcave.fusionConvLogConcaveCore_N1`).  For general `N` the core is the
genuinely-open `(r,d)` Gaussian local-CLT content — NOT the false generic "convolution
preserves log-concavity" (refuted in `SelfFusionLogConcave`). -/
def s1Dominance_of_p2 {N : Nat} {w : Q'} (hw : (0 : Q') < w)
    {hw0 : (0 : Q') ≤ w} {hw1 : w ≤ (1 : Q')}
    (core : FusionConvLogConcaveCore N w hw0 hw1)
    (hedge : bondMovedCoeff N w 2 2 ≤ bondMovedCoeff N w 2 1) :
    S1Dominance N w 2 :=
  s1Dominance_of_logConcave N w 2 (bmc2_logConcave_of_core core)
    (fun _s _hs hsN => SelfFusionLogConcave.bondMovedCoeff_p2_pos hw hsN) hedge

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):

  * `LogConcave` — the PF₂ datum; `coeffW_logConcave_pred` — `coeff_w` is
    log-concave (from the unconditional upstream lemma); `fusionUnit_logConcave` —
    the fusion unit is log-concave.
  * `lc_step`, `antitone_excited_bounded`, `antitone_s_form` — the UNIMODALITY half
    from scratch, truncation-aware: a log-concave sequence, positive up to the
    cutoff, with first-step edge `c 2 ≤ c 1`, is monotone non-increasing on the
    excited modes within the cutoff (ratio-monotonicity via cross-multiplied
    cancellation).
  * `head_dominates_bounded`, `s1_dominates_bounded` — the non-increase telescopes
    to full `s = 1`-dominance `c s ≤ c 1` (`1 ≤ s ≤ N`).
  * `s1Dominance_of_logConcave` — the ASSEMBLY: log-concavity + positivity-on-cutoff
    + edge INHABIT `S1Dominance N w p` for any `p`.
  * `bmc2_logConcave_of_core`, `s1Dominance_of_p2` — the HONEST `p = 2` wiring:
    `S1Dominance N w 2` from the genuine heat-kernel-specific box core
    `FusionConvLogConcaveCore` (inhabited at `N = 1`) + positivity + edge.

NAMED OPEN (NOT inhabited here — carried by `SelfFusionLogConcave`):

  * `FusionConvLogConcaveCore N w` for general `N` — the box log-concavity of the
    bond-moved tower.  This is the heat-kernel-specific `(r,d)` Gaussian local-CLT,
    NOT the classical "convolution preserves log-concavity" (which is FALSE here:
    truncation breaks it at `N = 1`, `w = 1`, and the SU(2) fusion does not preserve
    generic log-concavity — both refuted in `SelfFusionLogConcave`).  Inhabited at
    `N = 1`; general `N` open.  The first-step edge `bmc 2 ≤ bmc 1` is the elementary
    companion input.

HONEST VERDICT.  The "log-concave ⇒ unimodal ⇒ `s = 1`-dominant" implication is
PROVED GREEN from scratch (truncation-aware) and assembled into the `S1Dominance`
datum; the `p = 2` case is wired to the EXISTING genuine box-level core, NOT to any
false generic convolution-closure claim.  This sharpens the `s = 1`-dominance node to
its two honest ingredients (heat-kernel-specific tower log-concavity + the first-step
edge).  This is NOT a 4D Yang–Mills mass-gap proof. -/

end YMGap.Continuum.FusionLogConcave

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionLogConcave.coeffW_logConcave_pred
#print axioms YMGap.Continuum.FusionLogConcave.fusionUnit_logConcave
#print axioms YMGap.Continuum.FusionLogConcave.lc_step
#print axioms YMGap.Continuum.FusionLogConcave.antitone_excited_bounded
#print axioms YMGap.Continuum.FusionLogConcave.antitone_s_form
#print axioms YMGap.Continuum.FusionLogConcave.head_dominates_bounded
#print axioms YMGap.Continuum.FusionLogConcave.s1_dominates_bounded
#print axioms YMGap.Continuum.FusionLogConcave.s1Dominance_of_logConcave
#print axioms YMGap.Continuum.FusionLogConcave.bmc2_logConcave_of_core
#print axioms YMGap.Continuum.FusionLogConcave.s1Dominance_of_p2
