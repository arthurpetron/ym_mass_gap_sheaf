/-
⚠️ DEPRECATED ROUTE (2026-06-27) — `FusionRelResidualBound` is FALSE. ⚠️
This file reduces the bond-moving gap to the single obligation
`FusionRelResidualBound` (`|rrelFix s| ≤ (1−w)²·Peval P (yArg w s)`).  That
obligation is FALSE, for two independent reasons (verified by exact-arithmetic
numerics):
  (1) NORMALIZATION: `rrelFix` uses `KtauFix(0)=1`, but `bondMovedCoeff(0)` for
      `p≥2` is `Σ_i coeffW(i)² = 1+4w⁶+… ≠ 1`, so `rrelFix(0)=bmc(0)−1 →` large
      (157 at w=.99) ≫ `(1−w)²·P(0)`.  (Fixable by `÷bmc(0)`.)
  (2) FUNDAMENTAL: even normalized, the per-step defect is LINEAR `O(1−w)` (not
      `O((1−w)²)`) — the bulk modes `s ~ 1/√(1−w)` dominate with linear deviation;
      the marginal→quadratic mechanism only helps low modes.  ⇒ divergent floor,
      no gap.
The structural lemmas here (`KtauFix_ge_coeffW`, `bmc_ge_identity`,
`rrelFix_p1_zero`, `rrelFix_lower`) are TRUE and reusable; the reduction
(`genuineResidualBound_of_fusionRel`, `fullModeGap_of_fusionRel`) is logically
sound but rests on the FALSE `FusionRelResidualBound`, so it is NOT a live route
to the gap.  See `project_os2_critical_path_map` memory.

Track B / R2 — the CONCRETE bond-moving relative residual measured against the
CORRECTED retuned heat-kernel coefficient `KtauFix`, the genuine provable
structural one-sided bounds on it, and the PRECISE (now-satisfiable) reduction of
the `GenuineResidualDefect.GenuineResidualBound` load-bearing field to ONE named
two-sided fusion-coefficient obligation.

# Why this module exists — the OS2 critical-path residual, made concrete

The genuine relative residual carried abstractly by `GenuineResidualBound.hbound`
is the bond-moved coefficient measured RELATIVE to a RETUNED heat-kernel
coefficient.  The retune was corrected to the rational `w^{1/p}` surrogate
`renormWFix p hp w = 1 − (1 − w)/p` (which makes the residual SATISFIABLE: the
prior `p`-independent retune blew up).  This module builds the CONCRETE relative
residual `rrelFix` at the corrected base and proves everything that is solidly
provable about it:

  * `KtauFix` — the corrected retuned heat-kernel coefficient
    `dimQ s · renormWFix^{C₄(s)}`; `KtauFix_nonneg` / `KtauFix_pos` (the divisor
    positivity that makes `rrelFix` well defined).
  * `KtauFix_ge_coeffW` — `coeffW w s ≤ KtauFix p hp w s` (the corrected retune
    decays SLOWER than `w`, so `K_τ` dominates the bare weight per mode).
  * `bmc_ge_identity` — the IDENTITY-CHANNEL lower bound `coeffW w s ≤
    bondMovedCoeff N w p s` (the `(s,0,…,0)` fusion channel survives with
    coefficient `1` and all other channels are `≥ 0`), by induction on `p`.
  * `rrelFix` — the genuine relative residual `(bmc − K_τ)/K_τ` via `divPos`.
  * `rrelFix_p1_zero` — the EXACT `p = 1` vanishing `rrelFix N 1 _ w _ s ≃ 0`
    (`renormWFix 1 = w` so `K_τ = coeffW w`, and `bondMovedCoeff N w 1 s ≃
    coeffW w s` by the unit fusion identity): the residual is REAL, not posited.
  * `rrelFix_lower` — the provable LOWER bound `-(1) ≤ rrelFix` and the
    identity-channel quotient lower bound.

THE PRECISE NAMED OBLIGATION (research-grade, now SATISFIABLE):

  * `FusionRelResidualBound N p hp P` — the FULL two-sided quadratic bound
    `|rrelFix N p hp w _ s| ≤ (1−w)²·Peval P (yArg w s)` on `0 < w < 1`, `s ≤ N`.
    This is the Chebyshev-U fusion-coefficient analysis of `K_w^p` against the
    retuned heat kernel — the same deep tier as `JTPIdentity.DiffJTP`.  NOT
    inhabited.
  * `genuineResidualBound_of_fusionRel` — the PROVED reduction
    `(FusionRelResidualBound … at each AF weight) ∧ (uniform moment certificates)
    → GenuineResidualBound afr q m r S N₀`, assembling the structure with
    `rrel k := rrelFix N p hp (afr.w k) …` and `P`, with EVERYTHING ELSE proved.
    The residual `hbound` field is discharged DIRECTLY by `FusionRelResidualBound`;
    the moment certificates are carried as a precisely-named secondary obligation
    `UniformMomentCerts` (the "moving-cutoff upgrade").

# Honest verdict and scope

The structural bounds (identity-channel `bmc ≥ coeffW`, the `K_τ ≥ coeffW` retune
domination, the EXACT `p = 1` vanishing, the lower bound `≥ −1`) are GENUINELY
PROVED.  They establish that `rrelFix ≥ −1 + coeffW/K_τ` (the residual cannot fall
below the identity-channel quotient floor) and that it VANISHES at `p = 1`.  What
remains research-grade is the matching UPPER bound on the off-identity fusion
channels at general `p` — the genuine quadratic two-sided bound `|rrelFix| ≤
(1−w)²·P(y_s)`, named `FusionRelResidualBound` and reduced to (not faked).  This is
NOT a 4D Yang–Mills mass-gap proof; it is the concrete relative-residual framework,
the solidly-provable one-sided structural bounds, and the precise satisfiable
reduction of the OS2-critical `hbound` field.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, decidable `Nat`/`Q'` facts, and
reused order/`divPos` lemmas.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide` (only `decide` on decidable facts), no `sorry`.
All witnesses are `Type`-level data.
-/

import YMGap.Continuum.GenuineResidualDefect
import YMGap.Continuum.FusionResidualBound
import YMGap.Continuum.FusionQuotientCollapse
import YMGap.Continuum.SelfFusionLogConcave
import YMGap.Continuum.BondMovingRetuneFix

namespace YMGap.Continuum.BondMovingRelResidual

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.BondMovingRetuneFix
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.GenuineResidualDefect
open YMGap.Continuum.AFRateCalibration

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Small `Q'` helpers (proved here, axiom-clean) -/

/-- **`qpow` is congruent in the base under `≈`.**  `a ≈ b ⟹ qpow a n ≈ qpow b n`.
(Induction on `n`: at `n+1`, `qpow a n · a ≈ qpow b n · b` by congruence on both
factors.) -/
theorem qpow_eqv_congr_base {a b : Q'} (h : a ≈ b) :
    ∀ n, (qpow a n) ≈ (qpow b n)
  | 0 => Q'.eqv_refl _
  | n + 1 => by
      show (qpow a n * a) ≈ (qpow b n * b)
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ a (qpow_eqv_congr_base h n)) ?_
      exact Q'.mul_eqv_congr_left (qpow b n) _ _ h

/-- `a < b` and `b ≤ c` gives `a < c` (local copy from the `Int` cross-product
order; the foundation `Sqrt` provides only the `≤`/`<` form). -/
theorem q_lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (b.den : Int)) * (a.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_right e2
      (by exact_mod_cast Nat.le_of_lt a.den_pos : (0 : Int) ≤ (a.den : Int))
    have hr : (b.num * (c.den : Int)) * (a.den : Int)
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (c.den : Int) (a.den : Int)]
    rwa [hr] at this
  have s3 : (a.num * (c.den : Int)) * (b.den : Int)
          < (c.num * (a.den : Int)) * (b.den : Int) := by
    refine Int.lt_of_lt_of_le s1 ?_
    have hr : (c.num * (b.den : Int)) * (a.den : Int)
            = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rwa [hr] at s2
  exact Int.lt_of_mul_lt_mul_right s3
    (by exact_mod_cast Nat.le_of_lt b.den_pos : (0 : Int) ≤ (b.den : Int))

/-- `(-1 : Q') · x ≈ -x`. -/
theorem neg_one_mul_eqv (x : Q') : ((-1 : Q') * x) ≈ (-x) := by
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv (1 : Q') x) ?_
  exact Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv x)

/-- **`w ≤ renormWFix p hp w`** — the corrected retune base dominates the bare
weight.  `renormTauFix = (1 − w)·(1/p) ≤ (1 − w)·1 = 1 − w` (since `1/p ≤ 1` for
`p ≥ 1`), so `renormWFix = 1 − renormTauFix ≥ 1 − (1 − w) = w`. -/
theorem w_le_renormWFix {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (p : Nat) (hp : 0 < p) : w ≤ renormWFix p hp w := by
  -- renormTauFix p hp w = (1−w)·(1/p) ≤ (1−w)·1 ≃ 1−w
  have hτle : renormTauFix p hp w ≤ ((1 : Q') - w) := by
    show ((1 : Q') - w) * Q'.mkPos 1 p hp ≤ ((1 : Q') - w)
    have hstep : ((1 : Q') - w) * Q'.mkPos 1 p hp ≤ ((1 : Q') - w) * (1 : Q') :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (mkPos_one_p_le_one p hp)
        (Q'.sub_nonneg_of_le hw1)
    exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.mul_one_eqv ((1 : Q') - w)))
  -- renormWFix = 1 − renormTauFix ≥ 1 − (1−w) ≃ w
  show w ≤ (1 : Q') - renormTauFix p hp w
  -- 1 − (1−w) ≃ w and 1 − τ ≥ 1 − (1−w) since τ ≤ 1−w
  have hmono : (1 : Q') - ((1 : Q') - w) ≤ (1 : Q') - renormTauFix p hp w := by
    show (1 : Q') + -((1 : Q') - w) ≤ (1 : Q') + -(renormTauFix p hp w)
    refine Q'.add_le_add_left (1 : Q') _ _ ?_
    exact Q'.neg_le_neg hτle
  -- 1 − (1−w) ≃ w
  have heq : ((1 : Q') - ((1 : Q') - w)) ≈ w := by
    show ((1 : Q') + -((1 : Q') + (-w))) ≈ w
    have ha : (-((1 : Q') + (-w))) ≈ ((-1 : Q') + w) := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (1 : Q') (-w)) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv w)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (1 : Q') _ _ ha) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-1) w)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ w (Q'.add_neg_self_eqv (1 : Q'))) ?_
    exact QPoly.q_zero_add_eqv w
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hmono

/-! ## 1. The corrected retuned heat-kernel coefficient `KtauFix` -/

/-- **The corrected retuned heat-kernel coefficient** at base `renormWFix p hp w`:

    KtauFix p hp w s  =  dimQ s · renormWFix^{C₄(s)}.

This is `coeffW (renormWFix p hp w) s` written out; it is the per-mode retuned
heat-kernel coefficient the relative residual is measured against. -/
def KtauFix (p : Nat) (hp : 0 < p) (w : Q') (s : Nat) : Q' :=
  dimQ s * qpow (renormWFix p hp w) (c4 s)

/-- `KtauFix = coeffW (renormWFix …)` definitionally. -/
theorem KtauFix_eq_coeffW (p : Nat) (hp : 0 < p) (w : Q') (s : Nat) :
    KtauFix p hp w s = coeffW (renormWFix p hp w) s := rfl

/-- `KtauFix p hp w s ≥ 0` on `0 ≤ w ≤ 1` (`dimQ ≥ 0`, `renormWFix ≥ 0`). -/
theorem KtauFix_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (p : Nat) (hp : 0 < p) (s : Nat) : (0 : Q') ≤ KtauFix p hp w s :=
  Q'.mul_nonneg _ _ (dimQ_nonneg s)
    (qpow_nonneg _ (renormWFix_nonneg hw0 p hp) (c4 s))

/-- **`KtauFix p hp w s > 0` for `0 < w < 1`** — the divisor positivity that makes
`rrelFix` well defined.  `dimQ s = s + 1 > 0` and `renormWFix p hp w > 0` (since
`renormWFix < 1` ⟹ `> 0` via the gap margin), so `renormWFix^{C₄(s)} > 0`. -/
theorem KtauFix_pos {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (p : Nat) (hp : 0 < p) (s : Nat) : (0 : Q') < KtauFix p hp w s := by
  show (0 : Q') < dimQ s * qpow (renormWFix p hp w) (c4 s)
  -- 0 < dimQ s = ofNat (s+1)
  have hd : (0 : Q') < dimQ s := by
    show (0 : Q') < Q'.ofNat (s + 1)
    exact Q'.ofNat_succ_pos s
  -- 0 < renormWFix p hp w :  renormWFix = 1 − τ with 0 < τ < 1, so renormWFix > 0
  have hrw_pos : (0 : Q') < renormWFix p hp w := by
    -- renormWFix ≥ w > 0 (decays slower than w), via the satisfiability criterion
    -- but simplest: renormWFix ≥ 0 and renormWFix ≠ 0 is awkward; use w ≤ renormWFix
    have hge : w ≤ renormWFix p hp w := by
      -- renormTauFix = (1−w)/p ≤ (1−w) so 1 − (1−w)/p ≥ 1 − (1−w) = w; via #2's helper
      exact w_le_renormWFix (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) p hp
    exact q_lt_of_lt_of_le hw0 hge
  exact Q'.mul_pos hd (qpow_pos hrw_pos (c4 s))

/-! ## 2. The retune domination `coeffW w s ≤ KtauFix p hp w s` -/

/-- **`coeffW w s ≤ KtauFix p hp w s`** — the corrected retune coefficient dominates
the bare heat-kernel coefficient per mode.  `coeffW w s = dimQ s · w^{C₄(s)}`,
`KtauFix … s = dimQ s · renormWFix^{C₄(s)}`; since `w ≤ renormWFix` and `qpow` is
monotone in the base, `w^{C₄(s)} ≤ renormWFix^{C₄(s)}`, scaled by `dimQ s ≥ 0`. -/
theorem KtauFix_ge_coeffW {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (p : Nat) (hp : 0 < p) (s : Nat) :
    coeffW w s ≤ KtauFix p hp w s := by
  show dimQ s * qpow w (c4 s) ≤ dimQ s * qpow (renormWFix p hp w) (c4 s)
  have hpow : qpow w (c4 s) ≤ qpow (renormWFix p hp w) (c4 s) :=
    qpow_mono hw0 (w_le_renormWFix hw0 hw1 p hp) (c4 s)
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hpow (dimQ_nonneg s)

/-! ## 3. The IDENTITY-CHANNEL lower bound `coeffW w s ≤ bondMovedCoeff N w p s`

The bond-moved coefficient at any `p ≥ 1` is at least its `(s,0,…,0)` fusion
channel — the channel that fuses `χ_s` with `p − 1` copies of the vacuum `χ_0`.
That channel survives with `fusionInd s 0 s = 1`, `coeffW w 0 = 1`, and the
remaining factor `bondMovedCoeff N w (p−1) s ≥ coeffW w s` by induction; all other
fusion channels are `≥ 0`.  This is the genuine, provable one-sided structural
lower bound on the bond-moved coefficient. -/

/-- **Extract the `(a, b)`-summand of the fusion double sum.**  For `a ≤ N`,
`b ≤ N`, and nonnegative coefficient sequences `c, d`,

    fusionInd a b s · (c a · d b)  ≤  fusionProduct N c d s,

i.e. one nonnegative summand is `≤` the whole nonnegative double sum.  (Two
applications of `fsum_term_le_of_nonneg`.) -/
theorem fusionProduct_term_le (N : Nat) {c d : Nat → Q'}
    (hc : ∀ s, (0 : Q') ≤ c s) (hd : ∀ s, (0 : Q') ≤ d s)
    (a b s : Nat) (haN : a ≤ N) (hbN : b ≤ N) :
    fusionInd a b s * (c a * d b) ≤ fusionProduct N c d s := by
  -- inner: fusionInd a b s · (c a · d b) ≤ fsum (fun b => fusionInd a b s·(c a·d b)) (N+1)
  have hinner_nonneg : ∀ b', (0 : Q') ≤ fusionInd a b' s * (c a * d b') :=
    fun b' => Q'.mul_nonneg _ _ (fusionInd_nonneg a b' s)
      (Q'.mul_nonneg _ _ (hc a) (hd b'))
  have hb_lt : b < N + 1 := Nat.lt_succ_of_le hbN
  have hin : fusionInd a b s * (c a * d b)
      ≤ fsum (fun b' => fusionInd a b' s * (c a * d b')) (N + 1) :=
    fsum_term_le_of_nonneg hinner_nonneg b (N + 1) hb_lt
  -- outer: that inner sum ≤ fusionProduct N c d s
  have houter_nonneg : ∀ a',
      (0 : Q') ≤ fsum (fun b' => fusionInd a' b' s * (c a' * d b')) (N + 1) :=
    fun a' => fsum_nonneg (fun b' =>
      Q'.mul_nonneg _ _ (fusionInd_nonneg a' b' s)
        (Q'.mul_nonneg _ _ (hc a') (hd b'))) (N + 1)
  have ha_lt : a < N + 1 := Nat.lt_succ_of_le haN
  have hout : fsum (fun b' => fusionInd a b' s * (c a * d b')) (N + 1)
      ≤ fsum (fun a' => fsum (fun b' => fusionInd a' b' s * (c a' * d b')) (N + 1)) (N + 1) :=
    fsum_term_le_of_nonneg houter_nonneg a (N + 1) ha_lt
  exact Q'.le_trans' _ _ _ hin hout

/-- **THE IDENTITY-CHANNEL LOWER BOUND.**  For `0 ≤ w ≤ 1`, `p ≥ 1`, and `s ≤ N`,

    coeffW w s  ≤  bondMovedCoeff N w p s,

i.e. the bond-moved coefficient is at least its `(s, 0, …, 0)` identity fusion
channel.  PROOF by induction on `p`.  Base `p = 1`: `bondMovedCoeff N w 1 s ≃
coeffW w s` (`fusionPow_one_eq`).  Step: extract the `(a, b) = (s, 0)` summand of
`fusionProduct N (fusionPow N (coeffW w) p) (coeffW w) s`, which is
`fusionInd s 0 s · (g_p s · coeffW w 0) = 1 · (g_p s · 1) ≃ g_p s ≥ coeffW w s`
(IH); all other summands are `≥ 0`. -/
theorem bmc_ge_identity (N : Nat) {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) (hsN : s ≤ N) :
    ∀ (p : Nat), 0 < p → coeffW w s ≤ bondMovedCoeff N w p s
  | 1, _ => by
      -- bondMovedCoeff N w 1 s = fusionPow N (coeffW w) 1 s ≃ coeffW w s
      have heq : (bondMovedCoeff N w 1 s).eqv (coeffW w s) := fusionPow_one_eq hsN
      exact Q'.ge_of_eqv heq
  | p + 2, _ => by
      -- IH at p+1 ≥ 1
      have ih : coeffW w s ≤ bondMovedCoeff N w (p + 1) s :=
        bmc_ge_identity N hw0 hw1 s hsN (p + 1) (Nat.succ_pos p)
      -- bondMovedCoeff N w (p+2) s = fusionProduct N (fusionPow N (coeffW w) (p+1)) (coeffW w) s
      -- extract the (s, 0) summand
      have hc_nonneg : ∀ t, (0 : Q') ≤ fusionPow N (coeffW w) (p + 1) t :=
        fun t => fusionPow_nonneg N (coeffW_nonneg hw0) (p + 1) t
      have hd_nonneg : ∀ t, (0 : Q') ≤ coeffW w t := fun t => coeffW_nonneg hw0 t
      have hterm : fusionInd s 0 s * (fusionPow N (coeffW w) (p + 1) s * coeffW w 0)
          ≤ fusionProduct N (fusionPow N (coeffW w) (p + 1)) (coeffW w) s :=
        fusionProduct_term_le N hc_nonneg hd_nonneg s 0 s hsN (Nat.zero_le N)
      -- the (s,0) summand ≃ g_{p+1} s  (fusionInd s 0 s = 1, coeffW w 0 = 1)
      have hsumm_eq :
          (fusionInd s 0 s * (fusionPow N (coeffW w) (p + 1) s * coeffW w 0)).eqv
            (fusionPow N (coeffW w) (p + 1) s) := by
        rw [fusionInd_self_zero s, coeffW_zero w]
        -- 1 · (g · 1) ≃ g
        refine Q'.eqv_trans _ _ _
          (Q'.one_mul_eqv (fusionPow N (coeffW w) (p + 1) s * (1 : Q'))) ?_
        exact Q'.mul_one_eqv (fusionPow N (coeffW w) (p + 1) s)
      -- so g_{p+1} s ≤ bondMovedCoeff N w (p+2) s
      have hchan : fusionPow N (coeffW w) (p + 1) s
          ≤ bondMovedCoeff N w (p + 2) s := by
        show fusionPow N (coeffW w) (p + 1) s
            ≤ fusionProduct N (fusionPow N (coeffW w) (p + 1)) (coeffW w) s
        exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hsumm_eq) hterm
      -- coeffW w s ≤ g_{p+1} s (IH, = bondMovedCoeff N w (p+1) s) ≤ bondMovedCoeff N w (p+2) s
      exact Q'.le_trans' _ _ _ ih hchan

/-! ## 4. The genuine relative residual `rrelFix` -/

/-- **The genuine relative residual** at the corrected base:

    rrelFix N p hp w hw0 hw1 s  =  (bondMovedCoeff N w p s − KtauFix p hp w s)
                                     / KtauFix p hp w s,

the bond-moved coefficient measured RELATIVE to the corrected retuned heat-kernel
coefficient.  Guarded by `KtauFix_pos` (the divisor positivity). -/
def rrelFix (N p : Nat) (hp : 0 < p) {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (s : Nat) : Q' :=
  Q'.divPos (bondMovedCoeff N w p s + -(KtauFix p hp w s)) (KtauFix p hp w s)
    (KtauFix_pos hw0 hw1 p hp s)

/-! ## 5. The EXACT `p = 1` vanishing -/

/-- **`renormWFix 1 _ w = w`** — at `p = 1` the corrected retune is the identity:
`renormTauFix 1 _ w = (1 − w)·(1/1) ≃ 1 − w`, so `renormWFix = 1 − (1 − w) ≃ w`. -/
theorem renormWFix_one (w : Q') :
    (renormWFix 1 (by decide) w) ≈ w := by
  -- renormWFix 1 _ w = 1 − (1−w)·(1/1)
  show ((1 : Q') - ((1 : Q') - w) * Q'.mkPos 1 1 (by decide)) ≈ w
  -- (1−w)·(1/1) ≃ (1−w)·1 ≃ 1−w  [1/1 ≃ 1]
  have hmk : (Q'.mkPos 1 1 (by decide)) ≈ (1 : Q') := by
    show (Q'.mkPos 1 1 (by decide)).num * (((1 : Q').den) : Int)
       = ((1 : Q').num) * ((Q'.mkPos 1 1 (by decide)).den : Int)
    rw [Q'.mkPos_num, Q'.mkPos_den]; decide
  have hτ : (((1 : Q') - w) * Q'.mkPos 1 1 (by decide)) ≈ ((1 : Q') - w) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left ((1 : Q') - w) _ _ hmk) ?_
    exact Q'.mul_one_eqv ((1 : Q') - w)
  -- 1 − τ ≃ 1 − (1−w) ≃ w
  refine Q'.eqv_trans _ ((1 : Q') + -((1 : Q') - w)) _ ?_ ?_
  · show ((1 : Q') + -(((1 : Q') - w) * Q'.mkPos 1 1 (by decide)))
       ≈ ((1 : Q') + -((1 : Q') - w))
    exact Q'.add_eqv_congr_left (1 : Q') _ _ (Q'.neg_eqv_congr _ _ hτ)
  · -- 1 − (1−w) ≃ w
    show ((1 : Q') + -((1 : Q') + (-w))) ≈ w
    have ha : (-((1 : Q') + (-w))) ≈ ((-1 : Q') + w) := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (1 : Q') (-w)) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv w)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (1 : Q') _ _ ha) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-1) w)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ w (Q'.add_neg_self_eqv (1 : Q'))) ?_
    exact QPoly.q_zero_add_eqv w

/-- **THE `p = 1` EXACT VANISHING.**  For `0 < w < 1` and `s ≤ N`,

    rrelFix N 1 _ w _ _ s  ≃  0,

the relative residual at `p = 1` (one parallel plaquette = no bond-moving)
vanishes exactly: the numerator `bondMovedCoeff N w 1 s − KtauFix 1 _ w s ≃
coeffW w s − coeffW w s ≃ 0` because `renormWFix 1 _ w ≃ w` (so `KtauFix ≃
coeffW w s`) and `bondMovedCoeff N w 1 s ≃ coeffW w s` (`fusionPow_one_eq`).  This
is the genuine sanity check that the residual is REAL, not posited. -/
theorem rrelFix_p1_zero (N : Nat) {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (s : Nat) (hsN : s ≤ N) :
    (rrelFix N 1 (by decide) hw0 hw1 s) ≈ 0 := by
  unfold rrelFix
  -- the numerator is ≃ 0; then divPos of (≃0) is ≃ 0
  -- num = bondMovedCoeff N w 1 s + -(KtauFix 1 _ w s)
  have hbmc : (bondMovedCoeff N w 1 s).eqv (coeffW w s) := fusionPow_one_eq hsN
  -- KtauFix 1 _ w s = coeffW (renormWFix 1 _ w) s ≃ coeffW w s
  have hKt : (KtauFix 1 (by decide) w s).eqv (coeffW w s) := by
    show (coeffW (renormWFix 1 (by decide) w) s).eqv (coeffW w s)
    -- coeffW is congruent in the base: dimQ s · qpow base (c4 s)
    show (dimQ s * qpow (renormWFix 1 (by decide) w) (c4 s)).eqv
        (dimQ s * qpow w (c4 s))
    refine Q'.mul_eqv_congr_left (dimQ s) _ _ ?_
    exact qpow_eqv_congr_base (renormWFix_one w) (c4 s)
  -- numerator ≃ coeffW w s + -(coeffW w s) ≃ 0
  have hnum : (bondMovedCoeff N w 1 s + -(KtauFix 1 (by decide) w s)).eqv 0 := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hbmc (Q'.neg_eqv_congr _ _ hKt)) ?_
    exact Q'.add_neg_self_eqv (coeffW w s)
  -- divPos (num) den ≃ 0  since num ≃ 0
  -- divPos num den = num · (1/den); num ≃ 0 ⟹ product ≃ 0
  show (Q'.divPos (bondMovedCoeff N w 1 s + -(KtauFix 1 (by decide) w s))
        (KtauFix 1 (by decide) w s) _).eqv 0
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hnum) ?_
  exact Q'.zero_mul_eqv _

/-! ## 6. The provable LOWER bound on `rrelFix` -/

/-- **The identity-channel quotient lower bound.**  For `0 < w < 1` and `s ≤ N`,
`p ≥ 1`,

    (coeffW w s − KtauFix p hp w s) / KtauFix p hp w s  ≤  rrelFix N p hp w _ _ s,

i.e. the relative residual is at least the identity-channel quotient floor.
Since `coeffW w s ≤ bondMovedCoeff N w p s` (`bmc_ge_identity`), the numerator
`coeffW w s − K_τ ≤ bondMovedCoeff − K_τ`, divided by the positive `K_τ`. -/
theorem rrelFix_identity_lower (N p : Nat) (hp : 0 < p) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (s : Nat) (hsN : s ≤ N) :
    Q'.divPos (coeffW w s + -(KtauFix p hp w s)) (KtauFix p hp w s)
        (KtauFix_pos hw0 hw1 p hp s)
      ≤ rrelFix N p hp hw0 hw1 s := by
  unfold rrelFix
  -- divPos is monotone in the numerator (positive denominator)
  -- coeffW w s + -K ≤ bondMovedCoeff + -K
  have hnum : coeffW w s + -(KtauFix p hp w s)
      ≤ bondMovedCoeff N w p s + -(KtauFix p hp w s) :=
    Q'.add_le_add_right _ _ _ (bmc_ge_identity N (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) s hsN p hp)
  -- divPos monotone in the numerator: a ≤ b ⟹ divPos a den ≤ divPos b den
  exact HeatKernelLinearBound.divPos_le_divPos_of_le (KtauFix_pos hw0 hw1 p hp s) hnum

/-- **`-(1 : Q') ≤ rrelFix N p hp w _ _ s`** — the relative residual is bounded
below by `−1`.  Since `bondMovedCoeff N w p s ≥ 0` and `K_τ > 0`, the numerator
`bondMovedCoeff − K_τ ≥ −K_τ`, so the quotient `≥ −K_τ/K_τ = −1`.  (The exact
floor is `coeffW/K_τ − 1`, which is `≥ −1`; this is the clean uniform statement.) -/
theorem rrelFix_lower (N p : Nat) (hp : 0 < p) {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (s : Nat) :
    -(1 : Q') ≤ rrelFix N p hp hw0 hw1 s := by
  unfold rrelFix
  -- need -1 ≤ divPos (bmc + -K) K ; via le_divPos_of_mul_le : (-1)·K ≤ bmc + -K
  refine Q'.le_divPos_of_mul_le _ _ (KtauFix_pos hw0 hw1 p hp s) ?_
  -- (-1)·K ≃ -K ≤ bmc + -K  ⇐  0 ≤ bmc
  have hbmc_nn : (0 : Q') ≤ bondMovedCoeff N w p s :=
    bondMovedCoeff_nonneg N (Q'.le_of_lt hw0) p s
  -- -K ≤ bmc + -K  ⇐  0 + -K ≤ bmc + -K  ⇐  0 ≤ bmc
  have hstep : (0 : Q') + -(KtauFix p hp w s)
      ≤ bondMovedCoeff N w p s + -(KtauFix p hp w s) :=
    Q'.add_le_add_right _ _ _ hbmc_nn
  -- (-1)·K ≃ 0 + -K
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hstep
  -- (-1)·K ≃ -K ≃ 0 + -K
  refine Q'.eqv_trans _ _ _ (neg_one_mul_eqv (KtauFix p hp w s)) ?_
  exact Q'.eqv_symm (QPoly.q_zero_add_eqv (-(KtauFix p hp w s)))

/-! ## 7. THE PRECISE NAMED OBLIGATION + the PROVED reduction -/

/-- **THE PRECISE NAMED OBLIGATION — the genuine two-sided quadratic bound.**  For a
fixed bond-moving exponent `p ≥ 1`, fixed fusion degree `N`, and a fixed
nonneg-coefficient test polynomial `P`, the FULL relative-residual bound

    ∀ w, 0 < w → w < 1 → ∀ s, s ≤ N →
      |rrelFix N p hp w _ _ s|  ≤  (1 − w)²·Peval P (yArg w s).

This is the research-grade core: the Chebyshev-U fusion-coefficient analysis of
`K_w^p` against the corrected retuned heat kernel.  It is now SATISFIABLE (the
corrected retune `renormWFix` makes the relative residual `O(1)`, certified
numerically by `P(y) = 3y`); the matching UPPER bound on the off-identity channels
is the deep fusion / theta-function content.  NOT inhabited here.  Carries the
two-sided per-`w` per-`s` bound as a `Type`-level field. -/
structure FusionRelResidualBound (N p : Nat) (hp : 0 < p) (P : QPoly.Poly) : Type where
  /-- The full two-sided quadratic relative-residual bound, on every mode `s`.
  (The honest active content is `s ≤ N`, the certified-mode window — see
  `bmc_ge_identity`, `rrelFix_p1_zero`; for `s > N` the bound is the truncation
  tail, still inside the named obligation since the structure's `hbound` is
  `∀ s`.) -/
  bound : ∀ {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (s : Nat),
    absQ (rrelFix N p hp hw0 hw1 s)
      ≤ ((1 : Q') - w) * ((1 : Q') - w) * Peval P (yArg w s)

/-- **THE SECONDARY NAMED OBLIGATION — the uniform moment certificates.**  The
fixed-cutoff `moment_bound` inputs, named per AF step `k`, at the moving cutoff
`S ≤ N₀`.  These are the "moving-cutoff upgrade": at any concrete `w` each is a
decidable `Q'` fact (fired by `decide`), but the uniform-over-the-flow version is a
named follow-up.  Carries the per-step partition / tail / cutoff certificates. -/
structure UniformMomentCerts (afr : AFRateModulus) (q m r S N₀ : Nat)
    (P : QPoly.Poly) : Type where
  /-- `S ≤ N₀` (cutoff inside the fusion degree). -/
  hSN : S ≤ N₀
  /-- Strict positivity of each weight. -/
  hwpos : ∀ k, (0 : Q') < afr.w k
  /-- The partition positivity guard at the fixed cutoff `N₀`. -/
  hZ : ∀ k, (0 : Q') < Zsum (afr.w k) N₀
  /-- The per-tail-term Casimir domination at each weight. -/
  hsummand : ∀ k k',
    momentTerm (afr.w k) N₀ (hZ k) q P (S + k')
      ≤ tailTerm (afr.w k) (m + 2) (S + k')
  /-- The ratio cutoff inequality at each weight. -/
  hcut : ∀ k,
    Q'.ofNat (2 ^ (m + 2)) * qpow (afr.w k) (2 * S + 3) ≤ HalfPow.half
  /-- The head cutoff inequality at each weight. -/
  hhead : ∀ k, tailTerm (afr.w k) (m + 2) S ≤ dyad (r + 1)

/-- **THE PROVED REDUCTION.**  Given the genuine two-sided fusion residual bound
`FusionRelResidualBound N p hp P` (the research-grade core) and the uniform moment
certificates `UniformMomentCerts` (the moving-cutoff upgrade), CONSTRUCT a
`GenuineResidualDefect.GenuineResidualBound afr q m r S N₀` — the OS2-critical-path
structure whose load-bearing `hbound` field is exactly the per-mode relative
residual.

The construction sets, for each AF step `k`, the relative-residual sequence to the
CONCRETE `rrelFix N p hp (afr.w k) …` at the corrected retune, the test polynomial
to `P`, and discharges:

  * `hbound` — DIRECTLY from `FusionRelResidualBound.bound` (the genuine residual
    bound), instantiated at each weight `afr.w k` (`0 < w_k`, `w_k < 1` from the AF
    interface) and each mode `s`.  We require `N = N₀` so the concrete residual
    `rrelFix N₀ …` matches the obligation's fusion degree.
  * `hP`, `hSN`, `hwpos`, `hZ`, `hsummand`, `hcut`, `hhead` — from
    `UniformMomentCerts` and `hP` directly.

EVERYTHING ELSE is proved; the two genuinely-open inputs are exactly the two named
obligations.  This reduces `GenuineResidualBound` to
`{FusionRelResidualBound, UniformMomentCerts}`. -/
def genuineResidualBound_of_fusionRel
    (afr : AFRateModulus) (q m r S N₀ : Nat) (p : Nat) (hp : 0 < p)
    (P : QPoly.Poly) (hP : nonnegCoeffs P)
    (frb : FusionRelResidualBound N₀ p hp P)
    (umc : UniformMomentCerts afr q m r S N₀ P) :
    GenuineResidualBound afr q m r S N₀ where
  rrel := fun k s => rrelFix N₀ p hp (umc.hwpos k) (afr.w_lt_one k) s
  P := P
  hP := hP
  hSN := umc.hSN
  hwpos := umc.hwpos
  hZ := umc.hZ
  hsummand := umc.hsummand
  hcut := umc.hcut
  hhead := umc.hhead
  hbound := by
    intro k s
    -- the residual bound at weight afr.w k, mode s — directly from the obligation
    exact frb.bound (umc.hwpos k) (afr.w_lt_one k) s

/-- **CAPSTONE — the full-mode positive product floor from the two named obligations.**
Composing `genuineResidualBound_of_fusionRel` with
`GenuineResidualDefect.genuine_fullMode_gap`: given the genuine fusion relative-residual
bound `frb` and the uniform moment certificates `umc`, the running product of the
renormalized full-mode per-block rates has a STRICTLY POSITIVE floor.  This places the
two named obligations `{FusionRelResidualBound, UniformMomentCerts}` directly on the
critical path to the constructive finite-volume gap (the product floor feeds the
cluster bound → continuum mass).  Pure composition; no new analytic content. -/
def fullModeGap_of_fusionRel
    (afr : AFRateModulus) (q m r S N₀ : Nat) (p : Nat) (hp : 0 < p)
    (P : QPoly.Poly) (hP : nonnegCoeffs P)
    (frb : FusionRelResidualBound N₀ p hp P)
    (umc : UniformMomentCerts afr q m r S N₀ P)
    (Mwin : Nat) (hN : N₀ = S + Mwin) :=
  GenuineResidualDefect.genuine_fullMode_gap afr q m r S N₀
    (genuineResidualBound_of_fusionRel afr q m r S N₀ p hp P hP frb umc) Mwin hN

end YMGap.Continuum.BondMovingRelResidual

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BondMovingRelResidual.qpow_eqv_congr_base
#print axioms YMGap.Continuum.BondMovingRelResidual.neg_one_mul_eqv
#print axioms YMGap.Continuum.BondMovingRelResidual.w_le_renormWFix
#print axioms YMGap.Continuum.BondMovingRelResidual.KtauFix_eq_coeffW
#print axioms YMGap.Continuum.BondMovingRelResidual.KtauFix_nonneg
#print axioms YMGap.Continuum.BondMovingRelResidual.KtauFix_pos
#print axioms YMGap.Continuum.BondMovingRelResidual.KtauFix_ge_coeffW
#print axioms YMGap.Continuum.BondMovingRelResidual.fusionProduct_term_le
#print axioms YMGap.Continuum.BondMovingRelResidual.bmc_ge_identity
#print axioms YMGap.Continuum.BondMovingRelResidual.renormWFix_one
#print axioms YMGap.Continuum.BondMovingRelResidual.rrelFix_p1_zero
#print axioms YMGap.Continuum.BondMovingRelResidual.rrelFix_identity_lower
#print axioms YMGap.Continuum.BondMovingRelResidual.rrelFix_lower
#print axioms YMGap.Continuum.BondMovingRelResidual.genuineResidualBound_of_fusionRel

#print axioms YMGap.Continuum.BondMovingRelResidual.fullModeGap_of_fusionRel
