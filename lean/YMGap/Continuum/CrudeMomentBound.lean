/-
Track B / R2 — the **CRUDE w-INDEPENDENT moment bound** that ELIMINATES the
fixed-cutoff moment certificates (`UniformMomentCerts`) from the OS2-critical-path
full-mode gap.

# Why this module exists — the sharp certs are unsatisfiable AND overkill

The full-mode gap was previously reduced (via `genuineResidualBound_of_fusionRel`)
to TWO named obligations: the genuine fusion residual bound
`FusionRelResidualBound` and the fixed-cutoff moment certificates
`UniformMomentCerts` (`hcut`/`hhead`/`hsummand`).  The latter are UNSATISFIABLE
for any `AFRateModulus`: the AF rate forces `w_k → 1` (`1 − w_k ≤ A/(k+B) → 0`),
while the ratio cut `hcut : 2^{m+2}·w_k^{2S+3} ≤ 1/2` needs `w_k` bounded away
from `1`.  They are ALSO overkill: since `∑_k (1−w_k)² < ∞` along the AF rate, the
per-step quadratic margin `(1−w_k)²` already supplies summability, and a CRUDE
`w`-INDEPENDENT moment bound suffices for the product floor — no moving cutoff, no
dyadic tail modulus, no per-tail-term Casimir domination.

# The crude per-mode bound (the analytic heart — pure monotonicity)

For `s < N` and `0 ≤ w ≤ 1`,

    momentTerm w N hZ q P s  ≤  cterm q P s
      :=  (1 + C₄(s))^q · Peval P (C₄(s)),

a `w`-INDEPENDENT bound, because:
  (i)   `μ w N hZ s ≤ 1`  — the `s`-th summand `(s+1)²·w^{C₄(s)}` is one of the
        nonnegative terms of `Zsum w N` (`μ_le_one`, reused);
  (ii)  `qfac w s = 1 + (1−w)·C₄(s) ≤ 1 + C₄(s)` (since `1 − w ≤ 1`), so
        `qfac^q ≤ (1 + C₄(s))^q` (`pow_le_pow_of_le`);
  (iii) `yArg w s = (1−w)·C₄(s) ≤ C₄(s)`, so `Peval P (yArg) ≤ Peval P (C₄(s))`
        (`Peval_mono`, `P` nonneg-coeff).

Summing over `s < n ≤ N` gives the `w`-independent

    momentSum w N hZ q P n  ≤  crudeSum q P n  :=  ∑_{s<n} cterm q P s.

# What this DELIVERS

  * `Zsum_pos` (the `0 < N` form) — discharges the only needed partition guard
    `hZ` directly.
  * `momentTerm_le_cterm` / `momentSum_le_crudeSum` — the crude bound.
  * `fullModeDefect_crude` — a `FullModeAssembly.FullModeDefect` built with
    `M := crudeSum q P N₀` and `d k := scaledNorm (afr.w k) N₀ … q (rr k)`, whose
    clean quadratic bound `d k ≤ M·(1−w_k)²` chains `scaledNorm_le_momentSum`
    (needs ONLY the residual bound `hb`) with `momentSum_le_crudeSum`.  NO
    `hcut`/`hhead`/`hsummand` — the moment side is fully discharged.
  * `fullModeGap_crude` / `fullModeGap_crude_of_fusionRel` — the STRICTLY POSITIVE
    product floor, conditional ONLY on `FusionRelResidualBound` (plus a mild
    `0 < afr.w k` side-condition).  `UniformMomentCerts` is ELIMINATED.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and composition over already-proved engines; every
load-bearing declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`.  All constants
and moduli are `Type`-level data.
-/

import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.BondMovingMoment
import YMGap.Continuum.FullModeAssembly
import YMGap.Continuum.GenuineResidualDefect
import YMGap.Continuum.BondMovingRelResidual
import YMGap.Continuum.AFRateCalibration

namespace YMGap.Continuum.CrudeMomentBound

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.GenuineResidualDefect
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.AFRateCalibration

/-! ## 1. Partition positivity at `0 < N` (discharging the `hZ` guard) -/

/-- **`Zsum w N > 0` for `0 < w` and `0 < N`.**  Reduces to the existing
`BondMovingScaledNorm.Zsum_pos` (stated at `N+1`) by writing `N = (N-1)+1`. -/
theorem Zsum_pos {w : Q'} (hw : (0 : Q') < w) {N : Nat} (hN : 0 < N) :
    (0 : Q') < Zsum w N := by
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [hM]
  exact BondMovingScaledNorm.Zsum_pos hw M

/-! ## 2. The crude per-mode bound -/

/-- **The crude `w`-independent per-mode bound constant**
`cterm q P s = (1 + C₄(s))^q · Peval P (C₄(s))`. -/
def cterm (q : Nat) (P : Poly) (s : Nat) : Q' :=
  ((1 : Q') + Q'.ofNat (c4 s)) ^ q * Peval P (Q'.ofNat (c4 s))

/-- `cterm` is nonnegative (a power of `1 + C₄(s) ≥ 0` times `Peval P (C₄(s)) ≥ 0`
for nonneg-coefficient `P`). -/
theorem cterm_nonneg (q : Nat) (P : Poly) (hP : nonnegCoeffs P) (s : Nat) :
    (0 : Q') ≤ cterm q P s := by
  refine Q'.mul_nonneg _ _ (Q'.pow_nonneg _ ?_ q) (Peval_nonneg P hP (zero_le_ofNat _))
  exact Q'.zero_le_add _ _ (by decide) (zero_le_ofNat _)

/-- **THE CRUDE PER-MODE MOMENT BOUND.**  For `s < N`, `0 < w ≤ 1`, and a
nonneg-coefficient test polynomial `P`,

    momentTerm w N hZ q P s  ≤  cterm q P s    (w-INDEPENDENT).

PROOF.  `μ(s) ≤ 1` (`μ_le_one`); `qfac(w,s) ≤ 1 + C₄(s)` (`qfac_le_w0`), so
`qfac^q ≤ (1+C₄(s))^q` (`pow_le_pow_of_le`); `yArg w s ≤ C₄(s)` (`yArg_le_w0`), so
`Peval P (yArg) ≤ Peval P (C₄(s))` (`Peval_mono`).  All factors nonnegative. -/
theorem momentTerm_le_cterm {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat) (P : Poly) (hP : nonnegCoeffs P)
    (s : Nat) (hsN : s < N) :
    momentTerm w N hZ q P s ≤ cterm q P s := by
  show μ w N hZ s * (qfac w s ^ q * Peval P (yArg w s))
      ≤ ((1 : Q') + Q'.ofNat (c4 s)) ^ q * Peval P (Q'.ofNat (c4 s))
  have hw0' : (0 : Q') ≤ w := Q'.le_of_lt hw0
  -- nonnegativity facts
  have hqfacnn : (0 : Q') ≤ qfac w s := qfac_nonneg hw1 s
  have hqfacpownn : (0 : Q') ≤ qfac w s ^ q := Q'.pow_nonneg _ hqfacnn q
  have hyargnn : (0 : Q') ≤ yArg w s := yArg_nonneg hw1 s
  have hPynn : (0 : Q') ≤ Peval P (yArg w s) := Peval_nonneg P hP hyargnn
  have hbasenn : (0 : Q') ≤ (1 : Q') + Q'.ofNat (c4 s) :=
    Q'.zero_le_add _ _ (by decide) (zero_le_ofNat _)
  have hbasepownn : (0 : Q') ≤ ((1 : Q') + Q'.ofNat (c4 s)) ^ q :=
    Q'.pow_nonneg _ hbasenn q
  -- (ii) qfac^q ≤ (1+C₄ s)^q
  have hqbase : qfac w s ≤ (1 : Q') + Q'.ofNat (c4 s) := qfac_le_w0 hw0' s
  have hqfacpow : qfac w s ^ q ≤ ((1 : Q') + Q'.ofNat (c4 s)) ^ q :=
    pow_le_pow_of_le hqfacnn hqbase q
  -- (iii) P(yArg) ≤ P(C₄ s)
  have hyle : yArg w s ≤ Q'.ofNat (c4 s) := yArg_le_w0 hw0' s
  have hPmono : Peval P (yArg w s) ≤ Peval P (Q'.ofNat (c4 s)) :=
    Peval_mono P hP hyargnn hyle
  have hPSnn : (0 : Q') ≤ Peval P (Q'.ofNat (c4 s)) :=
    Peval_nonneg P hP (zero_le_ofNat _)
  -- combine the test factor: qfac^q·P(yArg) ≤ (1+C₄ s)^q·P(C₄ s)
  have hfac : qfac w s ^ q * Peval P (yArg w s)
      ≤ ((1 : Q') + Q'.ofNat (c4 s)) ^ q * Peval P (Q'.ofNat (c4 s)) := by
    have h1 : qfac w s ^ q * Peval P (yArg w s)
        ≤ ((1 : Q') + Q'.ofNat (c4 s)) ^ q * Peval P (yArg w s) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hqfacpow hPynn
    have h2 : ((1 : Q') + Q'.ofNat (c4 s)) ^ q * Peval P (yArg w s)
        ≤ ((1 : Q') + Q'.ofNat (c4 s)) ^ q * Peval P (Q'.ofNat (c4 s)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hPmono hbasepownn
    exact Q'.le_trans' _ _ _ h1 h2
  -- (i) μ ≤ 1, combine
  have hμle : μ w N hZ s ≤ (1 : Q') := μ_le_one hw0 N hZ s hsN
  have hfacnn : (0 : Q') ≤ qfac w s ^ q * Peval P (yArg w s) :=
    Q'.mul_nonneg _ _ hqfacpownn hPynn
  have hA : μ w N hZ s * (qfac w s ^ q * Peval P (yArg w s))
      ≤ (1 : Q') * (qfac w s ^ q * Peval P (yArg w s)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hμle hfacnn
  have hB : (1 : Q') * (qfac w s ^ q * Peval P (yArg w s))
      ≤ (1 : Q') * (((1 : Q') + Q'.ofNat (c4 s)) ^ q * Peval P (Q'.ofNat (c4 s))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hfac (by decide)
  refine Q'.le_trans' _ _ _ hA (Q'.le_trans' _ _ _ hB ?_)
  -- 1·cterm ≃ cterm
  exact Q'.le_of_eqv (Q'.one_mul_eqv _)

/-! ## 3. The crude `w`-independent moment-sum bound -/

/-- **The crude `w`-independent moment-sum bound constant**
`crudeSum q P n = ∑_{s<n} cterm q P s`. -/
def crudeSum (q : Nat) (P : Poly) (n : Nat) : Q' :=
  RationalTail.finSum (cterm q P) n

theorem crudeSum_nonneg (q : Nat) (P : Poly) (hP : nonnegCoeffs P) (n : Nat) :
    (0 : Q') ≤ crudeSum q P n :=
  FullModeAssembly.finSum_nonneg (fun s => cterm_nonneg q P hP s) n

/-- **THE CRUDE MOMENT-SUM BOUND.**  For `n ≤ N`, `0 < w ≤ 1`, and a
nonneg-coefficient test polynomial `P`,

    momentSum w N hZ q P n  ≤  crudeSum q P n    (w-INDEPENDENT).

PROOF.  Termwise `momentTerm_le_cterm` (each `s < n ≤ N`), lifted to the finite
sum by `finSum_le_termwise`. -/
theorem momentSum_le_crudeSum {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat) (P : Poly) (hP : nonnegCoeffs P)
    (n : Nat) (hnN : n ≤ N) :
    momentSum w N hZ q P n ≤ crudeSum q P n := by
  show RationalTail.finSum (fun s => momentTerm w N hZ q P s) n
      ≤ RationalTail.finSum (cterm q P) n
  -- range-restricted termwise: only `s < n ≤ N` is needed, so `s < N` holds.
  refine YMGap.Constructive.finSum_le_lt
    (fun s => momentTerm w N hZ q P s) (cterm q P) n ?_
  intro s hs
  exact momentTerm_le_cterm hw0 hw1 N hZ q P hP s (Nat.lt_of_lt_of_le hs hnN)

/-! ## 4. The crude full-mode defect (NO moment certificates) -/

/-- **THE CRUDE FULL-MODE DEFECT.**  Given an AF rate `afr` with strictly positive
weights, a nonneg-coefficient test polynomial `P`, residual sequences `rr` bounded
per mode by `(1−w_k)²·Peval P (yArg w_k s)` (the genuine residual bound `hb`),
build a `FullModeAssembly.FullModeDefect afr` with

    M  =  crudeSum q P N₀          (w-INDEPENDENT, NO moment certificates),
    d k  =  scaledNorm (w_k) N₀ … q (rr k).

The clean quadratic bound `d k ≤ M·(1−w_k)²` chains the summation half
`scaledNorm_le_momentSum` (needs ONLY `hb`) with the crude moment-sum bound
`momentSum_le_crudeSum`.  NO `hcut`/`hhead`/`hsummand` — the partition guard `hZ`
is discharged directly by `Zsum_pos`. -/
def fullModeDefect_crude (afr : AFRateModulus) (q N₀ : Nat) (hN0 : 0 < N₀)
    (P : Poly) (hP : nonnegCoeffs P) (hwpos : ∀ k, (0 : Q') < afr.w k)
    (rr : Nat → Nat → Q')
    (hb : ∀ k s, absQ (rr k s)
      ≤ ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k) * Peval P (yArg (afr.w k) s)) :
    FullModeDefect afr where
  d := fun k => scaledNorm (afr.w k) N₀ (Zsum_pos (hwpos k) hN0) q (rr k)
  d_nonneg := by
    intro k
    show (0 : Q') ≤ fsum
      (fun s => μ (afr.w k) N₀ (Zsum_pos (hwpos k) hN0) s
        * (qfac (afr.w k) s ^ q * absQ (rr k s))) N₀
    refine fsum_nonneg (fun s => ?_) N₀
    refine Q'.mul_nonneg _ _ (μ_nonneg (afr.w_nonneg k) N₀ (Zsum_pos (hwpos k) hN0) s) ?_
    exact Q'.mul_nonneg _ _
      (Q'.pow_nonneg _ (qfac_nonneg (Q'.le_of_lt (afr.w_lt_one k)) s) q)
      (absQ_nonneg (rr k s))
  M := crudeSum q P N₀
  M_nonneg := crudeSum_nonneg q P hP N₀
  d_quad := by
    intro k
    have hw0 : (0 : Q') ≤ afr.w k := afr.w_nonneg k
    have hw1 : afr.w k ≤ (1 : Q') := Q'.le_of_lt (afr.w_lt_one k)
    have hmarnn : (0 : Q') ≤ ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k) :=
      Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hw1) (Q'.sub_nonneg_of_le hw1)
    -- (1) summation half (at the scaled-norm cutoff N₀)
    have hsum : scaledNorm (afr.w k) N₀ (Zsum_pos (hwpos k) hN0) q (rr k)
        ≤ ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k)
            * momentSum (afr.w k) N₀ (Zsum_pos (hwpos k) hN0) q P N₀ :=
      scaledNorm_le_momentSum hw0 hw1 N₀ (Zsum_pos (hwpos k) hN0) q P (rr k) (hb k)
    -- (2) crude moment-sum bound, at window N₀ ≤ N₀
    have hmom : momentSum (afr.w k) N₀ (Zsum_pos (hwpos k) hN0) q P N₀
        ≤ crudeSum q P N₀ :=
      momentSum_le_crudeSum (hwpos k) hw1 N₀ (Zsum_pos (hwpos k) hN0) q P hP N₀
        (Nat.le_refl N₀)
    -- chain: scaledNorm ≤ (1−w)²·momentSum ≤ (1−w)²·crudeSum ≃ crudeSum·(1−w)²
    have hstep : ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k)
          * momentSum (afr.w k) N₀ (Zsum_pos (hwpos k) hN0) q P N₀
        ≤ ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k) * crudeSum q P N₀ :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hmom hmarnn
    refine Q'.le_trans' _ _ _ hsum (Q'.le_trans' _ _ _ hstep ?_)
    exact Q'.le_of_eqv
      (Q'.mul_comm_eqv (((1 : Q') - afr.w k) * ((1 : Q') - afr.w k)) (crudeSum q P N₀))

/-! ## 5. The crude full-mode gap (conditional ONLY on the residual bound) -/

/-- **THE CRUDE FULL-MODE GAP.**  Along ANY AF rate `afr` with strictly positive
weights, given ONLY the genuine per-mode residual bound `hb` (and a nonneg-coeff
test polynomial `P`), the running product of the renormalized full-mode per-block
rates has a STRICTLY POSITIVE floor.  This fires `fullMode_gap_of_AFRate` on the
crude defect — NO moment certificates (`hcut`/`hhead`/`hsummand`) are consumed. -/
def fullModeGap_crude (afr : AFRateModulus) (q N₀ : Nat) (hN0 : 0 < N₀)
    (P : Poly) (hP : nonnegCoeffs P) (hwpos : ∀ k, (0 : Q') < afr.w k)
    (rr : Nat → Nat → Q')
    (hb : ∀ k s, absQ (rr k s)
      ≤ ((1 : Q') - afr.w k) * ((1 : Q') - afr.w k) * Peval P (yArg (afr.w k) s)) :
    Σ' (floor : CReal) (ε : Q'),
      (0 : Q') < ε ∧ ExpPos.geRat floor ε
      ∧ ∀ n, CReal.leRat floor
          (RGGapPersistence.prodPrefix
            (fmTailRate afr (fullModeDefect_crude afr q N₀ hN0 P hP hwpos rr hb)
              (fmCutoff afr (fullModeDefect_crude afr q N₀ hN0 P hP hwpos rr hb))) n) :=
  fullMode_gap_of_AFRate afr (fullModeDefect_crude afr q N₀ hN0 P hP hwpos rr hb)

/-! ## 6. THE PAYOFF — the crude gap from `FusionRelResidualBound` ALONE -/

/-- **THE PAYOFF.**  Specializing `fullModeGap_crude` with the CONCRETE genuine
relative residual `rrelFix` and the residual bound supplied by
`FusionRelResidualBound.bound`, the STRICTLY POSITIVE full-mode product floor is
conditional ONLY on:

  * `FusionRelResidualBound N₀ p hp P` — the single genuine (research-grade) fusion
    residual obligation, AND
  * `hwpos : ∀ k, 0 < afr.w k` — a mild side-condition on the AF rate (the divisor
    positivity of `rrelFix`), a named HYPOTHESIS, NOT an obligation structure.

The fixed-cutoff moment certificates `UniformMomentCerts`
(`hcut`/`hhead`/`hsummand`) are ELIMINATED: the crude `w`-independent moment bound
`crudeSum` replaces them entirely (they were unsatisfiable along any AF rate, and
overkill since `∑ (1−w_k)² < ∞`). -/
def fullModeGap_crude_of_fusionRel
    (afr : AFRateModulus) (q N₀ : Nat) (hN0 : 0 < N₀) (p : Nat) (hp : 0 < p)
    (P : Poly) (hP : nonnegCoeffs P) (hwpos : ∀ k, (0 : Q') < afr.w k)
    (frb : FusionRelResidualBound N₀ p hp P) :
    Σ' (floor : CReal) (ε : Q'),
      (0 : Q') < ε ∧ ExpPos.geRat floor ε
      ∧ ∀ n, CReal.leRat floor
          (RGGapPersistence.prodPrefix
            (fmTailRate afr
              (fullModeDefect_crude afr q N₀ hN0 P hP hwpos
                (fun k s => rrelFix N₀ p hp (hwpos k) (afr.w_lt_one k) s)
                (fun k s => frb.bound (hwpos k) (afr.w_lt_one k) s))
              (fmCutoff afr
                (fullModeDefect_crude afr q N₀ hN0 P hP hwpos
                  (fun k s => rrelFix N₀ p hp (hwpos k) (afr.w_lt_one k) s)
                  (fun k s => frb.bound (hwpos k) (afr.w_lt_one k) s)))) n) :=
  fullModeGap_crude afr q N₀ hN0 P hP hwpos
    (fun k s => rrelFix N₀ p hp (hwpos k) (afr.w_lt_one k) s)
    (fun k s => frb.bound (hwpos k) (afr.w_lt_one k) s)

end YMGap.Continuum.CrudeMomentBound

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.CrudeMomentBound.Zsum_pos
#print axioms YMGap.Continuum.CrudeMomentBound.cterm_nonneg
#print axioms YMGap.Continuum.CrudeMomentBound.momentTerm_le_cterm
#print axioms YMGap.Continuum.CrudeMomentBound.crudeSum_nonneg
#print axioms YMGap.Continuum.CrudeMomentBound.momentSum_le_crudeSum
#print axioms YMGap.Continuum.CrudeMomentBound.fullModeDefect_crude
#print axioms YMGap.Continuum.CrudeMomentBound.fullModeGap_crude
#print axioms YMGap.Continuum.CrudeMomentBound.fullModeGap_crude_of_fusionRel
