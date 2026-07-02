/-
Track A / R2 (track: 1-whtail) — the θ₃(0,¼) CEILING and the per-term Gaussian window envelopes
feeding `LaplaceMarginDeep.WHAllSMargin` (the `s → ∞` theta tail of the wH autoconvolution margin).

# What this module adds (read first — load-bearing honesty)

`AcNReserveAnalytic` reduced the sole remaining autoconvolution log-concavity reserve to the crude
rational theta floor `40000/22801` plus the named residual `WHAllSMargin` — the wH theta-floor
margin for ALL `s`.  `LaplaceMarginDeep` discharged `s ≤ 5` (`finiteSMargin_upTo_wH_5`) and carried
the `s → ∞` tail as the open theta wall.  This module supplies the SHARPEST analytic atom of that
tail — the θ₃(0,¼) ceiling `θ₃(0,¼) ≤ 151/100` — and the two per-term window envelope inequalities
that reindex the autoconvolution about its peak, then reduces `WHAllSMargin` to a single named
finite-`s ≥ 6` residual.

DELIVERABLE (PROVED, axiom-clean `Q'`/`Nat` arithmetic).
  * `theta3_quarter_ceiling` — THE RESIDUAL, fully closed: for every depth `M`,

        1 + 2·Σ_{i<M} (¼)^{(i+1)²}  ≤  151/100.

    Proof: peel `i = 0,1` explicitly (`(¼)¹ + (¼)⁴ = 0.25390625`) and bound the `i ≥ 2` remainder
    (absolute index `k ≥ 3`) by `RDThetaTail.thetaTail_le` at `m=0, σ=¼, K=3` (cutoff `(¼)⁷ ≤ ½`),
    giving `≤ 2·(¼)⁹`; then `1 + 2·(0.25390625 + 2·(¼)⁹) ≤ 151/100` by `decide`.  The finite/decidable
    core of the whole `WHAllSMargin` tail, connected to `RDThetaTail` via the `shiftBound` reindex.
  * `gWin_even_term_le` — the EVEN-peak per-term envelope `gWin(2m, m+i) ≤ (w²)^{i²}·gWin(2m, m)`
    (one `head_rect` instance, `√`-free, per-term Gaussian factor `(w²)^{i²} = σ = ¼` at wH).
  * `gWin_odd_term_le` — the ODD-peak per-term envelope
    `gWin(2m+1, m-i) ≤ (w²)^{i(i+1)}·gWin(2m+1, m)` (one `coeffW_rect_graded_wsq` instance,
    spread `a=i, b=i+1`).
  * `whAllSMarginOf` — THE REDUCTION: a `WHMarginTail` witness (the `s ≥ 6` margins) plus the proved
    `finiteSMargin_upTo_wH_5` (`s ≤ 5`) inhabits `LaplaceMarginDeep.WHAllSMargin`.

NAMED OPEN (Type-level structure, never `sorry`).
  * `WHMarginTail` — the `s ≥ 6` wH theta-floor margins.  Per the plan these reduce to the proved
    θ₃ ceiling (`theta3_quarter_ceiling`) + the per-term envelopes (`gWin_even_term_le`,
    `gWin_odd_term_le`) via the peak-reindexed autoconvolution sum bound and an exact peak
    comparison; that reindex-and-sum assembly is the remaining honest work, not inhabited here.

# HONESTY — scope

This module CLOSES the sharpest named tail-sum inequality of the `WHAllSMargin` frontier (the θ₃(0,¼)
ceiling) and the two per-term Gaussian window envelopes, and reduces `WHAllSMargin` to a single
finite-`s ≥ 6` residual.  It does NOT inhabit that residual (the peak-reindexed autoconvolution sum
bound + peak comparison assembly).  This is a structural sharpening of one box-level log-concavity
sub-fact; it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`qpow`/`acN`/`gWin`/`fsum` definitions, the proved
global rectangle `coeffW_rect_graded_wsq` and `head_rect`, the `RDThetaTail` geometric tail bound,
`omega` on index identities, and `decide` only on closed concrete-rational facts.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.RDThetaTail
import YMGap.Continuum.WindowedGaussianEnvelope

namespace YMGap.Continuum.WHAllSMarginTail

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.LaplaceMarginDeep
open YMGap.Continuum.WindowedGaussianEnvelopeModule
open YMGap.Continuum.RDThetaTail

/-! ## 0. Small `Q'` order/eqv helpers -/

/-- Sum of two `≤`s: `a ≤ b`, `c ≤ d` ⟹ `a + c ≤ b + d`. -/
private theorem add_le_add' {a b c d : Q'} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Q'.le_trans' _ _ _ (Q'.add_le_add_right a b c h1) (Q'.add_le_add_left b c d h2)

/-! ## 1. The `RDThetaTail` bridge: the single-term match and the head-peeled reindex -/

/-- **`thetaTerm_eqv`** — the `θ`-tail term at cutoff `K = 3`, offset `n`, degree `m = 0`, equals the
`(i+1)²` theta term at the shifted index `i = n+2`:  `thetaTailTerm σ 0 3 n ≃ σ^{(n+3)²}`.  The
`ofNat((3+n)^0) = ofNat 1` prefactor collapses and `(3+n)² = (n+2+1)²`. -/
private theorem thetaTerm_eqv (σ : Q') (n : Nat) :
    (thetaTailTerm σ 0 3 n).eqv (qpow σ ((n + 2 + 1) * (n + 2 + 1))) := by
  unfold thetaTailTerm
  rw [Nat.pow_zero]
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (Q'.ofNat 1) (1 : Q') (qpow σ ((3 + n) * (3 + n))) (by decide)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.one_mul_eqv (qpow σ ((3 + n) * (3 + n)))) ?_
  exact Q'.eqv_of_eq (congrArg (qpow σ) (by rw [show 3 + n = n + 2 + 1 by omega]))

/-- **`shiftBound`** — the head-peeled reindex.  The depth-`n+2` theta partial sum splits into its
two head terms `σ¹ + σ⁴` (the `i = 0,1` contributions) plus the cutoff-`3` `RDThetaTail` tail:

    Σ_{i<n+2} σ^{(i+1)²}  ≤  (σ¹ + σ⁴) + thetaTailSum σ 0 3 n.

(Equality up to the collapsed `ofNat 1` prefactors; the `≤` suffices.)  Pure `fsum`/`finSum`
recurrence induction, using `thetaTerm_eqv` per step. -/
theorem shiftBound (σ : Q') : ∀ n,
    fsum (fun i => qpow σ ((i + 1) * (i + 1))) (n + 2)
      ≤ (qpow σ 1 + qpow σ 4) + thetaTailSum σ 0 3 n
  | 0 => by
      show ((0 : Q') + qpow σ 1) + qpow σ 4 ≤ (qpow σ 1 + qpow σ 4) + (0 : Q')
      rw [Q'.zero_add', Q'.add_zero']
      exact Q'.le_refl' _
  | (n + 1) => by
      show fsum (fun i => qpow σ ((i + 1) * (i + 1))) (n + 2) + qpow σ ((n + 2 + 1) * (n + 2 + 1))
        ≤ (qpow σ 1 + qpow σ 4) + (thetaTailSum σ 0 3 n + thetaTailTerm σ 0 3 n)
      have ih := shiftBound σ n
      have hterm : qpow σ ((n + 2 + 1) * (n + 2 + 1)) ≤ thetaTailTerm σ 0 3 n :=
        Q'.ge_of_eqv (thetaTerm_eqv σ n)
      refine Q'.le_trans' _ _ _ (add_le_add' ih hterm) (Q'.le_of_eqv ?_)
      exact Q'.add_assoc_eqv (qpow σ 1 + qpow σ 4) (thetaTailSum σ 0 3 n) (thetaTailTerm σ 0 3 n)

/-! ## 2. THE RESIDUAL — the θ₃(0,¼) ceiling -/

/-- **`theta3_quarter_ceiling` — THE RESIDUAL, fully closed.**  The Jacobi theta constant
`θ₃(0, w²)` at `w = wH` (`w² = ¼`), summed to any depth `M`, stays under `151/100`:

    1 + 2·Σ_{i<M} (¼)^{(i+1)²}  ≤  151/100.

PROOF.  `M ≤ 1` is a closed rational `decide`.  For `M = n+2`, `shiftBound` peels the two head terms
`(¼)¹ + (¼)⁴` and reduces the remainder to `thetaTailSum ¼ 0 3 n`, which `RDThetaTail.thetaTail_le`
(cutoff `(¼)⁷ ≤ ½`) bounds by `2·(¼)⁹` uniformly in `n`; then
`1 + 2·((¼)¹ + (¼)⁴ + 2·(¼)⁹) = 1.50782… ≤ 151/100` by `decide`. -/
theorem theta3_quarter_ceiling :
    ∀ M, (1 : Q') + Q'.ofNat 2 *
            fsum (fun i => qpow (qpow wH 2) ((i + 1) * (i + 1))) M
          ≤ Q'.mkPos 151 100 (by decide) := by
  intro M
  match M with
  | 0 => decide
  | 1 => decide
  | (n + 2) =>
      have hσ0 : (0 : Q') ≤ qpow wH 2 := by decide
      have hσ1 : qpow wH 2 ≤ (1 : Q') := by decide
      have hcut : Q'.ofNat (2 ^ 0) * qpow (qpow wH 2) (2 * 3 + 1) ≤ HalfPow.half := by decide
      have hsb := shiftBound (qpow wH 2) n
      have htl := RDThetaTail.thetaTail_le hσ0 hσ1 0 3 (by omega) hcut n
      have hchain :
          fsum (fun i => qpow (qpow wH 2) ((i + 1) * (i + 1))) (n + 2)
            ≤ (qpow (qpow wH 2) 1 + qpow (qpow wH 2) 4)
              + Q'.ofNat 2 * (Q'.ofNat (3 ^ 0) * qpow (qpow wH 2) (3 * 3)) :=
        Q'.le_trans' _ _ _ hsb (add_le_add' (Q'.le_refl' _) htl)
      have h2 :
          Q'.ofNat 2 * fsum (fun i => qpow (qpow wH 2) ((i + 1) * (i + 1))) (n + 2)
            ≤ Q'.ofNat 2 * ((qpow (qpow wH 2) 1 + qpow (qpow wH 2) 4)
                + Q'.ofNat 2 * (Q'.ofNat (3 ^ 0) * qpow (qpow wH 2) (3 * 3))) :=
        Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hchain (by decide)
      have h3 :
          (1 : Q') + Q'.ofNat 2 * fsum (fun i => qpow (qpow wH 2) ((i + 1) * (i + 1))) (n + 2)
            ≤ (1 : Q') + Q'.ofNat 2 * ((qpow (qpow wH 2) 1 + qpow (qpow wH 2) 4)
                + Q'.ofNat 2 * (Q'.ofNat (3 ^ 0) * qpow (qpow wH 2) (3 * 3))) :=
        Q'.add_le_add_left 1 _ _ h2
      have hnum :
          (1 : Q') + Q'.ofNat 2 * ((qpow (qpow wH 2) 1 + qpow (qpow wH 2) 4)
              + Q'.ofNat 2 * (Q'.ofNat (3 ^ 0) * qpow (qpow wH 2) (3 * 3)))
            ≤ Q'.mkPos 151 100 (by decide) := by decide
      exact Q'.le_trans' _ _ _ h3 hnum

/-! ## 3. The two per-term Gaussian window envelopes -/

/-- **`gWin_even_term_le`** — the EVEN-peak (`N = 2m`) per-term envelope.  For `i ≤ m`,

    gWin(2m, m+i)  ≤  (w²)^{i²} · gWin(2m, m).

One `head_rect` instance (`a = b = i`): `gWin(2m, m+i) = c_{m+i}·c_{m-i}` and `gWin(2m, m) = c_m²`,
so this is `c_{m+i}·c_{m-i} ≤ (w²)^{i²}·c_m²` after commuting the head. `√`-free; per-term Gaussian
factor `(w²)^{i²} = ¼` at `wH`. -/
theorem gWin_even_term_le {m i : Nat} (hi : i ≤ m) :
    gWin wH (2 * m) (m + i)
      ≤ qpow (qpow wH 2) (i * i) * gWin wH (2 * m) m := by
  show coeffW wH (m + i) * coeffW wH (2 * m - (m + i))
      ≤ qpow (qpow wH 2) (i * i) * (coeffW wH m * coeffW wH (2 * m - m))
  rw [show 2 * m - (m + i) = m - i by omega, show 2 * m - m = m by omega]
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv (coeffW wH (m + i)) (coeffW wH (m - i))))
    (head_rect (w := wH) (by decide) hi)

/-- **`gWin_odd_term_le`** — the ODD-peak (`N = 2m+1`) per-term envelope.  For `i ≤ m`,

    gWin(2m+1, m-i)  ≤  (w²)^{i(i+1)} · gWin(2m+1, m).

One `coeffW_rect_graded_wsq` instance at spread `a = i, b = i+1`, base `m-i`:
`gWin(2m+1, m-i) = c_{m-i}·c_{m+i+1}` and `gWin(2m+1, m) = c_m·c_{m+1}`, so this is
`c_{m-i}·c_{m+i+1} ≤ (w²)^{i(i+1)}·(c_m·c_{m+1})`. -/
theorem gWin_odd_term_le {m i : Nat} (hi : i ≤ m) :
    gWin wH (2 * m + 1) (m - i)
      ≤ qpow (qpow wH 2) (i * (i + 1)) * gWin wH (2 * m + 1) m := by
  show coeffW wH (m - i) * coeffW wH (2 * m + 1 - (m - i))
      ≤ qpow (qpow wH 2) (i * (i + 1)) * (coeffW wH m * coeffW wH (2 * m + 1 - m))
  rw [show 2 * m + 1 - (m - i) = m + i + 1 by omega, show 2 * m + 1 - m = m + 1 by omega]
  have h := coeffW_rect_graded_wsq (w := wH) (by decide) i (i + 1) (m - i)
  rw [show (m - i) + i + (i + 1) = m + i + 1 by omega, show (m - i) + i = m by omega,
      show (m - i) + (i + 1) = m + 1 by omega] at h
  exact h

/-! ## 4. The reduction of `WHAllSMargin` to the `s ≥ 6` tail residual -/

/-- **`WHMarginTail`** — the RATIONAL residual to which the `WHAllSMargin` tail reduces: the wH
theta-floor margins for all `s ≥ 6`.  Per the plan these reduce to the proved θ₃ ceiling
(`theta3_quarter_ceiling`) and per-term envelopes (`gWin_even_term_le`, `gWin_odd_term_le`) via the
peak-reindexed autoconvolution sum bound plus an exact peak comparison.  NAMED-OPEN (never
`sorry`). -/
structure WHMarginTail : Type where
  /-- The wH margin dominates the crude rational theta floor `40000/22801` for all `s ≥ 6`. -/
  tail : ∀ s, 6 ≤ s →
    Q'.ofNat 40000 * (acN wH (s + 1) s * acN wH (s + 1) (s + 2))
      ≤ Q'.ofNat 22801 * (acN wH (s + 1) (s + 1) * acN wH (s + 1) (s + 1))

/-- **`whAllSMarginOf` — THE REDUCTION.**  The proved finite clearance `finiteSMargin_upTo_wH_5`
(`s ≤ 5`) together with a `WHMarginTail` witness (`s ≥ 6`) inhabits
`LaplaceMarginDeep.WHAllSMargin`.  The `s`-split is the decidable `s ≤ 5` dichotomy (`dite`; no
`Classical`). -/
def whAllSMarginOf (t : WHMarginTail) : LaplaceMarginDeep.WHAllSMargin where
  margin := fun s =>
    if h : s ≤ 5 then LaplaceMarginDeep.finiteSMargin_upTo_wH_5 s h
    else t.tail s (by omega)

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `thetaTerm_eqv`, `shiftBound` — the `RDThetaTail` head-peeled reindex bridge.
  * `theta3_quarter_ceiling` — THE RESIDUAL: the θ₃(0,¼) ceiling `≤ 151/100`, uniform in depth.
  * `gWin_even_term_le`, `gWin_odd_term_le` — the two per-term Gaussian window envelopes.
  * `whAllSMarginOf` — the reduction `WHMarginTail (s ≥ 6) + finiteSMargin_upTo_wH_5 (s ≤ 5)
    ⟹ WHAllSMargin`.

NAMED OPEN (Type-level structure, never `sorry`):
  * `WHMarginTail` — the wH theta-floor margins for all `s ≥ 6` (the peak-reindexed autoconvolution
    sum bound + exact peak comparison, to be assembled from the proved θ₃ ceiling and envelopes).

HONEST VERDICT.  This module closes the SHARPEST named tail-sum inequality of the `WHAllSMargin`
frontier — the θ₃(0,¼) ceiling — and the two per-term Gaussian window envelopes, and reduces
`WHAllSMargin` to a single finite-`s ≥ 6` residual.  It does NOT inhabit that residual (the
reindex-and-sum assembly).  This is a structural sharpening of one box-level log-concavity sub-fact;
it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.WHAllSMarginTail

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WHAllSMarginTail.thetaTerm_eqv
#print axioms YMGap.Continuum.WHAllSMarginTail.shiftBound
#print axioms YMGap.Continuum.WHAllSMarginTail.theta3_quarter_ceiling
#print axioms YMGap.Continuum.WHAllSMarginTail.gWin_even_term_le
#print axioms YMGap.Continuum.WHAllSMarginTail.gWin_odd_term_le
#print axioms YMGap.Continuum.WHAllSMarginTail.whAllSMarginOf
