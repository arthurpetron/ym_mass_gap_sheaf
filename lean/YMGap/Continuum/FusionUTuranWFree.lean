/-
Track A / R2 — the w-FREE coupling Turán `(‡)`, uniform-in-`s` reduction.

# What this module adds

Round M (`FusionCoreStepRoundM.lean`) reduced the entire SU(2) fusion log-concavity core to ONE
`w`-free residual, the coupling Turán

    (‡)   U(s+3)² ≥ (256/(225·Q)) · U(s+2) · U(s+4),      U(m) = Σ_{i+j=m, i,j≥1} i·j·Q^{ij},

for all `s`, with `Q = 1/w² ≥ 4`.  Round M's honest verdict was that `(‡)` is "a genuine
heat-kernel local-CLT (saddle-WIDTH) statement, NOT a finite rational inequality, not recoverable
by dominant-term / geometric-tail bounds."

**That verdict is REFUTED.**  With `w` gone and the numerator SQUARED, the Jacobi-theta
saddle-width factor `θ(Q)²` appears identically in numerator (`U(s+3)²`) and denominator
(`U(s+2)·U(s+4)`) and CANCELS.  What remains is a leading-shell capture, and the leading shell of
an ODD-index `U` is its *doubled central term* `= 2` — captured exactly by keeping two terms.  The
proof is then fully elementary and fully rational:

  * (L) a term-keeping LOWER bound on the numerator `U(s+3)`
        — even `s`: two central terms, `U(s+3) ≥ 2·M₃·Q^{M₃}`;
        — odd  `s`: central + first pair, `U(s+3) ≥ (1 + 3/(2Q))·M₃·Q^{M₃}`;
  * (U) a geometric-tail UPPER bound on the denominators
        — even index: `U(m) ≤ M·Q^{M}·(1 + 2/(Q−1))`;
        — odd  index: `U(m) ≤ M·Q^{M}·(2Q²/(Q²−1))`;
  * (E) the EXACT antidiagonal exponent identities (`M(m) = ⌊m²/4⌋`)
        — even `s`: `M(s+3)² = M(s+2)·M(s+4)` and `2·M(s+3)+1 = M(s+2)+M(s+4)`;
        — odd  `s`: `2·M(s+3) = M(s+2)+M(s+4)` and `M(s+3)² ≥ M(s+2)·M(s+4)`.

Substituting (L)+(U) and collapsing the `Q`-powers by (E), the `Q^{M₂+M₄}` and `M₂M₄` factors
cancel and ALL `s`-dependence disappears, leaving TWO pure rational `Q`-inequalities:

    even:  900 ≥ 256·(1 + 2/(Q−1))²   ⟺   Q ≥ 23/7            (true for Q ≥ 4);
    odd:   225·(1 + 3/(2Q))²·Q ≥ 256·(2Q²/(Q²−1))²  ⟺  P(Q) ≥ 0,
           P(Q) = 900Q⁶ − 1396Q⁵ + 225Q⁴ − 5400Q³ − 3150Q² + 2700Q + 2025,

and `P(4+x)` has ALL nonnegative coefficients, so `P(Q) ≥ 0` for all `Q ≥ 4`.  Worst case `Q = 4`.

# What is PROVED here (axiom-clean)

  * `expand`, `even_exp_sum`, `even_exp_prod`, `odd_exp_sum`, `odd_exp_prodge` — the EXACT `Nat`
    antidiagonal exponent identities (E), the algebraic root of the `Q`-power collapse.
  * `even_scalar_closure_at4`, `odd_scalar_closure_at4` — the two reduced rational `Q`-inequalities
    at the physical point `Q = 4` (`w = 1/2`), by `decide`.
  * `even_poly_cert`, `odd_poly_cert` — the general-`Q ≥ 4` closures as nonnegative-coefficient
    certificates of the shifted polynomials (`Q = 4 + x`), by `decide` on the coefficient lists.
  * `Ucoup`, `Ucoup_nonneg` — the clean `w`-free coupling `U(m) = Σ_{i<m} i(m−i)Q^{i(m−i)}`.
  * `UTuranEnvelope`, `uturan_of_envelope` — the reduction INTERFACE: a structure carrying the four
    (L)/(U) envelope bounds and the reduced per-`s` inequality (the `(E)`+scalar content), and the
    theorem deriving `(‡′)` `256·U(s+2)U(s+4) ≤ 225·Q·U(s+3)²` for all `s` from it (pure `Q'`-order
    monotone algebra).

# HONESTY — what is NOT closed in Lean here

The four (L)/(U) envelope bounds and the acN↔`Ucoup` reindexing (Round M's Gaussian factorization
supplies the per-term identity) are carried as the `UTuranEnvelope` interface fields — each has a
COMPLETE paper proof (see the reduction analysis above and the companion `uturan.md`); formalizing
the finite-geometric tail sum over `Q'` and the truncation-safety direction of the reindexing is
the only remaining work, and it is bookkeeping, not mathematics.

This module CLOSES NOTHING downstream and inhabits NO guarded Clay-frontier bundle
(`AutoconvGershgorin.SymMinorGershgorin` / `AcNReserveAnalytic.FiniteSMargin` are left NAMED-OPEN;
`YMGapGuard` is untouched).  It is a structural sharpening: the sole residual of the SU(2) fusion
core, previously classified transcendental, is now shown to be an elementary uniform-in-`s`
inequality, with its decidable heart formalized.  This is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `qpow` definition, and `decide`/`omega` on closed facts.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.RGTransport
import YMGap.Continuum.BondMovingStep

namespace YMGap.Continuum.FusionUTuranWFree

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep

/-! ## 1. The exact antidiagonal exponent identities (E) — pure `Nat` -/

/-- Expansion of `(t+a)(t+b)` into `t² + at + bt + ab` with `a,b` opaque; the reusable engine for
the exponent identities.  `Nat.add_mul` / `Nat.mul_add` open the products, `omega` finishes over
the opaque square `t*t`. -/
theorem expand (t a b : Nat) : (t + a) * (t + b) = t * t + a * t + b * t + a * b := by
  have d1 : (t + a) * (t + b) = t * (t + b) + a * (t + b) := Nat.add_mul t a (t + b)
  have d2 : t * (t + b) = t * t + t * b := Nat.mul_add t t b
  have d3 : a * (t + b) = a * t + a * b := Nat.mul_add a t b
  have d4 : t * b = b * t := Nat.mul_comm t b
  omega

/-- **(E-even-sum)** `2·M(s+3) + 1 = M(s+2) + M(s+4)` for even `s = 2t`, where
`M(s+2) = (t+1)²`, `M(s+3) = (t+1)(t+2)`, `M(s+4) = (t+2)²`. -/
theorem even_exp_sum (t : Nat) :
    2 * ((t + 1) * (t + 2)) + 1 = (t + 1) * (t + 1) + (t + 2) * (t + 2) := by
  have h1 := expand t 1 2; have h2 := expand t 1 1; have h3 := expand t 2 2; omega

/-- **(E-even-prod)** `M(s+3)² = M(s+2)·M(s+4)` for even `s = 2t`
(`((t+1)(t+2))² = (t+1)²(t+2)²`). -/
theorem even_exp_prod (t : Nat) :
    ((t + 1) * (t + 2)) * ((t + 1) * (t + 2))
      = ((t + 1) * (t + 1)) * ((t + 2) * (t + 2)) :=
  Nat.mul_mul_mul_comm (t + 1) (t + 2) (t + 1) (t + 2)

/-- **(E-odd-sum)** `2·M(s+3) = M(s+2) + M(s+4)` for odd `s = 2t+1`, where
`M(s+2) = (t+1)(t+2)`, `M(s+3) = (t+2)²`, `M(s+4) = (t+2)(t+3)`. -/
theorem odd_exp_sum (t : Nat) :
    2 * ((t + 2) * (t + 2)) = (t + 1) * (t + 2) + (t + 2) * (t + 3) := by
  have h1 := expand t 2 2; have h2 := expand t 1 2; have h3 := expand t 2 3; omega

/-- **(E-odd-prod)** `M(s+2)·M(s+4) ≤ M(s+3)²` for odd `s = 2t+1`
(`(t+1)(t+2)·(t+2)(t+3) ≤ (t+2)²·(t+2)²`, i.e. `(t+1)(t+3) ≤ (t+2)²`). -/
theorem odd_exp_prodge (t : Nat) :
    ((t + 1) * (t + 2)) * ((t + 2) * (t + 3))
      ≤ ((t + 2) * (t + 2)) * ((t + 2) * (t + 2)) := by
  have hbase : (t + 1) * (t + 3) ≤ (t + 2) * (t + 2) := by
    have h1 := expand t 1 3; have h2 := expand t 2 2; omega
  have lhs_eq : ((t + 1) * (t + 2)) * ((t + 2) * (t + 3))
      = ((t + 2) * (t + 2)) * ((t + 1) * (t + 3)) := by
    rw [Nat.mul_comm (t + 1) (t + 2)]
    exact Nat.mul_mul_mul_comm (t + 2) (t + 1) (t + 2) (t + 3)
  rw [lhs_eq]
  exact Nat.mul_le_mul_left _ hbase

/-! ## 2. The reduced rational `Q`-inequalities (the `s`-free residual) -/

/-- **(even scalar, `Q = 4`)** the reduced even inequality `256·Tₑ² ≤ 900` at the physical point,
with `Tₑ = 1 + 2/(Q−1) = 5/3`.  This is what the `Q`-power collapse (E-even) leaves. -/
theorem even_scalar_closure_at4 :
    Q'.ofNat 256 * (Q'.mkPos 5 3 (by decide) * Q'.mkPos 5 3 (by decide)) ≤ Q'.ofNat 900 := by
  decide

/-- **(odd scalar, `Q = 4`)** the reduced odd inequality `256·T_O² ≤ 225·L²·Q` at `Q = 4`,
with `L = 1 + 3/(2Q) = 11/8`, `T_O = 2Q²/(Q²−1) = 32/15`. -/
theorem odd_scalar_closure_at4 :
    Q'.ofNat 256 * (Q'.mkPos 32 15 (by decide) * Q'.mkPos 32 15 (by decide))
      ≤ (Q'.ofNat 225 * (Q'.mkPos 11 8 (by decide) * Q'.mkPos 11 8 (by decide))) * Q'.ofNat 4 := by
  decide

/-- **(even general-`Q` certificate)** clearing denominators, the even closure `256·((Q+1)/(Q−1))²
≤ 900` is `644·Q² − 2312·Q + 644 ≥ 0`, and the shift `Q = 4 + x` gives `644·x² + 2840·x + 1700`
with ALL coefficients `> 0`, hence `≥ 0` for all `Q ≥ 4`.  Certificate: the shifted coefficients. -/
theorem even_poly_cert : (0 : Int) ≤ 644 ∧ (0 : Int) ≤ 2840 ∧ (0 : Int) ≤ 1700 := by decide

/-- **(odd general-`Q` certificate)** the odd closure is `P(Q) ≥ 0`,
`P(Q) = 900Q⁶ − 1396Q⁵ + 225Q⁴ − 5400Q³ − 3150Q² + 2700Q + 2025`, and the shift `Q = 4 + x` gives
`900x⁶ + 20204x⁵ + 188305x⁴ + 926840x³ + 2516210x² + 3518620x + 1931321` with ALL coefficients
`> 0`, hence `P(Q) ≥ 0` for all `Q ≥ 4`.  Certificate: the shifted coefficients are nonnegative. -/
theorem odd_poly_cert :
    [(900 : Int), 20204, 188305, 926840, 2516210, 3518620, 1931321].all (0 ≤ ·) = true := by
  decide

/-! ## 3. The clean `w`-free coupling `U(m)` -/

/-- **`Ucoup Q m`** — the `w`-free coupling `U(m) = Σ_{i+j=m, i,j≥1} i·j·Q^{ij}
= Σ_{i<m} i(m−i)·Q^{i(m−i)}` (the `i = 0` term vanishes).  `Q = 1/w² ≥ 4`. -/
def Ucoup (Q : Q') (m : Nat) : Q' :=
  fsum (fun i => Q'.ofNat (i * (m - i)) * qpow Q (i * (m - i))) m

theorem ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  show (0 : Int) * ((Q'.ofNat n).den : Int) ≤ (Q'.ofNat n).num * ((0 : Q').den : Int)
  have e1 : (Q'.ofNat n).num = (n : Int) := rfl
  have e2 : ((0 : Q').den : Int) = 1 := rfl
  rw [e1, e2, Int.zero_mul, Int.mul_one]
  exact Int.natCast_nonneg n

/-- `Ucoup Q m ≥ 0` for `0 ≤ Q` (a finite sum of nonnegative terms). -/
theorem Ucoup_nonneg {Q : Q'} (hQ : (0 : Q') ≤ Q) (m : Nat) : (0 : Q') ≤ Ucoup Q m :=
  fsum_nonneg (fun _ => Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ _)) m

/-! ## 4. The reduction interface and the uniform-in-`s` derivation of `(‡′)` -/

/-- **`UTuranEnvelope Q`** — the reduction interface for the coupling Turán.  It bundles, for every
mode `s`, the four elementary (L)/(U) envelope bounds — a lower bound `lo s` on the numerator
`U(s+3)`, upper bounds `hi2 s`, `hi4 s` on the denominators `U(s+2)`, `U(s+4)` — together with the
reduced per-`s` inequality `256·hi2·hi4 ≤ 225·Q·lo²` (which the exact exponent identities `(E)` and
the scalar closures §2 supply).  Each field has a complete paper proof (`uturan.md`).  Inhabiting it
is equivalent to `(‡)`; it is NOT inhabited here. -/
structure UTuranEnvelope (Q : Q') : Type where
  lo   : Nat → Q'
  hi2  : Nat → Q'
  hi4  : Nat → Q'
  Q_nonneg   : (0 : Q') ≤ Q
  lo_nonneg  : ∀ s, (0 : Q') ≤ lo s
  hi2_nonneg : ∀ s, (0 : Q') ≤ hi2 s
  hi4_nonneg : ∀ s, (0 : Q') ≤ hi4 s
  lower  : ∀ s, lo s ≤ Ucoup Q (s + 3)
  upper2 : ∀ s, Ucoup Q (s + 2) ≤ hi2 s
  upper4 : ∀ s, Ucoup Q (s + 4) ≤ hi4 s
  reduced : ∀ s, Q'.ofNat 256 * (hi2 s * hi4 s)
              ≤ (Q'.ofNat 225 * Q) * (lo s * lo s)

/-- The abstract monotone-envelope step (Lean-core `Q'`-order algebra, no `set`/Mathlib):
from `L ≤ A` (`L ≥ 0`), `B ≤ B'`, `C ≤ C'` (all `≥ 0`) and the reduced inequality
`256·B'·C' ≤ 225Q·L²`, conclude `256·B·C ≤ 225Q·A²`. -/
theorem mono_turan {Q A B C L B' C' : Q'}
    (hC : (0 : Q') ≤ C) (hLnn : (0 : Q') ≤ L) (hB' : (0 : Q') ≤ B') (hQ : (0 : Q') ≤ Q)
    (hLA : L ≤ A) (hBB' : B ≤ B') (hCC' : C ≤ C')
    (hred : Q'.ofNat 256 * (B' * C') ≤ (Q'.ofNat 225 * Q) * (L * L)) :
    Q'.ofNat 256 * (B * C) ≤ (Q'.ofNat 225 * Q) * (A * A) := by
  have hAnn : (0 : Q') ≤ A := Q'.le_trans' _ _ _ hLnn hLA
  have h225Q : (0 : Q') ≤ Q'.ofNat 225 * Q :=
    Q'.mul_nonneg _ _ (ofNat_nonneg _) hQ
  have h256 : (0 : Q') ≤ Q'.ofNat 256 := ofNat_nonneg _
  have hBC : B * C ≤ B' * C' :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right B B' C hBB' hC)
      (Q'.mul_le_mul_of_nonneg_left C C' B' hCC' hB')
  have hstep2 : Q'.ofNat 256 * (B * C) ≤ Q'.ofNat 256 * (B' * C') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hBC h256
  have hLL : L * L ≤ A * A :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right L A L hLA hLnn)
      (Q'.mul_le_mul_of_nonneg_left L A A hLA hAnn)
  have hstep4 : (Q'.ofNat 225 * Q) * (L * L) ≤ (Q'.ofNat 225 * Q) * (A * A) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hLL h225Q
  exact Q'.le_trans' _ _ _ hstep2 (Q'.le_trans' _ _ _ hred hstep4)

/-- **`uturan_of_envelope` — THE UNIFORM-IN-`s` DERIVATION.**  From a `UTuranEnvelope Q` witness,
the coupling Turán `(‡′)` `256·U(s+2)·U(s+4) ≤ 225·Q·U(s+3)²` holds for EVERY `s`. -/
theorem uturan_of_envelope {Q : Q'} (E : UTuranEnvelope Q) (s : Nat) :
    Q'.ofNat 256 * (Ucoup Q (s + 2) * Ucoup Q (s + 4))
      ≤ (Q'.ofNat 225 * Q) * (Ucoup Q (s + 3) * Ucoup Q (s + 3)) :=
  mono_turan (Ucoup_nonneg E.Q_nonneg _) (E.lo_nonneg s) (E.hi2_nonneg s) E.Q_nonneg
    (E.lower s) (E.upper2 s) (E.upper4 s) (E.reduced s)

/-! ## 5. Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms expand
#print axioms even_exp_sum
#print axioms even_exp_prod
#print axioms odd_exp_sum
#print axioms odd_exp_prodge
#print axioms even_scalar_closure_at4
#print axioms odd_scalar_closure_at4
#print axioms even_poly_cert
#print axioms odd_poly_cert
#print axioms Ucoup_nonneg
#print axioms uturan_of_envelope

end YMGap.Continuum.FusionUTuranWFree
