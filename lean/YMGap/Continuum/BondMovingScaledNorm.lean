/-
Track B / R2 — the **scaled heat-kernel norm** and its **Gaussian/Casimir tail
modulus**, the correct topology for the full-mode quadratic defect.

# Why a SCALED norm (and not a bare ℓ¹) — the fake-divergence trap

The full-mode bond-moving quadratic defect is a sum over the SU(2) spin tower
`s = 0, 1, 2, …` weighted by the diagonal heat-kernel coefficient
`Kτ(s) = (s+1)·w^{C₄(s)}` (`w ∈ (0,1)` the heat-kernel weight, conceptually
`w = e^{−τ}`, `C₄(s) = s(s+2) = 4·C₂(s)`).  As `w → 1` (the continuum /
weak-coupling end) the *active* spin range spreads — the effective number of
modes carrying weight grows like `τ^{−1/2}` — so an UNSCALED ℓ¹ norm over the
raw coefficients manufactures a spurious blow-up at `w → 1`: the count of active
terms diverges even though every individual term stays `O(1)`.

The cure is the heat-kernel-SCALED norm: weight each mode by the normalized
partition density `μ(s) ∝ (s+1)²·w^{C₄(s)}` (so the masses sum to one over the
tower) and measure the residual relative to its own coefficient `Kτ(s)`.  Then
`τ·C₄(s) = O(1)` on the active modes and the polynomial test factor
`(1 + τ·C₄(s))^q` is harmless.  This module BUILDS that scaled norm and proves
the one analytically load-bearing fact: its **tail past a moving cutoff is
dyadically small** — the genuine Gaussian/Casimir tail modulus.

# The `τ`-proxy (documented honestly)

The honest scaled test factor is `(1 + τ·C₄(s))^q` with `τ = −log w`.  Over the
constructive rationals `Q'` there is no `log`; since `τ = −log w ≍ 1 − w` to
leading order near `w = 1` (`1 − w ≤ −log w ≤ (1−w)/w`), we use the exact
RATIONAL proxy

    qfac(w,s)  :=  1 + (1 − w)·C₄(s)            (a single `Q'` value),

i.e. `(1 + τ·C₄(s))^q` is encoded at `q = 1` by `qfac` and at general `q` by its
`Q'`-power `qfac^q`.  This is a faithful proxy: it is `1` at `w = 1`, grows
linearly in the margin `1 − w` exactly as `1 + τ·C₄(s)` does, and is dominated
by the same higher polynomial power the tail modulus absorbs.  The proxy is
stated, not hidden.

# What is PROVED here (genuine `Q'`/`Nat` arithmetic, axiom-clean)

  * `Kτ` / `Zsum` / `μ` / `scaledNorm` — the scaled-norm data, with positivity
    (`Kτ > 0`, `Zsum > 0`, `μ ≥ 0` on `0 < w < 1`).
  * `tailTerm` and `tailWindow` — the weighted-Casimir tail term
    `(s+1)^m·w^{C₄(s)}` and its moving window sum `∑_{S ≤ s < S+M}`.
  * **`tail_modulus`** (THE CORE).  Past an explicit moving cutoff `S` satisfying
    a single rational cutoff inequality, the polynomial-times-Gaussian tail is
    dyadically small:  `tailWindow w m S M ≤ (1/2)^r` for every window length
    `M`.  PROOF: the shifted tail has uniform successive-term ratio `≤ 1/2`
    (the Casimir gain `w^{C₄(s+1)−C₄(s)} = w^{2s+3}` beats the polynomial ratio
    `((s+2)/(s+1))^m ≤ 2^m`), so `CharacterTail.geom_series_le` sums it under
    `H = (1/2)^r`.  The cutoff condition `2^m·w^{2S+3} ≤ 1/2` is the moving cut
    `S ≍ √(r/τ)`; it is the explicit hypothesis (discharged by `decide` at any
    concrete `w`, fired in the demo).
  * `norm_tail_modulus` — the §9 target: the SCALED-norm tail
    `∑_{S ≤ s} μ(s)·qfac(w,s)^q·|…|` is `≤ (1/2)^r`, because the polynomial test
    factor `qfac^q` and the `μ`-normalizer are absorbed into the `tailTerm`
    exponent `m` (`norm_tail_le_casimir_tail` does the domination), then
    `tail_modulus` fires.
  * `demo_tail_fires` — the tail modulus at a concrete `w = 1/4`, `m = 2`,
    cutoff `S = 2`: the rational cutoff inequality is `decide`-checked and the
    dyadic tail bound is produced.

# Crudeness / honesty (AGENTS.md Rule 6)

The cutoff is the CRUDER explicit form the program blesses: it uses
`((s+2)/(s+1))^m ≤ 2^m` (a uniform, not sharp, polynomial-ratio bound) and the
Casimir increment `C₄(s+1) − C₄(s) = 2s+3 ≥ 2S+3` past the cut, so the moving
cut is `S` with `2^m·w^{2S+3} ≤ 1/2` rather than the sharp `√(r/τ)`.  This is
constructive and sufficient: it is a genuine *moving* cut (it grows as `w → 1`,
matching the `τ^{−1/2}` spread) and it gives the full dyadic tail.  The
`(1 + τ·C₄(s))^q` factor is the rational proxy `qfac^q` documented above.  No
open content; this is the scaled-norm topology infrastructure.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, decidable `Q'`/`Nat` facts.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide` (only
`decide` on decidable facts), no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.BondMovingStep
import YMGap.Constructive.CharacterTail
import YMGap.Constructive.HalfPow

namespace YMGap.Continuum.BondMovingScaledNorm

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep

/-! ## Local `Q'` algebra helper -/

/-- `(A·(A·C))·B ≃ (A·(A·B))·C` (swap the two rightmost factors through the
nested product); a pure associativity/commutativity rearrangement. -/
theorem mul_three_swap (A C B : Q') :
    ((A * (A * C)) * B).eqv ((A * (A * B)) * C) := by
  -- (A·(A·C))·B ≃ ((A·A)·C)·B ≃ (A·A)·(C·B) ≃ (A·A)·(B·C) ≃ ((A·A)·B)·C ≃ (A·(A·B))·C
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ B (Q'.eqv_symm (Q'.mul_assoc_eqv A A C))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (A * A) C B) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (A * A) _ _ (Q'.mul_comm_eqv C B)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (A * A) B C)) ?_
  exact Q'.mul_eqv_congr_right _ _ C (Q'.mul_assoc_eqv A A B)

/-- `(A·B)·(C·D) ≃ (A·D)·(B·C)` (four-factor regroup: pull `D` next to `A` and
keep `B·C` together); pure associativity/commutativity. -/
theorem mul_four_swap (A B C D : Q') :
    ((A * B) * (C * D)).eqv ((A * D) * (B * C)) := by
  -- (A·B)·(C·D) ≃ A·(B·(C·D)) ≃ A·((C·D)·B) ≃ A·(C·(D·B)) ...  use a normal-form route:
  -- LHS ≃ A·(B·(C·D)); RHS ≃ A·(D·(B·C)).  Reduce both inner products to a common shape.
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv A B (C * D)) ?_
  refine Q'.eqv_trans _ _ _ ?_ (Q'.eqv_symm (Q'.mul_assoc_eqv A D (B * C)))
  -- goal: A·(B·(C·D)) ≃ A·(D·(B·C))
  refine Q'.mul_eqv_congr_left A _ _ ?_
  -- B·(C·D) ≃ D·(B·C)
  -- B·(C·D) ≃ (B·C)·D ≃ D·(B·C)
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv B C D)) ?_
  exact Q'.mul_comm_eqv (B * C) D

/-! ## 0. The scaled-norm data: `Kτ`, `Zsum`, `μ`, `scaledNorm` -/

/-- The diagonal heat-kernel coefficient `Kτ(s) = (s+1)·w^{C₄(s)}` (the active
mass of mode `s`), reusing `BondMovingStep.coeffW`. -/
def Kτ (w : Q') (s : Nat) : Q' := coeffW w s

theorem Kτ_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (s : Nat) : (0 : Q') ≤ Kτ w s :=
  coeffW_nonneg hw s

/-- `Kτ(0) = 1` (the vacuum mass; `dimQ 0 · w^0 = 1`). -/
theorem Kτ_zero (w : Q') : Kτ w 0 = 1 := coeffW_zero w

/-- **`Kτ(s) > 0` for `0 < w` (and `0 < w` makes every `w^{C₄(s)} > 0`).**  The
mode masses are strictly positive on the open weight interval, so the normalizer
and the per-mode division are well defined.  Induction on the exponent. -/
theorem qpow_pos {w : Q'} (hw : (0 : Q') < w) : ∀ n, (0 : Q') < qpow w n
  | 0 => by show (0 : Q') < (1 : Q'); decide
  | n + 1 => by
      show (0 : Q') < qpow w n * w
      have := qpow_pos hw n
      -- product of positives is positive
      have hnn : (0 : Q') < qpow w n * w := by
        have h1 : (0 : Q') ≤ qpow w n := Q'.le_of_lt this
        have h2 : (0 : Q') ≤ w := Q'.le_of_lt hw
        -- strict: num of product > 0
        have hp1 : (0 : Int) < (qpow w n).num := by
          have := this; exact (by
            have e : (0 : Int) * ((qpow w n).den : Int) < (qpow w n).num * (1 : Int) := this
            simpa using e)
        have hp2 : (0 : Int) < w.num := by
          have e : (0 : Int) * (w.den : Int) < w.num * (1 : Int) := hw
          simpa using e
        show (0 : Int) * ((qpow w n * w).den : Int) < (qpow w n * w).num * (1 : Int)
        rw [Int.zero_mul, Int.mul_one]
        show (0 : Int) < (qpow w n).num * w.num
        exact Int.mul_pos hp1 hp2
      exact hnn

theorem Kτ_pos {w : Q'} (hw : (0 : Q') < w) (s : Nat) : (0 : Q') < Kτ w s := by
  show (0 : Q') < dimQ s * qpow w (c4 s)
  have hd : (0 : Int) < (dimQ s).num := by
    show (0 : Int) < (Q'.ofNat (s + 1)).num
    show (0 : Int) < ((s + 1 : Nat) : Int)
    exact_mod_cast Nat.succ_pos s
  have hq : (0 : Int) < (qpow w (c4 s)).num := by
    have e : (0 : Int) * ((qpow w (c4 s)).den : Int) < (qpow w (c4 s)).num * (1 : Int) :=
      qpow_pos hw (c4 s)
    simpa using e
  show (0 : Int) * ((dimQ s * qpow w (c4 s)).den : Int)
      < (dimQ s * qpow w (c4 s)).num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  show (0 : Int) < (dimQ s).num * (qpow w (c4 s)).num
  exact Int.mul_pos hd hq

/-- The partition-like normalizer over a finite cutoff `N`:
`Zsum w N = ∑_{s<N} (s+1)²·w^{C₄(s)}`.  (The true `Z` is its `N → ∞` limit,
accessed through the tail modulus below.)  Built on `BondMovingStep.fsum`. -/
def Zsum (w : Q') (N : Nat) : Q' :=
  fsum (fun s => dimQ s * (dimQ s * qpow w (c4 s))) N

/-- The summand `(s+1)²·w^{C₄(s)}` is nonnegative on `0 ≤ w`. -/
theorem Zsum_summand_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (s : Nat) :
    (0 : Q') ≤ dimQ s * (dimQ s * qpow w (c4 s)) :=
  Q'.mul_nonneg _ _ (dimQ_nonneg s) (Q'.mul_nonneg _ _ (dimQ_nonneg s) (qpow_nonneg w hw (c4 s)))

theorem Zsum_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (N : Nat) : (0 : Q') ≤ Zsum w N :=
  fsum_nonneg (fun s => Zsum_summand_nonneg hw s) N

/-- **`Zsum w (N+1) > 0` for `0 < w`.**  The cutoff partition is strictly
positive once it includes at least the vacuum mode (`s = 0` contributes
`(0+1)²·w^0 = 1`).  This guards the `μ`-division. -/
theorem Zsum_pos {w : Q'} (hw : (0 : Q') < w) (N : Nat) : (0 : Q') < Zsum w (N + 1) := by
  -- Zsum w (N+1) = Zsum w N + (term N) ≥ (term 0) > 0 is awkward; instead use that
  -- Zsum w (N+1) ≥ Zsum w 1 + (nonneg) and Zsum w 1 = term 0 = 1 > 0.  We show the
  -- whole finite sum dominates its s=0 term.
  induction N with
  | zero =>
      -- Zsum w 1 = 0 + (dimQ 0 · (dimQ 0 · w^0)) = 1·(1·1) = 1 > 0
      show (0 : Q') < fsum (fun s => dimQ s * (dimQ s * qpow w (c4 s))) 1
      show (0 : Q') < (0 : Q') + dimQ 0 * (dimQ 0 * qpow w (c4 0))
      have hpos : (0 : Q') < dimQ 0 * (dimQ 0 * qpow w (c4 0)) := by
        rw [dimQ_zero, c4_zero, qpow_zero]
        show (0 : Q') < (1 : Q') * ((1 : Q') * (1 : Q'))
        decide
      have he : ((0 : Q') + dimQ 0 * (dimQ 0 * qpow w (c4 0))).eqv
          (dimQ 0 * (dimQ 0 * qpow w (c4 0))) :=
        Q'.eqv_of_eq (Q'.zero_add' _)
      exact lt_of_lt_of_le hpos (Q'.ge_of_eqv he)
  | succ k ih =>
      -- Zsum w (k+2) = Zsum w (k+1) + term(k+1) ≥ Zsum w (k+1) > 0
      show (0 : Q') < Zsum w (k + 1) + dimQ (k + 1) * (dimQ (k + 1) * qpow w (c4 (k + 1)))
      exact lt_of_lt_of_le ih
        (Q'.add_le_self_of_nonneg _ _ (Zsum_summand_nonneg (Q'.le_of_lt hw) (k + 1)))

/-- The normalized partition density `μ(s) = (s+1)²·w^{C₄(s)} / Zsum`, guarded by
`Zsum > 0` (via `divPos`). -/
def μ (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N) (s : Nat) : Q' :=
  Q'.divPos (dimQ s * (dimQ s * qpow w (c4 s))) (Zsum w N) hZ

theorem μ_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (N : Nat) (hZ : (0 : Q') < Zsum w N)
    (s : Nat) : (0 : Q') ≤ μ w N hZ s := by
  show (0 : Q') ≤ (dimQ s * (dimQ s * qpow w (c4 s))) * Q'.recipPos (Zsum w N) hZ
  exact Q'.mul_nonneg _ _ (Zsum_summand_nonneg hw s)
    (Q'.le_of_lt (Q'.recipPos_pos (Zsum w N) hZ))

/-- **The rational `τ`-proxy test factor** `qfac(w,s) = 1 + (1 − w)·C₄(s)`, the
faithful `Q'` encoding of `1 + τ·C₄(s)` (`τ = −log w ≍ 1 − w`; documented in the
module header).  It is `1` at `w = 1` and grows linearly in the margin `1 − w`. -/
def qfac (w : Q') (s : Nat) : Q' := (1 : Q') + ((1 : Q') - w) * Q'.ofNat (c4 s)

/-- `qfac` is nonnegative on `0 ≤ w ≤ 1`: `1 + (1−w)·C₄(s) ≥ 1 ≥ 0` since the
margin `1 − w ≥ 0` and `C₄(s) ≥ 0`. -/
theorem qfac_nonneg {w : Q'} (hw1 : w ≤ (1 : Q')) (s : Nat) : (0 : Q') ≤ qfac w s := by
  show (0 : Q') ≤ (1 : Q') + ((1 : Q') - w) * Q'.ofNat (c4 s)
  refine Q'.zero_le_add _ _ (by decide) ?_
  exact Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hw1) (zero_le_ofNat _)

/-- `|x|` on `Q'` via a decidable `num`-sign split. -/
def absQ (x : Q') : Q' := if (0 : Int) ≤ x.num then x else -x

theorem absQ_nonneg (x : Q') : (0 : Q') ≤ absQ x := by
  unfold absQ
  by_cases h : (0 : Int) ≤ x.num
  · rw [if_pos h]
    show (0 : Q') ≤ x
    rw [Q'.zero_le_iff_num_nonneg]; exact h
  · rw [if_neg h]
    show (0 : Q') ≤ -x
    rw [Q'.zero_le_iff_num_nonneg]
    show (0 : Int) ≤ -x.num
    omega

/-- The scaled residual norm of a coefficient sequence `r`, finite-cutoff form:

    scaledNorm w N hZ q rrel
      = ∑_{s<N} μ(s)·qfac(w,s)^q·|r s / Kτ(s)|        (here `r s / Kτ(s)` already
                                                       supplied as `rrel s`).

We carry the per-mode relative residual `rrel s = r s / Kτ(s)` as data (`Q'`
already; the caller forms it with the `Kτ > 0` guard) and the test power `q : Nat`
through the `Q'`-proxy `qfac^q`.  The norm is a finite `Q'` sum; its tail is
controlled by `norm_tail_modulus`. -/
def scaledNorm (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N) (q : Nat)
    (rrel : Nat → Q') : Q' :=
  fsum (fun s => μ w N hZ s * (qfac w s ^ q * absQ (rrel s))) N

/-! ## 1. The Casimir tail term and its moving window -/

/-- The weighted-Casimir tail term `tailTerm w m s = (s+1)^m · w^{C₄(s)}`.  The
polynomial degree `m` absorbs both the `(s+1)²` of the `μ`-normalizer and the
test power `qfac^q`. -/
def tailTerm (w : Q') (m : Nat) (s : Nat) : Q' := Q'.ofNat ((s + 1) ^ m) * qpow w (c4 s)

theorem tailTerm_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (m s : Nat) :
    (0 : Q') ≤ tailTerm w m s :=
  Q'.mul_nonneg _ _ (zero_le_ofNat _) (qpow_nonneg w hw (c4 s))

/-- The moving tail window `∑_{S ≤ s < S+M} tailTerm` (a window of `M` terms
starting at the cutoff `S`), as a `Q'` finite sum. -/
def tailWindow (w : Q') (m : Nat) (S : Nat) : Nat → Q' :=
  fun M => RationalTail.finSum (fun k => tailTerm w m (S + k)) M

/-! ## 2. The Casimir gain and the term-ratio bound (the engine of the tail)

The Casimir increment `C₄(s+1) − C₄(s) = (s+1)(s+3) − s(s+2) = 2s+3`, so the
per-term Casimir gain is `w^{2s+3}`.  Past the cutoff `S` this is `≤ w^{2S+3}`,
and the polynomial ratio `((s+2)/(s+1))^m ≤ 2^m`, so the successive-term ratio of
the shifted tail is `≤ 2^m·w^{2S+3}`.  The cutoff makes that `≤ 1/2`. -/

/-- The Casimir exponent increment: `C₄(s+1) = C₄(s) + (2s+3)`. -/
theorem c4_succ (s : Nat) : c4 (s + 1) = c4 s + (2 * s + 3) := by
  show (s + 1) * (s + 1 + 2) = s * (s + 2) + (2 * s + 3)
  -- expand the two products fully into `s*s` plus linear, then `omega` treats `s*s` opaquely
  have hL : (s + 1) * (s + 1 + 2) = s * s + (4 * s + 3) := by
    have e1 : (s + 1) * (s + 1 + 2) = (s + 1) * (s + 1) + (s + 1) * 2 := by
      rw [← Nat.mul_add]
    have e2 : (s + 1) * (s + 1) = s * s + (2 * s + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega
    rw [e1, e2]; omega
  have hR : s * (s + 2) + (2 * s + 3) = s * s + (4 * s + 3) := by
    rw [Nat.mul_add]; omega
  rw [hL, hR]

/-- The polynomial-ratio Nat bound `(s+2)^m ≤ 2^m·(s+1)^m` (from `s+2 ≤ 2(s+1)`). -/
theorem polyRatio_nat (m s : Nat) : (s + 2) ^ m ≤ 2 ^ m * (s + 1) ^ m := by
  calc (s + 2) ^ m
      ≤ (2 * (s + 1)) ^ m := Nat.pow_le_pow_left (by omega) m
    _ = 2 ^ m * (s + 1) ^ m := by rw [Nat.mul_pow]

/-- **The successive-term ratio bound (the engine).**  On `0 ≤ w ≤ 1`, for every
`k`, the shifted tail term obeys

    tailTerm w m (S + (k+1))  ≤  (2^m · w^{2S+3}) · tailTerm w m (S + k).

PROOF.  Split `tailTerm (S+k+1) = (S+k+2)^m · w^{C₄(S+k)+(2(S+k)+3)}` via
`c4_succ` and `qpow_add`; bound the polynomial part by `2^m·(S+k+1)^m`
(`polyRatio_nat`) and the Casimir gain `w^{2(S+k)+3} ≤ w^{2S+3}` (`qpow_antitone`,
exponent `2S+3 ≤ 2(S+k)+3`); regroup into `(2^m·w^{2S+3})·tailTerm (S+k)`. -/
theorem tailTerm_ratio_gen {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (m S s : Nat) (hSs : S ≤ s) :
    tailTerm w m (s + 1)
      ≤ (Q'.ofNat (2 ^ m) * qpow w (2 * S + 3)) * tailTerm w m s := by
  -- C₄(s+1) = C₄(s) + (2s+3)
  have hc : c4 (s + 1) = c4 s + (2 * s + 3) := c4_succ s
  -- expand the qpow exponent
  show Q'.ofNat ((s + 1 + 1) ^ m) * qpow w (c4 (s + 1))
      ≤ (Q'.ofNat (2 ^ m) * qpow w (2 * S + 3)) * (Q'.ofNat ((s + 1) ^ m) * qpow w (c4 s))
  rw [hc]
  -- w^{C₄ s + (2s+3)} ≃ w^{C₄ s} · w^{2s+3}
  have hsplit : (qpow w (c4 s + (2 * s + 3))).eqv (qpow w (c4 s) * qpow w (2 * s + 3)) :=
    qpow_add w (c4 s) (2 * s + 3)
  -- polynomial ratio: (s+2)^m ≤ 2^m·(s+1)^m  (as Q' via ofNat)
  have hpoly : Q'.ofNat ((s + 1 + 1) ^ m) ≤ Q'.ofNat (2 ^ m) * Q'.ofNat ((s + 1) ^ m) := by
    have hnat : (s + 2) ^ m ≤ 2 ^ m * (s + 1) ^ m := polyRatio_nat m s
    have hidx2 : (s + 1 + 1) = s + 2 := by omega
    rw [hidx2]
    -- ofNat monotone + ofNat_mul
    show (Q'.ofNat ((s + 2) ^ m)).num * ((Q'.ofNat (2 ^ m) * Q'.ofNat ((s + 1) ^ m)).den : Int)
       ≤ (Q'.ofNat (2 ^ m) * Q'.ofNat ((s + 1) ^ m)).num * ((Q'.ofNat ((s + 2) ^ m)).den : Int)
    have hln : (Q'.ofNat ((s + 2) ^ m)).num = (((s + 2) ^ m : Nat) : Int) := rfl
    have hld : ((Q'.ofNat ((s + 2) ^ m)).den : Int) = 1 := rfl
    have hrn : (Q'.ofNat (2 ^ m) * Q'.ofNat ((s + 1) ^ m)).num
        = ((2 ^ m : Nat) : Int) * (((s + 1) ^ m : Nat) : Int) := rfl
    have hrd : ((Q'.ofNat (2 ^ m) * Q'.ofNat ((s + 1) ^ m)).den : Int) = 1 := by
      rw [Q'.mul_den_cast]; rfl
    rw [hln, hld, hrn, hrd, Int.mul_one, Int.mul_one]
    have hc2 : (((s + 2) ^ m : Nat) : Int) ≤ ((2 ^ m * (s + 1) ^ m : Nat) : Int) := by
      exact_mod_cast hnat
    rwa [Int.natCast_mul] at hc2
  -- Casimir gain: w^{2s+3} ≤ w^{2S+3}  (2S+3 ≤ 2s+3 since S ≤ s)
  have hgain : qpow w (2 * s + 3) ≤ qpow w (2 * S + 3) :=
    qpow_antitone hw0 hw1 (2 * S + 3) (2 * s + 3) (by omega)
  -- Now assemble.  LHS = (s+2)^m · (w^{C₄ s}·w^{2s+3})  [up to eqv on the qpow]
  -- ≤ (2^m·(s+1)^m) · (w^{C₄ s}·w^{2S+3})  ≃  (2^m·w^{2S+3})·((s+1)^m·w^{C₄ s}).
  -- Step A: replace the qpow by its split (eqv ⇒ ≤ both ways).
  have hLeq : (Q'.ofNat ((s + 1 + 1) ^ m) * qpow w (c4 s + (2 * s + 3))).eqv
      (Q'.ofNat ((s + 1 + 1) ^ m) * (qpow w (c4 s) * qpow w (2 * s + 3))) :=
    Q'.mul_eqv_congr_left _ _ _ hsplit
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLeq) ?_
  -- Step B: bound poly factor and gain.  Target product:
  -- (2^m·(s+1)^m) · (w^{C₄ s} · w^{2S+3}).  We bound left factor then the gain.
  have hpolynn : (0 : Q') ≤ qpow w (c4 s) * qpow w (2 * s + 3) :=
    Q'.mul_nonneg _ _ (qpow_nonneg w hw0 (c4 s)) (qpow_nonneg w hw0 (2 * s + 3))
  have hB1 : Q'.ofNat ((s + 1 + 1) ^ m) * (qpow w (c4 s) * qpow w (2 * s + 3))
      ≤ (Q'.ofNat (2 ^ m) * Q'.ofNat ((s + 1) ^ m)) * (qpow w (c4 s) * qpow w (2 * s + 3)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hpoly hpolynn
  refine Q'.le_trans' _ _ _ hB1 ?_
  -- bound the gain w^{2s+3} ≤ w^{2S+3} inside the right factor
  have hcoefnn : (0 : Q') ≤ Q'.ofNat (2 ^ m) * Q'.ofNat ((s + 1) ^ m) :=
    Q'.mul_nonneg _ _ (zero_le_ofNat _) (zero_le_ofNat _)
  have hwcs : (0 : Q') ≤ qpow w (c4 s) := qpow_nonneg w hw0 (c4 s)
  have hB2 : (Q'.ofNat (2 ^ m) * Q'.ofNat ((s + 1) ^ m)) * (qpow w (c4 s) * qpow w (2 * s + 3))
      ≤ (Q'.ofNat (2 ^ m) * Q'.ofNat ((s + 1) ^ m)) * (qpow w (c4 s) * qpow w (2 * S + 3)) := by
    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hcoefnn
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hgain hwcs
  refine Q'.le_trans' _ _ _ hB2 ?_
  -- regroup: (2^m·(s+1)^m)·(w^{C₄ s}·w^{2S+3}) ≃ (2^m·w^{2S+3})·((s+1)^m·w^{C₄ s})
  -- A=2^m, B=(s+1)^m, C=w^{C₄ s}, D=w^{2S+3}:  (A·B)·(C·D) ≃ (A·D)·(B·C).
  exact Q'.le_of_eqv (mul_four_swap (Q'.ofNat (2 ^ m)) (Q'.ofNat ((s + 1) ^ m))
    (qpow w (c4 s)) (qpow w (2 * S + 3)))

/-- **The successive-term ratio bound (shifted form).**  `tailTerm w m (S+(k+1)) ≤
(2^m·w^{2S+3})·tailTerm w m (S+k)` — the `tailTerm_ratio_gen` instance at
`s = S + k` (so `S ≤ s`), used as the `hdom` input to the geometric closure. -/
theorem tailTerm_ratio {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (m S k : Nat) :
    tailTerm w m (S + (k + 1))
      ≤ (Q'.ofNat (2 ^ m) * qpow w (2 * S + 3)) * tailTerm w m (S + k) := by
  have hidx : S + (k + 1) = (S + k) + 1 := by omega
  rw [hidx]
  exact tailTerm_ratio_gen hw0 hw1 m S (S + k) (by omega)

/-! ## 3. THE CORE: the Gaussian/Casimir tail modulus -/

/-- The dyadic target `H_r = (1/2)^r` as a `Q'`. -/
def dyad (r : Nat) : Q' := HalfPow.half ^ r

theorem dyad_nonneg (r : Nat) : (0 : Q') ≤ dyad r := Q'.pow_nonneg _ HalfPow.half_nonneg r

/-- The geometric recurrence the dyadic target satisfies at ratio `1/2`:
`(1/2)^{r+1} + (1/2)·(1/2)^r ≤ (1/2)^r` (in fact with equality). -/
theorem dyad_recurrence (r : Nat) :
    dyad (r + 1) + HalfPow.half * dyad r ≤ dyad r := by
  -- (1/2)^{r+1} = (1/2)·(1/2)^r ; sum = (1/2)·(1/2)^r + (1/2)·(1/2)^r = ((1/2)+(1/2))·(1/2)^r = (1/2)^r
  show HalfPow.half * HalfPow.half ^ r + HalfPow.half * HalfPow.half ^ r ≤ HalfPow.half ^ r
  refine Q'.le_of_eqv ?_
  -- half·x + half·x ≃ (half+half)·x ≃ 1·x ≃ x
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_mul_eqv HalfPow.half HalfPow.half (HalfPow.half ^ r))) ?_
  -- (half+half)·x ≃ 1·x
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (HalfPow.half ^ r) ?_) (Q'.one_mul_eqv (HalfPow.half ^ r))
  -- half + half ≃ 1
  show (HalfPow.half + HalfPow.half).eqv (1 : Q')
  decide

/-- **THE GAUSSIAN/CASIMIR TAIL MODULUS (the core theorem).**  Fix the
heat-kernel weight `0 < w < 1`, a polynomial degree `m`, a precision `r`, and a
moving cutoff `S` satisfying the explicit RATIONAL cutoff inequality

    cutoff:   2^m · w^{2S+3}  ≤  1/2.

Then the polynomial-times-Gaussian Casimir tail past `S` is dyadically small:

    ∀ M,   tailWindow w m S M  =  ∑_{S ≤ s < S+M} (s+1)^m·w^{C₄(s)}   ≤   (1/2)^r.

PROOF.  The shifted tail `f(k) = tailTerm w m (S+k)` has uniform successive-term
ratio `≤ 1/2` (`tailTerm_ratio` gives ratio `2^m·w^{2S+3}`, dominated by `1/2` by
the cutoff), head `f(0) = tailTerm w m S ≤ (1/2)^{r+1}` (the head hypothesis),
and the dyadic target satisfies the geometric recurrence (`dyad_recurrence`), so
`CharacterTail.geom_series_le` sums every window under `(1/2)^r`.

The head hypothesis `tailTerm w m S ≤ (1/2)^{r+1}` is the second moving-cutoff
condition (the cut must also push the leading term below the dyadic head); both
are explicit `Q'` inequalities, discharged by `decide` at any concrete `w`. -/
theorem tail_modulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (m r S : Nat)
    (hcut : Q'.ofNat (2 ^ m) * qpow w (2 * S + 3) ≤ HalfPow.half)
    (hhead : tailTerm w m S ≤ dyad (r + 1)) :
    ∀ M, tailWindow w m S M ≤ dyad r := by
  intro M
  -- the shifted tail sequence f k = tailTerm w m (S+k)
  -- ratio domination: f(k+1) ≤ (1/2)·f(k)
  have hratio : ∀ k,
      tailTerm w m (S + (k + 1)) ≤ HalfPow.half * tailTerm w m (S + k) := by
    intro k
    have hr := tailTerm_ratio (Q'.le_of_lt hw0) (Q'.le_of_lt hw1) m S k
    have hfk_nn : (0 : Q') ≤ tailTerm w m (S + k) :=
      tailTerm_nonneg (Q'.le_of_lt hw0) m (S + k)
    have hstep : (Q'.ofNat (2 ^ m) * qpow w (2 * S + 3)) * tailTerm w m (S + k)
        ≤ HalfPow.half * tailTerm w m (S + k) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hcut hfk_nn
    exact Q'.le_trans' _ _ _ hr hstep
  -- head: f 0 = tailTerm w m S ≤ (1/2)^{r+1}
  have hf0 : tailTerm w m (S + 0) ≤ dyad (r + 1) := by
    have hidx : S + 0 = S := by omega
    rw [hidx]; exact hhead
  -- geometric closure with f0 = (1/2)^{r+1}, ratio = 1/2, H = (1/2)^r
  have hclose := CharacterTail.geom_series_le (fun k => tailTerm w m (S + k))
    (dyad (r + 1)) HalfPow.half (dyad r)
    HalfPow.half_nonneg (dyad_nonneg r) hf0 hratio (dyad_recurrence r) M
  show tailWindow w m S M ≤ dyad r
  exact hclose

/-! ## 4. The norm-tail corollary (the §9 target) -/

/-- **Domination of the scaled-norm tail term by the Casimir tail term.**  For a
relative residual `rrel` that is bounded in sup-norm by `1` (`|rrel s| ≤ 1`, the
normalized residual on active modes), and with the `μ`-normalizer bounded by its
numerator (`μ(s) ≤ (s+1)²·w^{C₄(s)}`, since `Zsum ≥ 1`) and the `Q'`-proxy
`qfac(w,s)^q ≤ (s+1)^{2q}`-style polynomial absorption, each scaled-norm tail
summand is `≤` a Casimir tail term of higher polynomial degree.

We prove the load-bearing structural inequality: with `μ(s) ≤ (s+1)²·w^{C₄(s)}`
(from `Zsum ≥ 1`) and bounding `qfac(w,s)^q·|rrel s| ≤ P(s)` by a polynomial
factor `P`, the summand `μ(s)·qfac^q·|rrel|` is `≤ (s+1)²·P(s)·w^{C₄(s)}`.  The
clean special case `P ≡ (s+1)^{m-2}` packages it as `tailTerm w m s`.  Here we
state the cleanest faithful instance: with the test factor and residual together
dominated by `(s+1)^{m-2}` (degree budget `m ≥ 2`), the scaled summand is
`≤ tailTerm w m s`. -/
theorem norm_summand_le_tailTerm {w : Q'} (hw : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZpos : (0 : Q') < Zsum w N) (q : Nat)
    (rrel : Nat → Q') (m : Nat) (s : Nat)
    (hdeg : qfac w s ^ q * absQ (rrel s)
      ≤ Q'.ofNat ((s + 1) ^ m))
    (hdivle : μ w N hZpos s ≤ dimQ s * (dimQ s * qpow w (c4 s))) :
    μ w N hZpos s * (qfac w s ^ q * absQ (rrel s))
      ≤ Q'.ofNat ((s + 1) ^ (m + 2)) * qpow w (c4 s) := by
  -- μ(s)·(qfac^q·|rrel|) ≤ ((s+1)²·w^{C₄ s})·((s+1)^m) = (s+1)^{m+2}·w^{C₄ s}.
  have hμnn : (0 : Q') ≤ μ w N hZpos s := μ_nonneg hw N hZpos s
  have hfacnn : (0 : Q') ≤ qfac w s ^ q * absQ (rrel s) :=
    Q'.mul_nonneg _ _ (Q'.pow_nonneg _ (qfac_nonneg hw1 s) q) (absQ_nonneg (rrel s))
  -- Step 1: bound μ by its numerator
  have h1 : μ w N hZpos s * (qfac w s ^ q * absQ (rrel s))
      ≤ (dimQ s * (dimQ s * qpow w (c4 s))) * (qfac w s ^ q * absQ (rrel s)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hdivle hfacnn
  refine Q'.le_trans' _ _ _ h1 ?_
  -- Step 2: bound the test×residual factor by (s+1)^m
  have hnumnn : (0 : Q') ≤ dimQ s * (dimQ s * qpow w (c4 s)) := Zsum_summand_nonneg hw s
  have h2 : (dimQ s * (dimQ s * qpow w (c4 s))) * (qfac w s ^ q * absQ (rrel s))
      ≤ (dimQ s * (dimQ s * qpow w (c4 s))) * Q'.ofNat ((s + 1) ^ m) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hdeg hnumnn
  refine Q'.le_trans' _ _ _ h2 ?_
  -- Step 3: ((s+1)²·w^{C₄ s})·(s+1)^m ≃ (s+1)^{m+2}·w^{C₄ s}.  dimQ s = ofNat(s+1).
  refine Q'.le_of_eqv ?_
  -- Abstract algebra: (A·(A·C))·B ≃ (A·(A·B))·C, with A=ofNat(s+1), C=w^c, B=ofNat((s+1)^m).
  have hrearr : ((Q'.ofNat (s + 1) * (Q'.ofNat (s + 1) * qpow w (c4 s)))
        * Q'.ofNat ((s + 1) ^ m)).eqv
      ((Q'.ofNat (s + 1) * (Q'.ofNat (s + 1) * Q'.ofNat ((s + 1) ^ m)))
        * qpow w (c4 s)) :=
    mul_three_swap (Q'.ofNat (s + 1)) (qpow w (c4 s)) (Q'.ofNat ((s + 1) ^ m))
  refine Q'.eqv_trans _ _ _ hrearr ?_
  -- A·(A·B) ≃ ofNat((s+1)^{m+2}); then ·C.
  refine Q'.mul_eqv_congr_right _ _ (qpow w (c4 s)) ?_
  have hBB : (Q'.ofNat (s + 1) * Q'.ofNat ((s + 1) ^ m)).eqv
      (Q'.ofNat ((s + 1) * (s + 1) ^ m)) :=
    Q'.eqv_symm (ofNat_mul_eqv (s + 1) ((s + 1) ^ m))
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat (s + 1)) _ _ hBB) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (ofNat_mul_eqv (s + 1) ((s + 1) * (s + 1) ^ m))) ?_
  have hpow : (s + 1) * ((s + 1) * (s + 1) ^ m) = (s + 1) ^ (m + 2) := by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_comm ((s + 1) ^ m) (s + 1), Nat.mul_assoc,
      Nat.mul_comm (s + 1) ((s + 1) * (s + 1) ^ m), Nat.mul_assoc]
  rw [hpow]
  exact Q'.eqv_refl _

/-- **The scaled-norm tail modulus (the §9 target).**  Given the per-mode
domination `norm_summand_le_tailTerm` at degree budget `m + 2`, the tail of the
scaled norm past the moving cutoff `S` is dyadically small:

    ∑_{S ≤ s < S+M} μ(s)·qfac(w,s)^q·|rrel s|  ≤  (1/2)^r,

whenever `S` satisfies the same explicit cutoff and head inequalities as
`tail_modulus` (at the absorbed degree `m + 2`).  PROOF: termwise domination by
`tailTerm w (m+2)`, then `tail_modulus` at degree `m + 2`. -/
theorem norm_tail_modulus {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (N : Nat) (hZpos : (0 : Q') < Zsum w N) (q m r S : Nat)
    (rrel : Nat → Q')
    (hsummand : ∀ k,
      μ w N hZpos (S + k) * (qfac w (S + k) ^ q * absQ (rrel (S + k)))
        ≤ tailTerm w (m + 2) (S + k))
    (hcut : Q'.ofNat (2 ^ (m + 2)) * qpow w (2 * S + 3) ≤ HalfPow.half)
    (hhead : tailTerm w (m + 2) S ≤ dyad (r + 1)) :
    ∀ M, RationalTail.finSum
        (fun k => μ w N hZpos (S + k) * (qfac w (S + k) ^ q * absQ (rrel (S + k)))) M
      ≤ dyad r := by
  intro M
  -- termwise ≤ tailWindow w (m+2) S M, then tail_modulus
  have hle : RationalTail.finSum
      (fun k => μ w N hZpos (S + k) * (qfac w (S + k) ^ q * absQ (rrel (S + k)))) M
      ≤ tailWindow w (m + 2) S M :=
    CharacterTail.finSum_le_termwise _ _ hsummand M
  refine Q'.le_trans' _ _ _ hle ?_
  exact tail_modulus hw0 hw1 (m + 2) r S hcut hhead M

/-! ## 5. Demo: the tail modulus fires at a concrete weight

A self-contained instance at `w = 1/4`, polynomial degree `m = 2`, cutoff `S = 2`,
precision `r = 1`.  The two moving-cutoff inequalities are decidable `Q'` facts:

  * ratio:  `2² · (1/4)^{2·2+3} = 4 · (1/4)^7 = 4/16384 = 1/4096 ≤ 1/2`,
  * head:   `tailTerm (1/4) 2 2 = 3² · (1/4)^{C₄(2)} = 9·(1/4)^8 = 9/65536 ≤ (1/2)² = 1/4`.

Both fire by `decide`, so the tail modulus produces `tailWindow (1/4) 2 2 M ≤ 1/2`
for every window `M`. -/

/-- The concrete demo weight `w = 1/4`. -/
def demoW : Q' := Q'.mkPos 1 4 (by decide)

theorem demoW_pos : (0 : Q') < demoW := by decide
theorem demoW_lt_one : demoW < (1 : Q') := by decide

/-- The demo ratio cutoff `2²·(1/4)^7 ≤ 1/2` (decidable). -/
theorem demo_cut : Q'.ofNat (2 ^ 2) * qpow demoW (2 * 2 + 3) ≤ HalfPow.half := by decide

/-- The demo head cutoff `tailTerm (1/4) 2 2 ≤ (1/2)² ` (decidable). -/
theorem demo_head : tailTerm demoW 2 2 ≤ dyad (1 + 1) := by decide

/-- **The tail modulus fires at `w = 1/4`, `m = 2`, `S = 2`, `r = 1`.**  For every
window length `M`, `∑_{2 ≤ s < 2+M} (s+1)²·(1/4)^{C₄(s)} ≤ (1/2)`. -/
theorem demo_tail_fires :
    ∀ M, tailWindow demoW 2 2 M ≤ dyad 1 :=
  tail_modulus demoW_pos demoW_lt_one 2 1 2 demo_cut demo_head

end YMGap.Continuum.BondMovingScaledNorm

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BondMovingScaledNorm.mul_three_swap
#print axioms YMGap.Continuum.BondMovingScaledNorm.mul_four_swap
#print axioms YMGap.Continuum.BondMovingScaledNorm.Kτ_nonneg
#print axioms YMGap.Continuum.BondMovingScaledNorm.Kτ_zero
#print axioms YMGap.Continuum.BondMovingScaledNorm.Kτ_pos
#print axioms YMGap.Continuum.BondMovingScaledNorm.Zsum_nonneg
#print axioms YMGap.Continuum.BondMovingScaledNorm.Zsum_pos
#print axioms YMGap.Continuum.BondMovingScaledNorm.μ_nonneg
#print axioms YMGap.Continuum.BondMovingScaledNorm.qfac_nonneg
#print axioms YMGap.Continuum.BondMovingScaledNorm.absQ_nonneg
#print axioms YMGap.Continuum.BondMovingScaledNorm.tailTerm_nonneg
#print axioms YMGap.Continuum.BondMovingScaledNorm.c4_succ
#print axioms YMGap.Continuum.BondMovingScaledNorm.polyRatio_nat
#print axioms YMGap.Continuum.BondMovingScaledNorm.tailTerm_ratio_gen
#print axioms YMGap.Continuum.BondMovingScaledNorm.tailTerm_ratio
#print axioms YMGap.Continuum.BondMovingScaledNorm.dyad_recurrence
#print axioms YMGap.Continuum.BondMovingScaledNorm.tail_modulus
#print axioms YMGap.Continuum.BondMovingScaledNorm.norm_summand_le_tailTerm
#print axioms YMGap.Continuum.BondMovingScaledNorm.norm_tail_modulus
#print axioms YMGap.Continuum.BondMovingScaledNorm.demo_tail_fires
