/-
# Closing `DerivStepProp` for all `N` — the differentiated q-Pascal step

`CoeffHalfIdentityClose` builds the formal `z`-derivative of Gauss's q-binomial
identity (`qProdDeriv`, `gaussSumDeriv`) and reduces the full differentiated
identity `qProdDeriv z q N ≈ gaussSumDeriv z q N` — and its `CReal` lift — to a
SINGLE finite named residual per `N`:

    DerivStepProp z q N :
      gaussSumDeriv z q N · (1 + z·q^{2N+1})  +  gaussSum z q N · q^{2N+1}
        ≈  gaussSumDeriv z q (N+1).

That residual was verified genuine only at `N = 0` (`derivStep_zero`).  This
module discharges it for **all** `N` (`derivStep_all`), by a running
differentiated q-Pascal induction that exactly mirrors
`GaussQBinom.gaussSum_run` / `gaussSum_step`, with the product-rule correction
`+ gaussSum · q^{2N+1}` threaded through.  Feeding `derivStep_all` turns the
single-`z` (`Q'`) case of `qProdDeriv_eq_gaussSumDeriv`,
`qProdDeriv_creal_equiv`, and `jacobiDeriv_of_engine` unconditional.

## Method

The `z`-derivative of `gaussSum_step` differentiates the q-Pascal split of each
Gauss term.  The differentiated q-Pascal split is

    dGaussTerm z q (N+1) k
      ≈ dGaussTerm z q N k  +  (k+1)·q^{2N+1}·gaussTerm z q N k       (k ≤ N),

whose exponent bookkeeping `(k+1)² + 2(N−k) = (2N+1) + k²` is the SAME identity
`GaussQBinom.shift_term_eqv` uses.  Running it over `k = 0 … M` (with the
product-rule correction) gives the running identity `dGaussSum_run`; at the full
bound `M = N` the out-of-range top term vanishes (`qbin_out_of_range`) and
`DerivStepProp` closes.

Only the additive-AC reshuffle of a five-term sum, the `z·dGaussTerm` shift, and
the integer-coefficient fold `⟨coefficient⟩ (M+1) + 1 = (M+2)` are new relative
to `GaussQBinom`; each is a small `Q'.eqv` lemma below.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only (`Quot.sound` only via the reused
`Nat`/`Int`/`omega`/`pow` helpers of the `Q'` base layer).  No `Classical.*`, no
`native_decide`, no `sorry`, no custom axiom.
-/

import YMGap.Continuum.GaussQBinom
import YMGap.Continuum.CoeffHalfIdentityClose
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.DerivStepPropClose

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum
open YMGap.Continuum.GaussQBinom
open YMGap.Continuum.CoeffHalfIdentityClose
open YMGap.Continuum.Cheb

local infix:50 " ≈ " => Q'.eqv

instance : Trans (Q'.eqv) (Q'.eqv) (Q'.eqv) where
  trans h1 h2 := eqv_trans _ _ _ h1 h2

/-! ## 0. Power-arithmetic helpers (mirror of `shift_term_eqv`'s internals) -/

/-- `(q·q)^m ≈ q^{2m}` — the base-`q²` power collapses to an even `q`-power. -/
theorem qq_pow (q : Q') (m : Nat) : (q * q) ^ m ≈ q ^ (2 * m) := by
  induction m with
  | zero =>
      calc (q * q) ^ 0 ≈ (1 : Q') := eqv_refl _
        _ ≈ q ^ (2 * 0) := by rw [Nat.mul_zero]; exact eqv_refl _
  | succ m ih =>
      calc (q * q) ^ (m + 1)
          ≈ (q * q) * (q * q) ^ m := by rw [Q'.pow_succ]; exact eqv_refl _
        _ ≈ (q * q) * q ^ (2 * m) := mul_eqv_congr_left _ _ _ ih
        _ ≈ q * (q * q ^ (2 * m)) := mul_assoc_eqv _ _ _
        _ ≈ q * q ^ (2 * m + 1) := by rw [Q'.pow_succ]; exact eqv_refl _
        _ ≈ q ^ (2 * m + 1 + 1) := by rw [Q'.pow_succ]; exact eqv_refl _
        _ ≈ q ^ (2 * (m + 1)) := by
            rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega]; exact eqv_refl _

/-- The q-power shift feeding the differentiated q-Pascal split:
`q^{(k+1)²}·(q·q)^{N−k} ≈ q^{2N+1}·q^{k²}` (for `k ≤ N`).  Exponent identity
`(k+1)² + 2(N−k) = (2N+1) + k²`. -/
theorem qpow_shift (q : Q') (N k : Nat) (hk : k ≤ N) :
    q ^ ((k + 1) * (k + 1)) * (q * q) ^ (N - k)
      ≈ q ^ (2 * N + 1) * q ^ (k * k) := by
  have hexp : (k + 1) * (k + 1) + 2 * (N - k) = (2 * N + 1) + k * k := by
    have hsq : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_one]
      omega
    rw [hsq]; omega
  calc q ^ ((k + 1) * (k + 1)) * (q * q) ^ (N - k)
      ≈ q ^ ((k + 1) * (k + 1)) * q ^ (2 * (N - k)) :=
        mul_eqv_congr_left _ _ _ (qq_pow q (N - k))
    _ ≈ q ^ ((k + 1) * (k + 1) + 2 * (N - k)) := pow_add_eqv q _ _
    _ ≈ q ^ ((2 * N + 1) + k * k) := by rw [hexp]; exact eqv_refl _
    _ ≈ q ^ (2 * N + 1) * q ^ (k * k) := eqv_symm (pow_add_eqv q _ _)

/-! ## 1. The differentiated q-Pascal split (the combinatorial heart) -/

/-- **Differentiated q-Pascal split.**  For `k ≤ N`:
`dGaussTerm z q (N+1) k ≈ dGaussTerm z q N k + (k+1)·q^{2N+1}·gaussTerm z q N k`.
The `z`-derivative analogue of `GaussQBinom.gaussTerm_pascal`. -/
theorem dGaussTerm_pascal (z q : Q') (N k : Nat) (hk : k ≤ N) :
    dGaussTerm z q (N + 1) k
      ≈ dGaussTerm z q N k
          + Q'.ofNat (k + 1) * q ^ (2 * N + 1) * gaussTerm z q N k := by
  unfold dGaussTerm gaussTerm
  rw [qbin_succ_succ]
  -- second summand: collapse the q-powers via `qpow_shift`
  have hsnd :
      (Q'.ofNat (k + 1)
          * (q ^ ((k + 1) * (k + 1)) * ((q * q) ^ (N - k) * qbin (q * q) N k))) * z ^ k
        ≈ (Q'.ofNat (k + 1) * q ^ (2 * N + 1))
            * ((q ^ (k * k) * qbin (q * q) N k) * z ^ k) := by
    calc (Q'.ofNat (k + 1)
            * (q ^ ((k + 1) * (k + 1)) * ((q * q) ^ (N - k) * qbin (q * q) N k))) * z ^ k
        ≈ (Q'.ofNat (k + 1)
            * ((q ^ ((k + 1) * (k + 1)) * (q * q) ^ (N - k)) * qbin (q * q) N k)) * z ^ k :=
          mul_eqv_congr_right _ _ _
            (mul_eqv_congr_left _ _ _ (eqv_symm (mul_assoc_eqv _ _ _)))
      _ ≈ (Q'.ofNat (k + 1)
            * ((q ^ (2 * N + 1) * q ^ (k * k)) * qbin (q * q) N k)) * z ^ k :=
          mul_eqv_congr_right _ _ _
            (mul_eqv_congr_left _ _ _
              (mul_eqv_congr_right _ _ _ (qpow_shift q N k hk)))
      _ ≈ (Q'.ofNat (k + 1)
            * (q ^ (2 * N + 1) * (q ^ (k * k) * qbin (q * q) N k))) * z ^ k :=
          mul_eqv_congr_right _ _ _ (mul_eqv_congr_left _ _ _ (mul_assoc_eqv _ _ _))
      _ ≈ ((Q'.ofNat (k + 1) * q ^ (2 * N + 1)) * (q ^ (k * k) * qbin (q * q) N k)) * z ^ k :=
          mul_eqv_congr_right _ _ _ (eqv_symm (mul_assoc_eqv _ _ _))
      _ ≈ (Q'.ofNat (k + 1) * q ^ (2 * N + 1))
            * ((q ^ (k * k) * qbin (q * q) N k) * z ^ k) :=
          mul_assoc_eqv _ _ _
  calc (Q'.ofNat (k + 1)
          * (q ^ ((k + 1) * (k + 1))
              * (qbin (q * q) N (k + 1) + (q * q) ^ (N - k) * qbin (q * q) N k))) * z ^ k
      ≈ (Q'.ofNat (k + 1)
          * (q ^ ((k + 1) * (k + 1)) * qbin (q * q) N (k + 1)
              + q ^ ((k + 1) * (k + 1)) * ((q * q) ^ (N - k) * qbin (q * q) N k))) * z ^ k :=
        mul_eqv_congr_right _ _ _ (mul_eqv_congr_left _ _ _ (mul_add_eqv _ _ _))
    _ ≈ (Q'.ofNat (k + 1) * (q ^ ((k + 1) * (k + 1)) * qbin (q * q) N (k + 1))
          + Q'.ofNat (k + 1) * (q ^ ((k + 1) * (k + 1)) * ((q * q) ^ (N - k) * qbin (q * q) N k)))
            * z ^ k :=
        mul_eqv_congr_right _ _ _ (mul_add_eqv _ _ _)
    _ ≈ (Q'.ofNat (k + 1) * (q ^ ((k + 1) * (k + 1)) * qbin (q * q) N (k + 1))) * z ^ k
          + (Q'.ofNat (k + 1)
              * (q ^ ((k + 1) * (k + 1)) * ((q * q) ^ (N - k) * qbin (q * q) N k))) * z ^ k :=
        Cheb.add_mul_eqv _ _ _
    _ ≈ (Q'.ofNat (k + 1) * (q ^ ((k + 1) * (k + 1)) * qbin (q * q) N (k + 1))) * z ^ k
          + (Q'.ofNat (k + 1) * q ^ (2 * N + 1))
              * ((q ^ (k * k) * qbin (q * q) N k) * z ^ k) :=
        add_eqv_congr_left _ _ _ hsnd

/-! ## 2. The `z`-shift of a differentiated term -/

/-- `z·dGaussTerm z q N M ≈ (M+1)·gaussTerm z q N (M+1)`.  Multiplying the
reindexed differentiated summand by `z` raises the `z`-power `M ↦ M+1` and turns
it into the plain `(M+1)`-th Gauss term scaled by the integer coefficient. -/
theorem z_mul_dGaussTerm (z q : Q') (N M : Nat) :
    z * dGaussTerm z q N M ≈ Q'.ofNat (M + 1) * gaussTerm z q N (M + 1) := by
  unfold dGaussTerm gaussTerm
  calc z * (Q'.ofNat (M + 1) * (q ^ ((M + 1) * (M + 1)) * qbin (q * q) N (M + 1)) * z ^ M)
      ≈ (z * (Q'.ofNat (M + 1) * (q ^ ((M + 1) * (M + 1)) * qbin (q * q) N (M + 1)))) * z ^ M :=
        eqv_symm (mul_assoc_eqv _ _ _)
    _ ≈ ((Q'.ofNat (M + 1) * (q ^ ((M + 1) * (M + 1)) * qbin (q * q) N (M + 1))) * z) * z ^ M :=
        mul_eqv_congr_right _ _ _ (mul_comm_eqv _ _)
    _ ≈ (Q'.ofNat (M + 1) * (q ^ ((M + 1) * (M + 1)) * qbin (q * q) N (M + 1))) * (z * z ^ M) :=
        mul_assoc_eqv _ _ _
    _ ≈ Q'.ofNat (M + 1)
          * (q ^ ((M + 1) * (M + 1)) * qbin (q * q) N (M + 1) * z ^ (M + 1)) :=
        mul_assoc_eqv _ _ _

/-- `(z·q^{2N+1})·dGaussTerm z q N M ≈ (M+1)·(q^{2N+1}·gaussTerm z q N (M+1))`. -/
theorem W_mul_dGaussTerm (z q : Q') (N M : Nat) :
    (z * q ^ (2 * N + 1)) * dGaussTerm z q N M
      ≈ Q'.ofNat (M + 1) * (q ^ (2 * N + 1) * gaussTerm z q N (M + 1)) := by
  calc (z * q ^ (2 * N + 1)) * dGaussTerm z q N M
      ≈ (q ^ (2 * N + 1) * z) * dGaussTerm z q N M :=
        mul_eqv_congr_right _ _ _ (mul_comm_eqv _ _)
    _ ≈ q ^ (2 * N + 1) * (z * dGaussTerm z q N M) := mul_assoc_eqv _ _ _
    _ ≈ q ^ (2 * N + 1) * (Q'.ofNat (M + 1) * gaussTerm z q N (M + 1)) :=
        mul_eqv_congr_left _ _ _ (z_mul_dGaussTerm z q N M)
    _ ≈ (q ^ (2 * N + 1) * Q'.ofNat (M + 1)) * gaussTerm z q N (M + 1) :=
        eqv_symm (mul_assoc_eqv _ _ _)
    _ ≈ (Q'.ofNat (M + 1) * q ^ (2 * N + 1)) * gaussTerm z q N (M + 1) :=
        mul_eqv_congr_right _ _ _ (mul_comm_eqv _ _)
    _ ≈ Q'.ofNat (M + 1) * (q ^ (2 * N + 1) * gaussTerm z q N (M + 1)) :=
        mul_assoc_eqv _ _ _

/-! ## 3. Two small algebra helpers -/

/-- Integer-coefficient fold: `(M+1)·X + X ≈ (M+2)·X`. -/
theorem coeff_sum_step (M : Nat) (X : Q') :
    Q'.ofNat (M + 1) * X + X ≈ Q'.ofNat ((M + 1) + 1) * X := by
  calc Q'.ofNat (M + 1) * X + X
      ≈ Q'.ofNat (M + 1) * X + Q'.ofNat 1 * X :=
        add_eqv_congr_left _ _ _ (eqv_symm (one_mul_eqv X))
    _ ≈ (Q'.ofNat (M + 1) + Q'.ofNat 1) * X := eqv_symm (Cheb.add_mul_eqv _ _ _)
    _ ≈ Q'.ofNat ((M + 1) + 1) * X :=
        mul_eqv_congr_right _ _ _ (eqv_symm (ofNat_add_eqv (M + 1) 1))

/-- Pure additive-AC reshuffle used to close the running step:
`(u+v) + ((c+w)+e) ≈ (u + (c + (v+e))) + w`. -/
theorem acStep (u v c w e : Q') :
    (u + v) + ((c + w) + e) ≈ (u + (c + (v + e))) + w := by
  calc (u + v) + ((c + w) + e)
      ≈ u + (v + ((c + w) + e)) := add_assoc_eqv _ _ _
    _ ≈ u + (v + (c + (w + e))) :=
        add_eqv_congr_left _ _ _ (add_eqv_congr_left _ _ _ (add_assoc_eqv _ _ _))
    _ ≈ u + ((v + c) + (w + e)) :=
        add_eqv_congr_left _ _ _ (eqv_symm (add_assoc_eqv _ _ _))
    _ ≈ u + ((c + v) + (w + e)) :=
        add_eqv_congr_left _ _ _ (add_eqv_congr_right _ _ _ (add_comm_eqv _ _))
    _ ≈ u + (c + (v + (w + e))) :=
        add_eqv_congr_left _ _ _ (add_assoc_eqv _ _ _)
    _ ≈ u + (c + (v + (e + w))) :=
        add_eqv_congr_left _ _ _
          (add_eqv_congr_left _ _ _ (add_eqv_congr_left _ _ _ (add_comm_eqv _ _)))
    _ ≈ u + (c + ((v + e) + w)) :=
        add_eqv_congr_left _ _ _
          (add_eqv_congr_left _ _ _ (eqv_symm (add_assoc_eqv _ _ _)))
    _ ≈ u + ((c + (v + e)) + w) :=
        add_eqv_congr_left _ _ _ (eqv_symm (add_assoc_eqv _ _ _))
    _ ≈ (u + (c + (v + e))) + w := eqv_symm (add_assoc_eqv _ _ _)

/-! ## 4. The running differentiated step identity -/

/-- **Running differentiated step identity.**  For `M ≤ N`:

    dGaussSumUpto z q N M · (1 + z·q^{2N+1})  +  gaussSumUpto z q N M · q^{2N+1}
      ≈  dGaussSumUpto z q (N+1) M  +  (z·q^{2N+1}) · dGaussTerm z q N M.

The `z`-derivative analogue of `GaussQBinom.gaussSum_run`, with the product-rule
correction `+ gaussSumUpto · q^{2N+1}` on the left. -/
theorem dGaussSum_run (z q : Q') (N : Nat) :
    ∀ M, M ≤ N →
      dGaussSumUpto z q N M * (1 + z * q ^ (2 * N + 1))
          + gaussSumUpto z q N M * q ^ (2 * N + 1)
        ≈ dGaussSumUpto z q (N + 1) M
            + (z * q ^ (2 * N + 1)) * dGaussTerm z q N M := by
  intro M
  induction M with
  | zero =>
      intro _
      -- both running sums reduce to their single `k=0` term
      show dGaussTerm z q N 0 * (1 + z * q ^ (2 * N + 1))
            + gaussTerm z q N 0 * q ^ (2 * N + 1)
          ≈ dGaussTerm z q (N + 1) 0
              + (z * q ^ (2 * N + 1)) * dGaussTerm z q N 0
      have hDP0 := dGaussTerm_pascal z q N 0 (Nat.zero_le N)
      -- the differentiated correction term at k=0 equals `gaussTerm · q^{2N+1}`
      have hT :
          Q'.ofNat (0 + 1) * q ^ (2 * N + 1) * gaussTerm z q N 0
            ≈ gaussTerm z q N 0 * q ^ (2 * N + 1) := by
        calc Q'.ofNat (0 + 1) * q ^ (2 * N + 1) * gaussTerm z q N 0
            ≈ q ^ (2 * N + 1) * gaussTerm z q N 0 :=
              mul_eqv_congr_right _ _ _ (one_mul_eqv _)
          _ ≈ gaussTerm z q N 0 * q ^ (2 * N + 1) := mul_comm_eqv _ _
      calc dGaussTerm z q N 0 * (1 + z * q ^ (2 * N + 1))
              + gaussTerm z q N 0 * q ^ (2 * N + 1)
          ≈ (dGaussTerm z q N 0 * 1 + dGaussTerm z q N 0 * (z * q ^ (2 * N + 1)))
              + gaussTerm z q N 0 * q ^ (2 * N + 1) :=
            add_eqv_congr_right _ _ _ (mul_add_eqv _ _ _)
        _ ≈ (dGaussTerm z q N 0 + dGaussTerm z q N 0 * (z * q ^ (2 * N + 1)))
              + gaussTerm z q N 0 * q ^ (2 * N + 1) :=
            add_eqv_congr_right _ _ _ (add_eqv_congr_right _ _ _ (mul_one_eqv _))
        _ ≈ dGaussTerm z q N 0
              + (dGaussTerm z q N 0 * (z * q ^ (2 * N + 1))
                  + gaussTerm z q N 0 * q ^ (2 * N + 1)) :=
            add_assoc_eqv _ _ _
        _ ≈ dGaussTerm z q N 0
              + (gaussTerm z q N 0 * q ^ (2 * N + 1)
                  + dGaussTerm z q N 0 * (z * q ^ (2 * N + 1))) :=
            add_eqv_congr_left _ _ _ (add_comm_eqv _ _)
        _ ≈ (dGaussTerm z q N 0 + gaussTerm z q N 0 * q ^ (2 * N + 1))
              + dGaussTerm z q N 0 * (z * q ^ (2 * N + 1)) :=
            eqv_symm (add_assoc_eqv _ _ _)
        _ ≈ (dGaussTerm z q N 0 + Q'.ofNat (0 + 1) * q ^ (2 * N + 1) * gaussTerm z q N 0)
              + dGaussTerm z q N 0 * (z * q ^ (2 * N + 1)) :=
            add_eqv_congr_right _ _ _ (add_eqv_congr_left _ _ _ (eqv_symm hT))
        _ ≈ (dGaussTerm z q N 0 + Q'.ofNat (0 + 1) * q ^ (2 * N + 1) * gaussTerm z q N 0)
              + (z * q ^ (2 * N + 1)) * dGaussTerm z q N 0 :=
            add_eqv_congr_left _ _ _ (mul_comm_eqv _ _)
        _ ≈ dGaussTerm z q (N + 1) 0 + (z * q ^ (2 * N + 1)) * dGaussTerm z q N 0 :=
            add_eqv_congr_right _ _ _ (eqv_symm hDP0)
  | succ M ih =>
      intro hM
      have hMN : M ≤ N := Nat.le_of_succ_le hM
      have hIH := ih hMN
      have hDP' :
          dGaussTerm z q (N + 1) (M + 1)
            ≈ dGaussTerm z q N (M + 1)
                + Q'.ofNat ((M + 1) + 1) * (q ^ (2 * N + 1) * gaussTerm z q N (M + 1)) :=
        eqv_trans _ _ _ (dGaussTerm_pascal z q N (M + 1) hM)
          (add_eqv_congr_left _ _ _ (mul_assoc_eqv _ _ _))
      show (dGaussSumUpto z q N M + dGaussTerm z q N (M + 1)) * (1 + z * q ^ (2 * N + 1))
            + (gaussSumUpto z q N M + gaussTerm z q N (M + 1)) * q ^ (2 * N + 1)
          ≈ (dGaussSumUpto z q (N + 1) M + dGaussTerm z q (N + 1) (M + 1))
              + (z * q ^ (2 * N + 1)) * dGaussTerm z q N (M + 1)
      calc (dGaussSumUpto z q N M + dGaussTerm z q N (M + 1)) * (1 + z * q ^ (2 * N + 1))
              + (gaussSumUpto z q N M + gaussTerm z q N (M + 1)) * q ^ (2 * N + 1)
          ≈ (dGaussSumUpto z q N M * (1 + z * q ^ (2 * N + 1))
                + dGaussTerm z q N (M + 1) * (1 + z * q ^ (2 * N + 1)))
              + (gaussSumUpto z q N M * q ^ (2 * N + 1)
                + gaussTerm z q N (M + 1) * q ^ (2 * N + 1)) :=
            add_eqv_congr _ _ _ _ (Cheb.add_mul_eqv _ _ _) (Cheb.add_mul_eqv _ _ _)
        _ ≈ (dGaussSumUpto z q N M * (1 + z * q ^ (2 * N + 1))
                + gaussSumUpto z q N M * q ^ (2 * N + 1))
              + (dGaussTerm z q N (M + 1) * (1 + z * q ^ (2 * N + 1))
                + gaussTerm z q N (M + 1) * q ^ (2 * N + 1)) :=
            add_swap_inner _ _ _ _
        _ ≈ (dGaussSumUpto z q (N + 1) M + (z * q ^ (2 * N + 1)) * dGaussTerm z q N M)
              + (dGaussTerm z q N (M + 1) * (1 + z * q ^ (2 * N + 1))
                + gaussTerm z q N (M + 1) * q ^ (2 * N + 1)) :=
            add_eqv_congr_right _ _ _ hIH
        _ ≈ (dGaussSumUpto z q (N + 1) M + (z * q ^ (2 * N + 1)) * dGaussTerm z q N M)
              + ((dGaussTerm z q N (M + 1)
                    + dGaussTerm z q N (M + 1) * (z * q ^ (2 * N + 1)))
                + gaussTerm z q N (M + 1) * q ^ (2 * N + 1)) :=
            add_eqv_congr_left _ _ _
              (add_eqv_congr_right _ _ _
                (eqv_trans _ _ _ (mul_add_eqv _ _ _)
                  (add_eqv_congr_right _ _ _ (mul_one_eqv _))))
        _ ≈ (dGaussSumUpto z q (N + 1) M
                + Q'.ofNat (M + 1) * (q ^ (2 * N + 1) * gaussTerm z q N (M + 1)))
              + ((dGaussTerm z q N (M + 1)
                    + (z * q ^ (2 * N + 1)) * dGaussTerm z q N (M + 1))
                + q ^ (2 * N + 1) * gaussTerm z q N (M + 1)) :=
            add_eqv_congr _ _ _ _
              (add_eqv_congr_left _ _ _ (W_mul_dGaussTerm z q N M))
              (add_eqv_congr _ _ _ _
                (add_eqv_congr_left _ _ _ (mul_comm_eqv _ _))
                (mul_comm_eqv _ _))
        _ ≈ (dGaussSumUpto z q (N + 1) M
                + (dGaussTerm z q N (M + 1)
                    + (Q'.ofNat (M + 1) * (q ^ (2 * N + 1) * gaussTerm z q N (M + 1))
                        + q ^ (2 * N + 1) * gaussTerm z q N (M + 1))))
              + (z * q ^ (2 * N + 1)) * dGaussTerm z q N (M + 1) :=
            acStep _ _ _ _ _
        _ ≈ (dGaussSumUpto z q (N + 1) M
                + (dGaussTerm z q N (M + 1)
                    + Q'.ofNat ((M + 1) + 1) * (q ^ (2 * N + 1) * gaussTerm z q N (M + 1))))
              + (z * q ^ (2 * N + 1)) * dGaussTerm z q N (M + 1) :=
            add_eqv_congr_right _ _ _
              (add_eqv_congr_left _ _ _
                (add_eqv_congr_left _ _ _
                  (coeff_sum_step M (q ^ (2 * N + 1) * gaussTerm z q N (M + 1)))))
        _ ≈ (dGaussSumUpto z q (N + 1) M + dGaussTerm z q (N + 1) (M + 1))
              + (z * q ^ (2 * N + 1)) * dGaussTerm z q N (M + 1) :=
            add_eqv_congr_right _ _ _ (add_eqv_congr_left _ _ _ (eqv_symm hDP'))

/-! ## 5. Closure: `DerivStepProp` for all `N` -/

/-- **`DerivStepProp z q N` for all `N`.**  Specialises `dGaussSum_run` at the
full bound `M = N`: the pending top term `dGaussTerm z q (N+1) (N+1)` vanishes
(out of range), leaving exactly `DerivStepProp`. -/
theorem derivStep_all (z q : Q') : ∀ N, DerivStepProp z q N
  | 0 => derivStep_zero z q
  | P + 1 => by
      have hdz : dGaussTerm z q (P + 1) (P + 1) ≈ (0 : Q') := by
        unfold dGaussTerm
        have hq0 : qbin (q * q) (P + 1) ((P + 1) + 1) ≈ (0 : Q') :=
          qbin_out_of_range (q * q) (P + 1) ((P + 1) + 1) (by omega)
        calc Q'.ofNat ((P + 1) + 1)
                * (q ^ (((P + 1) + 1) * ((P + 1) + 1)) * qbin (q * q) (P + 1) ((P + 1) + 1))
                * z ^ (P + 1)
            ≈ Q'.ofNat ((P + 1) + 1)
                * (q ^ (((P + 1) + 1) * ((P + 1) + 1)) * (0 : Q')) * z ^ (P + 1) :=
              mul_eqv_congr_right _ _ _
                (mul_eqv_congr_left _ _ _ (mul_eqv_congr_left _ _ _ hq0))
          _ ≈ Q'.ofNat ((P + 1) + 1) * (0 : Q') * z ^ (P + 1) :=
              mul_eqv_congr_right _ _ _ (mul_eqv_congr_left _ _ _ (mul_zero_eqv _))
          _ ≈ (0 : Q') * z ^ (P + 1) :=
              mul_eqv_congr_right _ _ _ (mul_zero_eqv _)
          _ ≈ (0 : Q') := zero_mul_eqv _
      have hg :
          gaussSumDeriv z q (P + 1) + dGaussTerm z q (P + 1) (P + 1)
            ≈ gaussSumDeriv z q (P + 1) := by
        calc gaussSumDeriv z q (P + 1) + dGaussTerm z q (P + 1) (P + 1)
            ≈ gaussSumDeriv z q (P + 1) + (0 : Q') := add_eqv_congr_left _ _ _ hdz
          _ ≈ gaussSumDeriv z q (P + 1) := by rw [add_zero']; exact eqv_refl _
      have hrun :
          (gaussSumDeriv z q (P + 1) + dGaussTerm z q (P + 1) (P + 1))
              * (1 + z * q ^ (2 * (P + 1) + 1))
            + gaussSum z q (P + 1) * q ^ (2 * (P + 1) + 1)
          ≈ gaussSumDeriv z q (P + 2)
              + (z * q ^ (2 * (P + 1) + 1)) * dGaussTerm z q (P + 1) (P + 1) :=
        dGaussSum_run z q (P + 1) (P + 1) (Nat.le_refl _)
      show gaussSumDeriv z q (P + 1) * (1 + z * q ^ (2 * (P + 1) + 1))
            + gaussSum z q (P + 1) * q ^ (2 * (P + 1) + 1)
          ≈ gaussSumDeriv z q (P + 2)
      calc gaussSumDeriv z q (P + 1) * (1 + z * q ^ (2 * (P + 1) + 1))
              + gaussSum z q (P + 1) * q ^ (2 * (P + 1) + 1)
          ≈ (gaussSumDeriv z q (P + 1) + dGaussTerm z q (P + 1) (P + 1))
                * (1 + z * q ^ (2 * (P + 1) + 1))
              + gaussSum z q (P + 1) * q ^ (2 * (P + 1) + 1) :=
            add_eqv_congr_right _ _ _
              (mul_eqv_congr_right _ _ _ (eqv_symm hg))
        _ ≈ gaussSumDeriv z q (P + 2)
              + (z * q ^ (2 * (P + 1) + 1)) * dGaussTerm z q (P + 1) (P + 1) := hrun
        _ ≈ gaussSumDeriv z q (P + 2) + (z * q ^ (2 * (P + 1) + 1)) * (0 : Q') :=
            add_eqv_congr_left _ _ _ (mul_eqv_congr_left _ _ _ hdz)
        _ ≈ gaussSumDeriv z q (P + 2) + (0 : Q') :=
            add_eqv_congr_left _ _ _ (mul_zero_eqv _)
        _ ≈ gaussSumDeriv z q (P + 2) := by rw [add_zero']; exact eqv_refl _

/-! ## 6. Unconditional downstream (single-`z` / `Q'` case) -/

/-- The full differentiated Gauss identity, now UNCONDITIONAL for any single-`z`
(`Q'`) parametrisation. -/
theorem qProdDeriv_eq_gaussSumDeriv_uncond (z q : Q') :
    ∀ N, qProdDeriv z q N ≈ gaussSumDeriv z q N :=
  qProdDeriv_eq_gaussSumDeriv z q (derivStep_all z q)

/-- The differentiated Jacobi identity at the `CReal` level, now UNCONDITIONAL
for any single-`z` (`Q'`) realisation of the product / sum-derivative partials. -/
theorem qProdDeriv_creal_equiv_uncond (z q : Q')
    {Pd Sd : CReal}
    (hPd : ∀ N : Nat, Pd.approx N = qProdDeriv z q N)
    (hSd : ∀ N : Nat, Sd.approx N = gaussSumDeriv z q N) :
    CReal.Equiv Pd Sd :=
  qProdDeriv_creal_equiv z q (derivStep_all z q) hPd hSd

/-- The engine's `jacobiDeriv` field, discharged UNCONDITIONALLY in the
single-`z` (`Q'`) case. -/
theorem jacobiDeriv_of_engine_uncond (z q : Q')
    {Pd Sd : CReal}
    (hPd : ∀ N : Nat, Pd.approx N = qProdDeriv z q N)
    (hSd : ∀ N : Nat, Sd.approx N = gaussSumDeriv z q N) :
    CReal.Equiv Pd Sd :=
  jacobiDeriv_of_engine z q (derivStep_all z q) hPd hSd

end YMGap.Continuum.DerivStepPropClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.DerivStepPropClose.qq_pow
#print axioms YMGap.Continuum.DerivStepPropClose.qpow_shift
#print axioms YMGap.Continuum.DerivStepPropClose.dGaussTerm_pascal
#print axioms YMGap.Continuum.DerivStepPropClose.z_mul_dGaussTerm
#print axioms YMGap.Continuum.DerivStepPropClose.W_mul_dGaussTerm
#print axioms YMGap.Continuum.DerivStepPropClose.coeff_sum_step
#print axioms YMGap.Continuum.DerivStepPropClose.acStep
#print axioms YMGap.Continuum.DerivStepPropClose.dGaussSum_run
#print axioms YMGap.Continuum.DerivStepPropClose.derivStep_all
#print axioms YMGap.Continuum.DerivStepPropClose.qProdDeriv_eq_gaussSumDeriv_uncond
#print axioms YMGap.Continuum.DerivStepPropClose.qProdDeriv_creal_equiv_uncond
#print axioms YMGap.Continuum.DerivStepPropClose.jacobiDeriv_of_engine_uncond
