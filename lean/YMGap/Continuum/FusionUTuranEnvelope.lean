/-
Track A / R2 — FORMALIZING the four elementary envelope bounds of the w-FREE coupling
Turán `(‡)`, and the load-bearing finite-geometric-sum lemma over `Q'`.

# What this module adds

`FusionUTuranWFree.uturan_of_envelope : UTuranEnvelope Q → ∀ s, (‡′)` reduces the whole
coupling Turán to inhabiting `UTuranEnvelope Q` for `Q ≥ 4` — i.e. the four elementary
envelope bounds on `Ucoup Q m = U(m) = Σ_{i+j=m} i·j·Q^{ij}`.  This module formalizes:

  * `geomTelescope` — the LOAD-BEARING new lemma: the exact finite-geometric telescoping
    identity `(Σ_{d<k} Q^d)·(Q−1) ≃ Q^k − 1` over `Q'` (`qpow`), by induction.  Its
    consequence `geomTail_le`, `(Σ_{d<k} Q^d)·(Q−1) ≤ Q^k`, is the finite geometric-sum
    UPPER bound.
  * `Ucoup_lower_even`, `Ucoup_lower_odd` — the two term-keeping LOWER bounds (L)(i)/(ii)
    on the numerator `U(s+3)`, division-free, by `fsum` term extraction:
      - even `s = 2t`: the two central terms of the odd index `s+3`,
        `U(s+3) ≥ 2·M₃·Q^{M₃}`, `M₃ = (t+1)(t+2)`;
      - odd `s = 2t+1`: central + first pair of the even index `s+3`,
        `U(s+3) ≥ M₃·Q^{M₃} + 2·(M₃−1)·Q^{M₃−1}`, `M₃ = (t+2)²`.

These are the (L) legs of the four `UTuranEnvelope` fields, plus the geometric engine that
the (U) legs need.  The two (U) geometric-tail UPPER bounds require, in addition, a
reindex-free split-at-the-peak of `Ucoup` and are named as the residual below (they are NOT
proved here); consequently `UTuranEnvelope` is NOT inhabited here and NOTHING downstream is
closed.  In particular this module inhabits NO guarded Clay-frontier bundle
(`FusionConvLogConcaveCore` for general `N`, `SymMinorGershgorin`, `FiniteSMargin`,
`YMGapGuard`) and the `acN ↔ Ucoup` reindexing bridge is left OPEN.  This is NOT a 4D
Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `qpow`/`fsum` definitions and their `eqv`/order
algebra, structural induction, and `decide`/`omega` on closed facts.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext`/`Quot.sound` only.
No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.FusionUTuranWFree
import YMGap.Continuum.CubeRatioBounds
import YMGap.Continuum.EigShiftOrder
import YMGap.Continuum.WHMarginTailClose
import YMGap.Continuum.HeatKernelRGStep
import YMGap.Constructive.Sqrt

namespace YMGap.Continuum.FusionUTuranEnvelope

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionUTuranWFree
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.HeatKernelRGStep

/-! ## 1. The finite-geometric telescoping identity over `Q'` (the load-bearing lemma) -/

/-- `1 + (Q + -1) ≃ Q` (a local additive-inverse helper). -/
theorem one_add_pred (Q : Q') : ((1 : Q') + (Q + -(1 : Q'))).eqv Q := by
  refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv (1 : Q') (Q + -(1 : Q'))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv Q (-(1 : Q')) (1 : Q')) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left Q (-(1 : Q') + (1 : Q')) 0 (by decide)) ?_
  exact q_add_zero_eqv Q

/-- **`geomTelescope` — THE FINITE-GEOMETRIC TELESCOPING IDENTITY.**  Over `Q'`, for every
`k`,

    (Σ_{d<k} Q^d)·(Q − 1)  ≃  Q^k − 1.

Proof: induction on `k`.  The successor step uses `Q^k·(Q−1) + (Q^{k}−1)` telescoping into
`Q^{k+1} − 1` via `Q^{k+1} = Q^k·Q` and `1 + (Q−1) ≃ Q`. -/
theorem geomTelescope (Q : Q') :
    ∀ k, (fsum (qpow Q) k * (Q + -(1 : Q'))).eqv (qpow Q k + -(1 : Q'))
  | 0 => by
      -- (0 · (Q−1)).eqv (1 + -1)
      show ((0 : Q') * (Q + -(1 : Q'))).eqv ((1 : Q') + -(1 : Q'))
      exact Q'.eqv_trans _ _ _ (q_zero_mul _) (by decide)
  | k + 1 => by
      -- ((fsum k + Q^k) · (Q−1)).eqv (Q^k · Q + -1)
      show ((fsum (qpow Q) k + qpow Q k) * (Q + -(1 : Q'))).eqv (qpow Q k * Q + -(1 : Q'))
      -- distribute
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (fsum (qpow Q) k) (qpow Q k) (Q + -(1 : Q'))) ?_
      -- fsum k·(Q−1) + Q^k·(Q−1) ≃ (Q^k + -1) + Q^k·(Q−1)   [IH on first]
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (qpow Q k * (Q + -(1 : Q'))) (geomTelescope Q k)) ?_
      -- (Q^k + -1) + Q^k·(Q−1) ≃ (Q^k + Q^k·(Q−1)) + -1
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (qpow Q k) (-(1 : Q')) (qpow Q k * (Q + -(1 : Q')))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (qpow Q k) (-(1 : Q') + qpow Q k * (Q + -(1 : Q')))
          (qpow Q k * (Q + -(1 : Q')) + -(1 : Q')) (Q'.add_comm_eqv _ _)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (qpow Q k) (qpow Q k * (Q + -(1 : Q'))) (-(1 : Q')))) ?_
      -- reduce to (Q^k + Q^k·(Q−1)).eqv (Q^k · Q)
      refine Q'.add_eqv_congr_right _ _ (-(1 : Q')) ?_
      -- Q^k + Q^k·(Q−1) ≃ Q^k·1 + Q^k·(Q−1) ≃ Q^k·(1 + (Q−1)) ≃ Q^k·Q
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (qpow Q k * (Q + -(1 : Q')))
          (Q'.eqv_symm (Q'.mul_one_eqv (qpow Q k)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_add_eqv (qpow Q k) (1 : Q') (Q + -(1 : Q')))) ?_
      exact Q'.mul_eqv_congr_left (qpow Q k) _ _ (one_add_pred Q)

/-- **`geomTail_le` — the finite geometric-sum UPPER bound.**  `(Σ_{d<k} Q^d)·(Q−1) ≤ Q^k`
(the `−1` in `geomTelescope` is dropped in the safe direction). -/
theorem geomTail_le (Q : Q') (k : Nat) :
    fsum (qpow Q) k * (Q + -(1 : Q')) ≤ qpow Q k := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (geomTelescope Q k)) ?_
  -- Q^k + -1 ≤ Q^k
  refine Q'.le_trans' _ _ _ (Q'.add_le_add_left (qpow Q k) (-(1 : Q')) 0 (by decide)) ?_
  exact Q'.le_of_eqv (q_add_zero_eqv (qpow Q k))

/-! ## 2. The two term-keeping LOWER bounds on the numerator `U(s+3)` (L)(i)/(ii) -/

/-- The `Ucoup` summand as an explicit function (`g i = i(m−i)·Q^{i(m−i)}`). -/
private def uterm (Q : Q') (m i : Nat) : Q' := Q'.ofNat (i * (m - i)) * qpow Q (i * (m - i))

private theorem Ucoup_eq_fsum (Q : Q') (m : Nat) :
    Ucoup Q m = fsum (uterm Q m) m := rfl

private theorem uterm_nonneg {Q : Q'} (hQ : (0 : Q') ≤ Q) (m i : Nat) :
    (0 : Q') ≤ uterm Q m i :=
  Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ _)

/-- **`Ucoup_lower_even` — the (L)(i) lower bound.**  For `s = 2t` (so `s+3 = 2t+3` is odd
with peak `M₃ = (t+1)(t+2)` achieved at the two central indices `t+1, t+2`),

    2·M₃·Q^{M₃}  ≤  U(s+3).

The two central summands `uterm (2t+3) (t+1)` and `uterm (2t+3) (t+2)` each equal
`M₃·Q^{M₃}` (`(t+1)(t+2−?) = (t+1)(t+2)`); `fsum_two_term_le` keeps both. -/
theorem Ucoup_lower_even {Q : Q'} (hQ : (0 : Q') ≤ Q) (t : Nat) :
    (Q'.ofNat ((t + 1) * (t + 2)) * qpow Q ((t + 1) * (t + 2))
      + Q'.ofNat ((t + 1) * (t + 2)) * qpow Q ((t + 1) * (t + 2)))
      ≤ Ucoup Q (2 * t + 3) := by
  rw [Ucoup_eq_fsum]
  -- the two central summands equal M₃·Q^{M₃}
  have hi1 : uterm Q (2 * t + 3) (t + 1)
      = Q'.ofNat ((t + 1) * (t + 2)) * qpow Q ((t + 1) * (t + 2)) := by
    unfold uterm
    have he : (t + 1) * (2 * t + 3 - (t + 1)) = (t + 1) * (t + 2) := by
      have : 2 * t + 3 - (t + 1) = t + 2 := by omega
      rw [this]
    rw [he]
  have hi2 : uterm Q (2 * t + 3) (t + 2)
      = Q'.ofNat ((t + 1) * (t + 2)) * qpow Q ((t + 1) * (t + 2)) := by
    unfold uterm
    have he : (t + 2) * (2 * t + 3 - (t + 2)) = (t + 1) * (t + 2) := by
      have : 2 * t + 3 - (t + 2) = t + 1 := by omega
      rw [this]; exact Nat.mul_comm (t + 2) (t + 1)
    rw [he]
  have hkey : uterm Q (2 * t + 3) (t + 1) + uterm Q (2 * t + 3) (t + 2)
      ≤ fsum (uterm Q (2 * t + 3)) (2 * t + 3) :=
    EigShiftOrder.fsum_two_term_le (uterm_nonneg hQ (2 * t + 3)) (t + 1) (t + 2)
      (by omega) (2 * t + 3) (by omega)
  rw [hi1, hi2] at hkey
  exact hkey

/-- **`Ucoup_lower_odd` — the (L)(ii) lower bound.**  For `s = 2t+1` (so `s+3 = 2t+4` is
even with peak `M₃ = (t+2)²` at the central index `t+2`, and first pair value `M₃−1` at
`t+1, t+3`),

    M₃·Q^{M₃} + (M₃−1)·Q^{M₃−1} + (M₃−1)·Q^{M₃−1}  ≤  U(s+3),

division-free (central + first pair kept), `M₃ = (t+2)²`, `M₃−1 = (t+1)(t+3)`. -/
theorem Ucoup_lower_odd {Q : Q'} (hQ : (0 : Q') ≤ Q) (t : Nat) :
    (Q'.ofNat ((t + 2) * (t + 2)) * qpow Q ((t + 2) * (t + 2))
      + (Q'.ofNat ((t + 1) * (t + 3)) * qpow Q ((t + 1) * (t + 3))
         + Q'.ofNat ((t + 1) * (t + 3)) * qpow Q ((t + 1) * (t + 3))))
      ≤ Ucoup Q (2 * t + 4) := by
  rw [Ucoup_eq_fsum]
  -- central summand at i = t+2 equals M₃·Q^{M₃}
  have hc : uterm Q (2 * t + 4) (t + 2)
      = Q'.ofNat ((t + 2) * (t + 2)) * qpow Q ((t + 2) * (t + 2)) := by
    unfold uterm
    have he : (t + 2) * (2 * t + 4 - (t + 2)) = (t + 2) * (t + 2) := by
      have : 2 * t + 4 - (t + 2) = t + 2 := by omega
      rw [this]
    rw [he]
  -- pair summands at i = t+1 and i = t+3 each equal (M₃−1)·Q^{M₃−1}
  have hp1 : uterm Q (2 * t + 4) (t + 1)
      = Q'.ofNat ((t + 1) * (t + 3)) * qpow Q ((t + 1) * (t + 3)) := by
    unfold uterm
    have he : (t + 1) * (2 * t + 4 - (t + 1)) = (t + 1) * (t + 3) := by
      have : 2 * t + 4 - (t + 1) = t + 3 := by omega
      rw [this]
    rw [he]
  have hp3 : uterm Q (2 * t + 4) (t + 3)
      = Q'.ofNat ((t + 1) * (t + 3)) * qpow Q ((t + 1) * (t + 3)) := by
    unfold uterm
    have he : (t + 3) * (2 * t + 4 - (t + 3)) = (t + 1) * (t + 3) := by
      have : 2 * t + 4 - (t + 3) = t + 1 := by omega
      rw [this]; exact Nat.mul_comm (t + 3) (t + 1)
    rw [he]
  -- keep the three summands i = t+1, t+2, t+3 (all < 2t+4), reorder to central + pair
  have h3 : (uterm Q (2 * t + 4) (t + 1) + uterm Q (2 * t + 4) (t + 2))
              + uterm Q (2 * t + 4) (t + 3)
      ≤ fsum (uterm Q (2 * t + 4)) (2 * t + 4) :=
    WHMarginTailClose.fsum_three_term_le (uterm_nonneg hQ (2 * t + 4)) (t + 1) (t + 2) (t + 3)
      (by omega) (by omega) (2 * t + 4) (by omega)
  rw [hc, hp1, hp3] at h3
  -- h3 LHS = (P + M₃) + P ; goal LHS = M₃ + (P + P)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) h3
  -- M₃ + (P + P)  ≃  (P + M₃) + P
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  exact Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv _ _)

/-! ## 3. The `qpow` exponent-monotone atom and the geometric-sum engines -/

/-- `1 ≤ qpow Q k` for `Q ≥ 1` (a power of something `≥ 1` is `≥ 1`). -/
theorem one_le_qpow {Q : Q'} (hQ : (1 : Q') ≤ Q) : ∀ k, (1 : Q') ≤ qpow Q k
  | 0 => by show (1 : Q') ≤ (1 : Q'); exact Q'.le_refl' 1
  | k + 1 => by
      show (1 : Q') ≤ qpow Q k * Q
      have hqk : (1 : Q') ≤ qpow Q k := one_le_qpow hQ k
      have hqk0 : (0 : Q') ≤ qpow Q k :=
        Q'.le_trans' _ _ _ (by decide) hqk
      have h1 : qpow Q k * (1 : Q') ≤ qpow Q k * Q :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hQ hqk0
      have h2 : qpow Q k ≤ qpow Q k * Q :=
        Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) h1
      exact Q'.le_trans' _ _ _ hqk h2

/-- **`qpow_exp_mono` — monotonicity of `qpow` in the exponent.**  For `Q ≥ 1` and
`a ≤ b`, `qpow Q a ≤ qpow Q b`. -/
theorem qpow_exp_mono {Q : Q'} (hQ : (1 : Q') ≤ Q) {a b : Nat} (hab : a ≤ b) :
    qpow Q a ≤ qpow Q b := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hab
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ
  have hqa0 : (0 : Q') ≤ qpow Q a := qpow_nonneg Q hQ0 a
  have hd1 : (1 : Q') ≤ qpow Q d := one_le_qpow hQ d
  have h1 : qpow Q a * (1 : Q') ≤ qpow Q a * qpow Q d :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hd1 hqa0
  have h2 : qpow Q a ≤ qpow Q a * qpow Q d :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _))) h1
  exact Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.eqv_symm (qpow_add Q a d)))

/-! ### 3a. Local finite-sum reversal (copied to avoid a heavy import). -/

private theorem fsum_shift_consE (g : Nat → Q') :
    ∀ n, (fsum g (n + 1)).eqv (g 0 + fsum (fun i => g (i + 1)) n)
  | 0 => by
    show ((0 : Q') + g 0).eqv (g 0 + (0 : Q'))
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' (g 0))) ?_
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (g 0)))
  | n + 1 => by
    show (fsum g (n + 1) + g (n + 1)).eqv
        (g 0 + (fsum (fun i => g (i + 1)) n + g (n + 1)))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (g (n + 1)) (fsum_shift_consE g n)) ?_
    exact Q'.add_assoc_eqv (g 0) (fsum (fun i => g (i + 1)) n) (g (n + 1))

/-- Split a partial sum at `a`: `Σ_{p<a+b} h ≃ Σ_{p<a} h + Σ_{k<b} h(a+k)`. -/
private theorem fsum_split_at (h : Nat → Q') (a : Nat) :
    ∀ b, (fsum h (a + b)).eqv (fsum h a + fsum (fun k => h (a + k)) b)
  | 0 => by
    show (fsum h a).eqv (fsum h a + (0 : Q'))
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (fsum h a)))
  | b + 1 => by
    show (fsum h (a + b) + h (a + b)).eqv
        (fsum h a + (fsum (fun k => h (a + k)) b + h (a + b)))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (h (a + b)) (fsum_split_at h a b)) ?_
    exact Q'.add_assoc_eqv (fsum h a) (fsum (fun k => h (a + k)) b) (h (a + b))

/-- Reversal of a partial sum over `[0,n]`: `Σ_{p≤n} G(n-p) ≃ Σ_{k≤n} G(k)`. -/
private theorem revSumE (G : Nat → Q') :
    ∀ n, (fsum (fun p => G (n - p)) (n + 1)).eqv (fsum G (n + 1))
  | 0 => Q'.eqv_refl _
  | n + 1 => by
    refine Q'.eqv_trans _ _ _ (fsum_shift_consE (fun p => G ((n + 1) - p)) (n + 1)) ?_
    have hcongr : (fsum (fun i => G ((n + 1) - (i + 1))) (n + 1)).eqv
        (fsum (fun i => G (n - i)) (n + 1)) := by
      refine fsum_eqv_congr _ _ (fun i => ?_) (n + 1)
      exact Q'.eqv_of_eq (congrArg G (by omega))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hcongr) ?_
    have hib : (fsum (fun i => G (n - i)) (n + 1)).eqv (fsum G (n + 1)) := revSumE G n
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hib) ?_
    show (G (n + 1) + fsum G (n + 1)).eqv (fsum G (n + 1) + G (n + 1))
    exact Q'.add_comm_eqv (G (n + 1)) (fsum G (n + 1))

/-! ### 3b. The ascending / descending geometric-sum bounds. -/

/-- **Ascending geometric bound.**  `(Σ_{i<k} Q^{base+i})·(Q−1) ≤ Q^{base+k}`. -/
theorem geomAsc_le {Q : Q'} (hQ0 : (0 : Q') ≤ Q) (base k : Nat) :
    fsum (fun i => qpow Q (base + i)) k * (Q + -(1 : Q')) ≤ qpow Q (base + k) := by
  have hS : (fsum (fun i => qpow Q (base + i)) k).eqv
      (qpow Q base * fsum (qpow Q) k) := by
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr _ _ (fun i => qpow_add Q base i) k) ?_
    exact Q'.eqv_symm (fsum_const_mul (qpow Q base) (qpow Q) k)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ (Q + -(1 : Q')) hS)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_assoc_eqv (qpow Q base) (fsum (qpow Q) k) (Q + -(1 : Q')))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (geomTail_le Q k) (qpow_nonneg Q hQ0 base)) ?_
  exact Q'.le_of_eqv (Q'.eqv_symm (qpow_add Q base k))

/-- **Descending geometric bound.**  `(Σ_{r<k} Q^{P-r})·(Q−1) ≤ Q^{P+1}` for `k ≤ P+1`. -/
theorem geomDesc_le {Q : Q'} (hQ0 : (0 : Q') ≤ Q) {P k : Nat} (hk : k ≤ P + 1) :
    fsum (fun r => qpow Q (P - r)) k * (Q + -(1 : Q')) ≤ qpow Q (P + 1) := by
  cases k with
  | zero =>
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (q_zero_mul _)) (qpow_nonneg Q hQ0 (P + 1))
  | succ n =>
      have hnP : n ≤ P := by omega
      have href : (fsum (fun r => qpow Q (P - r)) (n + 1)).eqv
          (fsum (fun x => qpow Q ((P - n) + x)) (n + 1)) := by
        have h1 : (fsum (fun r => qpow Q (P - r)) (n + 1)).eqv
            (fsum (fun p => qpow Q ((P - n) + (n - p))) (n + 1)) := by
          refine fsum_eqv_congr_lt _ _ (n + 1) (fun p hp => ?_)
          exact Q'.eqv_of_eq (congrArg (qpow Q) (by omega))
        exact Q'.eqv_trans _ _ _ h1 (revSumE (fun x => qpow Q ((P - n) + x)) n)
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ href)) ?_
      have hb := geomAsc_le hQ0 (P - n) (n + 1)
      have he : (P - n) + (n + 1) = P + 1 := by omega
      rw [he] at hb
      exact hb

/-! ### 3c. Nat exponent/coefficient identities for the antidiagonal peak. -/

/-- Peak identity (left half, even index): `i·(2(i+d)−i) + d² = (i+d)²`. -/
theorem sq_identity_even_left (i d : Nat) :
    i * (2 * (i + d) - i) + d * d = (i + d) * (i + d) := by
  have h2 : 2 * (i + d) - i = i + 2 * d := by omega
  rw [h2]
  have a1 : i * (i + 2 * d) = i * i + i * (2 * d) := Nat.mul_add i i (2 * d)
  have a2 : i * (2 * d) = i * d + i * d := by
    have : i * (2 * d) = i * (d + d) := by rw [Nat.two_mul]
    rw [this, Nat.mul_add]
  have a3 := expand i d d
  have a4 : i * d = d * i := Nat.mul_comm i d
  omega

/-- Peak identity (right half, even index): `(2r+d)·d + r² = (r+d)²`. -/
theorem sq_identity_even_right (r d : Nat) :
    (2 * r + d) * d + r * r = (r + d) * (r + d) := by
  have e1 : (2 * r + d) * d = 2 * (r * d) + d * d := by
    have h := Nat.add_mul (2 * r) d d
    have h2 : 2 * r * d = 2 * (r * d) := by rw [Nat.mul_assoc]
    omega
  have e2 := expand r d d
  have e3 : r * d = d * r := Nat.mul_comm r d
  omega

/-- Coefficient+exponent bound, even left half: for `i < n`,
`i·(2n−i) ≤ n²` and `i·(2n−i) ≤ (n²−n) + i`. -/
theorem coeff_exp_even_left (n i : Nat) (hi : i < n) :
    i * (2 * n - i) ≤ n * n ∧ i * (2 * n - i) ≤ (n * n - n) + i := by
  obtain ⟨d, rfl⟩ := Nat.le.dest (Nat.le_of_lt hi)
  have hid := sq_identity_even_left i d
  have hd1 : 1 ≤ d := by omega
  have hdd : d ≤ d * d := by
    calc d = d * 1 := (Nat.mul_one d).symm
      _ ≤ d * d := Nat.mul_le_mul_left d hd1
  have hNge : (i + d) ≤ (i + d) * (i + d) := by
    have h1 : 1 ≤ i + d := by omega
    calc i + d = (i + d) * 1 := (Nat.mul_one _).symm
      _ ≤ (i + d) * (i + d) := Nat.mul_le_mul_left _ h1
  exact ⟨by omega, by omega⟩

/-- Coefficient+exponent bound, even right half: for `r < n`,
`(n+r)·(2n−(n+r)) ≤ n²` and `(n+r)·(2n−(n+r)) ≤ n² − r`. -/
theorem coeff_exp_even_right (n r : Nat) (hr : r < n) :
    (n + r) * (2 * n - (n + r)) ≤ n * n ∧ (n + r) * (2 * n - (n + r)) ≤ n * n - r := by
  obtain ⟨d, rfl⟩ := Nat.le.dest (Nat.le_of_lt hr)
  -- n = r + d
  have hidx : (r + d + r) * (2 * (r + d) - (r + d + r)) = (2 * r + d) * d := by
    have h1 : 2 * (r + d) - (r + d + r) = d := by omega
    have h2 : r + d + r = 2 * r + d := by omega
    rw [h1, h2]
  rw [hidx]
  have hid := sq_identity_even_right r d
  have hd1 : 1 ≤ d := by omega
  have hrr : r ≤ r * r := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · simp [h0]
    · calc r = r * 1 := (Nat.mul_one r).symm
        _ ≤ r * r := Nat.mul_le_mul_left r hpos
  have hNge : (r + d) ≤ (r + d) * (r + d) := by
    have h1 : 1 ≤ r + d := by omega
    calc r + d = (r + d) * 1 := (Nat.mul_one _).symm
      _ ≤ (r + d) * (r + d) := Nat.mul_le_mul_left _ h1
  exact ⟨by omega, by omega⟩

/-! ## 4. The (U) UPPER envelope bound — even index. -/

/-- **`Ucoup_upper_even`.**  For even index `2n` (`n ≥ 1`, `M = n²`):
`U(2n)·(Q−1) ≤ (M·Q^M)·(Q+1)`, i.e. `U(2n) ≤ M·Q^M·(Q+1)/(Q−1) = M·Q^M·Tₑ`. -/
theorem Ucoup_upper_even {Q : Q'} (hQ1 : (1 : Q') ≤ Q) {n : Nat} (hn : 1 ≤ n) :
    Ucoup Q (2 * n) * (Q + -(1 : Q'))
      ≤ (Q'.ofNat (n * n) * qpow Q (n * n)) * (Q + 1) := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ1
  have hnM : n ≤ n * n := by
    calc n = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * n := Nat.mul_le_mul_left n hn
  have hD0 : (0 : Q') ≤ Q + -(1 : Q') := by
    have h0 : ((1 : Q') + -(1 : Q')).eqv 0 := by decide
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h0) (Q'.add_le_add_right _ _ (-(1 : Q')) hQ1)
  -- split U(2n) = L + R at the peak index n
  have hL : fsum (uterm Q (2 * n)) (2 * n) = fsum (uterm Q (2 * n)) (n + n) := by
    congr 1; omega
  have hsplit : (Ucoup Q (2 * n)).eqv
      (fsum (uterm Q (2 * n)) n + fsum (fun r => uterm Q (2 * n) (n + r)) n) := by
    rw [Ucoup_eq_fsum, hL]
    exact fsum_split_at (uterm Q (2 * n)) n n
  -- termwise majorants
  have termL : ∀ i, i < n →
      uterm Q (2 * n) i ≤ Q'.ofNat (n * n) * qpow Q ((n * n - n) + i) := by
    intro i hi
    have hc := (coeff_exp_even_left n i hi).1
    have he := (coeff_exp_even_left n i hi).2
    show Q'.ofNat (i * (2 * n - i)) * qpow Q (i * (2 * n - i))
        ≤ Q'.ofNat (n * n) * qpow Q ((n * n - n) + i)
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.ofNat_le_ofNat hc) (qpow_nonneg Q hQ0 _)) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_exp_mono hQ1 he) (ofNat_nonneg _)
  have termR : ∀ r, r < n →
      uterm Q (2 * n) (n + r) ≤ Q'.ofNat (n * n) * qpow Q (n * n - r) := by
    intro r hr
    have hc := (coeff_exp_even_right n r hr).1
    have he := (coeff_exp_even_right n r hr).2
    show Q'.ofNat ((n + r) * (2 * n - (n + r))) * qpow Q ((n + r) * (2 * n - (n + r)))
        ≤ Q'.ofNat (n * n) * qpow Q (n * n - r)
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.ofNat_le_ofNat hc) (qpow_nonneg Q hQ0 _)) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_exp_mono hQ1 he) (ofNat_nonneg _)
  have hLbound : fsum (uterm Q (2 * n)) n
      ≤ Q'.ofNat (n * n) * fsum (fun i => qpow Q ((n * n - n) + i)) n := by
    refine Q'.le_trans' _ _ _ (fsum_mono_lt n termL) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm
      (fsum_const_mul (Q'.ofNat (n * n)) (fun i => qpow Q ((n * n - n) + i)) n))
  have hRbound : fsum (fun r => uterm Q (2 * n) (n + r)) n
      ≤ Q'.ofNat (n * n) * fsum (fun r => qpow Q (n * n - r)) n := by
    refine Q'.le_trans' _ _ _ (fsum_mono_lt n termR) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm
      (fsum_const_mul (Q'.ofNat (n * n)) (fun r => qpow Q (n * n - r)) n))
  have hUb : Ucoup Q (2 * n)
      ≤ Q'.ofNat (n * n) * fsum (fun i => qpow Q ((n * n - n) + i)) n
        + Q'.ofNat (n * n) * fsum (fun r => qpow Q (n * n - r)) n := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
    exact Q'.add_le_add hLbound hRbound
  -- geometric bounds on the two shell sums
  have hSL : fsum (fun i => qpow Q ((n * n - n) + i)) n * (Q + -(1 : Q'))
      ≤ qpow Q (n * n) := by
    have h := geomAsc_le hQ0 (n * n - n) n
    have he : (n * n - n) + n = n * n := by omega
    rw [he] at h; exact h
  have hSR : fsum (fun r => qpow Q (n * n - r)) n * (Q + -(1 : Q'))
      ≤ qpow Q (n * n + 1) := geomDesc_le hQ0 (by omega)
  -- multiply the U-bound by (Q−1) ≥ 0 and distribute
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hUb hD0) ?_
  have hdist : ((Q'.ofNat (n * n) * fsum (fun i => qpow Q ((n * n - n) + i)) n
        + Q'.ofNat (n * n) * fsum (fun r => qpow Q (n * n - r)) n) * (Q + -(1 : Q'))).eqv
      (Q'.ofNat (n * n) * (fsum (fun i => qpow Q ((n * n - n) + i)) n * (Q + -(1 : Q')))
        + Q'.ofNat (n * n) * (fsum (fun r => qpow Q (n * n - r)) n * (Q + -(1 : Q')))) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _) ?_
    exact Q'.add_eqv_congr' (Q'.mul_assoc_eqv _ _ _) (Q'.mul_assoc_eqv _ _ _)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hdist) ?_
  have hbnd : Q'.ofNat (n * n) * (fsum (fun i => qpow Q ((n * n - n) + i)) n * (Q + -(1 : Q')))
        + Q'.ofNat (n * n) * (fsum (fun r => qpow Q (n * n - r)) n * (Q + -(1 : Q')))
      ≤ Q'.ofNat (n * n) * qpow Q (n * n) + Q'.ofNat (n * n) * qpow Q (n * n + 1) :=
    Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hSL (ofNat_nonneg _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hSR (ofNat_nonneg _))
  refine Q'.le_trans' _ _ _ hbnd ?_
  -- fold `A + A·Q ≃ A·(Q+1)`
  have hfold : (Q'.ofNat (n * n) * qpow Q (n * n) + Q'.ofNat (n * n) * qpow Q (n * n + 1)).eqv
      ((Q'.ofNat (n * n) * qpow Q (n * n)) * (Q + 1)) := by
    have e1 : (Q'.ofNat (n * n) * qpow Q (n * n + 1)).eqv
        ((Q'.ofNat (n * n) * qpow Q (n * n)) * Q) := by
      show (Q'.ofNat (n * n) * (qpow Q (n * n) * Q)).eqv
          ((Q'.ofNat (n * n) * qpow Q (n * n)) * Q)
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ e1) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv _ _) ?_
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv _ Q 1) ?_
    exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_one_eqv _)
  exact Q'.le_of_eqv hfold

/-! ## 5. The (U) UPPER envelope bound — odd index (step-2 geometric engines). -/

private theorem two_mul_eqvE (T : Q') : (Q'.ofNat 2 * T).eqv (T + T) := by
  have h : (Q'.ofNat 2).eqv (1 + 1) := by decide
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ T h) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (1 + 1) T) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv T 1 1) ?_
  exact Q'.add_eqv_congr' (Q'.mul_one_eqv T) (Q'.mul_one_eqv T)

/-- **Ascending step-2 geometric bound.**  `(Σ_{i<k} Q^{base+2i})·(Q²−1) ≤ Q^{base+2k}`. -/
theorem geomAsc2_le {Q : Q'} (hQ0 : (0 : Q') ≤ Q) (base k : Nat) :
    fsum (fun i => qpow Q (base + 2 * i)) k * (qpow Q 2 + -(1 : Q'))
      ≤ qpow Q (base + 2 * k) := by
  have hterm : ∀ i, (qpow Q (base + 2 * i)).eqv (qpow Q base * qpow (qpow Q 2) i) := by
    intro i
    refine Q'.eqv_trans _ _ _ (qpow_add Q base (2 * i)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (qpow_qpow Q 2 i))
  have hS : (fsum (fun i => qpow Q (base + 2 * i)) k).eqv
      (qpow Q base * fsum (qpow (qpow Q 2)) k) := by
    refine Q'.eqv_trans _ _ _ (fsum_eqv_congr _ _ hterm k) ?_
    exact Q'.eqv_symm (fsum_const_mul (qpow Q base) (qpow (qpow Q 2)) k)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hS)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_assoc_eqv (qpow Q base) (fsum (qpow (qpow Q 2)) k)
      (qpow Q 2 + -(1 : Q')))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (geomTail_le (qpow Q 2) k) (qpow_nonneg Q hQ0 base)) ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (qpow_qpow Q 2 k)) ?_
  exact Q'.eqv_symm (qpow_add Q base (2 * k))

/-- **Descending step-2 geometric bound.**  `(Σ_{r<k} Q^{P-2r})·(Q²−1) ≤ Q^{P+2}` for `2k ≤ P+2`. -/
theorem geomDesc2_le {Q : Q'} (hQ0 : (0 : Q') ≤ Q) {P k : Nat} (hk : 2 * k ≤ P + 2) :
    fsum (fun r => qpow Q (P - 2 * r)) k * (qpow Q 2 + -(1 : Q')) ≤ qpow Q (P + 2) := by
  cases k with
  | zero =>
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (q_zero_mul _)) (qpow_nonneg Q hQ0 (P + 2))
  | succ n =>
      have hnP : 2 * n ≤ P := by omega
      have href : (fsum (fun r => qpow Q (P - 2 * r)) (n + 1)).eqv
          (fsum (fun x => qpow Q ((P - 2 * n) + 2 * x)) (n + 1)) := by
        have h1 : (fsum (fun r => qpow Q (P - 2 * r)) (n + 1)).eqv
            (fsum (fun p => qpow Q ((P - 2 * n) + 2 * (n - p))) (n + 1)) := by
          refine fsum_eqv_congr_lt _ _ (n + 1) (fun p hp => ?_)
          exact Q'.eqv_of_eq (congrArg (qpow Q) (by omega))
        exact Q'.eqv_trans _ _ _ h1 (revSumE (fun x => qpow Q ((P - 2 * n) + 2 * x)) n)
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ href)) ?_
      have hb := geomAsc2_le hQ0 (P - 2 * n) (n + 1)
      have he : (P - 2 * n) + 2 * (n + 1) = P + 2 := by omega
      rw [he] at hb
      exact hb

/-! ### 5a. Nat exponent/coefficient identities for the odd antidiagonal peak. -/

/-- Peak identity (left half, odd index): `i·(2(i+d)+1−i) + d(d+1) = (i+d)(i+d+1)`. -/
theorem sq_identity_odd_left (i d : Nat) :
    i * (2 * (i + d) + 1 - i) + d * (d + 1) = (i + d) * ((i + d) + 1) := by
  have h2 : 2 * (i + d) + 1 - i = i + 2 * d + 1 := by omega
  rw [h2]
  have a1 : i * (i + 2 * d + 1) = i * i + i * (2 * d) + i := by
    rw [show i + 2 * d + 1 = (i + 2 * d) + 1 from rfl, Nat.mul_add, Nat.mul_add, Nat.mul_one]
  have a2 : i * (2 * d) = i * d + i * d := by
    rw [show 2 * d = d + d from Nat.two_mul d, Nat.mul_add]
  have a3 : (i + d) * ((i + d) + 1) = (i + d) * (i + d) + (i + d) := by
    rw [Nat.mul_add, Nat.mul_one]
  have a4 := expand i d d
  have a5 : d * (d + 1) = d * d + d := by rw [Nat.mul_add, Nat.mul_one]
  have a6 : i * d = d * i := Nat.mul_comm i d
  omega

/-- Peak identity (right half, odd index): `(2r+d+1)·d + r(r+1) = (r+d)(r+d+1)`. -/
theorem sq_identity_odd_right (r d : Nat) :
    (2 * r + d + 1) * d + r * (r + 1) = (r + d) * ((r + d) + 1) := by
  have a1 : (2 * r + d + 1) * d = (2 * r + d) * d + d := by
    rw [show 2 * r + d + 1 = (2 * r + d) + 1 from rfl, Nat.add_mul, Nat.one_mul]
  have a2 : (2 * r + d) * d = 2 * (r * d) + d * d := by
    rw [Nat.add_mul, Nat.mul_assoc]
  have a3 : r * (r + 1) = r * r + r := by rw [Nat.mul_add, Nat.mul_one]
  have a4 : (r + d) * ((r + d) + 1) = (r + d) * (r + d) + (r + d) := by
    rw [Nat.mul_add, Nat.mul_one]
  have a5 := expand r d d
  have a6 : r * d = d * r := Nat.mul_comm r d
  omega

/-- Coefficient+exponent bound, odd left half: for `i ≤ n`,
`i·(2n+1−i) ≤ n(n+1)` and `i·(2n+1−i) ≤ (n(n+1) − 2n) + 2i`. -/
theorem coeff_exp_odd_left (n i : Nat) (hi : i ≤ n) :
    i * (2 * n + 1 - i) ≤ n * (n + 1)
    ∧ i * (2 * n + 1 - i) ≤ (n * (n + 1) - 2 * n) + 2 * i := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hi
  have hid := sq_identity_odd_left i d
  have hdexp : d * (d + 1) = d * d + d := by rw [Nat.mul_add, Nat.mul_one]
  have hdd : d ≤ d * d := by
    rcases Nat.eq_zero_or_pos d with h0 | hp
    · simp [h0]
    · calc d = d * 1 := (Nat.mul_one d).symm
        _ ≤ d * d := Nat.mul_le_mul_left d hp
  have hMexp : (i + d) * ((i + d) + 1) = (i + d) * (i + d) + (i + d) := by
    rw [Nat.mul_add, Nat.mul_one]
  have hNsq : (i + d) ≤ (i + d) * (i + d) := by
    rcases Nat.eq_zero_or_pos (i + d) with h0 | hp
    · simp [h0]
    · calc (i + d) = (i + d) * 1 := (Nat.mul_one _).symm
        _ ≤ (i + d) * (i + d) := Nat.mul_le_mul_left _ hp
  exact ⟨by omega, by omega⟩

/-- Coefficient+exponent bound, odd right half: for `r < n`,
`(n+1+r)·(2n+1−(n+1+r)) ≤ n(n+1)` and `… ≤ n(n+1) − 2r`. -/
theorem coeff_exp_odd_right (n r : Nat) (hr : r < n) :
    (n + 1 + r) * (2 * n + 1 - (n + 1 + r)) ≤ n * (n + 1)
    ∧ (n + 1 + r) * (2 * n + 1 - (n + 1 + r)) ≤ n * (n + 1) - 2 * r := by
  obtain ⟨d, rfl⟩ := Nat.le.dest (Nat.le_of_lt hr)
  have hidx : (r + d + 1 + r) * (2 * (r + d) + 1 - (r + d + 1 + r)) = (2 * r + d + 1) * d := by
    have h1 : 2 * (r + d) + 1 - (r + d + 1 + r) = d := by omega
    have h2 : r + d + 1 + r = 2 * r + d + 1 := by omega
    rw [h1, h2]
  rw [hidx]
  have hid := sq_identity_odd_right r d
  have hrr : r ≤ r * r := by
    rcases Nat.eq_zero_or_pos r with h0 | hp
    · simp [h0]
    · calc r = r * 1 := (Nat.mul_one r).symm
        _ ≤ r * r := Nat.mul_le_mul_left r hp
  have hMexp : (r + d) * ((r + d) + 1) = (r + d) * (r + d) + (r + d) := by
    rw [Nat.mul_add, Nat.mul_one]
  have hNsq : (r + d) ≤ (r + d) * (r + d) := by
    rcases Nat.eq_zero_or_pos (r + d) with h0 | hp
    · simp [h0]
    · calc (r + d) = (r + d) * 1 := (Nat.mul_one _).symm
        _ ≤ (r + d) * (r + d) := Nat.mul_le_mul_left _ hp
  have hrexp : r * (r + 1) = r * r + r := by rw [Nat.mul_add, Nat.mul_one]
  exact ⟨by omega, by omega⟩

/-- **`Ucoup_upper_odd`.**  For odd index `2n+1` (`n ≥ 1`, `M = n(n+1)`):
`U(2n+1)·(Q²−1) ≤ (M·Q^M)·(2·Q²)`, i.e. `U(2n+1) ≤ M·Q^M·T_O`, `T_O = 2Q²/(Q²−1)`. -/
theorem Ucoup_upper_odd {Q : Q'} (hQ1 : (1 : Q') ≤ Q) {n : Nat} (hn : 1 ≤ n) :
    Ucoup Q (2 * n + 1) * (qpow Q 2 + -(1 : Q'))
      ≤ (Q'.ofNat (n * (n + 1)) * qpow Q (n * (n + 1))) * (Q'.ofNat 2 * qpow Q 2) := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ1
  have hq2 : (1 : Q') ≤ qpow Q 2 := one_le_qpow hQ1 2
  have hD20 : (0 : Q') ≤ qpow Q 2 + -(1 : Q') := by
    have h0 : ((1 : Q') + -(1 : Q')).eqv 0 := by decide
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h0) (Q'.add_le_add_right _ _ (-(1 : Q')) hq2)
  have hnn : n ≤ n * n := by
    calc n = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * n := Nat.mul_le_mul_left n hn
  have hMe : n * (n + 1) = n * n + n := by rw [Nat.mul_add, Nat.mul_one]
  have h2nM : 2 * n ≤ n * (n + 1) := by omega
  -- split U(2n+1) = L + R at index n+1
  have hL : fsum (uterm Q (2 * n + 1)) (2 * n + 1)
      = fsum (uterm Q (2 * n + 1)) ((n + 1) + n) := by
    congr 1; omega
  have hsplit : (Ucoup Q (2 * n + 1)).eqv
      (fsum (uterm Q (2 * n + 1)) (n + 1)
        + fsum (fun r => uterm Q (2 * n + 1) ((n + 1) + r)) n) := by
    rw [Ucoup_eq_fsum, hL]
    exact fsum_split_at (uterm Q (2 * n + 1)) (n + 1) n
  have termL : ∀ i, i < n + 1 →
      uterm Q (2 * n + 1) i ≤ Q'.ofNat (n * (n + 1)) * qpow Q ((n * (n + 1) - 2 * n) + 2 * i) := by
    intro i hi
    have hc := (coeff_exp_odd_left n i (by omega)).1
    have he := (coeff_exp_odd_left n i (by omega)).2
    show Q'.ofNat (i * (2 * n + 1 - i)) * qpow Q (i * (2 * n + 1 - i))
        ≤ Q'.ofNat (n * (n + 1)) * qpow Q ((n * (n + 1) - 2 * n) + 2 * i)
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.ofNat_le_ofNat hc) (qpow_nonneg Q hQ0 _)) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_exp_mono hQ1 he) (ofNat_nonneg _)
  have termR : ∀ r, r < n →
      uterm Q (2 * n + 1) ((n + 1) + r)
        ≤ Q'.ofNat (n * (n + 1)) * qpow Q (n * (n + 1) - 2 * r) := by
    intro r hr
    have hc := (coeff_exp_odd_right n r hr).1
    have he := (coeff_exp_odd_right n r hr).2
    show Q'.ofNat ((n + 1 + r) * (2 * n + 1 - (n + 1 + r)))
          * qpow Q ((n + 1 + r) * (2 * n + 1 - (n + 1 + r)))
        ≤ Q'.ofNat (n * (n + 1)) * qpow Q (n * (n + 1) - 2 * r)
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.ofNat_le_ofNat hc) (qpow_nonneg Q hQ0 _)) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_exp_mono hQ1 he) (ofNat_nonneg _)
  have hLbound : fsum (uterm Q (2 * n + 1)) (n + 1)
      ≤ Q'.ofNat (n * (n + 1)) * fsum (fun i => qpow Q ((n * (n + 1) - 2 * n) + 2 * i)) (n + 1) := by
    refine Q'.le_trans' _ _ _ (fsum_mono_lt (n + 1) termL) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm
      (fsum_const_mul (Q'.ofNat (n * (n + 1)))
        (fun i => qpow Q ((n * (n + 1) - 2 * n) + 2 * i)) (n + 1)))
  have hRbound : fsum (fun r => uterm Q (2 * n + 1) ((n + 1) + r)) n
      ≤ Q'.ofNat (n * (n + 1)) * fsum (fun r => qpow Q (n * (n + 1) - 2 * r)) n := by
    refine Q'.le_trans' _ _ _ (fsum_mono_lt n termR) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm
      (fsum_const_mul (Q'.ofNat (n * (n + 1)))
        (fun r => qpow Q (n * (n + 1) - 2 * r)) n))
  have hUb : Ucoup Q (2 * n + 1)
      ≤ Q'.ofNat (n * (n + 1)) * fsum (fun i => qpow Q ((n * (n + 1) - 2 * n) + 2 * i)) (n + 1)
        + Q'.ofNat (n * (n + 1)) * fsum (fun r => qpow Q (n * (n + 1) - 2 * r)) n := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) ?_
    exact Q'.add_le_add hLbound hRbound
  have hSL : fsum (fun i => qpow Q ((n * (n + 1) - 2 * n) + 2 * i)) (n + 1)
        * (qpow Q 2 + -(1 : Q')) ≤ qpow Q (n * (n + 1) + 2) := by
    have h := geomAsc2_le hQ0 (n * (n + 1) - 2 * n) (n + 1)
    have he : (n * (n + 1) - 2 * n) + 2 * (n + 1) = n * (n + 1) + 2 := by omega
    rw [he] at h; exact h
  have hSR : fsum (fun r => qpow Q (n * (n + 1) - 2 * r)) n * (qpow Q 2 + -(1 : Q'))
      ≤ qpow Q (n * (n + 1) + 2) := geomDesc2_le hQ0 (by omega)
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hUb hD20) ?_
  have hdist : ((Q'.ofNat (n * (n + 1))
          * fsum (fun i => qpow Q ((n * (n + 1) - 2 * n) + 2 * i)) (n + 1)
        + Q'.ofNat (n * (n + 1)) * fsum (fun r => qpow Q (n * (n + 1) - 2 * r)) n)
        * (qpow Q 2 + -(1 : Q'))).eqv
      (Q'.ofNat (n * (n + 1))
          * (fsum (fun i => qpow Q ((n * (n + 1) - 2 * n) + 2 * i)) (n + 1)
              * (qpow Q 2 + -(1 : Q')))
        + Q'.ofNat (n * (n + 1))
          * (fsum (fun r => qpow Q (n * (n + 1) - 2 * r)) n * (qpow Q 2 + -(1 : Q')))) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _) ?_
    exact Q'.add_eqv_congr' (Q'.mul_assoc_eqv _ _ _) (Q'.mul_assoc_eqv _ _ _)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hdist) ?_
  have hbnd : Q'.ofNat (n * (n + 1))
          * (fsum (fun i => qpow Q ((n * (n + 1) - 2 * n) + 2 * i)) (n + 1)
              * (qpow Q 2 + -(1 : Q')))
        + Q'.ofNat (n * (n + 1))
          * (fsum (fun r => qpow Q (n * (n + 1) - 2 * r)) n * (qpow Q 2 + -(1 : Q')))
      ≤ Q'.ofNat (n * (n + 1)) * qpow Q (n * (n + 1) + 2)
        + Q'.ofNat (n * (n + 1)) * qpow Q (n * (n + 1) + 2) :=
    Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hSL (ofNat_nonneg _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hSR (ofNat_nonneg _))
  refine Q'.le_trans' _ _ _ hbnd ?_
  have hfold : (Q'.ofNat (n * (n + 1)) * qpow Q (n * (n + 1) + 2)
               + Q'.ofNat (n * (n + 1)) * qpow Q (n * (n + 1) + 2)).eqv
      ((Q'.ofNat (n * (n + 1)) * qpow Q (n * (n + 1))) * (Q'.ofNat 2 * qpow Q 2)) := by
    have hterm : (Q'.ofNat (n * (n + 1)) * qpow Q (n * (n + 1) + 2)).eqv
        ((Q'.ofNat (n * (n + 1)) * qpow Q (n * (n + 1))) * qpow Q 2) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (qpow_add Q (n * (n + 1)) 2)) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hterm hterm) ?_
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (two_mul_eqvE (qpow Q 2))) ?_
    exact Q'.mul_add_eqv _ (qpow Q 2) (qpow Q 2)
  exact Q'.le_of_eqv hfold

/-! ## 6. Assembling `UTuranEnvelope` from the four PROVED legs.

The four legs above give, per parity of `s`, a term-keeping LOWER bound on the numerator
`U(s+3)` and geometric-tail UPPER bounds `U(m)·(Q−1) ≤ …` / `U(m)·(Q²−1) ≤ …` on the
denominators.  We now discharge the whole `UTuranEnvelope Q` interface for `Q ≥ 4`, using the
CRUDE-SCALAR packaging: the upper legs are converted to `U(m) ≤ c·(M·Q^M)` with the *clean*
rational constants `c = 5/3` (even, since `(Q+1)/(Q−1) ≤ 5/3` for `Q ≥ 4`) and `c = 32/15`
(odd, since `2Q²/(Q²−1) ≤ 32/15` for `Q ≥ 4`), avoiding division in the reduced field.  The
reduced inequality then collapses — via the exact antidiagonal exponent identities `(E)` — to
two elementary rational `Q`-facts (`even`: `256·(5/3)² ≤ 900`; `odd`: a positive-definite
quadratic `1048576·Q ≤ 50625·(2Q+3)²`, true for `Q ≥ 4`). -/

/-- Right cancellation of a positive factor (`a·c ≤ b·c → 0 < c → a ≤ b`). -/
private theorem le_of_mul_le_mul_rightL {a b c : Q'} (h : a * c ≤ b * c) (hc : (0 : Q') < c) :
    a ≤ b := by
  have h' : c * a ≤ c * b :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv c a))
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv b c)))
  exact Q'.le_of_mul_le_mul_left h' hc

/-- Four-product rearrangement `(a·b)·(c·d) ≃ (a·c)·(b·d)`. -/
private theorem mul4comm (a b c d : Q') : ((a * b) * (c * d)).eqv ((a * c) * (b * d)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

/-- Two coupling blocks multiply into one: `(c₁·Q^{m₁})·(c₂·Q^{m₂}) ≃ (c₁·c₂)·Q^{m₁+m₂}`. -/
private theorem blkMul (Q c1 c2 : Q') (m1 m2 : Nat) :
    ((c1 * qpow Q m1) * (c2 * qpow Q m2)).eqv ((c1 * c2) * qpow Q (m1 + m2)) := by
  refine Q'.eqv_trans _ _ _ (mul4comm c1 (qpow Q m1) c2 (qpow Q m2)) ?_
  exact Q'.mul_eqv_congr_left (c1 * c2) _ _ (Q'.eqv_symm (qpow_add Q m1 m2))

/-- `Q ≥ 4 ⟹ 1 ≤ Q`. -/
private theorem one_le_of_four_le {Q : Q'} (hQ4 : (Q'.ofNat 4) ≤ Q) : (1 : Q') ≤ Q :=
  Q'.le_trans' _ _ _ (by decide) hQ4

/-- `Q ≥ 4 ⟹ 0 ≤ Q`. -/
private theorem zero_le_of_four_le {Q : Q'} (hQ4 : (Q'.ofNat 4) ≤ Q) : (0 : Q') ≤ Q :=
  Q'.le_trans' _ _ _ (by decide) hQ4

/-- `Q ≥ 4 ⟹ 0 < Q − 1`. -/
private theorem sub1_pos {Q : Q'} (hQ4 : (Q'.ofNat 4) ≤ Q) : (0 : Q') < Q + -(1 : Q') := by
  have h3 : (Q'.ofNat 3) ≤ Q + -(1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (Q'.ofNat 3).eqv ((Q'.ofNat 4) + -(1 : Q'))))
      (Q'.add_le_add_right _ _ (-(1 : Q')) hQ4)
  exact Q'.pos_of_lt_of_le (by decide) h3

/-- `Q ≥ 4 ⟹ 16 ≤ Q²`. -/
private theorem qpow2_ge16 {Q : Q'} (hQ4 : (Q'.ofNat 4) ≤ Q) : (Q'.ofNat 16) ≤ qpow Q 2 := by
  have hQ0 : (0 : Q') ≤ Q := zero_le_of_four_le hQ4
  have h1 : (Q'.ofNat 4) * (Q'.ofNat 4) ≤ (Q'.ofNat 4) * Q :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hQ4 (by decide)
  have h2 : (Q'.ofNat 4) * Q ≤ Q * Q :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hQ4 hQ0
  have h16 : (Q'.ofNat 16) ≤ Q * Q :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (Q'.ofNat 16).eqv ((Q'.ofNat 4) * (Q'.ofNat 4))))
      (Q'.le_trans' _ _ _ h1 h2)
  -- qpow Q 2 = (qpow Q 1) * Q = ((qpow Q 0) * Q) * Q = (1 * Q) * Q
  have hq : (qpow Q 2).eqv (Q * Q) := by
    show ((qpow Q 0 * Q) * Q).eqv (Q * Q)
    exact Q'.mul_eqv_congr_right _ _ Q
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ Q (Q'.eqv_of_eq (qpow_zero Q)))
        (Q'.one_mul_eqv Q))
  exact Q'.le_trans' _ _ _ h16 (Q'.ge_of_eqv hq)

/-- `Q ≥ 4 ⟹ 0 < Q² − 1`. -/
private theorem sub1_pos2 {Q : Q'} (hQ4 : (Q'.ofNat 4) ≤ Q) : (0 : Q') < qpow Q 2 + -(1 : Q') := by
  have h16 := qpow2_ge16 hQ4
  have h15 : (Q'.ofNat 15) ≤ qpow Q 2 + -(1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by decide : (Q'.ofNat 15).eqv ((Q'.ofNat 16) + -(1 : Q'))))
      (Q'.add_le_add_right _ _ (-(1 : Q')) h16)
  exact Q'.pos_of_lt_of_le (by decide) h15

/-- Left-commutativity `a·(b·c) ≃ b·(a·c)`. -/
private theorem mulLC (a b c : Q') : (a * (b * c)).eqv (b * (a * c)) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

/-- **The reduced ODD scalar closure.**  `1048576·Q ≤ 50625·(2Q+3)²` for `Q ≥ 4`.  This is a
positive-definite quadratic; proved by the crude chain `(2Q+3)² ≥ 2Q·(2Q+3)` and `Q ≥ 4`. -/
theorem odd_scalar_ge {Q : Q'} (hQ4 : (Q'.ofNat 4) ≤ Q) :
    Q'.ofNat 1048576 * Q
      ≤ Q'.ofNat 50625 * ((Q'.ofNat 2 * Q + Q'.ofNat 3) * (Q'.ofNat 2 * Q + Q'.ofNat 3)) := by
  have hQ0 : (0 : Q') ≤ Q := zero_le_of_four_le hQ4
  have h2Q_nonneg : (0 : Q') ≤ Q'.ofNat 2 * Q := Q'.mul_nonneg _ _ (by decide) hQ0
  have hs_nonneg : (0 : Q') ≤ Q'.ofNat 2 * Q + Q'.ofNat 3 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (0 : Q').eqv ((0 : Q') + (0 : Q'))))
      (Q'.add_le_add h2Q_nonneg (by decide))
  have h2Qle : Q'.ofNat 2 * Q ≤ Q'.ofNat 2 * Q + Q'.ofNat 3 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))))
      (Q'.add_le_add_left _ _ _ (by decide : (0 : Q') ≤ Q'.ofNat 3))
  -- (2Q)·(2Q+3) ≤ (2Q+3)²
  have hstep1 : (Q'.ofNat 2 * Q) * (Q'.ofNat 2 * Q + Q'.ofNat 3)
      ≤ (Q'.ofNat 2 * Q + Q'.ofNat 3) * (Q'.ofNat 2 * Q + Q'.ofNat 3) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ h2Qle hs_nonneg
  have hstep2 : Q'.ofNat 50625 * ((Q'.ofNat 2 * Q) * (Q'.ofNat 2 * Q + Q'.ofNat 3))
      ≤ Q'.ofNat 50625 * ((Q'.ofNat 2 * Q + Q'.ofNat 3) * (Q'.ofNat 2 * Q + Q'.ofNat 3)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hstep1 (by decide)
  -- rewrite 50625·((2Q)·(2Q+3)) ≃ Q·(101250·(2Q+3))
  have hRe : (Q'.ofNat 50625 * ((Q'.ofNat 2 * Q) * (Q'.ofNat 2 * Q + Q'.ofNat 3))).eqv
      (Q * (Q'.ofNat 101250 * (Q'.ofNat 2 * Q + Q'.ofNat 3))) := by
    have e1 : ((Q'.ofNat 2 * Q) * (Q'.ofNat 2 * Q + Q'.ofNat 3)).eqv
        (Q * (Q'.ofNat 2 * (Q'.ofNat 2 * Q + Q'.ofNat 3))) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (Q'.ofNat 2) Q)) ?_
      exact Q'.mul_assoc_eqv Q (Q'.ofNat 2) (Q'.ofNat 2 * Q + Q'.ofNat 3)
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ e1) ?_
    refine Q'.eqv_trans _ _ _ (mulLC (Q'.ofNat 50625) Q _) ?_
    refine Q'.mul_eqv_congr_left Q _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 50625) (Q'.ofNat 2) _)) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide : (Q'.ofNat 50625 * Q'.ofNat 2).eqv (Q'.ofNat 101250))
  -- bound: 1048576 ≤ 101250·(2Q+3)
  have hbnd_eqv : (Q'.ofNat 101250 * (Q'.ofNat 2 * Q + Q'.ofNat 3)).eqv
      (Q'.ofNat 202500 * Q + Q'.ofNat 303750) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat 101250) (Q'.ofNat 2 * Q) (Q'.ofNat 3)) ?_
    refine Q'.add_eqv_congr' ?_ (by decide : (Q'.ofNat 101250 * Q'.ofNat 3).eqv (Q'.ofNat 303750))
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 101250) (Q'.ofNat 2) Q)) ?_
    exact Q'.mul_eqv_congr_right _ _ Q (by decide : (Q'.ofNat 101250 * Q'.ofNat 2).eqv (Q'.ofNat 202500))
  have h810 : (Q'.ofNat 810000) ≤ Q'.ofNat 202500 * Q :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by decide : (Q'.ofNat 810000).eqv (Q'.ofNat 202500 * Q'.ofNat 4)))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hQ4 (by decide))
  have hbnd : Q'.ofNat 1048576 ≤ Q'.ofNat 101250 * (Q'.ofNat 2 * Q + Q'.ofNat 3) := by
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hbnd_eqv)
    refine Q'.le_trans' _ _ _
      (by decide : Q'.ofNat 1048576 ≤ Q'.ofNat 810000 + Q'.ofNat 303750) ?_
    exact Q'.add_le_add_right _ _ _ h810
  have hStepA : Q'.ofNat 1048576 * Q
      ≤ Q'.ofNat 50625 * ((Q'.ofNat 2 * Q) * (Q'.ofNat 2 * Q + Q'.ofNat 3)) := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv (Q'.ofNat 1048576) Q)) ?_
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hRe)
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hbnd hQ0
  exact Q'.le_trans' _ _ _ hStepA hstep2

/-- **The reduced EVEN algebra.**  With the clean constant `5/3` on the denominators and the
even exponent identities `m₃² = m₂m₄`, `(m₃+m₃)+1 = m₂+m₄`, the reduced inequality collapses to
`256·(5/3)² ≤ 900`. -/
theorem even_reduced_alg {Q : Q'} (hQ0 : (0 : Q') ≤ Q) (m2 m3 m4 : Nat)
    (hprod : m3 * m3 = m2 * m4) (hsum1 : (m3 + m3) + 1 = m2 + m4) :
    Q'.ofNat 256 *
        ((Q'.mkPos 5 3 (by decide) * (Q'.ofNat m2 * qpow Q m2))
       * (Q'.mkPos 5 3 (by decide) * (Q'.ofNat m4 * qpow Q m4)))
      ≤ (Q'.ofNat 225 * Q) *
        ((Q'.ofNat m3 * qpow Q m3 + Q'.ofNat m3 * qpow Q m3)
       * (Q'.ofNat m3 * qpow Q m3 + Q'.ofNat m3 * qpow Q m3)) := by
  let A := Q'.ofNat m3 * qpow Q m3
  let mk := Q'.mkPos 5 3 (by decide : (0:Nat) < 3)
  -- common collapsed value V
  have hVnn : (0 : Q') ≤ Q'.ofNat (m2 * m4) * qpow Q (m2 + m4) :=
    Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ0 _)
  -- LHS ≃ (256·(mk·mk))·V
  have hB2B4 : ((Q'.ofNat m2 * qpow Q m2) * (Q'.ofNat m4 * qpow Q m4)).eqv
      (Q'.ofNat (m2 * m4) * qpow Q (m2 + m4)) :=
    Q'.eqv_trans _ _ _ (blkMul Q (Q'.ofNat m2) (Q'.ofNat m4) m2 m4)
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv m2 m4)))
  have hLHS : (Q'.ofNat 256 *
        ((mk * (Q'.ofNat m2 * qpow Q m2)) * (mk * (Q'.ofNat m4 * qpow Q m4)))).eqv
      ((Q'.ofNat 256 * (mk * mk)) * (Q'.ofNat (m2 * m4) * qpow Q (m2 + m4))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 256) _ _
        (Q'.eqv_trans _ _ _
          (mul4comm mk (Q'.ofNat m2 * qpow Q m2) mk (Q'.ofNat m4 * qpow Q m4))
          (Q'.mul_eqv_congr_left (mk * mk) _ _ hB2B4))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 256) (mk * mk) _)
  -- RHS ≃ 900·V
  have hA2 : (A * A).eqv (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3)) :=
    Q'.eqv_trans _ _ _ (blkMul Q (Q'.ofNat m3) (Q'.ofNat m3) m3 m3)
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv m3 m3)))
  have h_lo : (A + A).eqv (Q'.ofNat 2 * A) := Q'.eqv_symm (two_mul_eqvE A)
  have h_ll : ((A + A) * (A + A)).eqv
      (Q'.ofNat 4 * (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (A + A) h_lo)
        (Q'.mul_eqv_congr_left (Q'.ofNat 2 * A) _ _ h_lo)) ?_
    refine Q'.eqv_trans _ _ _ (mul4comm (Q'.ofNat 2) A (Q'.ofNat 2) A) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (A * A) (by decide : (Q'.ofNat 2 * Q'.ofNat 2).eqv (Q'.ofNat 4))) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ hA2
  have hVeq : Q'.ofNat (m3 * m3) * qpow Q ((m3 + m3) + 1)
      = Q'.ofNat (m2 * m4) * qpow Q (m2 + m4) := by rw [hprod, hsum1]
  have hQW3 : (Q * (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3))).eqv
      (Q'.ofNat (m2 * m4) * qpow Q (m2 + m4)) := by
    refine Q'.eqv_trans _ _ _ (mulLC Q (Q'.ofNat (m3 * m3)) (qpow Q (m3 + m3))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (m3 * m3)) _ _ (Q'.mul_comm_eqv Q (qpow Q (m3 + m3)))) ?_
    -- qpow (m3+m3) * Q = qpow ((m3+m3)+1) definitionally
    exact Q'.eqv_of_eq hVeq
  have hRHS : ((Q'.ofNat 225 * Q) * ((A + A) * (A + A))).eqv
      (Q'.ofNat 900 * (Q'.ofNat (m2 * m4) * qpow Q (m2 + m4))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 225 * Q) _ _ h_ll) ?_
    -- (225·Q)·(4·W3) ≃ 900·(Q·W3) ≃ 900·V
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat 225) Q (Q'.ofNat 4 * (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 225) _ _
        (mulLC Q (Q'.ofNat 4) (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 225) (Q'.ofNat 4)
        (Q * (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3))))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide : (Q'.ofNat 225 * Q'.ofNat 4).eqv (Q'.ofNat 900))) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat 900) _ _ hQW3
  -- combine
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) (Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hRHS))
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (by decide : Q'.ofNat 256 * (Q'.mkPos 5 3 (by decide) * Q'.mkPos 5 3 (by decide)) ≤ Q'.ofNat 900)
    hVnn

/-- `0 ≤ a → 0 ≤ b → 0 ≤ a + b`. -/
private theorem add_nn (a b : Q') (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) : (0 : Q') ≤ a + b :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (0 : Q').eqv ((0 : Q') + (0 : Q')))) (Q'.add_le_add ha hb)

/-- `qpow Q 2 ≃ Q·Q`. -/
private theorem qpow2_eq (Q : Q') : (qpow Q 2).eqv (Q * Q) := by
  show ((qpow Q 0 * Q) * Q).eqv (Q * Q)
  exact Q'.mul_eqv_congr_right _ _ Q
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ Q (Q'.eqv_of_eq (qpow_zero Q)))
      (Q'.one_mul_eqv Q))

/-- **The reduced ODD algebra.**  With the clean constant `32/15`, the odd exponent identities
`m₂+m₄ = m₃+m₃`, `m₂m₄ ≤ m₃²`, the central/pair split (`m₃ = mp+1`, `3m₃ ≤ 4mp`), the reduced
inequality collapses to the positive-definite quadratic `odd_scalar_ge`. -/
theorem odd_reduced_alg {Q : Q'} (hQ4 : (Q'.ofNat 4) ≤ Q) (m2 m3 m4 mp : Nat)
    (hsum2 : m2 + m4 = m3 + m3) (hprodle : m2 * m4 ≤ m3 * m3)
    (hmp : m3 = mp + 1) (hcoef : 3 * m3 ≤ 4 * mp) :
    Q'.ofNat 256 *
        ((Q'.mkPos 32 15 (by decide) * (Q'.ofNat m2 * qpow Q m2))
       * (Q'.mkPos 32 15 (by decide) * (Q'.ofNat m4 * qpow Q m4)))
      ≤ (Q'.ofNat 225 * Q) *
        ((Q'.ofNat m3 * qpow Q m3 + (Q'.ofNat mp * qpow Q mp + Q'.ofNat mp * qpow Q mp))
       * (Q'.ofNat m3 * qpow Q m3 + (Q'.ofNat mp * qpow Q mp + Q'.ofNat mp * qpow Q mp))) := by
  have hQ0 : (0 : Q') ≤ Q := zero_le_of_four_le hQ4
  let mk := Q'.mkPos 32 15 (by decide : (0:Nat) < 15)
  let C := Q'.ofNat m3 * qpow Q m3
  let P := Q'.ofNat mp * qpow Q mp
  let G := Q'.ofNat m3 * qpow Q mp
  let s2 := Q'.ofNat 2 * Q + Q'.ofNat 3
  let lo := C + (P + P)
  have hqmp0 : (0 : Q') ≤ qpow Q mp := qpow_nonneg Q hQ0 _
  have hC0 : (0 : Q') ≤ C := Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ0 _)
  have hP0 : (0 : Q') ≤ P := Q'.mul_nonneg _ _ (ofNat_nonneg _) hqmp0
  have hG0 : (0 : Q') ≤ G := Q'.mul_nonneg _ _ (ofNat_nonneg _) hqmp0
  have h2Q0 : (0 : Q') ≤ Q'.ofNat 2 * Q := Q'.mul_nonneg _ _ (by decide) hQ0
  have hs20 : (0 : Q') ≤ s2 := add_nn _ _ h2Q0 (by decide)
  have hlo0 : (0 : Q') ≤ lo := add_nn _ _ hC0 (add_nn _ _ hP0 hP0)
  -- Claim 1: G·(2Q+3) ≤ lo+lo.
  have hqm3 : (qpow Q mp * Q) = qpow Q m3 := congrArg (qpow Q) hmp.symm
  have hGQ : (G * Q).eqv C :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat m3) (qpow Q mp) Q)
      (Q'.eqv_of_eq (congrArg (fun z => Q'.ofNat m3 * z) hqm3))
  have hG2Q : (G * (Q'.ofNat 2 * Q)).eqv (C + C) :=
    Q'.eqv_trans _ _ _ (mulLC G (Q'.ofNat 2) Q)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ hGQ) (two_mul_eqvE C))
  have hG3 : (G * Q'.ofNat 3).eqv (Q'.ofNat (m3 * 3) * qpow Q mp) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat m3) (qpow Q mp) (Q'.ofNat 3)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat m3) _ _ (Q'.mul_comm_eqv (qpow Q mp) (Q'.ofNat 3))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat m3) (Q'.ofNat 3) (qpow Q mp))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv m3 3))
  have h4P : ((P + P) + (P + P)).eqv (Q'.ofNat (4 * mp) * qpow Q mp) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (two_mul_eqvE (P + P))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ (Q'.eqv_symm (two_mul_eqvE P))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) (Q'.ofNat 2) P)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ P (by decide : (Q'.ofNat 2 * Q'.ofNat 2).eqv (Q'.ofNat 4))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) (Q'.ofNat mp) (qpow Q mp))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv 4 mp))
  have hG3le : (G * Q'.ofNat 3) ≤ (P + P) + (P + P) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hG3)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.ofNat_le_ofNat (by omega : m3 * 3 ≤ 4 * mp)) hqmp0)
        (Q'.ge_of_eqv h4P))
  have hClaim1 : (G * s2) ≤ lo + lo := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_add_eqv G (Q'.ofNat 2 * Q) (Q'.ofNat 3))) ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add (Q'.le_of_eqv hG2Q) hG3le) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm (Q'.add_swap_inner C (P + P) C (P + P)))
  -- Claim 2: (G·s2)² ≤ (lo+lo)²
  have hGs20 : (0 : Q') ≤ G * s2 := Q'.mul_nonneg _ _ hG0 hs20
  have hlolo0 : (0 : Q') ≤ lo + lo := add_nn _ _ hlo0 hlo0
  have hClaim2 : (G * s2) * (G * s2) ≤ (lo + lo) * (lo + lo) :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hClaim1 hGs20)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hClaim1 hlolo0)
  -- collapse blocks
  have hGG : (G * G).eqv (Q'.ofNat (m3 * m3) * qpow Q (mp + mp)) :=
    Q'.eqv_trans _ _ _ (blkMul Q (Q'.ofNat m3) (Q'.ofNat m3) mp mp)
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv m3 m3)))
  have hGs2sq : ((G * s2) * (G * s2)).eqv
      ((Q'.ofNat (m3 * m3) * qpow Q (mp + mp)) * (s2 * s2)) :=
    Q'.eqv_trans _ _ _ (mul4comm G s2 G s2) (Q'.mul_eqv_congr_right _ _ _ hGG)
  have hB2B4 : ((Q'.ofNat m2 * qpow Q m2) * (Q'.ofNat m4 * qpow Q m4)).eqv
      (Q'.ofNat (m2 * m4) * qpow Q (m2 + m4)) :=
    Q'.eqv_trans _ _ _ (blkMul Q (Q'.ofNat m2) (Q'.ofNat m4) m2 m4)
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv m2 m4)))
  -- LHS ≤ (256·(mk·mk))·W'
  have hLHScollapse : (Q'.ofNat 256 *
        ((mk * (Q'.ofNat m2 * qpow Q m2)) * (mk * (Q'.ofNat m4 * qpow Q m4)))).eqv
      ((Q'.ofNat 256 * (mk * mk)) * (Q'.ofNat (m2 * m4) * qpow Q (m2 + m4))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 256) _ _
        (Q'.eqv_trans _ _ _
          (mul4comm mk (Q'.ofNat m2 * qpow Q m2) mk (Q'.ofNat m4 * qpow Q m4))
          (Q'.mul_eqv_congr_left (mk * mk) _ _ hB2B4))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 256) (mk * mk) _)
  have hVle : (Q'.ofNat (m2 * m4) * qpow Q (m2 + m4))
      ≤ Q'.ofNat (m3 * m3) * qpow Q (m3 + m3) := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_of_eq (by rw [hsum2] :
        Q'.ofNat (m2 * m4) * qpow Q (m2 + m4) = Q'.ofNat (m2 * m4) * qpow Q (m3 + m3)))) ?_
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.ofNat_le_ofNat hprodle) (qpow_nonneg Q hQ0 _)
  have hKL0 : (0 : Q') ≤ Q'.ofNat 256 * (mk * mk) :=
    Q'.mul_nonneg _ _ (ofNat_nonneg _)
      (Q'.mul_nonneg _ _ (by decide : (0:Q') ≤ Q'.mkPos 32 15 (by decide))
        (by decide : (0:Q') ≤ Q'.mkPos 32 15 (by decide)))
  have hLHSbound : (Q'.ofNat 256 *
        ((mk * (Q'.ofNat m2 * qpow Q m2)) * (mk * (Q'.ofNat m4 * qpow Q m4))))
      ≤ (Q'.ofNat 256 * (mk * mk)) * (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHScollapse)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hVle hKL0)
  -- W' ≃ U·Q²
  have hexp : m3 + m3 = (mp + mp) + 2 := by omega
  have hqe : (qpow Q (m3 + m3)).eqv (qpow Q (mp + mp) * qpow Q 2) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (congrArg (qpow Q) hexp)) (qpow_add Q (mp + mp) 2)
  have hW'U : (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3)).eqv
      ((Q'.ofNat (m3 * m3) * qpow Q (mp + mp)) * qpow Q 2) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat (m3 * m3)) _ _ hqe)
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (m3 * m3)) (qpow Q (mp + mp)) (qpow Q 2)))
  -- κL ≃ (256·(mk·mk)·Q²)·U  and  κR ≃ (225Q·s2²)·U ; reduce to odd_scalar_ge
  -- work with U := ofNat(m3*m3)·qpow(mp+mp)
  -- hLHS4 : 4·(KL·W') ≃ κL·U
  have hLHS4 : (Q'.ofNat 4 *
        ((Q'.ofNat 256 * (mk * mk)) * (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3)))).eqv
      ((Q'.ofNat 4 * ((Q'.ofNat 256 * (mk * mk)) * qpow Q 2))
        * (Q'.ofNat (m3 * m3) * qpow Q (mp + mp))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 256 * (mk * mk)) _ _ hW'U)) ?_
    -- 4·(KL·((U)·Q²)) ≃ (4·(KL·Q²))·U
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (Q'.ofNat 256 * (mk * mk)) _ _
            (Q'.mul_comm_eqv (Q'.ofNat (m3 * m3) * qpow Q (mp + mp)) (qpow Q 2)))
          (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 256 * (mk * mk)) (qpow Q 2)
            (Q'.ofNat (m3 * m3) * qpow Q (mp + mp)))))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) ((Q'.ofNat 256 * (mk * mk)) * qpow Q 2)
      (Q'.ofNat (m3 * m3) * qpow Q (mp + mp)))
  -- hRHSge : 225Q·(U·s2²) ≤ 4·(225Q·lo²)
  have hloAsTwo : ((lo + lo) * (lo + lo)).eqv (Q'.ofNat 4 * (lo * lo)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (lo + lo) (Q'.eqv_symm (two_mul_eqvE lo)))
        (Q'.mul_eqv_congr_left (Q'.ofNat 2 * lo) _ _ (Q'.eqv_symm (two_mul_eqvE lo)))) ?_
    refine Q'.eqv_trans _ _ _ (mul4comm (Q'.ofNat 2) lo (Q'.ofNat 2) lo) ?_
    exact Q'.mul_eqv_congr_right _ _ (lo * lo) (by decide : (Q'.ofNat 2 * Q'.ofNat 2).eqv (Q'.ofNat 4))
  have hRHSchain : ((Q'.ofNat 225 * Q) * ((Q'.ofNat (m3 * m3) * qpow Q (mp + mp)) * (s2 * s2)))
      ≤ Q'.ofNat 4 * ((Q'.ofNat 225 * Q) * (lo * lo)) := by
    -- 4·(225Q·lo²) ≃ 225Q·(4·lo²) ≃ 225Q·((lo+lo)²) ≥ 225Q·((G·s2)²) ≃ 225Q·(U·s2²)
    refine Q'.le_trans' _ _ _ ?_
      (Q'.ge_of_eqv (mulLC (Q'.ofNat 4) (Q'.ofNat 225 * Q) (lo * lo)))
    -- goal: 225Q·(U·s2²) ≤ 225Q·(4·(lo*lo))
    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ (Q'.mul_nonneg _ _ (ofNat_nonneg _) hQ0)
    -- U·s2² ≤ 4·(lo*lo)
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv hGs2sq) ?_
    refine Q'.le_trans' _ _ _ hClaim2 ?_
    exact Q'.le_of_eqv hloAsTwo
  -- κL ≤ κR
  have hκLκR : (Q'.ofNat 4 * ((Q'.ofNat 256 * (mk * mk)) * qpow Q 2))
      ≤ (Q'.ofNat 225 * Q) * (s2 * s2) := by
    -- κL ≃ mkPos1048576_225·(Q·Q) ≃ Q·(mkPos1048576_225·Q)
    have hκLe : (Q'.ofNat 4 * ((Q'.ofNat 256 * (mk * mk)) * qpow Q 2)).eqv
        (Q * (Q'.mkPos 1048576 225 (by decide) * Q)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) (Q'.ofNat 256 * (mk * mk)) (qpow Q 2))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (qpow Q 2)
          (by decide : (Q'.ofNat 4 * (Q'.ofNat 256 *
              (Q'.mkPos 32 15 (by decide) * Q'.mkPos 32 15 (by decide)))).eqv
              (Q'.mkPos 1048576 225 (by decide)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.mkPos 1048576 225 (by decide)) _ _ (qpow2_eq Q)) ?_
      exact mulLC (Q'.mkPos 1048576 225 (by decide)) Q Q
    have hκRe : ((Q'.ofNat 225 * Q) * (s2 * s2)).eqv
        (Q * (Q'.ofNat 225 * (s2 * s2))) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat 225) Q (s2 * s2)) ?_
      exact mulLC (Q'.ofNat 225) Q (s2 * s2)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hκLe) (Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hκRe))
    -- Q·(mkPos·Q) ≤ Q·(225·s2²)
    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hQ0
    -- mkPos1048576_225·Q ≤ 225·s2²  (cancel 225)
    refine le_of_mul_le_mul_rightL (c := Q'.ofNat 225) ?_ (by decide)
    -- (mkPos·Q)·225 ≤ (225·s2²)·225 ; both sides collapse, reduce to odd_scalar_ge
    have hLeq : ((Q'.mkPos 1048576 225 (by decide) * Q) * Q'.ofNat 225).eqv
        (Q'.ofNat 1048576 * Q) :=
      Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.mkPos 1048576 225 (by decide)) Q (Q'.ofNat 225))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left (Q'.mkPos 1048576 225 (by decide)) _ _
            (Q'.mul_comm_eqv Q (Q'.ofNat 225)))
          (Q'.eqv_trans _ _ _
            (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.mkPos 1048576 225 (by decide)) (Q'.ofNat 225) Q))
            (Q'.mul_eqv_congr_right _ _ Q
              (by decide : (Q'.mkPos 1048576 225 (by decide) * Q'.ofNat 225).eqv (Q'.ofNat 1048576)))))
    have hReq : ((Q'.ofNat 225 * (s2 * s2)) * Q'.ofNat 225).eqv
        (Q'.ofNat 50625 * (s2 * s2)) :=
      Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.ofNat 225 * (s2 * s2)) (Q'.ofNat 225))
        (Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 225) (Q'.ofNat 225) (s2 * s2)))
          (Q'.mul_eqv_congr_right _ _ (s2 * s2)
            (by decide : (Q'.ofNat 225 * Q'.ofNat 225).eqv (Q'.ofNat 50625))))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLeq)
      (Q'.le_trans' _ _ _ (odd_scalar_ge hQ4) (Q'.ge_of_eqv hReq))
  -- assemble
  have hStep2 : (Q'.ofNat 256 * (mk * mk)) * (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3))
      ≤ (Q'.ofNat 225 * Q) * (lo * lo) := by
    have hU0 : (0 : Q') ≤ Q'.ofNat (m3 * m3) * qpow Q (mp + mp) :=
      Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ0 _)
    have h4 : Q'.ofNat 4 *
          ((Q'.ofNat 256 * (mk * mk)) * (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3)))
        ≤ Q'.ofNat 4 * ((Q'.ofNat 225 * Q) * (lo * lo)) := by
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS4) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hκLκR hU0) ?_
      -- (κR)·U ≃ 225Q·(U·s2²) ≤ 4·(225Q·lo²)
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hRHSchain
      -- (225Q·s2²)·U ≃ 225Q·(U·s2²)
      refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat 225 * Q) (s2 * s2)
        (Q'.ofNat (m3 * m3) * qpow Q (mp + mp))) ?_
      exact Q'.mul_eqv_congr_left (Q'.ofNat 225 * Q) _ _
        (Q'.mul_comm_eqv (s2 * s2) (Q'.ofNat (m3 * m3) * qpow Q (mp + mp)))
    exact Q'.le_of_mul_le_mul_left h4 (by decide)
  exact Q'.le_trans' _ _ _ hLHSbound hStep2

/-- Generic clean-constant upper-bound closure: from a geometric leg `u·den ≤ B·R`, a scalar
comparison `R ≤ c·den` (`den > 0`, `B ≥ 0`), conclude `u ≤ c·B`. -/
private theorem upper_clean {u B R c den : Q'} (hden : (0 : Q') < den) (hB : (0 : Q') ≤ B)
    (hleg : u * den ≤ B * R) (hRc : R ≤ c * den) : u ≤ c * B := by
  have h1 : B * R ≤ B * (c * den) := Q'.mul_le_mul_of_nonneg_left _ _ _ hRc hB
  have h2 : (B * (c * den)).eqv ((c * B) * den) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv B c den))
      (Q'.mul_eqv_congr_right _ _ den (Q'.mul_comm_eqv B c))
  exact le_of_mul_le_mul_rightL
    (Q'.le_trans' _ _ _ hleg (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h2))) hden

/-- Even scalar upper: `(Q+1) ≤ (5/3)·(Q−1)` for `Q ≥ 4`. -/
theorem qp1_le_scaled {Q : Q'} (hQ4 : (Q'.ofNat 4) ≤ Q) :
    (Q + 1) ≤ Q'.mkPos 5 3 (by decide) * (Q + -(1 : Q')) := by
  refine le_of_mul_le_mul_rightL (c := Q'.ofNat 3) ?_ (by decide)
  have hR : ((Q'.mkPos 5 3 (by decide) * (Q + -(1 : Q'))) * Q'.ofNat 3).eqv
      (Q'.ofNat 5 * (Q + -(1 : Q'))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.mkPos 5 3 (by decide)) (Q + -(1 : Q')) (Q'.ofNat 3)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (Q + -(1 : Q')) (Q'.ofNat 3))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.mkPos 5 3 (by decide)) (Q'.ofNat 3) (Q + -(1 : Q')))) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (by decide : (Q'.mkPos 5 3 (by decide) * Q'.ofNat 3).eqv (Q'.ofNat 5))
  have hL : ((Q + 1) * Q'.ofNat 3).eqv (Q'.ofNat 3 * Q + Q'.ofNat 3) :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q + 1) (Q'.ofNat 3))
      (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat 3) Q 1)
        (Q'.add_eqv_congr_left _ _ _ (Q'.mul_one_eqv (Q'.ofNat 3))))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) (Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hR))
  -- ofNat3·Q + ofNat3 ≤ ofNat5·(Q+-1)
  have hExp : (Q'.ofNat 5 * (Q + -(1 : Q'))).eqv
      (Q'.ofNat 3 * Q + (Q'.ofNat 2 * Q + -(Q'.ofNat 5))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat 5) Q (-(1 : Q'))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (Q'.ofNat 5 * Q) _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (Q'.ofNat 5) 1)
          (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv (Q'.ofNat 5))))) ?_
    have h5split : (Q'.ofNat 5 * Q).eqv (Q'.ofNat 3 * Q + Q'.ofNat 2 * Q) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ Q (by decide : (Q'.ofNat 5).eqv (Q'.ofNat 3 + Q'.ofNat 2)))
        (Q'.add_mul_eqv (Q'.ofNat 3) (Q'.ofNat 2) Q)
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-(Q'.ofNat 5)) h5split)
      (Q'.add_assoc_eqv (Q'.ofNat 3 * Q) (Q'.ofNat 2 * Q) (-(Q'.ofNat 5)))
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hExp)
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add_left (Q'.ofNat 3 * Q) (Q'.ofNat 3) (Q'.ofNat 2 * Q + -(Q'.ofNat 5)) ?_)
    (Q'.le_refl' _)
  -- ofNat3 ≤ ofNat2·Q + -(ofNat5)
  have h8 : (Q'.ofNat 8) ≤ Q'.ofNat 2 * Q :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (Q'.ofNat 8).eqv (Q'.ofNat 2 * Q'.ofNat 4)))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hQ4 (by decide))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by decide : (Q'.ofNat 3).eqv (Q'.ofNat 8 + -(Q'.ofNat 5)))) ?_
  exact Q'.add_le_add_right _ _ _ h8

/-- Odd scalar upper: `2Q² ≤ (32/15)·(Q²−1)` for `Q ≥ 4`. -/
theorem q2_le_scaled {Q : Q'} (hQ4 : (Q'.ofNat 4) ≤ Q) :
    Q'.ofNat 2 * qpow Q 2 ≤ Q'.mkPos 32 15 (by decide) * (qpow Q 2 + -(1 : Q')) := by
  refine le_of_mul_le_mul_rightL (c := Q'.ofNat 15) ?_ (by decide)
  have hR : ((Q'.mkPos 32 15 (by decide) * (qpow Q 2 + -(1 : Q'))) * Q'.ofNat 15).eqv
      (Q'.ofNat 32 * (qpow Q 2 + -(1 : Q'))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.mkPos 32 15 (by decide)) (qpow Q 2 + -(1 : Q')) (Q'.ofNat 15)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (qpow Q 2 + -(1 : Q')) (Q'.ofNat 15))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.mkPos 32 15 (by decide)) (Q'.ofNat 15) (qpow Q 2 + -(1 : Q')))) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (by decide : (Q'.mkPos 32 15 (by decide) * Q'.ofNat 15).eqv (Q'.ofNat 32))
  have hL : ((Q'.ofNat 2 * qpow Q 2) * Q'.ofNat 15).eqv (Q'.ofNat 30 * qpow Q 2) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.ofNat 2 * qpow Q 2) (Q'.ofNat 15)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 15) (Q'.ofNat 2) (qpow Q 2))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide : (Q'.ofNat 15 * Q'.ofNat 2).eqv (Q'.ofNat 30))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) (Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hR))
  -- ofNat30·X ≤ ofNat32·(X+-1)
  have hExp : (Q'.ofNat 32 * (qpow Q 2 + -(1 : Q'))).eqv
      (Q'.ofNat 30 * qpow Q 2 + (Q'.ofNat 2 * qpow Q 2 + -(Q'.ofNat 32))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat 32) (qpow Q 2) (-(1 : Q'))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left (Q'.ofNat 32 * qpow Q 2) _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (Q'.ofNat 32) 1)
          (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv (Q'.ofNat 32))))) ?_
    have h32split : (Q'.ofNat 32 * qpow Q 2).eqv (Q'.ofNat 30 * qpow Q 2 + Q'.ofNat 2 * qpow Q 2) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (qpow Q 2) (by decide : (Q'.ofNat 32).eqv (Q'.ofNat 30 + Q'.ofNat 2)))
        (Q'.add_mul_eqv (Q'.ofNat 30) (Q'.ofNat 2) (qpow Q 2))
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (-(Q'.ofNat 32)) h32split)
      (Q'.add_assoc_eqv (Q'.ofNat 30 * qpow Q 2) (Q'.ofNat 2 * qpow Q 2) (-(Q'.ofNat 32)))
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hExp)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (Q'.ofNat 30 * qpow Q 2))))) ?_
  refine Q'.add_le_add_left (Q'.ofNat 30 * qpow Q 2) (0 : Q') (Q'.ofNat 2 * qpow Q 2 + -(Q'.ofNat 32)) ?_
  -- 0 ≤ ofNat2·X + -(ofNat32)
  have h32 : (Q'.ofNat 32) ≤ Q'.ofNat 2 * qpow Q 2 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (Q'.ofNat 32).eqv (Q'.ofNat 2 * Q'.ofNat 16)))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow2_ge16 hQ4) (by decide))
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by decide : (0 : Q').eqv (Q'.ofNat 32 + -(Q'.ofNat 32)))) ?_
  exact Q'.add_le_add_right _ _ _ h32

/-! ## 7. The parity-dispatched envelope fields and `utleEnvelope`. -/

/-- The lower-bound field: two central terms (even `s`) / central + first pair (odd `s`). -/
def loFn (Q : Q') (s : Nat) : Q' :=
  if s % 2 = 0 then
    Q'.ofNat ((s/2 + 1) * (s/2 + 2)) * qpow Q ((s/2 + 1) * (s/2 + 2))
      + Q'.ofNat ((s/2 + 1) * (s/2 + 2)) * qpow Q ((s/2 + 1) * (s/2 + 2))
  else
    Q'.ofNat ((s/2 + 2) * (s/2 + 2)) * qpow Q ((s/2 + 2) * (s/2 + 2))
      + (Q'.ofNat ((s/2 + 1) * (s/2 + 3)) * qpow Q ((s/2 + 1) * (s/2 + 3))
         + Q'.ofNat ((s/2 + 1) * (s/2 + 3)) * qpow Q ((s/2 + 1) * (s/2 + 3)))

/-- The `U(s+2)` upper-envelope field (clean rational constant on the peak block). -/
def hi2Fn (Q : Q') (s : Nat) : Q' :=
  if s % 2 = 0 then
    Q'.mkPos 5 3 (by decide) * (Q'.ofNat ((s/2 + 1) * (s/2 + 1)) * qpow Q ((s/2 + 1) * (s/2 + 1)))
  else
    Q'.mkPos 32 15 (by decide) * (Q'.ofNat ((s/2 + 1) * (s/2 + 2)) * qpow Q ((s/2 + 1) * (s/2 + 2)))

/-- The `U(s+4)` upper-envelope field. -/
def hi4Fn (Q : Q') (s : Nat) : Q' :=
  if s % 2 = 0 then
    Q'.mkPos 5 3 (by decide) * (Q'.ofNat ((s/2 + 2) * (s/2 + 2)) * qpow Q ((s/2 + 2) * (s/2 + 2)))
  else
    Q'.mkPos 32 15 (by decide) * (Q'.ofNat ((s/2 + 2) * (s/2 + 3)) * qpow Q ((s/2 + 2) * (s/2 + 3)))

theorem loFn_even (Q : Q') (t : Nat) :
    loFn Q (2 * t) =
      Q'.ofNat ((t + 1) * (t + 2)) * qpow Q ((t + 1) * (t + 2))
        + Q'.ofNat ((t + 1) * (t + 2)) * qpow Q ((t + 1) * (t + 2)) := by
  unfold loFn; rw [if_pos (by omega : (2 * t) % 2 = 0), (by omega : (2 * t) / 2 = t)]

theorem loFn_odd (Q : Q') (t : Nat) :
    loFn Q (2 * t + 1) =
      Q'.ofNat ((t + 2) * (t + 2)) * qpow Q ((t + 2) * (t + 2))
        + (Q'.ofNat ((t + 1) * (t + 3)) * qpow Q ((t + 1) * (t + 3))
           + Q'.ofNat ((t + 1) * (t + 3)) * qpow Q ((t + 1) * (t + 3))) := by
  unfold loFn; rw [if_neg (by omega : ¬ (2 * t + 1) % 2 = 0), (by omega : (2 * t + 1) / 2 = t)]

theorem hi2Fn_even (Q : Q') (t : Nat) :
    hi2Fn Q (2 * t) =
      Q'.mkPos 5 3 (by decide) * (Q'.ofNat ((t + 1) * (t + 1)) * qpow Q ((t + 1) * (t + 1))) := by
  unfold hi2Fn; rw [if_pos (by omega : (2 * t) % 2 = 0), (by omega : (2 * t) / 2 = t)]

theorem hi2Fn_odd (Q : Q') (t : Nat) :
    hi2Fn Q (2 * t + 1) =
      Q'.mkPos 32 15 (by decide) * (Q'.ofNat ((t + 1) * (t + 2)) * qpow Q ((t + 1) * (t + 2))) := by
  unfold hi2Fn; rw [if_neg (by omega : ¬ (2 * t + 1) % 2 = 0), (by omega : (2 * t + 1) / 2 = t)]

theorem hi4Fn_even (Q : Q') (t : Nat) :
    hi4Fn Q (2 * t) =
      Q'.mkPos 5 3 (by decide) * (Q'.ofNat ((t + 2) * (t + 2)) * qpow Q ((t + 2) * (t + 2))) := by
  unfold hi4Fn; rw [if_pos (by omega : (2 * t) % 2 = 0), (by omega : (2 * t) / 2 = t)]

theorem hi4Fn_odd (Q : Q') (t : Nat) :
    hi4Fn Q (2 * t + 1) =
      Q'.mkPos 32 15 (by decide) * (Q'.ofNat ((t + 2) * (t + 3)) * qpow Q ((t + 2) * (t + 3))) := by
  unfold hi4Fn; rw [if_neg (by omega : ¬ (2 * t + 1) % 2 = 0), (by omega : (2 * t + 1) / 2 = t)]

/-- **`utleEnvelope` — the `UTuranEnvelope Q` witness for `Q ≥ 4`.**  Inhabits the reduction
interface from the four PROVED legs + the two reduced scalar closures.  Via
`FusionUTuranWFree.uturan_of_envelope` this discharges the w-free coupling Turán `(‡′)`
UNCONDITIONALLY in `s`. -/
theorem utle_lo_nonneg {Q : Q'} (hQ4 : (4 : Q') ≤ Q) (s : Nat) : (0 : Q') ≤ loFn Q s := by
  rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
    rw [loFn_even]
    exact add_nn _ _
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q (zero_le_of_four_le hQ4) _))
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q (zero_le_of_four_le hQ4) _))
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
    rw [loFn_odd]
    exact add_nn _ _
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q (zero_le_of_four_le hQ4) _))
      (add_nn _ _
        (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q (zero_le_of_four_le hQ4) _))
        (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q (zero_le_of_four_le hQ4) _)))

theorem utle_hi2_nonneg {Q : Q'} (hQ4 : (4 : Q') ≤ Q) (s : Nat) : (0 : Q') ≤ hi2Fn Q s := by
  rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
    rw [hi2Fn_even]
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q (zero_le_of_four_le hQ4) _))
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
    rw [hi2Fn_odd]
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q (zero_le_of_four_le hQ4) _))

theorem utle_hi4_nonneg {Q : Q'} (hQ4 : (4 : Q') ≤ Q) (s : Nat) : (0 : Q') ≤ hi4Fn Q s := by
  rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
    rw [hi4Fn_even]
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q (zero_le_of_four_le hQ4) _))
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
    rw [hi4Fn_odd]
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q (zero_le_of_four_le hQ4) _))

theorem utle_lower {Q : Q'} (hQ4 : (4 : Q') ≤ Q) (s : Nat) : loFn Q s ≤ Ucoup Q (s + 3) := by
  rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
    rw [loFn_even]
    exact Ucoup_lower_even (zero_le_of_four_le hQ4) t
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
    rw [loFn_odd]
    exact Ucoup_lower_odd (zero_le_of_four_le hQ4) t

set_option maxHeartbeats 1000000 in
theorem utle_upper2 {Q : Q'} (hQ4 : (4 : Q') ≤ Q) (s : Nat) : Ucoup Q (s + 2) ≤ hi2Fn Q s := by
  rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
    rw [hi2Fn_even, (by omega : 2 * t + 2 = 2 * (t + 1))]
    exact upper_clean (sub1_pos hQ4)
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q (zero_le_of_four_le hQ4) _))
      (Ucoup_upper_even (one_le_of_four_le hQ4) (by omega : 1 ≤ t + 1)) (qp1_le_scaled hQ4)
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
    rw [hi2Fn_odd, (by omega : 2 * t + 1 + 2 = 2 * (t + 1) + 1)]
    exact upper_clean (sub1_pos2 hQ4)
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q (zero_le_of_four_le hQ4) _))
      (Ucoup_upper_odd (one_le_of_four_le hQ4) (by omega : 1 ≤ t + 1)) (q2_le_scaled hQ4)

set_option maxHeartbeats 1000000 in
theorem utle_upper4 {Q : Q'} (hQ4 : (4 : Q') ≤ Q) (s : Nat) : Ucoup Q (s + 4) ≤ hi4Fn Q s := by
  rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
    rw [hi4Fn_even, (by omega : 2 * t + 4 = 2 * (t + 2))]
    exact upper_clean (sub1_pos hQ4)
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q (zero_le_of_four_le hQ4) _))
      (Ucoup_upper_even (one_le_of_four_le hQ4) (by omega : 1 ≤ t + 2)) (qp1_le_scaled hQ4)
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
    rw [hi4Fn_odd, (by omega : 2 * t + 1 + 4 = 2 * (t + 2) + 1)]
    exact upper_clean (sub1_pos2 hQ4)
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q (zero_le_of_four_le hQ4) _))
      (Ucoup_upper_odd (one_le_of_four_le hQ4) (by omega : 1 ≤ t + 2)) (q2_le_scaled hQ4)

set_option maxHeartbeats 1000000 in
theorem utle_reduced {Q : Q'} (hQ4 : (4 : Q') ≤ Q) (s : Nat) :
    Q'.ofNat 256 * (hi2Fn Q s * hi4Fn Q s)
      ≤ (Q'.ofNat 225 * Q) * (loFn Q s * loFn Q s) := by
  rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
    rw [hi2Fn_even, hi4Fn_even, loFn_even]
    exact even_reduced_alg (zero_le_of_four_le hQ4) ((t + 1) * (t + 1)) ((t + 1) * (t + 2))
      ((t + 2) * (t + 2)) (even_exp_prod t) (by have := even_exp_sum t; omega)
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
    rw [hi2Fn_odd, hi4Fn_odd, loFn_odd]
    exact odd_reduced_alg hQ4 ((t + 1) * (t + 2)) ((t + 2) * (t + 2)) ((t + 2) * (t + 3))
      ((t + 1) * (t + 3))
      (by have := odd_exp_sum t; omega) (odd_exp_prodge t)
      (by have h1 := expand t 2 2; have h2 := expand t 1 3; omega)
      (by have h1 := expand t 2 2; have h2 := expand t 1 3; omega)

/-- **`utleEnvelope` — the `UTuranEnvelope Q` witness for `Q ≥ 4`.**  Inhabits the reduction
interface from the four PROVED legs + the two reduced scalar closures. -/
def utleEnvelope {Q : Q'} (hQ4 : (4 : Q') ≤ Q) : UTuranEnvelope Q where
  lo := loFn Q
  hi2 := hi2Fn Q
  hi4 := hi4Fn Q
  Q_nonneg := zero_le_of_four_le hQ4
  lo_nonneg := utle_lo_nonneg hQ4
  hi2_nonneg := utle_hi2_nonneg hQ4
  hi4_nonneg := utle_hi4_nonneg hQ4
  lower := utle_lower hQ4
  upper2 := utle_upper2 hQ4
  upper4 := utle_upper4 hQ4
  reduced := utle_reduced hQ4

/-- **`uturan_unconditional` — the w-free coupling Turán `(‡′)`, UNCONDITIONAL in `s`, for
`Q ≥ 4`.**  `256·U(s+2)·U(s+4) ≤ 225·Q·U(s+3)²`, obtained by feeding `utleEnvelope` (the four
PROVED legs + reduced closures) into `FusionUTuranWFree.uturan_of_envelope`. -/
theorem uturan_unconditional {Q : Q'} (hQ4 : (4 : Q') ≤ Q) (s : Nat) :
    Q'.ofNat 256 * (Ucoup Q (s + 2) * Ucoup Q (s + 4))
      ≤ (Q'.ofNat 225 * Q) * (Ucoup Q (s + 3) * Ucoup Q (s + 3)) :=
  uturan_of_envelope (utleEnvelope hQ4) s

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms utleEnvelope
#print axioms uturan_unconditional

#print axioms one_add_pred
#print axioms geomTelescope
#print axioms geomTail_le
#print axioms Ucoup_lower_even
#print axioms Ucoup_lower_odd
#print axioms qpow_exp_mono
#print axioms geomAsc_le
#print axioms geomDesc_le
#print axioms geomAsc2_le
#print axioms geomDesc2_le
#print axioms Ucoup_upper_even
#print axioms Ucoup_upper_odd

end YMGap.Continuum.FusionUTuranEnvelope
