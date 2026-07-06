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

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

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
