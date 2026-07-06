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

namespace YMGap.Continuum.FusionUTuranEnvelope

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionUTuranWFree

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

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms one_add_pred
#print axioms geomTelescope
#print axioms geomTail_le
#print axioms Ucoup_lower_even
#print axioms Ucoup_lower_odd

end YMGap.Continuum.FusionUTuranEnvelope
