/-
Track A / R2 — the `Q' = 1/w²` INVERSE REINDEXING carrying the truncated coupling Turán
`(‡_trunc)` (in `Q`) to the fusion-box reserve `(†)` (in `w`), and INHABITING
`AutoconvGershgorin.SymMinorGershgorin w` for general strong coupling `0 < w ≤ 1/2`.

# The reindexing (read `docs/reindexing-correction-2026-07-06.md`)

With `Q = 1/w²` (the positive reciprocal `Q'.divPos 1 (qpow w 2) _`) and `f(S) = c4 S + 2(S+1)`,
the range-`(s+1)` central autoconvolution factorizes EXACTLY as

    acN w (s+1) S  ≃  w^{f(S)} · Wtrunc(Q, s, S)                                  (`acN_reindex`)

via the per-antidiagonal Gaussian split `coeffW w p · coeffW w (S−p) ≃ w^{f(S)} · wterm Q (S+2)(p+1)`
(the shift `i = p+1`), whose exponent is the pure-`Nat` Casimir identity
`(c4 p + c4(S−p)) + 2·(p+1)(S−p+1) = f(S)` (`fexp_identity`, from `c4_antidiag`), and the
`Q'`-positive-inverse power law `(w²)^C · Q^C ≃ 1` (`powInv`, from `qpow w 2 · Q ≃ 1`).

Dividing the reserve `(†)` by the common Gaussian `w^{2 f(s+1)}` (exponent identity
`f(s)+f(s+2) = 2 f(s+1)+2`) leaves the residual `w² = 1/Q`, so `(†) ⟺ (‡_trunc)`; the reserve
constant `256/225` is exactly what the truncated Turán clears (margin ≈ 1.75).

# What is PROVED here (axiom-clean)

  * `fexp_identity`, `fExp_sum` — the pure-`Nat` Casimir exponent identities.
  * `powInv` — the `Q'`-positive-inverse power law `(w²)^C · Q^C ≃ 1`.
  * `qpow_reindex`, `coeff_reindex`, `Wtrunc_shift`, `acN_reindex` — the exact `acN ↔ Wtrunc` bridge.
  * `crossN` — the reserve `(†)` `256·acN(s+1,s)·acN(s+1,s+2) ≤ 225·acN(s+1,s+1)²` for `0<w≤1/2`,
    from `(‡_trunc)` through the reindexing.
  * `reserveOfTrunc` — `LeakGeoDecay.AcNDefectReserve w` (via `reserve_of_cross`).
  * `symMinorGershgorin_of_trunc` — **`AutoconvGershgorin.SymMinorGershgorin w` INHABITED** for
    every `0 < w ≤ 1/2`, via `LeakGeoDecay.gershgorinOfReserve`.

# HONESTY

`SymMinorGershgorin` is a fusion-box log-concavity NODE, NOT one of the guarded Clay-frontier
bundles (`YMGapGuard` must still report all five uninhabited).  This closes the general-`w`
strong-coupling reserve residual (previously reduced to `FiniteSMarginWorstcase`) via the
truncated coupling Turán; it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `qpow`/`fsum`/`divPos` API, `c4_antidiag`/`c4_sum_symm`, the
PROVED `(‡_trunc)` (`FusionUTuranTrunc.uturan_trunc_unconditional`), and `omega`.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is `propext`/`Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.FusionUTuranTrunc
import YMGap.Continuum.AcNReserveAnalytic
import YMGap.Continuum.LeakGeoDecay
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.FusionUTuranReindex

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.FusionUTuranWFree
open YMGap.Continuum.FusionUTuranTrunc
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.AutoconvGershgorin

/-! ## 0. Local `Q'` rearrangement helpers -/

private theorem mul4 (a b c d : Q') : ((a * b) * (c * d)).eqv ((a * c) * (b * d)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

private theorem mulLC (a b c : Q') : (a * (b * c)).eqv (b * (a * c)) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

private theorem blk (Q : Q') (a b i j : Nat) :
    ((Q'.ofNat a * qpow Q i) * (Q'.ofNat b * qpow Q j)).eqv
      (Q'.ofNat (a * b) * qpow Q (i + j)) := by
  refine Q'.eqv_trans _ _ _ (mul4 (Q'.ofNat a) (qpow Q i) (Q'.ofNat b) (qpow Q j)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv a b))) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (qpow_add Q i j))

/-- The index-0 term of `wterm` vanishes. -/
private theorem wt0 (Q : Q') (m : Nat) : (wterm Q m 0).eqv 0 := by
  show (Q'.ofNat (0 * (m - 0)) * qpow Q (0 * (m - 0))).eqv 0
  have h : 0 * (m - 0) = 0 := by omega
  rw [h]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (qpow Q 0) (by decide : (Q'.ofNat 0).eqv 0))
    (q_zero_mul (qpow Q 0))

/-! ## 1. The pure-`Nat` Casimir exponent identities -/

/-- `f(S) = c4 S + 2(S+1)` — the Gaussian exponent stripped by the reindexing. -/
def fExp (S : Nat) : Nat := c4 S + 2 * (S + 1)

/-- **`fexp_identity`** — the per-antidiagonal exponent identity (from `c4_antidiag`):
`(c4 p + c4(S−p)) + 2·(p+1)(S−p+1) = f(S)` for `p ≤ S`. -/
theorem fexp_identity (S p : Nat) (hp : p ≤ S) :
    (c4 p + c4 (S - p)) + 2 * ((p + 1) * ((S - p) + 1)) = fExp S := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hp
  have hsp : (p + d) - p = d := by omega
  rw [hsp]
  unfold fExp c4
  have ha : p * (p + 2) = p * p + p * 2 := Nat.mul_add p p 2
  have hb : d * (d + 2) = d * d + d * 2 := Nat.mul_add d d 2
  have hc1 : (p + 1) * (d + 1) = p * (d + 1) + 1 * (d + 1) := Nat.add_mul p 1 (d + 1)
  have hc2 : p * (d + 1) = p * d + p * 1 := Nat.mul_add p d 1
  have hd : (p + d) * ((p + d) + 2) = (p + d) * (p + d) + (p + d) * 2 :=
    Nat.mul_add (p + d) (p + d) 2
  have he := expand p d d
  have hcomm : d * p = p * d := Nat.mul_comm d p
  omega

/-- **`fExp_sum`** — `f(s) + f(s+2) = 2·f(s+1) + 2` (the reserve's Gaussian second difference). -/
theorem fExp_sum (s : Nat) : fExp s + fExp (s + 2) = 2 * fExp (s + 1) + 2 := by
  unfold fExp c4
  have a0 : s * (s + 2) = s * s + s * 2 := Nat.mul_add s s 2
  have a1 : (s + 2) * ((s + 2) + 2) = (s + 2) * (s + 2) + (s + 2) * 2 :=
    Nat.mul_add (s + 2) (s + 2) 2
  have a1' := expand s 2 2
  have a2 : (s + 1) * ((s + 1) + 2) = (s + 1) * (s + 1) + (s + 1) * 2 :=
    Nat.mul_add (s + 1) (s + 1) 2
  have a2' := expand s 1 1
  omega

/-! ## 2. The `Q'`-positive-inverse power law -/

/-- **`powInv`** — from the reciprocal atom `w²·Q ≃ 1`, the `C`-th power law `(w²)^C · Q^C ≃ 1`.
Induction on `C` (each step peels one `w²·Q ≃ 1`). -/
theorem powInv {w Q : Q'} (hatom : (qpow w 2 * Q).eqv 1) :
    ∀ C, (qpow (qpow w 2) C * qpow Q C).eqv 1
  | 0 => by
      show ((1 : Q') * 1).eqv 1
      exact Q'.mul_one_eqv 1
  | C + 1 => by
      show ((qpow (qpow w 2) C * qpow w 2) * (qpow Q C * Q)).eqv 1
      refine Q'.eqv_trans _ _ _
        (mul4 (qpow (qpow w 2) C) (qpow w 2) (qpow Q C) Q) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (qpow w 2 * Q) (powInv hatom C)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (1 : Q') _ _ hatom) ?_
      exact Q'.mul_one_eqv 1

/-! ## 3. The exact `acN ↔ Wtrunc` reindexing bridge -/

/-- **`qpow_reindex`** — `w^{c4 p + c4(S−p)} ≃ w^{f(S)} · Q^C`, `C = (p+1)(S−p+1)`, for `p ≤ S`. -/
theorem qpow_reindex {w Q : Q'} (hatom : (qpow w 2 * Q).eqv 1) (S p : Nat) (hp : p ≤ S) :
    (qpow w (c4 p + c4 (S - p))).eqv
      (qpow w (fExp S) * qpow Q ((p + 1) * ((S - p) + 1))) := by
  have hid : (c4 p + c4 (S - p)) + 2 * ((p + 1) * ((S - p) + 1)) = fExp S := fexp_identity S p hp
  have hfS : (qpow w (fExp S)).eqv
      (qpow w (c4 p + c4 (S - p)) * qpow (qpow w 2) ((p + 1) * ((S - p) + 1))) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (congrArg (qpow w) hid.symm)) ?_
    refine Q'.eqv_trans _ _ _
      (qpow_add w (c4 p + c4 (S - p)) (2 * ((p + 1) * ((S - p) + 1)))) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm (qpow_qpow w 2 ((p + 1) * ((S - p) + 1))))
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (qpow Q ((p + 1) * ((S - p) + 1))) hfS) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (qpow w (c4 p + c4 (S - p))) (qpow (qpow w 2) ((p + 1) * ((S - p) + 1)))
      (qpow Q ((p + 1) * ((S - p) + 1)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (powInv hatom ((p + 1) * ((S - p) + 1)))) ?_
  exact Q'.mul_one_eqv (qpow w (c4 p + c4 (S - p)))

/-- **`coeff_reindex`** — the per-antidiagonal bridge
`coeffW w p · coeffW w (S−p) ≃ w^{f(S)} · wterm Q (S+2)(p+1)`, for `p ≤ S`. -/
theorem coeff_reindex {w Q : Q'} (hatom : (qpow w 2 * Q).eqv 1) (S p : Nat) (hp : p ≤ S) :
    (coeffW w p * coeffW w (S - p)).eqv (qpow w (fExp S) * wterm Q (S + 2) (p + 1)) := by
  have e1 : (coeffW w p * coeffW w (S - p)).eqv
      (Q'.ofNat ((p + 1) * ((S - p) + 1)) * qpow w (c4 p + c4 (S - p))) := by
    show ((Q'.ofNat (p + 1) * qpow w (c4 p)) * (Q'.ofNat ((S - p) + 1) * qpow w (c4 (S - p)))).eqv _
    exact blk w (p + 1) ((S - p) + 1) (c4 p) (c4 (S - p))
  have e2 := qpow_reindex hatom S p hp
  have hwt : wterm Q (S + 2) (p + 1)
      = Q'.ofNat ((p + 1) * ((S - p) + 1)) * qpow Q ((p + 1) * ((S - p) + 1)) := by
    unfold wterm
    have he : (p + 1) * (S + 2 - (p + 1)) = (p + 1) * ((S - p) + 1) := by
      have : S + 2 - (p + 1) = (S - p) + 1 := by omega
      rw [this]
    rw [he]
  rw [hwt]
  refine Q'.eqv_trans _ _ _ e1 ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ e2) ?_
  exact mulLC (Q'.ofNat ((p + 1) * ((S - p) + 1))) (qpow w (fExp S))
    (qpow Q ((p + 1) * ((S - p) + 1)))

/-- **`Wtrunc_shift`** — `Wtrunc(Q,s,S) ≃ Σ_{p<s+1} wterm Q (S+2)(p+1)` (the `i=0` term vanishes). -/
theorem Wtrunc_shift (Q : Q') (s S : Nat) :
    (Wtrunc Q s S).eqv (fsum (fun p => wterm Q (S + 2) (p + 1)) (s + 1)) := by
  show (fsum (wterm Q (S + 2)) (s + 2)).eqv (fsum (fun p => wterm Q (S + 2) (p + 1)) (s + 1))
  have h12 : 1 + (s + 1) = s + 2 := by omega
  have hsplit := FusionCoreStepRoundH.fsum_split_at (wterm Q (S + 2)) 1 (s + 1)
  rw [h12] at hsplit
  refine Q'.eqv_trans _ _ _ hsplit ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (fsum (fun r => wterm Q (S + 2) (1 + r)) (s + 1))
      (show (fsum (wterm Q (S + 2)) 1).eqv 0 from
        Q'.eqv_trans _ _ _ (q_zero_add_eqv (wterm Q (S + 2) 0)) (wt0 Q (S + 2)))) ?_
  refine Q'.eqv_trans _ _ _ (q_zero_add_eqv _) ?_
  exact fsum_eqv_congr (fun r => wterm Q (S + 2) (1 + r)) (fun p => wterm Q (S + 2) (p + 1))
    (fun i => Q'.eqv_of_eq (congrArg (wterm Q (S + 2)) (by omega : 1 + i = i + 1))) (s + 1)

/-- **`acN_reindex`** — the full bridge `acN w (s+1) S ≃ w^{f(S)} · Wtrunc(Q,s,S)`, for `s ≤ S`. -/
theorem acN_reindex {w Q : Q'} (hatom : (qpow w 2 * Q).eqv 1) (s S : Nat) (hsS : s ≤ S) :
    (acN w (s + 1) S).eqv (qpow w (fExp S) * Wtrunc Q s S) := by
  show (fsum (fun p => coeffW w p * coeffW w (S - p)) (s + 1)).eqv
      (qpow w (fExp S) * Wtrunc Q s S)
  have hterm : (fsum (fun p => coeffW w p * coeffW w (S - p)) (s + 1)).eqv
      (fsum (fun p => qpow w (fExp S) * wterm Q (S + 2) (p + 1)) (s + 1)) :=
    fsum_eqv_congr_lt _ _ (s + 1) (fun p hp => coeff_reindex hatom S p (by omega))
  refine Q'.eqv_trans _ _ _ hterm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (fsum_const_mul (qpow w (fExp S)) (fun p => wterm Q (S + 2) (p + 1)) (s + 1))) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (Wtrunc_shift Q s S))

/-! ## 4. The reserve `(†)` in `acN`, and the `SymMinorGershgorin` inhabitant -/

/-- `qpow w 2 ≃ w · w`. -/
private theorem qpow2_ww (w : Q') : (qpow w 2).eqv (w * w) := by
  show ((qpow w 0 * w) * w).eqv (w * w)
  exact Q'.mul_eqv_congr_right _ _ w
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ w (Q'.eqv_of_eq (qpow_zero w)))
      (Q'.one_mul_eqv w))

/-- `0 < w ⟹ 0 < w²`. -/
private theorem qpow2_pos {w : Q'} (hw0 : (0 : Q') < w) : (0 : Q') < qpow w 2 :=
  lt_of_lt_of_le (Q'.mul_pos hw0 hw0) (Q'.ge_of_eqv (qpow2_ww w))

/-- **`crossN`** — the fusion-box reserve `(†)` `256·acN(s+1,s)·acN(s+1,s+2) ≤ 225·acN(s+1,s+1)²`
for `0 < w ≤ 1/2`, obtained from `(‡_trunc)` through the `Q = 1/w²` reindexing. -/
theorem crossN {w : Q'} (hw0 : (0 : Q') < w) (hwle : w ≤ FusionCoreStepRoundA.wH) (s : Nat) :
    Q'.ofNat 256 * (acN w (s + 1) s * acN w (s + 1) (s + 2))
      ≤ Q'.ofNat 225 * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1)) := by
  have hw0' : (0 : Q') ≤ w := Q'.le_of_lt hw0
  have hq : (0 : Q') < qpow w 2 := qpow2_pos hw0
  have hatom : (qpow w 2 * Q'.divPos 1 (qpow w 2) hq).eqv 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (qpow w 2) (Q'.divPos 1 (qpow w 2) hq))
      (Q'.divPos_mul_eqv 1 (qpow w 2) hq)
  have hQ0 : (0 : Q') ≤ Q'.divPos 1 (qpow w 2) hq :=
    Q'.le_of_lt (Q'.divPos_pos 1 (qpow w 2) hq (by decide))
  -- 4·w² ≤ 1  (from w ≤ 1/2)
  have h4 : Q'.ofNat 4 * qpow w 2 ≤ (1 : Q') := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_of_eqv (qpow2_ww w)) (by decide)) ?_
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) w w))) ?_
    have s1 : Q'.ofNat 4 * w ≤ Q'.ofNat 2 := by
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hwle (by decide : (0 : Q') ≤ Q'.ofNat 4)) ?_
      exact Q'.le_of_eqv (by decide : (Q'.ofNat 4 * FusionCoreStepRoundA.wH).eqv (Q'.ofNat 2))
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ s1 hw0') ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hwle (by decide : (0 : Q') ≤ Q'.ofNat 2)) ?_
    exact Q'.le_of_eqv (by decide : (Q'.ofNat 2 * FusionCoreStepRoundA.wH).eqv (1 : Q'))
  have hQ4 : Q'.ofNat 4 ≤ Q'.divPos 1 (qpow w 2) hq :=
    Q'.le_divPos_of_mul_le 1 (qpow w 2) hq h4
  have hq20 : (0 : Q') ≤ qpow w 2 := Q'.le_of_lt hq
  have hG0 : (0 : Q') ≤ qpow w (2 * fExp (s + 1)) := qpow_nonneg w hw0' _
  -- (‡_trunc)
  have hcross := uturan_trunc_unconditional hQ4 s
  -- X ≤ Y :  w²·(256·(Ws·Ws2)) ≤ 225·(Ws1·Ws1)
  have hXY : qpow w 2 * (Q'.ofNat 256 *
        (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s s * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 2)))
      ≤ Q'.ofNat 225 *
        (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)
          * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)) := by
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hcross hq20) ?_
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (qpow w 2) (Q'.ofNat 225 * Q'.divPos 1 (qpow w 2) hq)
        (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)
          * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)))) ?_
    refine Q'.mul_eqv_congr_right _ _ _ ?_
    refine Q'.eqv_trans _ _ _ (mulLC (qpow w 2) (Q'.ofNat 225) (Q'.divPos 1 (qpow w 2) hq)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 225) _ _ hatom) ?_
    exact Q'.mul_one_eqv (Q'.ofNat 225)
  -- Gaussian collapses
  have gs : (qpow w (fExp s) * qpow w (fExp (s + 2))).eqv
      (qpow w (2 * fExp (s + 1)) * qpow w 2) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (qpow_add w (fExp s) (fExp (s + 2)))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (congrArg (qpow w) (fExp_sum s))) ?_
    exact qpow_add w (2 * fExp (s + 1)) 2
  have gs1 : (qpow w (fExp (s + 1)) * qpow w (fExp (s + 1))).eqv (qpow w (2 * fExp (s + 1))) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (qpow_add w (fExp (s + 1)) (fExp (s + 1)))) ?_
    exact Q'.eqv_of_eq
      (congrArg (qpow w) (by omega : fExp (s + 1) + fExp (s + 1) = 2 * fExp (s + 1)))
  have hA_s : (acN w (s + 1) s).eqv (qpow w (fExp s) * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s s) :=
    acN_reindex hatom s s (Nat.le_refl s)
  have hA_s2 : (acN w (s + 1) (s + 2)).eqv
      (qpow w (fExp (s + 2)) * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 2)) :=
    acN_reindex hatom s (s + 2) (by omega)
  have hA_s1 : (acN w (s + 1) (s + 1)).eqv
      (qpow w (fExp (s + 1)) * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)) :=
    acN_reindex hatom s (s + 1) (by omega)
  -- LHS ≃ G·X
  have hLHS : (Q'.ofNat 256 * (acN w (s + 1) s * acN w (s + 1) (s + 2))).eqv
      (qpow w (2 * fExp (s + 1)) *
        (qpow w 2 * (Q'.ofNat 256 *
          (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s s
            * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 2))))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hA_s)
          (Q'.mul_eqv_congr_left _ _ _ hA_s2))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (mul4 (qpow w (fExp s)) (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s s)
          (qpow w (fExp (s + 2))) (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 2)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ gs)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_assoc_eqv (qpow w (2 * fExp (s + 1))) (qpow w 2)
          (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s s
            * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 2)))) ?_
    refine Q'.eqv_trans _ _ _
      (mulLC (Q'.ofNat 256) (qpow w (2 * fExp (s + 1)))
        (qpow w 2 * (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s s
          * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 2)))) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (mulLC (Q'.ofNat 256) (qpow w 2)
        (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s s
          * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 2)))
  -- RHS ≃ G·Y
  have hRHS : (Q'.ofNat 225 * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1))).eqv
      (qpow w (2 * fExp (s + 1)) *
        (Q'.ofNat 225 *
          (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)
            * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hA_s1)
          (Q'.mul_eqv_congr_left _ _ _ hA_s1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (mul4 (qpow w (fExp (s + 1))) (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1))
          (qpow w (fExp (s + 1))) (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ gs1)) ?_
    exact mulLC (Q'.ofNat 225) (qpow w (2 * fExp (s + 1)))
      (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)
        * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) (Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hRHS))
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hXY hG0

/-- **`reserveOfTrunc`** — `LeakGeoDecay.AcNDefectReserve w` for `0 < w ≤ 1/2`, from `crossN` via
`AcNReserveAnalytic.reserve_of_cross`. -/
def reserveOfTrunc {w : Q'} (hw0 : (0 : Q') < w) (hwle : w ≤ FusionCoreStepRoundA.wH) :
    LeakGeoDecay.AcNDefectReserve w where
  reserve := fun s => AcNReserveAnalytic.reserve_of_cross (crossN hw0 hwle s)

/-- **`symMinorGershgorin_of_trunc` — the general-`w` `SymMinorGershgorin` INHABITANT.**  For every
`0 < w ≤ 1/2` the aggregate `symMinor` Gershgorin domination `SymMinorGershgorin w` is inhabited,
via `LeakGeoDecay.gershgorinOfReserve` on the reserve produced by the truncated coupling Turán. -/
def symMinorGershgorin_of_trunc {w : Q'} (hw0 : (0 : Q') < w)
    (hwle : w ≤ FusionCoreStepRoundA.wH) : AutoconvGershgorin.SymMinorGershgorin w :=
  LeakGeoDecay.gershgorinOfReserve (reserveOfTrunc hw0 hwle)

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms fexp_identity
#print axioms fExp_sum
#print axioms powInv
#print axioms qpow_reindex
#print axioms coeff_reindex
#print axioms Wtrunc_shift
#print axioms acN_reindex
#print axioms crossN
#print axioms reserveOfTrunc
#print axioms symMinorGershgorin_of_trunc

end YMGap.Continuum.FusionUTuranReindex
