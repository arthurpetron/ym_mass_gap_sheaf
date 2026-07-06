/-
Track A / R2 — the FINITE-`S`-MARGIN truncated coupling Turán `(‡_finiteS)` and the general-`w`
`AcNReserveAnalytic.FiniteSMargin` INHABITANT.

# What this module adds (read `docs/reindexing-correction-2026-07-06.md` first)

`FusionUTuranTrunc.uturan_trunc_unconditional` proves the truncated coupling Turán at the WEAKER
reserve constant `256/225 = 1.1378` (clean legs `5/3` even, `32/15` odd).  Reindexed to `acN` this
inhabits `AutoconvGershgorin.SymMinorGershgorin`, but NOT the strictly-tighter
`AcNReserveAnalytic.FiniteSMargin w`, which needs the rational theta-floor constant
`40000/22801 = 1.7543` (`= 4/θ₃(0,¼)²`, `θ₃ ≤ 151/100`).

The genuine content here: the even-`s` cell's clean upper leg `(Q+1)/(Q−1) = 5/3` is too loose
(it forces the leg ratio down to `36/25 = 1.44 < 1.7543`).  The TRUE even autoconvolution peak
majorant is `≈ 1.508` — obtained by a STEP-3 geometric tail (the antidiagonal shell exponents drop
as `r²`, and `r² ≥ 3r − 2`), giving the sharp clean constant `c_e = 95/63 = 1.50794` and leg ratio
`4/c_e² = 15876/9025 = 1.75911 > 1.7543`.  The odd cell already clears the floor with `32/15` once
the crude `3m₃ ≤ 4mₚ` bound is replaced by the sharper `18mₚ ≥ 16m₃` (giving the reduced scalar
`14745600·Q ≤ 22801·(9Q+16)²`).

# What is PROVED here (axiom-clean)

  * `geomAsc3_le`, `geomDesc3_le` — the step-3 geometric-tail bounds (`(Σ Q^{base+3i})(Q³−1) ≤ …`).
  * `Ucoup_upper_even_tight` — the SHARP even upper `U(2n)·(Q³−1) ≤ (M·Q^M)·(Q³+2Q²−1)`,
    peak-exact + step-3 tail; wrapped to `U(2n) ≤ (95/63)·M·Q^M` (`c_e_valid`, cubic cert).
  * `finiteS_trunc_unconditional` — `(‡_finiteS)` `40000·Wtrunc(s,s)·Wtrunc(s,s+2) ≤
    22801·Q·Wtrunc(s,s+1)²`, all `s`, `Q ≥ 4`.
  * `finiteSMargin_of_trunc` — **`AcNReserveAnalytic.FiniteSMargin w` INHABITED** for every
    `0 < w ≤ 1/2`, via the `Q = 1/w²` reindexing (reusing `FusionUTuranReindex.acN_reindex`).

# HONESTY

`FiniteSMargin` is a fusion-box log-concavity NODE (`FrontierDAG.coreB`'s field), NOT one of the
five guarded Clay-frontier bundles.  Filling it does NOT inhabit `FrontierDAG` (its `minlos =
ClayContinuumExistence` slot stays open) and the frontier guard MUST still report all five
uninhabited.  This is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `qpow`/`fsum`/`divPos` API, the PROVED
`FusionUTuranEnvelope`/`FusionUTuranTrunc`/`FusionUTuranReindex` legs, and `decide`/`omega` on
closed rational/`Nat` facts.  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext`/`Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.FusionUTuranTrunc
import YMGap.Continuum.FusionUTuranReindex
import YMGap.Continuum.AcNReserveAnalytic

namespace YMGap.Continuum.FusionUTuranFiniteS

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.FusionUTuranWFree
open YMGap.Continuum.FusionUTuranEnvelope
open YMGap.Continuum.FusionUTuranTrunc
open YMGap.Continuum.CubeRatioBounds

/-! ## 1. Step-3 geometric-tail bounds (the machinery that beats the loose `5/3`) -/

/-- Local finite-sum reversal (copied from `FusionUTuranEnvelope.revSumE`, which is private). -/
private theorem fsum_shift_consL (g : Nat → Q') :
    ∀ n, (fsum g (n + 1)).eqv (g 0 + fsum (fun i => g (i + 1)) n)
  | 0 => by
    show ((0 : Q') + g 0).eqv (g 0 + (0 : Q'))
    refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' (g 0))) ?_
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (g 0)))
  | n + 1 => by
    show (fsum g (n + 1) + g (n + 1)).eqv
        (g 0 + (fsum (fun i => g (i + 1)) n + g (n + 1)))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (g (n + 1)) (fsum_shift_consL g n)) ?_
    exact Q'.add_assoc_eqv (g 0) (fsum (fun i => g (i + 1)) n) (g (n + 1))

private theorem revSumL (G : Nat → Q') :
    ∀ n, (fsum (fun p => G (n - p)) (n + 1)).eqv (fsum G (n + 1))
  | 0 => Q'.eqv_refl _
  | n + 1 => by
    refine Q'.eqv_trans _ _ _ (fsum_shift_consL (fun p => G ((n + 1) - p)) (n + 1)) ?_
    have hcongr : (fsum (fun i => G ((n + 1) - (i + 1))) (n + 1)).eqv
        (fsum (fun i => G (n - i)) (n + 1)) := by
      refine fsum_eqv_congr _ _ (fun i => ?_) (n + 1)
      exact Q'.eqv_of_eq (congrArg G (by omega))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hcongr) ?_
    have hib : (fsum (fun i => G (n - i)) (n + 1)).eqv (fsum G (n + 1)) := revSumL G n
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hib) ?_
    show (G (n + 1) + fsum G (n + 1)).eqv (fsum G (n + 1) + G (n + 1))
    exact Q'.add_comm_eqv (G (n + 1)) (fsum G (n + 1))

/-- **Ascending step-3 geometric bound.**  `(Σ_{i<k} Q^{base+3i})·(Q³−1) ≤ Q^{base+3k}`.
Mirrors `geomAsc2_le` with the peak-step `3`. -/
theorem geomAsc3_le {Q : Q'} (hQ0 : (0 : Q') ≤ Q) (base k : Nat) :
    fsum (fun i => qpow Q (base + 3 * i)) k * (qpow Q 3 + -(1 : Q'))
      ≤ qpow Q (base + 3 * k) := by
  have hterm : ∀ i, (qpow Q (base + 3 * i)).eqv (qpow Q base * qpow (qpow Q 3) i) := by
    intro i
    refine Q'.eqv_trans _ _ _ (qpow_add Q base (3 * i)) ?_
    exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (qpow_qpow Q 3 i))
  have hS : (fsum (fun i => qpow Q (base + 3 * i)) k).eqv
      (qpow Q base * fsum (qpow (qpow Q 3)) k) := by
    refine Q'.eqv_trans _ _ _ (fsum_eqv_congr _ _ hterm k) ?_
    exact Q'.eqv_symm (fsum_const_mul (qpow Q base) (qpow (qpow Q 3)) k)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hS)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_assoc_eqv (qpow Q base) (fsum (qpow (qpow Q 3)) k)
      (qpow Q 3 + -(1 : Q')))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (geomTail_le (qpow Q 3) k) (qpow_nonneg Q hQ0 base)) ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (qpow_qpow Q 3 k)) ?_
  exact Q'.eqv_symm (qpow_add Q base (3 * k))

/-- **Descending step-3 geometric bound.**  `(Σ_{r<k} Q^{P−3r})·(Q³−1) ≤ Q^{P+3}` for `3k ≤ P+3`.
Mirrors `geomDesc2_le`. -/
theorem geomDesc3_le {Q : Q'} (hQ0 : (0 : Q') ≤ Q) {P k : Nat} (hk : 3 * k ≤ P + 3) :
    fsum (fun r => qpow Q (P - 3 * r)) k * (qpow Q 3 + -(1 : Q')) ≤ qpow Q (P + 3) := by
  cases k with
  | zero =>
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (q_zero_mul _)) (qpow_nonneg Q hQ0 (P + 3))
  | succ n =>
      have hnP : 3 * n ≤ P := by omega
      have href : (fsum (fun r => qpow Q (P - 3 * r)) (n + 1)).eqv
          (fsum (fun x => qpow Q ((P - 3 * n) + 3 * x)) (n + 1)) := by
        have h1 : (fsum (fun r => qpow Q (P - 3 * r)) (n + 1)).eqv
            (fsum (fun p => qpow Q ((P - 3 * n) + 3 * (n - p))) (n + 1)) := by
          refine fsum_eqv_congr_lt _ _ (n + 1) (fun p hp => ?_)
          exact Q'.eqv_of_eq (congrArg (qpow Q) (by omega))
        exact Q'.eqv_trans _ _ _ h1 (revSumL (fun x => qpow Q ((P - 3 * n) + 3 * x)) n)
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ href)) ?_
      have hb := geomAsc3_le hQ0 (P - 3 * n) (n + 1)
      have he : (P - 3 * n) + 3 * (n + 1) = P + 3 := by omega
      rw [he] at hb
      exact hb

/-! ## 1b. Local `Q'` polynomial helpers (single-variable monomial arithmetic in `Q`) -/

private theorem mul4c (a b c d : Q') : ((a * b) * (c * d)).eqv ((a * c) * (b * d)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left a _ _ (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

/-- `(a·Q)·(b·Q) ≃ (a·b)·(Q·Q)`. -/
private theorem ccQ (Q : Q') (a b : Nat) :
    ((Q'.ofNat a * Q) * (Q'.ofNat b * Q)).eqv (Q'.ofNat (a * b) * (Q * Q)) :=
  Q'.eqv_trans _ _ _ (mul4c (Q'.ofNat a) Q (Q'.ofNat b) Q)
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv a b)))

/-- `n·(c·X) ≃ (n·c)·X`. -/
private theorem ncG (n c : Nat) (X : Q') :
    (Q'.ofNat n * (Q'.ofNat c * X)).eqv (Q'.ofNat (n * c) * X) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat n) (Q'.ofNat c) X)) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv n c))

/-- `(a·X + b·X) ≃ (a+b)·X`. -/
private theorem combX (a b : Nat) (X : Q') :
    (Q'.ofNat a * X + Q'.ofNat b * X).eqv (Q'.ofNat (a + b) * X) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat a) (Q'.ofNat b) X)) ?_
  refine Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm ?_)
  show (Q'.ofNat (a + b)).eqv (Q'.ofNat a + Q'.ofNat b)
  show ((a + b : Nat) : Int) * (((Q'.ofNat a + Q'.ofNat b).den : Nat) : Int)
      = ((Q'.ofNat a).num * ((Q'.ofNat b).den : Int)
          + (Q'.ofNat b).num * ((Q'.ofNat a).den : Int))
        * (((Q'.ofNat (a + b)).den : Nat) : Int)
  have h1 : ((Q'.ofNat a + Q'.ofNat b).den : Int) = 1 := rfl
  have h2 : ((Q'.ofNat (a + b)).den : Int) = 1 := rfl
  rw [h1, h2, Int.mul_one, Int.mul_one]
  show ((a + b : Nat) : Int) = (a : Int) * 1 + (b : Int) * 1
  rw [Int.mul_one, Int.mul_one, Int.natCast_add]

/-- **`Qsq_ge`** — `8·Q ≤ Q·Q + 16` for `Q ≥ 4` (from `(Q−4)² ≥ 0`). -/
private theorem Qsq_ge {Q : Q'} (hQ4 : Q'.ofNat 4 ≤ Q) :
    Q'.ofNat 8 * Q ≤ Q * Q + Q'.ofNat 16 := by
  have hD0 : (0 : Q') ≤ Q + -(Q'.ofNat 4) := by
    have h := Q'.add_le_add_right _ _ (-(Q'.ofNat 4)) hQ4
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (by decide : ((Q'.ofNat 4 + -(Q'.ofNat 4)) : Q').eqv 0)) h
  have hsq0 : (0 : Q') ≤ (Q + -(Q'.ofNat 4)) * (Q + -(Q'.ofNat 4)) := Q'.mul_nonneg _ _ hD0 hD0
  -- (Q-4)(Q-4) ≃ Q·Q + (-(8·Q) + 16)
  have hexp : ((Q + -(Q'.ofNat 4)) * (Q + -(Q'.ofNat 4))).eqv
      (Q * Q + (-(Q'.ofNat 8 * Q) + Q'.ofNat 16)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv Q (-(Q'.ofNat 4)) (Q + -(Q'.ofNat 4))) ?_
    have hL : (Q * (Q + -(Q'.ofNat 4))).eqv (Q * Q + -(Q'.ofNat 4 * Q)) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv Q Q (-(Q'.ofNat 4))) ?_
      refine Q'.add_eqv_congr_left _ _ _ ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv Q (Q'.ofNat 4)) ?_
      exact Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv Q (Q'.ofNat 4))
    have hR : ((-(Q'.ofNat 4)) * (Q + -(Q'.ofNat 4))).eqv
        (-(Q'.ofNat 4 * Q) + Q'.ofNat 16) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (-(Q'.ofNat 4)) Q (-(Q'.ofNat 4))) ?_
      refine Q'.add_eqv_congr' (Q'.neg_mul_eqv (Q'.ofNat 4) Q) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (-(Q'.ofNat 4)) (Q'.ofNat 4)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.neg_eqv_congr _ _ (Q'.neg_mul_eqv (Q'.ofNat 4) (Q'.ofNat 4))) ?_
      exact (by decide : ((-(-(Q'.ofNat 4 * Q'.ofNat 4))) : Q').eqv (Q'.ofNat 16))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hL hR) ?_
    -- (Q·Q + -(4Q)) + (-(4Q) + 16) ≃ Q·Q + (-(8Q) + 16)
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (Q * Q) (-(Q'.ofNat 4 * Q)) (-(Q'.ofNat 4 * Q) + Q'.ofNat 16)) ?_
    refine Q'.add_eqv_congr_left (Q * Q) _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-(Q'.ofNat 4 * Q)) (-(Q'.ofNat 4 * Q)) (Q'.ofNat 16))) ?_
    refine Q'.add_eqv_congr_right _ _ (Q'.ofNat 16) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_add_eqv (Q'.ofNat 4 * Q) (Q'.ofNat 4 * Q))) ?_
    exact Q'.neg_eqv_congr _ _ (combX 4 4 Q)
  -- 0 ≤ Q·Q + (-(8Q)+16)  ⟹  8Q ≤ Q·Q + 16
  have hstep : (0 : Q') ≤ Q * Q + (-(Q'.ofNat 8 * Q) + Q'.ofNat 16) :=
    Q'.le_trans' _ _ _ hsq0 (Q'.le_of_eqv hexp)
  have h := Q'.add_le_add_right _ _ (Q'.ofNat 8 * Q) hstep
  refine Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (Q'.ofNat 8 * Q)))) ?_
  refine Q'.le_trans' _ _ _ h ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (Q * Q) (-(Q'.ofNat 8 * Q) + Q'.ofNat 16) (Q'.ofNat 8 * Q)) ?_
  refine Q'.add_eqv_congr_left (Q * Q) _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (Q'.ofNat 8 * Q)
      (Q'.add_comm_eqv (-(Q'.ofNat 8 * Q)) (Q'.ofNat 16))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (Q'.ofNat 16) (-(Q'.ofNat 8 * Q)) (Q'.ofNat 8 * Q)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv (Q'.ofNat 8 * Q))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- `3·d ≤ d² + 2` for `d ≥ 1` (i.e. `d² ≥ 3d − 2`, the `r² ≥ 3r − 2` peak-decay engine). -/
private theorem three_mul_le_sq (d : Nat) (hd1 : 1 ≤ d) : 3 * d ≤ d * d + 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have ee : e ≤ e * e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · omega
    · calc e = e * 1 := (Nat.mul_one e).symm
        _ ≤ e * e := Nat.mul_le_mul_left e h
  have hexp : (e + 1) * (e + 1) = e * e + 2 * e + 1 := by have := expand e 1 1; omega
  omega

/-- Left half (`i < n`, `n ≥ 2`): coeff `i(2n−i) ≤ n²` and exp `i(2n−i) ≤ (n²−3n+2)+3i`. -/
theorem coeff_exp3_even_left (n i : Nat) (hn : 2 ≤ n) (hi : i < n) :
    i * (2 * n - i) ≤ n * n ∧ i * (2 * n - i) ≤ (n * n + 2 - 3 * n) + 3 * i := by
  obtain ⟨d, rfl⟩ := Nat.le.dest (Nat.le_of_lt hi)     -- n := i + d, d = n - i ≥ 1
  have hd1 : 1 ≤ d := by omega
  have hLHS : i * (2 * (i + d) - i) = i * i + 2 * (i * d) := by
    have h2 : 2 * (i + d) - i = i + 2 * d := by omega
    rw [h2, Nat.mul_add]
    have hh : i * (2 * d) = 2 * (i * d) := by
      rw [Nat.mul_comm i (2 * d), Nat.mul_assoc, Nat.mul_comm d i]
    omega
  have hNN : (i + d) * (i + d) = i * i + 2 * (i * d) + d * d := by
    have e := expand i d d       -- (i+d)*(i+d) = i*i + d*i + d*i + d*d
    have hc : d * i = i * d := Nat.mul_comm d i
    omega
  have hdd := three_mul_le_sq d hd1
  rw [hLHS]
  exact ⟨by omega, by omega⟩

/-- Right (peak-descending) shell `i = n+1+r` (`r+1 < n`): coeff `≤ n²` and exp `≤ (n²−1)−3r`. -/
theorem coeff_exp3_even_right (n r : Nat) (hr : r + 1 < n) :
    (n + 1 + r) * (2 * n - (n + 1 + r)) ≤ n * n
    ∧ (n + 1 + r) * (2 * n - (n + 1 + r)) ≤ (n * n - 1) - 3 * r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = (r + 1) + m := ⟨n - (r + 1), by omega⟩   -- m ≥ 1
  have hm1 : 1 ≤ m := by omega
  -- 2n − (n+1+r) = m ; coeff = (2r+2+m)·m
  have hidx : ((r + 1) + m + 1 + r) * (2 * ((r + 1) + m) - ((r + 1) + m + 1 + r))
      = (2 * r + 2 + m) * m := by
    have h1 : 2 * ((r + 1) + m) - ((r + 1) + m + 1 + r) = m := by omega
    have h2 : (r + 1) + m + 1 + r = 2 * r + 2 + m := by omega
    rw [h1, h2]
  rw [hidx]
  -- coeff expansion: (2r+2+m)·m = 2·(r·m) + 2·m + m·m
  have hcf : (2 * r + 2 + m) * m = 2 * (r * m) + 2 * m + m * m := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc]
  -- n·n = ((r+1)+m)² = (r+1)² + 2·((r+1)·m) + m²  and (r+1)·m = r·m + m
  have hNN : ((r + 1) + m) * ((r + 1) + m)
      = (r + 1) * (r + 1) + 2 * (r * m) + 2 * m + m * m := by
    have e := expand (r + 1) m m     -- = (r+1)*(r+1) + m*(r+1) + m*(r+1) + m*m
    have hc : m * (r + 1) = r * m + m := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm m r]
    omega
  -- (r+1)² ≥ 3r+1  (i.e. r²+2r+1 ≥ 3r+1 ⟺ r² ≥ r)
  have hrsq : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by have := expand r 1 1; omega
  have hrr : r ≤ r * r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · omega
    · calc r = r * 1 := (Nat.mul_one r).symm
        _ ≤ r * r := Nat.mul_le_mul_left r h
  rw [hcf]
  exact ⟨by omega, by omega⟩

/-! ## 3. The SHARP even upper bound `U(2n)·(Q³−1) ≤ M·Q^M·(Q³+2Q²−1)` -/

/-- The `wterm`/`Ucoup` summand as an explicit lower/upper handle at the peak. -/
private theorem wterm_peak_even (Q : Q') (n : Nat) :
    wterm Q (2 * n) n = Q'.ofNat (n * n) * qpow Q (n * n) := by
  unfold wterm
  have he : n * (2 * n - n) = n * n := by rw [show 2 * n - n = n by omega]
  rw [he]

private theorem q_add_zero_L (a : Q') : (a + (0 : Q')).eqv a := by
  exact Q'.eqv_of_eq (Q'.add_zero' a)

/-- **`Ucoup_upper_even_tight`** — the SHARP even majorant.  For `n ≥ 1`, `M = n²`:
`U(2n)·(Q³−1) ≤ (M·Q^M)·((Q³−1) + 2Q²)`, obtained by KEEPING the peak `M·Q^M` exact and bounding
both half-tails by the STEP-3 geometric sum (shell exponents drop as `r²`, `r² ≥ 3r − 2`). -/
theorem Ucoup_upper_even_tight {Q : Q'} (hQ1 : (1 : Q') ≤ Q) {n : Nat} (hn : 1 ≤ n) :
    Ucoup Q (2 * n) * (qpow Q 3 + -(1 : Q'))
      ≤ (Q'.ofNat (n * n) * qpow Q (n * n)) * ((qpow Q 3 + -(1 : Q')) + Q'.ofNat 2 * qpow Q 2) := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ1
  have hD30 : (0 : Q') ≤ qpow Q 3 + -(1 : Q') := by
    have h0 : ((1 : Q') + -(1 : Q')).eqv 0 := by decide
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv h0)
      (Q'.add_le_add_right _ _ (-(1 : Q')) (one_le_qpow hQ1 3))
  have hMQM0 : (0 : Q') ≤ Q'.ofNat (n * n) * qpow Q (n * n) :=
    Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ0 _)
  -- peak fact
  have hpeak : wterm Q (2 * n) n = Q'.ofNat (n * n) * qpow Q (n * n) := wterm_peak_even Q n
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · -- n = 1 : U(2) = wterm(2,1) = 1·Q^1 ; both tails empty
    have hn1' : n = 1 := by omega
    subst hn1'
    have hU : (Ucoup Q 2).eqv (Q'.ofNat 1 * qpow Q 1) := by
      show (fsum (wterm Q 2) 2).eqv (Q'.ofNat 1 * qpow Q 1)
      -- fsum (wterm Q 2) 2 = (0 + wterm 0) + wterm 1
      have h0 : (wterm Q 2 0).eqv 0 := by
        show (Q'.ofNat (0 * (2 - 0)) * qpow Q (0 * (2 - 0))).eqv 0
        exact Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ (by decide : (Q'.ofNat 0).eqv 0)) (q_zero_mul _)
      have h1 : wterm Q 2 1 = Q'.ofNat 1 * qpow Q 1 := rfl
      show (((0 : Q') + wterm Q 2 0) + wterm Q 2 1).eqv (Q'.ofNat 1 * qpow Q 1)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (wterm Q 2 1)
          (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) h0)) ?_
      exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) (Q'.eqv_of_eq h1)
    -- goal reduces to (1·Q)·D3 ≤ (1·Q)·(D3 + 2Q²)
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_eqv hU) hD30) ?_
    have hval : (Q'.ofNat (1 * 1) * qpow Q (1 * 1)) = Q'.ofNat 1 * qpow Q 1 := rfl
    rw [hval]
    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ0 _))
    -- D3 ≤ D3 + 2Q²
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (q_add_zero_L (qpow Q 3 + -(1:Q'))))) ?_
    exact Q'.add_le_add_left _ _ _
      (Q'.mul_nonneg _ _ (by decide) (qpow_nonneg Q hQ0 _))
  · -- n ≥ 2 : peak-exact + two step-3 tails
    -- 1. split U(2n) = L + R at n
    have hUw : Ucoup Q (2 * n) = fsum (wterm Q (2 * n)) (n + n) := by
      rw [Ucoup_as_wsum]; congr 1; omega
    have hsplit1 : (Ucoup Q (2 * n)).eqv
        (fsum (wterm Q (2 * n)) n + fsum (fun r => wterm Q (2 * n) (n + r)) n) := by
      rw [hUw]; exact FusionCoreStepRoundH.fsum_split_at (wterm Q (2 * n)) n n
    -- 2. split R = peak + Rtail
    have hsplit2 : (fsum (fun r => wterm Q (2 * n) (n + r)) n).eqv
        (wterm Q (2 * n) n
          + fsum (fun k => wterm Q (2 * n) (n + 1 + k)) (n - 1)) := by
      have hs := FusionCoreStepRoundH.fsum_split_at (fun r => wterm Q (2 * n) (n + r)) 1 (n - 1)
      rw [(by omega : 1 + (n - 1) = n)] at hs
      refine Q'.eqv_trans _ _ _ hs ?_
      refine Q'.add_eqv_congr' ?_ ?_
      · show ((0 : Q') + wterm Q (2 * n) (n + 0)).eqv (wterm Q (2 * n) n)
        refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
        exact Q'.eqv_of_eq (congrArg (wterm Q (2 * n)) (by omega))
      · exact fsum_eqv_congr _ _ (fun k => Q'.eqv_of_eq (congrArg (wterm Q (2 * n)) (by omega))) (n - 1)
    -- nonneg + endpoint Nat facts
    have h3nle : 3 * n ≤ n * n + 2 := by
      obtain ⟨e, rfl⟩ : ∃ e, n = e + 2 := ⟨n - 2, by omega⟩
      have := expand e 2 2; omega
    have hM1 : 1 ≤ n * n := by
      have : 1 * 1 ≤ n * n := Nat.mul_le_mul (by omega) (by omega); omega
    -- L termwise bound
    have hLterm : ∀ i, i < n →
        wterm Q (2 * n) i ≤ Q'.ofNat (n * n) * qpow Q ((n * n + 2 - 3 * n) + 3 * i) := by
      intro i hi
      have hce := coeff_exp3_even_left n i hn2 hi
      show Q'.ofNat (i * (2 * n - i)) * qpow Q (i * (2 * n - i))
          ≤ Q'.ofNat (n * n) * qpow Q ((n * n + 2 - 3 * n) + 3 * i)
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.ofNat_le_ofNat hce.1) (qpow_nonneg Q hQ0 _)) ?_
      exact Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_exp_mono hQ1 hce.2) (ofNat_nonneg _)
    have hLbound : fsum (wterm Q (2 * n)) n
        ≤ Q'.ofNat (n * n) * fsum (fun i => qpow Q ((n * n + 2 - 3 * n) + 3 * i)) n := by
      refine Q'.le_trans' _ _ _ (fsum_mono_lt n hLterm) ?_
      exact Q'.le_of_eqv (Q'.eqv_symm
        (fsum_const_mul (Q'.ofNat (n * n)) (fun i => qpow Q ((n * n + 2 - 3 * n) + 3 * i)) n))
    -- Rtail termwise bound
    have hRterm : ∀ k, k < n - 1 →
        wterm Q (2 * n) (n + 1 + k) ≤ Q'.ofNat (n * n) * qpow Q ((n * n - 1) - 3 * k) := by
      intro k hk
      have hce := coeff_exp3_even_right n k (by omega)
      show Q'.ofNat ((n + 1 + k) * (2 * n - (n + 1 + k)))
            * qpow Q ((n + 1 + k) * (2 * n - (n + 1 + k)))
          ≤ Q'.ofNat (n * n) * qpow Q ((n * n - 1) - 3 * k)
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.ofNat_le_ofNat hce.1) (qpow_nonneg Q hQ0 _)) ?_
      exact Q'.mul_le_mul_of_nonneg_left _ _ _ (qpow_exp_mono hQ1 hce.2) (ofNat_nonneg _)
    have hRbound : fsum (fun k => wterm Q (2 * n) (n + 1 + k)) (n - 1)
        ≤ Q'.ofNat (n * n) * fsum (fun k => qpow Q ((n * n - 1) - 3 * k)) (n - 1) := by
      refine Q'.le_trans' _ _ _ (fsum_mono_lt (n - 1) hRterm) ?_
      exact Q'.le_of_eqv (Q'.eqv_symm
        (fsum_const_mul (Q'.ofNat (n * n)) (fun k => qpow Q ((n * n - 1) - 3 * k)) (n - 1)))
    -- geometric sums
    have hSL : fsum (fun i => qpow Q ((n * n + 2 - 3 * n) + 3 * i)) n * (qpow Q 3 + -(1 : Q'))
        ≤ qpow Q (n * n + 2) := by
      have h := geomAsc3_le hQ0 (n * n + 2 - 3 * n) n
      have he : (n * n + 2 - 3 * n) + 3 * n = n * n + 2 := by omega
      rw [he] at h; exact h
    have hSR : fsum (fun k => qpow Q ((n * n - 1) - 3 * k)) (n - 1) * (qpow Q 3 + -(1 : Q'))
        ≤ qpow Q (n * n + 2) := by
      have h := geomDesc3_le hQ0 (P := n * n - 1) (k := n - 1) (by omega)
      have he : (n * n - 1) + 3 = n * n + 2 := by omega
      rw [he] at h; exact h
    -- assemble
    have hUeq : (Ucoup Q (2 * n)).eqv
        (fsum (wterm Q (2 * n)) n
          + (wterm Q (2 * n) n + fsum (fun k => wterm Q (2 * n) (n + 1 + k)) (n - 1))) :=
      Q'.eqv_trans _ _ _ hsplit1 (Q'.add_eqv_congr_left _ _ _ hsplit2)
    have hdist : (Ucoup Q (2 * n) * (qpow Q 3 + -(1 : Q'))).eqv
        (fsum (wterm Q (2 * n)) n * (qpow Q 3 + -(1 : Q'))
          + (wterm Q (2 * n) n * (qpow Q 3 + -(1 : Q'))
             + fsum (fun k => wterm Q (2 * n) (n + 1 + k)) (n - 1) * (qpow Q 3 + -(1 : Q')))) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hUeq) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.add_mul_eqv _ _ _)
    have hb1 : fsum (wterm Q (2 * n)) n * (qpow Q 3 + -(1 : Q'))
        ≤ Q'.ofNat (n * n) * qpow Q (n * n + 2) := by
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hLbound hD30) ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)) ?_
      exact Q'.mul_le_mul_of_nonneg_left _ _ _ hSL (ofNat_nonneg _)
    have hb3 : fsum (fun k => wterm Q (2 * n) (n + 1 + k)) (n - 1) * (qpow Q 3 + -(1 : Q'))
        ≤ Q'.ofNat (n * n) * qpow Q (n * n + 2) := by
      refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hRbound hD30) ?_
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)) ?_
      exact Q'.mul_le_mul_of_nonneg_left _ _ _ hSR (ofNat_nonneg _)
    have hb2 : (wterm Q (2 * n) n * (qpow Q 3 + -(1 : Q'))).eqv
        ((Q'.ofNat (n * n) * qpow Q (n * n)) * (qpow Q 3 + -(1 : Q'))) :=
      Q'.eqv_of_eq (by rw [hpeak])
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hdist) ?_
    have hcomb : fsum (wterm Q (2 * n)) n * (qpow Q 3 + -(1 : Q'))
          + (wterm Q (2 * n) n * (qpow Q 3 + -(1 : Q'))
             + fsum (fun k => wterm Q (2 * n) (n + 1 + k)) (n - 1) * (qpow Q 3 + -(1 : Q')))
        ≤ Q'.ofNat (n * n) * qpow Q (n * n + 2)
          + ((Q'.ofNat (n * n) * qpow Q (n * n)) * (qpow Q 3 + -(1 : Q'))
             + Q'.ofNat (n * n) * qpow Q (n * n + 2)) :=
      Q'.add_le_add hb1 (Q'.add_le_add (Q'.le_of_eqv hb2) hb3)
    refine Q'.le_trans' _ _ _ hcomb ?_
    refine Q'.le_of_eqv ?_
    have hQM2 : (Q'.ofNat (n * n) * qpow Q (n * n + 2)).eqv
        ((Q'.ofNat (n * n) * qpow Q (n * n)) * qpow Q 2) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (qpow_add Q (n * n) 2)) ?_
      exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
    -- convert both MQ^{M+2} to A·Q²
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hQM2 (Q'.add_eqv_congr_left _ _ _ hQM2)) ?_
    -- now : A·Q² + (A·D3 + A·Q²) ≃ A·(D3 + 2Q²)
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (Q'.ofNat (n * n) * qpow Q (n * n)) (qpow Q 3 + -(1 : Q'))
        (Q'.ofNat 2 * qpow Q 2)) ?_
    have hten : (Q'.ofNat 2 * qpow Q 2).eqv (qpow Q 2 + qpow Q 2) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (qpow Q 2) (by decide : (Q'.ofNat 2).eqv (1 + 1))) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 (qpow Q 2)) ?_
      exact Q'.add_eqv_congr' (Q'.one_mul_eqv _) (Q'.one_mul_eqv _)
    have h2AQ : ((Q'.ofNat (n * n) * qpow Q (n * n)) * (Q'.ofNat 2 * qpow Q 2)).eqv
        (((Q'.ofNat (n * n) * qpow Q (n * n)) * qpow Q 2)
          + ((Q'.ofNat (n * n) * qpow Q (n * n)) * qpow Q 2)) :=
      Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hten)
        (Q'.mul_add_eqv (Q'.ofNat (n * n) * qpow Q (n * n)) (qpow Q 2) (qpow Q 2))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left ((Q'.ofNat (n * n) * qpow Q (n * n)) * (qpow Q 3 + -(1 : Q'))) _ _ h2AQ) ?_
    -- A·D3 + (A·Q² + A·Q²) ≃ A·Q² + (A·D3 + A·Q²)
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv ((Q'.ofNat (n * n) * qpow Q (n * n)) * (qpow Q 3 + -(1 : Q')))
        ((Q'.ofNat (n * n) * qpow Q (n * n)) * qpow Q 2)
        ((Q'.ofNat (n * n) * qpow Q (n * n)) * qpow Q 2))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ ((Q'.ofNat (n * n) * qpow Q (n * n)) * qpow Q 2)
        (Q'.add_comm_eqv ((Q'.ofNat (n * n) * qpow Q (n * n)) * (qpow Q 3 + -(1 : Q')))
          ((Q'.ofNat (n * n) * qpow Q (n * n)) * qpow Q 2))) ?_
    exact Q'.add_assoc_eqv ((Q'.ofNat (n * n) * qpow Q (n * n)) * qpow Q 2)
      ((Q'.ofNat (n * n) * qpow Q (n * n)) * (qpow Q 3 + -(1 : Q')))
      ((Q'.ofNat (n * n) * qpow Q (n * n)) * qpow Q 2)


/-! ## 3b. The odd reduced scalar `14745600·Q ≤ 22801·(9Q+16)²` -/

private theorem le_cancel_right {a b c : Q'} (h : a + c ≤ b + c) : a ≤ b := by
  have h2 := Q'.add_le_add_right _ _ (-c) h
  have eL : ((a + c) + -c).eqv a :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a c (-c))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a _ _ (Q'.add_neg_self_eqv c))
        (Q'.eqv_of_eq (Q'.add_zero' a)))
  have eR : ((b + c) + -c).eqv b :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b c (-c))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left b _ _ (Q'.add_neg_self_eqv c))
        (Q'.eqv_of_eq (Q'.add_zero' b)))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv eL) (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv eR))

/-- **`odd_scalarF`** — `14745600·Q ≤ 22801·(9Q+16)²` for `Q ≥ 4`.  The reduced univariate closure
of the ODD fusion cell at the finite-`S` constants (nonneg-coeff cert `1846881x²+6596136x+2671504`,
`x = Q−4`). -/
theorem odd_scalarF {Q : Q'} (hQ4 : Q'.ofNat 4 ≤ Q) :
    Q'.ofNat 14745600 * Q
      ≤ Q'.ofNat 22801 * ((Q'.ofNat 9 * Q + Q'.ofNat 16) * (Q'.ofNat 9 * Q + Q'.ofNat 16)) := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  -- expand (9Q+16)² ≃ 81(Q*Q) + (288 Q + 256)
  have hsq : ((Q'.ofNat 9 * Q + Q'.ofNat 16) * (Q'.ofNat 9 * Q + Q'.ofNat 16)).eqv
      (Q'.ofNat 81 * (Q * Q) + (Q'.ofNat 288 * Q + Q'.ofNat 256)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (Q'.ofNat 9 * Q) (Q'.ofNat 16) (Q'.ofNat 9 * Q + Q'.ofNat 16)) ?_
    have hA : ((Q'.ofNat 9 * Q) * (Q'.ofNat 9 * Q + Q'.ofNat 16)).eqv
        (Q'.ofNat 81 * (Q * Q) + Q'.ofNat 144 * Q) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat 9 * Q) (Q'.ofNat 9 * Q) (Q'.ofNat 16)) ?_
      refine Q'.add_eqv_congr' (ccQ Q 9 9) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.ofNat 9 * Q) (Q'.ofNat 16)) ?_
      exact ncG 16 9 Q
    have hB : (Q'.ofNat 16 * (Q'.ofNat 9 * Q + Q'.ofNat 16)).eqv
        (Q'.ofNat 144 * Q + Q'.ofNat 256) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat 16) (Q'.ofNat 9 * Q) (Q'.ofNat 16)) ?_
      exact Q'.add_eqv_congr' (ncG 16 9 Q)
        (by decide : (Q'.ofNat 16 * Q'.ofNat 16).eqv (Q'.ofNat 256))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hA hB) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (Q'.ofNat 81 * (Q * Q)) (Q'.ofNat 144 * Q)
        (Q'.ofNat 144 * Q + Q'.ofNat 256)) ?_
    refine Q'.add_eqv_congr_left _ _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (Q'.ofNat 144 * Q) (Q'.ofNat 144 * Q) (Q'.ofNat 256))) ?_
    exact Q'.add_eqv_congr_right _ _ (Q'.ofNat 256) (combX 144 144 Q)
  -- 22801·(9Q+16)² ≃ 1846881(Q*Q) + (6566688 Q + 5837056)
  have hnorm : (Q'.ofNat 22801 * ((Q'.ofNat 9 * Q + Q'.ofNat 16) * (Q'.ofNat 9 * Q + Q'.ofNat 16))).eqv
      (Q'.ofNat 1846881 * (Q * Q) + (Q'.ofNat 6566688 * Q + Q'.ofNat 5837056)) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hsq) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (Q'.ofNat 22801) (Q'.ofNat 81 * (Q * Q))
        (Q'.ofNat 288 * Q + Q'.ofNat 256)) ?_
    refine Q'.add_eqv_congr' (ncG 22801 81 (Q * Q)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (Q'.ofNat 22801) (Q'.ofNat 288 * Q) (Q'.ofNat 256)) ?_
    exact Q'.add_eqv_congr' (ncG 22801 288 Q)
      (by decide : (Q'.ofNat 22801 * Q'.ofNat 256).eqv (Q'.ofNat 5837056))
  -- quadratic 14745600·Q ≤ 1846881(Q*Q) + (6566688 Q + 5837056)
  have hQsq := Qsq_ge hQ4
  have hA : Q'.ofNat 14775048 * Q ≤ Q'.ofNat 1846881 * (Q * Q) + Q'.ofNat 29550096 := by
    have h1 : Q'.ofNat 1846881 * (Q'.ofNat 8 * Q) ≤ Q'.ofNat 1846881 * (Q * Q + Q'.ofNat 16) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hQsq (by decide)
    have hL : (Q'.ofNat 1846881 * (Q'.ofNat 8 * Q)).eqv (Q'.ofNat 14775048 * Q) := ncG 1846881 8 Q
    have hR : (Q'.ofNat 1846881 * (Q * Q + Q'.ofNat 16)).eqv
        (Q'.ofNat 1846881 * (Q * Q) + Q'.ofNat 29550096) :=
      Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat 1846881) (Q * Q) (Q'.ofNat 16))
        (Q'.add_eqv_congr_left _ _ _
          (by decide : (Q'.ofNat 1846881 * Q'.ofNat 16).eqv (Q'.ofNat 29550096)))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL) (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv hR))
  have h2 : Q'.ofNat 23713040 ≤ Q'.ofNat 6596136 * Q := by
    refine Q'.le_trans' _ _ _ (by decide : Q'.ofNat 23713040 ≤ Q'.ofNat 6596136 * Q'.ofNat 4) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hQ4 (by decide)
  -- step_b : 21341736 Q + 5837056 ≤ (1846881(Q*Q)+(6566688Q+5837056)) + 29550096
  have step_b : Q'.ofNat 21341736 * Q + Q'.ofNat 5837056
      ≤ (Q'.ofNat 1846881 * (Q * Q) + (Q'.ofNat 6566688 * Q + Q'.ofNat 5837056))
        + Q'.ofNat 29550096 := by
    have hadd := Q'.add_le_add hA (Q'.le_refl' (Q'.ofNat 6566688 * Q + Q'.ofNat 5837056))
    -- LHS ≃ 21341736 Q + 5837056 ; RHS ≃ target + 29550096
    have eL : (Q'.ofNat 14775048 * Q + (Q'.ofNat 6566688 * Q + Q'.ofNat 5837056)).eqv
        (Q'.ofNat 21341736 * Q + Q'.ofNat 5837056) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (Q'.ofNat 14775048 * Q) (Q'.ofNat 6566688 * Q)
          (Q'.ofNat 5837056))) ?_
      exact Q'.add_eqv_congr_right _ _ (Q'.ofNat 5837056) (combX 14775048 6566688 Q)
    have eR : ((Q'.ofNat 1846881 * (Q * Q) + Q'.ofNat 29550096)
          + (Q'.ofNat 6566688 * Q + Q'.ofNat 5837056)).eqv
        ((Q'.ofNat 1846881 * (Q * Q) + (Q'.ofNat 6566688 * Q + Q'.ofNat 5837056))
          + Q'.ofNat 29550096) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (Q'.ofNat 1846881 * (Q * Q)) (Q'.ofNat 29550096)
          (Q'.ofNat 6566688 * Q + Q'.ofNat 5837056)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_comm_eqv (Q'.ofNat 29550096) (Q'.ofNat 6566688 * Q + Q'.ofNat 5837056))) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv (Q'.ofNat 1846881 * (Q * Q))
        (Q'.ofNat 6566688 * Q + Q'.ofNat 5837056) (Q'.ofNat 29550096))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv eL) (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv eR))
  -- step_a : 14745600 Q + 29550096 ≤ 21341736 Q + 5837056
  have step_a : Q'.ofNat 14745600 * Q + Q'.ofNat 29550096
      ≤ Q'.ofNat 21341736 * Q + Q'.ofNat 5837056 := by
    -- 14745600Q + 29550096 ≃ (14745600Q + 5837056) + 23713040
    --                      ≤ (14745600Q + 5837056) + 6596136Q   (h2)
    --                      ≃ 21341736Q + 5837056
    have e1 : (Q'.ofNat 14745600 * Q + Q'.ofNat 29550096).eqv
        ((Q'.ofNat 14745600 * Q + Q'.ofNat 5837056) + Q'.ofNat 23713040) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (Q'.ofNat 14745600 * Q) _ _
          (by decide : (Q'.ofNat 29550096).eqv (Q'.ofNat 5837056 + Q'.ofNat 23713040))) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv (Q'.ofNat 14745600 * Q) (Q'.ofNat 5837056)
        (Q'.ofNat 23713040))
    have e2 : ((Q'.ofNat 14745600 * Q + Q'.ofNat 5837056) + Q'.ofNat 6596136 * Q).eqv
        (Q'.ofNat 21341736 * Q + Q'.ofNat 5837056) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (Q'.ofNat 14745600 * Q) (Q'.ofNat 5837056) (Q'.ofNat 6596136 * Q)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _
          (Q'.add_comm_eqv (Q'.ofNat 5837056) (Q'.ofNat 6596136 * Q))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (Q'.ofNat 14745600 * Q) (Q'.ofNat 6596136 * Q)
          (Q'.ofNat 5837056))) ?_
      exact Q'.add_eqv_congr_right _ _ (Q'.ofNat 5837056) (combX 14745600 6596136 Q)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left (Q'.ofNat 14745600 * Q + Q'.ofNat 5837056) _ _ h2) ?_
    exact Q'.le_of_eqv e2
  -- chain and cancel +29550096
  have hchain : Q'.ofNat 14745600 * Q + Q'.ofNat 29550096
      ≤ (Q'.ofNat 1846881 * (Q * Q) + (Q'.ofNat 6566688 * Q + Q'.ofNat 5837056))
        + Q'.ofNat 29550096 :=
    Q'.le_trans' _ _ _ step_a step_b
  have hquad := le_cancel_right hchain
  exact Q'.le_trans' _ _ _ hquad (Q'.ge_of_eqv hnorm)

/-! ## 3c. Local cancellation + block helpers (private reproofs of `FusionUTuranEnvelope` privates) -/

/-- Right cancellation of a positive factor: `a·c ≤ b·c`, `0 < c ⟹ a ≤ b`. -/
private theorem le_mul_right_cancel {a b c : Q'} (h : a * c ≤ b * c) (hc : (0 : Q') < c) : a ≤ b := by
  have h' : c * a ≤ c * b :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv c a))
      (Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.mul_comm_eqv b c)))
  exact Q'.le_of_mul_le_mul_left h' hc

/-- `Q ≥ 4 ⟹ 16 ≤ Q²` (local reproof of `FusionUTuranEnvelope.qpow2_ge16`). -/
private theorem qpow2_ge16F {Q : Q'} (hQ4 : Q'.ofNat 4 ≤ Q) : Q'.ofNat 16 ≤ qpow Q 2 := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  have h1 : Q'.ofNat 4 * Q'.ofNat 4 ≤ Q'.ofNat 4 * Q :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hQ4 (by decide)
  have h2 : Q'.ofNat 4 * Q ≤ Q * Q := Q'.mul_le_mul_of_nonneg_right _ _ _ hQ4 hQ0
  have h16 : Q'.ofNat 16 ≤ Q * Q :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (Q'.ofNat 16).eqv (Q'.ofNat 4 * Q'.ofNat 4)))
      (Q'.le_trans' _ _ _ h1 h2)
  have hq : (qpow Q 2).eqv (Q * Q) := by
    show ((qpow Q 0 * Q) * Q).eqv (Q * Q)
    exact Q'.mul_eqv_congr_right _ _ Q
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ Q (Q'.eqv_of_eq (qpow_zero Q))) (Q'.one_mul_eqv Q))
  exact Q'.le_trans' _ _ _ h16 (Q'.ge_of_eqv hq)

/-- Two-block product law `(c₁·Q^{m₁})·(c₂·Q^{m₂}) ≃ (c₁·c₂)·Q^{m₁+m₂}` (reproof of `blkMul`). -/
private theorem blkMulF (Q c1 c2 : Q') (m1 m2 : Nat) :
    ((c1 * qpow Q m1) * (c2 * qpow Q m2)).eqv ((c1 * c2) * qpow Q (m1 + m2)) := by
  refine Q'.eqv_trans _ _ _ (mul4c c1 (qpow Q m1) c2 (qpow Q m2)) ?_
  exact Q'.mul_eqv_congr_left (c1 * c2) _ _ (Q'.eqv_symm (qpow_add Q m1 m2))

/-- `2·T ≃ T + T` (reproof of `two_mul_eqvE`). -/
private theorem two_mul_eqvF (T : Q') : (Q'.ofNat 2 * T).eqv (T + T) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ T (by decide : (Q'.ofNat 2).eqv (1 + 1))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (1 + 1) T) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv T 1 1) ?_
  exact Q'.add_eqv_congr' (Q'.mul_one_eqv T) (Q'.mul_one_eqv T)

/-- Left-commutativity `a·(b·c) ≃ b·(a·c)` (reproof of `mulLC`). -/
private theorem mulLCf (a b c : Q') : (a * (b * c)).eqv (b * (a * c)) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

/-! ## 3d. The even clean cubic certificate `c_e = 95/63` and the even upper `U(2n) ≤ c_e·M·Q^M` -/

/-- Generic clean-constant closure: `u·den ≤ B·R`, `R ≤ c·den` (`den > 0`, `B ≥ 0`) ⟹ `u ≤ c·B`. -/
private theorem upper_cleanF {u B R c den : Q'} (hden : (0 : Q') < den) (hB : (0 : Q') ≤ B)
    (hleg : u * den ≤ B * R) (hRc : R ≤ c * den) : u ≤ c * B := by
  have h1 : B * R ≤ B * (c * den) := Q'.mul_le_mul_of_nonneg_left _ _ _ hRc hB
  have h2 : (B * (c * den)).eqv ((c * B) * den) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv B c den))
      (Q'.mul_eqv_congr_right _ _ den (Q'.mul_comm_eqv B c))
  have hcancel : u * den ≤ (c * B) * den :=
    Q'.le_trans' _ _ _ hleg (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h2))
  exact le_mul_right_cancel hcancel hden

/-- **`cubic_cert`** — `126·Q² + 32 ≤ 32·Q³` for `Q ≥ 4` (the step-3 cubic validity, ×2 scale). -/
private theorem cubic_cert {Q : Q'} (hQ4 : Q'.ofNat 4 ≤ Q) :
    Q'.ofNat 126 * qpow Q 2 + Q'.ofNat 32 ≤ Q'.ofNat 32 * qpow Q 3 := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  have h16 : Q'.ofNat 16 ≤ qpow Q 2 := qpow2_ge16F hQ4
  have hq2nn : (0 : Q') ≤ qpow Q 2 := qpow_nonneg Q hQ0 2
  have step1 : qpow Q 2 * Q'.ofNat 4 ≤ qpow Q 2 * Q :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hQ4 hq2nn
  have step2 : Q'.ofNat 32 * (qpow Q 2 * Q'.ofNat 4) ≤ Q'.ofNat 32 * (qpow Q 2 * Q) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ step1 (by decide)
  have e128 : (Q'.ofNat 32 * (qpow Q 2 * Q'.ofNat 4)).eqv (Q'.ofNat 128 * qpow Q 2) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (qpow Q 2) (Q'.ofNat 4))) ?_
    exact ncG 32 4 (qpow Q 2)
  have e128split : (Q'.ofNat 128 * qpow Q 2).eqv (Q'.ofNat 126 * qpow Q 2 + Q'.ofNat 2 * qpow Q 2) :=
    Q'.eqv_symm (combX 126 2 (qpow Q 2))
  have h2X : Q'.ofNat 32 ≤ Q'.ofNat 2 * qpow Q 2 := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by decide : (Q'.ofNat 32).eqv (Q'.ofNat 2 * Q'.ofNat 16))) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ h16 (by decide)
  have hAdd : Q'.ofNat 126 * qpow Q 2 + Q'.ofNat 32 ≤ Q'.ofNat 126 * qpow Q 2 + Q'.ofNat 2 * qpow Q 2 :=
    Q'.add_le_add_left _ _ _ h2X
  exact Q'.le_trans' _ _ _ hAdd
    (Q'.le_trans' _ _ _ (Q'.ge_of_eqv e128split) (Q'.le_trans' _ _ _ (Q'.ge_of_eqv e128) step2))

/-- **`c_e_valid`** — the even clean cubic cert: `(Q³−1) + 2Q² ≤ (95/63)·(Q³−1)` for `Q ≥ 4`. -/
theorem c_e_valid {Q : Q'} (hQ4 : Q'.ofNat 4 ≤ Q) :
    (qpow Q 3 + -(1 : Q')) + Q'.ofNat 2 * qpow Q 2
      ≤ Q'.mkPos 95 63 (by decide) * (qpow Q 3 + -(1 : Q')) := by
  refine le_mul_right_cancel (c := Q'.ofNat 63) ?_ (by decide)
  have hR : ((Q'.mkPos 95 63 (by decide) * (qpow Q 3 + -(1 : Q'))) * Q'.ofNat 63).eqv
      (Q'.ofNat 95 * (qpow Q 3 + -(1 : Q'))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.mkPos 95 63 (by decide)) (qpow Q 3 + -(1 : Q')) (Q'.ofNat 63)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (qpow Q 3 + -(1 : Q')) (Q'.ofNat 63))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.mkPos 95 63 (by decide)) (Q'.ofNat 63) (qpow Q 3 + -(1 : Q')))) ?_
    exact Q'.mul_eqv_congr_right _ _ _
      (by decide : (Q'.mkPos 95 63 (by decide) * Q'.ofNat 63).eqv (Q'.ofNat 95))
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hR)
  have eL : (((qpow Q 3 + -(1 : Q')) + Q'.ofNat 2 * qpow Q 2) * Q'.ofNat 63).eqv
      ((Q'.ofNat 63 * qpow Q 3 + -(Q'.ofNat 63)) + Q'.ofNat 126 * qpow Q 2) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv (qpow Q 3 + -(1 : Q')) (Q'.ofNat 2 * qpow Q 2) (Q'.ofNat 63)) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (qpow Q 3 + -(1 : Q')) (Q'.ofNat 63)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat 63) (qpow Q 3) (-(1 : Q'))) ?_
      refine Q'.add_eqv_congr_left _ _ _ ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (Q'.ofNat 63) 1) ?_
      exact Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv (Q'.ofNat 63))
    · refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (Q'.ofNat 2 * qpow Q 2) (Q'.ofNat 63)) ?_
      exact ncG 63 2 (qpow Q 2)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv eL) ?_
  have hsub : Q'.ofNat 126 * qpow Q 2 ≤ Q'.ofNat 32 * qpow Q 3 + -(Q'.ofNat 32) := by
    have h := Q'.add_le_add_right _ _ (-(Q'.ofNat 32)) (cubic_cert hQ4)
    have eLc : ((Q'.ofNat 126 * qpow Q 2 + Q'.ofNat 32) + -(Q'.ofNat 32)).eqv
        (Q'.ofNat 126 * qpow Q 2) :=
      Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ _ _)
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (Q'.add_neg_self_eqv (Q'.ofNat 32)))
          (Q'.eqv_of_eq (Q'.add_zero' _)))
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv eLc) h
  have eR95 : (Q'.ofNat 95 * (qpow Q 3 + -(1 : Q'))).eqv
      ((Q'.ofNat 63 * qpow Q 3 + -(Q'.ofNat 63)) + (Q'.ofNat 32 * qpow Q 3 + -(Q'.ofNat 32))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat 95) (qpow Q 3) (-(1 : Q'))) ?_
    have hneg : (Q'.ofNat 95 * -(1 : Q')).eqv (-(Q'.ofNat 95)) :=
      Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (Q'.ofNat 95) 1)
        (Q'.neg_eqv_congr _ _ (Q'.mul_one_eqv (Q'.ofNat 95)))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hneg) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.eqv_symm (combX 63 32 (qpow Q 3)))
        (by decide : (-(Q'.ofNat 95)).eqv (-(Q'.ofNat 63) + -(Q'.ofNat 32)))) ?_
    exact Q'.add_swap_inner (Q'.ofNat 63 * qpow Q 3) (Q'.ofNat 32 * qpow Q 3)
      (-(Q'.ofNat 63)) (-(Q'.ofNat 32))
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv eR95)
  exact Q'.add_le_add_left _ _ _ hsub

/-- **`Ucoup_upper_even_c95`** — the even majorant at the sharp clean constant `95/63`.  For `n ≥ 1`,
`U(2n) ≤ (95/63)·(n²·Q^{n²})`. -/
theorem Ucoup_upper_even_c95 {Q : Q'} (hQ4 : Q'.ofNat 4 ≤ Q) {n : Nat} (hn : 1 ≤ n) :
    Ucoup Q (2 * n) ≤ Q'.mkPos 95 63 (by decide) * (Q'.ofNat (n * n) * qpow Q (n * n)) := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  have hQ1 : (1 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  have h64 : Q'.ofNat 64 ≤ qpow Q 3 := by
    have h16 := qpow2_ge16F hQ4
    have hq2nn : (0 : Q') ≤ qpow Q 2 := qpow_nonneg Q hQ0 2
    have s1 : qpow Q 2 * Q'.ofNat 4 ≤ qpow Q 2 * Q := Q'.mul_le_mul_of_nonneg_left _ _ _ hQ4 hq2nn
    have s2 : Q'.ofNat 16 * Q'.ofNat 4 ≤ qpow Q 2 * Q'.ofNat 4 :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ h16 (by decide)
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (by decide : (Q'.ofNat 64).eqv (Q'.ofNat 16 * Q'.ofNat 4))) ?_
    exact Q'.le_trans' _ _ _ s2 s1
  have hden : (0 : Q') < qpow Q 3 + -(1 : Q') := by
    have h63 : Q'.ofNat 63 ≤ qpow Q 3 + -(1 : Q') :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (Q'.ofNat 63).eqv (Q'.ofNat 64 + -(1 : Q'))))
        (Q'.add_le_add_right _ _ _ h64)
    exact Q'.pos_of_lt_of_le (by decide) h63
  have hB : (0 : Q') ≤ Q'.ofNat (n * n) * qpow Q (n * n) :=
    Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ0 _)
  exact upper_cleanF hden hB (Ucoup_upper_even_tight hQ1 hn) (c_e_valid hQ4)

/-! ## 4. The even reduced closure at the FiniteS constants (`40000/22801`, `95/63`) -/

/-- **`even_reduced_finiteS`** — the reduced EVEN inequality at the theta-floor constants.  With the
even exponent identities `m₃² = m₂m₄`, `(m₃+m₃)+1 = m₂+m₄` and clean constant `95/63`, it collapses
to the closed numeric fact `40000·(95/63)² ≤ 91204`. -/
theorem even_reduced_finiteS {Q : Q'} (hQ0 : (0 : Q') ≤ Q) (m2 m3 m4 : Nat)
    (hprod : m3 * m3 = m2 * m4) (hsum1 : (m3 + m3) + 1 = m2 + m4) :
    Q'.ofNat 40000 *
        ((Q'.mkPos 95 63 (by decide) * (Q'.ofNat m2 * qpow Q m2))
       * (Q'.mkPos 95 63 (by decide) * (Q'.ofNat m4 * qpow Q m4)))
      ≤ (Q'.ofNat 22801 * Q) *
        ((Q'.ofNat m3 * qpow Q m3 + Q'.ofNat m3 * qpow Q m3)
       * (Q'.ofNat m3 * qpow Q m3 + Q'.ofNat m3 * qpow Q m3)) := by
  let A := Q'.ofNat m3 * qpow Q m3
  let mk := Q'.mkPos 95 63 (by decide : (0:Nat) < 63)
  have hVnn : (0 : Q') ≤ Q'.ofNat (m2 * m4) * qpow Q (m2 + m4) :=
    Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ0 _)
  have hB2B4 : ((Q'.ofNat m2 * qpow Q m2) * (Q'.ofNat m4 * qpow Q m4)).eqv
      (Q'.ofNat (m2 * m4) * qpow Q (m2 + m4)) :=
    Q'.eqv_trans _ _ _ (blkMulF Q (Q'.ofNat m2) (Q'.ofNat m4) m2 m4)
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv m2 m4)))
  have hLHS : (Q'.ofNat 40000 *
        ((mk * (Q'.ofNat m2 * qpow Q m2)) * (mk * (Q'.ofNat m4 * qpow Q m4)))).eqv
      ((Q'.ofNat 40000 * (mk * mk)) * (Q'.ofNat (m2 * m4) * qpow Q (m2 + m4))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 40000) _ _
        (Q'.eqv_trans _ _ _
          (mul4c mk (Q'.ofNat m2 * qpow Q m2) mk (Q'.ofNat m4 * qpow Q m4))
          (Q'.mul_eqv_congr_left (mk * mk) _ _ hB2B4))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 40000) (mk * mk) _)
  have hA2 : (A * A).eqv (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3)) :=
    Q'.eqv_trans _ _ _ (blkMulF Q (Q'.ofNat m3) (Q'.ofNat m3) m3 m3)
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv m3 m3)))
  have h_lo : (A + A).eqv (Q'.ofNat 2 * A) := Q'.eqv_symm (two_mul_eqvF A)
  have h_ll : ((A + A) * (A + A)).eqv
      (Q'.ofNat 4 * (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (A + A) h_lo)
        (Q'.mul_eqv_congr_left (Q'.ofNat 2 * A) _ _ h_lo)) ?_
    refine Q'.eqv_trans _ _ _ (mul4c (Q'.ofNat 2) A (Q'.ofNat 2) A) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (A * A) (by decide : (Q'.ofNat 2 * Q'.ofNat 2).eqv (Q'.ofNat 4))) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat 4) _ _ hA2
  have hVeq : Q'.ofNat (m3 * m3) * qpow Q ((m3 + m3) + 1)
      = Q'.ofNat (m2 * m4) * qpow Q (m2 + m4) := by rw [hprod, hsum1]
  have hQW3 : (Q * (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3))).eqv
      (Q'.ofNat (m2 * m4) * qpow Q (m2 + m4)) := by
    refine Q'.eqv_trans _ _ _ (mulLCf Q (Q'.ofNat (m3 * m3)) (qpow Q (m3 + m3))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (m3 * m3)) _ _ (Q'.mul_comm_eqv Q (qpow Q (m3 + m3)))) ?_
    exact Q'.eqv_of_eq hVeq
  have hRHS : ((Q'.ofNat 22801 * Q) * ((A + A) * (A + A))).eqv
      (Q'.ofNat 91204 * (Q'.ofNat (m2 * m4) * qpow Q (m2 + m4))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 22801 * Q) _ _ h_ll) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat 22801) Q (Q'.ofNat 4 * (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 22801) _ _
        (mulLCf Q (Q'.ofNat 4) (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 22801) (Q'.ofNat 4)
        (Q * (Q'.ofNat (m3 * m3) * qpow Q (m3 + m3))))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (by decide : (Q'.ofNat 22801 * Q'.ofNat 4).eqv (Q'.ofNat 91204))) ?_
    exact Q'.mul_eqv_congr_left (Q'.ofNat 91204) _ _ hQW3
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) (Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hRHS))
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (by decide : Q'.ofNat 40000 * (Q'.mkPos 95 63 (by decide) * Q'.mkPos 95 63 (by decide))
        ≤ Q'.ofNat 91204)
    hVnn

/-! ## 5. The odd reduced closure at the FiniteS constants (via `odd_scalarF`) -/

/-- **`odd_reduced_finiteS`** — the reduced ODD inequality at the theta-floor constants.  With the
odd exponent identities `m₂+m₄ = m₃+m₃`, `m₂m₄ ≤ m₃²`, the central/pair split (`m₃ = mₚ+1`,
`18mₚ ≥ 16m₃`), the reduced inequality collapses to `odd_scalarF` (`14745600·Q ≤ 22801·(9Q+16)²`). -/
theorem odd_reduced_finiteS {Q : Q'} (hQ4 : Q'.ofNat 4 ≤ Q) (m2 m3 m4 mp : Nat)
    (hsum2 : m2 + m4 = m3 + m3) (hprodle : m2 * m4 ≤ m3 * m3) (hmp : m3 = mp + 1)
    (hbig : 16 * m3 ≤ 18 * mp) :
    Q'.ofNat 40000 *
        ((Q'.mkPos 32 15 (by decide) * (Q'.ofNat m2 * qpow Q m2))
       * (Q'.mkPos 32 15 (by decide) * (Q'.ofNat m4 * qpow Q m4)))
      ≤ (Q'.ofNat 22801 * Q) *
        ((Q'.ofNat m3 * qpow Q m3 + (Q'.ofNat mp * qpow Q mp + Q'.ofNat mp * qpow Q mp))
       * (Q'.ofNat m3 * qpow Q m3 + (Q'.ofNat mp * qpow Q mp + Q'.ofNat mp * qpow Q mp))) := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  have hqmp0 : (0 : Q') ≤ qpow Q mp := qpow_nonneg Q hQ0 mp
  have hQQ0 : (0 : Q') ≤ Q * Q := Q'.mul_nonneg _ _ hQ0 hQ0
  let mk := Q'.mkPos 32 15 (by decide : (0:Nat) < 15)
  let base := Q'.ofNat m3 * Q + Q'.ofNat (2 * mp)
  let X9 := Q'.ofNat 9 * Q + Q'.ofNat 16
  have hX90 : (0 : Q') ≤ X9 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (0:Q').eqv ((0:Q')+(0:Q'))))
      (Q'.add_le_add (Q'.mul_nonneg _ _ (by decide) hQ0) (by decide))
  have hbase0 : (0 : Q') ≤ base :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide : (0:Q').eqv ((0:Q')+(0:Q'))))
      (Q'.add_le_add (Q'.mul_nonneg _ _ (ofNat_nonneg _) hQ0) (ofNat_nonneg _))
  have hmk20 : (0 : Q') ≤ mk * mk :=
    Q'.mul_nonneg _ _ (by decide : (0:Q') ≤ Q'.mkPos 32 15 (by decide))
      (by decide : (0:Q') ≤ Q'.mkPos 32 15 (by decide))
  have hqm3 : (qpow Q m3).eqv (qpow Q mp * Q) := by
    rw [hmp]; exact Q'.eqv_refl _
  have hqmqm : (qpow Q mp * qpow Q mp).eqv (qpow Q (mp + mp)) := Q'.eqv_symm (qpow_add Q mp mp)
  have hG0 : (0 : Q') ≤ qpow Q (mp + mp) := qpow_nonneg Q hQ0 _
  have hq2QQ : (qpow Q 2).eqv (Q * Q) := by
    show ((qpow Q 0 * Q) * Q).eqv (Q * Q)
    exact Q'.mul_eqv_congr_right _ _ Q
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ Q (Q'.eqv_of_eq (qpow_zero Q))) (Q'.one_mul_eqv Q))
  -- ===== Step 1: lo ≃ qpow Q mp · base =====
  have hlo_fac : (Q'.ofNat m3 * qpow Q m3 + (Q'.ofNat mp * qpow Q mp + Q'.ofNat mp * qpow Q mp)).eqv
      (qpow Q mp * base) := by
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (qpow Q mp) (Q'.ofNat m3 * Q) (Q'.ofNat (2 * mp))) ?_
    refine Q'.add_eqv_congr' ?_ ?_
    · refine Q'.eqv_trans _ _ _ (mulLCf (qpow Q mp) (Q'.ofNat m3) Q) ?_
      exact Q'.mul_eqv_congr_left (Q'.ofNat m3) _ _ (Q'.eqv_symm hqm3)
    · refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (qpow Q mp) (Q'.ofNat (2 * mp))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (qpow Q mp)
          (Q'.eqv_of_eq (congrArg Q'.ofNat (by omega : 2 * mp = mp + mp)))) ?_
      exact Q'.eqv_symm (combX mp mp (qpow Q mp))
  -- ===== Lift setup =====
  have hB2B4 : ((Q'.ofNat m2 * qpow Q m2) * (Q'.ofNat m4 * qpow Q m4)).eqv
      (Q'.ofNat (m2 * m4) * qpow Q (m2 + m4)) :=
    Q'.eqv_trans _ _ _ (blkMulF Q (Q'.ofNat m2) (Q'.ofNat m4) m2 m4)
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv m2 m4)))
  have hE : m2 + m4 = (mp + mp) + 2 := by omega
  have hqe2 : (qpow Q (m2 + m4)).eqv (qpow Q (mp + mp) * (Q * Q)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (congrArg (qpow Q) hE))
      (Q'.eqv_trans _ _ _ (qpow_add Q (mp + mp) 2)
        (Q'.mul_eqv_congr_left (qpow Q (mp + mp)) _ _ hq2QQ))
  have inner1 : ((mk * (Q'.ofNat m2 * qpow Q m2)) * (mk * (Q'.ofNat m4 * qpow Q m4))).eqv
      ((mk * mk) * (Q'.ofNat (m2 * m4) * (qpow Q (mp + mp) * (Q * Q)))) :=
    Q'.eqv_trans _ _ _ (mul4c mk (Q'.ofNat m2 * qpow Q m2) mk (Q'.ofNat m4 * qpow Q m4))
      (Q'.mul_eqv_congr_left (mk * mk) _ _
        (Q'.eqv_trans _ _ _ hB2B4 (Q'.mul_eqv_congr_left (Q'.ofNat (m2 * m4)) _ _ hqe2)))
  have inner2 : ((mk * mk) * (Q'.ofNat (m2 * m4) * (qpow Q (mp + mp) * (Q * Q)))).eqv
      (qpow Q (mp + mp) * ((mk * mk) * (Q'.ofNat (m2 * m4) * (Q * Q)))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (mk * mk) _ _
        (mulLCf (Q'.ofNat (m2 * m4)) (qpow Q (mp + mp)) (Q * Q)))
      (mulLCf (mk * mk) (qpow Q (mp + mp)) (Q'.ofNat (m2 * m4) * (Q * Q)))
  have hLHSe : (Q'.ofNat 40000 *
        ((mk * (Q'.ofNat m2 * qpow Q m2)) * (mk * (Q'.ofNat m4 * qpow Q m4)))).eqv
      (qpow Q (mp + mp) *
        (Q'.ofNat 40000 * ((mk * mk) * (Q'.ofNat (m2 * m4) * (Q * Q))))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 40000) _ _ (Q'.eqv_trans _ _ _ inner1 inner2))
      (mulLCf (Q'.ofNat 40000) (qpow Q (mp + mp)) ((mk * mk) * (Q'.ofNat (m2 * m4) * (Q * Q))))
  have hlolo : ((Q'.ofNat m3 * qpow Q m3 + (Q'.ofNat mp * qpow Q mp + Q'.ofNat mp * qpow Q mp))
        * (Q'.ofNat m3 * qpow Q m3 + (Q'.ofNat mp * qpow Q mp + Q'.ofNat mp * qpow Q mp))).eqv
      (qpow Q (mp + mp) * (base * base)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hlo_fac)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (qpow Q mp * base) _ _ hlo_fac)
        (Q'.eqv_trans _ _ _ (mul4c (qpow Q mp) base (qpow Q mp) base)
          (Q'.mul_eqv_congr_right _ _ (base * base) hqmqm)))
  have hRHSe : ((Q'.ofNat 22801 * Q) *
        ((Q'.ofNat m3 * qpow Q m3 + (Q'.ofNat mp * qpow Q mp + Q'.ofNat mp * qpow Q mp))
       * (Q'.ofNat m3 * qpow Q m3 + (Q'.ofNat mp * qpow Q mp + Q'.ofNat mp * qpow Q mp)))).eqv
      (qpow Q (mp + mp) * ((Q'.ofNat 22801 * Q) * (base * base))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 22801 * Q) _ _ hlolo)
      (mulLCf (Q'.ofNat 22801 * Q) (qpow Q (mp + mp)) (base * base))
  -- ===== Step 3: reduced closure  R2 : KQ2 ≤ RB =====
  -- h9base : m3·(9Q+16) ≤ 9·base
  have h9base : Q'.ofNat m3 * X9 ≤ Q'.ofNat 9 * base := by
    have eL : (Q'.ofNat m3 * X9).eqv (Q'.ofNat (m3 * 9) * Q + Q'.ofNat (m3 * 16)) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat m3) (Q'.ofNat 9 * Q) (Q'.ofNat 16)) ?_
      refine Q'.add_eqv_congr' ?_ ?_
      · refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat m3) (Q'.ofNat 9) Q)) ?_
        exact Q'.mul_eqv_congr_right _ _ Q (Q'.eqv_symm (ofNat_mul_eqv m3 9))
      · exact Q'.eqv_symm (ofNat_mul_eqv m3 16)
    have eR : (Q'.ofNat 9 * base).eqv (Q'.ofNat (9 * m3) * Q + Q'.ofNat (9 * (2 * mp))) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv (Q'.ofNat 9) (Q'.ofNat m3 * Q) (Q'.ofNat (2 * mp))) ?_
      refine Q'.add_eqv_congr' ?_ ?_
      · refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 9) (Q'.ofNat m3) Q)) ?_
        exact Q'.mul_eqv_congr_right _ _ Q (Q'.eqv_symm (ofNat_mul_eqv 9 m3))
      · exact Q'.eqv_symm (ofNat_mul_eqv 9 (2 * mp))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv eL) (Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv eR))
    refine Q'.add_le_add ?_ (Q'.ofNat_le_ofNat (by omega : m3 * 16 ≤ 9 * (2 * mp)))
    exact Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ Q
      (Q'.eqv_of_eq (congrArg Q'.ofNat (by omega : m3 * 9 = 9 * m3))))
  have hD90 : (0 : Q') ≤ Q'.ofNat m3 * X9 := Q'.mul_nonneg _ _ (ofNat_nonneg _) hX90
  have h9base0 : (0 : Q') ≤ Q'.ofNat 9 * base := Q'.mul_nonneg _ _ (by decide) hbase0
  have hD9sq : (Q'.ofNat m3 * X9) * (Q'.ofNat m3 * X9)
      ≤ (Q'.ofNat 9 * base) * (Q'.ofNat 9 * base) :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ h9base hD90)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ h9base h9base0)
  have hD9sq_eqv : ((Q'.ofNat m3 * X9) * (Q'.ofNat m3 * X9)).eqv
      (Q'.ofNat (m3 * m3) * (X9 * X9)) :=
    Q'.eqv_trans _ _ _ (mul4c (Q'.ofNat m3) X9 (Q'.ofNat m3) X9)
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv m3 m3)))
  have h9sq_eqv : ((Q'.ofNat 9 * base) * (Q'.ofNat 9 * base)).eqv (Q'.ofNat 81 * (base * base)) :=
    Q'.eqv_trans _ _ _ (mul4c (Q'.ofNat 9) base (Q'.ofNat 9) base)
      (Q'.mul_eqv_congr_right _ _ _ (by decide : (Q'.ofNat 9 * Q'.ofNat 9).eqv (Q'.ofNat 81)))
  have hsq_bound : Q'.ofNat (m3 * m3) * (X9 * X9) ≤ Q'.ofNat 81 * (base * base) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hD9sq_eqv)
      (Q'.le_trans' _ _ _ hD9sq (Q'.le_of_eqv h9sq_eqv))
  -- odd_scalarF reduced core (matching X9)
  have hm3m3Q0 : (0 : Q') ≤ Q'.ofNat (m3 * m3) * Q := Q'.mul_nonneg _ _ (ofNat_nonneg _) hQ0
  have h22Q0 : (0 : Q') ≤ Q'.ofNat 22801 * Q := Q'.mul_nonneg _ _ (ofNat_nonneg _) hQ0
  -- KQ2'' ≤ RB (× 81)
  have hR2'' : (Q'.ofNat 40000 * ((mk * mk) * (Q'.ofNat (m3 * m3) * (Q * Q))))
      ≤ (Q'.ofNat 22801 * Q) * (base * base) := by
    refine Q'.le_of_mul_le_mul_left ?_ (show (0:Q') < Q'.ofNat 81 by decide)
    -- 81·KQ2'' ≃ (m3m3·Q)·(14745600·Q)
    have eLL : (Q'.ofNat 81 * (Q'.ofNat 40000 * ((mk * mk) * (Q'.ofNat (m3 * m3) * (Q * Q))))).eqv
        ((Q'.ofNat (m3 * m3) * Q) * (Q'.ofNat 14745600 * Q)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 81) _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 40000) (mk * mk)
            (Q'.ofNat (m3 * m3) * (Q * Q))))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 81) (Q'.ofNat 40000 * (mk * mk))
          (Q'.ofNat (m3 * m3) * (Q * Q)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (Q'.ofNat (m3 * m3) * (Q * Q))
          (by decide : (Q'.ofNat 81 * (Q'.ofNat 40000 *
              (Q'.mkPos 32 15 (by decide) * Q'.mkPos 32 15 (by decide)))).eqv (Q'.ofNat 14745600))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 14745600) (Q'.ofNat (m3 * m3)) (Q * Q))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (Q * Q)
          (Q'.mul_comm_eqv (Q'.ofNat 14745600) (Q'.ofNat (m3 * m3)))) ?_
      exact Q'.eqv_symm (mul4c (Q'.ofNat (m3 * m3)) Q (Q'.ofNat 14745600) Q)
    have hMid : ((Q'.ofNat (m3 * m3) * Q) * (Q'.ofNat 22801 * (X9 * X9))).eqv
        ((Q'.ofNat 22801 * Q) * (Q'.ofNat (m3 * m3) * (X9 * X9))) :=
      Q'.eqv_trans _ _ _ (mul4c (Q'.ofNat (m3 * m3)) Q (Q'.ofNat 22801) (X9 * X9))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ (Q * (X9 * X9))
            (Q'.mul_comm_eqv (Q'.ofNat (m3 * m3)) (Q'.ofNat 22801)))
          (Q'.eqv_symm (mul4c (Q'.ofNat 22801) Q (Q'.ofNat (m3 * m3)) (X9 * X9))))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv eLL) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (odd_scalarF hQ4) hm3m3Q0) ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hMid) ?_
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hsq_bound h22Q0) ?_
    exact Q'.le_of_eqv (Q'.eqv_symm (mulLCf (Q'.ofNat 81) (Q'.ofNat 22801 * Q) (base * base)))
  -- KQ2 ≤ KQ2''  (via m2·m4 ≤ m3·m3)
  have hR2 : (Q'.ofNat 40000 * ((mk * mk) * (Q'.ofNat (m2 * m4) * (Q * Q))))
      ≤ (Q'.ofNat 22801 * Q) * (base * base) := by
    refine Q'.le_trans' _ _ _ ?_ hR2''
    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ (by decide : (0:Q') ≤ Q'.ofNat 40000)
    refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ hmk20
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.ofNat_le_ofNat hprodle) hQQ0
  -- ===== assemble =====
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHSe) (Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hRHSe))
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hR2 hG0

/-! ## 6. The FiniteS envelope legs, generic monotone step, and the truncated FiniteS Turán -/

/-- The `U(s+2)` upper-envelope field at the FiniteS constants. -/
def hi2F (Q : Q') (s : Nat) : Q' :=
  if s % 2 = 0 then
    Q'.mkPos 95 63 (by decide) * (Q'.ofNat ((s/2 + 1) * (s/2 + 1)) * qpow Q ((s/2 + 1) * (s/2 + 1)))
  else
    Q'.mkPos 32 15 (by decide) * (Q'.ofNat ((s/2 + 1) * (s/2 + 2)) * qpow Q ((s/2 + 1) * (s/2 + 2)))

/-- The `U(s+4)` upper-envelope field at the FiniteS constants. -/
def hi4F (Q : Q') (s : Nat) : Q' :=
  if s % 2 = 0 then
    Q'.mkPos 95 63 (by decide) * (Q'.ofNat ((s/2 + 2) * (s/2 + 2)) * qpow Q ((s/2 + 2) * (s/2 + 2)))
  else
    Q'.mkPos 32 15 (by decide) * (Q'.ofNat ((s/2 + 2) * (s/2 + 3)) * qpow Q ((s/2 + 2) * (s/2 + 3)))

theorem hi2F_even (Q : Q') (t : Nat) :
    hi2F Q (2 * t) =
      Q'.mkPos 95 63 (by decide) * (Q'.ofNat ((t + 1) * (t + 1)) * qpow Q ((t + 1) * (t + 1))) := by
  unfold hi2F; rw [if_pos (by omega : (2 * t) % 2 = 0), (by omega : (2 * t) / 2 = t)]

theorem hi2F_odd (Q : Q') (t : Nat) :
    hi2F Q (2 * t + 1) =
      Q'.mkPos 32 15 (by decide) * (Q'.ofNat ((t + 1) * (t + 2)) * qpow Q ((t + 1) * (t + 2))) := by
  unfold hi2F; rw [if_neg (by omega : ¬ (2 * t + 1) % 2 = 0), (by omega : (2 * t + 1) / 2 = t)]

theorem hi4F_even (Q : Q') (t : Nat) :
    hi4F Q (2 * t) =
      Q'.mkPos 95 63 (by decide) * (Q'.ofNat ((t + 2) * (t + 2)) * qpow Q ((t + 2) * (t + 2))) := by
  unfold hi4F; rw [if_pos (by omega : (2 * t) % 2 = 0), (by omega : (2 * t) / 2 = t)]

theorem hi4F_odd (Q : Q') (t : Nat) :
    hi4F Q (2 * t + 1) =
      Q'.mkPos 32 15 (by decide) * (Q'.ofNat ((t + 2) * (t + 3)) * qpow Q ((t + 2) * (t + 3))) := by
  unfold hi4F; rw [if_neg (by omega : ¬ (2 * t + 1) % 2 = 0), (by omega : (2 * t + 1) / 2 = t)]

/-- **`mono_turan_gen`** — the abstract monotone-envelope step at the FiniteS constants
(`40000/22801`).  Copy of `FusionUTuranWFree.mono_turan` with the two scalar literals swapped. -/
theorem mono_turan_gen {Q A B C L B' C' : Q'}
    (hC : (0 : Q') ≤ C) (hLnn : (0 : Q') ≤ L) (hB' : (0 : Q') ≤ B') (hQ : (0 : Q') ≤ Q)
    (hLA : L ≤ A) (hBB' : B ≤ B') (hCC' : C ≤ C')
    (hred : Q'.ofNat 40000 * (B' * C') ≤ (Q'.ofNat 22801 * Q) * (L * L)) :
    Q'.ofNat 40000 * (B * C) ≤ (Q'.ofNat 22801 * Q) * (A * A) := by
  have hAnn : (0 : Q') ≤ A := Q'.le_trans' _ _ _ hLnn hLA
  have h22Q : (0 : Q') ≤ Q'.ofNat 22801 * Q := Q'.mul_nonneg _ _ (ofNat_nonneg _) hQ
  have h40000 : (0 : Q') ≤ Q'.ofNat 40000 := ofNat_nonneg _
  have hBC : B * C ≤ B' * C' :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right B B' C hBB' hC)
      (Q'.mul_le_mul_of_nonneg_left C C' B' hCC' hB')
  have hstep2 : Q'.ofNat 40000 * (B * C) ≤ Q'.ofNat 40000 * (B' * C') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hBC h40000
  have hLL : L * L ≤ A * A :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right L A L hLA hLnn)
      (Q'.mul_le_mul_of_nonneg_left L A A hLA hAnn)
  have hstep4 : (Q'.ofNat 22801 * Q) * (L * L) ≤ (Q'.ofNat 22801 * Q) * (A * A) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hLL h22Q
  exact Q'.le_trans' _ _ _ hstep2 (Q'.le_trans' _ _ _ hred hstep4)

/-- Nonnegativity of the `hi2F` upper-envelope field. -/
theorem hi2F_nonneg {Q : Q'} (hQ4 : Q'.ofNat 4 ≤ Q) (s : Nat) : (0 : Q') ≤ hi2F Q s := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
    rw [hi2F_even]
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ0 _))
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
    rw [hi2F_odd]
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ0 _))

/-- **`finiteS_trunc_ge2`** — the truncated FiniteS coupling Turán for `s ≥ 2`, `Q ≥ 4`. -/
theorem finiteS_trunc_ge2 {Q : Q'} (hQ4 : Q'.ofNat 4 ≤ Q) {s : Nat} (hs : 2 ≤ s) :
    Q'.ofNat 40000 * (Wtrunc Q s s * Wtrunc Q s (s + 2))
      ≤ (Q'.ofNat 22801 * Q) * (Wtrunc Q s (s + 1) * Wtrunc Q s (s + 1)) := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  have hLA : loFn Q s ≤ Wtrunc Q s (s + 1) := by
    rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
    · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
      exact Wtrunc_lower_even hQ0 (by omega : 1 ≤ t)
    · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
      exact Wtrunc_lower_odd hQ0 (by omega : 1 ≤ t)
  have hBB' : Wtrunc Q s s ≤ hi2F Q s := by
    rw [Wtrunc_diag]
    rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
    · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
      rw [hi2F_even, (by omega : 2 * t + 2 = 2 * (t + 1))]
      exact Ucoup_upper_even_c95 hQ4 (by omega : 1 ≤ t + 1)
    · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
      rw [hi2F_odd]
      refine Q'.le_trans' _ _ _ (utle_upper2 hQ4 (2 * t + 1)) ?_
      rw [hi2Fn_odd]; exact Q'.le_refl' _
  have hCC' : Wtrunc Q s (s + 2) ≤ hi4F Q s := by
    refine Q'.le_trans' _ _ _ (Wtrunc_le_Ucoup hQ0 s (s + 2) (by omega)) ?_
    rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
    · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
      rw [hi4F_even, (by omega : 2 * t + 4 = 2 * (t + 2))]
      exact Ucoup_upper_even_c95 hQ4 (by omega : 1 ≤ t + 2)
    · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
      rw [hi4F_odd]
      refine Q'.le_trans' _ _ _ (utle_upper4 hQ4 (2 * t + 1)) ?_
      rw [hi4Fn_odd]; exact Q'.le_refl' _
  have hred : Q'.ofNat 40000 * (hi2F Q s * hi4F Q s)
      ≤ (Q'.ofNat 22801 * Q) * (loFn Q s * loFn Q s) := by
    rcases Nat.mod_two_eq_zero_or_one s with hmod | hmod
    · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t := ⟨s / 2, by omega⟩
      rw [hi2F_even, hi4F_even, loFn_even]
      exact even_reduced_finiteS hQ0 ((t + 1) * (t + 1)) ((t + 1) * (t + 2)) ((t + 2) * (t + 2))
        (even_exp_prod t) (by have := even_exp_sum t; omega)
    · obtain ⟨t, rfl⟩ : ∃ t, s = 2 * t + 1 := ⟨s / 2, by omega⟩
      have ht1 : 1 ≤ t := by omega
      have htt : t ≤ t * t := by
        calc t = t * 1 := (Nat.mul_one t).symm
          _ ≤ t * t := Nat.mul_le_mul_left t ht1
      rw [hi2F_odd, hi4F_odd, loFn_odd]
      exact odd_reduced_finiteS hQ4 ((t + 1) * (t + 2)) ((t + 2) * (t + 2)) ((t + 2) * (t + 3))
        ((t + 1) * (t + 3))
        (by have := odd_exp_sum t; omega)
        (odd_exp_prodge t)
        (by have := expand t 2 2; have := expand t 1 3; omega)
        (by have := expand t 2 2; have := expand t 1 3; omega)
  exact mono_turan_gen (Wtrunc_nonneg hQ0 s (s + 2)) (utle_lo_nonneg hQ4 s) (hi2F_nonneg hQ4 s)
    hQ0 hLA hBB' hCC' hred

/-! ### edge modes `s = 0, 1` — local monomial helpers (reproofs of `FusionUTuranTrunc` privates) -/

private theorem blkF (Q : Q') (a b i j : Nat) :
    ((Q'.ofNat a * qpow Q i) * (Q'.ofNat b * qpow Q j)).eqv (Q'.ofNat (a * b) * qpow Q (i + j)) := by
  refine Q'.eqv_trans _ _ _ (mul4c (Q'.ofNat a) (qpow Q i) (Q'.ofNat b) (qpow Q j)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv a b))) ?_
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm (qpow_add Q i j))

private theorem scaleF (Q : Q') (n c k : Nat) :
    (Q'.ofNat n * (Q'.ofNat c * qpow Q k)).eqv (Q'.ofNat (n * c) * qpow Q k) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat n) (Q'.ofNat c) (qpow Q k))) ?_
  exact Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv n c))

private theorem scaleQF (Q : Q') (n c k : Nat) :
    ((Q'.ofNat n * Q) * (Q'.ofNat c * qpow Q k)).eqv (Q'.ofNat (n * c) * qpow Q (k + 1)) := by
  refine Q'.eqv_trans _ _ _ (mul4c (Q'.ofNat n) Q (Q'.ofNat c) (qpow Q k)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm (ofNat_mul_eqv n c))) ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  show (Q * qpow Q k).eqv (qpow Q (k + 1))
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv Q (qpow Q k)) ?_
  exact Q'.eqv_refl _

private theorem mulLeF {a b c d : Q'} (hab : a ≤ b) (hcd : c ≤ d) (hc : (0 : Q') ≤ c)
    (hb : (0 : Q') ≤ b) : a * c ≤ b * d :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hab hc)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcd hb)

private theorem stepQF {Q : Q'} (hQ4 : Q'.ofNat 4 ≤ Q) {a b i : Nat}
    (hab : Q'.ofNat a ≤ Q'.ofNat 4 * Q'.ofNat b) :
    Q'.ofNat a * qpow Q i ≤ Q'.ofNat b * qpow Q (i + 1) := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  have hqi0 : (0 : Q') ≤ qpow Q i := qpow_nonneg Q hQ0 i
  have hb0 : (0 : Q') ≤ Q'.ofNat b := ofNat_nonneg _
  have h1 : Q'.ofNat a * qpow Q i ≤ (Q'.ofNat 4 * Q'.ofNat b) * qpow Q i :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hab hqi0
  have e1 : ((Q'.ofNat 4 * Q'.ofNat b) * qpow Q i).eqv (Q'.ofNat b * (Q'.ofNat 4 * qpow Q i)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (Q'.ofNat 4) (Q'.ofNat b))) ?_
    exact Q'.mul_assoc_eqv (Q'.ofNat b) (Q'.ofNat 4) (qpow Q i)
  have h4Q : Q'.ofNat 4 * qpow Q i ≤ Q * qpow Q i :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hQ4 hqi0
  have h2 : Q'.ofNat b * (Q'.ofNat 4 * qpow Q i) ≤ Q'.ofNat b * (Q * qpow Q i) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h4Q hb0
  have e2 : (Q'.ofNat b * (Q * qpow Q i)).eqv (Q'.ofNat b * qpow Q (i + 1)) := by
    refine Q'.mul_eqv_congr_left _ _ _ ?_
    exact Q'.mul_comm_eqv Q (qpow Q i)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv e1)
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv e2)))

private theorem wt0F (Q : Q') (m : Nat) : (wterm Q m 0).eqv 0 := by
  show (Q'.ofNat (0 * (m - 0)) * qpow Q (0 * (m - 0))).eqv 0
  rw [(by omega : 0 * (m - 0) = 0)]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (qpow Q 0) (by decide : (Q'.ofNat 0).eqv 0)) (q_zero_mul (qpow Q 0))

private theorem wtsum2F (Q : Q') (m : Nat) : (fsum (wterm Q m) 2).eqv (wterm Q m 1) := by
  show (((0 : Q') + wterm Q m 0) + wterm Q m 1).eqv (wterm Q m 1)
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (wterm Q m 1)
      (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) (wt0F Q m))) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (wterm Q m 1))

private theorem wtsum3F (Q : Q') (m : Nat) :
    (fsum (wterm Q m) 3).eqv (wterm Q m 1 + wterm Q m 2) := by
  show ((((0 : Q') + wterm Q m 0) + wterm Q m 1) + wterm Q m 2).eqv (wterm Q m 1 + wterm Q m 2)
  refine Q'.add_eqv_congr_right _ _ (wterm Q m 2) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (wterm Q m 1)
      (Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) (wt0F Q m))) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (wterm Q m 1))

/-- **`finiteS_trunc_s0`** — the edge mode `s = 0`.  Reduces to `120000·Q⁴ ≤ 91204·Q⁵`. -/
theorem finiteS_trunc_s0 {Q : Q'} (hQ4 : Q'.ofNat 4 ≤ Q) :
    Q'.ofNat 40000 * (Wtrunc Q 0 0 * Wtrunc Q 0 2)
      ≤ (Q'.ofNat 22801 * Q) * (Wtrunc Q 0 1 * Wtrunc Q 0 1) := by
  have e00 : (Wtrunc Q 0 0).eqv (Q'.ofNat 1 * qpow Q 1) := wtsum2F Q 2
  have e01 : (Wtrunc Q 0 1).eqv (Q'.ofNat 2 * qpow Q 2) := wtsum2F Q 3
  have e02 : (Wtrunc Q 0 2).eqv (Q'.ofNat 3 * qpow Q 3) := wtsum2F Q 4
  have hL : (Q'.ofNat 40000 * (Wtrunc Q 0 0 * Wtrunc Q 0 2)).eqv (Q'.ofNat 120000 * qpow Q 4) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ e00)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ e02) (blkF Q 1 3 1 3)))) ?_
    exact scaleF Q 40000 3 4
  have hR : ((Q'.ofNat 22801 * Q) * (Wtrunc Q 0 1 * Wtrunc Q 0 1)).eqv (Q'.ofNat 91204 * qpow Q 5) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ e01)
          (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ e01) (blkF Q 2 2 2 2)))) ?_
    exact scaleQF Q 22801 4 4
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) (Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hR))
  exact stepQF hQ4 (by decide : Q'.ofNat 120000 ≤ Q'.ofNat 4 * Q'.ofNat 91204)

/-- **`finiteS_trunc_s1`** — the edge mode `s = 1`.  Uses `W11 ≤ 4Q²`, `W13 ≤ 7Q⁶`, `4Q⁴ ≤ W12`;
reduces to `1120000·Q⁸ ≤ 364816·Q⁹`. -/
theorem finiteS_trunc_s1 {Q : Q'} (hQ4 : Q'.ofNat 4 ≤ Q) :
    Q'.ofNat 40000 * (Wtrunc Q 1 1 * Wtrunc Q 1 3)
      ≤ (Q'.ofNat 22801 * Q) * (Wtrunc Q 1 2 * Wtrunc Q 1 2) := by
  have hQ0 : (0 : Q') ≤ Q := Q'.le_trans' _ _ _ (by decide) hQ4
  have hW11le : Wtrunc Q 1 1 ≤ Q'.ofNat 4 * qpow Q 2 :=
    Q'.le_of_eqv (Q'.eqv_trans _ _ _ (wtsum3F Q 3) (combX 2 2 (qpow Q 2)))
  have hW13le : Wtrunc Q 1 3 ≤ Q'.ofNat 7 * qpow Q 6 := by
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (wtsum3F Q 5)) ?_
    have ht1 : wterm Q 5 1 = Q'.ofNat 4 * qpow Q 4 := rfl
    have ht2 : wterm Q 5 2 = Q'.ofNat 6 * qpow Q 6 := rfl
    rw [ht1, ht2]
    have h4q4 : Q'.ofNat 4 * qpow Q 4 ≤ Q'.ofNat 1 * qpow Q 6 := by
      have h16 : Q'.ofNat 16 ≤ qpow Q 2 := qpow2_ge16F hQ4
      have hq40 : (0 : Q') ≤ qpow Q 4 := qpow_nonneg Q hQ0 4
      have s1 : Q'.ofNat 4 * qpow Q 4 ≤ Q'.ofNat 16 * qpow Q 4 :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide : Q'.ofNat 4 ≤ Q'.ofNat 16) hq40
      have s2 : Q'.ofNat 16 * qpow Q 4 ≤ qpow Q 2 * qpow Q 4 :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ h16 hq40
      have e6 : (qpow Q 2 * qpow Q 4).eqv (Q'.ofNat 1 * qpow Q 6) :=
        Q'.eqv_trans _ _ _ (Q'.eqv_symm (qpow_add Q 2 4)) (Q'.eqv_symm (Q'.one_mul_eqv (qpow Q 6)))
      exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ s2 (Q'.le_of_eqv e6))
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_right (Q'.ofNat 4 * qpow Q 4) _ (Q'.ofNat 6 * qpow Q 6) h4q4) ?_
    exact Q'.le_of_eqv (combX 1 6 (qpow Q 6))
  have hW12ge : Q'.ofNat 4 * qpow Q 4 ≤ Wtrunc Q 1 2 :=
    BondMovingMoment.fsum_term_le_of_nonneg (wterm_nonneg hQ0 4) 2 3 (by omega)
  have hW13_0 : (0 : Q') ≤ Wtrunc Q 1 3 := Wtrunc_nonneg hQ0 1 3
  have h4q2_0 : (0 : Q') ≤ Q'.ofNat 4 * qpow Q 2 :=
    Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ0 _)
  have h4q4_0 : (0 : Q') ≤ Q'.ofNat 4 * qpow Q 4 :=
    Q'.mul_nonneg _ _ (ofNat_nonneg _) (qpow_nonneg Q hQ0 _)
  have hLHS : Q'.ofNat 40000 * (Wtrunc Q 1 1 * Wtrunc Q 1 3) ≤ Q'.ofNat 1120000 * qpow Q 8 := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (mulLeF hW11le hW13le hW13_0 h4q2_0) (ofNat_nonneg _)) ?_
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (blkF Q 4 7 2 6)) ?_
    exact scaleF Q 40000 28 8
  have hRHS : Q'.ofNat 364816 * qpow Q 9
      ≤ (Q'.ofNat 22801 * Q) * (Wtrunc Q 1 2 * Wtrunc Q 1 2) := by
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (mulLeF hW12ge hW12ge h4q4_0 (Wtrunc_nonneg hQ0 1 2))
        (Q'.mul_nonneg _ _ (ofNat_nonneg _) hQ0))
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (blkF Q 4 4 4 4)) ?_
    exact scaleQF Q 22801 16 8
  refine Q'.le_trans' _ _ _ hLHS (Q'.le_trans' _ _ _ ?_ hRHS)
  exact stepQF hQ4 (by decide : Q'.ofNat 1120000 ≤ Q'.ofNat 4 * Q'.ofNat 364816)

/-- **`finiteS_trunc_unconditional`** — the truncated FiniteS coupling Turán `(‡_finiteS)`, all `s`. -/
theorem finiteS_trunc_unconditional {Q : Q'} (hQ4 : Q'.ofNat 4 ≤ Q) (s : Nat) :
    Q'.ofNat 40000 * (Wtrunc Q s s * Wtrunc Q s (s + 2))
      ≤ (Q'.ofNat 22801 * Q) * (Wtrunc Q s (s + 1) * Wtrunc Q s (s + 1)) := by
  match s with
  | 0 => exact finiteS_trunc_s0 hQ4
  | 1 => exact finiteS_trunc_s1 hQ4
  | (n + 2) => exact finiteS_trunc_ge2 hQ4 (by omega : 2 ≤ n + 2)

/-! ## 7. Reindex to `acN` and inhabit `AcNReserveAnalytic.FiniteSMargin` -/

open YMGap.Continuum.FusionUTuranReindex
open YMGap.Continuum.AutoconvGershgorin

/-- `qpow w 2 ≃ w · w` (reproof of `FusionUTuranReindex.qpow2_ww`). -/
private theorem qpow2_wwF (w : Q') : (qpow w 2).eqv (w * w) := by
  show ((qpow w 0 * w) * w).eqv (w * w)
  exact Q'.mul_eqv_congr_right _ _ w
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ w (Q'.eqv_of_eq (qpow_zero w))) (Q'.one_mul_eqv w))

/-- `0 < w ⟹ 0 < w²` (reproof of `FusionUTuranReindex.qpow2_pos`). -/
private theorem qpow2_posF {w : Q'} (hw0 : (0 : Q') < w) : (0 : Q') < qpow w 2 :=
  lt_of_lt_of_le (Q'.mul_pos hw0 hw0) (Q'.ge_of_eqv (qpow2_wwF w))

/-- **`crossN_finiteS`** — the fusion-box FiniteS reserve `(†_finiteS)`
`40000·acN(s+1,s)·acN(s+1,s+2) ≤ 22801·acN(s+1,s+1)²` for `0 < w ≤ 1/2`, from `(‡_finiteS)` through
the `Q = 1/w²` reindexing.  Copy of `FusionUTuranReindex.crossN` with the two scalar constants
swapped and the truncated Turán replaced by its FiniteS version. -/
theorem crossN_finiteS {w : Q'} (hw0 : (0 : Q') < w) (hwle : w ≤ FusionCoreStepRoundA.wH) (s : Nat) :
    Q'.ofNat 40000 * (acN w (s + 1) s * acN w (s + 1) (s + 2))
      ≤ Q'.ofNat 22801 * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1)) := by
  have hw0' : (0 : Q') ≤ w := Q'.le_of_lt hw0
  have hq : (0 : Q') < qpow w 2 := qpow2_posF hw0
  have hatom : (qpow w 2 * Q'.divPos 1 (qpow w 2) hq).eqv 1 :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (qpow w 2) (Q'.divPos 1 (qpow w 2) hq))
      (Q'.divPos_mul_eqv 1 (qpow w 2) hq)
  have hQ0 : (0 : Q') ≤ Q'.divPos 1 (qpow w 2) hq :=
    Q'.le_of_lt (Q'.divPos_pos 1 (qpow w 2) hq (by decide))
  have h4 : Q'.ofNat 4 * qpow w 2 ≤ (1 : Q') := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.le_of_eqv (qpow2_wwF w)) (by decide)) ?_
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
  have hcross := finiteS_trunc_unconditional hQ4 s
  have hXY : qpow w 2 * (Q'.ofNat 40000 *
        (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s s * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 2)))
      ≤ Q'.ofNat 22801 *
        (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)
          * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)) := by
    refine Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hcross hq20) ?_
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (qpow w 2) (Q'.ofNat 22801 * Q'.divPos 1 (qpow w 2) hq)
        (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)
          * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)))) ?_
    refine Q'.mul_eqv_congr_right _ _ _ ?_
    refine Q'.eqv_trans _ _ _ (mulLCf (qpow w 2) (Q'.ofNat 22801) (Q'.divPos 1 (qpow w 2) hq)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.ofNat 22801) _ _ hatom) ?_
    exact Q'.mul_one_eqv (Q'.ofNat 22801)
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
  have hLHS : (Q'.ofNat 40000 * (acN w (s + 1) s * acN w (s + 1) (s + 2))).eqv
      (qpow w (2 * fExp (s + 1)) *
        (qpow w 2 * (Q'.ofNat 40000 *
          (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s s
            * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 2))))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hA_s)
          (Q'.mul_eqv_congr_left _ _ _ hA_s2))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (mul4c (qpow w (fExp s)) (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s s)
          (qpow w (fExp (s + 2))) (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 2)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ gs)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_assoc_eqv (qpow w (2 * fExp (s + 1))) (qpow w 2)
          (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s s
            * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 2)))) ?_
    refine Q'.eqv_trans _ _ _
      (mulLCf (Q'.ofNat 40000) (qpow w (2 * fExp (s + 1)))
        (qpow w 2 * (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s s
          * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 2)))) ?_
    exact Q'.mul_eqv_congr_left _ _ _
      (mulLCf (Q'.ofNat 40000) (qpow w 2)
        (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s s
          * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 2)))
  have hRHS : (Q'.ofNat 22801 * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1))).eqv
      (qpow w (2 * fExp (s + 1)) *
        (Q'.ofNat 22801 *
          (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)
            * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hA_s1)
          (Q'.mul_eqv_congr_left _ _ _ hA_s1))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _
        (mul4c (qpow w (fExp (s + 1))) (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1))
          (qpow w (fExp (s + 1))) (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ _ gs1)) ?_
    exact mulLCf (Q'.ofNat 22801) (qpow w (2 * fExp (s + 1)))
      (Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1)
        * Wtrunc (Q'.divPos 1 (qpow w 2) hq) s (s + 1))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) (Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv hRHS))
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hXY hG0

/-- **`finiteSMargin_of_trunc` — `AcNReserveAnalytic.FiniteSMargin w` INHABITED** for every
`0 < w ≤ 1/2`, via the `Q = 1/w²` reindexing of the truncated FiniteS coupling Turán. -/
def finiteSMargin_of_trunc {w : Q'} (hw0 : (0 : Q') < w)
    (hwle : w ≤ FusionCoreStepRoundA.wH) : AcNReserveAnalytic.FiniteSMargin w where
  margin := fun s => crossN_finiteS hw0 hwle s

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms Ucoup_upper_even_c95
#print axioms even_reduced_finiteS
#print axioms odd_reduced_finiteS
#print axioms finiteS_trunc_unconditional
#print axioms crossN_finiteS
#print axioms finiteSMargin_of_trunc

end YMGap.Continuum.FusionUTuranFiniteS
