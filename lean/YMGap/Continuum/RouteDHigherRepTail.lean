/-
Track B / R2 — ROUTE D: the HIGHER-REPRESENTATION suppression half of
`GapChannelDomination`.

# What this module proves (read first)

`HeatKernelSecondCumulant.GapChannelDomination` isolates the single open input of
the whole continuum gap: the real 4D SU(2) per-step margin degradation is dominated
by the FUNDAMENTAL-channel (`s = 1`) heat-kernel second cumulant
`δ_model = pMult·chanCumulant 1 (w_k)`.  There are two physical halves to that claim:

  * the LARGE-FIELD / Bałaban half (the small-field vs large-field decomposition
    controlling the gap-channel back-reaction) — a SEPARATE attack;
  * the HIGHER-REP half — that the contribution of the `s ≥ 2` representation
    channels is negligible relative to the `s = 1` channel.

THIS module proves the higher-rep half, constructively, via the PROVED
character-tail machinery (`RG/CharacterTailAntitone`, `RG/CharacterTailMajorant`,
`Constructive/CharacterTail.geom_series_le`).

The heat-kernel character coefficient of channel `s` is `dimQ(s)·w^{C₄(s)}` with
`dimQ(s) = s+1`, `C₄(s) = s(s+2)` (`C₄(1)=3`, `C₄(2)=8`, …).  The PHYSICAL channel
contribution to the gap defect is the heat-kernel-WEIGHTED per-channel second
cumulant

    weightedChan(s,w) := w^{C₄(s)} · chanCumulant(s,w) ,

so the `s ≥ 2` tail carries `w^{C₄(2)} = w⁸`, i.e. `w^{C₄(2)−C₄(1)} = w⁵` smaller
than the `s = 1` term `w³·chanCumulant(1,w)`.

# THE PROVED HIGHER-REP TAIL BOUND (axiom-clean `Q'`/`Nat`)

  * `weightedChan_le_linEnv` — per channel, `weightedChan(s,w) ≤ linEnv(s,w)`, the
    LINEAR heat-kernel envelope `w^{C₄(s)}·dimQ(s)·C₄(s)·(1−w)` (from the proved
    over-estimate `1 − w^{C₄(s)} ≤ C₄(s)·(1−w)`, `oneSub_qpow_le`).
  * `linEnv_ratio` — the per-axis character-tail ratio: `linEnv(j+3,w) ≤
    (3·w⁷)·linEnv(j+2,w)` (successive `s ≥ 2` channels drop by a factor `≤ 3·w⁷`;
    the polynomial part `dimQ·C₄` grows by `≤ 3` while the exponent gap
    `C₄(s+1)−C₄(s) = 2s+3 ≥ 7` supplies `w⁷`).  This is the exponential-beats-
    polynomial term-ratio the geometric character tail rests on.
  * `higherRep_tail_le` — **THE HIGHER-REP SUPPRESSION SUB-LEMMA.**  For the
    STRONG-COUPLING regime `0 ≤ w ≤ 1/2`,

        Σ_{s≥2} weightedChan(s,w)  ≤  weightedChan(1,w) ,

    i.e. the ENTIRE higher-representation tail is dominated by the fundamental
    channel.  Proved by `geom_series_le` (the ratio `3·w⁷ ≤ 1/2` closes the
    geometric series into `weightedChan(1,w)` once the strong-coupling comparison
    `2·linEnv(2,w) ≤ weightedChan(1,w)` — via the EXACT `s = 1` factorization
    `renDefect_factor`, `chanCumulant(1,w) = (1−w)²(2+w)·2`, and `12w⁵ ≤ 1−w` on
    `[0,1/2]` — is discharged).

# THE HONEST REGIME (adversarial, AGENTS.md Rule 6)

The higher-rep tail is dominated by `s = 1` ONLY at STRONG COUPLING.  Numerically
(`routeD_channeltail.md`, mpmath dps 50), the ratio
`Σ_{s≥2} weightedChan(s,w) / weightedChan(1,w)` is `≤ 1` for `w ≤ 0.6377…` and
DIVERGES as `w → 1` (`≈ 49` at `w = 0.9`, `≈ 4·10⁷` at `w = 0.999`) — the same
`w → 1` blow-up as Route B's total-second-cumulant refutation.  The proven Lean
threshold `w ≤ 1/2` is a clean rational SUFFICIENT regime strictly inside the true
crossover `0.6377…`, and comfortably contains the strong-coupling anchor
`w = 1/6 ≈ 0.167`.  This is NOT uniform in `w`: at weak coupling the naive
all-channel weighted defect is an over-count (as Route B established).  Nothing is
faked; the honest regime is reported and the `w → 1` failure is documented.

# WHAT THIS REDUCES

`GapChannelDomination` remains UNINHABITED (it IS the real Bałaban estimate; NO 4D
mass gap is claimed).  This module discharges its HIGHER-REP half as a genuine
`Q'` theorem, leaving the LARGE-FIELD half (the parallel Bałaban attack) as the
residual — exactly the split named in the module header.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and structural induction, reusing the PROVED
`secondOrder_qpow`, `oneSub_qpow_le`, `qpow_add`, `qpow_antitone`, `renDefect_factor`,
and `CharacterTail.geom_series_le`.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext`/`Quot.sound` only.  No `Classical.*`,
no `native_decide`, no `sorry`.  All witnesses are `Type` data.
-/

import YMGap.Continuum.HeatKernelSecondCumulant
import YMGap.Continuum.RenDefectQuadFactor
import YMGap.Constructive.CharacterTail

namespace YMGap.Continuum.RouteDHigherRepTail

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.RenDefectQuadFactor
open YMGap.Continuum.HeatKernelSecondCumulant

/-! ## 0. Small reusable `Q'` / `Nat` helpers (axiom-clean). -/

/-- `ofNat n ≥ 0`. -/
theorem ofNat_nn (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]; exact Int.natCast_nonneg _

/-- `n ≤ m ⟹ ofNat n ≤ ofNat m`. -/
theorem ofNat_le {n m : Nat} (h : n ≤ m) : (Q'.ofNat n) ≤ Q'.ofNat m := by
  show (Int.ofNat n) * (((Q'.ofNat m).den : Int)) ≤ (Int.ofNat m) * ((Q'.ofNat n).den : Int)
  show (Int.ofNat n) * (1 : Int) ≤ (Int.ofNat m) * (1 : Int)
  rw [Int.mul_one, Int.mul_one]; exact Int.ofNat_le.mpr h

/-- `ofNat (a*b) ≃ ofNat a · ofNat b`. -/
theorem ofNat_mul_eqv (a b : Nat) :
    (Q'.ofNat (a * b)).eqv (Q'.ofNat a * Q'.ofNat b) := by
  show (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
     = (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int)
  rw [Q'.mul_den_cast]
  show ((a * b : Nat) : Int) * (((Q'.ofNat a).den : Int) * ((Q'.ofNat b).den : Int))
     = ((a : Int) * (b : Int)) * (1 : Int)
  show ((a * b : Nat) : Int) * ((1 : Int) * (1 : Int))
     = ((a : Int) * (b : Int)) * (1 : Int)
  rw [Int.natCast_mul a b, Int.mul_one, Int.mul_one]

/-- `-Y ≤ 0` for `Y ≥ 0`. -/
theorem neg_nonpos {Y : Q'} (h : (0 : Q') ≤ Y) : -Y ≤ (0 : Q') := by
  rw [Q'.zero_le_iff_num_nonneg] at h
  show (-Y).num * (((0 : Q').den) : Int) ≤ ((0 : Q').num) * (((-Y).den) : Int)
  show (-(Y.num)) * ((1 : Nat) : Int) ≤ (0 : Int) * (((-Y).den) : Int)
  rw [Int.zero_mul]
  show (-(Y.num)) * (1 : Int) ≤ 0
  rw [Int.mul_one]; omega

/-- `X - Y ≤ X` for `Y ≥ 0`. -/
theorem sub_le_self' (X : Q') {Y : Q'} (hY : (0 : Q') ≤ Y) : X - Y ≤ X := by
  have h1 : X + (-Y) ≤ X + 0 := Q'.add_le_add_left X (-Y) 0 (neg_nonpos hY)
  rw [Q'.add_zero' X] at h1
  exact h1

/-- `qpow` monotone in the BASE on `[0,∞)`: `0 ≤ a ≤ b ⟹ qpow a n ≤ qpow b n`. -/
theorem qpow_base_mono {a b : Q'} (ha : (0 : Q') ≤ a) (hab : a ≤ b) :
    ∀ n, qpow a n ≤ qpow b n
  | 0 => Q'.le_refl' (1 : Q')
  | n + 1 => by
      show qpow a n * a ≤ qpow b n * b
      exact Q'.mul_le_mul_of_nonneg (qpow_base_mono ha hab n) hab
        (qpow_nonneg b (Q'.le_trans' _ _ _ ha hab) n) ha

/-- 4-factor multiplicative swap: `(a·b)·(c·d) ≃ (a·c)·(b·d)`. -/
theorem mul_swap4 (a b c d : Q') : ((a * b) * (c * d)).eqv ((a * c) * (b * d)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _
      (Q'.mul_eqv_congr_right _ _ d (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a _ _ (Q'.mul_assoc_eqv c b d)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))

/-- `c4 (j+3) = c4 (j+2) + (2j+7)`. -/
theorem c4_step (j : Nat) : c4 (j + 3) = c4 (j + 2) + (2 * j + 7) := by
  show (j + 3) * ((j + 3) + 2) = (j + 2) * ((j + 2) + 2) + (2 * j + 7)
  have e1 : (j + 3) * ((j + 3) + 2) = j * j + 8 * j + 15 := by
    rw [Nat.mul_add (j + 3) j 5, Nat.add_mul j 3 j, Nat.add_mul j 3 5]
    omega
  have e2 : (j + 2) * ((j + 2) + 2) = j * j + 6 * j + 8 := by
    rw [Nat.mul_add (j + 2) j 4, Nat.add_mul j 2 j, Nat.add_mul j 2 4]
    omega
  rw [e1, e2]; omega

/-- The polynomial part of the character-tail ratio: `dimQ·C₄` grows by `≤ 3`.
`((j+3)+1)·C₄(j+3) ≤ 3·(((j+2)+1)·C₄(j+2))`. -/
theorem natratio_c4 (j : Nat) :
    ((j + 3) + 1) * (c4 (j + 3)) ≤ 3 * (((j + 2) + 1) * (c4 (j + 2))) := by
  show ((j + 3) + 1) * ((j + 3) * ((j + 3) + 2))
     ≤ 3 * (((j + 2) + 1) * ((j + 2) * ((j + 2) + 2)))
  have e1 : (j + 3) + 2 = j + 5 := by omega
  have e2 : (j + 2) + 2 = j + 4 := by omega
  have e3 : (j + 3) + 1 = j + 4 := by omega
  have e4 : (j + 2) + 1 = j + 3 := by omega
  rw [e1, e2, e3, e4]
  have h : j + 5 ≤ 3 * (j + 2) := by omega
  have step : ((j + 3) * (j + 4)) * (j + 5) ≤ ((j + 3) * (j + 4)) * (3 * (j + 2)) :=
    Nat.mul_le_mul_left _ h
  have l : (j + 4) * ((j + 3) * (j + 5)) = ((j + 3) * (j + 4)) * (j + 5) := by
    simp [Nat.mul_assoc, Nat.mul_left_comm]
  have r : 3 * ((j + 3) * ((j + 2) * (j + 4))) = ((j + 3) * (j + 4)) * (3 * (j + 2)) := by
    simp [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
  rw [l, r]; exact step

/-! ## 1. The heat-kernel-weighted per-channel second cumulant and its envelope. -/

/-- The rational coefficient `dimQ(s)·C₄(s) = (s+1)·s(s+2)` of the linear envelope. -/
def coefLin (s : Nat) : Q' := dimQ s * Q'.ofNat (c4 s)

/-- The LINEAR heat-kernel envelope `w^{C₄(s)}·dimQ(s)·C₄(s)·(1−w)`, laid out as
`(coefLin s · w^{C₄(s)}) · (1−w)`. -/
def linEnv (s : Nat) (w : Q') : Q' :=
  (coefLin s * qpow w (c4 s)) * ((1 : Q') - w)

/-- **The heat-kernel-WEIGHTED per-channel second cumulant** — the physical
contribution of representation channel `s` to the gap defect:
`weightedChan(s,w) = w^{C₄(s)}·chanCumulant(s,w)`. -/
def weightedChan (s : Nat) (w : Q') : Q' := qpow w (c4 s) * chanCumulant s w

theorem coefLin_nonneg (s : Nat) : (0 : Q') ≤ coefLin s :=
  Q'.mul_nonneg _ _ (dimQ_nonneg s) (ofNat_nn (c4 s))

theorem weightedChan_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) : (0 : Q') ≤ weightedChan s w :=
  Q'.mul_nonneg _ _ (qpow_nonneg w hw0 (c4 s)) (chanCumulant_nonneg hw0 hw1 s)

/-- `chanCumulant(s,w) ≤ coefLin(s)·(1−w)`: the linear over-estimate of the second
cumulant (`1 − w^{C₄(s)} ≥ 0`, so subtracting it only decreases). -/
theorem chanCumulant_le_coefU {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) : chanCumulant s w ≤ coefLin s * ((1 : Q') - w) := by
  -- Y := 1 − w^{C₄ s} ≥ 0
  have hqle : qpow w (c4 s) ≤ (1 : Q') := by
    have h := qpow_antitone hw0 hw1 0 (c4 s) (Nat.zero_le _)
    -- qpow w (c4 s) ≤ qpow w 0 = 1
    exact h
  have hYnn : (0 : Q') ≤ (1 : Q') - qpow w (c4 s) := Q'.sub_nonneg_of_le hqle
  -- chanCumulant = dimQ s · (X − Y) ≤ dimQ s · X
  have hstep : chanCumulant s w
      ≤ dimQ s * (Q'.ofNat (c4 s) * ((1 : Q') - w)) := by
    show dimQ s * ((Q'.ofNat (c4 s) * ((1 : Q') - w)) - ((1 : Q') - qpow w (c4 s)))
        ≤ dimQ s * (Q'.ofNat (c4 s) * ((1 : Q') - w))
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (sub_le_self' (Q'.ofNat (c4 s) * ((1 : Q') - w)) hYnn) (dimQ_nonneg s)
  -- dimQ s · (ofNat(c4 s) · (1−w)) ≃ (dimQ s · ofNat(c4 s)) · (1−w) = coefLin s · (1−w)
  refine Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv ?_)
  exact Q'.eqv_symm (Q'.mul_assoc_eqv (dimQ s) (Q'.ofNat (c4 s)) ((1 : Q') - w))

/-- **Per channel: the weighted second cumulant is bounded by the linear envelope.**
`weightedChan(s,w) ≤ linEnv(s,w)`. -/
theorem weightedChan_le_linEnv {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) : weightedChan s w ≤ linEnv s w := by
  -- weightedChan = w^{C₄}·chanCumulant ≤ w^{C₄}·(coefLin·(1−w))
  have h1 : weightedChan s w ≤ qpow w (c4 s) * (coefLin s * ((1 : Q') - w)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (chanCumulant_le_coefU hw0 hw1 s) (qpow_nonneg w hw0 (c4 s))
  -- w^{C₄}·(coefLin·(1−w)) ≃ (coefLin·w^{C₄})·(1−w) = linEnv
  refine Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv ?_)
  -- q·(C·u) ≃ (q·C)·u ≃ (C·q)·u
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (qpow w (c4 s)) (coefLin s) ((1 : Q') - w))) ?_
  exact Q'.mul_eqv_congr_right _ _ ((1 : Q') - w) (Q'.mul_comm_eqv (qpow w (c4 s)) (coefLin s))

/-! ## 2. The character-tail ratio `linEnv(j+3) ≤ (3·w⁷)·linEnv(j+2)`. -/

/-- Coefficient ratio: `coefLin(j+3) ≤ 3·coefLin(j+2)`. -/
theorem coefLin_ratio (j : Nat) : coefLin (j + 3) ≤ Q'.ofNat 3 * coefLin (j + 2) := by
  -- coefLin(j+3) = dimQ(j+3)·ofNat(c4(j+3)) = ofNat((j+3)+1)·ofNat(c4(j+3))
  have hL : (coefLin (j + 3)).eqv (Q'.ofNat (((j + 3) + 1) * c4 (j + 3))) := by
    show (Q'.ofNat ((j + 3) + 1) * Q'.ofNat (c4 (j + 3))).eqv
        (Q'.ofNat (((j + 3) + 1) * c4 (j + 3)))
    exact Q'.eqv_symm (ofNat_mul_eqv ((j + 3) + 1) (c4 (j + 3)))
  have hR : (Q'.ofNat 3 * coefLin (j + 2)).eqv
      (Q'.ofNat (3 * (((j + 2) + 1) * c4 (j + 2)))) := by
    -- 3·(ofNat((j+2)+1)·ofNat(c4(j+2))) ≃ 3·ofNat(((j+2)+1)·c4(j+2)) ≃ ofNat(3·…)
    have h1 : (Q'.ofNat 3 * coefLin (j + 2)).eqv
        (Q'.ofNat 3 * Q'.ofNat (((j + 2) + 1) * c4 (j + 2))) :=
      Q'.mul_eqv_congr_left (Q'.ofNat 3) _ _
        (Q'.eqv_symm (ofNat_mul_eqv ((j + 2) + 1) (c4 (j + 2))))
    exact Q'.eqv_trans _ _ _ h1
      (Q'.eqv_symm (ofNat_mul_eqv 3 (((j + 2) + 1) * c4 (j + 2))))
  have hnat : ((j + 3) + 1) * c4 (j + 3) ≤ 3 * (((j + 2) + 1) * c4 (j + 2)) :=
    natratio_c4 j
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hL) ?_
  refine Q'.le_trans' _ _ _ (ofNat_le hnat) (Q'.ge_of_eqv hR)

/-- Power ratio: `w^{C₄(j+3)} ≤ w⁷·w^{C₄(j+2)}` on `[0,1]`. -/
theorem qpow_c4_ratio {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (j : Nat) :
    qpow w (c4 (j + 3)) ≤ qpow w 7 * qpow w (c4 (j + 2)) := by
  rw [c4_step j]
  -- qpow w (c4(j+2)+(2j+7)) ≃ qpow w (c4(j+2))·qpow w (2j+7)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (qpow_add w (c4 (j + 2)) (2 * j + 7))) ?_
  -- ·qpow w (2j+7) ≤ ·qpow w 7   (antitone in exponent, 7 ≤ 2j+7)
  have hanti : qpow w (2 * j + 7) ≤ qpow w 7 := qpow_antitone hw0 hw1 7 (2 * j + 7) (by omega)
  have h1 : qpow w (c4 (j + 2)) * qpow w (2 * j + 7)
      ≤ qpow w (c4 (j + 2)) * qpow w 7 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hanti (qpow_nonneg w hw0 _)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.mul_comm_eqv _ _))

/-- **The character-tail term ratio.**  `linEnv(j+3,w) ≤ (3·w⁷)·linEnv(j+2,w)` on
`[0,1]`: successive higher-rep channels decay by a factor `≤ 3·w⁷` (exponential
beats polynomial).  The per-term input `geom_series_le` consumes. -/
theorem linEnv_ratio {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (j : Nat) :
    linEnv (j + 3) w ≤ (Q'.ofNat 3 * qpow w 7) * linEnv (j + 2) w := by
  have hu : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hC : coefLin (j + 3) ≤ Q'.ofNat 3 * coefLin (j + 2) := coefLin_ratio j
  have hP : qpow w (c4 (j + 3)) ≤ qpow w 7 * qpow w (c4 (j + 2)) := qpow_c4_ratio hw0 hw1 j
  have hA : coefLin (j + 3) * qpow w (c4 (j + 3))
      ≤ (Q'.ofNat 3 * coefLin (j + 2)) * (qpow w 7 * qpow w (c4 (j + 2))) :=
    Q'.mul_le_mul_of_nonneg hC hP
      (Q'.mul_nonneg _ _ (ofNat_nn 3) (coefLin_nonneg (j + 2)))
      (qpow_nonneg w hw0 (c4 (j + 3)))
  have hswap : ((Q'.ofNat 3 * coefLin (j + 2)) * (qpow w 7 * qpow w (c4 (j + 2)))).eqv
      ((Q'.ofNat 3 * qpow w 7) * (coefLin (j + 2) * qpow w (c4 (j + 2)))) :=
    mul_swap4 (Q'.ofNat 3) (coefLin (j + 2)) (qpow w 7) (qpow w (c4 (j + 2)))
  have hA2 : coefLin (j + 3) * qpow w (c4 (j + 3))
      ≤ (Q'.ofNat 3 * qpow w 7) * (coefLin (j + 2) * qpow w (c4 (j + 2))) :=
    Q'.le_trans' _ _ _ hA (Q'.le_of_eqv hswap)
  show (coefLin (j + 3) * qpow w (c4 (j + 3))) * ((1 : Q') - w)
      ≤ (Q'.ofNat 3 * qpow w 7) * ((coefLin (j + 2) * qpow w (c4 (j + 2))) * ((1 : Q') - w))
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _ ((1 : Q') - w) hA2 hu) ?_
  exact Q'.le_of_eqv
    (Q'.mul_assoc_eqv (Q'.ofNat 3 * qpow w 7)
      (coefLin (j + 2) * qpow w (c4 (j + 2))) ((1 : Q') - w))

/-! ## 3. Strong-coupling scalar facts (`w ≤ 1/2`). -/

/-- `1/2 ≤ 1 − w` for `w ≤ 1/2`. -/
theorem half_le_one_sub {w : Q'} (h : w ≤ Q'.mkPos 1 2 (by decide)) :
    Q'.mkPos 1 2 (by decide) ≤ (1 : Q') - w := by
  have hn : -(Q'.mkPos 1 2 (by decide)) ≤ -w := Q'.neg_le_neg h
  have h1 : (1 : Q') + -(Q'.mkPos 1 2 (by decide)) ≤ (1 : Q') + -w :=
    Q'.add_le_add_left 1 _ _ hn
  have he : ((1 : Q') + -(Q'.mkPos 1 2 (by decide))).eqv (Q'.mkPos 1 2 (by decide)) := by
    decide
  show Q'.mkPos 1 2 (by decide) ≤ (1 : Q') + -w
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) h1

/-- The geometric ratio `3·w⁷ ≤ 1/2` on `[0,1/2]`. -/
theorem r_le_half {w : Q'} (hw0 : (0 : Q') ≤ w) (hwstar : w ≤ Q'.mkPos 1 2 (by decide)) :
    Q'.ofNat 3 * qpow w 7 ≤ Q'.mkPos 1 2 (by decide) := by
  have hbm : qpow w 7 ≤ qpow (Q'.mkPos 1 2 (by decide)) 7 :=
    qpow_base_mono hw0 hwstar 7
  have h1 : Q'.ofNat 3 * qpow w 7 ≤ Q'.ofNat 3 * qpow (Q'.mkPos 1 2 (by decide)) 7 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hbm (ofNat_nn 3)
  have h2 : Q'.ofNat 3 * qpow (Q'.mkPos 1 2 (by decide)) 7 ≤ Q'.mkPos 1 2 (by decide) := by
    decide
  exact Q'.le_trans' _ _ _ h1 h2

/-- The strong-coupling core monomial inequality `48·w⁵ ≤ 4·(1−w)` on `[0,1/2]`
(the `12w⁵ ≤ 1−w` estimate, scaled). -/
theorem core_mono {w : Q'} (hw0 : (0 : Q') ≤ w) (hwstar : w ≤ Q'.mkPos 1 2 (by decide)) :
    Q'.ofNat 48 * qpow w 5 ≤ Q'.ofNat 4 * ((1 : Q') - w) := by
  have hbm : qpow w 5 ≤ qpow (Q'.mkPos 1 2 (by decide)) 5 :=
    qpow_base_mono hw0 hwstar 5
  have h1 : Q'.ofNat 48 * qpow w 5 ≤ Q'.ofNat 48 * qpow (Q'.mkPos 1 2 (by decide)) 5 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hbm (ofNat_nn 48)
  -- 48·(1/2)^5 = 3/2 ≤ 2 = 4·(1/2) ≤ 4·(1−w)
  have h2 : Q'.ofNat 48 * qpow (Q'.mkPos 1 2 (by decide)) 5
      ≤ Q'.ofNat 4 * Q'.mkPos 1 2 (by decide) := by decide
  have h3 : Q'.ofNat 4 * Q'.mkPos 1 2 (by decide) ≤ Q'.ofNat 4 * ((1 : Q') - w) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (half_le_one_sub hwstar) (ofNat_nn 4)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 h3)

/-! ## 4. The `s = 1` lower bound and the strong-coupling comparison. -/

/-- Lower bound on the fundamental-channel overshoot:
`2·(1−w)² ≤ C₄(1)·(1−w) − (1 − w^{C₄(1)})` (via the EXACT factorization
`renDefect_factor`, `(1−w)²(2+w) ≥ 2(1−w)²`). -/
theorem over1_ge {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    Q'.ofNat 2 * (((1 : Q') - w) * ((1 : Q') - w))
      ≤ (Q'.ofNat 3 * ((1 : Q') - w)) - ((1 : Q') - qpow w 3) := by
  have hfac : ((Q'.ofNat 3 * ((1 : Q') - w)) - ((1 : Q') - qpow w 3)).eqv
      ((((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 2 + w)) := renDefect_factor w
  have h2w : Q'.ofNat 2 ≤ Q'.ofNat 2 + w := by
    have := Q'.add_le_add_left (Q'.ofNat 2) 0 w hw0
    rwa [Q'.add_zero' (Q'.ofNat 2)] at this
  have hunn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have huu : (0 : Q') ≤ ((1 : Q') - w) * ((1 : Q') - w) := Q'.mul_nonneg _ _ hunn hunn
  -- (1−w)²·2 ≤ (1−w)²·(2+w) ≃ over1 ; and ofNat2·(1−w)² ≃ (1−w)²·ofNat2
  have hle : (((1 : Q') - w) * ((1 : Q') - w)) * Q'.ofNat 2
      ≤ (((1 : Q') - w) * ((1 : Q') - w)) * (Q'.ofNat 2 + w) :=
    Q'.mul_le_mul_of_nonneg_left (Q'.ofNat 2) (Q'.ofNat 2 + w)
      (((1 : Q') - w) * ((1 : Q') - w)) h2w huu
  have hcomm : (Q'.ofNat 2 * (((1 : Q') - w) * ((1 : Q') - w))).eqv
      ((((1 : Q') - w) * ((1 : Q') - w)) * Q'.ofNat 2) :=
    Q'.mul_comm_eqv (Q'.ofNat 2) (((1 : Q') - w) * ((1 : Q') - w))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm)
    (Q'.le_trans' _ _ _ hle (Q'.ge_of_eqv hfac))

/-- Lower bound on the fundamental-channel WEIGHTED cumulant:
`4·(w³·(1−w)²) ≤ weightedChan(1,w)`. -/
theorem weightedChan1_ge {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    Q'.ofNat 4 * (qpow w 3 * (((1 : Q') - w) * ((1 : Q') - w))) ≤ weightedChan 1 w := by
  -- weightedChan 1 w = qpow w 3 · (ofNat 2 · over1)   (c4 1 = 3, dimQ 1 = 2, defeq)
  show Q'.ofNat 4 * (qpow w 3 * (((1 : Q') - w) * ((1 : Q') - w)))
      ≤ qpow w 3 *
          (Q'.ofNat 2 * ((Q'.ofNat 3 * ((1 : Q') - w)) - ((1 : Q') - qpow w 3)))
  -- LHS ≃ q3·(ofNat4·(u·u)) ≃ q3·(ofNat2·(ofNat2·(u·u))) ≤ q3·(ofNat2·over1)
  have eqvA : (Q'.ofNat 4 * (qpow w 3 * (((1 : Q') - w) * ((1 : Q') - w)))).eqv
      (qpow w 3 * (Q'.ofNat 4 * (((1 : Q') - w) * ((1 : Q') - w)))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) (qpow w 3) (((1 : Q') - w) * ((1 : Q') - w)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (((1 : Q') - w) * ((1 : Q') - w))
        (Q'.mul_comm_eqv (Q'.ofNat 4) (qpow w 3))) ?_
    exact Q'.mul_assoc_eqv (qpow w 3) (Q'.ofNat 4) (((1 : Q') - w) * ((1 : Q') - w))
  have eqvB : (qpow w 3 * (Q'.ofNat 4 * (((1 : Q') - w) * ((1 : Q') - w)))).eqv
      (qpow w 3 * (Q'.ofNat 2 * (Q'.ofNat 2 * (((1 : Q') - w) * ((1 : Q') - w))))) := by
    refine Q'.mul_eqv_congr_left (qpow w 3) _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (((1 : Q') - w) * ((1 : Q') - w))
        (by decide : (Q'.ofNat 4).eqv (Q'.ofNat 2 * Q'.ofNat 2))) ?_
    exact Q'.mul_assoc_eqv (Q'.ofNat 2) (Q'.ofNat 2) (((1 : Q') - w) * ((1 : Q') - w))
  have hinner : Q'.ofNat 2 * (Q'.ofNat 2 * (((1 : Q') - w) * ((1 : Q') - w)))
      ≤ Q'.ofNat 2 * ((Q'.ofNat 3 * ((1 : Q') - w)) - ((1 : Q') - qpow w 3)) :=
    Q'.mul_le_mul_of_nonneg_left (Q'.ofNat 2 * (((1 : Q') - w) * ((1 : Q') - w)))
      ((Q'.ofNat 3 * ((1 : Q') - w)) - ((1 : Q') - qpow w 3)) (Q'.ofNat 2)
      (over1_ge hw0 hw1) (ofNat_nn 2)
  have hstep : qpow w 3 * (Q'.ofNat 2 * (Q'.ofNat 2 * (((1 : Q') - w) * ((1 : Q') - w))))
      ≤ qpow w 3 * (Q'.ofNat 2 * ((Q'.ofNat 3 * ((1 : Q') - w)) - ((1 : Q') - qpow w 3))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (qpow w 3) hinner (qpow_nonneg w hw0 3)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ eqvA eqvB)) hstep

/-- **The strong-coupling comparison** `2·linEnv(2,w) ≤ weightedChan(1,w)` on
`[0,1/2]` — the heat-kernel `s = 2` (leading higher-rep) envelope, doubled, is
dominated by the `s = 1` weighted cumulant.  Via the core `48w⁵ ≤ 4(1−w)`. -/
theorem two_linEnv2_le_gap {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwstar : w ≤ Q'.mkPos 1 2 (by decide)) :
    Q'.ofNat 2 * linEnv 2 w ≤ weightedChan 1 w := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hwstar (by decide)
  have hcnn : (0 : Q') ≤ qpow w 3 * ((1 : Q') - w) :=
    Q'.mul_nonneg _ _ (qpow_nonneg w hw0 3) (Q'.sub_nonneg_of_le hw1)
  -- E1 : ofNat2·linEnv2 ≃ (ofNat48·q5)·common,  common := q3·u
  have E1 : (Q'.ofNat 2 * linEnv 2 w).eqv
      ((Q'.ofNat 48 * qpow w 5) * (qpow w 3 * ((1 : Q') - w))) := by
    show (Q'.ofNat 2 * (((Q'.ofNat 3 * Q'.ofNat 8) * qpow w 8) * ((1 : Q') - w))).eqv
        ((Q'.ofNat 48 * qpow w 5) * (qpow w 3 * ((1 : Q') - w)))
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
        (Q'.mul_assoc_eqv (Q'.ofNat 3 * Q'.ofNat 8) (qpow w 8) ((1 : Q') - w))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) (Q'.ofNat 3 * Q'.ofNat 8)
        (qpow w 8 * ((1 : Q') - w)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (qpow w 8 * ((1 : Q') - w))
        (by decide : (Q'.ofNat 2 * (Q'.ofNat 3 * Q'.ofNat 8)).eqv (Q'.ofNat 48))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 48) _ _
        (Q'.mul_eqv_congr_right _ _ ((1 : Q') - w) (qpow_add w 3 5))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat 48) _ _
        (Q'.mul_assoc_eqv (qpow w 3) (qpow w 5) ((1 : Q') - w))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 48) (qpow w 3)
        (qpow w 5 * ((1 : Q') - w)))) ?_
    exact mul_swap4 (Q'.ofNat 48) (qpow w 3) (qpow w 5) ((1 : Q') - w)
  -- E2 : ofNat4·(q3·(u·u)) ≃ (ofNat4·u)·common
  have E2 : (Q'.ofNat 4 * (qpow w 3 * (((1 : Q') - w) * ((1 : Q') - w)))).eqv
      ((Q'.ofNat 4 * ((1 : Q') - w)) * (qpow w 3 * ((1 : Q') - w))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) (qpow w 3)
        (((1 : Q') - w) * ((1 : Q') - w)))) ?_
    exact mul_swap4 (Q'.ofNat 4) (qpow w 3) ((1 : Q') - w) ((1 : Q') - w)
  have hcore : (Q'.ofNat 48 * qpow w 5) * (qpow w 3 * ((1 : Q') - w))
      ≤ (Q'.ofNat 4 * ((1 : Q') - w)) * (qpow w 3 * ((1 : Q') - w)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ (qpow w 3 * ((1 : Q') - w)) (core_mono hw0 hwstar) hcnn
  have hchain : Q'.ofNat 2 * linEnv 2 w
      ≤ Q'.ofNat 4 * (qpow w 3 * (((1 : Q') - w) * ((1 : Q') - w))) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv E1)
      (Q'.le_trans' _ _ _ hcore (Q'.ge_of_eqv E2))
  exact Q'.le_trans' _ _ _ hchain (weightedChan1_ge hw0 hw1)

/-! ## 5. THE HIGHER-REP SUPPRESSION SUB-LEMMA (strong coupling). -/

/-- **THE HIGHER-REP TAIL BOUND.**  For the strong-coupling regime `0 ≤ w ≤ 1/2`,
the entire `s ≥ 2` heat-kernel-weighted second-cumulant tail is dominated by the
fundamental (`s = 1`) channel:

    ∀ N, Σ_{j<N} weightedChan(j+2, w)  ≤  weightedChan(1, w) .

Proved via the character-tail geometric closure `geom_series_le` (ratio `3w⁷ ≤ 1/2`,
`geometric-domination`) once the strong-coupling comparison `2·linEnv(2,w) ≤
weightedChan(1,w)` is discharged.  This is NOT uniform in `w`: see the module header
and `routeD_channeltail.md` for the `w → 1` blow-up (true crossover `≈ 0.6377`). -/
theorem higherRep_tail_le {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hwstar : w ≤ Q'.mkPos 1 2 (by decide)) :
    ∀ N, RationalTail.finSum (fun j => weightedChan (j + 2) w) N ≤ weightedChan 1 w := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hwstar (by decide)
  -- Geometric bound on the linear envelope, closing into weightedChan 1 w.
  have hgeom : ∀ N,
      RationalTail.finSum (fun j => linEnv (j + 2) w) N ≤ weightedChan 1 w := by
    refine CharacterTail.geom_series_le (fun j => linEnv (j + 2) w)
      (linEnv 2 w) (Q'.ofNat 3 * qpow w 7) (weightedChan 1 w)
      (Q'.mul_nonneg _ _ (ofNat_nn 3) (qpow_nonneg w hw0 7))
      (weightedChan_nonneg hw0 hw1 1)
      (Q'.le_refl' _)
      (fun k => linEnv_ratio hw0 hw1 k)
      ?hrec
    -- hrec : linEnv 2 w + r·(weightedChan 1 w) ≤ weightedChan 1 w
    have hgnn : (0 : Q') ≤ weightedChan 1 w := weightedChan_nonneg hw0 hw1 1
    have hrhalf : Q'.ofNat 3 * qpow w 7 ≤ Q'.mkPos 1 2 (by decide) := r_le_half hw0 hwstar
    have hrg : (Q'.ofNat 3 * qpow w 7) * weightedChan 1 w
        ≤ Q'.mkPos 1 2 (by decide) * weightedChan 1 w :=
      Q'.mul_le_mul_of_nonneg_right _ _ (weightedChan 1 w) hrhalf hgnn
    -- linEnv 2 w ≤ (1/2)·weightedChan 1 w
    have hlin : linEnv 2 w ≤ Q'.mkPos 1 2 (by decide) * weightedChan 1 w := by
      have heq : (Q'.mkPos 1 2 (by decide) * (Q'.ofNat 2 * linEnv 2 w)).eqv (linEnv 2 w) := by
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.mkPos 1 2 (by decide)) (Q'.ofNat 2) (linEnv 2 w))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ (linEnv 2 w)
            (by decide : (Q'.mkPos 1 2 (by decide) * Q'.ofNat 2).eqv (1 : Q'))) ?_
        exact Q'.one_mul_eqv (linEnv 2 w)
      have hle2 : Q'.mkPos 1 2 (by decide) * (Q'.ofNat 2 * linEnv 2 w)
          ≤ Q'.mkPos 1 2 (by decide) * weightedChan 1 w :=
        Q'.mul_le_mul_of_nonneg_left (Q'.ofNat 2 * linEnv 2 w) (weightedChan 1 w)
          (Q'.mkPos 1 2 (by decide)) (two_linEnv2_le_gap hw0 hwstar) (by decide)
      exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv heq) hle2
    have hsum : linEnv 2 w + (Q'.ofNat 3 * qpow w 7) * weightedChan 1 w
        ≤ Q'.mkPos 1 2 (by decide) * weightedChan 1 w
          + Q'.mkPos 1 2 (by decide) * weightedChan 1 w :=
      Q'.add_le_add hlin hrg
    have hhalf2 : (Q'.mkPos 1 2 (by decide) * weightedChan 1 w
        + Q'.mkPos 1 2 (by decide) * weightedChan 1 w).eqv (weightedChan 1 w) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_mul_eqv (Q'.mkPos 1 2 (by decide)) (Q'.mkPos 1 2 (by decide))
          (weightedChan 1 w))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (weightedChan 1 w)
          (by decide : (Q'.mkPos 1 2 (by decide) + Q'.mkPos 1 2 (by decide)).eqv (1 : Q'))) ?_
      exact Q'.one_mul_eqv (weightedChan 1 w)
    exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hhalf2)
  intro N
  exact Q'.le_trans' _ _ _
    (CharacterTail.finSum_le_termwise
      (fun j => weightedChan (j + 2) w) (fun j => linEnv (j + 2) w)
      (fun j => weightedChan_le_linEnv hw0 hw1 (j + 2)) N)
    (hgeom N)

/-! ## 6. Doc — the honest reduction (AGENTS.md Rule 6 / Rule 9). -/

/-- **PROVED (genuine `Q'` facts, axiom-clean):**
  * `weightedChan_le_linEnv` — the per-channel weighted second cumulant is bounded
    by the linear heat-kernel envelope.
  * `linEnv_ratio` — the character-tail term ratio `linEnv(j+3) ≤ 3w⁷·linEnv(j+2)`
    (exponential beats polynomial per higher-rep step).
  * `higherRep_tail_le` — the HIGHER-REP SUPPRESSION SUB-LEMMA: for `w ≤ 1/2`,
    `Σ_{s≥2} weightedChan(s,w) ≤ weightedChan(1,w)`.

**HONEST REGIME (adversarial):** the domination holds ONLY at strong coupling
(`w ≤ 1/2` proven; true crossover `≈ 0.6377`); the ratio `Σ_{s≥2}/s=1` DIVERGES as
`w → 1` (`≈ 49` at `w = 0.9`), the same blow-up as Route B's total-cumulant
refutation.  NOT uniform in `w`.

**WHAT THIS REDUCES:** `GapChannelDomination` (the real Bałaban estimate) remains
UNINHABITED; NO 4D Yang–Mills mass gap is claimed.  Its HIGHER-REP half is now a
proved theorem, leaving the LARGE-FIELD (Bałaban small-field/large-field) half as the
residual.  Nothing is faked; no free field. -/
theorem routeD_honesty : True := trivial

end YMGap.Continuum.RouteDHigherRepTail

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RouteDHigherRepTail.weightedChan_le_linEnv
#print axioms YMGap.Continuum.RouteDHigherRepTail.linEnv_ratio
#print axioms YMGap.Continuum.RouteDHigherRepTail.over1_ge
#print axioms YMGap.Continuum.RouteDHigherRepTail.weightedChan1_ge
#print axioms YMGap.Continuum.RouteDHigherRepTail.two_linEnv2_le_gap
#print axioms YMGap.Continuum.RouteDHigherRepTail.higherRep_tail_le
