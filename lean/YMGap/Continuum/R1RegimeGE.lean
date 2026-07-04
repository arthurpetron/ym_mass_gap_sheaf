/-
Track B / local-CLT — STAGE 3 of R1: the upper-half regime cell
`R1CaseSplit.RegimeGECell w` (`1/2 ≤ w`, both parities, all windows), reduced to the base
cases (FREE) + ONE named large-window residual, with the reusable theta anchor built.

# What this file provides (read first — load-bearing honesty)

`RegimeGECell w` asks for `FullRangeFloor w s` for EVERY window `s` on the upper half `1/2 ≤ w`.
`FullRangeFloor w s` is `Δ²V ≥ −2` centred at `N = s+1` (the paper's `Δ²V(N)+2 ≥ 0`).  The paper
proof (`computations/r1_remaining_pieces.md`, Task B) splits into base cases `N = 2..7` and a
large-`N` (`N ≥ 8`) theta-anchored tail.  This file:

  * **Base cases (FREE).**  The windows `s = 0..6` (centres `N = 1..7`) are already discharged
    UNCONDITIONALLY on the physical window `0 ≤ w ≤ 1` by the Pólya/Bernstein certificates
    `CircleFourierPowerModel.fullRangeFloor_zero … _six` (which are `w`-UNRESTRICTED on `[0,1]`).
    So the `w ≥ 1/2` base cases cost nothing — `regimeGE_base` just dispatches them.

  * **Theta anchor (reusable).**  `theta4QuarterAnchor` PROVES the paper anchor
    `ϑ₄(1/4)⁴ ≤ 7/100` at the rational level: the alternating theta-4 partial sums
    `Σ_{n<N} (−1)ⁿ · 2·(1/4)^{n²}` (with head `1`) are bracketed in `[0, 65/128]` for `N ≥ 2`,
    and `(65/128)⁴ ≤ 7/100`.  The bracket is the standard alternating-series estimate
    (`altSum_le_head`, `altSum_nonneg`), proved here from scratch over `Q'` for a decreasing
    nonnegative magnitude sequence — a clean, self-contained, REUSABLE piece (Stage 4's
    `OddCentreCellLE` φ-chain reuses the same `altSum` alternating machinery and `bMag` theta
    magnitudes).

  * **Large-`N` residual (NAMED OPEN).**  `RegimeGETailBound w` carries the ONE remaining input:
    the floor for centres `N ≥ 8` (`s ≥ 7`) on `w ∈ [1/2,1]`.  The paper discharges it by the
    two-region (theta/parabolic) split with the anchor `2(1−ϑ₄(w²)⁴) ≥ 93/50` and per-region
    floors `≥ 12/7` (threshold `τ = 1/50`); those constants are documented on the field.  It is a
    genuine, non-vacuous input (a real family of `Q'` inequalities, one per `s ≥ 7`), strictly
    smaller than `RegimeGECell` (the `s ≤ 6` base cases are proved), never `Prop := True`.

  * **Capstone.**  `regimeGECell` assembles the base cases + the residual into `RegimeGECell w`
    (on the physical window `0 ≤ w ≤ 1`) by the decidable window split `s < 7 ∨ 7 ≤ s`.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

Every load-bearing declaration is axiom-checked at file end.  The base dispatch reuses the proved
`fullRangeFloor_*`; the anchor is pure `Q'`/`Nat` arithmetic (`decide` on decidable rational
facts, `omega` on `Nat` parity/index identities, reused `Q'` order/`qpow`/`eqv` lemmas); the
capstone is modus ponens over the residual field.  Permitted output is `propext` / `Quot.sound`
only (via the `Q'` setoid).  No `Classical.*`, no `native_decide`, no `sorry`, no custom `axiom`.
The residual `RegimeGETailBound` is a `Type`-level structure (Rule 6a), never a `Unit`/`True`
witness.
-/

import YMGap.Continuum.CircleFourierPowerModel
import YMGap.Continuum.R1CaseSplit

namespace YMGap.Continuum.R1RegimeGE

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.R1CaseSplit

/-! ## 0. Base cases `s = 0..6` (centres `N = 1..7`) — FREE from the Pólya certificates.

`fullRangeFloor_zero` needs only `0 ≤ w`; `fullRangeFloor_one … _six` are proved on the physical
window `0 ≤ w ≤ 1` and are `w`-UNRESTRICTED there, so they cover the `w ≥ 1/2` base cases with no
extra work. -/

/-- **`regimeGE_base`** — the six-plus-one base windows of R1 on the physical window `0 ≤ w ≤ 1`.
Pure dispatch to the reused Pólya/Bernstein certificates. -/
theorem regimeGE_base {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1) :
    ∀ s, s ≤ 6 → FullRangeFloor w s
  | 0, _ => fullRangeFloor_zero hw0
  | 1, _ => fullRangeFloor_one hw0 hw1
  | 2, _ => fullRangeFloor_two hw0 hw1
  | 3, _ => fullRangeFloor_three hw0 hw1
  | 4, _ => fullRangeFloor_four hw0 hw1
  | 5, _ => fullRangeFloor_five hw0 hw1
  | 6, _ => fullRangeFloor_six hw0 hw1
  | (n + 7), h => absurd h (by omega)

/-! ## 1. The alternating-series machinery over `Q'` (reusable).

For a decreasing nonnegative magnitude sequence `c` the alternating partial sums
`altSum c N = Σ_{i<N} (−1)ⁱ cᵢ` are bracketed in `[0, c₀]` (Leibniz).  We prove this from scratch
by two clean single inductions (even partials increase from `0`; odd-count partials decrease from
`c₀`), then dispatch arbitrary `N` by parity. -/

/-- The alternating partial sum `Σ_{i<N} (−1)ⁱ · b i` (sign `+` at even index). -/
def altSum (b : Nat → Q') : Nat → Q'
  | 0 => 0
  | (N + 1) => altSum b N + (if N % 2 = 0 then b N else -(b N))

/-- The one-step recurrence of `altSum` (definitional). -/
theorem altSum_succ (b : Nat → Q') (N : Nat) :
    altSum b (N + 1) = altSum b N + (if N % 2 = 0 then b N else -(b N)) := rfl

/-- `a ≤ b → 0 ≤ b + -a` (subtraction is nonnegative). -/
theorem sub_nonneg' {a b : Q'} (h : a ≤ b) : (0 : Q') ≤ b + -a := by
  have h2 : a + -a ≤ b + -a := Q'.add_le_add_right a b (-a) h
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.add_neg_self_eqv a)) h2

/-- `a ≤ b → a + -b ≤ 0` (the reflected subtraction is nonpositive). -/
theorem sub_nonpos' {a b : Q'} (h : a ≤ b) : a + -b ≤ (0 : Q') := by
  have h2 : a + -b ≤ b + -b := Q'.add_le_add_right a b (-b) h
  exact Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.add_neg_self_eqv b))

/-- **Even partials are nonnegative.**  `0 ≤ altSum c (2k)` for decreasing nonneg `c`. -/
theorem altSum_even_nonneg {c : Nat → Q'}
    (hdec : ∀ i, c (i + 1) ≤ c i) : ∀ k, (0 : Q') ≤ altSum c (2 * k) := by
  intro k
  induction k with
  | zero => exact Q'.le_refl' 0
  | succ k ih =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by omega,
          altSum_succ c (2 * k + 1), if_neg (by omega : ¬ (2 * k + 1) % 2 = 0),
          altSum_succ c (2 * k), if_pos (by omega : (2 * k) % 2 = 0)]
      -- goal: 0 ≤ (altSum c (2k) + c (2k)) + -(c (2k+1))
      have hpair : (0 : Q') ≤ c (2 * k) + -(c (2 * k + 1)) := sub_nonneg' (hdec (2 * k))
      refine Q'.le_trans' _ _ _ (Q'.zero_le_add _ _ ih hpair) ?_
      exact Q'.ge_of_eqv (Q'.add_assoc_eqv (altSum c (2 * k)) (c (2 * k)) (-(c (2 * k + 1))))

/-- **Odd-count partials are `≤ c₀`.**  `altSum c (2k+1) ≤ c 0` for decreasing `c`. -/
theorem altSum_odd_le_head {c : Nat → Q'}
    (hdec : ∀ i, c (i + 1) ≤ c i) : ∀ k, altSum c (2 * k + 1) ≤ c 0 := by
  intro k
  induction k with
  | zero =>
      rw [show 2 * 0 + 1 = 0 + 1 from by omega, altSum_succ c 0,
          if_pos (by decide : (0 : Nat) % 2 = 0)]
      -- goal: altSum c 0 + c 0 ≤ c 0 ; altSum c 0 = 0
      show (0 : Q') + c 0 ≤ c 0
      rw [Q'.zero_add']
      exact Q'.le_refl' _
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = ((2 * k + 1) + 1) + 1 from by omega,
          altSum_succ c ((2 * k + 1) + 1), if_pos (by omega : ((2 * k + 1) + 1) % 2 = 0),
          altSum_succ c (2 * k + 1), if_neg (by omega : ¬ (2 * k + 1) % 2 = 0)]
      -- goal: (altSum c (2k+1) + -(c (2k+1))) + c ((2k+1)+1) ≤ c 0
      have hle0 : c ((2 * k + 1) + 1) + -(c (2 * k + 1)) ≤ (0 : Q') :=
        sub_nonpos' (hdec (2 * k + 1))
      have hre : ((altSum c (2 * k + 1) + -(c (2 * k + 1))) + c ((2 * k + 1) + 1)).eqv
          (altSum c (2 * k + 1) + (c ((2 * k + 1) + 1) + -(c (2 * k + 1)))) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv (altSum c (2 * k + 1)) (-(c (2 * k + 1))) (c ((2 * k + 1) + 1))) ?_
        exact Q'.add_eqv_congr_left _ _ _
          (Q'.add_comm_eqv (-(c (2 * k + 1))) (c ((2 * k + 1) + 1)))
      refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hre) ?_
      have hstep : altSum c (2 * k + 1) + (c ((2 * k + 1) + 1) + -(c (2 * k + 1)))
          ≤ altSum c (2 * k + 1) + 0 :=
        Q'.add_le_add_left (altSum c (2 * k + 1)) _ 0 hle0
      refine Q'.le_trans' _ _ _ hstep ?_
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' _))) ih

/-- **`altSum` is bounded below by `0`** for decreasing nonneg `c` (any `N`, by parity). -/
theorem altSum_nonneg {c : Nat → Q'} (hnn : ∀ i, (0 : Q') ≤ c i)
    (hdec : ∀ i, c (i + 1) ≤ c i) : ∀ N, (0 : Q') ≤ altSum c N := by
  intro N
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, N = 2 * k := ⟨N / 2, by omega⟩
    exact altSum_even_nonneg hdec k
  · obtain ⟨k, rfl⟩ : ∃ k, N = 2 * k + 1 := ⟨N / 2, by omega⟩
    rw [altSum_succ c (2 * k), if_pos (by omega : (2 * k) % 2 = 0)]
    exact Q'.zero_le_add _ _ (altSum_even_nonneg hdec k) (hnn (2 * k))

/-- **`altSum` is bounded above by the head `c 0`** for decreasing nonneg `c` (Leibniz). -/
theorem altSum_le_head {c : Nat → Q'} (hnn : ∀ i, (0 : Q') ≤ c i)
    (hdec : ∀ i, c (i + 1) ≤ c i) : ∀ N, altSum c N ≤ c 0 := by
  intro N
  rcases Nat.mod_two_eq_zero_or_one N with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, N = 2 * k := ⟨N / 2, by omega⟩
    have h1 : altSum c (2 * k) ≤ altSum c (2 * k) + c (2 * k) :=
      Q'.add_le_self_of_nonneg _ _ (hnn (2 * k))
    have h2 : altSum c (2 * k + 1) = altSum c (2 * k) + c (2 * k) := by
      rw [altSum_succ c (2 * k), if_pos (by omega : (2 * k) % 2 = 0)]
    refine Q'.le_trans' _ _ _ h1 ?_
    rw [← h2]
    exact altSum_odd_le_head hdec k
  · obtain ⟨k, rfl⟩ : ∃ k, N = 2 * k + 1 := ⟨N / 2, by omega⟩
    exact altSum_odd_le_head hdec k

/-- **The two-term split at `k = 2`** (the parity-aligned peel of the first two terms):
`altSum b (2+M) ≃ altSum b 2 + altSum (fun i => b (2+i)) M`. -/
theorem altSum_split2 (b : Nat → Q') :
    ∀ M, (altSum b (2 + M)).eqv (altSum b 2 + altSum (fun i => b (2 + i)) M)
  | 0 => Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (altSum b 2)))
  | (M + 1) => by
      show (altSum b ((2 + M) + 1)).eqv (altSum b 2 + altSum (fun i => b (2 + i)) (M + 1))
      rw [altSum_succ b (2 + M), show (2 + M) % 2 = M % 2 from by omega,
          altSum_succ (fun i => b (2 + i)) M]
      -- goal: (altSum b (2+M) + T).eqv (altSum b 2 + (altSum (fun i=>b(2+i)) M + T))
      have ih := altSum_split2 b M
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ ih) ?_
      exact Q'.add_assoc_eqv (altSum b 2) (altSum (fun i => b (2 + i)) M) _

/-! ## 2. The theta-4 magnitudes and the reusable anchor `ϑ₄(1/4)⁴ ≤ 7/100`. -/

/-- The nome `q = 1/4` (the anchor point `w² = 1/4` at `w = 1/2`). -/
def quarter : Q' := Q'.mkPos 1 4 (by decide)

theorem quarter_nonneg : (0 : Q') ≤ quarter := by decide
theorem quarter_le_one : quarter ≤ (1 : Q') := by decide

/-- The theta-4 magnitude sequence `b₀ = 1`, `bₙ = 2·q^{n²}` (`n ≥ 1`). -/
def bMag (q : Q') : Nat → Q'
  | 0 => 1
  | (n + 1) => Q'.ofNat 2 * qpow q ((n + 1) * (n + 1))

/-- The anchor upper bracket `ϑ₄(1/4) ≤ 65/128`. -/
def theta4UB : Q' := Q'.mkPos 65 128 (by decide)

/-- The anchor target `7/100`. -/
def sevenPercent : Q' := Q'.mkPos 7 100 (by decide)

/-- `bMag quarter` is nonnegative. -/
theorem bMag_quarter_nonneg : ∀ n, (0 : Q') ≤ bMag quarter n
  | 0 => by decide
  | (n + 1) =>
      Q'.mul_nonneg _ _ (zero_le_ofNat 2) (qpow_nonneg quarter quarter_nonneg _)

/-- `bMag q` is decreasing on `q ∈ [0,1]` from index `1` on (the pure Gaussian tail). -/
theorem bMag_dec_ge1 {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ 1) :
    ∀ n, bMag q ((n + 1) + 1) ≤ bMag q (n + 1) := by
  intro n
  show Q'.ofNat 2 * qpow q (((n + 1) + 1) * ((n + 1) + 1))
      ≤ Q'.ofNat 2 * qpow q ((n + 1) * (n + 1))
  refine Q'.mul_le_mul_of_nonneg_left _ _ _ ?_ (zero_le_ofNat 2)
  exact qpow_antitone hq0 hq1 ((n + 1) * (n + 1)) (((n + 1) + 1) * ((n + 1) + 1))
    (Nat.mul_le_mul (by omega) (by omega))

/-- `bMag quarter` is decreasing everywhere (the `0 → 1` step `1/2 ≤ 1` is decidable). -/
theorem bMag_quarter_dec : ∀ n, bMag quarter (n + 1) ≤ bMag quarter n
  | 0 => by decide
  | (n + 1) => bMag_dec_ge1 quarter_nonneg quarter_le_one n

/-- The shifted magnitude sequence `d i = bMag quarter (2+i)` is decreasing. -/
theorem d_dec : ∀ i,
    (fun i => bMag quarter (2 + i)) (i + 1) ≤ (fun i => bMag quarter (2 + i)) i := by
  intro i
  show bMag quarter (2 + (i + 1)) ≤ bMag quarter (2 + i)
  rw [show 2 + (i + 1) = (2 + i) + 1 from by omega]
  exact bMag_quarter_dec (2 + i)

/-- The shifted magnitude sequence is nonnegative. -/
theorem d_nonneg : ∀ i, (0 : Q') ≤ (fun i => bMag quarter (2 + i)) i :=
  fun i => bMag_quarter_nonneg (2 + i)

/-- **`theta4_quarter_partial_lb`** — every theta-4 partial sum at `q = 1/4` is `≥ 0`. -/
theorem theta4_quarter_partial_lb : ∀ N, (0 : Q') ≤ altSum (bMag quarter) N :=
  altSum_nonneg bMag_quarter_nonneg bMag_quarter_dec

/-- **`theta4_quarter_partial_ub`** — every theta-4 partial sum at `q = 1/4` past the first two
terms is `≤ 65/128` (the Leibniz upper bracket, anchoring at `altSum 2 = 1 − 1/2` plus the head
`b₂` of the alternating remainder). -/
theorem theta4_quarter_partial_ub :
    ∀ N, 2 ≤ N → altSum (bMag quarter) N ≤ theta4UB := by
  intro N hN
  obtain ⟨M, rfl⟩ : ∃ M, N = 2 + M := ⟨N - 2, by omega⟩
  have hsplit := altSum_split2 (bMag quarter) M
  have hd_head : altSum (fun i => bMag quarter (2 + i)) M ≤ bMag quarter 2 :=
    altSum_le_head d_nonneg d_dec M
  have hstep : altSum (bMag quarter) 2 + altSum (fun i => bMag quarter (2 + i)) M
      ≤ altSum (bMag quarter) 2 + bMag quarter 2 :=
    Q'.add_le_add_left _ _ _ hd_head
  have hfin : altSum (bMag quarter) 2 + bMag quarter 2 ≤ theta4UB := by decide
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsplit) (Q'.le_trans' _ _ _ hstep hfin)

/-- **`theta4_quarter_pow4`** — the anchor's 4th-power arithmetic `(65/128)⁴ ≤ 7/100`. -/
theorem theta4_quarter_pow4 : qpow theta4UB 4 ≤ sevenPercent := by decide

/-- **`Theta4QuarterAnchor`** — the reusable anchor bundle.  Together its fields certify
`ϑ₄(1/4) ∈ [0, 65/128]` (via the alternating partial-sum bracket) and `(65/128)⁴ ≤ 7/100`, i.e.
the paper anchor `ϑ₄(1/4)⁴ ≤ 7/100`.  Stage 4's `OddCentreCellLE` φ-chain reuses `altSum`, `bMag`,
and these brackets. -/
structure Theta4QuarterAnchor : Type where
  /-- Every alternating partial sum at `q = 1/4` is `≥ 0`. -/
  lb : ∀ N, (0 : Q') ≤ altSum (bMag quarter) N
  /-- Every alternating partial sum past the first two terms is `≤ 65/128`. -/
  ub : ∀ N, 2 ≤ N → altSum (bMag quarter) N ≤ theta4UB
  /-- `(65/128)⁴ ≤ 7/100`. -/
  pow4 : qpow theta4UB 4 ≤ sevenPercent

/-- The anchor, PROVED. -/
def theta4QuarterAnchor : Theta4QuarterAnchor where
  lb := theta4_quarter_partial_lb
  ub := theta4_quarter_partial_ub
  pow4 := theta4_quarter_pow4

/-! ## 3. The large-`N` residual and the capstone cell. -/

/-- **`RegimeGETailBound w`** (NAMED OPEN — the large-window residual of Task B).  The floor for
centres `N ≥ 8` (windows `s ≥ 7`) on the physical upper half `w ∈ [1/2,1]`.  The paper
(`computations/r1_remaining_pieces.md`, Task B (ii)) discharges it by a `w`-adaptive two-region
split at `τ = 1/50` on the smallest physical weight `w^{(N−1)²/2}`:

  * THETA region (`w^{(N−1)²/2} < 1/50`): theta-dominated, `Δ²V+2 → 2(1−ϑ₄(w²)⁴) ≥ 93/50`
    (using the anchor `ϑ₄(w²)⁴ ≤ ϑ₄(1/4)⁴ ≤ 7/100`, `ϑ₄` decreasing in the nome, `w² ≥ 1/4`);
  * PARABOLIC region (`w^{(N−1)²/2} ≥ 1/50`): measure within a factor `50` of `(N²−D²)`,
    `Δ²V+2 → 12/5`.

Both region minima are `≥ 12/7` (interval-verified `N = 8..46`, monotone increasing toward the
`≈1.836` plateau).  A genuine, non-vacuous family of `Q'` inequalities (false for arbitrary
moments); strictly smaller than `RegimeGECell` (the base windows `s ≤ 6` are proved above). -/
structure RegimeGETailBound (w : Q') : Type where
  tail : half ≤ w → w ≤ 1 → ∀ s, 7 ≤ s → FullRangeFloor w s

/-- **`regimeGECell`** — THE STAGE-3 CAPSTONE.  On the physical window `0 ≤ w ≤ 1`, the base cases
(`regimeGE_base`, FREE) plus the large-window residual (`RegimeGETailBound`) inhabit
`R1CaseSplit.RegimeGECell w`.  Pure decidable window split `s < 7 ∨ 7 ≤ s` — axiom-clean. -/
def regimeGECell {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ 1)
    (T : RegimeGETailBound w) : RegimeGECell w where
  cell := fun hge s => by
    rcases Nat.lt_or_ge s 7 with hlt | hge7
    · exact regimeGE_base hw0 hw1 s (by omega)
    · exact T.tail hge hw1 s hge7

/-! ## 4. Doc-section — PROVED vs NAMED-open (CRITICAL honesty)

PROVED (axiom-clean):
  * `regimeGE_base` — base windows `s = 0..6` (centres `N = 1..7`), reusing the Pólya certificates
    `fullRangeFloor_zero … _six` (`w`-unrestricted on `[0,1]`, hence FREE for `w ≥ 1/2`).
  * `altSum_even_nonneg`, `altSum_odd_le_head`, `altSum_nonneg`, `altSum_le_head`, `altSum_split2`
    — the reusable `Q'` alternating-series (Leibniz) machinery.
  * `theta4_quarter_partial_lb`, `theta4_quarter_partial_ub`, `theta4_quarter_pow4`,
    `theta4QuarterAnchor` — the reusable theta anchor `ϑ₄(1/4) ∈ [0, 65/128]`, `(65/128)⁴ ≤ 7/100`.
  * `regimeGECell` — the capstone: base cases + the residual inhabit `RegimeGECell w`.

NAMED OPEN (Type-level structure, never `sorry`):
  * `RegimeGETailBound w` — the large-window floor (`N ≥ 8`, `w ∈ [1/2,1]`), Task B (ii): anchor
    `2(1−ϑ₄(w²)⁴) ≥ 93/50` + two-region (`τ = 1/50`) split, both floors `≥ 12/7`.
-/

end YMGap.Continuum.R1RegimeGE

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.R1RegimeGE.regimeGE_base
#print axioms YMGap.Continuum.R1RegimeGE.altSum_even_nonneg
#print axioms YMGap.Continuum.R1RegimeGE.altSum_odd_le_head
#print axioms YMGap.Continuum.R1RegimeGE.altSum_nonneg
#print axioms YMGap.Continuum.R1RegimeGE.altSum_le_head
#print axioms YMGap.Continuum.R1RegimeGE.altSum_split2
#print axioms YMGap.Continuum.R1RegimeGE.theta4_quarter_partial_lb
#print axioms YMGap.Continuum.R1RegimeGE.theta4_quarter_partial_ub
#print axioms YMGap.Continuum.R1RegimeGE.theta4_quarter_pow4
#print axioms YMGap.Continuum.R1RegimeGE.theta4QuarterAnchor
#print axioms YMGap.Continuum.R1RegimeGE.regimeGECell
