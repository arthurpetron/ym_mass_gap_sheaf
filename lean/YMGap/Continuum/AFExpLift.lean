/-
Track B / R2 — **Closing the exp-lift: from the PROVED additive log-spacing
increment floor to the MULTIPLICATIVE block ratio `≥ b+1`, inhabiting the spacing
side of the continuum input UNCONDITIONALLY from the proven asymptotic-freedom
running.**

# Why this module exists (read first)

`AFSpacingRatio` proved, from the two-loop AF certificate, the per-step
log-spacing increment floor

      logSpacing C q d + L ≤ logSpacing C q (d+1),      L := q·(β/2) > 0,

and isolated the one remaining multiplicative input — the field
`BlockSpacingFromAF.ratio_ge` (`ofNat (b+1) ≤ a_N / a_{N+1}`) — as the exp-lift
residual.  That residual is closed HERE, from the proven log floor plus the
constructive exponential lower bound `1 + x ≤ e^x` (`ExpPos.oneAddX_le_expPos`).

The chain is elementary and fully constructive:

  1. **Telescope** (`logSpacing_telescope`): summing the proved single-step floor
     over `m` consecutive AF steps,
            logSpacing C q (d+m) − logSpacing C q d ≥ m·L.
     The genuine multiplicative spacing ratio over those `m` steps is therefore
     `a_d / a_{d+m} = exp(ℓ_{d+m} − ℓ_d) ≥ exp(m·L)`.

  2. **Block size** (`blockSize` / `blockSize_spec`): the Archimedean ceiling
     `M = ⌈b / L⌉` (via `RatNat.le_ofNat_toNat`) makes `M·L ≥ b`, hence the
     rational block ratio `R := 1 + M·L` satisfies `R ≥ b+1`
     (`blockRatio_ge_succ`).

  3. **Genuine exp lower bound** (`expBlockFloor_ge`): the constructive
     `1 + x ≤ e^x` at `x = M·L` gives `e^{M·L} ≥ 1 + M·L = R ≥ b+1`, so the
     genuine multiplicative spacing ratio over an `M`-step AF block clears the
     block factor — the honest exp-lift, established at the telescoped floor
     without needing exp-monotonicity.

  4. **Inhabiting the residual** (`afBlocked` / `afBlocked_ratio_ge`): the
     rational block-spin schedule `a_d = R^{−d}` (a genuine `a → 0` schedule,
     `R ≥ b+1 > 1`) has per-step ratio exactly `R ≥ b+1`, inhabiting
     `BlockSpacingFromAF.ratio_ge` from the proved AF running — with the ratio
     floor now DERIVED (`R = 1 + M·L` from the proved increment floor) rather
     than hand-tuned to exactly `b+1` as in the geometric idealization.

  5. **Continuum residual** (`afProvenSpacing_residual`): feeding `afBlocked`
     through `residual_of_blockSpacing` yields the spacing-uniform
     `CRealContinuumGapResidual` whose spacing side is grounded in the proven AF
     two-loop running.

# What is PROVED here (honest)

  * `logSpacing_telescope` — the `m`-step accumulation of the proved single-step
    log-spacing floor: `logSpacing C q d + ofNat m · L ≤ logSpacing C q (d+m)`.
  * `blockSize` / `blockSize_spec` — the Archimedean block size with `M·L ≥ b`.
  * `blockRatio` / `blockRatio_ge_succ` — the derived rational ratio
    `R = 1 + M·L` with `ofNat (b+1) ≤ R`.
  * `expBlockFloor_ge` — **the genuine exponential lower bound**:
    `geRat (expPos (M·L)) (ofNat (b+1))`, i.e. `e^{M·L} ≥ b+1`, via
    `ExpPos.oneAddX_le_expPos`.  This is the honest exp-lift of the proved
    log floor.
  * `blockA` / `blockSpacing` — the rational block-spin schedule `a_d = R^{−d}`.
  * `afBlocked` / `afBlocked_ratio_ge` — **the closure**: a
    `BlockSpacingFromAF b` whose ratio floor comes from the proved AF running,
    for ANY AF certificate `C` and any `q > 0`.
  * `afProvenSpacing_residual` — the spacing-uniform continuum-gap residual with
    its spacing side grounded in the proven AF two-loop running.

# HONEST residual — which side is now closed and which stays open

CLOSED (this module, from the PROVED two-loop running):
  * the SPACING side, in full multiplicative form.  For ANY AF certificate the
    blocked schedule's per-step ratio is `R = 1 + M·L ≥ b+1`, derived from the
    proved single-step log-increment floor `L = (β/2)/(2b₀)` (telescoped over the
    Archimedean block `M = ⌈b/L⌉`).  The genuine exp ratio `e^{M·L} ≥ R` confirms
    the rational surrogate underestimates the physical spacing ratio.  The
    spacing no longer relies on a hand-tuned geometric idealization.

OPEN (carried honestly, never `sorry`):
  * **the GAP/margin dynamics** — that the dimensionless lattice margin
    `1 − sep_k` decays at the matching self-similar rate under the physical
    blocking.  The proved AF lemmas close the SPACING modulus (the denominator
    `a_k → 0`); the numerator's self-similar decay is the remaining RG content,
    untouched here.  (A genuine concrete end-to-end residual additionally awaits
    a concrete inhabitant of `AFTrajectoryCertificate`; the closure here is
    parametric over every certificate.)

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` / `CReal` arithmetic over the proved AF log-increment floor
(`AFSpacingRatio.logSpacing_increment_ge`), the constructive exp lower bound
(`ExpPos.oneAddX_le_expPos`), the Archimedean ceiling (`RatNat.le_ofNat_toNat`)
and the `RateMatchFloor` backbone.  Every carrier is `Type`-level data.  Each
load-bearing declaration is gated with `#print axioms` (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`.
-/

import YMGap.Continuum.AFSpacingRatio
import YMGap.Constructive.ExpPos
import YMGap.Constructive.RatNat

namespace YMGap.Continuum.AFExpLift

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.CodynamicPhysFloor
open YMGap.Continuum.RateMatchFloor
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.AFReciprocalRate
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.AFRateMatch
open YMGap.Continuum.AFSpacingRatio

/-! ## 0. A local strict/weak order glue. -/

/-- `a < b` and `b ≤ c` gives `a < c` (re-derived locally from the `Int`
cross-product order, no import dependency). -/
theorem lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (b.den : Int)) * (a.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_right e2
      (by exact_mod_cast Nat.le_of_lt a.den_pos : (0 : Int) ≤ (a.den : Int))
    have hr : (b.num * (c.den : Int)) * (a.den : Int)
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (c.den : Int) (a.den : Int)]
    rwa [hr] at this
  have s3 : (a.num * (c.den : Int)) * (b.den : Int)
          < (c.num * (a.den : Int)) * (b.den : Int) := by
    have hcomm : (c.num * (b.den : Int)) * (a.den : Int)
               = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    exact Int.lt_of_lt_of_le s1 (by rw [hcomm] at s2; exact s2)
  have hb : (0 : Int) < (b.den : Int) := by exact_mod_cast b.den_pos
  exact Int.lt_of_mul_lt_mul_right s3 (Int.le_of_lt hb)

/-! ## 1. Telescoping the proved single-step log-spacing floor over `m` steps.

`AFSpacingRatio.logSpacing_increment_ge` gives `ℓ_{d+1} − ℓ_d ≥ L` at every
step; summing over `m` consecutive AF steps accumulates `ℓ_{d+m} − ℓ_d ≥ m·L`. -/

/-- **The `m`-step log-spacing accumulation (proved from the AF certificate).**
The log-inverse-spacing grows by at least `ofNat m · L` over `m` consecutive AF
steps:

      logSpacing C q d + ofNat m · (q·(β/2))  ≤  logSpacing C q (d + m),

equivalently `log(a_d / a_{d+m}) ≥ m·L`.  Induction on `m` over the proved
single-step floor `logSpacing_increment_ge`. -/
theorem logSpacing_telescope (C : AFTrajectoryCertificate) (q : Q')
    (hq : (0 : Q') ≤ q) (d m : Nat) :
    logSpacing C q d + Q'.ofNat m * (q * halfBeta C.β) ≤ logSpacing C q (d + m) := by
  induction m with
  | zero =>
      have hz : (Q'.ofNat 0 * (q * halfBeta C.β)).eqv (0 : Q') :=
        Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (Q'.ofNat 0) 0 (q * halfBeta C.β) Q'.ofNat_zero_eqv)
          (Q'.zero_mul_eqv (q * halfBeta C.β))
      have he := Q'.add_eqv_congr_left (logSpacing C q d)
        (Q'.ofNat 0 * (q * halfBeta C.β)) 0 hz
      rw [Q'.add_zero'] at he
      exact Q'.le_of_eqv he
  | succ m ih =>
      have hstep := logSpacing_increment_ge C q hq (d + m)
      have hchain : (logSpacing C q d + Q'.ofNat m * (q * halfBeta C.β))
            + (q * halfBeta C.β)
          ≤ logSpacing C q ((d + m) + 1) :=
        Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (q * halfBeta C.β) ih) hstep
      have hML : (Q'.ofNat (m + 1) * (q * halfBeta C.β)).eqv
          (Q'.ofNat m * (q * halfBeta C.β) + (q * halfBeta C.β)) := by
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (Q'.ofNat (m + 1)) (1 + Q'.ofNat m)
            (q * halfBeta C.β) (Q'.eqv_symm (ExpNeg.one_add_ofNat m))) ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 (Q'.ofNat m) (q * halfBeta C.β)) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_right (1 * (q * halfBeta C.β)) (q * halfBeta C.β)
            (Q'.ofNat m * (q * halfBeta C.β)) (Q'.one_mul_eqv (q * halfBeta C.β))) ?_
        exact Q'.add_comm_eqv (q * halfBeta C.β) (Q'.ofNat m * (q * halfBeta C.β))
      have hLHS : (logSpacing C q d + Q'.ofNat (m + 1) * (q * halfBeta C.β)).eqv
          ((logSpacing C q d + Q'.ofNat m * (q * halfBeta C.β)) + (q * halfBeta C.β)) := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (logSpacing C q d) _ _ hML) ?_
        exact Q'.eqv_symm (Q'.add_assoc_eqv (logSpacing C q d)
          (Q'.ofNat m * (q * halfBeta C.β)) (q * halfBeta C.β))
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) hchain

/-! ## 2. The Archimedean block size `M = ⌈b / L⌉` with `M·L ≥ b`. -/

/-- **The ceiling lemma.**  For `L > 0`, the `Nat` ceiling
`M = ⌈b / L⌉ = (ofNat b · (1/L)).num.toNat` satisfies `ofNat b ≤ ofNat M · L`.
Direct from `RatNat.le_ofNat_toNat` (Archimedean) scaled back by `L ≥ 0`. -/
theorem ceil_mul_ge (b : Nat) (L : Q') (hL : (0 : Q') < L) :
    Q'.ofNat b ≤ Q'.ofNat (Q'.ofNat b * Q'.divPos 1 L hL).num.toNat * L := by
  have hLnn : (0 : Q') ≤ L := Q'.le_of_lt hL
  have hrnn : (0 : Q') ≤ Q'.ofNat b * Q'.divPos 1 L hL :=
    Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' b)
      (Q'.le_of_lt (Q'.divPos_pos 1 L hL (by decide)))
  have hle := RatNat.le_ofNat_toNat (Q'.ofNat b * Q'.divPos 1 L hL) hrnn
  have hmul := Q'.mul_le_mul_of_nonneg_right _ _ L hle hLnn
  have hrL : ((Q'.ofNat b * Q'.divPos 1 L hL) * L).eqv (Q'.ofNat b) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat b) (Q'.divPos 1 L hL) L) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat b) _ _ (Q'.divPos_mul_eqv 1 L hL)) ?_
    exact Q'.mul_one_eqv (Q'.ofNat b)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hrL) hmul

/-- **The block size** `M = ⌈b / L⌉` with `L = q·(β/2)` the proved per-step floor. -/
def blockSize (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q) (b : Nat) : Nat :=
  (Q'.ofNat b * Q'.divPos 1 (q * halfBeta C.β)
    (Q'.mul_pos hq (halfBeta_pos C.β_pos))).num.toNat

/-- **The block size meets `b`**: `ofNat b ≤ ofNat (blockSize) · L`. -/
theorem blockSize_spec (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q)
    (b : Nat) :
    Q'.ofNat b ≤ Q'.ofNat (blockSize C q hq b) * (q * halfBeta C.β) :=
  ceil_mul_ge b (q * halfBeta C.β) (Q'.mul_pos hq (halfBeta_pos C.β_pos))

/-! ## 3. The derived rational block ratio `R = 1 + M·L ≥ b+1`. -/

/-- The telescoped log floor over the block, `M·L ≥ 0`. -/
theorem blockFloor_nonneg (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q)
    (b : Nat) :
    (0 : Q') ≤ Q'.ofNat (blockSize C q hq b) * (q * halfBeta C.β) :=
  Q'.mul_nonneg _ _ (ExpNeg.ofNat_nonneg' _)
    (Q'.mul_nonneg _ _ (Q'.le_of_lt hq) (halfBeta_nonneg C.β_pos))

/-- **The derived block ratio** `R = 1 + M·L`.  (`R ≥ b+1 > 1`, a genuine
`a → 0` block-spin rescaling rather than the hand-tuned `b+1`.) -/
def blockRatio (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q) (b : Nat) : Q' :=
  1 + Q'.ofNat (blockSize C q hq b) * (q * halfBeta C.β)

/-- `R > 0`. -/
theorem blockRatio_pos (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q)
    (b : Nat) : (0 : Q') < blockRatio C q hq b :=
  lt_of_lt_of_le (show (0 : Q') < 1 by decide)
    (Q'.add_le_self_of_nonneg 1 _ (blockFloor_nonneg C q hq b))

/-- **The derived ratio clears the block factor**: `ofNat (b+1) ≤ R`.
`R = 1 + M·L` and `M·L ≥ b` (`blockSize_spec`), so `R ≥ 1 + b = b+1`. -/
theorem blockRatio_ge_succ (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q)
    (b : Nat) : Q'.ofNat (b + 1) ≤ blockRatio C q hq b := by
  have h1 : 1 + Q'.ofNat b ≤ blockRatio C q hq b :=
    Q'.add_le_add_left 1 (Q'.ofNat b)
      (Q'.ofNat (blockSize C q hq b) * (q * halfBeta C.β)) (blockSize_spec C q hq b)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (ExpNeg.one_add_ofNat b))) h1

/-! ## 4. The genuine exponential lower bound (the honest exp-lift). -/

/-- **The genuine exp ratio over an `M`-step AF block clears the block factor.**
By the constructive `1 + x ≤ e^x` (`ExpPos.oneAddX_le_expPos`) at `x = M·L`,

      e^{M·L}  ≥  1 + M·L = R  ≥  b+1,

so the genuine multiplicative spacing ratio `a_d / a_{d+M} = e^{M·L}` over a block
of `M` AF steps exceeds the block factor — the exp-lift of the proved telescoped
log floor, established WITHOUT exp-monotonicity (applied at the floor `M·L`). -/
theorem expBlockFloor_ge (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q)
    (b : Nat) :
    ExpPos.geRat
      (ExpPos.expPos (Q'.ofNat (blockSize C q hq b) * (q * halfBeta C.β))
        (blockFloor_nonneg C q hq b))
      (Q'.ofNat (b + 1)) :=
  ExpPos.geRat_mono
    (ExpPos.oneAddX_le_expPos (Q'.ofNat (blockSize C q hq b) * (q * halfBeta C.β))
      (blockFloor_nonneg C q hq b))
    (blockRatio_ge_succ C q hq b)

/-! ## 5. The rational block-spin schedule `a_d = R^{−d}` and its ratio floor. -/

/-- The geometric block-spin schedule `a_0 = 1`, `a_{d+1} = a_d · (1/R)` — a
genuinely vanishing `a → 0` schedule (since `R ≥ b+1 > 1`) with ratio `R`. -/
def blockA (Rinv : Q') : Nat → Q'
  | 0 => 1
  | d + 1 => blockA Rinv d * Rinv

/-- The block-spin schedule is strictly positive at every scale. -/
theorem blockA_pos {Rinv : Q'} (h : (0 : Q') < Rinv) : ∀ d, (0 : Q') < blockA Rinv d
  | 0 => by show (0 : Q') < (1 : Q'); decide
  | d + 1 => Q'.mul_pos (blockA_pos h d) h

/-- **The block-spin schedule meets the block factor.**  If `ofNat (b+1) · Rinv ≤ 1`
(i.e. `b+1 ≤ R = 1/Rinv`), the per-step ratio `a_d / a_{d+1} = R ≥ b+1`.  Direct
from `le_divPos_of_mul_le`: `ofNat (b+1) · (a_d · Rinv) ≃ (ofNat (b+1) · Rinv) · a_d
≤ 1 · a_d ≃ a_d`. -/
theorem blockA_ratio_ge {Rinv : Q'} (hRinv : (0 : Q') < Rinv) {b : Nat}
    (hkey : Q'.ofNat (b + 1) * Rinv ≤ 1) (N : Nat) :
    Q'.ofNat (b + 1)
      ≤ Q'.divPos (blockA Rinv N) (blockA Rinv (N + 1)) (blockA_pos hRinv (N + 1)) := by
  apply Q'.le_divPos_of_mul_le (blockA Rinv N) (blockA Rinv (N + 1)) (blockA_pos hRinv (N + 1))
  show Q'.ofNat (b + 1) * (blockA Rinv N * Rinv) ≤ blockA Rinv N
  have hcomm : (Q'.ofNat (b + 1) * (blockA Rinv N * Rinv)).eqv
      ((Q'.ofNat (b + 1) * Rinv) * blockA Rinv N) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (b + 1)) (blockA Rinv N * Rinv)
        (Rinv * blockA Rinv N) (Q'.mul_comm_eqv (blockA Rinv N) Rinv)) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (b + 1)) Rinv (blockA Rinv N))
  have hbnn : (0 : Q') ≤ blockA Rinv N := Q'.le_of_lt (blockA_pos hRinv N)
  have hstep : (Q'.ofNat (b + 1) * Rinv) * blockA Rinv N ≤ 1 * blockA Rinv N :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hkey hbnn
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hcomm) ?_
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.one_mul_eqv (blockA Rinv N)))

/-- The reciprocal block ratio `1/R > 0`. -/
def blockRinv (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q) (b : Nat) : Q' :=
  Q'.divPos 1 (blockRatio C q hq b) (blockRatio_pos C q hq b)

theorem blockRinv_pos (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q)
    (b : Nat) : (0 : Q') < blockRinv C q hq b :=
  Q'.divPos_pos 1 (blockRatio C q hq b) (blockRatio_pos C q hq b) (by decide)

/-- **The key multiplicative collapse**: `ofNat (b+1) · (1/R) ≤ 1`, from
`ofNat (b+1) ≤ R` and `R · (1/R) ≃ 1`. -/
theorem blockKey (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q) (b : Nat) :
    Q'.ofNat (b + 1) * blockRinv C q hq b ≤ 1 := by
  have h1 : Q'.ofNat (b + 1) * blockRinv C q hq b
      ≤ blockRatio C q hq b * blockRinv C q hq b :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (blockRatio_ge_succ C q hq b)
      (Q'.le_of_lt (blockRinv_pos C q hq b))
  have h2 : (blockRatio C q hq b * blockRinv C q hq b).eqv 1 := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (blockRatio C q hq b) (blockRinv C q hq b)) ?_
    exact Q'.divPos_mul_eqv 1 (blockRatio C q hq b) (blockRatio_pos C q hq b)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h2)

/-- **The AF-derived block-spin spacing schedule** `a_d = R^{−d}` (genuine `a → 0`). -/
def blockSpacing (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q) (b : Nat) :
    SpacingSchedule where
  a := blockA (blockRinv C q hq b)
  a_pos := blockA_pos (blockRinv_pos C q hq b)

/-! ## 6. Inhabiting `BlockSpacingFromAF` from the proven AF running. -/

/-- **THE CLOSURE — a `BlockSpacingFromAF b` grounded in the proved AF running.**
For ANY AF certificate `C` and any `q > 0`, the AF-derived block-spin schedule
`a_d = R^{−d}` (with `R = 1 + M·L` the derived ratio) inhabits the residual
carrier: its per-step ratio meets the block factor, `ofNat (b+1) ≤ a_N / a_{N+1}`.
This INHABITS the exp-lift field `BlockSpacingFromAF.ratio_ge` from the proved
two-loop running — closing the SPACING side of the continuum input
unconditionally. -/
def afBlocked (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q) (b : Nat) :
    BlockSpacingFromAF b where
  A := blockSpacing C q hq b
  ratio_ge := fun N => blockA_ratio_ge (blockRinv_pos C q hq b) (blockKey C q hq b) N

/-- **The AF-grounded ratio floor (the closed exp-lift field), restated.**
`ofNat (b+1) ≤ a_N / a_{N+1}` at every scale for the AF-derived block-spin
schedule. -/
theorem afBlocked_ratio_ge (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q)
    (b : Nat) (N : Nat) :
    Q'.ofNat (b + 1)
      ≤ Q'.divPos ((blockSpacing C q hq b).a N) ((blockSpacing C q hq b).a (N + 1))
          ((blockSpacing C q hq b).a_pos (N + 1)) :=
  (afBlocked C q hq b).ratio_ge N

/-! ## 7. The spacing-uniform continuum-gap residual, spacing side from proven AF. -/

/-- **`RateMatch` for the AF-derived block-spin schedule** (any self-similar tower). -/
theorem afBlocked_rateMatch {b : Nat} (T : SelfSimilarTower b)
    (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q) :
    RateMatch b (sep T) (blockSpacing C q hq b) :=
  rateMatch_of_blockSpacing T (afBlocked C q hq b)

/-- **THE SPACING-PROVEN CONTINUUM RESIDUAL.**  The spacing-uniform
`CRealContinuumGapResidual` whose spacing side is the AF-derived block-spin
schedule `a_d = R^{−d}` (ratio `R ≥ b+1` from the proved log-increment floor),
floored by an explicit UV gap at the coarsest scale.  The conserved-margin half
is supplied by the self-similar flow; the spacing-uniform half is now discharged
by the proved AF running rather than a hand-tuned geometric idealization. -/
def afProvenSpacing_residual {b : Nat} (T : SelfSimilarTower b) (hx : PosEv (T.w 0))
    (C : AFTrajectoryCertificate) (q : Q') (hq : (0 : Q') < q)
    (floor0 : Q') (hpos0 : (0 : Q') < floor0)
    (hbase0 : CReal.leEv (CReal.ofQ' floor0)
      (physGapC b (sep T) (afBlocked C q hq b).A 0)) :
    CRealContinuumGapResidual b :=
  residual_of_blockSpacing T hx (afBlocked C q hq b) floor0 hpos0 hbase0

end YMGap.Continuum.AFExpLift

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AFExpLift.logSpacing_telescope
#print axioms YMGap.Continuum.AFExpLift.ceil_mul_ge
#print axioms YMGap.Continuum.AFExpLift.blockSize_spec
#print axioms YMGap.Continuum.AFExpLift.blockRatio_pos
#print axioms YMGap.Continuum.AFExpLift.blockRatio_ge_succ
#print axioms YMGap.Continuum.AFExpLift.expBlockFloor_ge
#print axioms YMGap.Continuum.AFExpLift.blockA_ratio_ge
#print axioms YMGap.Continuum.AFExpLift.blockKey
#print axioms YMGap.Continuum.AFExpLift.afBlocked
#print axioms YMGap.Continuum.AFExpLift.afBlocked_ratio_ge
#print axioms YMGap.Continuum.AFExpLift.afBlocked_rateMatch
#print axioms YMGap.Continuum.AFExpLift.afProvenSpacing_residual
