/-
Track A / R2 (track: 1-whmargin) — CLOSING the `WHMarginTail` residual of `WHAllSMargin` from the
two full-window θ-ceilings, with ALL of the peak-comparison arithmetic and central lower bounds
proved axiom-clean.

# What this module adds (read first — load-bearing honesty)

`WHAllSMarginTail` reduced the `s → ∞` tail of the wH autoconvolution margin to the single named
residual `WHMarginTail` — the crude rational theta-floor margins `40000·(A·C) ≤ 22801·B²` for all
`s ≥ 6`, with `A = acN wH (s+1) s`, `B = acN wH (s+1)(s+1)`, `C = acN wH (s+1)(s+2)`.  This module
proves the ENTIRE assembly of that residual EXCEPT the two full-window θ-envelope ceilings, which it
isolates as the structure `WHTailCeilings`:

    evenCeil M :  acN wH (2M+1) (2M)   ≤ (151/100)·(c_M·c_M)
    oddCeil  M :  acN wH (2M+2) (2M+1) ≤ (16/15)·(2·c_M·c_{M+1})

and it produces `whMarginTailOfCeilings : WHTailCeilings → WHMarginTail` (hence, composed with the
in-tree `whAllSMarginOf`, `whAllSMarginOfCeilings : WHTailCeilings → WHAllSMargin`).

DELIVERABLE (PROVED, axiom-clean `Q'`/`Nat` arithmetic):
  * `peak_even_arith` — the EXACT even-peak comparison: from `A ≤ (151/100)x²`, `C ≤ (151/100)y²`,
    `2xy ≤ B` (nonnegs) conclude `40000·(A·C) ≤ 22801·B²`.  Saturates the identity
    `40000·(151/100)² = 4·22801 = 91204` (razor-thin; the `151/100` ceiling cannot be loosened).
  * `peak_odd_arith` — the odd-peak comparison genuinely requiring BOTH the THREE-central `B` lower
    bound `y² + 2xz ≤ B` AND the Hankel super-log-concavity `xz ≤ (1/4)y²`: from
    `A ≤ (16/15)·2xy`, `C ≤ (16/15)·2yz`, `y²+2xz ≤ B`, `xz ≤ (1/4)y²` conclude
    `40000·(A·C) ≤ 22801·B²` (margin ≈ 1.13 at the extremal `xz = y²/4`).
  * `gWin_symm`, `acN_range_mono`, `fsum_three_term_le` — the window-reflection, range-completion,
    and three-term lower-bound scaffolding.
  * `whMarginTail_even`, `whMarginTail_odd`, `whMarginTailOfCeilings`, `whAllSMarginOfCeilings` — the
    parity assembly reducing `WHMarginTail`/`WHAllSMargin` to `WHTailCeilings`.

NAMED OPEN (Type-level structure, never `sorry`):
  * `WHTailCeilings` — the two full-window θ-envelope ceilings (the reflect-and-fold sum bound plus
    the θ₃(0,¼) `≤ 151/100` and the geometric `Σ(¼)^{i(i+1)} ≤ 16/15` ceilings).  These are the sole
    remaining content; everything downstream of them is proved here.

# HONESTY — scope

This module CLOSES the entire arithmetic backbone of the `WHMarginTail` residual — both peak
comparisons (the exact even identity and the odd Hankel-cross), the central lower bounds, and the
parity assembly — reducing `WHAllSMargin` to just the two full-window θ-ceilings `WHTailCeilings`.
It does NOT inhabit those ceilings (the reflect-and-fold θ-envelope sum bound).  This is a structural
sharpening of one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `acN`/`coeffW`/`gWin`/`fsum`/`qpow` definitions,
`coeffW_superLogConcave_wsq`, the `fsum` two/three-term and range-monotone lemmas, `omega` on index
identities, and `decide` only on closed concrete-rational facts.  Every load-bearing declaration is
gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.WHAllSMarginTail
import YMGap.Continuum.AFRateCalibration
import YMGap.Continuum.EigShiftOrder
import YMGap.Continuum.FusionGenFunction

namespace YMGap.Continuum.WHMarginTailClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.LaplaceMarginDeep
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.WHAllSMarginTail
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.EigShiftOrder
open YMGap.Continuum.FusionGenFunction

/-! ## 0. Small `Q'` algebra helpers (pure commutative algebra) -/

/-- Product of two `≤`s of nonnegatives: `a ≤ b`, `c ≤ d`, `0 ≤ c`, `0 ≤ b` ⟹ `a·c ≤ b·d`. -/
private theorem mul_le_mul' {a b c d : Q'} (hab : a ≤ b) (hcd : c ≤ d)
    (hc : (0 : Q') ≤ c) (hb : (0 : Q') ≤ b) : a * c ≤ b * d :=
  Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ hab hc)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hcd hb)

/-- `(X·Y)·Z ≃ Y·(X·Z)`. -/
private theorem mul3_swap (X Y Z : Q') : ((X * Y) * Z).eqv (Y * (X * Z)) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ Z (Q'.mul_comm_eqv X Y))
    (Q'.mul_assoc_eqv Y X Z)

/-- `X·(Y·Z) ≃ Y·(X·Z)`. -/
private theorem mul3_swap' (X Y Z : Q') : (X * (Y * Z)).eqv (Y * (X * Z)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv X Y Z)) (mul3_swap X Y Z)

/-- `ofNat 2 · z ≃ z + z`. -/
private theorem two_mul_eqv (z : Q') : (Q'.ofNat 2 * z).eqv (z + z) := by
  have h1 : (Q'.ofNat 2 * z).eqv (((1 : Q') + 1) * z) :=
    Q'.mul_eqv_congr_right (Q'.ofNat 2) ((1 : Q') + 1) z (by decide)
  have h2 : (((1 : Q') + 1) * z).eqv ((1 : Q') * z + (1 : Q') * z) :=
    Q'.add_mul_eqv (1 : Q') (1 : Q') z
  have h3 : ((1 : Q') * z + (1 : Q') * z).eqv (z + z) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ ((1 : Q') * z) (Q'.one_mul_eqv z))
      (Q'.add_eqv_congr_left z _ _ (Q'.one_mul_eqv z))
  exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 h3)

/-- The square-of-binomial lower bound `S² + 4·(S·T) ≤ (S + 2T)²` (drop the `4T² ≥ 0` term). -/
private theorem sq_lb (S T : Q') (hT : (0 : Q') ≤ T) :
    S * S + Q'.ofNat 4 * (S * T)
      ≤ (S + Q'.ofNat 2 * T) * (S + Q'.ofNat 2 * T) := by
  have step_a : ((S + Q'.ofNat 2 * T) * (S + Q'.ofNat 2 * T)).eqv
      ((S + Q'.ofNat 2 * T) * S + (S + Q'.ofNat 2 * T) * (Q'.ofNat 2 * T)) :=
    Q'.mul_add_eqv (S + Q'.ofNat 2 * T) S (Q'.ofNat 2 * T)
  have hb1 : ((S + Q'.ofNat 2 * T) * S).eqv (S * S + (Q'.ofNat 2 * T) * S) :=
    Q'.add_mul_eqv S (Q'.ofNat 2 * T) S
  have hb2 : ((S + Q'.ofNat 2 * T) * (Q'.ofNat 2 * T)).eqv
      (S * (Q'.ofNat 2 * T) + (Q'.ofNat 2 * T) * (Q'.ofNat 2 * T)) :=
    Q'.add_mul_eqv S (Q'.ofNat 2 * T) (Q'.ofNat 2 * T)
  have h2T0 : (0 : Q') ≤ (Q'.ofNat 2 * T) * (Q'.ofNat 2 * T) :=
    Q'.mul_nonneg _ _ (Q'.mul_nonneg _ _ (by decide) hT) (Q'.mul_nonneg _ _ (by decide) hT)
  have hc2 : S * (Q'.ofNat 2 * T) ≤ (S + Q'.ofNat 2 * T) * (Q'.ofNat 2 * T) :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ h2T0) (Q'.ge_of_eqv hb2)
  have hc1 : S * S + (Q'.ofNat 2 * T) * S ≤ (S + Q'.ofNat 2 * T) * S := Q'.ge_of_eqv hb1
  have hadd : (S * S + (Q'.ofNat 2 * T) * S) + S * (Q'.ofNat 2 * T)
      ≤ (S + Q'.ofNat 2 * T) * S + (S + Q'.ofNat 2 * T) * (Q'.ofNat 2 * T) :=
    Q'.add_le_add hc1 hc2
  -- LHS reorganize:  S² + 4(S·T) ≃ (S² + (2T)·S) + S·(2T)
  have p1 : ((Q'.ofNat 2 * T) * S).eqv (Q'.ofNat 2 * (S * T)) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (Q'.ofNat 2) T S)
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) (T * S) (S * T) (Q'.mul_comm_eqv T S))
  have p2 : (S * (Q'.ofNat 2 * T)).eqv (Q'.ofNat 2 * (S * T)) := mul3_swap' S (Q'.ofNat 2) T
  have p3 : ((Q'.ofNat 2 * T) * S + S * (Q'.ofNat 2 * T)).eqv
      (Q'.ofNat 2 * (S * T) + Q'.ofNat 2 * (S * T)) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (S * (Q'.ofNat 2 * T)) p1)
      (Q'.add_eqv_congr_left (Q'.ofNat 2 * (S * T)) _ _ p2)
  have p4 : (Q'.ofNat 2 * (S * T) + Q'.ofNat 2 * (S * T)).eqv (Q'.ofNat 4 * (S * T)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat 2) (Q'.ofNat 2) (S * T)))
      (Q'.mul_eqv_congr_right (Q'.ofNat 2 + Q'.ofNat 2) (Q'.ofNat 4) (S * T) (by decide))
  have hmid : ((Q'.ofNat 2 * T) * S + S * (Q'.ofNat 2 * T)).eqv (Q'.ofNat 4 * (S * T)) :=
    Q'.eqv_trans _ _ _ p3 p4
  have Efwd : ((S * S + (Q'.ofNat 2 * T) * S) + S * (Q'.ofNat 2 * T)).eqv
      (S * S + Q'.ofNat 4 * (S * T)) :=
    Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (S * S) ((Q'.ofNat 2 * T) * S) (S * (Q'.ofNat 2 * T)))
      (Q'.add_eqv_congr_left (S * S) _ _ hmid)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv Efwd)
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (Q'.eqv_symm step_a)))

/-! ## 1. Window reflection, range completion, three-term lower bound -/

/-- **`gWin_symm`** — window reflection: for `p ≤ N`, `gWin w N p ≃ gWin w N (N − p)`. -/
theorem gWin_symm (w : Q') {N p : Nat} (hp : p ≤ N) :
    (gWin w N p).eqv (gWin w N (N - p)) := by
  show (coeffW w p * coeffW w (N - p)).eqv (coeffW w (N - p) * coeffW w (N - (N - p)))
  rw [show N - (N - p) = p from by omega]
  exact Q'.mul_comm_eqv _ _

/-- **`acN_range_mono`** — the central autoconvolution `acN wH n N` is monotone in its range `n`
(nonnegative summand). -/
theorem acN_range_mono {N n n' : Nat} (h : n ≤ n') : acN wH n N ≤ acN wH n' N := by
  unfold acN
  exact fsum_le_of_le
    (fun p => Q'.mul_nonneg _ _ (coeffW_nonneg (by decide) p) (coeffW_nonneg (by decide) (N - p))) h

/-- **`fsum_three_term_le`** — three summands `(f i + f j) + f k` are `≤` the whole nonnegative sum
`fsum f n` for `i < j < k < n`. -/
theorem fsum_three_term_le {f : Nat → Q'} (hf : ∀ i, (0 : Q') ≤ f i)
    (i j k : Nat) (hij : i < j) (hjk : j < k) :
    ∀ (n : Nat), k < n → (f i + f j) + f k ≤ fsum f n
  | 0, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
      · show (f i + f j) + f k ≤ fsum f n + f n
        exact Q'.le_trans' _ _ _ (fsum_three_term_le hf i j k hij hjk n hlt)
          (Q'.add_le_self_of_nonneg _ _ (hf n))
      · subst k
        show (f i + f j) + f n ≤ fsum f n + f n
        exact Q'.add_le_add_right _ _ (f n) (fsum_two_term_le hf i j hij n hjk)

/-! ## 2. The two peak-comparison arithmetic lemmas (pure `Q'`) -/

/-- **`peak_even_arith` — the EXACT even-peak comparison.**  Saturates
`40000·(151/100)² = 4·22801`; `P = 151/100`, `x = c_M`, `y = c_{M+1}`. -/
theorem peak_even_arith {A B C x y P : Q'}
    (hP0 : (0 : Q') ≤ P)
    (hA : A ≤ P * (x * x)) (hC : C ≤ P * (y * y))
    (hB : Q'.ofNat 2 * (x * y) ≤ B)
    (hconst : (Q'.ofNat 40000 * (P * P)).eqv (Q'.ofNat 22801 * (Q'.ofNat 2 * Q'.ofNat 2)))
    (hx : (0 : Q') ≤ x) (hy : (0 : Q') ≤ y)
    (hC0 : (0 : Q') ≤ C) (hB0 : (0 : Q') ≤ B) :
    Q'.ofNat 40000 * (A * C) ≤ Q'.ofNat 22801 * (B * B) := by
  have hPx0 : (0 : Q') ≤ P * (x * x) := Q'.mul_nonneg _ _ hP0 (Q'.mul_nonneg _ _ hx hx)
  have hAC : A * C ≤ (P * (x * x)) * (P * (y * y)) := mul_le_mul' hA hC hC0 hPx0
  have h40 : Q'.ofNat 40000 * (A * C) ≤ Q'.ofNat 40000 * ((P * (x * x)) * (P * (y * y))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hAC (by decide)
  -- identity  40000·((Px²)(Py²)) ≃ 22801·((2xy)(2xy))
  have e1 : ((P * (x * x)) * (P * (y * y))).eqv ((P * P) * ((x * x) * (y * y))) :=
    mul_swap4 P (x * x) P (y * y)
  have e2 : (Q'.ofNat 40000 * ((P * (x * x)) * (P * (y * y)))).eqv
      (Q'.ofNat 40000 * ((P * P) * ((x * x) * (y * y)))) :=
    Q'.mul_eqv_congr_left _ _ _ e1
  have e3 : (Q'.ofNat 40000 * ((P * P) * ((x * x) * (y * y)))).eqv
      ((Q'.ofNat 40000 * (P * P)) * ((x * x) * (y * y))) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 40000) (P * P) ((x * x) * (y * y)))
  have f1 : ((Q'.ofNat 2 * (x * y)) * (Q'.ofNat 2 * (x * y))).eqv
      ((Q'.ofNat 2 * Q'.ofNat 2) * ((x * y) * (x * y))) :=
    mul_swap4 (Q'.ofNat 2) (x * y) (Q'.ofNat 2) (x * y)
  have f2 : ((x * y) * (x * y)).eqv ((x * x) * (y * y)) := mul_swap4 x y x y
  have f4 : ((Q'.ofNat 2 * (x * y)) * (Q'.ofNat 2 * (x * y))).eqv
      ((Q'.ofNat 2 * Q'.ofNat 2) * ((x * x) * (y * y))) :=
    Q'.eqv_trans _ _ _ f1 (Q'.mul_eqv_congr_left _ _ _ f2)
  have f5 : (Q'.ofNat 22801 * ((Q'.ofNat 2 * (x * y)) * (Q'.ofNat 2 * (x * y)))).eqv
      (Q'.ofNat 22801 * ((Q'.ofNat 2 * Q'.ofNat 2) * ((x * x) * (y * y)))) :=
    Q'.mul_eqv_congr_left _ _ _ f4
  have f6 : (Q'.ofNat 22801 * ((Q'.ofNat 2 * Q'.ofNat 2) * ((x * x) * (y * y)))).eqv
      ((Q'.ofNat 22801 * (Q'.ofNat 2 * Q'.ofNat 2)) * ((x * x) * (y * y))) :=
    Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)
  have hc : ((Q'.ofNat 40000 * (P * P)) * ((x * x) * (y * y))).eqv
      ((Q'.ofNat 22801 * (Q'.ofNat 2 * Q'.ofNat 2)) * ((x * x) * (y * y))) :=
    Q'.mul_eqv_congr_right _ _ _ hconst
  have hident : (Q'.ofNat 40000 * ((P * (x * x)) * (P * (y * y)))).eqv
      (Q'.ofNat 22801 * ((Q'.ofNat 2 * (x * y)) * (Q'.ofNat 2 * (x * y)))) :=
    Q'.eqv_trans _ _ _ e2 (Q'.eqv_trans _ _ _ e3 (Q'.eqv_trans _ _ _ hc
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm f6) (Q'.eqv_symm f5))))
  -- (2xy)² ≤ B²
  have hD0 : (0 : Q') ≤ Q'.ofNat 2 * (x * y) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hx hy)
  have h3 : (Q'.ofNat 2 * (x * y)) * (Q'.ofNat 2 * (x * y)) ≤ B * B := mul_le_mul' hB hB hD0 hB0
  have h4 : Q'.ofNat 22801 * ((Q'.ofNat 2 * (x * y)) * (Q'.ofNat 2 * (x * y)))
      ≤ Q'.ofNat 22801 * (B * B) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ h3 (by decide)
  exact Q'.le_trans' _ _ _ h40 (Q'.le_trans' _ _ _ (Q'.le_of_eqv hident) h4)

/-- **`peak_odd_arith` — the odd-peak comparison.**  Genuinely requires BOTH the three-central `B`
lower bound `y² + 2xz ≤ B` AND the Hankel bound `xz ≤ (1/4)y²`; `x = c_M`, `y = c_{M+1}`,
`z = c_{M+2}`. -/
theorem peak_odd_arith {A B C x y z : Q'}
    (hA : A ≤ Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (x * y)))
    (hC : C ≤ Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (y * z)))
    (hB : y * y + Q'.ofNat 2 * (x * z) ≤ B)
    (hank : x * z ≤ Q'.mkPos 1 4 (by decide) * (y * y))
    (hx : (0 : Q') ≤ x) (hy : (0 : Q') ≤ y) (hz : (0 : Q') ≤ z)
    (hC0 : (0 : Q') ≤ C) (hB0 : (0 : Q') ≤ B) :
    Q'.ofNat 40000 * (A * C) ≤ Q'.ofNat 22801 * (B * B) := by
  have hT0 : (0 : Q') ≤ x * z := Q'.mul_nonneg _ _ hx hz
  have hS0 : (0 : Q') ≤ y * y := Q'.mul_nonneg _ _ hy hy
  have hSS0 : (0 : Q') ≤ (y * y) * (y * y) := Q'.mul_nonneg _ _ hS0 hS0
  have hRA0 : (0 : Q') ≤ Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (x * y)) :=
    Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ (by decide) (Q'.mul_nonneg _ _ hx hy))
  have hAC : A * C ≤ (Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (x * y)))
      * (Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (y * z))) := mul_le_mul' hA hC hC0 hRA0
  have h40 : Q'.ofNat 40000 * (A * C) ≤ Q'.ofNat 40000
      * ((Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (x * y)))
        * (Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (y * z)))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hAC (by decide)
  -- normalize  40000·RA·RC ≃ (40960000/225)·((xz)(y²))
  have hnorm : (Q'.ofNat 40000 * ((Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (x * y)))
        * (Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (y * z))))).eqv
      (Q'.mkPos 40960000 225 (by decide) * ((x * z) * (y * y))) := by
    have e1 := mul_swap4 (Q'.mkPos 16 15 (by decide)) (Q'.ofNat 2 * (x * y))
      (Q'.mkPos 16 15 (by decide)) (Q'.ofNat 2 * (y * z))
    have e2 := mul_swap4 (Q'.ofNat 2) (x * y) (Q'.ofNat 2) (y * z)
    have e3a : ((x * y) * (y * z)).eqv ((x * y) * (z * y)) :=
      Q'.mul_eqv_congr_left (x * y) (y * z) (z * y) (Q'.mul_comm_eqv y z)
    have e3b := mul_swap4 x y z y
    have e3 : ((x * y) * (y * z)).eqv ((x * z) * (y * y)) := Q'.eqv_trans _ _ _ e3a e3b
    have e2' : ((Q'.ofNat 2 * (x * y)) * (Q'.ofNat 2 * (y * z))).eqv
        ((Q'.ofNat 2 * Q'.ofNat 2) * ((x * z) * (y * y))) :=
      Q'.eqv_trans _ _ _ e2 (Q'.mul_eqv_congr_left (Q'.ofNat 2 * Q'.ofNat 2) _ _ e3)
    have hR : ((Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (x * y)))
          * (Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (y * z)))).eqv
        ((Q'.mkPos 16 15 (by decide) * Q'.mkPos 16 15 (by decide))
          * ((Q'.ofNat 2 * Q'.ofNat 2) * ((x * z) * (y * y)))) :=
      Q'.eqv_trans _ _ _ e1 (Q'.mul_eqv_congr_left _ _ _ e2')
    have hm1 := Q'.mul_eqv_congr_left (Q'.ofNat 40000) _ _ hR
    have hassoc1 : ((Q'.mkPos 16 15 (by decide) * Q'.mkPos 16 15 (by decide))
          * ((Q'.ofNat 2 * Q'.ofNat 2) * ((x * z) * (y * y)))).eqv
        (((Q'.mkPos 16 15 (by decide) * Q'.mkPos 16 15 (by decide))
          * (Q'.ofNat 2 * Q'.ofNat 2)) * ((x * z) * (y * y))) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.mkPos 16 15 (by decide) * Q'.mkPos 16 15 (by decide))
        (Q'.ofNat 2 * Q'.ofNat 2) ((x * z) * (y * y)))
    have hm2 := Q'.mul_eqv_congr_left (Q'.ofNat 40000) _ _ hassoc1
    have hassoc2 : (Q'.ofNat 40000 * (((Q'.mkPos 16 15 (by decide) * Q'.mkPos 16 15 (by decide))
          * (Q'.ofNat 2 * Q'.ofNat 2)) * ((x * z) * (y * y)))).eqv
        ((Q'.ofNat 40000 * ((Q'.mkPos 16 15 (by decide) * Q'.mkPos 16 15 (by decide))
          * (Q'.ofNat 2 * Q'.ofNat 2))) * ((x * z) * (y * y))) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 40000)
        ((Q'.mkPos 16 15 (by decide) * Q'.mkPos 16 15 (by decide)) * (Q'.ofNat 2 * Q'.ofNat 2))
        ((x * z) * (y * y)))
    have hGc : (Q'.ofNat 40000 * ((Q'.mkPos 16 15 (by decide) * Q'.mkPos 16 15 (by decide))
        * (Q'.ofNat 2 * Q'.ofNat 2))).eqv (Q'.mkPos 40960000 225 (by decide)) := by decide
    have hGcW : ((Q'.ofNat 40000 * ((Q'.mkPos 16 15 (by decide) * Q'.mkPos 16 15 (by decide))
          * (Q'.ofNat 2 * Q'.ofNat 2))) * ((x * z) * (y * y))).eqv
        (Q'.mkPos 40960000 225 (by decide) * ((x * z) * (y * y))) :=
      Q'.mul_eqv_congr_right _ _ _ hGc
    exact Q'.eqv_trans _ _ _ hm1 (Q'.eqv_trans _ _ _ hm2 (Q'.eqv_trans _ _ _ hassoc2 hGcW))
  have hL : Q'.ofNat 40000 * (A * C) ≤ Q'.mkPos 40960000 225 (by decide) * ((x * z) * (y * y)) :=
    Q'.le_trans' _ _ _ h40 (Q'.le_of_eqv hnorm)
  -- B² ≥ (y² + 2xz)² ≥ y⁴ + 4·(y²·xz)
  have hSum0 : (0 : Q') ≤ y * y + Q'.ofNat 2 * (x * z) :=
    Q'.zero_le_add _ _ hS0 (Q'.mul_nonneg _ _ (by decide) hT0)
  have hBB : (y * y + Q'.ofNat 2 * (x * z)) * (y * y + Q'.ofNat 2 * (x * z)) ≤ B * B :=
    mul_le_mul' hB hB hSum0 hB0
  have hlb : (y * y) * (y * y) + Q'.ofNat 4 * ((y * y) * (x * z))
      ≤ (y * y + Q'.ofNat 2 * (x * z)) * (y * y + Q'.ofNat 2 * (x * z)) := sq_lb (y * y) (x * z) hT0
  have hlbBB : (y * y) * (y * y) + Q'.ofNat 4 * ((y * y) * (x * z)) ≤ B * B :=
    Q'.le_trans' _ _ _ hlb hBB
  have h22 : Q'.ofNat 22801 * ((y * y) * (y * y) + Q'.ofNat 4 * ((y * y) * (x * z)))
      ≤ Q'.ofNat 22801 * (B * B) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hlbBB (by decide)
  have hexp : (Q'.ofNat 22801 * ((y * y) * (y * y) + Q'.ofNat 4 * ((y * y) * (x * z)))).eqv
      (Q'.ofNat 22801 * ((y * y) * (y * y)) + Q'.ofNat 91204 * ((y * y) * (x * z))) := by
    have m1 := Q'.mul_add_eqv (Q'.ofNat 22801) ((y * y) * (y * y)) (Q'.ofNat 4 * ((y * y) * (x * z)))
    have m2 : (Q'.ofNat 22801 * (Q'.ofNat 4 * ((y * y) * (x * z)))).eqv
        (Q'.ofNat 91204 * ((y * y) * (x * z))) :=
      Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 22801) (Q'.ofNat 4) ((y * y) * (x * z))))
        (Q'.mul_eqv_congr_right _ _ _ (by decide))
    exact Q'.eqv_trans _ _ _ m1 (Q'.add_eqv_congr_left _ _ _ m2)
  have hRHSle : Q'.ofNat 22801 * ((y * y) * (y * y)) + Q'.ofNat 91204 * ((y * y) * (x * z))
      ≤ Q'.ofNat 22801 * (B * B) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm hexp)) h22
  -- G·((xz)(y²)) ≤ 22801·y⁴ + 91204·(y²·xz)
  have hWST : (Q'.mkPos 40960000 225 (by decide) * ((x * z) * (y * y))).eqv
      (Q'.mkPos 40960000 225 (by decide) * ((y * y) * (x * z))) :=
    Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (x * z) (y * y))
  have hGsplit : (Q'.mkPos 40960000 225 (by decide)).eqv
      (Q'.mkPos 20439100 225 (by decide) + Q'.ofNat 91204) := by decide
  have hGST : (Q'.mkPos 40960000 225 (by decide) * ((y * y) * (x * z))).eqv
      (Q'.mkPos 20439100 225 (by decide) * ((y * y) * (x * z))
        + Q'.ofNat 91204 * ((y * y) * (x * z))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hGsplit)
      (Q'.add_mul_eqv (Q'.mkPos 20439100 225 (by decide)) (Q'.ofNat 91204) ((y * y) * (x * z)))
  have hST_bound : (y * y) * (x * z) ≤ (y * y) * (Q'.mkPos 1 4 (by decide) * (y * y)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hank hS0
  have hqq4SS : ((y * y) * (Q'.mkPos 1 4 (by decide) * (y * y))).eqv
      (Q'.mkPos 1 4 (by decide) * ((y * y) * (y * y))) :=
    mul3_swap' (y * y) (Q'.mkPos 1 4 (by decide)) (y * y)
  have hSTle : (y * y) * (x * z) ≤ Q'.mkPos 1 4 (by decide) * ((y * y) * (y * y)) :=
    Q'.le_trans' _ _ _ hST_bound (Q'.le_of_eqv hqq4SS)
  have hHST : Q'.mkPos 20439100 225 (by decide) * ((y * y) * (x * z))
      ≤ Q'.ofNat 22801 * ((y * y) * (y * y)) := by
    have t1 : Q'.mkPos 20439100 225 (by decide) * ((y * y) * (x * z))
        ≤ Q'.mkPos 20439100 225 (by decide) * (Q'.mkPos 1 4 (by decide) * ((y * y) * (y * y))) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hSTle (by decide)
    have t2 : (Q'.mkPos 20439100 225 (by decide) * (Q'.mkPos 1 4 (by decide) * ((y * y) * (y * y)))).eqv
        ((Q'.mkPos 20439100 225 (by decide) * Q'.mkPos 1 4 (by decide)) * ((y * y) * (y * y))) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.mkPos 20439100 225 (by decide)) (Q'.mkPos 1 4 (by decide))
        ((y * y) * (y * y)))
    have t3 : (Q'.mkPos 20439100 225 (by decide) * Q'.mkPos 1 4 (by decide)) * ((y * y) * (y * y))
        ≤ Q'.ofNat 22801 * ((y * y) * (y * y)) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ (by decide) hSS0
    exact Q'.le_trans' _ _ _ t1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv t2) t3)
  have hmid : Q'.mkPos 40960000 225 (by decide) * ((x * z) * (y * y))
      ≤ Q'.ofNat 22801 * ((y * y) * (y * y)) + Q'.ofNat 91204 * ((y * y) * (x * z)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hWST hGST))
      (Q'.add_le_add_right _ _ _ hHST)
  exact Q'.le_trans' _ _ _ hL (Q'.le_trans' _ _ _ hmid hRHSle)

/-! ## 3. The named residual: the two full-window θ-ceilings -/

/-- **`WHTailCeilings`** — the sole remaining content of the `WHMarginTail` tail: the two full-window
θ-envelope ceilings (each is the reflect-and-fold sum bound × the θ₃(0,¼) `≤ 151/100` resp. the
geometric `Σ(¼)^{i(i+1)} ≤ 16/15` ceiling).  NAMED-OPEN (never `sorry`). -/
structure WHTailCeilings : Type where
  /-- Even full window: `Σ_{p<2M+1} g^{(2M)}_p ≤ (151/100)·c_M²`. -/
  evenCeil : ∀ M, acN wH (2 * M + 1) (2 * M)
    ≤ Q'.mkPos 151 100 (by decide) * (coeffW wH M * coeffW wH M)
  /-- Odd full window: `Σ_{p<2M+2} g^{(2M+1)}_p ≤ (16/15)·(2·c_M·c_{M+1})`. -/
  oddCeil : ∀ M, acN wH (2 * M + 2) (2 * M + 1)
    ≤ Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (coeffW wH M * coeffW wH (M + 1)))

/-! ## 4. The parity assembly -/

/-- Even-`s` (`s = 2M`, `M ≥ 3`) tail margin from the ceilings. -/
theorem whMarginTail_even (cel : WHTailCeilings) (M : Nat) (hM : 3 ≤ M) :
    Q'.ofNat 40000 * (acN wH (2 * M + 1) (2 * M) * acN wH (2 * M + 1) (2 * M + 2))
      ≤ Q'.ofNat 22801 * (acN wH (2 * M + 1) (2 * M + 1) * acN wH (2 * M + 1) (2 * M + 1)) := by
  have hw0 : (0 : Q') ≤ wH := by decide
  have hA : acN wH (2 * M + 1) (2 * M)
      ≤ Q'.mkPos 151 100 (by decide) * (coeffW wH M * coeffW wH M) := cel.evenCeil M
  have hC1 : acN wH (2 * M + 1) (2 * M + 2) ≤ acN wH (2 * M + 3) (2 * M + 2) :=
    acN_range_mono (by omega)
  have hC2 : acN wH (2 * M + 3) (2 * M + 2)
      ≤ Q'.mkPos 151 100 (by decide) * (coeffW wH (M + 1) * coeffW wH (M + 1)) := cel.evenCeil (M + 1)
  have hC : acN wH (2 * M + 1) (2 * M + 2)
      ≤ Q'.mkPos 151 100 (by decide) * (coeffW wH (M + 1) * coeffW wH (M + 1)) :=
    Q'.le_trans' _ _ _ hC1 hC2
  have hf : ∀ i, (0 : Q') ≤ (fun p => coeffW wH p * coeffW wH (2 * M + 1 - p)) i :=
    fun i => Q'.mul_nonneg _ _ (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 (2 * M + 1 - i))
  have key : coeffW wH M * coeffW wH (2 * M + 1 - M)
      + coeffW wH (M + 1) * coeffW wH (2 * M + 1 - (M + 1))
      ≤ acN wH (2 * M + 1) (2 * M + 1) :=
    fsum_two_term_le hf M (M + 1) (Nat.lt_succ_self M) (2 * M + 1) (by omega)
  rw [show 2 * M + 1 - M = M + 1 from by omega, show 2 * M + 1 - (M + 1) = M from by omega] at key
  have hcomm : (coeffW wH (M + 1) * coeffW wH M).eqv (coeffW wH M * coeffW wH (M + 1)) :=
    Q'.mul_comm_eqv _ _
  have hBeqv : (coeffW wH M * coeffW wH (M + 1) + coeffW wH (M + 1) * coeffW wH M).eqv
      (Q'.ofNat 2 * (coeffW wH M * coeffW wH (M + 1))) :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hcomm)
      (Q'.eqv_symm (two_mul_eqv (coeffW wH M * coeffW wH (M + 1))))
  have hB : Q'.ofNat 2 * (coeffW wH M * coeffW wH (M + 1)) ≤ acN wH (2 * M + 1) (2 * M + 1) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hBeqv) key
  exact peak_even_arith (by decide) hA hC hB (by decide)
    (coeffW_nonneg hw0 M) (coeffW_nonneg hw0 (M + 1))
    (acN_nonneg hw0 _ _) (acN_nonneg hw0 _ _)

/-- Odd-`s` (`s = 2M+1`, `M ≥ 3`) tail margin from the ceilings. -/
theorem whMarginTail_odd (cel : WHTailCeilings) (M : Nat) (hM : 3 ≤ M) :
    Q'.ofNat 40000 * (acN wH (2 * M + 2) (2 * M + 1) * acN wH (2 * M + 2) (2 * M + 3))
      ≤ Q'.ofNat 22801 * (acN wH (2 * M + 2) (2 * M + 2) * acN wH (2 * M + 2) (2 * M + 2)) := by
  have hw0 : (0 : Q') ≤ wH := by decide
  have hA : acN wH (2 * M + 2) (2 * M + 1)
      ≤ Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (coeffW wH M * coeffW wH (M + 1))) :=
    cel.oddCeil M
  have hC1 : acN wH (2 * M + 2) (2 * M + 3) ≤ acN wH (2 * M + 4) (2 * M + 3) :=
    acN_range_mono (by omega)
  have hC2 : acN wH (2 * M + 4) (2 * M + 3)
      ≤ Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (coeffW wH (M + 1) * coeffW wH (M + 2))) :=
    cel.oddCeil (M + 1)
  have hC : acN wH (2 * M + 2) (2 * M + 3)
      ≤ Q'.mkPos 16 15 (by decide) * (Q'.ofNat 2 * (coeffW wH (M + 1) * coeffW wH (M + 2))) :=
    Q'.le_trans' _ _ _ hC1 hC2
  have hf : ∀ i, (0 : Q') ≤ (fun p => coeffW wH p * coeffW wH (2 * M + 2 - p)) i :=
    fun i => Q'.mul_nonneg _ _ (coeffW_nonneg hw0 i) (coeffW_nonneg hw0 (2 * M + 2 - i))
  have key : (coeffW wH M * coeffW wH (2 * M + 2 - M)
        + coeffW wH (M + 1) * coeffW wH (2 * M + 2 - (M + 1)))
      + coeffW wH (M + 2) * coeffW wH (2 * M + 2 - (M + 2))
      ≤ acN wH (2 * M + 2) (2 * M + 2) :=
    fsum_three_term_le hf M (M + 1) (M + 2) (by omega) (by omega) (2 * M + 2) (by omega)
  rw [show 2 * M + 2 - M = M + 2 from by omega, show 2 * M + 2 - (M + 1) = M + 1 from by omega,
      show 2 * M + 2 - (M + 2) = M from by omega] at key
  -- rearrange  (a + b) + d ≃ b + 2a   with a = c_M·c_{M+2}, b = c_{M+1}², d = c_{M+2}·c_M
  have hda : (coeffW wH (M + 2) * coeffW wH M).eqv (coeffW wH M * coeffW wH (M + 2)) :=
    Q'.mul_comm_eqv _ _
  have s1 : ((coeffW wH M * coeffW wH (M + 2) + coeffW wH (M + 1) * coeffW wH (M + 1))
        + coeffW wH (M + 2) * coeffW wH M).eqv
      ((coeffW wH M * coeffW wH (M + 2) + coeffW wH (M + 1) * coeffW wH (M + 1))
        + coeffW wH M * coeffW wH (M + 2)) :=
    Q'.add_eqv_congr_left _ _ _ hda
  have s2 : ((coeffW wH M * coeffW wH (M + 2) + coeffW wH (M + 1) * coeffW wH (M + 1))
        + coeffW wH M * coeffW wH (M + 2)).eqv
      (coeffW wH M * coeffW wH (M + 2)
        + (coeffW wH (M + 1) * coeffW wH (M + 1) + coeffW wH M * coeffW wH (M + 2))) :=
    Q'.add_assoc_eqv (coeffW wH M * coeffW wH (M + 2)) (coeffW wH (M + 1) * coeffW wH (M + 1))
      (coeffW wH M * coeffW wH (M + 2))
  have s3 : (coeffW wH M * coeffW wH (M + 2)
        + (coeffW wH (M + 1) * coeffW wH (M + 1) + coeffW wH M * coeffW wH (M + 2))).eqv
      (coeffW wH M * coeffW wH (M + 2)
        + (coeffW wH M * coeffW wH (M + 2) + coeffW wH (M + 1) * coeffW wH (M + 1))) :=
    Q'.add_eqv_congr_left _ _ _
      (Q'.add_comm_eqv (coeffW wH (M + 1) * coeffW wH (M + 1)) (coeffW wH M * coeffW wH (M + 2)))
  have s4 : (coeffW wH M * coeffW wH (M + 2)
        + (coeffW wH M * coeffW wH (M + 2) + coeffW wH (M + 1) * coeffW wH (M + 1))).eqv
      ((coeffW wH M * coeffW wH (M + 2) + coeffW wH M * coeffW wH (M + 2))
        + coeffW wH (M + 1) * coeffW wH (M + 1)) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (coeffW wH M * coeffW wH (M + 2))
      (coeffW wH M * coeffW wH (M + 2)) (coeffW wH (M + 1) * coeffW wH (M + 1)))
  have s5 : ((coeffW wH M * coeffW wH (M + 2) + coeffW wH M * coeffW wH (M + 2))
        + coeffW wH (M + 1) * coeffW wH (M + 1)).eqv
      (coeffW wH (M + 1) * coeffW wH (M + 1)
        + (coeffW wH M * coeffW wH (M + 2) + coeffW wH M * coeffW wH (M + 2))) :=
    Q'.add_comm_eqv _ _
  have s6 : (coeffW wH (M + 1) * coeffW wH (M + 1)
        + (coeffW wH M * coeffW wH (M + 2) + coeffW wH M * coeffW wH (M + 2))).eqv
      (coeffW wH (M + 1) * coeffW wH (M + 1)
        + Q'.ofNat 2 * (coeffW wH M * coeffW wH (M + 2))) :=
    Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm (two_mul_eqv (coeffW wH M * coeffW wH (M + 2))))
  have hBeqv : ((coeffW wH M * coeffW wH (M + 2) + coeffW wH (M + 1) * coeffW wH (M + 1))
        + coeffW wH (M + 2) * coeffW wH M).eqv
      (coeffW wH (M + 1) * coeffW wH (M + 1)
        + Q'.ofNat 2 * (coeffW wH M * coeffW wH (M + 2))) :=
    Q'.eqv_trans _ _ _ s1 (Q'.eqv_trans _ _ _ s2 (Q'.eqv_trans _ _ _ s3
      (Q'.eqv_trans _ _ _ s4 (Q'.eqv_trans _ _ _ s5 s6))))
  have hB : coeffW wH (M + 1) * coeffW wH (M + 1)
      + Q'.ofNat 2 * (coeffW wH M * coeffW wH (M + 2)) ≤ acN wH (2 * M + 2) (2 * M + 2) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hBeqv) key
  -- Hankel super-log-concavity  c_M·c_{M+2} ≤ (1/4)·c_{M+1}²
  have hqe : (qpow wH 2).eqv (Q'.mkPos 1 4 (by decide)) := by decide
  have hank0 := coeffW_superLogConcave_wsq hw0 M
  have hank : coeffW wH M * coeffW wH (M + 2)
      ≤ Q'.mkPos 1 4 (by decide) * (coeffW wH (M + 1) * coeffW wH (M + 1)) :=
    Q'.le_trans' _ _ _ hank0 (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ _ hqe))
  exact peak_odd_arith hA hC hB hank
    (coeffW_nonneg hw0 M) (coeffW_nonneg hw0 (M + 1)) (coeffW_nonneg hw0 (M + 2))
    (acN_nonneg hw0 _ _) (acN_nonneg hw0 _ _)

/-- **`whMarginTailOfCeilings` — THE REDUCTION.**  The two full-window θ-ceilings inhabit the
`WHMarginTail` residual (parity split via `s % 2`; `6 ≤ s` gives `M ≥ 3` in both parities). -/
def whMarginTailOfCeilings (cel : WHTailCeilings) : WHAllSMarginTail.WHMarginTail where
  tail := fun s hs => by
    rcases Nat.lt_or_ge (s % 2) 1 with h0 | h1
    · have heven : s % 2 = 0 := by omega
      have hdm := Nat.div_add_mod s 2
      generalize hMdef : s / 2 = M at hdm
      have hs2 : s = 2 * M := by omega
      have key := whMarginTail_even cel M (by omega)
      rw [hs2]
      exact key
    · have hodd : s % 2 = 1 := by
        have hlt : s % 2 < 2 := Nat.mod_lt s (by decide)
        omega
      have hdm := Nat.div_add_mod s 2
      generalize hMdef : s / 2 = M at hdm
      have hs2 : s = 2 * M + 1 := by omega
      have key := whMarginTail_odd cel M (by omega)
      rw [hs2]
      exact key

/-- **`whAllSMarginOfCeilings`** — composing with the in-tree `whAllSMarginOf`, the two ceilings
inhabit the full `LaplaceMarginDeep.WHAllSMargin`. -/
def whAllSMarginOfCeilings (cel : WHTailCeilings) : LaplaceMarginDeep.WHAllSMargin :=
  WHAllSMarginTail.whAllSMarginOf (whMarginTailOfCeilings cel)

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `peak_even_arith` — the EXACT even-peak comparison (saturates `40000·(151/100)² = 4·22801`).
  * `peak_odd_arith` — the odd-peak comparison via the three-central `B` bound AND the Hankel bound.
  * `gWin_symm`, `acN_range_mono`, `fsum_three_term_le` — window/range/lower-bound scaffolding.
  * `whMarginTail_even`, `whMarginTail_odd`, `whMarginTailOfCeilings`, `whAllSMarginOfCeilings` — the
    parity assembly reducing `WHMarginTail` / `WHAllSMargin` to `WHTailCeilings`.

NAMED OPEN (Type-level structure, never `sorry`):
  * `WHTailCeilings` — the two full-window θ-envelope ceilings (the reflect-and-fold θ-sum bound).

HONEST VERDICT.  This module CLOSES the entire arithmetic backbone of the `WHMarginTail` residual —
both peak comparisons and the central lower bounds — reducing `WHAllSMargin` to just the two
full-window θ-ceilings `WHTailCeilings`.  It does NOT inhabit those ceilings.  This is a structural
sharpening of one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.WHMarginTailClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.WHMarginTailClose.gWin_symm
#print axioms YMGap.Continuum.WHMarginTailClose.acN_range_mono
#print axioms YMGap.Continuum.WHMarginTailClose.fsum_three_term_le
#print axioms YMGap.Continuum.WHMarginTailClose.peak_even_arith
#print axioms YMGap.Continuum.WHMarginTailClose.peak_odd_arith
#print axioms YMGap.Continuum.WHMarginTailClose.whMarginTail_even
#print axioms YMGap.Continuum.WHMarginTailClose.whMarginTail_odd
#print axioms YMGap.Continuum.WHMarginTailClose.whMarginTailOfCeilings
#print axioms YMGap.Continuum.WHMarginTailClose.whAllSMarginOfCeilings
