/-
Track A / R2 — the moving-window edge-block bound of the fusion box TP₂ node, and the
sharp reduction of `MovingWindowEdge` to a single named sign-matching residual.

# What this module adds (read first — load-bearing honesty)

`ThetaExponentConvexity.gramTP2_common` closes the `2×2` total-positivity minor of the
theta lag-correlation `lagCorrCR w n p q = Σ_{r<n} c_{p+r}·c_{q+r}` at ANY single common
cutoff `n`.  The growing-range `lagCorr w N p q = lagCorrCR w (N+1−max p q) p q` (RoundD)
uses a PAIR-DEPENDENT cutoff, so the four entries of its `2×2` minor live at four different
cutoffs.  `MovingWindowEdge w` (ThetaExponentConvexity) packages the reconciliation.

DELIVERABLE 1 — the geometric edge-block bound (PROVED, ~from the RoundI atoms).
  * `geoPow_add` — the trivial power-additivity split `(1/16)^{n+j} ≃ (1/16)^n·(1/16)^j`
    (the one lemma absent from RoundI).
  * `cc2_geo` — the per-term two-leg geometric decay `c_{p+σ}·c_{q+σ} ≤ (1/16)^σ·(c_p·c_q)`
    for INDEPENDENT indices `p, q` (`leg_geo`(p) ⊗ `leg_geo`(q) via `geoPow_quarter_sq`).
  * `lagCorr_movingEdge_le` — THE EDGE-BLOCK BOUND: for `n ≤ n'`,
        lagCorrCR w n' p q + -(lagCorrCR w n p q)  ≤  (16/15)·(1/16)^n·(c_p·c_q),
    i.e. the growing-vs-common range difference `Σ_{r=n}^{n'−1} c_{p+r}·c_{q+r}` is a
    super-geometric boundary strip.  Proved from `fsum_split_at` + `cc2_geo` + `geoTail_le`.
  * `lagCorr_entry_ext_le` — the same bound specialized to the actual growing-window entry:
    if `max p q ≤ max p' q'` then `lagCorr w N p q − lagCorrCR w (N+1−max p' q') p q` is a
    super-geometric strip.  This bounds the MAGNITUDE of the edge extensions `a, b, c`.

DELIVERABLE 2 — the reduction of `MovingWindowEdge` to ONE sign-matching residual.
  * `edge_algebra` — the pure-`Q'` `2×2` block identity: from the sign-matching inequality
    `a·B + A·b + a·b ≤ (C·D − A·B) + c·D` alone, conclude `(A+a)(B+b) ≤ (C+c)·D`.
  * `blockCoreDeficit_nonneg` — `gramTP2_common` rearranged: `0 ≤ C·D − A·B` at the common
    cutoff.  This certifies the residual's core RHS term is nonneg (so it is not vacuous).
  * `EdgeSignMatch w` — the SOLE remaining residual: the sign-matching inequality, stated on
    the concrete entries at the maximal common cutoff `N+1−max p' q'` (where the `(p',q')`
    entry's edge extension is exactly `0`).
  * `movingWindowEdgeOfSignMatch` — THE REDUCTION: a `EdgeSignMatch w` witness inhabits the
    full `MovingWindowEdge w` (pure algebra via `edge_algebra`).

# HONESTY — what is NOT closed

`lagCorr_movingEdge_le` and `lagCorr_entry_ext_le` are PROVED.  They bound the MAGNITUDE of
the negative edge residue `a·B + A·b + a·b` super-geometrically, but they do NOT by
themselves force the sign match against the (also-small) core deficit `(C·D − A·B) + c·D`.
`EdgeSignMatch w` is a Type-level NAMED-OPEN structure (never `sorry`): it is exactly that
one remaining sign-matching inequality.  `movingWindowEdgeOfSignMatch` is a genuine
REDUCTION (`gramTP2_common` proved ⊕ `EdgeSignMatch` residual ⟹ `MovingWindowEdge`), NOT a
closure — the geometric reserve dominates the residue's size but not its sign, so
`EdgeSignMatch` is not handed to us for free.  This is a structural sharpening of one
box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`fsum`/`lagCorrCR`/`geoPow` lemmas, finite
inductions, `omega` on the cutoff, and `decide` on closed concrete-rational facts.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are
`Type`-level data.
-/

import YMGap.Continuum.FusionCoreStepRoundI
import YMGap.Continuum.ThetaExponentConvexity

namespace YMGap.Continuum.MovingWindowEdgeClose

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionPositivity
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionCoreStepRoundF
open YMGap.Continuum.FusionCoreStepRoundG
open YMGap.Continuum.FusionCoreStepRoundI
open YMGap.Continuum.ThetaExponentConvexity

/-! ## 0. Small `Q'` add/cancel helpers -/

/-- `((X + Y) + -X) ≃ Y`. -/
theorem add_sub_cancel_left (X Y : Q') : ((X + Y) + -X).eqv Y := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (X + Y) (Y + X) (-X) (Q'.add_comm_eqv X Y)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv Y X (-X)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left Y (X + -X) 0 (Q'.add_neg_self_eqv X)) ?_
  exact q_add_zero_eqv Y

/-- `(X + (Y + -X)) ≃ Y`. -/
theorem mixAdd_eqv (X Y : Q') : (X + (Y + -X)).eqv Y := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left X (Y + -X) (-X + Y) (Q'.add_comm_eqv Y (-X))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv X (-X) Y)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (X + -X) 0 Y (Q'.add_neg_self_eqv X)) ?_
  exact q_zero_add_eqv Y

/-- Congruence of `·` in both arguments. -/
theorem mulEqv {X X' Y Y' : Q'} (hx : X.eqv X') (hy : Y.eqv Y') :
    (X * Y).eqv (X' * Y') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right X X' Y hx)
    (Q'.mul_eqv_congr_left X' Y Y' hy)

/-! ## 1. The power-additivity split (the one lemma absent from RoundI) -/

/-- **`geoPow_add`** — `r^{n+j} ≃ r^n · r^j`.  Induction on `j`. -/
theorem geoPow_add (r : Q') (n j : Nat) :
    (geoPow r (n + j)).eqv (geoPow r n * geoPow r j) := by
  induction j with
  | zero =>
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (geoPow r n) (geoPow r 0))
          (Q'.one_mul_eqv (geoPow r n)))
  | succ j ih =>
      show (r * geoPow r (n + j)).eqv (geoPow r n * (r * geoPow r j))
      have e1 : (r * geoPow r (n + j)).eqv (r * (geoPow r n * geoPow r j)) :=
        Q'.mul_eqv_congr_left r (geoPow r (n + j)) (geoPow r n * geoPow r j) ih
      have e2 : (r * (geoPow r n * geoPow r j)).eqv (geoPow r n * (r * geoPow r j)) := by
        refine Q'.eqv_trans _ _ _
          (Q'.eqv_symm (Q'.mul_assoc_eqv r (geoPow r n) (geoPow r j))) ?_
        refine Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (r * geoPow r n) (geoPow r n * r) (geoPow r j)
            (Q'.mul_comm_eqv r (geoPow r n))) ?_
        exact Q'.mul_assoc_eqv (geoPow r n) r (geoPow r j)
      exact Q'.eqv_trans _ _ _ e1 e2

/-! ## 2. The per-term two-leg geometric bound (independent indices) -/

/-- **`cc2_geo`** — the per-term two-leg geometric decay for INDEPENDENT indices
`c_{p+σ}·c_{q+σ} ≤ (1/16)^σ·(c_p·c_q)` (`leg_geo`(p) ⊗ `leg_geo`(q), combined via
`geoPow_quarter_sq`).  This is the `ccT_geo` construction with the second leg carrying its
own index `q` rather than `t−p`. -/
theorem cc2_geo {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (hwpos : (0 : Q') < w)
    (p q σ : Nat) :
    coeffW w (p + σ) * coeffW w (q + σ)
      ≤ geoPow qq16 σ * (coeffW w p * coeffW w q) := by
  have hleg1 : coeffW w (p + σ) ≤ geoPow qq4 σ * coeffW w p := leg_geo hw0 hw12 hwpos p σ
  have hleg2 : coeffW w (q + σ) ≤ geoPow qq4 σ * coeffW w q := leg_geo hw0 hw12 hwpos q σ
  have hy0 : (0 : Q') ≤ coeffW w (q + σ) := coeffW_nonneg hw0 _
  have hX : (0 : Q') ≤ geoPow qq4 σ * coeffW w p :=
    Q'.mul_nonneg _ _ (geoPow_nonneg (by decide) σ) (coeffW_nonneg hw0 _)
  have hprod : coeffW w (p + σ) * coeffW w (q + σ)
      ≤ (geoPow qq4 σ * coeffW w p) * (geoPow qq4 σ * coeffW w q) :=
    prod_le_prod hleg1 hleg2 hy0 hX
  have eswap : ((geoPow qq4 σ * coeffW w p) * (geoPow qq4 σ * coeffW w q)).eqv
      ((geoPow qq4 σ * geoPow qq4 σ) * (coeffW w p * coeffW w q)) :=
    mul_swap4 (geoPow qq4 σ) (coeffW w p) (geoPow qq4 σ) (coeffW w q)
  have esq : ((geoPow qq4 σ * geoPow qq4 σ) * (coeffW w p * coeffW w q)).eqv
      (geoPow qq16 σ * (coeffW w p * coeffW w q)) :=
    Q'.mul_eqv_congr_right _ _ _ (geoPow_quarter_sq σ)
  exact Q'.le_trans' _ _ _ hprod
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv eswap) (Q'.le_of_eqv esq))

/-! ## 3. The moving-window edge-block bound -/

/-- **`lagCorr_movingEdge_le` — THE EDGE-BLOCK BOUND (PROVED).**  For `0 < w ≤ wH`, any
`p q`, and `n ≤ n'`,

    lagCorrCR w n' p q + -(lagCorrCR w n p q)  ≤  (16/15)·(1/16)^n·(coeffW w p · coeffW w q).

The growing-vs-common range difference `Σ_{r=n}^{n'−1} c_{p+r}·c_{q+r}` is a super-geometric
boundary strip.  Proof: `fsum_split_at` isolates the shifted tail block, `cc2_geo` gives the
per-term two-leg decay with the `(1/16)^n` factor pulled out (`geoPow_add`), and `geoTail_le`
sums the residual geometric series to `16/15`. -/
theorem lagCorr_movingEdge_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) (p q : Nat) {n n' : Nat} (hnn' : n ≤ n') :
    lagCorrCR w n' p q + -(lagCorrCR w n p q)
      ≤ qq1615 * (geoPow qq16 n * (coeffW w p * coeffW w q)) := by
  have hM : n + (n' - n) = n' := by omega
  -- the range difference is the shifted tail block
  have hsplit : (lagCorrCR w n' p q).eqv
      (lagCorrCR w n p q
        + fsum (fun j => coeffW w (p + (n + j)) * coeffW w (q + (n + j))) (n' - n)) := by
    have h := fsum_split_at (fun r => coeffW w (p + r) * coeffW w (q + r)) n (n' - n)
    rw [hM] at h
    exact h
  -- per-term two-leg bound with the (1/16)^n factor split off
  have hterm : ∀ j,
      coeffW w (p + (n + j)) * coeffW w (q + (n + j))
        ≤ geoPow qq16 j * (geoPow qq16 n * (coeffW w p * coeffW w q)) := by
    intro j
    have hcc := cc2_geo hw0 hw12 hwpos p q (n + j)
    have erear : (geoPow qq16 (n + j) * (coeffW w p * coeffW w q)).eqv
        (geoPow qq16 j * (geoPow qq16 n * (coeffW w p * coeffW w q))) := by
      have e1 := Q'.mul_eqv_congr_right (geoPow qq16 (n + j))
        (geoPow qq16 n * geoPow qq16 j) (coeffW w p * coeffW w q) (geoPow_add qq16 n j)
      have e2a := Q'.mul_eqv_congr_right (geoPow qq16 n * geoPow qq16 j)
        (geoPow qq16 j * geoPow qq16 n) (coeffW w p * coeffW w q)
        (Q'.mul_comm_eqv (geoPow qq16 n) (geoPow qq16 j))
      have e2b := Q'.mul_assoc_eqv (geoPow qq16 j) (geoPow qq16 n) (coeffW w p * coeffW w q)
      exact Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2a e2b)
    exact Q'.le_trans' _ _ _ hcc (Q'.le_of_eqv erear)
  -- sum the per-term bound
  have hmono : fsum (fun j => coeffW w (p + (n + j)) * coeffW w (q + (n + j))) (n' - n)
      ≤ fsum (fun j => geoPow qq16 j * (geoPow qq16 n * (coeffW w p * coeffW w q))) (n' - n) :=
    fsum_mono hterm (n' - n)
  have hpull :
      (fsum (geoPow qq16) (n' - n) * (geoPow qq16 n * (coeffW w p * coeffW w q))).eqv
        (fsum (fun j => geoPow qq16 j * (geoPow qq16 n * (coeffW w p * coeffW w q)))
          (n' - n)) :=
    fsum_mul_const (geoPow qq16) (geoPow qq16 n * (coeffW w p * coeffW w q)) (n' - n)
  have hKnn : (0 : Q') ≤ geoPow qq16 n * (coeffW w p * coeffW w q) :=
    Q'.mul_nonneg _ _ (geoPow_nonneg (by decide) n)
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw0 p) (coeffW_nonneg hw0 q))
  have hgeo : fsum (geoPow qq16) (n' - n) * (geoPow qq16 n * (coeffW w p * coeffW w q))
      ≤ qq1615 * (geoPow qq16 n * (coeffW w p * coeffW w q)) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (geoTail_le (n' - n)) hKnn
  -- the LHS reduces to the tail block
  have hlhs : (lagCorrCR w n' p q + -(lagCorrCR w n p q)).eqv
      (fsum (fun j => coeffW w (p + (n + j)) * coeffW w (q + (n + j))) (n' - n)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right (lagCorrCR w n' p q)
        (lagCorrCR w n p q
          + fsum (fun j => coeffW w (p + (n + j)) * coeffW w (q + (n + j))) (n' - n))
        (-(lagCorrCR w n p q)) hsplit) ?_
    exact add_sub_cancel_left (lagCorrCR w n p q)
      (fsum (fun j => coeffW w (p + (n + j)) * coeffW w (q + (n + j))) (n' - n))
  -- assemble
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hlhs)
    (Q'.le_trans' _ _ _ hmono
      (Q'.le_trans' _ _ _ (Q'.ge_of_eqv hpull) hgeo))

/-- The maximal common cutoff of the `2×2` block with `p ≤ p'`, `q ≤ q'`
(the `(p',q')` corner cutoff, smallest of the four). -/
def cutMin (N p' q' : Nat) : Nat := N + 1 - Nat.max p' q'

/-- **`lagCorr_entry_ext_le`** — the edge-block bound specialized to the actual
growing-window entry.  If `max p q ≤ max p' q'` then the edge extension
`lagCorr w N p q − lagCorrCR w (cutMin N p' q') p q` is a super-geometric boundary strip.
This bounds the magnitude of the edge extensions `a, b, c` in the block reduction. -/
theorem lagCorr_entry_ext_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) (N p q p' q' : Nat) (hmax : Nat.max p q ≤ Nat.max p' q') :
    lagCorr w N p q + -(lagCorrCR w (cutMin N p' q') p q)
      ≤ qq1615 * (geoPow qq16 (cutMin N p' q') * (coeffW w p * coeffW w q)) := by
  have hle : cutMin N p' q' ≤ N + 1 - Nat.max p q := by
    unfold cutMin; omega
  have h := lagCorr_movingEdge_le hw0 hw12 hwpos p q hle
  rw [lagCorr_eq_cr]
  exact h

/-! ## 4. The pure-`Q'` `2×2` block identity -/

/-- **`edge_algebra`** — the pure-`Q'` `2×2` moving-window block identity.  Writing the four
common-cutoff entries `A = CR_{pq'}`, `B = CR_{p'q}`, `C = CR_{pq}`, `D = CR_{p'q'}` and the
edge extensions `a, b, c` (with `(p',q')`'s extension `= 0`), the growing-window minor is
`(A+a)(B+b) ≤ (C+c)·D`.  This follows PURELY ALGEBRAICALLY from the sign-matching inequality
`a·B + A·b + a·b ≤ (C·D − A·B) + c·D` (the core-deficit `C·D − A·B` is carried on its RHS, so
no separate `A·B ≤ C·D` input is needed for the algebra; that fact certifies the RHS is
nonneg — see `blockCoreDeficit_nonneg`). -/
theorem edge_algebra {A B C D a b c : Q'}
    (hsm : a * B + A * b + a * b ≤ (C * D + -(A * B)) + c * D) :
    (A + a) * (B + b) ≤ (C + c) * D := by
  -- expand the growing-window product
  have eL : ((A + a) * (B + b)).eqv (A * B + ((a * B + A * b) + a * b)) := by
    have h1 : ((A + a) * (B + b)).eqv ((A + a) * B + (A + a) * b) :=
      Q'.mul_add_eqv (A + a) B b
    have h2 : ((A + a) * B + (A + a) * b).eqv ((A * B + a * B) + (A * b + a * b)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right ((A + a) * B) (A * B + a * B) ((A + a) * b)
          (Q'.add_mul_eqv A a B)) ?_
      exact Q'.add_eqv_congr_left (A * B + a * B) ((A + a) * b) (A * b + a * b)
        (Q'.add_mul_eqv A a b)
    have h3 : ((A * B + a * B) + (A * b + a * b)).eqv
        (A * B + ((a * B + A * b) + a * b)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv (A * B) (a * B) (A * b + a * b)) ?_
      refine Q'.add_eqv_congr_left (A * B) (a * B + (A * b + a * b))
        ((a * B + A * b) + a * b) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv (a * B) (A * b) (a * b))
    exact Q'.eqv_trans _ _ _ h1 (Q'.eqv_trans _ _ _ h2 h3)
  -- expand the target product and reconstitute the core
  have eR : (A * B + ((C * D + -(A * B)) + c * D)).eqv ((C + c) * D) := by
    have r1 : (A * B + ((C * D + -(A * B)) + c * D)).eqv
        ((A * B + (C * D + -(A * B))) + c * D) :=
      Q'.eqv_symm (Q'.add_assoc_eqv (A * B) (C * D + -(A * B)) (c * D))
    have r2 : ((A * B + (C * D + -(A * B))) + c * D).eqv (C * D + c * D) :=
      Q'.add_eqv_congr_right (A * B + (C * D + -(A * B))) (C * D) (c * D)
        (mixAdd_eqv (A * B) (C * D))
    have r3 : (C * D + c * D).eqv ((C + c) * D) := Q'.eqv_symm (Q'.add_mul_eqv C c D)
    exact Q'.eqv_trans _ _ _ r1 (Q'.eqv_trans _ _ _ r2 r3)
  -- chain: (A+a)(B+b) ≃ AB + residue ≤ AB + (core-deficit) ≃ (C+c)D
  have step : A * B + ((a * B + A * b) + a * b)
      ≤ A * B + ((C * D + -(A * B)) + c * D) :=
    Q'.add_le_add_left (A * B) ((a * B + A * b) + a * b) ((C * D + -(A * B)) + c * D) hsm
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eL)
    (Q'.le_trans' _ _ _ step (Q'.le_of_eqv eR))

/-- **`blockCoreDeficit_nonneg`** — the square-core deficit at the maximal common cutoff is
nonnegative: `0 ≤ CR_{pq}·CR_{p'q'} − CR_{pq'}·CR_{p'q}`.  This is exactly `gramTP2_common`
(the proved common-range TP₂) rearranged.  It certifies that the RHS core term of
`EdgeSignMatch` is `≥ 0`, so the sign-matching residual is a genuine (not-vacuous) target. -/
theorem blockCoreDeficit_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH)
    (hwpos : (0 : Q') < w) {p q p' q' : Nat} (hpp' : p ≤ p') (hqq' : q ≤ q') (n : Nat) :
    (0 : Q') ≤ lagCorrCR w n p q * lagCorrCR w n p' q'
      + -(lagCorrCR w n p q' * lagCorrCR w n p' q) := by
  have hw1 : w ≤ (1 : Q') := Q'.le_trans' _ _ _ hw12 (by decide)
  have hcore := gramTP2_common hw0 hw1 hwpos hpp' hqq' n
  -- from `A·B ≤ C·D` add `-(A·B)` to both sides
  have hstep := Q'.add_le_add_right (lagCorrCR w n p q' * lagCorrCR w n p' q)
    (lagCorrCR w n p q * lagCorrCR w n p' q')
    (-(lagCorrCR w n p q' * lagCorrCR w n p' q)) hcore
  have hz : (0 : Q').eqv
      (lagCorrCR w n p q' * lagCorrCR w n p' q
        + -(lagCorrCR w n p q' * lagCorrCR w n p' q)) :=
    Q'.eqv_symm (Q'.add_neg_self_eqv (lagCorrCR w n p q' * lagCorrCR w n p' q))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hz) hstep

/-! ## 5. The reduction of `MovingWindowEdge` to the sign-matching residual -/

/-- **`EdgeSignMatch w`** — the SOLE remaining residual of `MovingWindowEdge` after the
proved common-range TP₂ (`gramTP2_common`) and the proved edge-block magnitude bound
(`lagCorr_movingEdge_le`).  The single sign-matching inequality: at the maximal common
cutoff `cutMin N p' q'`, the negative edge residue `a·B + A·b + a·b` is dominated by the
square-core deficit extension `(C·D − A·B) + c·D`.  NAMED-OPEN (never `sorry`); the
geometric reserve bounds the residue's magnitude but not its sign against the core. -/
structure EdgeSignMatch (w : Q') : Type where
  /-- The sign-matching inequality on the concrete entries at the maximal common cutoff. -/
  signMatch : ∀ N p q p' q', p ≤ p' → q ≤ q' →
    (lagCorr w N p q' + -(lagCorrCR w (cutMin N p' q') p q'))
        * lagCorrCR w (cutMin N p' q') p' q
      + lagCorrCR w (cutMin N p' q') p q'
        * (lagCorr w N p' q + -(lagCorrCR w (cutMin N p' q') p' q))
      + (lagCorr w N p q' + -(lagCorrCR w (cutMin N p' q') p q'))
        * (lagCorr w N p' q + -(lagCorrCR w (cutMin N p' q') p' q))
      ≤ (lagCorrCR w (cutMin N p' q') p q * lagCorrCR w (cutMin N p' q') p' q'
          + -(lagCorrCR w (cutMin N p' q') p q' * lagCorrCR w (cutMin N p' q') p' q))
        + (lagCorr w N p q + -(lagCorrCR w (cutMin N p' q') p q))
          * lagCorrCR w (cutMin N p' q') p' q'

/-- **`movingWindowEdgeOfSignMatch` — THE REDUCTION.**  A `EdgeSignMatch w` witness inhabits
the full `MovingWindowEdge w`.  The four growing-window entries are reconstituted from the
maximal common cutoff `cutMin N p' q'` plus their edge extensions (`mixAdd_eqv`; the
`(p',q')` corner extension is exactly `0`), and `edge_algebra` combines them from the
sign-matching residual.  This exhibits `EdgeSignMatch` as the ONLY inequality standing between
the proved common-range TP₂ / edge-block bound and the moving-window TP₂.  (The reduction is
pure algebra; `gramTP2_common` separately certifies the residual's core term via
`blockCoreDeficit_nonneg`.) -/
def movingWindowEdgeOfSignMatch {w : Q'} (sm : EdgeSignMatch w) : MovingWindowEdge w where
  edge := by
    intro N p q p' q' hpp' hqq'
    -- the sign-matching residual
    have hsm := sm.signMatch N p q p' q' hpp' hqq'
    -- reconstitute the growing-window entries from the common cutoff + extensions
    have e1 : (lagCorr w N p q').eqv
        (lagCorrCR w (cutMin N p' q') p q'
          + (lagCorr w N p q' + -(lagCorrCR w (cutMin N p' q') p q'))) :=
      Q'.eqv_symm (mixAdd_eqv (lagCorrCR w (cutMin N p' q') p q') (lagCorr w N p q'))
    have e2 : (lagCorr w N p' q).eqv
        (lagCorrCR w (cutMin N p' q') p' q
          + (lagCorr w N p' q + -(lagCorrCR w (cutMin N p' q') p' q))) :=
      Q'.eqv_symm (mixAdd_eqv (lagCorrCR w (cutMin N p' q') p' q) (lagCorr w N p' q))
    have e3 : (lagCorr w N p q).eqv
        (lagCorrCR w (cutMin N p' q') p q
          + (lagCorr w N p q + -(lagCorrCR w (cutMin N p' q') p q))) :=
      Q'.eqv_symm (mixAdd_eqv (lagCorrCR w (cutMin N p' q') p q) (lagCorr w N p q))
    -- the (p',q') corner lives exactly at the common cutoff
    have e4 : (lagCorr w N p' q').eqv (lagCorrCR w (cutMin N p' q') p' q') :=
      Q'.eqv_refl (lagCorr w N p' q')
    have tL := mulEqv e1 e2
    have tR := mulEqv e3 e4
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv tL)
      (Q'.le_trans' _ _ _ (edge_algebra hsm) (Q'.ge_of_eqv tR))

/-! ## 6. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `add_sub_cancel_left`, `mixAdd_eqv`, `mulEqv` — the `Q'` add/cancel helpers.
  * `geoPow_add` — the power-additivity split.
  * `cc2_geo` — the per-term two-leg geometric decay for independent indices.
  * `lagCorr_movingEdge_le` — THE EDGE-BLOCK BOUND: the range difference is a super-geometric
    boundary strip `≤ (16/15)·(1/16)^n·(c_p·c_q)`.
  * `lagCorr_entry_ext_le` — the edge extension of the actual growing-window entry.
  * `edge_algebra` — the pure-`Q'` `2×2` block identity (sign-match ⟹ minor).
  * `blockCoreDeficit_nonneg` — `gramTP2_common` rearranged: the residual's core term ≥ 0.
  * `movingWindowEdgeOfSignMatch` — THE REDUCTION: `EdgeSignMatch` ⟹ `MovingWindowEdge`.

NAMED OPEN (Type-level structure, never `sorry`):
  * `EdgeSignMatch w` — the SOLE remaining sign-matching inequality: the negative edge
    residue `a·B + A·b + a·b` dominated by the square-core deficit `(C·D − A·B) + c·D` at the
    maximal common cutoff.  The geometric reserve (`lagCorr_movingEdge_le`) bounds the
    residue's MAGNITUDE super-geometrically but not its SIGN against the core.

HONEST VERDICT.  This module PROVES the moving-window edge-block bound outright and REDUCES
`MovingWindowEdge` from "reconcile four different cutoffs" to the single named sign-matching
inequality `EdgeSignMatch` (via the proved `gramTP2_common` core and the proved
`edge_algebra` identity).  It does NOT inhabit `EdgeSignMatch`.  This is a structural
sharpening of one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.MovingWindowEdgeClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MovingWindowEdgeClose.add_sub_cancel_left
#print axioms YMGap.Continuum.MovingWindowEdgeClose.mixAdd_eqv
#print axioms YMGap.Continuum.MovingWindowEdgeClose.mulEqv
#print axioms YMGap.Continuum.MovingWindowEdgeClose.geoPow_add
#print axioms YMGap.Continuum.MovingWindowEdgeClose.cc2_geo
#print axioms YMGap.Continuum.MovingWindowEdgeClose.lagCorr_movingEdge_le
#print axioms YMGap.Continuum.MovingWindowEdgeClose.lagCorr_entry_ext_le
#print axioms YMGap.Continuum.MovingWindowEdgeClose.edge_algebra
#print axioms YMGap.Continuum.MovingWindowEdgeClose.blockCoreDeficit_nonneg
#print axioms YMGap.Continuum.MovingWindowEdgeClose.movingWindowEdgeOfSignMatch
