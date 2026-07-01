/-
Track A / R2 — the ANDRÉIEF HALF-SUM EXPANSION of the central-autoconvolution defect into the
symmetrized off-diagonal Menon minor `symMinor`, and the reduction of the autoconvolution
reserve to a single Gershgorin domination residual.

# What this module adds (read first — load-bearing honesty)

Round I reduced the fusion-box log-concavity node to the SINGLE open reserve
`AutoconvReserveResidual.reserve`; Round J supplied the diagonal `(3/4)` minor reserve and
MACHINE-CHECKED that the symmetrized off-diagonal minor `symMinor(m,n)` is indefinite (strictly
negative at spread `|m−n| = 2`); `LocalCLTSteepestDescent` recast the reserve as the equivalent
autoconvolution DEFECT `H0auto(s+1)² − H0auto(s)·H0auto(s+2)` and proved the diagonal + first
off-diagonal band of the governing `symMinor` quadratic form is `≥ 0`, LOCATING the indefinite
content at spread `|i−j| ≥ 2`.  What was left open there is (i) the DEFECT ↦ `Σ_{i,j} c_i c_j
symMinor(s−i,s−j)` expansion identity (the Andréief half-sum of the autoconvolution square) and
(ii) the aggregate Gershgorin domination of the `|i−j| ≥ 2` `symMinor` tail.

This module CLOSES (i) — the expansion identity — in full, at a fixed common index range, and
reduces (ii) to one named residual.

DELIVERABLE (a) — THE ANDRÉIEF HALF-SUM IDENTITY (PROVED, axiom-clean).
  * `acN` — the range-`n` central autoconvolution `Σ_{p<n} c_p·c_{s−p}` (the untruncated
    idealization the `min 1 nP → 1` collapse of `H0auto` targets on `t ≤ N`).
  * `autoTerm` — the `(i,j)` summand of `acN(s)·acN(s+2) − acN(s+1)²`.
  * `swap_core` — the pure 8-variable `Q'` distributive identity underlying the half-sum.
  * `autoTerm_swap_eq_symMinor` — THE LOAD-BEARING POINTWISE IDENTITY: for `i,j ≤ s`,
        autoTerm(s,i,j) + autoTerm(s,j,i)  ≃  −(c_i·c_j·symMinor(s−i, s−j)).
    The single-sequence analogue of Round F's `term2_swap_eq_minorProd`/`plucker8`; it confirms
    the sign and the factor-2 the whole expansion rests on.
  * `acN_defect_eq_termSum` — `acN(s)·acN(s+2) − acN(s+1)² ≃ Σ_i Σ_j autoTerm(s,i,j)`
    (`fsum_mul_fsum` twice; the exact clone of `Mdet_eq_termSum`).
  * `acN_defect_double_eq` — THE HALF-SUM: for `n ≤ s+1` (so every summand has `i,j ≤ s`),
        2·(acN(s)·acN(s+2) − acN(s+1)²)  ≃  Σ_i Σ_j −(c_i·c_j·symMinor(s−i,s−j)),
    equivalently `2·(acN(s+1)² − acN(s)·acN(s+2)) ≃ Σ_i Σ_j c_i c_j symMinor(s−i,s−j)`.  The
    exact clone of `Mdet_double_eq`.

REDUCTION (b) — the reserve reduced to ONE Gershgorin domination (REDUCTION, not closure).
  * `SymMinorGershgorin w` — the SOLE remaining sharp inequality on the range-`(s+1)` block:
        2·δ·(acN(s)·acN(s+2))  ≤  Σ_{i,j<s+1} c_i c_j symMinor(s−i,s−j),   δ = 31/225.
    This is exactly the aggregate cancellation `LocalCLTSteepestDescent` located: the diagonal
    `(3/4)` reserve dominating the `|i−j| ≥ 2` leak.  NAMED-OPEN (never `sorry`).
  * `acN_defect_reserve_of_gershgorin` — a Gershgorin witness YIELDS the range-`(s+1)` defect
    reserve `δ·(acN(s)·acN(s+2)) ≤ acN(s+1)² + −(acN(s)·acN(s+2))` (cancel the positive `2`
    against the half-sum identity).

# HONESTY — what is NOT closed

`SymMinorGershgorin w` is NAMED-OPEN; this module does NOT inhabit it.  It closes the Andréief
half-sum EXPANSION IDENTITY (the deliverable-(a) content that `LocalCLTSteepestDescent` left
open) and reduces the reserve to the single aggregate Gershgorin domination.  Two gaps remain:
the Gershgorin domination itself (the genuine heat-kernel local-CLT wall), and the
truncation-edge BRIDGE from the uniform-range `acN(s+1, ·)` block used here to the per-level
natural ranges of `H0auto(N, ·)` (which the `AutoconvDefectReserve` on `H0auto` needs).  This is
a structural sharpening of one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass
gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW`/`symMinor`/`fsum` lemmas, the `fsum_mul_fsum`/
`fsum_swap`/`q2_add`/`q2_neg` finite-sum algebra, and `omega` on index identities.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are
`Type`-level data.
-/

import YMGap.Continuum.LocalCLTSteepestDescent

namespace YMGap.Continuum.AutoconvGershgorin

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionCoreStepRoundF
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.FusionCoreStepRoundJ

/-! ## 0. Small `Q'` rearrangement helpers -/

/-- **`add4_rearrange`** — the commutative-monoid reshuffle
`(z + z) + (x + y) ≃ (x + z) + (y + z)` (both sides `≃ (x + y) + (z + z)`). -/
theorem add4_rearrange (x y z : Q') :
    ((z + z) + (x + y)).eqv ((x + z) + (y + z)) := by
  have hL : ((z + z) + (x + y)).eqv ((x + y) + (z + z)) := Q'.add_comm_eqv (z + z) (x + y)
  have hR : ((x + z) + (y + z)).eqv ((x + y) + (z + z)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (x + z) y z)) ?_
    have h1 : ((x + z) + y).eqv ((x + y) + z) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv x z y) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left x (z + y) (y + z) (Q'.add_comm_eqv z y)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv x y z)
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right ((x + z) + y) ((x + y) + z) z h1) ?_
    exact Q'.add_assoc_eqv (x + y) z z
  exact Q'.eqv_trans _ _ _ hL (Q'.eqv_symm hR)

/-- **`neg_defect_comm`** — `−(X + −Y) ≃ Y + −X`. -/
theorem neg_defect_comm (X Y : Q') : (-(X + -Y)).eqv (Y + -X) := by
  refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv X (-Y)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (-X) (-(-Y)) Y (Q'.neg_neg_eqv Y)) ?_
  exact Q'.add_comm_eqv (-X) Y

/-! ## 1. The pure `Q'` half-sum monomial identity -/

/-- **`swap_core`** — the single-sequence Andréief monomial identity over `Q'`:

    ((a·P)·(b·Q) − (a·R)·(b·S))  +  ((b·U)·(a·V) − (b·S)·(a·R))
      ≃  −((a·b)·((R·S + R·S) − (P·Q + U·V))).

Both sides `≃ ((a·b)·(P·Q) − (a·b)·(R·S)) + ((a·b)·(U·V) − (a·b)·(R·S))`.  Pure distributivity
(`mul_swap4`, `mul_add`/`add_mul`, the neg combinators) + `add4_rearrange`. -/
theorem swap_core (a b P Q R S U V : Q') :
    (((a * P) * (b * Q) + -((a * R) * (b * S)))
      + ((b * U) * (a * V) + -((b * S) * (a * R)))).eqv
      (-((a * b) * ((R * S + R * S) + -(P * Q + U * V)))) := by
  -- LHS ≃ E (per-term).
  have h1 : ((a * P) * (b * Q)).eqv ((a * b) * (P * Q)) := mul_swap4 a P b Q
  have h2 : (-((a * R) * (b * S))).eqv (-((a * b) * (R * S))) :=
    Q'.neg_eqv_congr _ _ (mul_swap4 a R b S)
  have h3 : ((b * U) * (a * V)).eqv ((a * b) * (U * V)) :=
    Q'.eqv_trans _ _ _ (mul_swap4 b U a V)
      (Q'.mul_eqv_congr_right (b * a) (a * b) (U * V) (Q'.mul_comm_eqv b a))
  have h4 : (-((b * S) * (a * R))).eqv (-((a * b) * (R * S))) :=
    Q'.neg_eqv_congr _ _
      (Q'.eqv_trans _ _ _ (mul_swap4 b S a R)
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right (b * a) (a * b) (S * R) (Q'.mul_comm_eqv b a))
          (Q'.mul_eqv_congr_left (a * b) (S * R) (R * S) (Q'.mul_comm_eqv S R))))
  have hLHS :
      (((a * P) * (b * Q) + -((a * R) * (b * S)))
        + ((b * U) * (a * V) + -((b * S) * (a * R)))).eqv
        (((a * b) * (P * Q) + -((a * b) * (R * S)))
          + ((a * b) * (U * V) + -((a * b) * (R * S)))) :=
    Q'.add_eqv_congr' (Q'.add_eqv_congr' h1 h2) (Q'.add_eqv_congr' h3 h4)
  -- RHS ≃ E.
  have eInner :
      ((a * b) * ((R * S + R * S) + -(P * Q + U * V))).eqv
        (((a * b) * (R * S) + (a * b) * (R * S))
          + -((a * b) * (P * Q) + (a * b) * (U * V))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (a * b) (R * S + R * S) (-(P * Q + U * V))) ?_
    refine Q'.add_eqv_congr' (Q'.mul_add_eqv (a * b) (R * S) (R * S)) ?_
    exact Q'.eqv_trans _ _ _ (Q'.mul_neg_eqv (a * b) (P * Q + U * V))
      (Q'.neg_eqv_congr _ _ (Q'.mul_add_eqv (a * b) (P * Q) (U * V)))
  have hRHS_F :
      (-((a * b) * ((R * S + R * S) + -(P * Q + U * V)))).eqv
        ((-((a * b) * (R * S)) + -((a * b) * (R * S)))
          + ((a * b) * (P * Q) + (a * b) * (U * V))) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ eInner) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.neg_add_eqv ((a * b) * (R * S) + (a * b) * (R * S))
        (-((a * b) * (P * Q) + (a * b) * (U * V)))) ?_
    exact Q'.add_eqv_congr'
      (Q'.neg_add_eqv ((a * b) * (R * S)) ((a * b) * (R * S)))
      (Q'.neg_neg_eqv ((a * b) * (P * Q) + (a * b) * (U * V)))
  have hFE :
      ((-((a * b) * (R * S)) + -((a * b) * (R * S)))
        + ((a * b) * (P * Q) + (a * b) * (U * V))).eqv
        (((a * b) * (P * Q) + -((a * b) * (R * S)))
          + ((a * b) * (U * V) + -((a * b) * (R * S)))) :=
    add4_rearrange ((a * b) * (P * Q)) ((a * b) * (U * V)) (-((a * b) * (R * S)))
  exact Q'.eqv_trans _ _ _ hLHS
    (Q'.eqv_symm (Q'.eqv_trans _ _ _ hRHS_F hFE))

/-! ## 2. The range-`n` central autoconvolution and its defect summand -/

/-- **`acN`** — the range-`n` central autoconvolution `Σ_{p<n} c_p·c_{s−p}`. -/
def acN (w : Q') (n s : Nat) : Q' :=
  fsum (fun p => coeffW w p * coeffW w (s - p)) n

/-- **`autoTerm`** — the `(i,j)` summand of `acN(s)·acN(s+2) − acN(s+1)²`. -/
def autoTerm (w : Q') (s i j : Nat) : Q' :=
  (coeffW w i * coeffW w (s - i)) * (coeffW w j * coeffW w (s + 2 - j))
    + -((coeffW w i * coeffW w (s + 1 - i)) * (coeffW w j * coeffW w (s + 1 - j)))

/-- **`autoTerm_swap_eq_symMinor` — THE LOAD-BEARING POINTWISE IDENTITY.**  For `i,j ≤ s`,

    autoTerm(s,i,j) + autoTerm(s,j,i)  ≃  −(c_i·c_j·symMinor(s−i, s−j)).

`swap_core` after normalizing the `Nat` antidiagonal arguments (`s+2−j = (s−j)+2`, etc., valid
for `i,j ≤ s`). -/
theorem autoTerm_swap_eq_symMinor {w : Q'} {s i j : Nat} (hi : i ≤ s) (hj : j ≤ s) :
    (autoTerm w s i j + autoTerm w s j i).eqv
      (-(coeffW w i * coeffW w j * symMinor w (s - i) (s - j))) := by
  unfold autoTerm symMinor
  rw [show s + 2 - j = (s - j) + 2 by omega, show s + 1 - i = (s - i) + 1 by omega,
      show s + 1 - j = (s - j) + 1 by omega, show s + 2 - i = (s - i) + 2 by omega]
  exact swap_core (coeffW w i) (coeffW w j) (coeffW w (s - i)) (coeffW w ((s - j) + 2))
    (coeffW w ((s - i) + 1)) (coeffW w ((s - j) + 1)) (coeffW w (s - j)) (coeffW w ((s - i) + 2))

/-! ## 3. The Andréief half-sum expansion -/

/-- **`acN_defect_eq_termSum`** — `acN(s)·acN(s+2) − acN(s+1)² ≃ Σ_i Σ_j autoTerm(s,i,j)`.
`fsum_mul_fsum` opens each product of column sums; the clone of `Mdet_eq_termSum`. -/
theorem acN_defect_eq_termSum (w : Q') (n s : Nat) :
    (acN w n s * acN w n (s + 2) + -(acN w n (s + 1) * acN w n (s + 1))).eqv
      (fsum (fun i => fsum (fun j => autoTerm w s i j) n) n) := by
  unfold acN autoTerm
  have hAB := fsum_mul_fsum (fun p => coeffW w p * coeffW w (s - p))
    (fun p => coeffW w p * coeffW w (s + 2 - p)) n n
  have hCD := fsum_mul_fsum (fun p => coeffW w p * coeffW w (s + 1 - p))
    (fun p => coeffW w p * coeffW w (s + 1 - p)) n n
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hAB (Q'.neg_eqv_congr _ _ hCD)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
    (q2_neg (fun i j =>
      (coeffW w i * coeffW w (s + 1 - i)) * (coeffW w j * coeffW w (s + 1 - j))) n)) ?_
  exact q2_add
    (fun i j => (coeffW w i * coeffW w (s - i)) * (coeffW w j * coeffW w (s + 2 - j)))
    (fun i j => -((coeffW w i * coeffW w (s + 1 - i)) * (coeffW w j * coeffW w (s + 1 - j))))
    n

/-- **`acN_defect_double_eq` — THE ANDRÉIEF HALF-SUM IDENTITY.**  For `n ≤ s+1` (so every
summand has `i,j ≤ s`),

    2·(acN(s)·acN(s+2) − acN(s+1)²)  ≃  Σ_i Σ_j −(c_i·c_j·symMinor(s−i,s−j)).

`acN_defect_eq_termSum ≃ Σ autoTerm(i,j) ≃ Σ autoTerm(j,i)` (the `i↔j` swap); add and apply
`autoTerm_swap_eq_symMinor` per summand.  The clone of `Mdet_double_eq`. -/
theorem acN_defect_double_eq (w : Q') (n s : Nat) (hn : n ≤ s + 1) :
    ((acN w n s * acN w n (s + 2) + -(acN w n (s + 1) * acN w n (s + 1)))
      + (acN w n s * acN w n (s + 2) + -(acN w n (s + 1) * acN w n (s + 1)))).eqv
      (fsum (fun i => fsum (fun j =>
        -(coeffW w i * coeffW w j * symMinor w (s - i) (s - j))) n) n) := by
  have hS := acN_defect_eq_termSum w n s
  have hSwap : (fsum (fun i => fsum (fun j => autoTerm w s i j) n) n).eqv
      (fsum (fun i => fsum (fun j => autoTerm w s j i) n) n) :=
    fsum_swap (fun i j => autoTerm w s i j) n n
  have hS' : (acN w n s * acN w n (s + 2) + -(acN w n (s + 1) * acN w n (s + 1))).eqv
      (fsum (fun i => fsum (fun j => autoTerm w s j i) n) n) :=
    Q'.eqv_trans _ _ _ hS hSwap
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hS hS') ?_
  refine Q'.eqv_trans _ _ _
    (q2_add (fun i j => autoTerm w s i j) (fun i j => autoTerm w s j i) n) ?_
  refine fsum_eqv_congr_lt _ _ n (fun i hi => ?_)
  refine fsum_eqv_congr_lt _ _ n (fun j hj => ?_)
  exact autoTerm_swap_eq_symMinor (by omega) (by omega)

/-! ## 4. The one-residual reduction: reserve ⟸ Gershgorin domination -/

/-- **`SymMinorGershgorin w`** — the SOLE remaining sharp inequality: the aggregate Gershgorin
domination of the `symMinor` quadratic form on the range-`(s+1)` block by twice the reserve,

    2·δ·(acN(s+1,s)·acN(s+1,s+2))  ≤  Σ_{i,j<s+1} c_i c_j symMinor(s−i,s−j),   δ = 31/225.

This is exactly the aggregate cancellation `LocalCLTSteepestDescent` located (the diagonal
`(3/4)` reserve dominating the `|i−j| ≥ 2` leak).  NAMED-OPEN (never `sorry`). -/
structure SymMinorGershgorin (w : Q') : Type where
  /-- Twice the reserve dominates the `symMinor` quadratic form (uniform in `s`). -/
  gershgorin : ∀ s,
    Q'.ofNat 2 * (Q'.mkPos 31 225 (by decide) * (acN w (s + 1) s * acN w (s + 1) (s + 2)))
      ≤ fsum (fun i => fsum (fun j =>
          coeffW w i * coeffW w j * symMinor w (s - i) (s - j)) (s + 1)) (s + 1)

/-- **`reserve_of_double_and_dom` — the pure `Q'` factor-2 cancellation core.**  From the
doubled defect identity `(A + −B) + (A + −B) ≃ −Ssym` and the domination `2·(δ·A) ≤ Ssym`,
conclude the reserve `δ·A ≤ B + −A`.  (`Ssym ≃ 2·(B + −A)` via `neg_defect_comm`, then cancel
the positive `2` with `le_of_mul_le_mul_left_pos`.) -/
theorem reserve_of_double_and_dom {A B Ssym : Q'}
    (hMD : ((A + -B) + (A + -B)).eqv (-Ssym))
    (hG : Q'.ofNat 2 * (Q'.mkPos 31 225 (by decide) * A) ≤ Ssym) :
    Q'.mkPos 31 225 (by decide) * A ≤ B + -A := by
  have hE1 : Ssym.eqv (-((A + -B) + (A + -B))) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_neg_eqv Ssym))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hMD))
  have hE2 : (-((A + -B) + (A + -B))).eqv ((B + -A) + (B + -A)) :=
    Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (A + -B) (A + -B))
      (Q'.add_eqv_congr' (neg_defect_comm A B) (neg_defect_comm A B))
  have hEfull : Ssym.eqv (Q'.ofNat 2 * (B + -A)) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ hE1 hE2)
      (Q'.eqv_symm (ofNat_two_mul_eqv (B + -A)))
  have hle : Q'.ofNat 2 * (Q'.mkPos 31 225 (by decide) * A) ≤ Q'.ofNat 2 * (B + -A) :=
    Q'.le_trans' _ _ _ hG (Q'.le_of_eqv hEfull)
  exact le_of_mul_le_mul_left_pos (Q'.ofNat_succ_pos 1) hle

/-- **`acN_defect_reserve_of_gershgorin` — THE REDUCTION.**  A Gershgorin witness yields the
range-`(s+1)` autoconvolution defect reserve

    δ·(acN(s)·acN(s+2))  ≤  acN(s+1)² + −(acN(s)·acN(s+2)),   δ = 31/225,

by cancelling the positive factor `2` against the half-sum identity `acN_defect_double_eq`. -/
theorem acN_defect_reserve_of_gershgorin {w : Q'} (g : SymMinorGershgorin w) (s : Nat) :
    Q'.mkPos 31 225 (by decide) * (acN w (s + 1) s * acN w (s + 1) (s + 2))
      ≤ acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1)
        + -(acN w (s + 1) s * acN w (s + 1) (s + 2)) := by
  -- (A + −B) + (A + −B) ≃ −Ssym, with A = acN(s)·acN(s+2), B = acN(s+1)², Ssym = Σ c_i c_j symMinor.
  have hMD :
      ((acN w (s + 1) s * acN w (s + 1) (s + 2)
          + -(acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1)))
        + (acN w (s + 1) s * acN w (s + 1) (s + 2)
          + -(acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1)))).eqv
        (-(fsum (fun i => fsum (fun j =>
          coeffW w i * coeffW w j * symMinor w (s - i) (s - j)) (s + 1)) (s + 1))) :=
    Q'.eqv_trans _ _ _ (acN_defect_double_eq w (s + 1) s (Nat.le_refl (s + 1)))
      (Q'.eqv_symm
        (q2_neg (fun i j => coeffW w i * coeffW w j * symMinor w (s - i) (s - j)) (s + 1)))
  exact reserve_of_double_and_dom hMD (g.gershgorin s)

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `add4_rearrange`, `neg_defect_comm`, `swap_core` — the pure `Q'` half-sum algebra.
  * `autoTerm_swap_eq_symMinor` — the pointwise identity `autoTerm(i,j)+autoTerm(j,i) ≃
    −(c_i c_j symMinor(s−i,s−j))` for `i,j ≤ s`.
  * `acN_defect_eq_termSum` — the double-sum expansion of the autoconvolution defect.
  * `acN_defect_double_eq` — THE ANDRÉIEF HALF-SUM IDENTITY (the deliverable-(a) content that
    `LocalCLTSteepestDescent` left open), at the fixed common range `n ≤ s+1`.
  * `acN_defect_reserve_of_gershgorin` — a Gershgorin witness yields the range-`(s+1)` defect
    reserve (the factor-2 cancellation).

NAMED OPEN (Type-level structure, never `sorry`):
  * `SymMinorGershgorin w` — the aggregate Gershgorin domination `2δ·(acN(s)·acN(s+2)) ≤
    Σ_{i,j} c_i c_j symMinor(s−i,s−j)`.  This is the genuine heat-kernel local-CLT wall (the
    diagonal `(3/4)` reserve dominating the `|i−j| ≥ 2` leak).

HONEST VERDICT.  This module CLOSES the Andréief half-sum expansion of the autoconvolution
defect into the `symMinor` quadratic form (deliverable (a)) and REDUCES the reserve to the
single aggregate Gershgorin domination.  It does NOT prove that domination, nor the
truncation-edge bridge from the uniform-range `acN(s+1, ·)` block to the per-level ranges of
`H0auto(N, ·)`.  This is a structural sharpening of one box-level log-concavity sub-fact; it is
NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.AutoconvGershgorin

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AutoconvGershgorin.add4_rearrange
#print axioms YMGap.Continuum.AutoconvGershgorin.neg_defect_comm
#print axioms YMGap.Continuum.AutoconvGershgorin.swap_core
#print axioms YMGap.Continuum.AutoconvGershgorin.autoTerm_swap_eq_symMinor
#print axioms YMGap.Continuum.AutoconvGershgorin.acN_defect_eq_termSum
#print axioms YMGap.Continuum.AutoconvGershgorin.acN_defect_double_eq
#print axioms YMGap.Continuum.AutoconvGershgorin.reserve_of_double_and_dom
#print axioms YMGap.Continuum.AutoconvGershgorin.acN_defect_reserve_of_gershgorin
