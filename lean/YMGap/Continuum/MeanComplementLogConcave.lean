/-
Track CB-lc / local-CLT — the AGGREGATE line-sum log-concavity RECAST of the complement half
`MeanShiftComplementHalf` (atom `msch`), reducing the tight cross-product second-difference to a
single subtraction-free curvature floor written purely in the module's own line-sums
`acnFmom` / `acN` / `pmomN`.

# What this module adds (read first — load-bearing honesty)

`XMeanSecondDiffProgress.MeanShiftComplementHalf w` is the genuinely-decoupled complement half
`d2x − dB ≤ 1/2` of the tight shift second-difference, cleared over `A_s·A_{s+1}·A_{s+2}` in a
`×2` cross-product (`X`) form.  Its `X`/`P` presentation obscures the analytic object.  Using the
two ALREADY-PROVED identities of `MeanExpConvexProgress`

  * `mu_eq`                     :  `F_t + 2·X_t ≃ C₄(t)·A_t`   (the moment identity `μ = C₄ − 2⟨x⟩`),
  * `casimir_secondDiff_eq_two` :  `C₄(s) + C₄(s+2) = 2·C₄(s+1) + 2`  (constant curvature `Δ²C₄ = 2`),

the complement half is EXACTLY the aggregate mean-curvature floor (⋆)

    Δ²_t μ(t)  ≥  1 − 2·dB,      i.e.   μ(s) + μ(s+2) − 2μ(s+1)  ≥  1 − 2·(⟨p⟩_{s+2} − ⟨p⟩_{s+1}),

cleared over `A_s·A_{s+1}·A_{s+2} > 0` into the subtraction-free line-sum inequality

    A_s·(A_1·A_2) + 2·(F_1·(A_s·A_2)) + 2·(P_1·(A_s·A_2))
      ≤ F_s·(A_1·A_2) + F_2·(A_s·A_1) + 2·(P_2·(A_s·A_1)),                 (`AggMeanCurvatureFloor`)

with `A_t = acN w (s+1) t`, `F_t = acnFmom w (s+1) t`, `P_t = pmomN w (s+1) t` and the window
abbreviations `A_1 = A_{s+1}`, `A_2 = A_{s+2}`, etc.  Since the ALREADY-PROVED companion half
`MeanShiftHalf` gives `dB ≤ 1/2`, the RHS `1 − 2dB ≥ 0`, so (⋆) is STRICTLY STRONGER than the
first-order midpoint convexity `Δ²μ ≥ 0` (`MeanExpConvex`); the complement half is the genuinely
harder of the two decoupled halves.

# What this module proves (all axiom-clean, `[propext]` / `[propext, Quot.sound]`)

  * `complementBridge` — the pure-`Q'` combination core: from the three per-window moment identities
    (`F_t + 2·X_t ≃ C_t·A_t`), the constant-curvature relation (`C_s + C_2 ≃ 2·C_1 + 2`), the numeric
    doubling `2·(A_s·(A_1·A_2)) ≃ A_s·(A_1·A_2) + A_s·(A_1·A_2)`, and the AGGREGATE curvature floor
    (`F`/`P` form), the `msch` cross-product inequality (`X`/`P` form) follows.  Every bridging
    identity is SUBTRACTION-FREE (closed by the reused `ring_qeqv`); the sole cancellation is the one
    common block `+B/−B` (`le_of_add_le_add_right`).  This is the machine-checked (⋆) ⟺ `msch`
    substitution.
  * `meanShiftComplementHalf_of_aggFloor` — **THE REDUCTION**: an `AggMeanCurvatureFloor w` witness
    inhabits `XMeanSecondDiffProgress.MeanShiftComplementHalf w` (instantiate `complementBridge` per
    window with `mu_eq`, `casimirEqv`, `two_mul_eqv`).
  * `meanExpConvex_of_aggFloor_msh` — the composite: `MeanShiftHalf w ∧ AggMeanCurvatureFloor w`
    inhabits `FusionMarginMonotone.MeanExpConvex w`, chaining `meanExpConvex_of_halves`.

# NAMED OPEN (Type-level structure, never `sorry`)

  * `AggMeanCurvatureFloor w` — the aggregate mean-curvature floor `Δ²μ ≥ 1 − 2dB`, cleared over
    `A_s·A_{s+1}·A_{s+2}` in subtraction-free line-sum form.  It is EQUIVALENT to
    `MeanShiftComplementHalf` (via the two proved identities), so it is the honest relocation of the
    complement half onto a single aggregate log-concavity datum — the second-order (strong-log-
    concavity / Efron-variance) analogue of the first-order mean-shift `dB ≤ 1/2`.  Universal-sign,
    corner-tight at the even-`s`, `w → 0` two-point tie; NOT provably-empty, NOT circular.

# HONEST VERDICT

A recast + genuine reduction: the `X`/`P` complement half `msch` is relocated onto the aggregate
line-sum curvature floor `AggMeanCurvatureFloor`, using ONLY the already-proved `mu_eq` +
`casimir_secondDiff_eq_two`.  This NAMES the sharpest aggregate datum and connects it to the
mass-gap chain (`… ⟹ MeanExpConvex`), but does NOT close it: `AggMeanCurvatureFloor` is corner-tight
(exact cancellation `Δ²Var → −½` vs `dB → +½`), so the local-CLT crux is relocated, not removed.
The Clay Yang–Mills mass gap remains OPEN (reduction mode).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` arithmetic, the reused `ring_qeqv` cancellation-free ring closer (subtraction-free only —
every use here is subtraction-free), the `Nat→Q'` moment identity `mu_eq`, the constant-curvature
relation `casimirEqv`, and the numeric doubling `two_mul_eqv`.  Every load-bearing declaration is
gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.XMeanSecondDiffProgress

namespace YMGap.Continuum.MeanComplementLogConcave

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.FusionMarginMonotone
open YMGap.Continuum.MeanExpConvexProgress
open YMGap.Continuum.XMeanSecondDiffProgress

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The pure-`Q'` combination core: aggregate floor (`F`/`P`) ⟹ complement half (`X`/`P`). -/

/-- **`complementBridge`** — the machine-checked `(⋆) ⟹ msch` substitution.

From
  * `hs`, `h1`, `h2` — the per-window moment identities `F_t + two·X_t ≃ c_t·A_t`  (`mu_eq`);
  * `hcas` — the constant-curvature relation `c_s + c_2 ≃ two·c_1 + two`  (`casimirEqv`);
  * `hdbl` — the numeric doubling `two·(A_s·(A_1·A_2)) ≃ A_s·(A_1·A_2) + A_s·(A_1·A_2)`  (`two_mul_eqv`);
  * `hAgg` — the AGGREGATE curvature floor (`F`/`P` cleared form),

the complement-half (`X`/`P` cleared) inequality follows.  Adding the `X`-augmentation `E` to both
sides of `hAgg`, folding `F_1 + two·X_1 → c_1·A_1` on the left and `F_s + two·X_s → c_s·A_s`,
`F_2 + two·X_2 → c_2·A_2` on the right, then collapsing `c_s + c_2 → two·c_1 + two` and splitting the
single `two·(A_s·(A_1·A_2))` via `hdbl`, both augmented sides reduce to `target + B` with a common
block `B = A_s·(A_1·A_2) + two·(c_1·(A_s·(A_1·A_2)))`; `le_of_add_le_add_right` strips `B`. -/
theorem complementBridge
    (As A1 A2 Xs X1 X2 P1 P2 Fs F1 F2 cs c1 c2 two : Q')
    (hs : (Fs + two * Xs).eqv (cs * As))
    (h1 : (F1 + two * X1).eqv (c1 * A1))
    (h2 : (F2 + two * X2).eqv (c2 * A2))
    (hcas : (cs + c2).eqv (two * c1 + two))
    (hdbl : (two * (As * (A1 * A2))) ≈ (As * (A1 * A2) + As * (A1 * A2)))
    (hAgg : As * (A1 * A2) + two * (F1 * (As * A2)) + two * (P1 * (As * A2))
              ≤ Fs * (A1 * A2) + F2 * (As * A1) + two * (P2 * (As * A1))) :
    two * (Xs * (A1 * A2)) + two * (X2 * (As * A1)) + two * (P1 * (As * A2))
      ≤ As * (A1 * A2) + two * (two * (X1 * (As * A2))) + two * (P2 * (As * A1)) := by
  -- add the `X`-augmentation `E` to both sides of the aggregate floor
  have hsum :
      (As * (A1 * A2) + two * (F1 * (As * A2)) + two * (P1 * (As * A2)))
        + (two * (Xs * (A1 * A2)) + two * (X2 * (As * A1)) + two * (two * (X1 * (As * A2))))
      ≤ (Fs * (A1 * A2) + F2 * (As * A1) + two * (P2 * (As * A1)))
        + (two * (Xs * (A1 * A2)) + two * (X2 * (As * A1)) + two * (two * (X1 * (As * A2)))) :=
    Q'.add_le_add_right _ _
      (two * (Xs * (A1 * A2)) + two * (X2 * (As * A1)) + two * (two * (X1 * (As * A2)))) hAgg
  -- LHS: fold `two·F_1 + two·(two·X_1) → two·(c_1·A_1·…)`  (uses `h1`)
  have eLa :
      ((As * (A1 * A2) + two * (F1 * (As * A2)) + two * (P1 * (As * A2)))
        + (two * (Xs * (A1 * A2)) + two * (X2 * (As * A1)) + two * (two * (X1 * (As * A2)))))
      ≈ (two * ((F1 + two * X1) * (As * A2))
          + (two * (P1 * (As * A2)) + two * (Xs * (A1 * A2)) + two * (X2 * (As * A1))
              + As * (A1 * A2))) := by ring_qeqv
  have eLb :
      (two * ((F1 + two * X1) * (As * A2))
          + (two * (P1 * (As * A2)) + two * (Xs * (A1 * A2)) + two * (X2 * (As * A1))
              + As * (A1 * A2)))
      ≈ (two * ((c1 * A1) * (As * A2))
          + (two * (P1 * (As * A2)) + two * (Xs * (A1 * A2)) + two * (X2 * (As * A1))
              + As * (A1 * A2))) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left two _ _ (Q'.mul_eqv_congr_right _ _ (As * A2) h1))
  have eLc :
      (two * ((c1 * A1) * (As * A2))
          + (two * (P1 * (As * A2)) + two * (Xs * (A1 * A2)) + two * (X2 * (As * A1))
              + As * (A1 * A2)))
      ≈ ((two * (Xs * (A1 * A2)) + two * (X2 * (As * A1)) + two * (P1 * (As * A2)))
          + (As * (A1 * A2) + two * (c1 * (As * (A1 * A2))))) := by ring_qeqv
  have eL := Q'.eqv_trans _ _ _ eLa (Q'.eqv_trans _ _ _ eLb eLc)
  -- RHS: fold `F_s + two·X_s → c_s·A_s`, `F_2 + two·X_2 → c_2·A_2`, collapse curvature, split via `hdbl`
  have eRa :
      ((Fs * (A1 * A2) + F2 * (As * A1) + two * (P2 * (As * A1)))
        + (two * (Xs * (A1 * A2)) + two * (X2 * (As * A1)) + two * (two * (X1 * (As * A2)))))
      ≈ (((Fs + two * Xs) * (A1 * A2) + (F2 + two * X2) * (As * A1))
          + (two * (P2 * (As * A1)) + two * (two * (X1 * (As * A2))))) := by ring_qeqv
  have eRb :
      (((Fs + two * Xs) * (A1 * A2) + (F2 + two * X2) * (As * A1))
          + (two * (P2 * (As * A1)) + two * (two * (X1 * (As * A2)))))
      ≈ (((cs * As) * (A1 * A2) + (c2 * A2) * (As * A1))
          + (two * (P2 * (As * A1)) + two * (two * (X1 * (As * A2))))) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ (A1 * A2) hs)
        (Q'.mul_eqv_congr_right _ _ (As * A1) h2))
  have eRc :
      (((cs * As) * (A1 * A2) + (c2 * A2) * (As * A1))
          + (two * (P2 * (As * A1)) + two * (two * (X1 * (As * A2)))))
      ≈ ((cs + c2) * (As * (A1 * A2))
          + (two * (P2 * (As * A1)) + two * (two * (X1 * (As * A2))))) := by ring_qeqv
  have eRd :
      ((cs + c2) * (As * (A1 * A2))
          + (two * (P2 * (As * A1)) + two * (two * (X1 * (As * A2)))))
      ≈ ((two * c1 + two) * (As * (A1 * A2))
          + (two * (P2 * (As * A1)) + two * (two * (X1 * (As * A2))))) :=
    Q'.add_eqv_congr_right _ _ _ (Q'.mul_eqv_congr_right _ _ (As * (A1 * A2)) hcas)
  have eRe1 :
      ((two * c1 + two) * (As * (A1 * A2))
          + (two * (P2 * (As * A1)) + two * (two * (X1 * (As * A2)))))
      ≈ (two * (As * (A1 * A2))
          + (two * (c1 * (As * (A1 * A2)))
              + (two * (P2 * (As * A1)) + two * (two * (X1 * (As * A2)))))) := by ring_qeqv
  have eRe2 :
      (two * (As * (A1 * A2))
          + (two * (c1 * (As * (A1 * A2)))
              + (two * (P2 * (As * A1)) + two * (two * (X1 * (As * A2))))))
      ≈ ((As * (A1 * A2) + As * (A1 * A2))
          + (two * (c1 * (As * (A1 * A2)))
              + (two * (P2 * (As * A1)) + two * (two * (X1 * (As * A2)))))) :=
    Q'.add_eqv_congr_right _ _ _ hdbl
  have eRe3 :
      ((As * (A1 * A2) + As * (A1 * A2))
          + (two * (c1 * (As * (A1 * A2)))
              + (two * (P2 * (As * A1)) + two * (two * (X1 * (As * A2))))))
      ≈ ((As * (A1 * A2) + two * (two * (X1 * (As * A2))) + two * (P2 * (As * A1)))
          + (As * (A1 * A2) + two * (c1 * (As * (A1 * A2))))) := by ring_qeqv
  have eR := Q'.eqv_trans _ _ _ eRa (Q'.eqv_trans _ _ _ eRb
    (Q'.eqv_trans _ _ _ eRc (Q'.eqv_trans _ _ _ eRd
      (Q'.eqv_trans _ _ _ eRe1 (Q'.eqv_trans _ _ _ eRe2 eRe3)))))
  -- both augmented sides now read `target + B` with the common block `B`
  have hL2 :
      ((two * (Xs * (A1 * A2)) + two * (X2 * (As * A1)) + two * (P1 * (As * A2)))
          + (As * (A1 * A2) + two * (c1 * (As * (A1 * A2)))))
      ≤ ((As * (A1 * A2) + two * (two * (X1 * (As * A2))) + two * (P2 * (As * A1)))
          + (As * (A1 * A2) + two * (c1 * (As * (A1 * A2))))) :=
    le_of_eqvL (Q'.eqv_symm eL) (le_of_eqvR hsum eR)
  exact le_of_add_le_add_right hL2

/-! ## 2. The aggregate mean-curvature floor (named open Type-level residual). -/

/-- **`AggMeanCurvatureFloor w`** — the aggregate mean-curvature floor `Δ²μ ≥ 1 − 2dB`, cleared over
`acN_s·acN_{s+1}·acN_{s+2}` in subtraction-free line-sum form:

    acN_s·(acN_{s+1}·acN_{s+2}) + 2·(acnFmom_{s+1}·(acN_s·acN_{s+2})) + 2·(pmomN_{s+1}·(acN_s·acN_{s+2}))
      ≤ acnFmom_s·(acN_{s+1}·acN_{s+2}) + acnFmom_{s+2}·(acN_s·acN_{s+1}) + 2·(pmomN_{s+2}·(acN_s·acN_{s+1})).

Via the proved `mu_eq` + `casimir_secondDiff_eq_two` this is EQUIVALENT to
`XMeanSecondDiffProgress.MeanShiftComplementHalf w` (the `X`/`P` complement half); it is the honest
relocation of the complement half onto a single aggregate log-concavity datum (the second-order
Efron / strong-log-concavity-under-convolution analogue of `dB ≤ 1/2`).  Universal-sign,
corner-tight at the even-`s`, `w → 0` two-point tie; NOT provably-empty, NOT circular.
NAMED-OPEN (never `sorry`). -/
structure AggMeanCurvatureFloor (w : Q') : Type where
  amcf : ∀ s,
    acN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))
        + Q'.ofNat 2 * (acnFmom w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2)))
        + Q'.ofNat 2 * (pmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2)))
      ≤ acnFmom w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))
        + acnFmom w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1))
        + Q'.ofNat 2 * (pmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1)))

/-! ## 3. THE REDUCTION and the composite. -/

/-- **`meanShiftComplementHalf_of_aggFloor` — THE REDUCTION.**  An `AggMeanCurvatureFloor w` witness
inhabits `XMeanSecondDiffProgress.MeanShiftComplementHalf w`: instantiate `complementBridge` per
window with the three moment identities `mu_eq w s t`, the constant-curvature relation `casimirEqv s`,
and the numeric doubling `two_mul_eqv`.  This is the honest relocation of the `X`/`P` complement half
onto the aggregate line-sum curvature floor. -/
def meanShiftComplementHalf_of_aggFloor {w : Q'} (H : AggMeanCurvatureFloor w) :
    MeanShiftComplementHalf w where
  msch := fun s =>
    complementBridge
      (acN w (s + 1) s) (acN w (s + 1) (s + 1)) (acN w (s + 1) (s + 2))
      (xmomN w (s + 1) s) (xmomN w (s + 1) (s + 1)) (xmomN w (s + 1) (s + 2))
      (pmomN w (s + 1) (s + 1)) (pmomN w (s + 1) (s + 2))
      (acnFmom w (s + 1) s) (acnFmom w (s + 1) (s + 1)) (acnFmom w (s + 1) (s + 2))
      (Q'.ofNat (c4 s)) (Q'.ofNat (c4 (s + 1))) (Q'.ofNat (c4 (s + 2)))
      (Q'.ofNat 2)
      (mu_eq w s s (Nat.le_refl s))
      (mu_eq w s (s + 1) (by omega))
      (mu_eq w s (s + 2) (by omega))
      (casimirEqv s)
      (two_mul_eqv (acN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))))
      (H.amcf s)

/-- **`meanExpConvex_of_aggFloor_msh` — the composite.**  For `0 ≤ w`, a `MeanShiftHalf w` witness
together with an `AggMeanCurvatureFloor w` witness inhabits `FusionMarginMonotone.MeanExpConvex w`,
chaining `meanShiftComplementHalf_of_aggFloor` through the existing `meanExpConvex_of_halves`. -/
def meanExpConvex_of_aggFloor_msh {w : Q'} (hw0 : (0 : Q') ≤ w)
    (M : MeanShiftHalf w) (H : AggMeanCurvatureFloor w) : MeanExpConvex w :=
  meanExpConvex_of_halves hw0 M (meanShiftComplementHalf_of_aggFloor H)

/-! ## 4. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `complementBridge` — the pure-`Q'` combination `(⋆) ⟹ msch` (aggregate `F`/`P` floor ⟹ `X`/`P`
    complement half), using the proved moment/curvature identities as hypotheses.
  * `meanShiftComplementHalf_of_aggFloor` — THE REDUCTION
    `AggMeanCurvatureFloor w ⟹ MeanShiftComplementHalf w`.
  * `meanExpConvex_of_aggFloor_msh` — the composite `MeanShiftHalf ∧ AggMeanCurvatureFloor ⟹
    MeanExpConvex`.

NAMED OPEN (Type-level structure, never `sorry`):
  * `AggMeanCurvatureFloor w` — the aggregate mean-curvature floor `Δ²μ ≥ 1 − 2dB` (universal-sign,
    corner-tight); EQUIVALENT to `MeanShiftComplementHalf` via `mu_eq` + `casimir_secondDiff_eq_two`.

HONEST VERDICT.  A recast + genuine reduction, NOT a closure.  The `X`/`P` complement half is
relocated onto the aggregate line-sum curvature floor using ONLY already-proved identities.  The
floor is corner-tight (exact `Δ²Var → −½` vs `dB → +½` cancellation at the even-`s`, `w → 0` two-point
tie), so the local-CLT crux is relocated, not removed.  The Clay Yang–Mills mass gap remains OPEN. -/

end YMGap.Continuum.MeanComplementLogConcave

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MeanComplementLogConcave.complementBridge
#print axioms YMGap.Continuum.MeanComplementLogConcave.meanShiftComplementHalf_of_aggFloor
#print axioms YMGap.Continuum.MeanComplementLogConcave.meanExpConvex_of_aggFloor_msh
