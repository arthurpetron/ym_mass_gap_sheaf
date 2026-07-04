/-
Track B / local-CLT — the EXACT Casimir ledger and the DIRECT antidiagonal-variance recast of the
open shift second-difference datum `XMeanSecondDiffLeOne` (`d2x ≤ 1`), onto the single cleanest
possible residual: the position-variance curvature floor `Δ²⟨D²⟩ ≥ −2`.

# What this module adds (read first — load-bearing honesty)

`MeanExpConvexProgress.XMeanSecondDiffLeOne w` (`d2x ≤ 1`, cleared over `A_s·A_{s+1}·A_{s+2}`) is the
sole open first-moment datum feeding `MeanExpConvex` after the entire Casimir/geometry has been
stripped to the exact constant `+2` (`casimir_secondDiff_eq_two : Δ²C₄ = 2`).  The moment identity
`4·⟨x⟩_t + ⟨D²⟩_t = t²·A_t` (`MeanComplementCovariance.momentTwoTwo`, with `D²_p = (t−2p)²`) plus the
constant `t²`-curvature `Δ²(t²) = 2` (`MeanComplementCovariance.sqEqv`) give the EXACT ledger

    Δ²_t ( 4·⟨x⟩_t + ⟨D²⟩_t )  =  Δ²(t²)  =  2                              (`ledgerCore`),

cleared over `A_s·A_{s+1}·A_{s+2}` in subtraction-free form.  This is the rigorous Lean form of the
independently-confirmed corner ledger `Δ²E[D²] + 4·dB = 4·(½ − dC)`: the `+2` constant-curvature term
is spent EXACTLY, so `d2x ≤ 1` becomes the manifest curvature floor

    Δ²_t ⟨D²⟩_t  ≥  −2                                                     (`TwoPointTieSubleading`).

The recast `XMeanSecondDiffLeOne ⟺ (Δ²⟨D²⟩ ≥ −2)` is a genuine ring-level `↔` (`xmsd_iff_d2var`), both
directions, with NO nonnegativity: it eliminates the cross-product statistic `⟨x⟩ = ⟨p(t−p)⟩` entirely
in favour of the antidiagonal square `⟨D²⟩`, and localises ALL open content into the single
position-variance curvature floor.

# HONEST VERDICT — the route is a sharp reduction, NOT a closure

The floor `Δ²⟨D²⟩ ≥ −2` is corner-tight BY CONSTRUCTION: at the even-`s`, `w → 0` two-point tie
(`½δ_m + ½δ_{m+1}`) the confirmed data give `Δ²⟨D²⟩ → −2` exactly (concave in `t`), saturating the
floor with slack `→ 0`.  So the residual is NOT a bare nonnegativity/variance — it is the exact
sub-leading local-CLT (Tate–Zelditch / theta `q→1`) constant of the degenerate two-point-tie window,
and the recast RELOCATES it onto the cleanest possible object without signing it.  This is a genuine
sharp reduction to a strictly-smaller NAMED residual; the Clay Yang–Mills mass gap remains OPEN
(reduction mode).

# What this module proves (all axiom-clean, `[propext]` / `[propext, Quot.sound]`)

  * `ledgerCore` — the abstract EXACT ledger `Δ²(4⟨x⟩+⟨D²⟩) = 2` (cleared, subtraction-free), from the
    three per-window moment identities (`4⟨x⟩+⟨D²⟩ ≃ t²·A`) and the constant-curvature relation.
  * `xmsd_iff_d2var_core`, `xmsd_iff_d2var` — THE EXACT RECAST: `XMeanSecondDiffLeOne`'s cleared
    inequality is a ring-level `↔` with the position-variance curvature floor `Δ²⟨D²⟩ ≥ −2`.
  * `xmsd_of_twoPointTie` — THE REDUCTION: a `TwoPointTieSubleading w` witness inhabits
    `MeanExpConvexProgress.XMeanSecondDiffLeOne w`.
  * `meanExpConvex_of_twoPointTie` — the composite `… ⟹ FusionMarginMonotone.MeanExpConvex w`
    (chained through the existing `meanExpConvex_of_xmsd`).

# NAMED OPEN (Type-level structure, never `sorry`)

  * `TwoPointTieSubleading w` — the position-variance curvature floor `Δ²⟨D²⟩ ≥ −2`, cleared over
    `A_s·A_{s+1}·A_{s+2}` in subtraction-free form.  EQUIVALENT to `XMeanSecondDiffLeOne` (via the exact
    `ledgerCore`).  Corner-tight (`→ −2` at the even-`s`, `w → 0` two-point tie); the exact sub-leading
    two-point-tie local-CLT constant, NOT a nonnegativity.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` arithmetic, the reused subtraction-free `ring_qeqv` closer (EVERY use here is
subtraction-free), the proved moment identity `momentTwoTwo`, the constant-curvature relation `sqEqv`,
and the numeric doubling `two_mul_eqv`.  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.
All witnesses are `Type`-level data.
-/

import YMGap.Continuum.MeanComplementCovariance

namespace YMGap.Continuum.MeanComplementClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.FusionMarginMonotone
open YMGap.Continuum.MeanExpConvexProgress
open YMGap.Continuum.XMeanSecondDiffProgress
open YMGap.Continuum.MeanComplementCovariance

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The abstract EXACT Casimir ledger `Δ²(4⟨x⟩ + ⟨D²⟩) = 2`.

Given the three per-window moment identities `two·(two·X_t) + D_t ≃ c_t·A_t` (i.e. `4⟨x⟩+⟨D²⟩ = t²`,
cleared of the mass `A_t`) and the constant-curvature relation `c_s + c_2 ≃ two·c_1 + two`
(i.e. `Δ²(t²) = 2`), the second difference of `4⟨x⟩+⟨D²⟩`, cleared over `A_s·A_1·A_2`, equals exactly
the constant curvature `two·(A_s·(A_1·A_2))`.  All bridging identities are SUBTRACTION-FREE
(`ring_qeqv`); the moment/curvature inputs enter only as congruences. -/

/-- **`ledgerCore`** — the abstract exact ledger

    (two·(two·Xs)+Ds)·(A1·A2) + (two·(two·X2)+D2)·(As·A1)
      ≃ two·((two·(two·X1)+D1)·(As·A2)) + two·(As·(A1·A2)),

i.e. `[4⟨x⟩+⟨D²⟩]_s + [4⟨x⟩+⟨D²⟩]_{s+2} = 2·[4⟨x⟩+⟨D²⟩]_{s+1} + 2` cleared over `A_s·A_1·A_2`. -/
theorem ledgerCore
    (As A1 A2 Xs X1 X2 Ds D1 D2 cs c1 c2 two : Q')
    (hM0 : (two * (two * Xs) + Ds).eqv (cs * As))
    (hM1 : (two * (two * X1) + D1).eqv (c1 * A1))
    (hM2 : (two * (two * X2) + D2).eqv (c2 * A2))
    (hcas : (cs + c2).eqv (two * c1 + two)) :
    ((two * (two * Xs) + Ds) * (A1 * A2) + (two * (two * X2) + D2) * (As * A1)).eqv
      (two * ((two * (two * X1) + D1) * (As * A2)) + two * (As * (A1 * A2))) := by
  -- fold `Ms → cs·As`, `M2 → c2·A2`
  have e1 :
      ((two * (two * Xs) + Ds) * (A1 * A2) + (two * (two * X2) + D2) * (As * A1)).eqv
        ((cs * As) * (A1 * A2) + (c2 * A2) * (As * A1)) :=
    Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_right _ _ (A1 * A2) hM0)
      (Q'.mul_eqv_congr_right _ _ (As * A1) hM2)
  -- collect `(cs + c2)·(As·(A1·A2))`
  have e2 :
      ((cs * As) * (A1 * A2) + (c2 * A2) * (As * A1)).eqv
        ((cs + c2) * (As * (A1 * A2))) := by ring_qeqv
  -- apply the constant-curvature relation
  have e3 :
      ((cs + c2) * (As * (A1 * A2))).eqv
        ((two * c1 + two) * (As * (A1 * A2))) :=
    Q'.mul_eqv_congr_right _ _ (As * (A1 * A2)) hcas
  -- split off the constant `two·Π` and expose the `c1·A1` factor
  have e4 :
      ((two * c1 + two) * (As * (A1 * A2))).eqv
        (two * ((c1 * A1) * (As * A2)) + two * (As * (A1 * A2))) := by ring_qeqv
  -- fold back `c1·A1 ← two·(two·X1)+D1`
  have e5 :
      (two * ((c1 * A1) * (As * A2)) + two * (As * (A1 * A2))).eqv
        (two * ((two * (two * X1) + D1) * (As * A2)) + two * (As * (A1 * A2))) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left two _ _
        (Q'.mul_eqv_congr_right _ _ (As * A2) (Q'.eqv_symm hM1)))
  exact Q'.eqv_trans _ _ _ e1
    (Q'.eqv_trans _ _ _ e2 (Q'.eqv_trans _ _ _ e3 (Q'.eqv_trans _ _ _ e4 e5)))

/-! ## 2. The exact ring-level recast `XMeanSecondDiffLeOne ⟺ (Δ²⟨D²⟩ ≥ −2)` (pure-`Q'` core). -/

/-- **`xmsd_iff_d2var_core`** — the abstract ring-level equivalence between the cleared shift
second-difference inequality `d2x ≤ 1` (LEFT, in the cross-product moment `X`) and the position-
variance curvature floor `Δ²⟨D²⟩ ≥ −2` (RIGHT, in the antidiagonal square `D`).

Both directions are proved by scaling LEFT by the positive factor `two·two`, adding the common block
`Ds·(A1·A2)+D2·(As·A1)`, rewriting through the exact ledger (`ledgerCore`) and one numeric doubling
(`hdbl`), and cancelling a common additive block plus the positive factor.  Every bridging identity is
SUBTRACTION-FREE; the moment/curvature inputs enter only via `ledgerCore`.  NO nonnegativity, NO
analysis — this is the honest curvature identity. -/
theorem xmsd_iff_d2var_core
    (As A1 A2 Xs X1 X2 Ds D1 D2 cs c1 c2 two : Q')
    (htwo0 : (0 : Q') ≤ two) (htwo_pos : (0 : Q') < two)
    (hM0 : (two * (two * Xs) + Ds).eqv (cs * As))
    (hM1 : (two * (two * X1) + D1).eqv (c1 * A1))
    (hM2 : (two * (two * X2) + D2).eqv (c2 * A2))
    (hcas : (cs + c2).eqv (two * c1 + two))
    (hdbl : (two * (two * (As * (A1 * A2)))).eqv
              (two * (As * (A1 * A2)) + two * (As * (A1 * A2)))) :
    ( Xs * (A1 * A2) + X2 * (As * A1)
        ≤ As * (A1 * A2) + two * (X1 * (As * A2)) )
    ↔
    ( two * (D1 * (As * A2))
        ≤ Ds * (A1 * A2) + D2 * (As * A1) + two * (As * (A1 * A2)) ) := by
  -- LEFT-side collapse: `two·(two·LEFTlhs) + COMMON ≃ RIGHTlhs + SHARED`  (uses `ledgerCore`)
  have eqvL :
      (two * (two * (Xs * (A1 * A2) + X2 * (As * A1)))
          + (Ds * (A1 * A2) + D2 * (As * A1))).eqv
        (two * (D1 * (As * A2))
          + (two * (two * (two * (X1 * (As * A2)))) + two * (As * (A1 * A2)))) := by
    have a1 :
        (two * (two * (Xs * (A1 * A2) + X2 * (As * A1)))
            + (Ds * (A1 * A2) + D2 * (As * A1))).eqv
          ((two * (two * Xs) + Ds) * (A1 * A2) + (two * (two * X2) + D2) * (As * A1)) := by
      ring_qeqv
    have a3 :
        (two * ((two * (two * X1) + D1) * (As * A2)) + two * (As * (A1 * A2))).eqv
          (two * (D1 * (As * A2))
            + (two * (two * (two * (X1 * (As * A2)))) + two * (As * (A1 * A2)))) := by
      ring_qeqv
    exact Q'.eqv_trans _ _ _ a1
      (Q'.eqv_trans _ _ _ (ledgerCore As A1 A2 Xs X1 X2 Ds D1 D2 cs c1 c2 two hM0 hM1 hM2 hcas) a3)
  -- RIGHT-side collapse: `two·(two·LEFTrhs) + COMMON ≃ RIGHTrhs + SHARED`  (uses `hdbl` only)
  have eqvR :
      (two * (two * (As * (A1 * A2) + two * (X1 * (As * A2))))
          + (Ds * (A1 * A2) + D2 * (As * A1))).eqv
        ((Ds * (A1 * A2) + D2 * (As * A1) + two * (As * (A1 * A2)))
          + (two * (two * (two * (X1 * (As * A2)))) + two * (As * (A1 * A2)))) := by
    have b1 :
        (two * (two * (As * (A1 * A2) + two * (X1 * (As * A2))))
            + (Ds * (A1 * A2) + D2 * (As * A1))).eqv
          (two * (two * (As * (A1 * A2)))
            + (two * (two * (two * (X1 * (As * A2)))) + Ds * (A1 * A2) + D2 * (As * A1))) := by
      ring_qeqv
    have b2 :
        (two * (two * (As * (A1 * A2)))
            + (two * (two * (two * (X1 * (As * A2)))) + Ds * (A1 * A2) + D2 * (As * A1))).eqv
          ((two * (As * (A1 * A2)) + two * (As * (A1 * A2)))
            + (two * (two * (two * (X1 * (As * A2)))) + Ds * (A1 * A2) + D2 * (As * A1))) :=
      Q'.add_eqv_congr_right _ _ _ hdbl
    have b3 :
        ((two * (As * (A1 * A2)) + two * (As * (A1 * A2)))
            + (two * (two * (two * (X1 * (As * A2)))) + Ds * (A1 * A2) + D2 * (As * A1))).eqv
          ((Ds * (A1 * A2) + D2 * (As * A1) + two * (As * (A1 * A2)))
            + (two * (two * (two * (X1 * (As * A2)))) + two * (As * (A1 * A2)))) := by
      ring_qeqv
    exact Q'.eqv_trans _ _ _ b1 (Q'.eqv_trans _ _ _ b2 b3)
  constructor
  · intro h
    have h2a : two * (Xs * (A1 * A2) + X2 * (As * A1))
        ≤ two * (As * (A1 * A2) + two * (X1 * (As * A2))) :=
      Q'.mul_le_mul_of_nonneg_left _ _ two h htwo0
    have h2 : two * (two * (Xs * (A1 * A2) + X2 * (As * A1)))
        ≤ two * (two * (As * (A1 * A2) + two * (X1 * (As * A2)))) :=
      Q'.mul_le_mul_of_nonneg_left _ _ two h2a htwo0
    have h3 := Q'.add_le_add_right _ _ (Ds * (A1 * A2) + D2 * (As * A1)) h2
    have h4 := le_of_eqvR (le_of_eqvL (Q'.eqv_symm eqvL) h3) eqvR
    exact le_of_add_le_add_right h4
  · intro h
    have h4 := Q'.add_le_add_right _ _
      (two * (two * (two * (X1 * (As * A2)))) + two * (As * (A1 * A2))) h
    have h3 := le_of_eqvR (le_of_eqvL eqvL h4) (Q'.eqv_symm eqvR)
    have h2 := le_of_add_le_add_right h3
    have h2a := Q'.le_of_mul_le_mul_left h2 htwo_pos
    exact Q'.le_of_mul_le_mul_left h2a htwo_pos

/-- **`xmsd_iff_d2var` — THE EXACT RECAST (over the genuine objects).**  The cleared shift second-
difference inequality of `XMeanSecondDiffLeOne` (in the cross-product moment `xmomN`) is EXACTLY the
position-variance curvature floor `Δ²⟨D²⟩ ≥ −2` (in `dmomN`).  A ring-level `↔`, both directions, over
the genuine `acN`/`xmomN`/`dmomN`; no nonnegativity, no analysis. -/
theorem xmsd_iff_d2var (w : Q') (s : Nat) :
    ( xmomN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))
        + xmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1))
      ≤ acN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))
        + Q'.ofNat 2 * (xmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2))) )
    ↔
    ( Q'.ofNat 2 * (dmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2)))
      ≤ dmomN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))
        + dmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1))
        + Q'.ofNat 2 * (acN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))) ) :=
  xmsd_iff_d2var_core
    (acN w (s + 1) s) (acN w (s + 1) (s + 1)) (acN w (s + 1) (s + 2))
    (xmomN w (s + 1) s) (xmomN w (s + 1) (s + 1)) (xmomN w (s + 1) (s + 2))
    (dmomN w (s + 1) s) (dmomN w (s + 1) (s + 1)) (dmomN w (s + 1) (s + 2))
    (Q'.ofNat (s * s)) (Q'.ofNat ((s + 1) * (s + 1))) (Q'.ofNat ((s + 2) * (s + 2)))
    (Q'.ofNat 2)
    (by decide) (by decide)
    (momentTwoTwo w s s (Nat.le_refl s))
    (momentTwoTwo w s (s + 1) (by omega))
    (momentTwoTwo w s (s + 2) (by omega))
    (sqEqv s)
    (two_mul_eqv (Q'.ofNat 2 * (acN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2)))))

/-! ## 3. The position-variance curvature floor (named open Type-level residual). -/

/-- **`TwoPointTieSubleading w`** — the position-variance curvature floor `Δ²_t ⟨D²⟩_t ≥ −2`, cleared
over `acN_s·acN_{s+1}·acN_{s+2}` in subtraction-free form:

    2·⟨D²⟩_{s+1}  ≤  ⟨D²⟩_s + ⟨D²⟩_{s+2} + 2      (all cleared over the mass product),

with `⟨D²⟩_t = dmomN_t/acN_t` the tilted mean of the antidiagonal square `D²_p = (t−2p)²`.  Via the
exact `ledgerCore` (`Δ²(4⟨x⟩+⟨D²⟩) = 2`) this is EXACTLY equivalent to
`MeanExpConvexProgress.XMeanSecondDiffLeOne w` (`d2x ≤ 1`); it is the honest relocation of the sole
open shift second-difference onto the single cleanest position-variance curvature datum, with the
cross-product statistic `⟨p(t−p)⟩` eliminated.  Corner-tight (`Δ²⟨D²⟩ → −2` at the even-`s`, `w → 0`
two-point tie), hence the exact sub-leading two-point-tie local-CLT constant, NOT a nonnegativity.
NAMED-OPEN (never `sorry`). -/
structure TwoPointTieSubleading (w : Q') : Type where
  d2var : ∀ s,
    Q'.ofNat 2 * (dmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2)))
      ≤ dmomN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))
        + dmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1))
        + Q'.ofNat 2 * (acN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2)))

/-! ## 4. THE REDUCTION and the composite. -/

/-- **`xmsd_of_twoPointTie` — THE REDUCTION.**  A `TwoPointTieSubleading w` witness inhabits
`MeanExpConvexProgress.XMeanSecondDiffLeOne w`: apply `xmsd_iff_d2var` backward per window.  This is
the honest relocation of the open shift second-difference `d2x ≤ 1` onto the position-variance
curvature floor `Δ²⟨D²⟩ ≥ −2`. -/
def xmsd_of_twoPointTie {w : Q'} (T : TwoPointTieSubleading w) : XMeanSecondDiffLeOne w where
  xmsd := fun s => (xmsd_iff_d2var w s).mpr (T.d2var s)

/-- **`meanExpConvex_of_twoPointTie` — the composite reduction.**  A `TwoPointTieSubleading w` witness
inhabits `FusionMarginMonotone.MeanExpConvex w`, chaining `xmsd_of_twoPointTie` through the existing
`meanExpConvex_of_xmsd`. -/
def meanExpConvex_of_twoPointTie {w : Q'} (T : TwoPointTieSubleading w) : MeanExpConvex w :=
  meanExpConvex_of_xmsd (xmsd_of_twoPointTie T)

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `ledgerCore` — the abstract EXACT ledger `Δ²(4⟨x⟩+⟨D²⟩) = 2` (cleared, subtraction-free).
  * `xmsd_iff_d2var_core`, `xmsd_iff_d2var` — THE EXACT RECAST `XMeanSecondDiffLeOne ⟺ (Δ²⟨D²⟩ ≥ −2)`.
  * `xmsd_of_twoPointTie` — THE REDUCTION `TwoPointTieSubleading w ⟹ XMeanSecondDiffLeOne w`.
  * `meanExpConvex_of_twoPointTie` — the composite `… ⟹ MeanExpConvex w`.

NAMED OPEN (Type-level structure, never `sorry`):
  * `TwoPointTieSubleading w` — the position-variance curvature floor `Δ²⟨D²⟩ ≥ −2`; corner-tight, the
    exact sub-leading two-point-tie local-CLT constant, NOT a nonnegativity.

HONEST VERDICT.  An EXACT ledger + exact curvature recast + genuine reduction, NOT a closure.  The
`+2` constant-curvature term is spent EXACTLY (`ledgerCore`), so `d2x ≤ 1` is losslessly relocated onto
the single cleanest position-variance curvature floor `Δ²⟨D²⟩ ≥ −2`, eliminating the cross-product
statistic.  The floor is corner-tight (`→ −2` at the even-`s`, `w → 0` two-point tie), so the exact
sub-leading local-CLT constant is relocated, not signed.  The Clay Yang–Mills mass gap remains OPEN. -/

end YMGap.Continuum.MeanComplementClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MeanComplementClose.ledgerCore
#print axioms YMGap.Continuum.MeanComplementClose.xmsd_iff_d2var_core
#print axioms YMGap.Continuum.MeanComplementClose.xmsd_iff_d2var
#print axioms YMGap.Continuum.MeanComplementClose.xmsd_of_twoPointTie
#print axioms YMGap.Continuum.MeanComplementClose.meanExpConvex_of_twoPointTie
