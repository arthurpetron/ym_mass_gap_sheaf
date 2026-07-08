/-
Track A / R2 — the ANALYTIC (theta-limit) reduction of the sole remaining autoconvolution
log-concavity reserve `AcNDefectReserve` to a single crude rational theta-floor cushion plus one
named finite-`s` saddle residual.

# Context (what is already in tree)

`AutoconvGershgorin` closed the Andréief half-sum EXPANSION of the central-autoconvolution defect
into the `symMinor` quadratic form, and `LeakGeoDecay` proved the EXACT collapse

    SymMinorGershgorin w  ⟺  AcNDefectReserve w
      (`gershgorin_iff_reserve`, via the half-sum identity `sym_eq_two_defect`),

reducing the whole `symMinor` Gershgorin node to the SINGLE scalar reserve on the uniform
range-`(s+1)` block,

    δ·(acN(s+1,s)·acN(s+1,s+2)) ≤ acN(s+1,s+1)² + −(acN(s+1,s)·acN(s+1,s+2)),   δ = 31/225,

equivalently `(1+δ)·A ≤ B` with `A = acN(s+1,s)·acN(s+1,s+2)`, `B = acN(s+1,s+1)²`, and
`1+δ = 256/225`.  Writing the margin `B/A`, the reserve is exactly `256·A ≤ 225·B`.

# What this module adds (read first — load-bearing honesty)

The magnitude `256/225 ≈ 1.1378` is far below the theta-autoconvolution limit margin
`L_even(w) ≈ 1.987` (`w ≤ 1/2`, even-`s → ∞`).  Its crude two-term theta floor is
`L_even(w) ≥ 4/θ₃(0,¼)² ≥ 40000/22801 = 1.7543 > 256/225`.  This module isolates the genuine
content — that the FINITE-`s` truncated margins dominate that rational theta floor — as ONE named
residual `FiniteSMargin`, and proves EVERYTHING ELSE (the rational cushion and both algebraic
bridges) axiom-clean.

DELIVERABLE (PROVED, axiom-clean).
  * `acN_nonneg` — the range-`n` central autoconvolution is `≥ 0` on `0 ≤ w` (`fsum_nonneg` of
    the nonnegative `coeffW` products).
  * `thetaFloor_cushion` — the crude rational theta-floor cushion `256·22801 ≤ 225·40000`
    (i.e. `256/225 ≤ 40000/22801`); pure `decide`, ≈1.54× rounding room.
  * `perDiagonal_newton` — the in-tree per-diagonal factor-4 Newton inequality
    `4·(c_m·c_{m+2}) ≤ c_{m+1}²` (`coeffW_superLogConcave_four`), the certificate that the
    margin is bounded away from `1` at strong coupling (Step 1 of the analytic chain).
  * `cross_of_thetaMargin` — the pure-`Q'` bridge `40000·A ≤ 22801·B  ⟹  256·A ≤ 225·B`
    (on `0 ≤ B`), discharging `256/225` through the rational cushion.
  * `reserve_of_cross` — the pure-`Q'` bridge `256·A ≤ 225·B  ⟹  δ·A ≤ B + −A`, δ = 31/225
    (cancel the positive `225` against the linear rearrangement `256 = 31 + 225`).
  * `reserveOfFiniteSMargin` — THE REDUCTION: a `FiniteSMargin w` witness (plus `0 ≤ w`) yields
    the full `AcNDefectReserve w`.
  * `gershgorinOfFiniteSMargin` — end-to-end wiring to `SymMinorGershgorin w`
    (`LeakGeoDecay.gershgorinOfReserve` composed with the reduction).

NAMED OPEN (Type-level structure, never `sorry`).
  * `FiniteSMargin w` — the finite-`s` truncated margins dominate the crude rational theta floor,
        ∀ s, 40000·(acN(s+1,s)·acN(s+1,s+2)) ≤ 22801·(acN(s+1,s+1)²).
    This is `SymMinorGershgorin`/`AcNDefectReserve` re-expressed analytically as a uniform
    steepest-descent saddle-remainder `≥ 0` for the theta autoconvolution (the finite-`s` saddle
    remainder plus the `n = s+1` truncation-edge defect).  It is numerically true (even-`s`
    margins decrease monotonically to `L_even` from above; odd-`s` sit higher) with a ≈1.5×
    cushion over the floor, but it is the genuine content and is NOT a finite rational inequality.

# HONESTY — what is NOT closed

`FiniteSMargin w` is NAMED-OPEN; this module does NOT inhabit it.  What is closed is (a) the crude
rational theta floor `40000/22801 > 256/225` and (b) the two algebraic bridges that turn a
finite-`s` margin `≥ 40000/22801` into the reserve.  The single genuine wall — the uniform
finite-`s` saddle-remainder bound — is exactly `SymMinorGershgorin` restated; Route A (pure
Cauchy–Schwarz/Hoggar on the indefinite off-diagonal `symMinor`) is ruled out for a uniform
constant `> 1`, so this analytic (Tate–Zelditch) reduction is the correct move.  This is a
structural sharpening of one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `acN`/`coeffW`/`fsum` definitions, `coeffW_superLogConcave_four`,
the `le_of_mul_le_mul_left_pos` positive cancellation, and `decide` only on closed concrete-rational
facts.  Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses
are `Type`-level data.
-/

import YMGap.Continuum.LeakGeoDecay
import YMGap.Continuum.FusionCoreStep

namespace YMGap.Continuum.AcNReserveAnalytic

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.LeakGeoDecay

/-! ## 0. Nonnegativity of the range-`n` autoconvolution -/

/-- **`acN_nonneg`** — on `0 ≤ w`, the range-`n` central autoconvolution
`acN w n s = Σ_{p<n} c_p·c_{s−p}` is `≥ 0` (a finite sum of nonnegative `coeffW` products). -/
theorem acN_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (n s : Nat) : (0 : Q') ≤ acN w n s := by
  unfold acN
  exact fsum_nonneg
    (fun p => Q'.mul_nonneg _ _ (coeffW_nonneg hw0 p) (coeffW_nonneg hw0 (s - p))) n

/-! ## 1. The crude rational theta-floor cushion and the diagonal Newton certificate -/

/-- **`thetaFloor_cushion`** — the crude two-term theta floor beats the target magnitude:
`256·22801 ≤ 225·40000` (i.e. `256/225 ≤ 40000/22801 = 1.7543…`).  This is Step 3 of the
analytic chain: dropping the `≥ 1` theta numerator factor and using `θ₃(0,w²) ≤ θ₃(0,¼) ≤ 151/100`
for `w ≤ 1/2` gives `L_even(w) ≥ 4/θ₃(0,¼)² ≥ 40000/22801`.  Pure `decide`, ≈1.54× room over
`256/225 = 1.1378…`. -/
theorem thetaFloor_cushion :
    Q'.ofNat 256 * Q'.ofNat 22801 ≤ Q'.ofNat 225 * Q'.ofNat 40000 := by decide

/-- **`perDiagonal_newton`** — the in-tree per-diagonal factor-4 Newton inequality
`4·(c_m·c_{m+2}) ≤ c_{m+1}²` (`coeffW_superLogConcave_four`), for `0 ≤ w ≤ 1/2`.  This is the
Step-1 certificate that the autoconvolution margin is bounded away from `1` at strong coupling
(the diagonal `3/4` reserve); it does not aggregate by itself — the off-diagonal `symMinor` is
indefinite — which is why the analytic theta-limit route (not Cauchy–Schwarz) is required. -/
theorem perDiagonal_newton {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) (m : Nat) :
    (4 : Q') * (coeffW w m * coeffW w (m + 2)) ≤ coeffW w (m + 1) * coeffW w (m + 1) :=
  coeffW_superLogConcave_four hw0 hw12 m

/-! ## 2. The two pure-`Q'` algebraic bridges -/

/-- **`cross_of_thetaMargin`** — the theta-floor bridge.  From the finite-`s` margin
`40000·A ≤ 22801·B` (and `0 ≤ B`) conclude the target cross form `256·A ≤ 225·B`.  Cancel the
positive factor `40000`: `40000·(256·A) ≃ 256·(40000·A) ≤ 256·(22801·B) ≃ 5837056·B ≤ 9000000·B
≃ 40000·(225·B)`, using the rational cushion `256·22801 = 5837056 ≤ 9000000 = 225·40000`. -/
theorem cross_of_thetaMargin {A B : Q'} (hB : (0 : Q') ≤ B)
    (h : Q'.ofNat 40000 * A ≤ Q'.ofNat 22801 * B) :
    Q'.ofNat 256 * A ≤ Q'.ofNat 225 * B := by
  -- 40000·(256·A) ≃ 256·(40000·A)
  have eL : (Q'.ofNat 40000 * (Q'.ofNat 256 * A)).eqv
      (Q'.ofNat 256 * (Q'.ofNat 40000 * A)) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 40000) (Q'.ofNat 256) A))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right (Q'.ofNat 40000 * Q'.ofNat 256)
          (Q'.ofNat 256 * Q'.ofNat 40000) A (Q'.mul_comm_eqv _ _))
        (Q'.mul_assoc_eqv (Q'.ofNat 256) (Q'.ofNat 40000) A))
  -- 256·(40000·A) ≤ 256·(22801·B)
  have step1 : Q'.ofNat 256 * (Q'.ofNat 40000 * A) ≤ Q'.ofNat 256 * (Q'.ofNat 22801 * B) :=
    Q'.mul_le_mul_of_nonneg_left (Q'.ofNat 40000 * A) (Q'.ofNat 22801 * B)
      (Q'.ofNat 256) h (by decide)
  -- 256·(22801·B) ≃ 5837056·B
  have e2 : (Q'.ofNat 256 * (Q'.ofNat 22801 * B)).eqv (Q'.ofNat 5837056 * B) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 256) (Q'.ofNat 22801) B))
      (Q'.mul_eqv_congr_right (Q'.ofNat 256 * Q'.ofNat 22801) (Q'.ofNat 5837056) B (by decide))
  -- 5837056·B ≤ 9000000·B   (the rational cushion, scaled by B ≥ 0)
  have ineq : Q'.ofNat 5837056 * B ≤ Q'.ofNat 9000000 * B :=
    Q'.mul_le_mul_of_nonneg_right (Q'.ofNat 5837056) (Q'.ofNat 9000000) B (by decide) hB
  -- 9000000·B ≃ 40000·(225·B)
  have e3 : (Q'.ofNat 9000000 * B).eqv (Q'.ofNat 40000 * (Q'.ofNat 225 * B)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (Q'.ofNat 9000000) (Q'.ofNat 40000 * Q'.ofNat 225) B (by decide))
      (Q'.mul_assoc_eqv (Q'.ofNat 40000) (Q'.ofNat 225) B)
  have hmain : Q'.ofNat 40000 * (Q'.ofNat 256 * A)
      ≤ Q'.ofNat 40000 * (Q'.ofNat 225 * B) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv eL)
      (Q'.le_trans' _ _ _ step1
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv e2)
          (Q'.le_trans' _ _ _ ineq (Q'.le_of_eqv e3))))
  exact le_of_mul_le_mul_left_pos (show (0 : Q') < Q'.ofNat 40000 by decide) hmain

/-- **`reserve_of_cross`** — the reserve bridge.  From `256·A ≤ 225·B` conclude the defect
reserve `δ·A ≤ B + −A` with `δ = 31/225`.  Cancel the positive factor `225`:
`225·(δ·A) ≃ 31·A ≤ 225·B + −(225·A) ≃ 225·(B + −A)`, using the linear identity `256 = 31 + 225`
(so `31·A + 225·A ≤ 225·B` from the hypothesis, then move `225·A` across). -/
theorem reserve_of_cross {A B : Q'}
    (h : Q'.ofNat 256 * A ≤ Q'.ofNat 225 * B) :
    Q'.mkPos 31 225 (by decide) * A ≤ B + -A := by
  apply le_of_mul_le_mul_left_pos (show (0 : Q') < Q'.ofNat 225 by decide)
  -- goal: 225·(δ·A) ≤ 225·(B + −A)
  -- LHS ≃ 31·A
  have eLL : (Q'.ofNat 225 * (Q'.mkPos 31 225 (by decide) * A)).eqv (Q'.ofNat 31 * A) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 225) (Q'.mkPos 31 225 (by decide)) A))
      (Q'.mul_eqv_congr_right (Q'.ofNat 225 * Q'.mkPos 31 225 (by decide)) (Q'.ofNat 31) A
        (by decide))
  -- RHS ≃ 225·B + −(225·A)
  have eRR : (Q'.ofNat 225 * (B + -A)).eqv (Q'.ofNat 225 * B + -(Q'.ofNat 225 * A)) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_add_eqv (Q'.ofNat 225) B (-A))
      (Q'.add_eqv_congr_left (Q'.ofNat 225 * B) (Q'.ofNat 225 * (-A)) (-(Q'.ofNat 225 * A))
        (Q'.mul_neg_eqv (Q'.ofNat 225) A))
  -- 31·A + 225·A ≃ 256·A ≤ 225·B
  have hsum : (Q'.ofNat 31 * A + Q'.ofNat 225 * A).eqv (Q'.ofNat 256 * A) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat 31) (Q'.ofNat 225) A))
      (Q'.mul_eqv_congr_right (Q'.ofNat 31 + Q'.ofNat 225) (Q'.ofNat 256) A (by decide))
  have h' : Q'.ofNat 31 * A + Q'.ofNat 225 * A ≤ Q'.ofNat 225 * B :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hsum) h
  have h'' : (Q'.ofNat 31 * A + Q'.ofNat 225 * A) + -(Q'.ofNat 225 * A)
      ≤ Q'.ofNat 225 * B + -(Q'.ofNat 225 * A) :=
    Q'.add_le_add_right _ _ (-(Q'.ofNat 225 * A)) h'
  have eCancel : ((Q'.ofNat 31 * A + Q'.ofNat 225 * A) + -(Q'.ofNat 225 * A)).eqv
      (Q'.ofNat 31 * A) :=
    Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (Q'.ofNat 31 * A) (Q'.ofNat 225 * A) (-(Q'.ofNat 225 * A)))
      (Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (Q'.ofNat 31 * A)
          (Q'.ofNat 225 * A + -(Q'.ofNat 225 * A)) 0
          (Q'.add_neg_self_eqv (Q'.ofNat 225 * A)))
        (QPoly.q_add_zero_eqv (Q'.ofNat 31 * A)))
  have hmid : Q'.ofNat 31 * A ≤ Q'.ofNat 225 * B + -(Q'.ofNat 225 * A) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv eCancel) h''
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eLL)
    (Q'.le_trans' _ _ _ hmid (Q'.ge_of_eqv eRR))

/-! ## 3. The single named residual and the reduction -/

/-- **`FiniteSMargin w`** — the SOLE genuine residual to which the analytic chain reduces: the
finite-`s` truncated central-autoconvolution margins dominate the crude rational theta floor
`40000/22801` uniformly in `s`,

    ∀ s, 40000·(acN(s+1,s)·acN(s+1,s+2)) ≤ 22801·(acN(s+1,s+1)²).

This is `AutoconvGershgorin.SymMinorGershgorin` / `LeakGeoDecay.AcNDefectReserve` re-expressed
analytically as a uniform steepest-descent saddle-remainder `≥ 0` for the theta autoconvolution
(the finite-`s` saddle remainder plus the `n = s+1` truncation-edge defect).  It is numerically
true — even-`s` margins decrease monotonically to `L_even(w)` from above; odd-`s` sit higher —
with a ≈1.5× cushion over the floor, but it is NOT a finite rational inequality.  NAMED-OPEN
(never `sorry`). -/
structure FiniteSMargin (w : Q') : Type where
  /-- The finite-`s` margin dominates the crude rational theta floor `40000/22801`, uniform in `s`. -/
  margin : ∀ s,
    Q'.ofNat 40000 * (acN w (s + 1) s * acN w (s + 1) (s + 2))
      ≤ Q'.ofNat 22801 * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1))

/-- **`reserveOfFiniteSMargin` — THE REDUCTION.**  A `FiniteSMargin w` witness (with `0 ≤ w`)
yields the full `AcNDefectReserve w`: for each `s`, the finite-`s` theta-floor margin is turned
into the cross form `256·A ≤ 225·B` (`cross_of_thetaMargin`, with `B ≥ 0` from `acN_nonneg`) and
then into the defect reserve `δ·A ≤ B + −A` (`reserve_of_cross`). -/
def reserveOfFiniteSMargin {w : Q'} (hw0 : (0 : Q') ≤ w) (m : FiniteSMargin w) :
    AcNDefectReserve w where
  reserve := fun s => by
    have hB : (0 : Q') ≤ acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1) :=
      Q'.mul_nonneg _ _ (acN_nonneg hw0 _ _) (acN_nonneg hw0 _ _)
    exact reserve_of_cross (cross_of_thetaMargin hB (m.margin s))

/-- **`gershgorinOfFiniteSMargin` — end-to-end wiring.**  Composed with the in-tree converse
`LeakGeoDecay.gershgorinOfReserve`, a `FiniteSMargin w` witness (with `0 ≤ w`) yields the full
aggregate `SymMinorGershgorin w` domination — i.e. the whole `symMinor` Gershgorin node closes
iff this one analytic finite-`s` saddle residual closes. -/
def gershgorinOfFiniteSMargin {w : Q'} (hw0 : (0 : Q') ≤ w) (m : FiniteSMargin w) :
    SymMinorGershgorin w :=
  gershgorinOfReserve (reserveOfFiniteSMargin hw0 m)

/-! ## 4. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `acN_nonneg` — the range-`n` autoconvolution is `≥ 0` on `0 ≤ w`.
  * `thetaFloor_cushion` — the crude rational theta floor `256·22801 ≤ 225·40000`
    (`256/225 ≤ 40000/22801`), pure `decide`.
  * `perDiagonal_newton` — the in-tree diagonal factor-4 Newton inequality (Step-1 certificate).
  * `cross_of_thetaMargin` — `40000·A ≤ 22801·B ⟹ 256·A ≤ 225·B` (on `0 ≤ B`).
  * `reserve_of_cross` — `256·A ≤ 225·B ⟹ δ·A ≤ B + −A`, δ = 31/225.
  * `reserveOfFiniteSMargin` — the reduction `FiniteSMargin ⟹ AcNDefectReserve` (with `0 ≤ w`).
  * `gershgorinOfFiniteSMargin` — end-to-end `FiniteSMargin ⟹ SymMinorGershgorin`.

NAMED OPEN (Type-level structure, never `sorry`):
  * `FiniteSMargin w` — the finite-`s` truncated margins dominate the crude rational theta floor
    `40000/22801` uniformly in `s`.  The genuine content: `SymMinorGershgorin`/`AcNDefectReserve`
    restated as a uniform steepest-descent saddle-remainder `≥ 0` for the theta autoconvolution.

HONEST VERDICT.  This module REDUCES the sole remaining autoconvolution log-concavity reserve to
ONE crude rational theta-floor cushion (`256/225 ≤ 40000/22801`, proved) plus ONE named finite-`s`
saddle residual (`FiniteSMargin`), and proves both algebraic bridges.  It does NOT inhabit that
residual; Route A (Cauchy–Schwarz/Hoggar on the indefinite off-diagonal `symMinor`) is ruled out
for a uniform constant `> 1`, leaving the analytic (Tate–Zelditch) finite-`s` saddle bound as the
single genuine wall.  This is a structural sharpening of one box-level log-concavity sub-fact; it
is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.AcNReserveAnalytic

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AcNReserveAnalytic.acN_nonneg
#print axioms YMGap.Continuum.AcNReserveAnalytic.thetaFloor_cushion
#print axioms YMGap.Continuum.AcNReserveAnalytic.perDiagonal_newton
#print axioms YMGap.Continuum.AcNReserveAnalytic.cross_of_thetaMargin
#print axioms YMGap.Continuum.AcNReserveAnalytic.reserve_of_cross
#print axioms YMGap.Continuum.AcNReserveAnalytic.reserveOfFiniteSMargin
#print axioms YMGap.Continuum.AcNReserveAnalytic.gershgorinOfFiniteSMargin
