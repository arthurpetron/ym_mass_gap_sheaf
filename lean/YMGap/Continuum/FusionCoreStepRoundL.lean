/-
Track A / R2 — Round L of the fusion box log-concavity node: the RESERVE QUADRATIC-FORM
MATRIX `reserveM`, and the DECISIVE machine-checked REFUTATION of the Gershgorin /
diagonal-dominance / matrix-PSD closure routes for the sole open residual `SymMinorGershgorin`
(equivalently `AutoconvReserveResidual`).

# What this module adds (read first — load-bearing honesty)

Rounds A–K reduced the whole fusion-box log-concavity node (`FusionConvLogConcaveCore` ⟹
log-concavity ⟹ peak ⟹ `s=1`-dominance) to ONE open residual: the aggregate cross-strand
cancellation of the central-autoconvolution reserve, packaged as
`AutoconvGershgorin.SymMinorGershgorin w`:

    2·δ·(acN(s+1,s)·acN(s+1,s+2))  ≤  Σ_{i,j<s+1} c_i c_j · symMinor(s−i, s−j),   δ = 31/225,

which (via the proved Andréief half-sum identity `acN_defect_double_eq`) is EQUIVALENT to the
truncated-block reserve

    (1 + 31/225)·acN(s+1,s)·acN(s+1,s+2)  ≤  acN(s+1,s+1)².          (†)

`coeffW_strandReserve` (Round K) proved the DIAGONAL / single-strand half of (†) holds with a
uniform ≈3.5× margin (`(256/225)·(1/4) = 64/225 ≤ 1`).  The coordinator's hypothesis was that
PSD — hence (†) — would then follow by GERSHGORIN / diagonal-dominance, IF the cross-strand
off-diagonal row-sum is below the (cushioned) diagonal.

**This module settles that hypothesis: it is FALSE.**  The reserve is the quadratic form of an
explicit symmetric matrix `reserveM(w,s,·,·)` in the monomial weights `c_p`; that matrix is
NOT diagonally dominant and — decisively — NOT even positive-semidefinite (a `2×2` principal
minor is strictly negative at the physical strong-coupling weight `w = 1/2`).  So NO
Gershgorin / diagonal-dominance / matrix-PSD argument can close (†); the residual is a
genuinely SIGNED, weight-specific cancellation (the heat-kernel local-CLT), not a generic
linear-algebra fact.  Round L pins this precisely and records the confirming/refuting concrete
witnesses.

ROUND-L DELIVERABLES (all PROVED, axiom-clean).
  * `reserveM` — the reserve quadratic-form matrix entry
        reserveM(w,s,p,q) = c_{s+1−p}·c_{s+1−q}
                            − (128/225)·(c_{s−p}·c_{s+2−q} + c_{s−q}·c_{s+2−p}),
    whose `c`-weighted full sum `Σ_{p,q≤s} c_p c_q · reserveM(w,s,p,q)` equals the reserve
    slack `acN(s+1,s+1)² − (256/225)·acN(s+1,s)·acN(s+1,s+2)` (numerically/exactly verified;
    `twoReserveM_link` certifies the pointwise algebraic identity `2·reserveM = symMinor −
    δ·cross`).
  * `twoReserveM_link` — the pointwise identity `2·reserveM(s,p,q) ≃ symMinor(s−p,s−q) −
    δ·(c_{s−p}c_{s+2−q}+c_{s−q}c_{s+2−p})` (for `p,q ≤ s`): reserveM IS the matrix of the
    residual's `S − 2δA` quadratic form.
  * `reserveM_offDiag_neg` — the off-diagonal entry `reserveM(1/2,2,0,2) < 0` (indefinite).
  * `reserve_matrix_2x2_minor_neg` — **THE REFUTATION**: the `{0,2}` principal minor
    `reserveM₀₀·reserveM₂₂ − reserveM₀₂² < 0` at `w = 1/2` (exact value
    `−1518001/869730877440000`).  By Sylvester's criterion `reserveM(1/2,2,·,·)` is NOT PSD;
    a fortiori NOT diagonally dominant.  Gershgorin / PSD closure is IMPOSSIBLE.
  * `reserve_holds_at_half_0..3` — (†) HOLDS at the physical strong-coupling point `w = 1/2`
    for `s = 0,1,2,3` (`B/A ≈ 2.0`, a ≈1.76× margin over the needed `256/225 ≈ 1.138`) — so
    the residual is TRUE where it is needed; the wall is only the general-`s`/uniform proof.
  * `reserve_fails_near_one` — (†) FAILS at `w = 63/64`, `s = 4` (`B/A ≈ 1.123 < 1.138`).  So
    the reserve constant `256/225` is a genuinely STRONG-COUPLING fact: it degrades to `→ 1`
    as `w → 1` and is FALSE near weak coupling.  Any proof of (†) MUST consume `w ≤ 1/2`
    (matching `coeffW_superLogConcave`'s hypothesis); a `w`-uniform statement is unprovable.

# HONESTY — what is NOT closed

`SymMinorGershgorin w` / `AutoconvReserveResidual w` remain NAMED-OPEN; this module does NOT
inhabit them and CLOSES NOTHING downstream.  It REFUTES the Gershgorin/PSD closure route
(negative principal minor), CONFIRMS the residual at the physical point, and PINS its
essential strong-coupling character (failure near `w = 1`).  The genuine open content is the
weight-specific signed cancellation `Σ_{p,q} c_p c_q reserveM(w,s,p,q) ≥ 0` for all `s` at
`w ≤ 1/2` — a heat-kernel local-CLT inequality, not a matrix-positivity fact.  This is a
structural localization of one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills
mass gap, and inhabits NO guarded Clay-frontier bundle.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW` / `symMinor` / `acN` definitions, small
`Q'`-algebra congruences, and `decide` only on closed concrete-rational facts.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is `propext` /
`Quot.sound` only (the `decide` facts depend on NO axioms).  No `Classical.*`, no
`native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.AutoconvGershgorin

namespace YMGap.Continuum.FusionCoreStepRoundL

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundJ
open YMGap.Continuum.AutoconvGershgorin

/-! ## 0. The pinned reserve constants -/

/-- The full reserve constant `256/225 = 1 + 31/225`. -/
abbrev reserveC : Q' := Q'.mkPos 256 225 (by decide)
/-- Half the reserve constant `128/225 = (1 + 31/225)/2`, the off-diagonal weight in the
reserve quadratic form. -/
abbrev halfReserveC : Q' := Q'.mkPos 128 225 (by decide)
/-- The reserve gap `δ = 31/225` (`= reserveC − 1`). -/
abbrev deltaC : Q' := Q'.mkPos 31 225 (by decide)

/-! ## 1. The reserve quadratic-form matrix -/

/-- **`reserveM`** — the `(p,q)` entry of the reserve quadratic form.  Its `c`-weighted full
sum over `p,q ≤ s` equals the reserve slack `acN(s+1,s+1)² − (256/225)·acN(s+1,s)·acN(s+1,s+2)`
(the residual's `½·(S − 2δA)`).  Symmetric in `p,q`; the diagonal carries the proved
`coeffW_diagReserve`; the off-diagonal is indefinite (`reserveM_offDiag_neg`). -/
def reserveM (w : Q') (s p q : Nat) : Q' :=
  coeffW w (s + 1 - p) * coeffW w (s + 1 - q)
    + -(halfReserveC * (coeffW w (s - p) * coeffW w (s + 2 - q)
        + coeffW w (s - q) * coeffW w (s + 2 - p)))

/-- **`reserveM_symm`** — the reserve matrix is symmetric: `reserveM(s,p,q) ≃ reserveM(s,q,p)`.
`mul_comm` on the leading product and `add_comm` on the two off-diagonal legs. -/
theorem reserveM_symm (w : Q') (s p q : Nat) :
    (reserveM w s p q).eqv (reserveM w s q p) := by
  unfold reserveM
  refine Q'.add_eqv_congr' (Q'.mul_comm_eqv _ _) (Q'.neg_eqv_congr _ _
    (Q'.mul_eqv_congr_left halfReserveC _ _ (Q'.add_comm_eqv _ _)))

/-- **`two_minor_identity`** — the pure `Q'` core of `twoReserveM_link` (no `set`; LEAN-CORE):
`2·(X − (128/225)·Y) ≃ ((2X − Y) − (31/225)·Y)`, since `256/225 = 2·(128/225) = 1 + 31/225`. -/
theorem two_minor_identity (X Y : Q') :
    ((X + -(halfReserveC * Y)) + (X + -(halfReserveC * Y))).eqv
      (((X + X) + -Y) + -(deltaC * Y)) := by
  -- Step A: (X+N)+(X+N) ≃ (X+X)+(N+N)   (commute each pair, then `add4_rearrange` reversed).
  have hA : ((X + -(halfReserveC * Y)) + (X + -(halfReserveC * Y))).eqv
      ((X + X) + (-(halfReserveC * Y) + -(halfReserveC * Y))) :=
    Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' (Q'.add_comm_eqv X (-(halfReserveC * Y)))
        (Q'.add_comm_eqv X (-(halfReserveC * Y))))
      (Q'.eqv_symm (add4_rearrange (-(halfReserveC * Y)) (-(halfReserveC * Y)) X))
  -- Step B: (128/225·Y)+(128/225·Y) ≃ (256/225)·Y ≃ (1+31/225)·Y ≃ Y + (31/225)·Y.
  have hcoef : ((halfReserveC * Y) + (halfReserveC * Y)).eqv (Y + deltaC * Y) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv halfReserveC halfReserveC Y)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (halfReserveC + halfReserveC) ((1 : Q') + deltaC) Y (by decide)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (1 : Q') deltaC Y) ?_
    exact Q'.add_eqv_congr_right ((1 : Q') * Y) Y (deltaC * Y) (Q'.one_mul_eqv Y)
  -- N + N ≃ −Y + −(31/225·Y).
  have hNN : (-(halfReserveC * Y) + -(halfReserveC * Y)).eqv (-Y + -(deltaC * Y)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.neg_add_eqv (halfReserveC * Y) (halfReserveC * Y))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hcoef) ?_
    exact Q'.neg_add_eqv Y (deltaC * Y)
  -- assemble.
  refine Q'.eqv_trans _ _ _ hA ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (X + X) _ _ hNN) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv (X + X) (-Y) (-(deltaC * Y)))

/-- **`twoReserveM_link` — reserveM IS the matrix of the residual's `S − 2δA` form.**  For
`p,q ≤ s`, `2·reserveM(s,p,q) ≃ symMinor(s−p,s−q) − δ·(c_{s−p}c_{s+2−q}+c_{s−q}c_{s+2−p})`.
Confirms `Σ_{p,q} c_p c_q · 2reserveM = S − 2δA`, i.e. reserveM is the reserve quadratic form. -/
theorem twoReserveM_link {w : Q'} {s p q : Nat} (hp : p ≤ s) (hq : q ≤ s) :
    (reserveM w s p q + reserveM w s p q).eqv
      (symMinor w (s - p) (s - q)
        + -(deltaC * (coeffW w (s - p) * coeffW w (s + 2 - q)
            + coeffW w (s - q) * coeffW w (s + 2 - p)))) := by
  unfold reserveM symMinor
  rw [show s + 1 - p = (s - p) + 1 by omega, show s + 1 - q = (s - q) + 1 by omega,
      show s + 2 - q = (s - q) + 2 by omega, show s + 2 - p = (s - p) + 2 by omega]
  exact two_minor_identity (coeffW w ((s - p) + 1) * coeffW w ((s - q) + 1))
    (coeffW w (s - p) * coeffW w ((s - q) + 2) + coeffW w (s - q) * coeffW w ((s - p) + 2))

/-! ## 2. THE REFUTATION — the reserve matrix is not PSD / not diagonally dominant -/

/-- **`reserveM_offDiag_neg`** — the off-diagonal entry `reserveM(1/2, 2, 0, 2)` is strictly
negative (`= −1409/29491200`).  The reserve quadratic form has genuinely negative
off-diagonal couplings: the cross-strand contribution is signed, not manifestly nonnegative.
Machine-checked (no axioms). -/
theorem reserveM_offDiag_neg : reserveM wH 2 0 2 < 0 := by decide

/-- **`reserve_matrix_2x2_minor_neg` — THE GERSHGORIN/PSD REFUTATION.**  The `{0,2}` principal
`2×2` minor of `reserveM(1/2, 2, ·, ·)` is strictly negative,

    reserveM₀₀·reserveM₂₂ + −(reserveM₀₂·reserveM₀₂)  =  −1518001/869730877440000  <  0.

By Sylvester's criterion the symmetric matrix `reserveM(1/2, 2, ·, ·)` is NOT
positive-semidefinite; a fortiori it is NOT diagonally dominant (diagonal dominance with
nonnegative diagonal would force PSD).  Therefore NO Gershgorin / diagonal-dominance /
matrix-PSD argument can establish the reserve `Σ_{p,q} c_p c_q reserveM ≥ 0` — despite the
proved ≈3.5× DIAGONAL cushion (`coeffW_strandReserve`).  The residual is a genuinely SIGNED,
`c`-weight-specific cancellation (the heat-kernel local-CLT), not a generic positivity fact.
Machine-checked (no axioms). -/
theorem reserve_matrix_2x2_minor_neg :
    ¬ ((0 : Q') ≤ reserveM wH 2 0 0 * reserveM wH 2 2 2
        + -(reserveM wH 2 0 2 * reserveM wH 2 0 2)) := by decide

/-- **`reserveM_diag_pos`** — the diagonal entries are strictly positive (the proved reserve
cushion): `reserveM(1/2,2,0,0) > 0` and `reserveM(1/2,2,2,2) > 0`.  So the negative minor is
NOT a broken diagonal — it is genuine off-diagonal dominance of the indefinite coupling.
Machine-checked. -/
theorem reserveM_diag_pos :
    (0 : Q') < reserveM wH 2 0 0 ∧ (0 : Q') < reserveM wH 2 2 2 := by
  refine ⟨by decide, by decide⟩

/-! ## 3. The residual HOLDS at the physical strong-coupling point `w = 1/2` -/

/-- The truncated-block reserve (†) at `w = 1/2` for mode `s`:
`(256/225)·acN(s+1,s)·acN(s+1,s+2) ≤ acN(s+1,s+1)²`. -/
abbrev reserveHoldsAt (s : Nat) : Prop :=
  reserveC * (acN wH (s + 1) s * acN wH (s + 1) (s + 2))
    ≤ acN wH (s + 1) (s + 1) * acN wH (s + 1) (s + 1)

/-- **`reserve_holds_at_half_0`** — (†) at `w = 1/2`, `s = 0` (`B/A = 16/3`). -/
theorem reserve_holds_at_half_0 : reserveHoldsAt 0 := by decide
/-- **`reserve_holds_at_half_1`** — (†) at `w = 1/2`, `s = 1` (`B/A = 361/100`). -/
theorem reserve_holds_at_half_1 : reserveHoldsAt 1 := by decide
/-- **`reserve_holds_at_half_2`** — (†) at `w = 1/2`, `s = 2` (`B/A ≈ 2.476`). -/
theorem reserve_holds_at_half_2 : reserveHoldsAt 2 := by decide
/-- **`reserve_holds_at_half_3`** — (†) at `w = 1/2`, `s = 3` (`B/A ≈ 2.203`). -/
theorem reserve_holds_at_half_3 : reserveHoldsAt 3 := by decide

/-! ## 4. The reserve is STRONG-COUPLING — it FAILS near `w = 1` -/

/-- **`reserve_fails_near_one` — the reserve constant `256/225` is a strong-coupling fact.**
At the WEAK-coupling weight `w = 63/64` and mode `s = 4`, the truncated-block reserve (†)
FAILS:

    (256/225)·acN(5,4)·acN(5,6)  >  acN(5,5)²          (`B/A ≈ 1.123 < 256/225 ≈ 1.138`).

Hence there is NO `w`-uniform proof of the residual: the reserve degrades to `→ 1` as
`w → 1` and is false near weak coupling, so any proof MUST consume the strong-coupling
hypothesis `w ≤ 1/2` (matching `coeffW_superLogConcave`).  Machine-checked (no axioms). -/
theorem reserve_fails_near_one :
    ¬ (reserveC * (acN (Q'.mkPos 63 64 (by decide)) 5 4
          * acN (Q'.mkPos 63 64 (by decide)) 5 6)
        ≤ acN (Q'.mkPos 63 64 (by decide)) 5 5
          * acN (Q'.mkPos 63 64 (by decide)) 5 5) := by decide

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`; the `decide` facts depend on NO
axioms):
  * `reserveM`, `reserveM_symm`, `twoReserveM_link` — the reserve quadratic-form matrix and
    its pointwise identification with the residual's `S − 2δA` form.
  * `reserveM_offDiag_neg`, `reserveM_diag_pos`, `reserve_matrix_2x2_minor_neg` — the
    Gershgorin/PSD REFUTATION: positive diagonal but a strictly negative `2×2` principal
    minor at `w = 1/2`, so `reserveM(1/2,2,·,·)` is not PSD and not diagonally dominant.
  * `reserve_holds_at_half_0..3` — (†) holds at the physical point `w = 1/2` (`s = 0..3`).
  * `reserve_fails_near_one` — (†) fails at `w = 63/64`, `s = 4`: the reserve is strong-coupling.

NAMED OPEN (carried from Rounds I/J/K, NOT inhabited here):
  * `AutoconvGershgorin.SymMinorGershgorin w` / `FusionCoreStepRoundI.AutoconvReserveResidual w`
    — the aggregate signed reserve `Σ_{p,q≤s} c_p c_q reserveM(w,s,p,q) ≥ 0` for all `s` at
    `w ≤ 1/2`.  Round L proves this is NOT closable by Gershgorin/PSD (negative principal
    minor), holds at the physical point, and requires strong coupling — a weight-specific
    heat-kernel local-CLT inequality.

HONEST VERDICT.  The coordinator's Gershgorin/diagonal-dominance closure hypothesis is
REFUTED: the reserve quadratic-form matrix is not positive-semidefinite (negative principal
minor at `w = 1/2`), so the ≈3.5× diagonal cushion cannot dominate the signed cross-strand
coupling by any absolute-value/Gershgorin bound.  The residual is TRUE at strong coupling
(verified at `w = 1/2`) and FALSE near `w = 1` — a genuine, `c`-weight-specific signed
cancellation (local-CLT), not a matrix-positivity fact.  This module CLOSES NOTHING
downstream and inhabits NO guarded Clay-frontier bundle; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundL

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundL.reserveM_symm
#print axioms YMGap.Continuum.FusionCoreStepRoundL.two_minor_identity
#print axioms YMGap.Continuum.FusionCoreStepRoundL.twoReserveM_link
#print axioms YMGap.Continuum.FusionCoreStepRoundL.reserveM_offDiag_neg
#print axioms YMGap.Continuum.FusionCoreStepRoundL.reserve_matrix_2x2_minor_neg
#print axioms YMGap.Continuum.FusionCoreStepRoundL.reserveM_diag_pos
#print axioms YMGap.Continuum.FusionCoreStepRoundL.reserve_holds_at_half_0
#print axioms YMGap.Continuum.FusionCoreStepRoundL.reserve_holds_at_half_1
#print axioms YMGap.Continuum.FusionCoreStepRoundL.reserve_holds_at_half_2
#print axioms YMGap.Continuum.FusionCoreStepRoundL.reserve_holds_at_half_3
#print axioms YMGap.Continuum.FusionCoreStepRoundL.reserve_fails_near_one
