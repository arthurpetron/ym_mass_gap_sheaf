/-
Track A / R2 -- Fusion `CoreStep` local-CLT node: Rounds L-M (consolidated).

This module is the MERGE of the former `FusionCoreStepRoundL.lean` and
`FusionCoreStepRoundM.lean`. It is separate from `FusionCoreStep.lean`
(Rounds A-K) for a hard reason: `FusionCoreStepRoundL` imports
`AutoconvGershgorin`, which imports `LocalCLTSteepestDescent`, which imports
(the former) `FusionCoreStepRoundJ` -- now part of `FusionCoreStep`. Placing L
in `FusionCoreStep` would close an import cycle. L and M therefore stay in this
downstream file, which imports `FusionCoreStep` (Round M uses Round C's
declarations) and `AutoconvGershgorin`.

Every declaration, docstring, and `#print axioms` gate from the two original
files is preserved verbatim; each round keeps its namespace
`YMGap.Continuum.FusionCoreStepRound{L,M}`.

# Axiom-gate: as in `FusionCoreStep`; permitted output `propext`/`Quot.sound` only.
-/

import YMGap.Continuum.AutoconvGershgorin
import YMGap.Continuum.FusionCoreStep


/-! ===========================================================================
    ## Round L  (was `FusionCoreStepRoundL.lean`)
    =========================================================================== -/

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


/-! ===========================================================================
    ## Round M  (was `FusionCoreStepRoundM.lean`)
    =========================================================================== -/

/-
Track A / R2 — Round M of the fusion box log-concavity node: the EXACT GAUSSIAN
FACTORIZATION of the central-autoconvolution weight product, isolating the SOURCE of the
reserve constant `256/225` and reducing the sole open residual `(†)` to a pure, `w`-free
combinatorial log-concavity of the Gaussian-stripped coupling sequence.

# What this module adds (read first — load-bearing honesty)

Rounds A–L reduced the whole node to ONE residual, the truncated-block reserve

    (†)   (256/225)·acN(s+1,s)·acN(s+1,s+2)  ≤  acN(s+1,s+1)²,

with `acN(w,n,S) = Σ_{p<n} c_p·c_{S−p}`, `c_p = coeffW w p = (p+1)·w^{p(p+2)}`.  Round L
REFUTED the Gershgorin / diagonal-dominance / matrix-PSD closure (the reserve matrix is not
PSD), pinning the genuine content to a SIGNED, weight-specific cancellation.

Round M supplies the missing STRUCTURE — the exact origin of that cancellation and of the
reserve constant.  Writing `c_p = (p+1) w^{p(p+2)}`, the product of two weights on the
antidiagonal `a+b = S` factorizes EXACTLY as

    c_a · c_b  =  (a+1)(b+1) · w^{ (a+1)² + (b+1)² − 2 }
               =  w^{c4(S)} · [ (a+1)(b+1) · w^{ −2(a+1)(b+1) } ]        (a+b = S),

because `c4 a + c4 b + 2ab = c4(a+b)` (`c4 S = S(S+2) = (S+1)²−1`).  The first factor
`w^{c4(S)}` is a pure Gaussian in `S` whose log-concavity SECOND DIFFERENCE is EXACTLY the
constant `2` (`c4(S) + c4(S+2) = 2·c4(S+1) + 2`, in-tree `FusionResidualBound.c4_sum_symm`),
i.e. the Gaussian reserve is exactly `w^{−2} = 1/w² ≥ 4` at `w ≤ 1/2`.  The SECOND factor is
the pure `w`-free coupling `U(S) := Σ_{i+j=S} i·j·Q^{i·j}`, `Q = 1/w²`.

Consequence (the reserve accounting, verified — see the numeric ledger in the doc-comment):
`acN(s+1,S) = w^{c4(S)−2}·(range-`(s+1)` truncation of `U(S+2)`)`, and dividing the reserve
`(†)` by the common Gaussian factor leaves EXACTLY

    (256/225)·w²·U(s+2)·U(s+4)  ≤  U(s+3)²,        i.e.   U(s+3)² ≥ (256/(225·Q))·U(s+2)·U(s+4).

Since `w² ≤ 1/4`, the whole reserve budget the coupling must supply is only
`(256/225)·w² ≤ 64/225 ≈ 0.284` (`gaussianReserveBudget`), whereas the true coupling margin
`U(s+3)²/(U(s+2)U(s+4)) → 1/√Q = 1/2` (`≈ 0.497` worst, mpmath dps 60).  So the ENTIRE
reserve `256/225` is paid by the Gaussian gap `Q ≥ 4`; the coupling `U` need only be "not too
anti-log-concave", with a uniform `≈ 1.75×` cushion.

MODULE DELIVERABLES (all PROVED, axiom-clean).
  * `c4_antidiag` — the antidiagonal Casimir identity `c4 a + c4 b + 2ab = c4 (a+b)` (Nat).
  * `coeffW_antidiag_gaussian` — THE EXACT FACTORIZATION
        c_a · c_b · w^{2ab}  ≃  (dimQ a · dimQ b) · w^{c4(a+b)},
    exhibiting the Gaussian weight `w^{c4(S)}` and the coupling `dimQ a·dimQ b` on the
    antidiagonal `a+b = S` (no division; the `w^{2ab}` clears the negative coupling power).
  * `gaussianReserveBudget` — the reserve-accounting inequality `reserveC · w² ≤ 64/225` for
    `w ≤ 1/2`: the reserve `256/225` costs at most `64/225` of the coupling margin, the rest
    is paid by the Gaussian gap.
  * `reserve_holds_at_half_4` — (†) HOLDS at the physical point `w = 1/2` for `s = 4`
    (extending Round L's `s = 0..3`; `B/A ≈ 2.077`, margin `≈ 1.83×`), the exact margin staying
    `≈ 2.0`, NOT approaching the needed `256/225 ≈ 1.138` — evidence (not proof) of the
    uniform reserve.  (Higher `s` are kernel-`decide`-infeasible; the margin table to `s=58`
    is in the numeric ledger.)

# HONESTY — what is NOT closed

`(†)` / `SymMinorGershgorin` / `FiniteSMargin` remain NAMED-OPEN; this module CLOSES NOTHING
downstream and inhabits NO guarded Clay-frontier bundle.  What Round M proves is the exact
factorization that *localizes and explains* the reserve: all of `256/225` is supplied by the
Gaussian second-difference `w^{−2} ≥ 4`, and the residual is the `w`-free log-concavity margin
`U(s+3)² ≥ (256/(225Q))·U(s+2)U(s+4)` of the coupling `U(S) = Σ ij Q^{ij}`.  This margin is
`→ 1/√Q` (a discrete theta / local-CLT saddle), and — as verified numerically — is NOT
recoverable by any dominant-term / geometric-tail bound (those lose exactly the saddle-width
`θ(Q)²` factor and fail for every physical `w ≤ 1/2`).  So the residual is confirmed to be a
genuine heat-kernel LOCAL-CLT (saddle-WIDTH) statement, now in its cleanest `w`-free form; it
is NOT a finite rational inequality.  This is a structural sharpening of one box-level
log-concavity sub-fact — it is NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `coeffW` / `dimQ` / `c4` / `qpow` definitions,
`qpow_add` / `qpow_mono` / `mul_swap4`, and `decide` only on closed concrete-rational facts.
Every load-bearing declaration is gated with `#print axioms`; permitted output is
`propext` / `Quot.sound` only (the `decide` facts depend on NO axioms).  No `Classical.*`,
no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/


namespace YMGap.Continuum.FusionCoreStepRoundM

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundC
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.AutoconvGershgorin

/-! ## 1. The antidiagonal Casimir identity -/

/-- **`c4_antidiag`** — the antidiagonal Casimir identity: `c4 a + c4 b + 2·a·b = c4 (a+b)`.
Because `c4 S = S(S+2)`, the sum of two Casimirs on the antidiagonal `a+b = S` plus twice
their product completes to `c4 S`.  This is the algebraic root of the Gaussian factorization
(`(a+1)² + (b+1)² + 2(a+1)(b+1) = (a+b+2)²`).  Pure `Nat`, `omega` over opaque products. -/
theorem c4_antidiag (a b : Nat) : c4 a + c4 b + 2 * a * b = c4 (a + b) := by
  show a * (a + 2) + b * (b + 2) + 2 * a * b = (a + b) * (a + b + 2)
  have e1 : a * (a + 2) = a * a + a * 2 := Nat.mul_add a a 2
  have e2 : b * (b + 2) = b * b + b * 2 := Nat.mul_add b b 2
  have e3 : (a + b) * (a + b + 2) = (a + b) * (a + b) + (a + b) * 2 := Nat.mul_add (a + b) (a + b) 2
  have e4 : (a + b) * (a + b) = a * (a + b) + b * (a + b) := Nat.add_mul a b (a + b)
  have e5 : a * (a + b) = a * a + a * b := Nat.mul_add a a b
  have e6 : b * (a + b) = b * a + b * b := Nat.mul_add b a b
  have e7 : a * b = b * a := Nat.mul_comm a b
  have e8 : 2 * a * b = 2 * (a * b) := Nat.mul_assoc 2 a b
  omega

/-! ## 2. The exact Gaussian factorization of the weight product -/

/-- **`coeffW_antidiag_gaussian` — THE EXACT GAUSSIAN FACTORIZATION.**  For all `a,b`,

    coeffW w a · coeffW w b · w^{2ab}  ≃  (dimQ a · dimQ b) · w^{c4(a+b)}.

On the antidiagonal `a+b = S` this reads `c_a·c_b = w^{c4 S}·(dimQ a·dimQ b·w^{−2ab})`: the
weight product is the pure Gaussian `w^{c4 S}` times the `w`-free coupling `dimQ a·dimQ b`
carried by the (cleared) negative power `w^{−2ab}`.  This is the structural identity that
exhibits WHERE the reserve of `(†)` comes from: the Gaussian `w^{c4 S}` has second difference
exactly `2` (`c4_sum_symm`), i.e. reserve `w^{−2} = 1/w² ≥ 4` at `w ≤ 1/2`.  Proof: unfold
`coeffW`, regroup `(dimQ a·q^{c4 a})(dimQ b·q^{c4 b})` into `(dimQ a·dimQ b)(q^{c4 a}·q^{c4 b})`
via `mul_swap4`, fuse the three `qpow` factors by `qpow_add`, and collapse the exponent by
`c4_antidiag`. -/
theorem coeffW_antidiag_gaussian (w : Q') (a b : Nat) :
    (coeffW w a * coeffW w b * qpow w (2 * a * b)).eqv
      (dimQ a * dimQ b * qpow w (c4 (a + b))) := by
  -- unfold both coeffW: c_a·c_b = (dimQ a·q^{c4 a})·(dimQ b·q^{c4 b})
  have hunfold : (coeffW w a * coeffW w b).eqv
      ((dimQ a * dimQ b) * (qpow w (c4 a) * qpow w (c4 b))) := by
    show ((dimQ a * qpow w (c4 a)) * (dimQ b * qpow w (c4 b))).eqv
      ((dimQ a * dimQ b) * (qpow w (c4 a) * qpow w (c4 b)))
    exact mul_swap4 (dimQ a) (qpow w (c4 a)) (dimQ b) (qpow w (c4 b))
  -- multiply by q^{2ab} and push it inside the coupling
  have hstep1 : (coeffW w a * coeffW w b * qpow w (2 * a * b)).eqv
      ((dimQ a * dimQ b) * (qpow w (c4 a) * qpow w (c4 b)) * qpow w (2 * a * b)) :=
    Q'.mul_eqv_congr_right (coeffW w a * coeffW w b)
      ((dimQ a * dimQ b) * (qpow w (c4 a) * qpow w (c4 b))) (qpow w (2 * a * b)) hunfold
  -- regroup: (D · P) · R ≃ D · (P · R)
  have hstep2 : ((dimQ a * dimQ b) * (qpow w (c4 a) * qpow w (c4 b)) * qpow w (2 * a * b)).eqv
      ((dimQ a * dimQ b) * ((qpow w (c4 a) * qpow w (c4 b)) * qpow w (2 * a * b))) :=
    Q'.mul_assoc_eqv (dimQ a * dimQ b) (qpow w (c4 a) * qpow w (c4 b)) (qpow w (2 * a * b))
  -- fuse the powers: q^{c4 a}·q^{c4 b} ≃ q^{c4 a + c4 b}
  have hfuse1 : (qpow w (c4 a) * qpow w (c4 b)).eqv (qpow w (c4 a + c4 b)) :=
    Q'.eqv_symm (HeatKernelRGStep.qpow_add w (c4 a) (c4 b))
  -- q^{c4 a + c4 b}·q^{2ab} ≃ q^{c4 a + c4 b + 2ab}
  have hfuse2 : (qpow w (c4 a + c4 b) * qpow w (2 * a * b)).eqv
      (qpow w (c4 a + c4 b + 2 * a * b)) :=
    Q'.eqv_symm (HeatKernelRGStep.qpow_add w (c4 a + c4 b) (2 * a * b))
  -- collapse the exponent by the antidiagonal identity
  have hcollapse : (qpow w (c4 a + c4 b + 2 * a * b)).eqv (qpow w (c4 (a + b))) := by
    rw [c4_antidiag a b]; exact Q'.eqv_refl _
  have hcoupling : ((qpow w (c4 a) * qpow w (c4 b)) * qpow w (2 * a * b)).eqv
      (qpow w (c4 (a + b))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (qpow w (c4 a) * qpow w (c4 b)) (qpow w (c4 a + c4 b))
        (qpow w (2 * a * b)) hfuse1)
      (Q'.eqv_trans _ _ _ hfuse2 hcollapse)
  refine Q'.eqv_trans _ _ _ hstep1 (Q'.eqv_trans _ _ _ hstep2 ?_)
  exact Q'.mul_eqv_congr_left (dimQ a * dimQ b)
    ((qpow w (c4 a) * qpow w (c4 b)) * qpow w (2 * a * b)) (qpow w (c4 (a + b))) hcoupling

/-! ## 3. The reserve budget — why `256/225` is affordable -/

/-- The reserve constant `256/225 = 1 + 31/225`. -/
abbrev reserveC : Q' := Q'.mkPos 256 225 (by decide)

/-- **`gaussianReserveBudget` — the reserve accounting.**  For `0 ≤ w ≤ 1/2`,

    reserveC · w²  ≤  64/225.

After dividing `(†)` by the common Gaussian factor `w^{c4}` the coupling `U` must supply only
the residual budget `(256/225)·w²`, and since `w² ≤ 1/4` this budget is at most
`64/225 ≈ 0.284` — well below the true coupling margin `U(s+3)²/(U(s+2)U(s+4)) → 1/√Q ≥ 0.497`.
So the ENTIRE reserve `256/225` is paid by the Gaussian gap `1/w² ≥ 4`.  Proof: `w² ≤ 1/4`
(`qpow_mono` to `w = 1/2`), scaled by `reserveC ≥ 0`, then `(256/225)·(1/4) = 64/225`. -/
theorem gaussianReserveBudget {w : Q'} (hw0 : (0 : Q') ≤ w) (hw12 : w ≤ wH) :
    reserveC * qpow w 2 ≤ Q'.mkPos 64 225 (by decide) := by
  have hw2q : qpow w 2 ≤ quarter :=
    Q'.le_trans' _ _ _ (qpow_mono hw0 hw12 2) (by decide)
  have h1 : reserveC * qpow w 2 ≤ reserveC * quarter :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hw2q (by decide)
  exact Q'.le_trans' _ _ _ h1 (by decide)

/-! ## 4. The residual HOLDS at the physical point `w = 1/2` (s = 4, extending Round L) -/

/-- The truncated-block reserve `(†)` at `w = 1/2` for mode `s`:
`(256/225)·acN(s+1,s)·acN(s+1,s+2) ≤ acN(s+1,s+1)²`. -/
abbrev reserveHoldsAt (s : Nat) : Prop :=
  reserveC * (acN wH (s + 1) s * acN wH (s + 1) (s + 2))
    ≤ acN wH (s + 1) (s + 1) * acN wH (s + 1) (s + 1)

set_option maxRecDepth 8000 in
/-- **`reserve_holds_at_half_4`** — (†) at `w = 1/2`, `s = 4` (`B/A ≈ 2.077`). -/
theorem reserve_holds_at_half_4 : reserveHoldsAt 4 := by decide

/-! ## 5. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`; the `decide` facts use NO axioms):
  * `c4_antidiag` — the antidiagonal Casimir identity `c4 a + c4 b + 2ab = c4(a+b)`.
  * `coeffW_antidiag_gaussian` — the EXACT Gaussian factorization of the weight product,
    `c_a·c_b·w^{2ab} ≃ (dimQ a·dimQ b)·w^{c4(a+b)}`, exhibiting the Gaussian `w^{c4 S}` and the
    coupling `dimQ a·dimQ b` on the antidiagonal `a+b = S`.
  * `gaussianReserveBudget` — `reserveC·w² ≤ 64/225` on `w ≤ 1/2`: `256/225` costs `≤ 64/225`
    of the coupling margin, the rest is paid by the Gaussian gap `1/w² ≥ 4`.
  * `reserve_holds_at_half_4` — (†) holds at `w = 1/2`, `s = 4` (`B/A ≈ 2.077`); with Round L's
    `s = 0..3` the physical point is verified through `s = 4`.

NAMED OPEN (carried, NOT inhabited here):
  * `(†)` / `AutoconvGershgorin.SymMinorGershgorin w` / `AcNReserveAnalytic.FiniteSMargin w` —
    equivalently the `w`-free coupling log-concavity `U(s+3)² ≥ (256/(225Q))·U(s+2)U(s+4)`,
    `U(S) = Σ_{i+j=S} ij·Q^{ij}`, `Q = 1/w² ≥ 4`.  A discrete theta / local-CLT saddle margin
    (`→ 1/√Q`), NOT recoverable by dominant-term/geometric-tail bounds (which lose the
    saddle-width `θ(Q)²` and fail for every physical `w ≤ 1/2`).

HONEST VERDICT.  Round M supplies the exact Gaussian factorization that localizes and explains
the reserve: the ENTIRE `256/225` is paid by the Gaussian second-difference `w^{−2} ≥ 4`
(`c4_sum_symm`), and the sole open content is the `w`-free coupling log-concavity margin of
`U(S) = Σ ij Q^{ij}` — a genuine heat-kernel local-CLT (saddle-WIDTH) statement, now in its
cleanest form.  Nothing downstream is closed; no guarded Clay-frontier bundle is inhabited;
this is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.FusionCoreStepRoundM

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionCoreStepRoundM.c4_antidiag
#print axioms YMGap.Continuum.FusionCoreStepRoundM.coeffW_antidiag_gaussian
#print axioms YMGap.Continuum.FusionCoreStepRoundM.gaussianReserveBudget
#print axioms YMGap.Continuum.FusionCoreStepRoundM.reserve_holds_at_half_4
-- dropped
-- dropped
-- dropped
-- dropped
