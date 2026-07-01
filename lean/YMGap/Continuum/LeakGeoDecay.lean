/-
Track A / R2 — the CONVERSE of the Andréief-Gershgorin reduction: collapsing the aggregate
`symMinor` Gershgorin domination (`AutoconvGershgorin.SymMinorGershgorin`) to the SINGLE
untruncated-`acN` central-autoconvolution log-concavity reserve.

# What this module adds (read first — load-bearing honesty)

`AutoconvGershgorin` proved the Andréief half-sum identity

    2·(acN(s+1,s)·acN(s+1,s+2) − acN(s+1,s+1)²)  ≃  −symQuadForm(s),                    (⋆)
      symQuadForm(s) := Σ_{i,j<s+1} c_i c_j symMinor(s−i,s−j),

and used it (via `reserve_of_double_and_dom`) for the FORWARD direction

    SymMinorGershgorin  ⟹  δ·A ≤ B + −A,   A := acN(s+1,s)·acN(s+1,s+2), B := acN(s+1,s+1)².

`SymMinorGershgorinProof` then tried to DISCHARGE `SymMinorGershgorin` through a two-residual
band split (`QuadSlackLower` + `AnchorDominatesProd`).  That plan is UNSOUND at the leak level:
for the extremal admissible super-log-concave sequence `c_k = (1/4)^{k(k+1)/2}` (which saturates
every available `coeffW` handle), the geometric leak target `L_env ≤ (1/15)·S` is FALSE
(measured `L_env/S ≈ 0.25–0.57`) and the anchor-product bridge `2·A ≤ S` is FALSE
(`2A/S ≈ 1.88–2.26`).  So neither `QuadSlackLower`'s band-split route nor `AnchorDominatesProd`
can be inhabited from the atoms; the leak is an *in-antidiagonal spread* whose per-term envelope
GROWS with `|i−j|`, not the off-antidiagonal decay the `offAuto_dominate` template provides.

The correct move is not to lower-bound `symQuadForm` by `S` at all, but to run the half-sum
identity (⋆) BACKWARD.  Since (⋆) is an EQUALITY, `SymMinorGershgorin` is *equivalent* to the
single scalar reserve, and the whole node collapses to one already-named wall.

DELIVERABLE (PROVED, axiom-clean).
  * `sym_eq_two_defect` — the pure-`Q'` half-sum inversion: from `(A + −B) + (A + −B) ≃ −Ssym`
    conclude `Ssym ≃ 2·(B + −A)`.  (The `hE1/hE2/hEfull` core of `reserve_of_double_and_dom`,
    isolated and re-used in the converse direction.)
  * `gershgorin_of_reserve_core` — from that identity and the reserve `δ·A ≤ B + −A`, conclude
    the Gershgorin domination `2·(δ·A) ≤ Ssym` (scale by `0 ≤ 2`, rewrite `2·(B+−A) ≃ Ssym`).
  * `AcNDefectReserve w` — the SOLE genuine residual on the UNTRUNCATED `acN` block:
        δ·(acN(s+1,s)·acN(s+1,s+2)) ≤ acN(s+1,s+1)² + −(acN(s+1,s)·acN(s+1,s+2)),   δ = 31/225,
    equivalently `(1+δ)·acN(s+1,s)·acN(s+1,s+2) ≤ acN(s+1,s+1)²`.  This is the local-CLT
    log-concavity node the whole Round-G/H/I stack already reduces to (`AutoconvReserveResidual`
    on the untruncated idealization); it holds numerically with ≈2× margin.  NAMED-OPEN.
  * `gershgorinOfReserve` — THE CONVERSE: `AcNDefectReserve w ⟹ SymMinorGershgorin w`.
  * `reserveOfGershgorin` — the FORWARD packaging: `SymMinorGershgorin w ⟹ AcNDefectReserve w`
    (each field is `AutoconvGershgorin.acN_defect_reserve_of_gershgorin`).
  * `gershgorin_iff_reserve` — the two witnesses paired: `SymMinorGershgorin` and
    `AcNDefectReserve` inter-derive.  The two-residual plan is thereby BYPASSED — the node
    closes iff the one reserve closes.

# HONESTY — what is NOT closed

`AcNDefectReserve w` is NAMED-OPEN; this module does NOT inhabit it.  It is the genuine
heat-kernel local-CLT log-concavity reserve (the same content as `AutoconvReserveResidual`,
modulo the separate `H0auto`↦`acN` truncation-edge bridge).  What is proved here is the EXACT
equivalence of the aggregate Gershgorin domination with that one reserve — i.e. the two-residual
`QuadSlackLower`/`AnchorDominatesProd` route (falsified above) is unnecessary and the node has a
single residual.  This is a structural sharpening of one box-level log-concavity sub-fact; it is
NOT a 4D Yang–Mills mass gap.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` arithmetic, the reused `acN`/`symMinor`/`coeffW`/`symQuadForm` definitions, the
`acN_defect_double_eq` half-sum identity, `q2_neg`, `ofNat_two_mul_eqv`, `neg_defect_comm`,
`Q'.mul_le_mul_of_nonneg_left`.  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no `native_decide`, no
`sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.SymMinorGershgorinProof

namespace YMGap.Continuum.LeakGeoDecay

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SelfFusionLogConcave
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionCoreStepRoundF
open YMGap.Continuum.FusionCoreStepRoundJ
open YMGap.Continuum.LocalCLTSteepestDescent
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.SymMinorGershgorinProof

/-! ## 1. The pure-`Q'` half-sum inversion -/

/-- **`sym_eq_two_defect`** — the half-sum identity, inverted.  From
`(A + −B) + (A + −B) ≃ −Ssym` conclude `Ssym ≃ 2·(B + −A)`.  This is the `hE1/hE2/hEfull` core of
`AutoconvGershgorin.reserve_of_double_and_dom`, isolated so the converse can reuse it. -/
theorem sym_eq_two_defect {A B Ssym : Q'}
    (hMD : ((A + -B) + (A + -B)).eqv (-Ssym)) :
    Ssym.eqv (Q'.ofNat 2 * (B + -A)) := by
  have hE1 : Ssym.eqv (-((A + -B) + (A + -B))) :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.neg_neg_eqv Ssym))
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hMD))
  have hE2 : (-((A + -B) + (A + -B))).eqv ((B + -A) + (B + -A)) :=
    Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (A + -B) (A + -B))
      (Q'.add_eqv_congr' (neg_defect_comm A B) (neg_defect_comm A B))
  exact Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ hE1 hE2)
    (Q'.eqv_symm (ofNat_two_mul_eqv (B + -A)))

/-- **`gershgorin_of_reserve_core`** — the pure-`Q'` converse cancellation.  From the half-sum
identity `(A + −B) + (A + −B) ≃ −Ssym` and the defect reserve `δ·A ≤ B + −A`, conclude the
Gershgorin domination `2·(δ·A) ≤ Ssym`.  (Scale the reserve by `0 ≤ 2`, then rewrite
`2·(B + −A) ≃ Ssym`.) -/
theorem gershgorin_of_reserve_core {A B Ssym : Q'}
    (hMD : ((A + -B) + (A + -B)).eqv (-Ssym))
    (hres : Q'.mkPos 31 225 (by decide) * A ≤ B + -A) :
    Q'.ofNat 2 * (Q'.mkPos 31 225 (by decide) * A) ≤ Ssym := by
  have hmul :
      Q'.ofNat 2 * (Q'.mkPos 31 225 (by decide) * A) ≤ Q'.ofNat 2 * (B + -A) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hres (Q'.le_of_lt (Q'.ofNat_succ_pos 1))
  exact Q'.le_trans' _ _ _ hmul (Q'.ge_of_eqv (sym_eq_two_defect hMD))

/-! ## 2. The single untruncated-`acN` reserve residual -/

/-- **`AcNDefectReserve w`** — the SOLE genuine residual to which the whole `symMinor` Gershgorin
node collapses: the untruncated central-autoconvolution log-concavity defect exceeds `δ = 31/225`
of the product on the range-`(s+1)` block,

    δ·(acN(s+1,s)·acN(s+1,s+2)) ≤ acN(s+1,s+1)² + −(acN(s+1,s)·acN(s+1,s+2)),

equivalently `(1+δ)·acN(s+1,s)·acN(s+1,s+2) ≤ acN(s+1,s+1)²`.  This is the same local-CLT
log-concavity content as `LocalCLTSteepestDescent.AutoconvReserveResidual` (on the untruncated
idealization); it holds numerically with ≈2× margin.  NAMED-OPEN (never `sorry`). -/
structure AcNDefectReserve (w : Q') : Type where
  /-- The autoconvolution log-concavity reserve on the uniform range-`(s+1)` block. -/
  reserve : ∀ s,
    Q'.mkPos 31 225 (by decide) * (acN w (s + 1) s * acN w (s + 1) (s + 2))
      ≤ acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1)
        + -(acN w (s + 1) s * acN w (s + 1) (s + 2))

/-! ## 3. The converse (and the paired equivalence) -/

/-- The half-sum identity `(A + −B) + (A + −B) ≃ −symQuadForm(s)` on the range-`(s+1)` block,
extracted from `AutoconvGershgorin.acN_defect_double_eq` (the same `hMD` used forward in
`acN_defect_reserve_of_gershgorin`). -/
theorem acN_half_sum_eq (w : Q') (s : Nat) :
    ((acN w (s + 1) s * acN w (s + 1) (s + 2)
        + -(acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1)))
      + (acN w (s + 1) s * acN w (s + 1) (s + 2)
        + -(acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1)))).eqv
      (-(symQuadForm w s)) :=
  Q'.eqv_trans _ _ _ (acN_defect_double_eq w (s + 1) s (Nat.le_refl (s + 1)))
    (Q'.eqv_symm
      (q2_neg (fun i j => coeffW w i * coeffW w j * symMinor w (s - i) (s - j)) (s + 1)))

/-- **`gershgorinOfReserve` — THE CONVERSE.**  The single untruncated-`acN` reserve residual
yields a full `SymMinorGershgorin` witness, by running the Andréief half-sum identity BACKWARD
(`gershgorin_of_reserve_core` on `acN_half_sum_eq`).  This is the converse of
`AutoconvGershgorin.acN_defect_reserve_of_gershgorin`. -/
def gershgorinOfReserve {w : Q'} (r : AcNDefectReserve w) : SymMinorGershgorin w where
  gershgorin := fun s => gershgorin_of_reserve_core (acN_half_sum_eq w s) (r.reserve s)

/-- **`reserveOfGershgorin` — THE FORWARD packaging.**  A `SymMinorGershgorin` witness yields the
single reserve residual (each field is `AutoconvGershgorin.acN_defect_reserve_of_gershgorin`). -/
def reserveOfGershgorin {w : Q'} (g : SymMinorGershgorin w) : AcNDefectReserve w where
  reserve := fun s => acN_defect_reserve_of_gershgorin g s

/-- **`gershgorin_iff_reserve` — THE COLLAPSE.**  The aggregate `symMinor` Gershgorin domination
and the single untruncated-`acN` log-concavity reserve inter-derive.  The whole node closes iff
this ONE reserve closes; the two-residual `QuadSlackLower`/`AnchorDominatesProd` band-split route
is thereby bypassed (and, per the header, is individually false for the extremal sequence). -/
def gershgorin_iff_reserve (w : Q') :
    (AcNDefectReserve w → SymMinorGershgorin w) × (SymMinorGershgorin w → AcNDefectReserve w) :=
  (gershgorinOfReserve, reserveOfGershgorin)

/-! ## 4. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `sym_eq_two_defect` — the pure-`Q'` half-sum inversion `Ssym ≃ 2·(B + −A)`.
  * `gershgorin_of_reserve_core` — `δ·A ≤ B + −A` and the half-sum identity yield `2·(δ·A) ≤ Ssym`.
  * `acN_half_sum_eq` — the range-`(s+1)` half-sum identity `(A+−B)+(A+−B) ≃ −symQuadForm(s)`.
  * `gershgorinOfReserve` — the CONVERSE: one reserve yields the full Gershgorin domination.
  * `reserveOfGershgorin` — the forward packaging.
  * `gershgorin_iff_reserve` — the two witnesses paired (the node ⟺ the single reserve).

NAMED OPEN (Type-level structure, never `sorry`):
  * `AcNDefectReserve w` — the untruncated central-autoconvolution log-concavity reserve
    `δ·(acN(s+1,s)·acN(s+1,s+2)) ≤ acN(s+1,s+1)² + −(acN(s+1,s)·acN(s+1,s+2))`.  This is the
    genuine local-CLT wall (`AutoconvReserveResidual` on the untruncated idealization).

HONEST VERDICT.  This module PROVES that the aggregate `symMinor` Gershgorin domination
(`AutoconvGershgorin.SymMinorGershgorin`) is EQUIVALENT to the single untruncated-`acN`
log-concavity reserve, collapsing the node to one residual and BYPASSING the two-residual
band-split plan (`QuadSlackLower` + `AnchorDominatesProd`), whose leak/anchor targets are false
for the extremal admissible sequence.  It does NOT inhabit that reserve.  This is a structural
sharpening of one box-level log-concavity sub-fact; it is NOT a 4D Yang–Mills mass gap. -/

end YMGap.Continuum.LeakGeoDecay

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.LeakGeoDecay.sym_eq_two_defect
#print axioms YMGap.Continuum.LeakGeoDecay.gershgorin_of_reserve_core
#print axioms YMGap.Continuum.LeakGeoDecay.acN_half_sum_eq
#print axioms YMGap.Continuum.LeakGeoDecay.gershgorinOfReserve
#print axioms YMGap.Continuum.LeakGeoDecay.reserveOfGershgorin
#print axioms YMGap.Continuum.LeakGeoDecay.gershgorin_iff_reserve
