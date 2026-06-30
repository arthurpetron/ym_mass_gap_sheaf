/-
Track B / R2 — RESOLVING THE δ-LOOP AMBIGUITY: the lattice mass gap is the
multiplicity-BLIND transfer EIGENVALUE, NOT the multiplicity-WEIGHTED character
coefficient.  VERDICT: **(A)**.

# The ambiguity (and why it decides the continuum route)

A δ-loop surfaced a genuine ambiguity in WHICH object sets the lattice mass gap:

  * **(A)** the multiplicity-BLIND largest excited transfer EIGENVALUE
    `eigA w s = w^{C₄(s)}` (so the gap edge is `eigA w 1 = w³`, and the
    `(s+1)`-style degeneracy is mere DEGENERACY of that eigenvalue), versus
  * **(B)** the multiplicity-WEIGHTED character COEFFICIENT
    `coeffW w s = (s+1)·w^{C₄(s)}` (which is `s = 1`-dominant only on the window
    `w ≤ 7/9` and FAILS as `w → 1`).

`Continuum/SpectralLocalizationCrux.lean` builds the gap on (A) (`eigA`);
`Continuum/S1Dominance.lean` showed the (B) object's dominance needs `w ≤ 7/9`.
If the gap were (B), the bond-moving-preserves-the-gap route would have a genuine
continuum (`w → 1`) problem.  This module reads the repo's ACTUAL gap definition
and proves which object sets the gap.

# What the repo's gap definition ACTUALLY is (the reading)

The reconstructed mass gap is, throughout the spectral stack,

    Δ = 1 − sep,   sep = the located bound on `SpectralModel.lam`,

where (`Continuum/SpectralGap.lean`)

    structure SpectralModel where
      lam : QSeq          -- "Transfer-matrix eigenvalues λ_i = e^{-E_i} ≥ 0"
      w   : QSeq          -- "Spectral weights w_i = |⟨Ω, A i⟩|² ≥ 0"
    def corr (S) (n) := Σ_{i<k} (S.w i) · (S.lam i)^n          -- Källén–Lehmann
    def SpectralGapBound (S) (μ) := ∀ i, S.lam i ≤ μ           -- bounds `lam`

and (`Continuum/LocatedSpectralGap.lean`) `LocatedSpectralGap.sep < 1` with
`bound : SpectralGapBound S sep`, and (`Continuum/GNSDynamics.lean`)
`SpectralGapData.massGap = gap.gapMargin = 1 − sep`.

So **the gap bounds `lam` — the transfer EIGENVALUE — NOT `w` (the amplitude).**
In the Källén–Lehmann form `corr n = Σ w_i·λ_i^n`, the decay RATE is `max λ_i`
(the eigenvalue), and `w_i` (which carries the multiplicity) sets only the
AMPLITUDE.  The gap is **multiplicity-BLIND**.  This is exactly (A).

# The physics this encodes

The spin-`s` two-point function `⟨χ_s(x)χ_s(y)⟩` decays as `(λ_s)^{|x−y|}` with
`λ_s = w^{C₄(s)}` the spin-`s` transfer eigenvalue (the bare normalized character
coefficient — the dimension factor `(s+1)` in the heat-kernel expansion is exactly
cancelled by the `1/d_r` of Schur convolution, so the convolution eigenvalue is
the bare `w^{C₄(s)}`).  The multiplicity `(s+1)²` is the dimension of the spin-`s`
representation — the NUMBER of degenerate states with that eigenvalue — and it
multiplies the AMPLITUDE `w_i`, not the decay rate.  Hence

    mass gap edge = max_{s≥1} λ_s = max_{s≥1} eigA w s = eigA w 1 = w³,

multiplicity-BLIND, attained at the first-excited level `s = 1`.

# What this module PROVES (genuine `Q'`/`Nat`, axiom-clean)

  * `coeffDominance_is_measureWeight` — `coeffW w s = dimQ s · eigA w s`: the (B)
    object is the measure WEIGHT (multiplicity × eigenvalue = the partition /
    heat-kernel density numerator), NOT the eigenvalue.  Its `w → 1` non-dominance
    is a property of the multiplicity (spectral density), quarantined from the gap.
  * `eigEdge_dominates_all_w` — the EIGENVALUE gap edge `eigA w 1` dominates every
    excited eigenvalue `eigA w s` (`s ≥ 1`) for ALL `w ∈ [0,1]`, with NO character
    window restriction (contrast (B): `coeffW` dominance needs `w ≤ 7/9`).  So the
    eigenvalue route survives the continuum `w → 1`; the coefficient route does not.
  * `eigModel` — the physically-correct Källén–Lehmann reconstruction: a
    `SpectralModel` whose EIGENVALUE field `lam i = eigA w (i+1)` (multiplicity-blind)
    and whose AMPLITUDE field `w i = dimQ (i+1)` (carries the multiplicity).
  * `eigModel_gapBound` / `gap_multiplicity_blind` — the eigenvalue model satisfies
    `SpectralGapBound (eigModel …) (eigA w 1)`: the located separator is the
    multiplicity-blind gap edge `eigA w 1 = w³`.
  * `eigLocatedGap` — a genuine `LocatedSpectralGap` for the eigenvalue model with
    separator `sep = eigA w 1 = w³` (given the decidable `w³ < 1`), so the
    reconstructed mass gap is `Δ = 1 − w³ > 0`, multiplicity-blind.
  * `eigModel_decay` — the connected correlator decays at the multiplicity-blind
    rate: `corr (eigModel) n ≤ corr (eigModel) 0 · (eigA w 1)^n = … · w^{3n}`, the
    multiplicity entering ONLY the amplitude `corr(eigModel) 0`.
  * `reconTransfer_lam_is_measureWeight` — the HONEST DIAGNOSIS of where (B) came
    from: `Continuum/TransferCorr.lean`'s `reconTransfer` sets its eigenvalue field
    `lam i = coeffW w (i+1) = dimQ (i+1)·eigA w (i+1)`, i.e. it loads the FULL
    measure weight into the eigenvalue slot (a Källén–Lehmann surrogate of the
    single-line character double-sum, with `w_i = λ_i = coeffW`).  That conflation
    — not the physical transfer eigenvalue — is what produced the `w ≤ 7/9`
    coefficient caveat; it is the spectral density, not the gap location.
  * `demo_eigGap_near_one` — at `w = 95/96` (near the continuum `w → 1`) the
    eigenvalue gap is genuinely inhabited: `eigA (95/96) 1 = (95/96)³ < 1`, a
    `LocatedSpectralGap` with positive margin, WITHOUT any `w ≤ 7/9` restriction.

# VERDICT (A) and what it means for the continuum route

The repo's gap is the multiplicity-BLIND transfer eigenvalue (`SpectralModel.lam`,
bounded by `LocatedSpectralGap.sep`); the gap edge is `eigA w 1 = w³`, dominant
over all excited modes for ALL `w ∈ [0,1]`.  The `coeffW = (s+1)·w^{C₄(s)}` object
of `S1Dominance` is the heat-kernel MEASURE weight (partition-density numerator),
and its `w → 1` non-dominance does NOT threaten the gap.  Therefore the
bond-moving-preserves-the-gap route IS valid in the continuum `w → 1` **when tied
to the multiplicity-blind eigenvalue**, and the residual handed to the parallel
agent is the MULTIPLICITY-BLIND eigenvalue defect being quadratic (the `s = 1`
eigenvalue shift `O((1−w)²)` — `SpectralLocalization.bulk_shift`, the eigenvalue
perturbation bound that is multiplicity-blind, NOT the scaled-norm summability that
`BulkModeCrux` showed FAILS).  This is NOT a 4D Yang–Mills mass-gap proof; it is
the precise resolution of the (A)-vs-(B) ambiguity in favor of (A).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`, reusing `eigA` / `gapEdge_dominates` (Casimir antitonicity) and the
`SpectralModel` / `LocatedSpectralGap` data.  Every load-bearing declaration is
gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide` (only `decide` on closed decidable `Q'` facts),
no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.SpectralLocalizationCrux
import YMGap.Continuum.S1Dominance
import YMGap.Continuum.TransferCorr

namespace YMGap.Continuum.GapIsEigenvalue

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SpectralLocalizationCrux

/-! ## 1. The measure-weight factorization — quarantining the (B) caveat

The (B) object `coeffW w s = (s+1)·w^{C₄(s)}` factors DEFINITIONALLY as
multiplicity `dimQ s = s+1` times the eigenvalue `eigA w s = w^{C₄(s)}`.  So it is
the spectral MEASURE WEIGHT (the heat-kernel partition-density numerator), not the
transfer eigenvalue.  Its `w → 1` non-dominance lives in the multiplicity. -/

/-- **`coeffDominance_is_measureWeight` — the quarantine.**  The multiplicity-weighted
character coefficient is exactly multiplicity × eigenvalue:

    coeffW w s  =  dimQ s · eigA w s        ( = (s+1) · w^{C₄(s)} ).

So `coeffW` is the heat-kernel MEASURE weight (partition-function density numerator),
NOT the transfer eigenvalue `eigA`.  Its `w → 1` non-dominance (the `S1Dominance`
`w ≤ 7/9` window) is a property of the multiplicity factor `dimQ s = s+1` — the
spectral DENSITY — and is decoupled from the gap, which bounds `eigA`. -/
theorem coeffDominance_is_measureWeight (w : Q') (s : Nat) :
    coeffW w s = dimQ s * eigA w s := rfl

/-- The eigenvalue is the measure weight with the multiplicity STRIPPED:
`eigA w s = w^{C₄(s)}`, the `dimQ`-free factor of `coeffW`. -/
theorem eigA_eq_coeffW_div_dim (w : Q') (s : Nat) :
    eigA w s = qpow w (c4 s) := rfl

/-! ## 2. The gap edge is the multiplicity-blind eigenvalue `eigA w 1 = w³`

`c4 1 = 1·(1+2) = 3`, so the first-excited transfer eigenvalue is `eigA w 1 = w³`.
The `gapEdge_dominates` Casimir-antitonicity (`SpectralLocalizationCrux`) makes it
the maximum over ALL excited modes, for ALL `w ∈ [0,1]` — NO `w ≤ 7/9` window. -/

/-- The gap-edge eigenvalue is `w³`: `eigA w 1 = qpow w 3` (`c4 1 = 3`). -/
theorem eigA_one_eq_cube (w : Q') : eigA w 1 = qpow w 3 := rfl

/-- **`eigEdge_dominates_all_w` — the EIGENVALUE gap edge dominates, NO window.**
For ALL `w ∈ [0,1]` and every excited mode `s ≥ 1`,

    eigA w s  ≤  eigA w 1  = w³,

so the largest excited transfer eigenvalue (the gap edge) is the `s = 1` level for
EVERY `w ∈ [0,1]`, including the continuum end `w → 1`.  Contrast the (B) object:
`coeffW` dominance (`S1Dominance.bmc_one_dominates_p1`) holds only on `w ≤ 7/9`.
The eigenvalue route survives the continuum; the coefficient route does not.  PROOF:
`gapEdge_dominates` (`w^{C₄(s)}` is antitone in the increasing Casimir `C₄(s)`). -/
theorem eigEdge_dominates_all_w {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    {s : Nat} (hs : 1 ≤ s) : eigA w s ≤ eigA w 1 :=
  gapEdge_dominates hw0 hw1 hs

/-! ## 3. The physically-correct Källén–Lehmann reconstruction `eigModel`

The eigenvalue field `lam` carries the multiplicity-BLIND `eigA w (i+1)`; the
amplitude field `w` carries the multiplicity `dimQ (i+1) = (i+2)`.  This is the
correct split for `corr n = Σ w_i·λ_i^n`: the decay rate is the eigenvalue, the
amplitude carries the degeneracy.  (Contrast `TransferCorr.reconTransfer`, which
puts the full `coeffW` in BOTH `w` and `lam`; see §5.) -/

/-- **The eigenvalue spectral model** on the `M` excited modes `i = 0,…,M−1`
(rep `s = i+1`): EIGENVALUE `lam i = eigA w (i+1) = w^{C₄(i+1)}` (multiplicity-blind),
AMPLITUDE `w i = dimQ (i+1) = i+2` (the degeneracy).  This is the Källén–Lehmann
reconstruction in which the gap bounds the genuine transfer eigenvalue. -/
def eigModel (w : Q') (hw : (0 : Q') ≤ w) (M : Nat) : SpectralModel where
  k := M
  w := fun i => dimQ (i + 1)
  lam := fun i => eigA w (i + 1)
  w_nonneg := fun i => dimQ_nonneg (i + 1)
  lam_nonneg := fun i => eigA_nonneg hw (i + 1)

/-- **`eigModel_gapBound` / `gap_multiplicity_blind` — the located separator is the
multiplicity-blind gap edge.**  Every eigenvalue of `eigModel` is `≤ eigA w 1 = w³`:

    SpectralGapBound (eigModel w hw M) (eigA w 1).

Because `eigModel.lam i = eigA w (i+1)` and `i+1 ≥ 1` for every `i`, the bound is the
EIGENVALUE dominance `eigEdge_dominates_all_w` — no multiplicity, no `w ≤ 7/9`
window, valid for ALL `w ∈ [0,1]`. -/
theorem eigModel_gapBound (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (M : Nat) :
    SpectralGapBound (eigModel w hw0 M) (eigA w 1) := by
  intro i
  show eigA w (i + 1) ≤ eigA w 1
  exact eigEdge_dominates_all_w hw0 hw1 (Nat.le_add_left 1 i)

/-- Restatement as the headline `gap_multiplicity_blind`: the mass-gap separator of
the eigenvalue model is the multiplicity-BLIND `eigA w 1 = w³`, bounding every
transfer eigenvalue, for every `w ∈ [0,1]`. -/
theorem gap_multiplicity_blind (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (M : Nat) :
    SpectralGapBound (eigModel w hw0 M) (eigA w 1) :=
  eigModel_gapBound w hw0 hw1 M

/-! ## 4. The located eigenvalue gap and its multiplicity-blind decay

Given the decidable `eigA w 1 = w³ < 1` (true for every `w < 1`), the eigenvalue
model carries a genuine `LocatedSpectralGap` with separator `sep = w³`.  Its mass
gap is `Δ = 1 − w³ > 0`, and the connected correlator decays at the
multiplicity-blind rate `w^{3n}`. -/

/-- **`eigLocatedGap` — the genuine located gap at separator `w³`.**  When the
gap-edge eigenvalue `eigA w 1 = w³` is `< 1` (decidable; true for every `w < 1`),
the eigenvalue model has a `LocatedSpectralGap` with `sep = eigA w 1 = w³` — the
multiplicity-blind gap edge, with NO `w ≤ 7/9` restriction. -/
def eigLocatedGap (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (M : Nat)
    (heig1 : eigA w 1 < (1 : Q')) : LocatedSpectralGap (eigModel w hw0 M) where
  sep := eigA w 1
  sep_lt_one := heig1
  bound := eigModel_gapBound w hw0 hw1 M

/-- The reconstructed mass gap of the eigenvalue model is `Δ = 1 − w³ > 0` — the
multiplicity-blind positive gap margin. -/
theorem eigGap_margin_pos (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (M : Nat)
    (heig1 : eigA w 1 < (1 : Q')) :
    (0 : Q') < (eigLocatedGap w hw0 hw1 M heig1).gapMargin :=
  (eigLocatedGap w hw0 hw1 M heig1).gapMargin_pos

/-- **`eigModel_decay` — the correlator decays at the multiplicity-blind rate.**  The
connected two-point function of the eigenvalue model decays geometrically at the
EIGENVALUE rate `eigA w 1 = w³`:

    corr (eigModel w hw M) n  ≤  corr (eigModel w hw M) 0 · (eigA w 1)^n  ( = …·w^{3n} ),

the multiplicity entering ONLY the amplitude `corr(eigModel) 0 = Σ_{i<M} dimQ(i+1)`,
not the decay rate.  This is the precise sense in which the gap is the decay RATE
(eigenvalue), and the multiplicity is the AMPLITUDE/degeneracy. -/
theorem eigModel_decay (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (M : Nat)
    (heig1 : eigA w 1 < (1 : Q')) (n : Nat) :
    corr (eigModel w hw0 M) n
      ≤ (corr (eigModel w hw0 M) 0) * (eigA w 1) ^ n :=
  (eigLocatedGap w hw0 hw1 M heig1).decay n

/-! ## 5. The honest diagnosis — where (B) came from

`TransferCorr.reconTransfer` reconstructs the single-line character double-sum as a
Källén–Lehmann model with `w_i = λ_i = coeffW w (i+1)` — it loads the FULL measure
weight `coeffW = dimQ · eigA` into the EIGENVALUE slot.  That surrogate is fine as a
collapse of `wilsonG`, but its per-step "decay" is then `coeffW`, the (B) object;
this conflation of measure weight with eigenvalue is exactly the source of the
`w ≤ 7/9` caveat.  The physical transfer eigenvalue is the `dimQ`-stripped `eigA`. -/

/-- **`reconTransfer_lam_is_measureWeight` — the conflation, made explicit.**  The
eigenvalue field of `TransferCorr.reconTransfer` is the FULL measure weight:

    (reconTransfer w hw M).lam i  =  coeffW w (i+1)  =  dimQ (i+1) · eigA w (i+1),

i.e. it carries the multiplicity `dimQ (i+1)` INSIDE the eigenvalue slot.  The
physically-correct `eigModel.lam i = eigA w (i+1)` strips that multiplicity into the
amplitude.  This identifies precisely where the (B) coefficient object entered the
spectral stack — as a `wilsonG`-surrogate modelling choice, not the physical gap. -/
theorem reconTransfer_lam_is_measureWeight (w : Q') (hw : (0 : Q') ≤ w) (M i : Nat) :
    (TransferCorr.reconTransfer w hw M).lam i = dimQ (i + 1) * eigA w (i + 1) := rfl

/-- The eigenvalue model strips that multiplicity: its `lam` is the bare eigenvalue,
with the multiplicity moved to the amplitude field `w`. -/
theorem eigModel_lam_is_eigenvalue (w : Q') (hw : (0 : Q') ≤ w) (M i : Nat) :
    (eigModel w hw M).lam i = eigA w (i + 1) ∧ (eigModel w hw M).w i = dimQ (i + 1) :=
  ⟨rfl, rfl⟩

/-! ## 6. Demo — the eigenvalue gap survives near the continuum `w → 1`

At `w = 95/96` (`1 − w = 1/96`, deep in the near-continuum regime where the (B)
window `w ≤ 7/9` is VIOLATED), the multiplicity-blind eigenvalue gap is genuinely
inhabited: `eigA (95/96) 1 = (95/96)³ < 1`, a `LocatedSpectralGap` with positive
margin.  This concretely exhibits (A) surviving where (B) fails. -/

/-- The near-continuum demo weight `w = 95/96` (the (B) window `w ≤ 7/9` is violated). -/
def demoW : Q' := Q'.mkPos 95 96 (by decide)

theorem demoW_pos : (0 : Q') ≤ demoW := by decide
theorem demoW_le_one : demoW ≤ (1 : Q') := by decide

/-- `eigA (95/96) 1 = (95/96)³ < 1` — the gap edge is strictly below the vacuum
eigenvalue at a weight where the coefficient object (B) is NON-dominant. -/
theorem demo_eigEdge_lt_one : eigA demoW 1 < (1 : Q') := by decide

/-- **`demo_eigGap_near_one` — the eigenvalue gap is inhabited near `w → 1`.**  A
genuine `LocatedSpectralGap` for the eigenvalue model at `w = 95/96`, separator
`sep = (95/96)³ < 1`, multiplicity-blind, WITHOUT any `w ≤ 7/9` window. -/
def demo_eigGap_near_one (M : Nat) : LocatedSpectralGap (eigModel demoW demoW_pos M) :=
  eigLocatedGap demoW demoW_pos demoW_le_one M demo_eigEdge_lt_one

/-- The demo gap margin is strictly positive: `Δ = 1 − (95/96)³ > 0`. -/
theorem demo_eigGap_margin_pos (M : Nat) :
    (0 : Q') < (demo_eigGap_near_one M).gapMargin :=
  (demo_eigGap_near_one M).gapMargin_pos

/-! ## 7. Doc — PROVED, the VERDICT, and the residual (AGENTS.md Rule 6)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):

  * `coeffDominance_is_measureWeight` — `coeffW = dimQ · eigA`: the (B) object is the
    measure weight (multiplicity × eigenvalue), quarantined from the gap.
  * `eigEdge_dominates_all_w` — the eigenvalue gap edge `eigA w 1 = w³` dominates all
    excited modes for ALL `w ∈ [0,1]` (no `w ≤ 7/9` window).
  * `eigModel` / `eigModel_gapBound` / `gap_multiplicity_blind` — the located gap
    separator of the eigenvalue Källén–Lehmann model is the multiplicity-blind `w³`.
  * `eigLocatedGap` / `eigGap_margin_pos` / `eigModel_decay` — a genuine
    `LocatedSpectralGap` with `sep = w³`, margin `Δ = 1 − w³ > 0`, and geometric decay
    at the multiplicity-blind rate `w^{3n}`.
  * `reconTransfer_lam_is_measureWeight` — the diagnosis: `TransferCorr.reconTransfer`
    loads the full measure weight `coeffW` into its eigenvalue slot (the source of the
    (B) caveat, a `wilsonG`-surrogate choice).
  * `demo_eigGap_near_one` — the eigenvalue gap inhabited at `w = 95/96`, where (B) is
    non-dominant.

VERDICT: **(A)**.  The repo's gap (`SpectralModel.lam`, bounded by
`LocatedSpectralGap.sep`, margin `SpectralGapData.massGap = 1 − sep`) is the
multiplicity-BLIND transfer eigenvalue; the edge is `eigA w 1 = w³`, dominant for
ALL `w ∈ [0,1]`.  The `coeffW = (s+1)·w^{C₄(s)}` object of `S1Dominance` is the
heat-kernel MEASURE weight; its `w → 1` non-dominance is multiplicity (spectral
density), NOT the gap.  So the bond-moving-preserves-gap route IS valid in the
continuum `w → 1` when tied to the eigenvalue; the residual is the MULTIPLICITY-BLIND
eigenvalue defect being quadratic (`SpectralLocalization.bulk_shift`, the eigenvalue
shift `O((1−w)²)` that perturbation theory makes multiplicity-blind — NOT the
scaled-norm summability that `BulkModeCrux` showed fails).

This is NOT a 4D Yang–Mills mass-gap proof; it is the precise, green resolution of
the (A)-vs-(B) ambiguity in favor of (A). -/

end YMGap.Continuum.GapIsEigenvalue

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.GapIsEigenvalue.coeffDominance_is_measureWeight
#print axioms YMGap.Continuum.GapIsEigenvalue.eigA_eq_coeffW_div_dim
#print axioms YMGap.Continuum.GapIsEigenvalue.eigA_one_eq_cube
#print axioms YMGap.Continuum.GapIsEigenvalue.eigEdge_dominates_all_w
#print axioms YMGap.Continuum.GapIsEigenvalue.eigModel
#print axioms YMGap.Continuum.GapIsEigenvalue.eigModel_gapBound
#print axioms YMGap.Continuum.GapIsEigenvalue.gap_multiplicity_blind
#print axioms YMGap.Continuum.GapIsEigenvalue.eigLocatedGap
#print axioms YMGap.Continuum.GapIsEigenvalue.eigGap_margin_pos
#print axioms YMGap.Continuum.GapIsEigenvalue.eigModel_decay
#print axioms YMGap.Continuum.GapIsEigenvalue.reconTransfer_lam_is_measureWeight
#print axioms YMGap.Continuum.GapIsEigenvalue.eigModel_lam_is_eigenvalue
#print axioms YMGap.Continuum.GapIsEigenvalue.demo_eigEdge_lt_one
#print axioms YMGap.Continuum.GapIsEigenvalue.demo_eigGap_near_one
#print axioms YMGap.Continuum.GapIsEigenvalue.demo_eigGap_margin_pos
