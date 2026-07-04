/-
Track 11.7-fusion / R2 — **the discrete SU(2) fusion local-CLT residual, re-expressed
in LOG / SADDLE form and WIRED to the δ-loop capstone.**

# What this module does (read first)

The δ-loop (`DeltaFrontierLedger`) reduced the 4D Migdal–Kadanoff bond-moving
obstruction to ONE named residual: the vacuum-normalized bulk transfer
eigenvalue-shift control `bulk_shift ≤ 1/12` carried by
`SpectralLocalizationCrux.SpectralLocalization` — equivalently, the discrete SU(2)
heat-kernel fusion LOCAL-CLT (the vacuum-normalized `p`-fold fusion eigenvalue
`bmc(s)/((s+1)·bmc(0))` matches the Gaussian to quadratic order uniformly in `s`).

This tranche re-expresses THAT SAME residual in the log / saddle form
(`SaddleLogForm`: leading exponent `A`, curvature-remainder modulus `eta`, and the
`estimate` `|log K̂ + A·C₂| ≤ eta·C₂²` on the EIGENVALUE form `fusionEig`) and WIRES
its Q'-level consequence — the eigenvalue-shift bound `bulkShiftBound` — into the
`SpectralLocalization` interface (`saddleToLocalization`) and thence into the
δ-loop capstone (`saddleBundle`, `saddle_gap_reduction`).  It does NOT close the
residual: `SaddleLogForm` is a NAMED, UNINHABITED analytic core (Rule 5).

# Why the estimate is on `fusionEig`, not `fusionKernelNorm`

`fusionKernelNorm = normSep = bmc(s)/bmc(0)` is the COEFFICIENT ratio (it carries the
multiplicity `dimQ s = s+1`).  The object the δ-loop bridge perturbs is the
EIGENVALUE `fusionEig = bmc(s)/((s+1)·bmc(0)) = fusionKernelNorm/dimQ s`
(multiplicity divided out; cf. `SpectralLocalizationCrux.eigA`).  The coefficient's
`log(s+1)` multiplicity term is not linearizable, so the saddle `estimate` MUST be
stated on `fusionEig` — the multiplicity-blind object, exactly as
`SpectralLocalizationCrux` requires.

# What is PROVED here (axiom-clean `Q'`/`Nat`)

  * `fusionKernelNorm` / `fusionEig` — the coefficient ratio and the (guarded)
    vacuum-normalized eigenvalue, with the denominator positivity `fusionEigDenom_pos`
    from `bmc(0) > 0`.
  * `FusionKernelLogConcave` + `fusionKernelLogConcave_p2` — the log-concavity
    (Pólya-frequency-2 / total-positivity) carrier; the `p = 2` face inhabited from
    the genuine box-level core `FusionConvLogConcaveCore` (via
    `FusionLogConcave.bmc2_logConcave_of_core`).  General `p` is named-open.
  * `fusionEig_p1_le_eigA`, `bmc_p1_zero_above` — the `p = 1` SATISFIABILITY: on the
    truncated modes `s ≤ N` the fusion eigenvalue EQUALS the heat kernel
    (`fusionEig ≤ eigA`), and above the cutoff `s > N` the `p = 1` coefficient
    VANISHES.  Together they INHABIT the wiring carrier at `p = 1`
    (`saddleLocalCLT_p1`) — the residual is genuinely satisfiable (`shift = 0`),
    exactly as `SpectralLocalizationCrux.trivialLocalization`.
  * `saddleToLocalization` / `saddleBundle` / `saddle_gap_reduction` — the WIRING:
    the eigenvalue-shift bound `bulkShiftBound` discharges
    `SpectralLocalization.bulk_shift`, feeding the δ-loop capstone
    `bond_moving_preserves_gap_reduction`.

# What is NAMED-OPEN (NOT inhabited, NOT faked)

  * `SaddleLogForm N w p` for the genuine 4D exponent `p ≥ 2` — the log/saddle form
    of the discrete fusion local-CLT (the `A`/`eta`/`estimate` mechanism).
  * `SaddleLocalCLT.bulkShiftBound` for `p ≥ 2` — the Q'-level eigenvalue-shift
    consequence of that estimate.  Both are the SAME single discrete SU(2) fusion
    local-CLT statement already named by `DeltaFrontierLedger.delta_frontier_ledger`,
    here re-expressed in log/saddle form.  `p = 1` inhabited; `p ≥ 2` open.

This is NOT a 4D Yang–Mills mass-gap proof; it is the log/saddle re-expression of the
one discrete-fusion residual, with the `p = 1` case inhabited and the wiring green.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the proved unit-fusion identity and its above-cutoff
vanishing, `divPos` monotonicity, and composition over the already-green δ-loop
engine.  Every load-bearing declaration is gated with `#print axioms` (permitted:
`propext` / `Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`, no
custom `axiom`.  All witnesses are `Type`-level data; the open core is a named
uninhabited interface.
-/

import YMGap.Continuum.DeltaFrontierLedger
import YMGap.Continuum.FusionLogConcave
import YMGap.Continuum.FusionQuotientCollapse
import YMGap.Constructive.CRealLog

namespace YMGap.Continuum.FusionKernelStatement

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.BulkModeCrux
open YMGap.Continuum.FusionQuotientCollapse

/-! ## 0. Positivity plumbing for the eigenvalue denominator -/

/-- `0 < dimQ s` (`dimQ s = s + 1`). -/
theorem dimQ_pos (s : Nat) : (0 : Q') < dimQ s := by
  show (0 : Q') < Q'.ofNat (s + 1)
  exact Q'.ofNat_succ_pos s

/-- The eigenvalue denominator `dimQ s · bmc(0)` is positive whenever the vacuum
coefficient is. -/
theorem fusionEigDenom_pos {N : Nat} {w : Q'} {p : Nat} (s : Nat)
    (h0 : (0 : Q') < bondMovedCoeff N w p 0) :
    (0 : Q') < dimQ s * bondMovedCoeff N w p 0 :=
  Q'.mul_pos (dimQ_pos s) h0

/-! ## 1. Deliverable (1): `K_{w,p}` and the eigenvalue form -/

/-- **`K_{w,p}(s) = fusionKernelNorm` — the vacuum-normalized `p`-fold fusion
COEFFICIENT ratio** `bmc(s)/bmc(0)` (carries the multiplicity `dimQ s`).  Thin alias
of `S1Dominance.normSep`. -/
def fusionKernelNorm (N : Nat) (w : Q') (p : Nat)
    (h0 : (0 : Q') < bondMovedCoeff N w p 0) (s : Nat) : Q' :=
  S1Dominance.normSep N w p h0 s

/-- `fusionKernelNorm` at `s = 1` is the bond-moved gap separator `sepBM`. -/
theorem fusionKernelNorm_one_eq_sepBM (N : Nat) (w : Q') (p : Nat)
    (h0 : (0 : Q') < bondMovedCoeff N w p 0) :
    fusionKernelNorm N w p h0 1 = sepBM N w p h0 := rfl

/-- **`fusionEig` — the vacuum-normalized EIGENVALUE** `bmc(s)/((s+1)·bmc(0))`
(multiplicity `dimQ s` divided out).  This is the object the δ-loop bridge perturbs
(`= fusionKernelNorm / dimQ s`; the `s = 0` vacuum is `1`). -/
def fusionEig (N : Nat) (w : Q') (p : Nat) (s : Nat)
    (h0' : (0 : Q') < dimQ s * bondMovedCoeff N w p 0) : Q' :=
  Q'.divPos (bondMovedCoeff N w p s) (dimQ s * bondMovedCoeff N w p 0) h0'

/-! ## 2. Deliverable (2): log-concavity / total positivity (reuse; general-`p` open) -/

/-- **General-`p` log-concavity (PF₂) of the `p`-fold fusion tower.**  The carrier for
"the excited fusion coefficients are maximized at a low mode".  `p = 2` inhabited
from the genuine box core (`fusionKernelLogConcave_p2`); `p ≥ 3` named-open.  NOTE:
"fusion preserves log-concavity" is FALSE in general
(`SelfFusionLogConcave.boxSum1_logConcave_FALSE_at_one`) — this carries the
heat-kernel-specific content, not a generic convolution-closure claim. -/
structure FusionKernelLogConcave (N : Nat) (w : Q') (p : Nat) : Type where
  /-- The PF₂ / log-concavity datum of the `p`-fold bond-moved tower. -/
  lc : FusionLogConcave.LogConcave (bondMovedCoeff N w p)

/-- **`p = 2` log-concavity from the genuine box core.**  Given a
`FusionConvLogConcaveCore N w` witness (heat-kernel-specific box log-concavity — NOT
a generic convolution claim), the `p = 2` fusion tower is log-concave. -/
def fusionKernelLogConcave_p2 {N : Nat} {w : Q'} {hw0 : (0 : Q') ≤ w} {hw1 : w ≤ (1 : Q')}
    (core : SelfFusionLogConcave.FusionConvLogConcaveCore N w hw0 hw1) :
    FusionKernelLogConcave N w 2 :=
  ⟨FusionLogConcave.bmc2_logConcave_of_core core⟩

/-! ## 3. Deliverable (3a): the LOG / SADDLE form — the named-open analytic core

The honest re-expression of the discrete-fusion residual in log / saddle form.  A_p,
eta_p are DATA (leading exponent / curvature-remainder modulus).  The `estimate` is
the saddle bound `|log(fusionEig s) + A·C₂(s)| ≤ eta·C₂(s)²`, `C₂(s) = c4 s = s(s+2)`,
stated on the EIGENVALUE form (multiplicity divided out).  NAMED-OPEN for `p ≥ 2`:
this structure is NOT inhabited here and NOT faked. -/

/-- **`SaddleLogForm` — the discrete SU(2) fusion local-CLT in LOG / SADDLE form.**
The leading exponent `A` (expected `−log w`, the Gaussian rate `(1−w)/p`), the
curvature/remainder modulus `eta`, the range-reduction plumbing `red` so `CReal.log`
is defined on each eigenvalue, and the saddle `estimate` on `fusionEig`.  This is the
honest mechanism record for the residual; it is NAMED-OPEN (uninhabited) for the
genuine 4D exponent `p ≥ 2`. -/
structure SaddleLogForm (N : Nat) (w : Q') (p : Nat)
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0) : Type where
  /-- `A_p(w)` — leading exponent (expected `−log w`). -/
  A : Q'
  /-- `eta_p(w)` — curvature / remainder modulus. -/
  eta : Q'
  /-- Range-reduction plumbing so `CReal.log` is defined on each eigenvalue. -/
  red : (s : Nat) → CRealLogRangeReduction (CReal.ofQ' (fusionEig N w p s (h0' s)))
  /-- **THE SADDLE ESTIMATE (log form, `CReal`)**:
      `|log(fusionEig s) + A·C₂(s)| ≤ eta·C₂(s)²`, `C₂(s) = c4 s = s(s+2)`.
      On the EIGENVALUE form (the coefficient's `log(s+1)` term is not linearizable). -/
  estimate : ∀ s, CReal.leEv
    (CReal.abs (CReal.add
      (CReal.log (CReal.ofQ' (fusionEig N w p s (h0' s))) (red s))
      (CReal.ofQ' (A * Q'.ofNat (c4 s)))))
    (CReal.ofQ' (eta * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))))

/-! ## 3b. Deliverable (3b): the Q'-level wiring carrier and THE named residual

The load-bearing Q'-level consequence of the saddle estimate: the vacuum-normalized
eigenvalue-shift stays below the localization margin `1/12`.  This is the field the
wiring discharges into `SpectralLocalization.bulk_shift`. -/

/-- **`SaddleLocalCLT` — the Q'-level wiring carrier.**  Carries the saddle moduli
`A`, `eta` (data) and THE LOAD-BEARING NAMED RESIDUAL `bulkShiftBound`: the
vacuum-normalized eigenvalue-shift `fusionEig s − eigA w s` is below the localization
margin `1/12` for every mode.  This is the exp'd consequence of `SaddleLogForm.estimate`
(the `eta·C₂²` remainder under the bulk margin) — the SAME single discrete SU(2)
fusion local-CLT residual as `DeltaFrontierLedger.delta_frontier_ledger`.  `p = 1`
inhabited (`saddleLocalCLT_p1`); `p ≥ 2` named-open.

⚠ **SUPERSEDED for `p ≥ 2`.** The `bulkShiftBound` field below compares `fusionEig`
to the BARE `p = 1` heat rate `eigA w s`, which the pilot (`computations/core_b_pilot.py`)
proved is FALSE for every `p ≥ 2` (the reference rate must be re-based to the aggregate
`w_eff ≈ exp(−A_p)`).  Do NOT attempt to inhabit `bulkShiftBound` for `p ≥ 2` — it is
unsatisfiable as stated.  The CORRECTED, satisfiable carrier is
`Continuum.RebasedBulkShift.RebasedLocalCLT` (`rebasedBulkShift`, off `rateP w_eff`),
whose `p ≥ 2` obligation is the single `ExpShiftBridge`.  This structure is retained only
for the `p = 1` anchor and the historical wiring shape. -/
structure SaddleLocalCLT (N : Nat) (w : Q') (p : Nat)
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0) : Type where
  /-- `A_p(w)` — leading exponent (data). -/
  A : Q'
  /-- `eta_p(w)` — curvature / remainder modulus (data). -/
  eta : Q'
  /-- **THE LOAD-BEARING OPEN FIELD** — the vacuum-normalized eigenvalue-shift stays
  below the localization margin: `fusionEig s − eigA w s ≤ 1/12` for every mode.
  Discharges `SpectralLocalization.bulk_shift`.
  ⚠ KNOWN-FALSE for `p ≥ 2` (bare `p = 1` rate `eigA`); use
  `RebasedBulkShift.RebasedLocalCLT.rebasedBulkShift` instead. -/
  bulkShiftBound : ∀ s, fusionEig N w p s (h0' s) - eigA w s ≤ q112

/-! ## 4. Deliverable (4): the wiring into the δ-loop capstone -/

/-- **`saddleToLocalization` — SaddleLocalCLT ⟹ SpectralLocalization.**  The perturbed
spectrum is `fusionEig`, the per-mode shift is `fusionEig − eigA`, the perturbation
bound `pert` is a definitional rearrangement, and `bulk_shift` is discharged directly
from `bulkShiftBound`. -/
def saddleToLocalization {N : Nat} {w : Q'} {p : Nat}
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0)
    (E : SaddleLocalCLT N w p h0') (hnc : (1 : Q') - w ≤ q112) :
    SpectralLocalization w where
  eig' := fun s => fusionEig N w p s (h0' s)
  shift := fun s => fusionEig N w p s (h0' s) - eigA w s
  hnc := hnc
  pert := fun s => by
    -- eig' s ≤ eigA w s + (fusionEig s − eigA w s), by the rearrangement a+(f−a) ≃ f.
    have hre :
        (eigA w s + (fusionEig N w p s (h0' s) - eigA w s)).eqv
          (fusionEig N w p s (h0' s)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (eigA w s) _ _
          (Q'.add_comm_eqv (fusionEig N w p s (h0' s)) (-(eigA w s)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv (eigA w s) (-(eigA w s))
          (fusionEig N w p s (h0' s)))) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ (fusionEig N w p s (h0' s))
          (Q'.add_neg_self_eqv (eigA w s))) ?_
      exact Q'.eqv_of_eq (Q'.zero_add' (fusionEig N w p s (h0' s)))
    exact Q'.ge_of_eqv hre
  bulk_shift := E.bulkShiftBound

/-- **`saddleBundle` — feed the produced localization as the δ-loop bundle's
`bulkCtrl`.**  From a `SaddleLocalCLT` (and the window data) build the end-to-end
`BondMovingGapPreservation`. -/
def saddleBundle {N : Nat} {w : Q'} {p : Nat}
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0)
    (E : SaddleLocalCLT N w p h0')
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hN : 1 ≤ N) (hp : 0 < p)
    (hnc : (1 : Q') - w ≤ q112) :
    DeltaFrontierLedger.BondMovingGapPreservation N w p where
  hw0 := hw0
  hw1 := hw1
  hN := hN
  hp := hp
  bulkCtrl := saddleToLocalization h0' E hnc

/-- **`saddle_gap_reduction` — the δ-loop capstone FIRES off the saddle carrier.**
Given a `SaddleLocalCLT`, the full δ-loop `GapReductionConclusion` holds for the
bond-moved bulk spectrum `fusionEig`.  Composition over
`DeltaFrontierLedger.bond_moving_preserves_gap_reduction`. -/
theorem saddle_gap_reduction {N : Nat} {w : Q'} {p : Nat}
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w p 0)
    (E : SaddleLocalCLT N w p h0')
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (hN : 1 ≤ N) (hp : 0 < p)
    (hnc : (1 : Q') - w ≤ q112) :
    DeltaFrontierLedger.GapReductionConclusion N w p
      (saddleToLocalization h0' E hnc).eig' :=
  DeltaFrontierLedger.bond_moving_preserves_gap_reduction
    (saddleBundle h0' E hw0 hw1 hN hp hnc)

/-! ## 5. The `p = 1` SATISFIABILITY — the residual is genuinely inhabited

Per the SZZ-surrogate lesson (verify a named obligation is satisfiable before building
on it): at `p = 1` the fusion eigenvalue coincides with the bare heat kernel, so the
shift is `0`, well inside the margin.  We prove the two facts and inhabit
`SaddleLocalCLT N w 1` unconditionally in `s`. -/

/-- **`fusionEig_p1_le_eigA` — at `p = 1`, on the truncated modes `s ≤ N` the fusion
eigenvalue does NOT exceed the heat kernel** `fusionEig ≤ eigA`.  (In fact they are
equal: `bmc(s) ≃ coeffW w s = dimQ s · w^{C₄(s)}`, `bmc(0) ≃ 1`, so the `dimQ s`
cancels.) -/
theorem fusionEig_p1_le_eigA {N : Nat} {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) (haN : s ≤ N)
    (h0' : (0 : Q') < dimQ s * bondMovedCoeff N w 1 0) :
    fusionEig N w 1 s h0' ≤ eigA w s := by
  -- bmc(s) ≃ coeffW w s
  have e_s : (bondMovedCoeff N w 1 s).eqv (coeffW w s) := fusionPow_one_eq haN
  -- bmc(0) ≃ 1
  have e_0 : (bondMovedCoeff N w 1 0).eqv (1 : Q') :=
    Q'.eqv_trans _ _ _ (fusionPow_one_eq (Nat.zero_le N)) (Q'.eqv_of_eq (coeffW_zero w))
  -- dimQ s · bmc(0) ≃ dimQ s
  have hA : (dimQ s * bondMovedCoeff N w 1 0).eqv (dimQ s) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (dimQ s) _ _ e_0) (Q'.mul_one_eqv (dimQ s))
  -- eigA w s · (dimQ s · bmc(0)) ≃ eigA w s · dimQ s ≃ dimQ s · eigA w s = coeffW w s
  have hRHS :
      (eigA w s * (dimQ s * bondMovedCoeff N w 1 0)).eqv (coeffW w s) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (eigA w s) _ _ hA)
      (Q'.mul_comm_eqv (eigA w s) (dimQ s))
  -- bmc(s) ≤ eigA w s · (dimQ s · bmc(0))
  have hle : bondMovedCoeff N w 1 s ≤ eigA w s * (dimQ s * bondMovedCoeff N w 1 0) :=
    Q'.le_of_eqv (Q'.eqv_trans _ _ _ e_s (Q'.eqv_symm hRHS))
  exact Q'.divPos_le_of_le_mul _ _ h0' hle

/-- **`bmc_p1_zero_above` — at `p = 1`, above the cutoff the coefficient vanishes**:
`bondMovedCoeff N w 1 s ≃ 0` for `N < s`.  (Only `d₁ = 0` survives the outer fusion
unit; then `fusionInd 0 d₂ s = δ_{d₂,s}` needs `d₂ = s > N`, absent from the truncated
inner range.) -/
theorem bmc_p1_zero_above {N : Nat} {w : Q'} {s : Nat} (hlt : N < s) :
    (bondMovedCoeff N w 1 s).eqv 0 := by
  show (fsum (fun d₁ => fsum (fun d₂ =>
      fusionInd d₁ d₂ s * (fusionUnit d₁ * coeffW w d₂)) (N + 1)) (N + 1)).eqv 0
  refine fsum_zero_below (N + 1) (fun d₁ _ => ?_)
  refine fsum_zero_below (N + 1) (fun d₂ hd₂ => ?_)
  by_cases hd0 : d₁ = 0
  · subst hd0
    have hind : fusionInd 0 d₂ s = (0 : Q') :=
      fusionInd_zero_left_ne d₂ s (by omega)
    rw [hind]
    exact Q'.zero_mul_eqv _
  · have hunit : fusionUnit d₁ = (0 : Q') := by
      unfold fusionUnit
      have hb : (d₁ == 0) = false := by
        cases d₁ with
        | zero => exact absurd rfl hd0
        | succ k => rfl
      rw [hb]; rfl
    rw [hunit]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left _ _ 0 (Q'.zero_mul_eqv (coeffW w d₂))) ?_
    exact Q'.mul_zero_eqv _

/-- **`saddleLocalCLT_p1` — the `p = 1` INHABITANT of the wiring carrier.**  The
heat-kernel input (`p = 1`) inhabits `SaddleLocalCLT` unconditionally in `s`: on
`s ≤ N` the shift is `0` (`fusionEig = eigA`), and on `s > N` the coefficient
vanishes so `fusionEig ≃ 0 ≤ eigA`; either way `fusionEig − eigA ≤ 0 ≤ 1/12`.  So the
residual `bulkShiftBound` is genuinely satisfiable (`A = eta = 0`, the unperturbed
Gaussian rate placeholder). -/
def saddleLocalCLT_p1 {N : Nat} {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N w 1 0) :
    SaddleLocalCLT N w 1 h0' where
  A := 0
  eta := 0
  bulkShiftBound := fun s => by
    -- fusionEig s ≤ eigA w s
    have hle : fusionEig N w 1 s (h0' s) ≤ eigA w s := by
      by_cases hsN : s ≤ N
      · exact fusionEig_p1_le_eigA hw0 hw1 s hsN (h0' s)
      · have hlt : N < s := by omega
        have hz : (bondMovedCoeff N w 1 s).eqv 0 := bmc_p1_zero_above hlt
        have hrhs_nn : (0 : Q') ≤ eigA w s * (dimQ s * bondMovedCoeff N w 1 0) :=
          Q'.mul_nonneg _ _ (eigA_nonneg hw0 s) (Q'.le_of_lt (h0' s))
        have hle2 : bondMovedCoeff N w 1 s
            ≤ eigA w s * (dimQ s * bondMovedCoeff N w 1 0) :=
          Q'.le_trans' _ _ _ (Q'.le_of_eqv hz) hrhs_nn
        exact Q'.divPos_le_of_le_mul _ _ (h0' s) hle2
    -- fusionEig s − eigA w s ≤ 0 ≤ 1/12
    have hstep : fusionEig N w 1 s (h0' s) + -(eigA w s) ≤ (eigA w s) + -(eigA w s) :=
      qadd_le_add hle (Q'.le_refl' (-(eigA w s)))
    have hzero : (eigA w s + -(eigA w s)) ≤ (0 : Q') :=
      Q'.le_of_eqv (Q'.add_neg_self_eqv (eigA w s))
    exact Q'.le_trans' _ _ _ hstep
      (Q'.le_trans' _ _ _ hzero (by decide : (0 : Q') ≤ q112))

/-- **The `p = 1` capstone fires** on the demo weight `w = 95/96`
(`1 − w = 1/96 ≤ 1/12`): the heat-kernel input satisfies the full δ-loop
`GapReductionConclusion` through the saddle carrier, with NO open hypothesis. -/
theorem saddleLocalCLT_p1_capstone (N : Nat) (hN : 1 ≤ N)
    (h0' : ∀ s, (0 : Q') < dimQ s * bondMovedCoeff N SpectralLocalizationCrux.demoW 1 0) :
    DeltaFrontierLedger.GapReductionConclusion N SpectralLocalizationCrux.demoW 1
      (saddleToLocalization h0'
        (saddleLocalCLT_p1 SpectralLocalizationCrux.demoW_pos
          SpectralLocalizationCrux.demoW_le_one h0') SpectralLocalizationCrux.demoW_nc).eig' :=
  saddle_gap_reduction h0'
    (saddleLocalCLT_p1 SpectralLocalizationCrux.demoW_pos
      SpectralLocalizationCrux.demoW_le_one h0')
    SpectralLocalizationCrux.demoW_pos SpectralLocalizationCrux.demoW_le_one hN (by decide)
    SpectralLocalizationCrux.demoW_nc

end YMGap.Continuum.FusionKernelStatement

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionKernelStatement.fusionKernelNorm_one_eq_sepBM
#print axioms YMGap.Continuum.FusionKernelStatement.fusionEigDenom_pos
#print axioms YMGap.Continuum.FusionKernelStatement.fusionKernelLogConcave_p2
#print axioms YMGap.Continuum.FusionKernelStatement.saddleToLocalization
#print axioms YMGap.Continuum.FusionKernelStatement.saddleBundle
#print axioms YMGap.Continuum.FusionKernelStatement.saddle_gap_reduction
#print axioms YMGap.Continuum.FusionKernelStatement.fusionEig_p1_le_eigA
#print axioms YMGap.Continuum.FusionKernelStatement.bmc_p1_zero_above
#print axioms YMGap.Continuum.FusionKernelStatement.saddleLocalCLT_p1
#print axioms YMGap.Continuum.FusionKernelStatement.saddleLocalCLT_p1_capstone
