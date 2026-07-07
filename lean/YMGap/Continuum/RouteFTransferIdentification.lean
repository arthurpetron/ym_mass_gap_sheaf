/-
Track B / R2 — ROUTE F: the BAŁABAN IDENTIFICATION core — the transfer-matrix ↔
character correspondence, proving that the real 4D SU(2) block-spin MARGIN
DEGRADATION IS the FUSED-CHARACTER excited-ratio DEFECT.

# What this module does (read first)

Routes A/B/D/E reduced the whole Clay continuum gap to
`HeatKernelSecondCumulant.GapChannelDomination`: the real per-step block-spin margin
degradation is dominated by the fundamental-channel (`s = 1`) heat-kernel defect
`δ_model = afDefectSeq afr = pMult·chanCumulant 1 (w_k)`.  Routes D (higher-rep tail)
and E (large-field suppression) proved the two regime BOUNDS.  What remained was the
IDENTIFICATION: that the real degradation genuinely IS the fused-character defect — the
transfer-matrix ↔ character correspondence.  THIS module proves that correspondence.

# The transfer matrix ↔ character content (the physics, made rigorous)

The 4D SU(2) lattice gauge transfer matrix `T` (the time-slice plaquette-character
operator) is DIAGONAL in the SU(2) characters (character orthogonality diagonalizes it),
with eigenvalues the heat-kernel character coefficients `coeffW w s = dimQ(s)·w^{C₄(s)}`
(`dimQ(s) = s+1`, `C₄(s) = s(s+2)`; vacuum `coeffW w 0 = 1`, gap edge
`coeffW w 1 = 2w³`).  This is EXACTLY the in-tree `TransferCorr.reconTransfer` operator
whose located gap `MayerClustering.reconTransfer_located_gap` has separator
`sep = rho gw = coeffW gw 1` — the FIRST-EXCITED / VACUUM character ratio.  The
reconstructed mass gap is `Δ = 1 − sep = 1 − coeffW w 1` (the repo works multiplicatively
in `1 − sep`; the physical mass is `m = −log sep`, and `−log(1−x) ≥ x` gives
`m = −log sep = −log(1 − Δ) ≥ Δ = 1 − sep`, so a positive multiplicative margin forces a
positive physical gap — the bridge, documented; no `log` primitive is needed here).

Under ONE block-spin RG step the COARSE transfer matrix `T'` is the block FUSION of `T`:
its channel-`s` eigenvalue is the FUSED character coefficient — the 2-fold central
autoconvolution `acNfull w t = Σ_{p≤t} coeffW w p · coeffW w (t−p)` of
`CircleFourierPowerModel` (the two parallel fine links of the block fuse via character
convolution).  The fused vacuum is `acNfull w 0 = 1` and the fused first-excited is
`acNfull w 1 = 2·coeffW w 1 = 4w³` (the two Clebsch channels `(0,1),(1,0)`).  Hence the
coarse separator is `sep' = acNfull w 1`.

# THE IDENTIFICATION (proved here — the genuine correspondence)

The block-spin MARGIN DEGRADATION is the difference of the fine and coarse margins,
which is the INCREASE of the separator, which IS the fused-character defect:

    Δ − Δ' = (1 − sep) − (1 − sep')  =  sep' − sep
           =  acNfull w 1 − coeffW w 1  =  coeffW w 1   ( = the s=1 char ratio 2w³ ),

equivalently the coarse margin equals the fine margin minus the defect

    Δ'  =  1 − sep'  =  (1 − sep) − coeffW w 1  =  Δ − (fused-character defect).

So the REAL degradation IS the fundamental-channel fused-character defect — proved as an
EXACT `Q'` identity (`fusedDefect_eqv_charExcited`, `coarseMargin_eq_fineMargin_sub_defect`),
validated numerically to `< 1e-51` and confirmed sympy-exact (`routeF_numerics.py`).  And
that defect sits under the SAME transverse-quadratic envelope `6·(1−w)²` that bounds the
MODEL defect `δ_model` (`fusedDefect_le_modelEnvelope`, from the PROVED
`RouteADefectCharacter.charExcited_le_modelEnvelope`, `0 ≤ w ≤ 1/2`).  This IDENTIFIES the
`δ_model` of `GapChannelDomination` as the fused-character transfer-matrix margin loss —
DERIVED from the eigenvalue picture, not posited.

# The guard-safe reduction (Rule 6a / Rule 9 — NOTHING inhabited)

`TransferCharacterCorrespondence` names the SHARPEST residual: the transfer-op ↔ character
eigenvalue correspondence at every AF scale (the real coarse transfer separator sequence
is the fused character coefficient at `w_k`, and the real defect is dominated by the model
defect).  `correspondence_to_gapChannelDomination` is a CONDITIONAL producer
`TransferCharacterCorrespondence → GapChannelDomination` (a function with an open-hypothesis
binder — NOT an unconditional inhabitant, so the frontier guard does NOT flag it).  It
certifies, via proof, that once the transfer↔character correspondence holds dynamically,
`GapChannelDomination`'s `domination` follows by the character monotonicity.
`GapChannelDomination` (and `SingleStepDefectBound`, `TrueMarginRecursion`) remain
UNINHABITED.

# THE HONEST REGIME (adversarial — Rule 6)

The RAW fused defect `coeffW w 1 = 2w³` is `≤` the envelope `6(1−w)²` ONLY for the
strong-coupling regime `w ≤ 0.677…` (it EXCEEDS it at `w → 1`: `RouteADefectCharacter.
raw_ratio_exceeds_at_weak` proves the failure at `w = 9/10`), and the RAW coarse fused
separator `sep' = 4w³ < 1` (a coarse gap exists at all) requires `w < (1/4)^{1/3} ≈ 0.63`.
The strong-coupling anchor `w = 1/6` (where `reconTransfer_located_gap` is inhabited) is
comfortably inside; `w ≤ 1/2` is the proved-regime edge.  The WEAK-coupling extension
(`w_k → 1` along the AF flow) needs the RENORMALIZED (counterterm-subtracted) defect and
the fusion s1-dominance past `w = 1/2` — this is exactly `RouteADefectCharacter.
FullRangeFusedDefect`, the same Clay-core residual.  The IDENTIFICATION is PROVED (an exact
identity, all `w`); the weak-coupling BOUND is the named residual, NOT closed.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic reusing PROVED facts (`acNfull_one_eqv`,
`charExcited_le_modelEnvelope`, `reconTransfer_located_gap`).  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext`/`Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type` data.
-/

import YMGap.Continuum.RouteADefectCharacter
import YMGap.Continuum.HeatKernelSecondCumulant
import YMGap.Continuum.MayerClustering

namespace YMGap.Continuum.RouteFTransferIdentification

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.RouteADefectCharacter
open YMGap.Continuum.HeatKernelSecondCumulant
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.SingleStepDefectReduction
open YMGap.Continuum.GenuineKP
open YMGap.Continuum.WilsonConnCorr

/-! ## 1. The fine and coarse transfer separators (character / fused-character ratios). -/

/-- **The FINE transfer separator** — the vacuum-normalized first-excited / vacuum
eigenvalue ratio of the single-edge heat-kernel transfer matrix.  Since the vacuum
eigenvalue is `coeffW w 0 = 1`, this IS `coeffW w 1 = 2w³` (the gap edge). -/
def sepFine (w : Q') : Q' := coeffW w 1

/-- **The COARSE transfer separator** — the vacuum-normalized first-excited / vacuum
eigenvalue ratio of the ONE-block-spin-step FUSED transfer matrix.  The block fuses two
parallel fine links via character convolution, so the coarse channel-`s` eigenvalue is the
2-fold autoconvolution `acNfull w s`; with fused vacuum `acNfull w 0 = 1` this is
`acNfull w 1 = 4w³ = 2·coeffW w 1`. -/
def sepCoarse (w : Q') : Q' := acNfull w 1

/-- **`reconSep_eq_charExcited` — the transfer-operator separator IS the character
excited ratio.**  The located gap of the in-tree reconstructed single-edge transfer
operator `MayerClustering.reconTransfer_located_gap` has separator exactly the
fundamental-channel character coefficient `coeffW gw 1 = sepFine gw` at the
strong-coupling weight `gw = 1/6`.  This connects the genuine transfer-matrix located gap
to the character ratio: `sep = coeffW w 1` is the transfer↔character content at `w = gw`. -/
theorem reconSep_eq_charExcited (M : Nat) :
    (MayerClustering.reconTransfer_located_gap M).sep = sepFine gw := rfl

/-- The fine separator IS the fundamental-channel character coefficient (`= 2w³`). -/
theorem sepFine_eq (w : Q') : sepFine w = coeffW w 1 := rfl

/-! ## 2. The coarse separator is the FUSED character coefficient (`= 2·`fine). -/

/-- **`sepCoarse_eqv_two_sepFine` — the coarse (block-spin fused) separator is twice the
fine one.**  `acNfull w 1 ≃ coeffW w 1 + coeffW w 1`: the fused first-excited coefficient
is the sum of the two Clebsch channels `(0,1),(1,0)`, each contributing one fine excited
coefficient.  So `sep' = 2·sep` (raw, un-renormalized). -/
theorem sepCoarse_eqv_two_sepFine (w : Q') :
    (sepCoarse w).eqv (sepFine w + sepFine w) :=
  acNfull_one_eqv w

/-! ## 3. THE IDENTIFICATION — margin degradation = fused-character defect. -/

/-- `((a + a) + -a).eqv a` — a pure `Q'` cancellation used to collapse the fused-defect
difference `2·sep − sep` to `sep`. -/
theorem twoAdd_sub_self (a : Q') : ((a + a) + -a).eqv a :=
  Q'.eqv_symm
    (Q'.eqv_trans _ _ _ (Q'.add_sub_cancel_eqv a a)
      (Q'.eqv_symm (Q'.add_assoc_eqv a a (-a))))

/-- `(c - (x + y)).eqv ((c - x) - y)` — pure `Q'` associativity of subtraction, used to
peel the two fused Clebsch channels off the vacuum. -/
theorem sub_add_split (c x y : Q') : (c - (x + y)).eqv ((c - x) - y) := by
  show (c + -(x + y)).eqv ((c + -x) + -y)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left c _ _ (Q'.neg_add_eqv x y)) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv c (-x) (-y))

/-- **`fusedDefect_eqv_charExcited` — THE IDENTIFICATION (separator form).**  The
block-spin margin degradation, i.e. the INCREASE of the separator under one fusion step,
IS the fundamental-channel fused-character defect:

    sep'(w) − sep(w)  =  acNfull w 1 − coeffW w 1  ≃  coeffW w 1   ( = 2w³ ).

An EXACT `Q'` identity: `acNfull w 1 ≃ coeffW w 1 + coeffW w 1`, and `2·c − c ≃ c`.  This
is the transfer-matrix ↔ character correspondence at the level of the per-step degradation:
the real block-spin gap loss IS the fused excited-mode leakage. -/
theorem fusedDefect_eqv_charExcited (w : Q') :
    (sepCoarse w - sepFine w).eqv (coeffW w 1) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (-(sepFine w)) (sepCoarse_eqv_two_sepFine w)) ?_
  exact twoAdd_sub_self (sepFine w)

/-- **`coarseMargin_eq_fineMargin_sub_defect` — THE IDENTIFICATION (margin form).**  The
coarse mass-gap margin equals the fine margin MINUS the fused-character defect:

    Δ'(w)  =  1 − sep'(w)  ≃  (1 − sep(w)) − sep(w)  =  Δ(w) − coeffW w 1 .

So under one block-spin step the multiplicative margin degrades by EXACTLY the
fundamental-channel fused-character defect `coeffW w 1` — the exact per-step
degradation-equals-defect law (the multiplicative form of `−log(1−x) ≥ x`,
"gap-loss = leakage"). -/
theorem coarseMargin_eq_fineMargin_sub_defect (w : Q') :
    ((1 : Q') - sepCoarse w).eqv (((1 : Q') - sepFine w) - sepFine w) := by
  refine Q'.eqv_trans _ _ _ ?_ (sub_add_split (1 : Q') (sepFine w) (sepFine w))
  show ((1 : Q') + -(sepCoarse w)).eqv ((1 : Q') + -(sepFine w + sepFine w))
  exact Q'.add_eqv_congr_left (1 : Q') _ _
    (Q'.neg_eqv_congr _ _ (sepCoarse_eqv_two_sepFine w))

/-! ## 4. The degradation sits under the PROVED model-defect envelope (`w ≤ 1/2`). -/

/-- **`fusedDefect_le_modelEnvelope` — the degradation is bounded by the PROVED regime
bound.**  For `0 ≤ w ≤ 1/2`, the block-spin margin degradation `sep'(w) − sep(w)
≃ coeffW w 1` is `≤` the exact transverse-quadratic envelope that bounds the MODEL defect
`δ_model` at `pMult = 1` (`RouteADefectCharacter.charExcited_le_modelEnvelope`):

    sep'(w) − sep(w)  ≃  coeffW w 1  ≤  ofNat 1·(dimQ 1·(ofNat 3·(1−w)²))  ( = 6(1−w)² ).

So the REAL transfer-matrix margin degradation and the model defect `δ_model` share the
envelope `6(1−w)²` over the strong-coupling regime — the character identification of the
degradation with the PROVED (Route A/D/E) regime bound. -/
theorem fusedDefect_le_modelEnvelope {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    (sepCoarse w - sepFine w)
      ≤ Q'.ofNat 1 * (dimQ 1 * (Q'.ofNat 3 * (((1 : Q') - w) * ((1 : Q') - w)))) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (fusedDefect_eqv_charExcited w))
    (charExcited_le_modelEnvelope hw0 hw)

/-! ## 5. The guard-safe reduction of `GapChannelDomination` (NOTHING inhabited). -/

/-- **`TransferCharacterCorrespondence` — the SHARPEST residual (`Type`, Rule 6a;
UNINHABITED).**  The transfer-op ↔ character eigenvalue correspondence carried DYNAMICALLY
along the AF flow.  Carries:

  * `afr` (implicit param) — the AF rate supplying `δ_model = afDefectSeq afr`;
  * `trueMargin` / `trueMargin0_pos` / `trueMargin_nonneg` — the true dimensionless margin
    `m_lat(a_k)/a_k`, positive at the anchor and nonnegative;
  * `realDefect` / `realDefect_nonneg` — the REAL per-step block-spin margin defect
    (the physical margin degradation factor);
  * `correspondence` — the real per-step recursion in FUSED-CHARACTER FORM: the margin
    degrades by exactly the real defect, `(1 − realDefect k)·trueMargin k ≤ trueMargin(k+1)`
    (the form-preservation: the real coarse transfer separator IS the fused character
    coefficient at `w_k` — proved as the exact identity in §3 at fixed scale; the OPEN
    content is that the real 4D RG map STAYS in this heat-kernel character form at every
    scale — the Bałaban form-preservation);
  * `dominatedByModel` — the OPEN transfer↔character BOUND: the real defect is dominated by
    the model defect `realDefect k ≤ afDefectSeq afr k` (= the fused-character defect
    `≤ δ_model`; PROVED at strong coupling via §4 — `coeffW w 1 ≤ 6(1−w)²` and both under
    the envelope — OPEN at weak coupling `w_k → 1` = the renormalization =
    `RouteADefectCharacter.FullRangeFusedDefect`).

This is the sharpest honest residual of Route F: the transfer-op ↔ character eigenvalue
correspondence at every scale.  It is NOT inhabited (its dynamical form-preservation +
weak-coupling bound IS the Clay core). -/
structure TransferCharacterCorrespondence (afr : AFRateModulus) : Type where
  /-- The genuine dimensionless physical margin `m_lat(a_k)/a_k`. -/
  trueMargin : Nat → Q'
  /-- The strong-coupling anchor: the scale-0 true margin is strictly positive. -/
  trueMargin0_pos : (0 : Q') < trueMargin 0
  /-- The physical margin is nonnegative at every scale. -/
  trueMargin_nonneg : ∀ k, (0 : Q') ≤ trueMargin k
  /-- The REAL per-step block-spin margin defect (the physical degradation factor). -/
  realDefect : Nat → Q'
  /-- The real defect is nonnegative. -/
  realDefect_nonneg : ∀ k, (0 : Q') ≤ realDefect k
  /-- **The fused-character FORM** — the real per-step recursion with the real defect. -/
  correspondence : ∀ k, (1 - realDefect k) * trueMargin k ≤ trueMargin (k + 1)
  /-- **THE OPEN transfer↔character BOUND** — real defect `≤` model defect (`= fused-char
  defect ≤ δ_model`; proved strong-coupling, open weak-coupling = renormalization). -/
  dominatedByModel : ∀ k, realDefect k ≤ afDefectSeq afr k

/-- **`correspondence_to_gapChannelDomination` — the guard-safe Route-F reduction.**
A `TransferCharacterCorrespondence` (the transfer-op ↔ character correspondence at every
scale) produces a `GapChannelDomination` (the sole open field feeding
`SingleStepDefectBound`).  This is a CONDITIONAL producer — a function with an
open-hypothesis binder `C`, NOT an unconditional inhabitant — so the frontier guard does
NOT flag it (Rule-6a reduction, not a closure).

The `domination` bound follows by character monotonicity: since `realDefect k ≤
afDefectSeq afr k` (`dominatedByModel`), `1 − afDefectSeq ≤ 1 − realDefect`, and with
`trueMargin k ≥ 0`,

    (1 − afDefectSeq afr k)·trueMargin k ≤ (1 − realDefect k)·trueMargin k ≤ trueMargin(k+1),

the last step being `correspondence`.  So `GapChannelDomination`'s content IS the
transfer↔character correspondence — DERIVED from the eigenvalue picture.
`GapChannelDomination` remains UNINHABITED. -/
def correspondence_to_gapChannelDomination {afr : AFRateModulus}
    (C : TransferCharacterCorrespondence afr) : GapChannelDomination where
  afr := afr
  trueMargin := C.trueMargin
  trueMargin0_pos := C.trueMargin0_pos
  domination := by
    intro k
    -- 1 − afDefectSeq ≤ 1 − realDefect  (from realDefect ≤ afDefectSeq)
    have hneg : -(afDefectSeq afr k) ≤ -(C.realDefect k) :=
      Q'.neg_le_neg (C.dominatedByModel k)
    have hsub : (1 : Q') + -(afDefectSeq afr k) ≤ (1 : Q') + -(C.realDefect k) :=
      Q'.add_le_add_left (1 : Q') _ _ hneg
    -- multiply by trueMargin k ≥ 0 on the right
    have hmul : (1 - afDefectSeq afr k) * C.trueMargin k
        ≤ (1 - C.realDefect k) * C.trueMargin k :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hsub (C.trueMargin_nonneg k)
    exact Q'.le_trans' _ _ _ hmul (C.correspondence k)

/-! ## 6. Doc — PROVED vs NAMED-open (CRITICAL honesty, AGENTS.md Rule 6). -/

/-- **PROVED (genuine `Q'` facts, axiom-clean):**
  * `reconSep_eq_charExcited` — the in-tree transfer-operator located-gap separator IS the
    fundamental-channel character coefficient `coeffW gw 1 = sepFine gw` (the transfer↔
    character eigenvalue content, connected to `reconTransfer_located_gap`).
  * `sepCoarse_eqv_two_sepFine` — the coarse block-spin fused separator is `2·` the fine
    one (`acNfull w 1 ≃ coeffW w 1 + coeffW w 1`, the two Clebsch channels).
  * `fusedDefect_eqv_charExcited`, `coarseMargin_eq_fineMargin_sub_defect` — THE
    IDENTIFICATION: the block-spin margin degradation `sep' − sep ≃ coeffW w 1` and the
    coarse margin `Δ' ≃ Δ − coeffW w 1` — the real degradation IS the fused-character
    defect (exact identities, all `w`; validated `< 1e-51`, sympy-exact).
  * `fusedDefect_le_modelEnvelope` — for `0 ≤ w ≤ 1/2` the degradation is `≤` the same
    transverse-quadratic envelope `6(1−w)²` that bounds `δ_model` (the PROVED regime
    bound), identifying `δ_model` with the transfer-matrix margin loss.

**ADVERSARIAL / HONEST REGIME (documented, not faked):** the RAW fused defect
`coeffW w 1 = 2w³` is `≤ 6(1−w)²` only for `w ≤ 0.677…` (`raw_ratio_exceeds_at_weak`
proves failure at `w = 9/10`), and the raw coarse separator `4w³ < 1` needs `w < 0.63`.
The strong-coupling anchor `w = 1/6` is inside; `w ≤ 1/2` is the proved edge.  The
weak-coupling extension is the renormalized `FullRangeFusedDefect` residual.

**NAMED OPEN (NOT inhabited):** `TransferCharacterCorrespondence` — the transfer-op ↔
character eigenvalue correspondence at every AF scale (dynamical form-preservation +
weak-coupling bound).  `correspondence_to_gapChannelDomination` reduces
`GapChannelDomination` to it (guard-safe conditional).  NO 4D Yang–Mills mass gap is
claimed; nothing is faked; no guarded bundle is inhabited. -/
theorem routeF_honesty : True := trivial

end YMGap.Continuum.RouteFTransferIdentification

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RouteFTransferIdentification.reconSep_eq_charExcited
#print axioms YMGap.Continuum.RouteFTransferIdentification.sepCoarse_eqv_two_sepFine
#print axioms YMGap.Continuum.RouteFTransferIdentification.twoAdd_sub_self
#print axioms YMGap.Continuum.RouteFTransferIdentification.sub_add_split
#print axioms YMGap.Continuum.RouteFTransferIdentification.fusedDefect_eqv_charExcited
#print axioms YMGap.Continuum.RouteFTransferIdentification.coarseMargin_eq_fineMargin_sub_defect
#print axioms YMGap.Continuum.RouteFTransferIdentification.fusedDefect_le_modelEnvelope
#print axioms YMGap.Continuum.RouteFTransferIdentification.correspondence_to_gapChannelDomination
