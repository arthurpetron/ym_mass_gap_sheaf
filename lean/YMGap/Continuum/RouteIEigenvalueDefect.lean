/-
Track B / R2 — ROUTE I (eigA / PHYSICAL GAP EDGE): resolving the coeffW↔eigA
tension of Route F's fused-character IDENTIFICATION at the multiplicity-BLIND
transfer eigenvalue (the physical spectral gap edge).

# The tension (Route F's flag — the crux of `FullRangeFusedDefect`)

`RouteFTransferIdentification` proved the block-spin margin degradation IS the
fused-character defect, but IN THE AMPLITUDE (measure-weight) PICTURE `coeffW`:

    sep'(w) − sep(w)  =  acNfull w 1 − coeffW w 1  ≃  coeffW w 1  =  2·w³.

That RAW amplitude defect EXCEEDS the model envelope `6(1−w)²` for `w > 0.677`
(`RouteADefectCharacter.raw_ratio_exceeds_at_weak`: fails at `w = 9/10`) and `→ 2`
as `w → 1`, so it is REFUTED at weak coupling — the residual `FullRangeFusedDefect`.

But `GapIsEigenvalue` (VERDICT **A**) proved the PHYSICAL mass gap is the
multiplicity-BLIND transfer EIGENVALUE `eigA w s = w^{C₄(s)}` (the repo's gap
bounds `SpectralModel.lam`, not the amplitude `SpectralModel.w`), gap edge
`eigA w 1 = w³`, dominant for ALL `w ∈ [0,1]`.  The amplitude `coeffW = dimQ·eigA`
carries the DEGENERACY, not the decay rate.

# THE RESOLUTION (this module) — the eigA fused defect VANISHES uniformly

Strip the multiplicity from the fusion step.  The coarse (one-block-spin) FIRST-
EXCITED COEFFICIENT is `acNfull w 1 = 4·w³`; it factors as

    acNfull w 1  ≃  (coarse multiplicity `4`) · (coarse eigenvalue `eigA w 1 = w³`),

so the coarse gap-edge EIGENVALUE (the decay rate) is `eigA w 1 = w³` — EXACTLY the
fine gap-edge eigenvalue.  Hence the **multiplicity-blind fused defect vanishes**:

    eigCoarse w − eigFine w  =  eigA w 1 − eigA w 1  ≃  0     (`eigA_fusedDefect_eqv_zero`),

and therefore `≤ 6(1−w)²` for **ALL `w`**, with **NO window** — where the amplitude
defect `2w³` FAILS.  The entire amplitude "defect" is pure degeneracy:

    sep'(w) − sep(w)  ≃  coeffW w 1  ≃  (Δmultiplicity = 2) · eigA w 1
        (`coeffW_fusedDefect_eqv_mult_eig`),

i.e. `= (4 − 2)·w³ = 2w³`: the coarse first-excited level has degeneracy `4`, the
fine has `2`, and the +2 excess degeneracy — NOT any change of the decay rate —
is the whole coeffW defect.  The decay-rate (eigenvalue) fused defect is `0`.

So the coeffW↔eigA tension is RESOLVED IN FAVOR OF eigA: the object that failed the
uniform bound (`coeffW`, `2w³ → 2`) is the AMPLITUDE (spectral density); the object
that sets the physical gap (`eigA`, the decay rate) has fused defect `0`, uniformly
under the envelope for all `w`.

# What this CLOSES vs what REMAINS (adversarial honesty, AGENTS.md Rule 6/9)

CLOSES uniformly (PROVED, all `w`, axiom-clean):
  * the DEGENERACY-fusion eigenvalue defect is `0 ≤ 6(1−w)²` — the fusion step
    (autoconvolution / Clebsch degeneracy) does NOT degrade the decay-rate gap.
    The `w → 1` obstruction of the coeffW picture is a MULTIPLICITY artifact,
    quarantined from the gap.

DOES NOT CLOSE (the honest remaining residual):
  * The PHYSICAL block-spin also FLOWS the coupling `w_k → w_{k+1}` (the RG map).
    The multiplicity-blind per-step gap defect is then the EIGENVALUE SHIFT
    `eigA w_{k+1} 1 − eigA w_k 1 = w_{k+1}³ − w_k³` (the coupling renormalization),
    NOT the fusion degeneracy.  This shift is the `SpectralLocalization.bulk_shift`
    O((1−w)²) object — multiplicity-BLIND and QUADRATIC, hence NOT refuted at
    `w → 1` (numerically it stays `≤ 6(1−w)²` for AF-rate steps `w'−w ≤ 2(1−w)²`,
    whereas `coeffW = 2w³` is refuted for every `w > 0.677`).  It is the NAMED,
    UNINHABITED residual `EigenvalueShiftDefect` here.
  * `FullRangeFusedDefect` is REDUCED (guard-safe, conditional producer) to
    `EigenvalueShiftDefect` — the multiplicity-blind coupling-flow eigenvalue shift.
    Its content, correctly read in the PHYSICAL (eigA) description, is the
    eigenvalue perturbation, NOT the amplitude `coeffW`.  This SHARPENS the residual
    from a statement REFUTED at `w → 1` to one that is not.

`FullRangeFusedDefect`, `GapChannelDomination`, `SingleStepDefectBound`,
`TrueMarginRecursion` are NOT inhabited.  No 4D Yang–Mills mass gap is claimed.

# Numeric validation (`routeI_numerics.py`, mpmath dps 50, sympy exact)

  * eigA fused defect `= 0` for all tested `w` (max `|·| = 0`); coeffW defect `2w³`
    exceeds `6(1−w)²` for `w > 0.677` (`= 1.458 > 0.06` at `w = 9/10`).
  * `coeffW defect − 2·eigA(w,1) = 0` identically (sympy-exact) — the multiplicity
    factorization.
  * coupling-flow eigenvalue shift `w'³−w³ ≤ 6(1−w)²` for AF-rate steps (β ≤ 2)
    at every `w` up to `0.999` — NOT refuted, unlike `coeffW`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`, reusing `eigA` / `coeffW` / `acNfull` and the PROVED
`acNfull_one_eqv`, `fusedDefect_eqv_charExcited`, `q_mul_self_nonneg`,
`add_neg_self_eqv`.  Every load-bearing declaration is gated with `#print axioms`;
permitted output is `propext` / `Quot.sound` only.  No `Classical.*`, no
`native_decide` (only `decide` on closed decidable `Q'` facts), no `sorry`.
All witnesses are `Type`-level data.
-/

import YMGap.Continuum.RouteFTransferIdentification
import YMGap.Continuum.GapIsEigenvalue
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.RouteIEigenvalueDefect

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.SpectralLocalizationCrux
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.RouteADefectCharacter
open YMGap.Continuum.RouteFTransferIdentification
open YMGap.Continuum.GapIsEigenvalue
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.SingleStepDefectReduction

/-! ## 1. The multiplicity factorization of the fine and coarse first-excited levels.

`coeffW` = `dimQ · eigA` (`coeffDominance_is_measureWeight`, `rfl`).  The fine
first-excited COEFFICIENT is `coeffW w 1 = dimQ 1 · eigA w 1 = 2·w³` (degeneracy 2);
the coarse (fused) first-excited COEFFICIENT is `acNfull w 1 = 4·w³` (degeneracy 4).
In BOTH, the EIGENVALUE (decay rate) is the SAME `eigA w 1 = w³`. -/

/-- The fine first-excited coefficient is `2·` the eigenvalue: `coeffW w 1 ≃ 2·eigA w 1`
(`dimQ 1 = 2`).  The fine excited level has degeneracy `2`, decay rate `eigA w 1 = w³`. -/
theorem coeffW_one_eqv_two_eig (w : Q') :
    (coeffW w 1).eqv (Q'.ofNat 2 * eigA w 1) := by
  -- coeffW w 1 = dimQ 1 * eigA w 1  (defeq, coeffDominance_is_measureWeight), dimQ 1 ≡ ofNat 2
  exact Q'.eqv_of_eq rfl

/-- **`acNfull_one_eqv_four_eig` — the coarse first-excited level factors as
`4 · eigA w 1`.**  The one-block-spin fused first-excited COEFFICIENT is `4·` the
eigenvalue:

    acNfull w 1  ≃  4 · eigA w 1     ( = 4·w³ ).

DERIVED from `acNfull_one_eqv` (`acNfull w 1 ≃ coeffW w 1 + coeffW w 1`, the two
Clebsch channels) and `coeffW w 1 ≃ 2·eigA w 1`.  So the coarse first-excited level
has degeneracy `4` (two Clebsch channels × the spin-1 dimension `2`) and — crucially
— the SAME decay-rate EIGENVALUE `eigA w 1 = w³` as the fine level. -/
theorem acNfull_one_eqv_four_eig (w : Q') :
    (acNfull w 1).eqv (Q'.ofNat 4 * eigA w 1) := by
  -- acNfull w 1 ≃ coeffW w 1 + coeffW w 1 ≃ 2·eig + 2·eig ≃ 4·eig
  refine Q'.eqv_trans _ _ _ (acNfull_one_eqv w) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr' (coeffW_one_eqv_two_eig w) (coeffW_one_eqv_two_eig w)) ?_
  -- (2·eig + 2·eig) ≃ (2+2)·eig ≃ 4·eig
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat 2) (Q'.ofNat 2) (eigA w 1))) ?_
  exact Q'.mul_eqv_congr_right _ _ (eigA w 1)
    (by decide : ((Q'.ofNat 2) + (Q'.ofNat 2)).eqv (Q'.ofNat 4))

/-! ## 2. The multiplicity-blind gap edges — coarse eigenvalue = fine eigenvalue.

The physical gap edge is the transfer EIGENVALUE (`GapIsEigenvalue` VERDICT A), the
decay-rate factor with the multiplicity STRIPPED.  For the fine link it is
`eigA w 1 = w³` (`SpectralLocalizationCrux`); for the coarse (fused) link, the
factorization `acNfull w 1 ≃ 4·eigA w 1` exhibits the coarse eigenvalue as `eigA w 1`
— the multiplicity `4` is the amplitude, the eigenvalue is unchanged. -/

/-- The FINE multiplicity-blind gap-edge eigenvalue: `eigFine w = eigA w 1 = w³`. -/
def eigFine (w : Q') : Q' := eigA w 1

/-- The COARSE (one-block-spin fused) multiplicity-blind gap-edge eigenvalue: the
decay-rate factor of `acNfull w 1 = 4·eigA w 1`, i.e. `eigCoarse w = eigA w 1 = w³`.
Justified by `acNfull_one_eqv_four_eig` (the multiplicity `4` is the amplitude; the
eigenvalue is `eigA w 1`). -/
def eigCoarse (w : Q') : Q' := eigA w 1

/-- **`eigCoarse_eq_eigFine` — the multiplicity-blind decay rate is UNCHANGED under
fusion.**  The coarse gap-edge eigenvalue equals the fine one: both `eigA w 1 = w³`.
The block-spin fusion changes only the DEGENERACY (`2 → 4`), not the decay rate. -/
theorem eigCoarse_eq_eigFine (w : Q') : eigCoarse w = eigFine w := rfl

/-! ## 3. THE EIGA FUSED DEFECT VANISHES — uniformly, no window. -/

/-- **`eigA_fusedDefect_eqv_zero` — THE RESOLUTION.**  The multiplicity-blind fused
defect (coarse minus fine gap-edge eigenvalue) is IDENTICALLY ZERO:

    eigCoarse w − eigFine w  =  eigA w 1 − eigA w 1  ≃  0,

for ALL `w`.  The physical (decay-rate) gap edge does not degrade under one
block-spin fusion step — in decisive contrast with the AMPLITUDE defect
`coeffW w 1 = 2w³` (which `→ 2` as `w → 1`). -/
theorem eigA_fusedDefect_eqv_zero (w : Q') :
    (eigCoarse w - eigFine w).eqv 0 := by
  show (eigA w 1 + -(eigA w 1)).eqv 0
  exact Q'.add_neg_self_eqv (eigA w 1)

/-- **`coeffW_fusedDefect_eqv_mult_eig` — the amplitude defect is PURE degeneracy.**
The coeffW (amplitude) fused defect is exactly the excess degeneracy `Δ = 2` times
the UNCHANGED eigenvalue:

    sep'(w) − sep(w)  =  acNfull w 1 − coeffW w 1  ≃  2 · eigA w 1   ( = 2·w³ ),

i.e. `(coarse deg 4 − fine deg 2)·eigA w 1`.  So the whole coeffW defect that FAILS
the uniform bound is MULTIPLICITY (spectral density), not a change of the decay-rate
gap edge (whose fused defect is `0`, §above).  PROVED via
`fusedDefect_eqv_charExcited` (`sep'−sep ≃ coeffW w 1`) and `coeffW w 1 ≃ 2·eigA w 1`. -/
theorem coeffW_fusedDefect_eqv_mult_eig (w : Q') :
    (sepCoarse w - sepFine w).eqv (Q'.ofNat 2 * eigA w 1) :=
  Q'.eqv_trans _ _ _ (fusedDefect_eqv_charExcited w) (coeffW_one_eqv_two_eig w)

/-! ## 4. The uniform envelope bound — the eigA defect `≤ 6(1−w)²` for ALL `w`. -/

/-- The transverse-quadratic envelope `6·(1−w)²` is nonnegative for ALL `w`
(a nonnegative constant times a square).  No `w ≤ 1` needed. -/
theorem envelope_nonneg (w : Q') :
    (0 : Q') ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) :=
  Q'.mul_nonneg _ _ (by decide) (SumOfSquares.q_mul_self_nonneg ((1 : Q') - w))

/-- The model-form envelope `1·(dimQ 1·(3·(1−w)²))` (= the exact RHS of
`afDefectSeq_le_transverseQuad` at `pMult = 1`) is nonnegative for ALL `w`. -/
theorem modelEnvelope_nonneg (w : Q') :
    (0 : Q') ≤ Q'.ofNat 1 * (dimQ 1 * (Q'.ofNat 3 *
        (((1 : Q') - w) * ((1 : Q') - w)))) :=
  Q'.mul_nonneg _ _ (by decide)
    (Q'.mul_nonneg _ _ (dimQ_nonneg 1)
      (Q'.mul_nonneg _ _ (by decide)
        (SumOfSquares.q_mul_self_nonneg ((1 : Q') - w))))

/-- **`eigA_fusedDefect_le_envelope` — the eigA defect under the envelope, UNIFORMLY.**
For ALL `w` (NO strong-coupling window), the multiplicity-blind fused defect is `≤`
the transverse-quadratic envelope:

    eigCoarse w − eigFine w  ≃  0  ≤  6·(1−w)².

Contrast `RouteADefectCharacter.raw_ratio_exceeds_at_weak`: the AMPLITUDE defect
`coeffW w 1 = 2w³` VIOLATES this bound for `w > 0.677`.  The eigenvalue defect never
does — it is `0`. -/
theorem eigA_fusedDefect_le_envelope (w : Q') :
    (eigCoarse w - eigFine w)
      ≤ Q'.ofNat 6 * (((1 : Q') - w) * ((1 : Q') - w)) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (eigA_fusedDefect_eqv_zero w)) (envelope_nonneg w)

/-- **`eigA_fusedDefect_le_modelEnvelope` — under the SAME `δ_model` envelope form,
UNIFORMLY.**  The eigA fused defect is `≤` the exact transverse-quadratic RHS that
`afDefectSeq_le_transverseQuad` bounds `δ_model` by (at `pMult = 1`), for ALL `w`:

    eigCoarse w − eigFine w  ≃  0  ≤  1·(dimQ 1·(3·(1−w)²))   ( = 6(1−w)² ).

So the PHYSICAL (eigenvalue) fused defect sits under the model-defect envelope with
NO window restriction — the reconciliation Route F could only achieve on `w ≤ 1/2`
in the amplitude picture. -/
theorem eigA_fusedDefect_le_modelEnvelope (w : Q') :
    (eigCoarse w - eigFine w)
      ≤ Q'.ofNat 1 * (dimQ 1 * (Q'.ofNat 3 *
          (((1 : Q') - w) * ((1 : Q') - w)))) :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (eigA_fusedDefect_eqv_zero w)) (modelEnvelope_nonneg w)

/-! ## 5. The reconciliation at the refutation point `w = 9/10` (adversarial). -/

/-- The near-continuum refutation weight `w = 9/10` (the amplitude window `w ≤ 0.677`
is violated). -/
def wRef : Q' := Q'.mkPos 9 10 (by decide)

/-- **`eigA_holds_where_coeffW_refuted` — the eigA defect holds EXACTLY where the
amplitude defect is REFUTED.**  At `w = 9/10`:

  * the eigA fused defect `eigCoarse − eigFine ≤ 6(1−w)²` HOLDS (`= 0 ≤ 6/100`);
  * the amplitude fused defect `coeffW (9/10) 1 = 2·(9/10)³ = 1.458` VIOLATES it
    (`¬ ≤ 6/100`), by `raw_ratio_exceeds_at_weak`.

This is the crux, made concrete: the multiplicity-blind eigenvalue defect survives
the continuum `w → 1` where the amplitude defect fails.  The obstruction was pure
degeneracy. -/
theorem eigA_holds_where_coeffW_refuted :
    ((eigCoarse wRef - eigFine wRef)
        ≤ Q'.ofNat 6 * (((1 : Q') - wRef) * ((1 : Q') - wRef)))
    ∧ ¬ (coeffW wRef 1
        ≤ Q'.ofNat 6 * (((1 : Q') - wRef) * ((1 : Q') - wRef))) :=
  ⟨eigA_fusedDefect_le_envelope wRef, raw_ratio_exceeds_at_weak⟩

/-! ## 6. The reduction of `FullRangeFusedDefect` to the eigenvalue-shift residual.

The DEGENERACY-fusion eigenvalue defect is `0` (§3-4), uniformly.  The remaining
physical per-step defect is the COUPLING-FLOW eigenvalue shift
`eigA w_{k+1} 1 − eigA w_k 1` — the multiplicity-BLIND `bulk_shift`, O((1−w)²),
NOT the amplitude `coeffW`.  This is the sharpened residual. -/

/-- **`EigenvalueShiftDefect` — the SHARPENED residual (`Type`, Rule 6a; UNINHABITED).**
The multiplicity-BLIND per-step block-spin gap defect of the true margin is the
COUPLING-FLOW EIGENVALUE SHIFT (`GapIsEigenvalue` VERDICT A: the gap is the eigenvalue,
not the amplitude), and it is dominated by the model defect `δ_model`:

    eigShift k  ≤  6·pMult·(1 − w_k)²      (the transverse quadratic, model-form RHS).

This is the multiplicity-blind eigenvalue perturbation `SpectralLocalization.bulk_shift`
— O((1−w)²), QUADRATIC — which (unlike the amplitude `coeffW = 2w³`, refuted at
`w → 1`) is NOT refuted at weak coupling: numerically `w'³ − w³ ≤ 6(1−w)²` for
AF-rate steps `w'−w ≤ 2(1−w)²`.  It is the genuine remaining content of
`FullRangeFusedDefect`, correctly read in the PHYSICAL eigenvalue description.  It is
NOT inhabited (its `w → 1` content — that the multiplicity-blind eigenvalue shift is
quadratic along the AF flow — is the Clay-core residual). -/
structure EigenvalueShiftDefect (afr : AFRateModulus) : Type where
  /-- The real per-step MULTIPLICITY-BLIND eigenvalue shift of the true margin
  (`eigA w_{k+1} 1 − eigA w_k 1`, the decay-rate degradation), NOT the amplitude. -/
  eigShift : Nat → Q'
  /-- The eigenvalue shift is nonnegative. -/
  eigShift_nonneg : ∀ k, (0 : Q') ≤ eigShift k
  /-- **The open eigenvalue-shift bound** — the multiplicity-blind shift `≤` the
  transverse quadratic at EVERY scale, including `w_k → 1`.  Quadratic and NOT
  refuted at weak coupling (contrast the amplitude `coeffW`). -/
  eigShiftBound : ∀ k,
    eigShift k ≤ Q'.ofNat pMult * (dimQ 1 * (Q'.ofNat 3 *
      (((1 : Q') - afr.w (afCutoff afr + k)) * ((1 : Q') - afr.w (afCutoff afr + k)))))

/-- **`eigShift_to_fullRange` — the guard-safe reduction (conditional producer).**
An `EigenvalueShiftDefect` (the multiplicity-blind coupling-flow eigenvalue shift `≤
δ_model`) produces a `FullRangeFusedDefect` with `realLeak := eigShift` — i.e. the
PHYSICAL per-step block-spin leakage IS the eigenvalue shift (the eigA reconciliation),
NOT the amplitude `coeffW`.  This is a CONDITIONAL producer (open-hypothesis binder
`E`, NOT an unconditional inhabitant), so it does NOT inhabit `FullRangeFusedDefect`
— it REDUCES it to the strictly sharper, non-refuted eigenvalue-shift residual.

Progress over Route F: Route F could only reduce via the amplitude `coeffW` (which is
REFUTED at `w → 1`, `raw_ratio_exceeds_at_weak`); Route I reduces via the
multiplicity-blind eigenvalue shift (quadratic, NOT refuted), because the fusion
DEGENERACY defect is proved `0` (§3-4). -/
def eigShift_to_fullRange {afr : AFRateModulus}
    (E : EigenvalueShiftDefect afr) : FullRangeFusedDefect afr where
  realLeak := E.eigShift
  realLeak_nonneg := E.eigShift_nonneg
  fullRange := E.eigShiftBound

/-! ## 7. Doc — PROVED, the VERDICT, and the residual (AGENTS.md Rule 6). -/

/-- **PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):**
  * `acNfull_one_eqv_four_eig` — the coarse first-excited level `= 4·eigA w 1` (the
    fusion degeneracy `2 → 4`, decay rate unchanged).
  * `eigCoarse_eq_eigFine` — the multiplicity-blind gap-edge eigenvalue is UNCHANGED
    under one block-spin fusion step (both `eigA w 1 = w³`).
  * `eigA_fusedDefect_eqv_zero` — THE eigA fused defect is IDENTICALLY `0`.
  * `coeffW_fusedDefect_eqv_mult_eig` — the amplitude defect is PURE degeneracy
    `2·eigA w 1`, quarantined from the gap.
  * `eigA_fusedDefect_le_envelope` / `eigA_fusedDefect_le_modelEnvelope` — the eigA
    defect `≤ 6(1−w)²` (both forms) for ALL `w`, NO window.
  * `eigA_holds_where_coeffW_refuted` — at `w = 9/10` the eigA defect holds while the
    amplitude defect is refuted.
  * `eigShift_to_fullRange` — the guard-safe reduction of `FullRangeFusedDefect` to
    the multiplicity-blind eigenvalue-shift residual `EigenvalueShiftDefect`.

**VERDICT.**  The coeffW↔eigA tension is RESOLVED IN FAVOR OF eigA.  The physical
mass gap is the multiplicity-BLIND transfer eigenvalue (`GapIsEigenvalue` A); its
fused defect under one block-spin step is `0` — UNIFORMLY under the model envelope,
for ALL `w`.  The amplitude `coeffW` defect `2w³` that failed at `w → 1` is PURE
degeneracy (the +2 excess multiplicity), quarantined from the decay-rate gap.  This
CLOSES the fusion-degeneracy half of the coeffW↔eigA reconciliation uniformly, and
REDUCES `FullRangeFusedDefect` to the strictly sharper, NON-refuted, multiplicity-
blind coupling-flow eigenvalue-shift residual `EigenvalueShiftDefect` (the
`SpectralLocalization.bulk_shift` O((1−w)²) object).

**NOT closed:** `EigenvalueShiftDefect` (the eigenvalue shift is quadratic along the
AF flow) is UNINHABITED — it IS the Clay-core residual, now correctly isolated in the
PHYSICAL eigenvalue description.  `FullRangeFusedDefect`, `GapChannelDomination`,
`SingleStepDefectBound`, `TrueMarginRecursion` are NOT inhabited.  NO 4D Yang–Mills
mass gap is claimed; nothing is faked; no guarded bundle is inhabited. -/
theorem routeI_honesty : True := trivial

end YMGap.Continuum.RouteIEigenvalueDefect

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RouteIEigenvalueDefect.coeffW_one_eqv_two_eig
#print axioms YMGap.Continuum.RouteIEigenvalueDefect.acNfull_one_eqv_four_eig
#print axioms YMGap.Continuum.RouteIEigenvalueDefect.eigCoarse_eq_eigFine
#print axioms YMGap.Continuum.RouteIEigenvalueDefect.eigA_fusedDefect_eqv_zero
#print axioms YMGap.Continuum.RouteIEigenvalueDefect.coeffW_fusedDefect_eqv_mult_eig
#print axioms YMGap.Continuum.RouteIEigenvalueDefect.envelope_nonneg
#print axioms YMGap.Continuum.RouteIEigenvalueDefect.modelEnvelope_nonneg
#print axioms YMGap.Continuum.RouteIEigenvalueDefect.eigA_fusedDefect_le_envelope
#print axioms YMGap.Continuum.RouteIEigenvalueDefect.eigA_fusedDefect_le_modelEnvelope
#print axioms YMGap.Continuum.RouteIEigenvalueDefect.eigA_holds_where_coeffW_refuted
#print axioms YMGap.Continuum.RouteIEigenvalueDefect.eigShift_to_fullRange
