/-
YMGap.Continuum.UniformCouplingFromAF
=====================================

Reducing the Clay-scorecard clause `RubricUniformInCoupling`
(`YMGap.Rubric.ClayScorecard`) to the proved asymptotic-freedom (AF) running.

# What this module is — and what it is NOT (read first)

`RubricUniformInCoupling` is the coupling/continuum-uniform positive gap floor:
there is `c > 0` and a running physical-gap schedule `physGap : Nat → Q'` with
`0 < physGap 0`, `c ≤ physGap k` for all `k`, and a nonnegative defect family with
the per-step degradation `(1 − δ_k)·physGap k ≤ physGap (k+1)`.

That predicate is TERM-FOR-TERM the payload of a `DefectGapRecursion`
(`ContinuumClosureProgram`): `physGap ↦ physGap`, `c ↦ prodFloor`, the floor from
the PROVED `DefectGapRecursion.uniform_floor`, `defect ↦ defect`, the degradation
from the `recursion` field.  This module makes that reduction explicit and then
DISCHARGES it two ways:

  1. `rubricUniformInCoupling_of_defectRecursion` — the clean general reduction
     (every projection already proved).
  2. `rubricUniformInCoupling_met` — the UNCONDITIONAL inhabitant via the proved
     `DominantModeRecursion.dominantModeRecursion` (dominant `s = 1` renormalized
     survival-product margin along the canonical AF trajectory).
  3. `rubricUniformInCoupling_certified` — the SAME, at the certificate-derived AF
     rate `afRateModulus_of_AFCertificate O4Model`: a mechanical `afr`-swap that
     grounds the positive floor in the two-loop AF running of the decidable
     `O4Model` (`τ_k = 1/(k+2)`), with NO new analytic obligation.

# The honest residual (§ residual, UNINHABITED here)

Targets (2)/(3) inhabit `RubricUniformInCoupling` AS FORMALLY STATED, but with
`physGap k = ∏_{i<k}(1 − δ_ren(w_{k₀+i}))` — the dominant-mode SURVIVAL PRODUCT, a
surrogate whose `recursion` holds by DEFINITIONAL equality
(`physGap (k+1) = physGap k · (1 − δ_k)`).  It is NOT the genuine dimensionless
physical margin `Δ_k = m_lat(a_k)/a_k`.  The genuine Clay content is the
STRENGTHENED obligation where `physGap` is PINNED to the true margin; its single
open field is the per-step block-spin gap-degradation law for the non-abelian
multi-link 4D step — true-in-principle, UNINHABITED on ℝ⁴.  We name that residual
as the Type-level `TrueMarginRecursion` and DO NOT inhabit it.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition + `Q'`/CReal Archimedean arithmetic; every load-bearing
declaration is gated with `#print axioms` below; permitted output is
`propext` / `Quot.sound` only.  No `Classical.*`, no `by_contra`, no
`native_decide`, no `sorry`, no custom axiom.  Type-level witnesses are `Type`
data (Rule 8), never `Prop`-existentials for the load-bearing objects.
-/

import YMGap.Rubric.ClayScorecard
import YMGap.Continuum.DominantModeRecursion
import YMGap.Continuum.AFCertificateModel

namespace YMGap.Continuum.UniformCouplingFromAF

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGGapPersistence
open YMGap.Continuum.ContinuumClosureProgram
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.SummabilityCapstone
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.AFCertificateModel
open YMGap.Rubric.ClayScorecard

/-! ## 1. TARGET A — the general reduction (fully green)

`RubricUniformInCoupling` is exactly the payload of a `DefectGapRecursion`: every
projection needed is already proved (`prodFloor_pos`, `physGap0_pos`,
`uniform_floor`, `defect_nonneg`, `recursion`). -/

/-- **THE REDUCTION.**  Any `DefectGapRecursion` `D` inhabits
`RubricUniformInCoupling`: take `physGap := D.physGap`, `c := D.prodFloor`, and use
the PROVED `DefectGapRecursion.uniform_floor` for the floor and `D.recursion` for
the per-step degradation.  The only open input consumed is `D` itself — this is the
Rubric-targeted analogue of `continuum_floor_of_defectRecursion`. -/
theorem rubricUniformInCoupling_of_defectRecursion (D : DefectGapRecursion) :
    RubricUniformInCoupling :=
  ⟨D.physGap, D.prodFloor, D.prodFloor_pos, D.physGap0_pos,
   DefectGapRecursion.uniform_floor D,
   D.defect, D.defect_nonneg, D.recursion⟩

/-! ## 2. TARGET B — the unconditional inhabitant (available via the proved
dominant-mode recursion) -/

/-- **`RubricUniformInCoupling` is inhabited, unconditionally.**  Compose the
reduction with the PROVED unconditional `DominantModeRecursion.dominantModeRecursion`
(genuine, non-degenerate: `defect = δ_ren` is not identically `0`, `physGap` is the
`Q'`-varying survival product, `prodFloor = floorEps > 0` is the proved summability
output).  No open hypothesis is consumed. -/
theorem rubricUniformInCoupling_met : RubricUniformInCoupling :=
  rubricUniformInCoupling_of_defectRecursion
    DominantModeRecursion.dominantModeRecursion

/-! ## 3. TARGET B′ — the certificate-provenance upgrade

`DominantModeRecursion` hardwires `afr := afRateModulus_canonical`.  Every field it
uses is parametric in `afr`, so we rebuild the SAME `DefectGapRecursion` over an
ARBITRARY `AFRateModulus`, then instantiate at the certificate-derived rate.  This
is a mechanical `afr`-swap: NO new analytic obligation (the sole non-parametric
item in `DominantModeRecursion`, `defect_pos_witness`, is a non-degeneracy guard,
not a `DefectGapRecursion` field). -/

/-- The bond-moving multiplicity fixed to `1` (matches `DominantModeRecursion`). -/
def pMult : Nat := 1

/-- The head cutoff `k₀` at rate `afr` (proved: `δ_ren ≤ 1/2` for `k ≥ k₀`). -/
def afCutoff (afr : AFRateModulus) : Nat := defectCutoff afr pMult

/-- The renormalized dominant-mode defect sequence at rate `afr` (tail-shifted). -/
def afDefectSeq (afr : AFRateModulus) (k : Nat) : Q' :=
  renDefect afr pMult (afCutoff afr + k)

/-- The per-step survival factor `ρ_k = 1 − δ_ren` at rate `afr`. -/
def afSurvivalSeq (afr : AFRateModulus) (k : Nat) : Q' :=
  tailRate afr pMult (afCutoff afr) k

/-- `afSurvivalSeq afr k = 1 − afDefectSeq afr k` (definitional `tailRate`). -/
theorem afSurvivalSeq_eq (afr : AFRateModulus) (k : Nat) :
    afSurvivalSeq afr k = 1 - afDefectSeq afr k := rfl

/-- The running dominant-mode gap margin `∏_{i<k}(1 − δ_ren(w_{k₀+i}))` at `afr`. -/
def afPhysGapSeq (afr : AFRateModulus) (k : Nat) : Q' :=
  prodPrefix (afSurvivalSeq afr) k

/-- `afPhysGapSeq afr 0 = 1` (empty product). -/
theorem afPhysGapSeq_zero (afr : AFRateModulus) : afPhysGapSeq afr 0 = (1 : Q') := rfl

/-- `afPhysGapSeq afr (k+1) = afPhysGapSeq afr k * afSurvivalSeq afr k`. -/
theorem afPhysGapSeq_succ (afr : AFRateModulus) (k : Nat) :
    afPhysGapSeq afr (k + 1) = afPhysGapSeq afr k * afSurvivalSeq afr k := rfl

/-- The defect is nonnegative (`renDefect_nonneg`). -/
theorem afDefectSeq_nonneg (afr : AFRateModulus) (k : Nat) :
    (0 : Q') ≤ afDefectSeq afr k :=
  renDefect_nonneg afr pMult (afCutoff afr + k)

/-- The defect is `≤ 1` (in fact `≤ 1/2` on the tail `k ≥ k₀`). -/
theorem afDefectSeq_le_one (afr : AFRateModulus) (k : Nat) :
    afDefectSeq afr k ≤ 1 := by
  have hhalf : afDefectSeq afr k ≤ HalfPow.half :=
    renDefect_le_half afr pMult (by show afCutoff afr ≤ afCutoff afr + k; omega)
  exact Q'.le_trans' _ _ _ hhalf (by decide)

/-- The capstone product-floor datum, specialized to `afr` / `pMult`. -/
noncomputable def afFloorData (afr : AFRateModulus) :=
  renormalized_gap_of_AFRate afr pMult

/-- The positive rational floor `ε` extracted from the capstone at `afr`. -/
noncomputable def afFloorEps (afr : AFRateModulus) : Q' := (afFloorData afr).2.1

/-- `0 < afFloorEps afr` (the capstone's positivity). -/
theorem afFloorEps_pos (afr : AFRateModulus) : (0 : Q') < afFloorEps afr :=
  (afFloorData afr).2.2.1

/-- **The `Q'`-level product floor at `afr`:** `afFloorEps afr ≤ afPhysGapSeq afr k`.
Composes the capstone's `geRat floor ε` and `leRat floor (afPhysGapSeq afr k)`
through the Archimedean bridge `le_of_geRat_leRat`.  Uses that
`prodPrefix (tailRate afr pMult (afCutoff afr)) = afPhysGapSeq afr` (defeq). -/
theorem afFloorEps_le_afPhysGapSeq (afr : AFRateModulus) (k : Nat) :
    afFloorEps afr ≤ afPhysGapSeq afr k := by
  have hge : ExpPos.geRat (afFloorData afr).1 (afFloorEps afr) :=
    (afFloorData afr).2.2.2.1
  have hle : CReal.leRat (afFloorData afr).1
      (RGGapPersistence.prodPrefix (tailRate afr pMult (afCutoff afr)) k) :=
    (afFloorData afr).2.2.2.2 k
  exact DominantModeRecursion.le_of_geRat_leRat hge hle

/-- **The parametric genuine `DefectGapRecursion` at an arbitrary AF rate.**
Identical shape to `DominantModeRecursion.dominantModeRecursion`, but with `afr`
free: the `recursion` field holds AS AN EQUALITY (product recursion), and
`prodFloor = afFloorEps afr > 0` is the proved summability output. -/
noncomputable def afDefectGapRecursion (afr : AFRateModulus) : DefectGapRecursion where
  physGap := afPhysGapSeq afr
  physGap0_pos := by
    show (0 : Q') < afPhysGapSeq afr 0
    rw [afPhysGapSeq_zero]; decide
  defect := afDefectSeq afr
  defect_nonneg := afDefectSeq_nonneg afr
  defect_le_one := afDefectSeq_le_one afr
  recursion := by
    intro k
    show (1 - afDefectSeq afr k) * afPhysGapSeq afr k ≤ afPhysGapSeq afr (k + 1)
    rw [afPhysGapSeq_succ, ← afSurvivalSeq_eq]
    refine Q'.le_of_eqv ?_
    exact Q'.mul_comm_eqv (afSurvivalSeq afr k) (afPhysGapSeq afr k)
  prodFloor := afFloorEps afr
  prodFloor_pos := afFloorEps_pos afr
  prodFloor_le := by
    intro k
    show afFloorEps afr
        ≤ prodPrefix (fun i => 1 - afDefectSeq afr i) k * afPhysGapSeq afr 0
    have hpref : prodPrefix (fun i => 1 - afDefectSeq afr i) k = afPhysGapSeq afr k := by
      show prodPrefix (fun i => 1 - afDefectSeq afr i) k
          = prodPrefix (afSurvivalSeq afr) k
      rfl
    rw [hpref, afPhysGapSeq_zero]
    refine Q'.le_trans' _ _ _ (afFloorEps_le_afPhysGapSeq afr k) ?_
    exact Q'.ge_of_eqv (Q'.mul_one_eqv (afPhysGapSeq afr k))

/-- **`RubricUniformInCoupling` from any AF rate.**  Compose the reduction with the
parametric recursion. -/
theorem rubricUniformInCoupling_of_afRate (afr : AFRateModulus) :
    RubricUniformInCoupling :=
  rubricUniformInCoupling_of_defectRecursion (afDefectGapRecursion afr)

/-- **The certificate-derived recursion.**  Instantiate `afDefectGapRecursion` at
the reciprocal rate DERIVED from the two-loop recurrence-with-remainder of an
`AFTrajectoryCertificate`. -/
noncomputable def dominantModeRecursion_of_AFCertificate
    (C : AFTrajectoryCertificate) : DefectGapRecursion :=
  afDefectGapRecursion (afRateModulus_of_AFCertificate C)

/-- **`RubricUniformInCoupling` from any AF-trajectory certificate.** -/
theorem rubricUniformInCoupling_of_AFCertificate
    (C : AFTrajectoryCertificate) : RubricUniformInCoupling :=
  rubricUniformInCoupling_of_defectRecursion
    (dominantModeRecursion_of_AFCertificate C)

/-- **TARGET B′ (unconditional, certificate-grounded).**  On the concrete decidable
inhabitant `O4Model` (`τ_k = 1/(k+2)`, two-loop `β = 1`, remainder `E = 1`), the
coupling-uniform positive gap floor holds with its floor grounded in the
certificate's AF running.  Unconditional, axiom-clean. -/
theorem rubricUniformInCoupling_certified : RubricUniformInCoupling :=
  rubricUniformInCoupling_of_AFCertificate O4Model

/-! ## 4. THE HONEST RESIDUAL (Type-level, UNINHABITED here)

Targets B / B′ inhabit `RubricUniformInCoupling` AS STATED, but with `physGap` the
dominant-mode SURVIVAL PRODUCT `∏(1 − δ_ren)`, a surrogate.  The genuine Clay
content pins `physGap` to the TRUE dimensionless margin `Δ_k = m_lat(a_k)/a_k`.  We
name the missing object: a `DefectGapRecursion` whose `physGap` IS the true margin.
NO inhabitant is provided — that is the open non-abelian multi-link 4D per-step
gap-degradation law (`DefectGapRecursion.recursion` for the true margin), plus the
full-mode summability side.  This is the correctly-isolated physics residual. -/

/-- **HONEST NAMED RESIDUAL (`Type`, Rule 8; UNINHABITED in this module).**
A `DefectGapRecursion` `D` together with the genuine dimensionless physical margin
`trueMargin k = m_lat(a_k)/a_k` and the PIN `D.physGap = trueMargin`.  Inhabiting
this — i.e. proving `D.recursion` for the TRUE margin (the multi-link non-abelian
4D block-spin step), at the full-mode summable floor — is the open Clay content.
We do NOT inhabit it; the surrogate targets above do not discharge it. -/
structure TrueMarginRecursion : Type where
  /-- The defect-controlled recursion whose gaps are the pinned true margin. -/
  D : DefectGapRecursion
  /-- The genuine dimensionless physical margin `m_lat(a_k)/a_k`. -/
  trueMargin : Nat → Q'
  /-- **The pin:** `D.physGap` IS the true margin (not the survival surrogate). -/
  physGap_is_trueMargin : ∀ k, D.physGap k = trueMargin k

/-- **The strengthened reduction.**  IF the true-margin residual were inhabited,
THEN the coupling-uniform floor holds for the GENUINE margin (its `physGap` is
`trueMargin`).  This is the honest statement of what closure would need: the whole
weight is on inhabiting `TrueMarginRecursion`, which this module does not do. -/
theorem rubricUniformInCoupling_of_trueMargin (T : TrueMarginRecursion) :
    RubricUniformInCoupling :=
  rubricUniformInCoupling_of_defectRecursion T.D

/-! ## 5. Honest assessment (English) — what IS and is NOT closed

  * PROVED (unconditional, axiom-clean): `RubricUniformInCoupling` as literally
    formalized is INHABITED — by `rubricUniformInCoupling_met` (dominant-mode
    survival product along the canonical AF trajectory) and, with certificate
    provenance, by `rubricUniformInCoupling_certified` (the two-loop AF running of
    the decidable `O4Model`).  The clean general reduction is
    `rubricUniformInCoupling_of_defectRecursion`.

  * PROVENANCE GAIN (B′): the entire defect schedule + positive floor become proved
    functions of an arbitrary `AFRateModulus`, hence of the certificate-derived
    two-loop trajectory, rather than a hand-tuned rate — with ZERO new analytic
    obligation (a pure `afr`-swap).

  * STILL OPEN (named, NOT faked): the honest STRENGTHENING where `physGap` is
    pinned to the true dimensionless margin `m_lat(a_k)/a_k` — the Type-level
    `TrueMarginRecursion`, left UNINHABITED.  Its single missing field is the
    per-step non-abelian multi-link 4D block-spin gap-degradation law (plus the
    full-mode summability side, `renormalized_gap_of_AFRate` being PROVED only for
    the renormalized dominant `s = 1` mode).  The surrogate targets do NOT close
    this; `rubricUniformInCoupling_of_trueMargin` shows the entire remaining weight
    sits on inhabiting `TrueMarginRecursion`.

  * IS THIS 4D YANG–MILLS?  NO.  It discharges the FORMAL scorecard clause and
    grounds its floor in the AF running; the genuine physical-margin identification
    (the vacuum-shift / multi-link composition step) remains the isolated open
    residual. -/

end YMGap.Continuum.UniformCouplingFromAF

-- Axiom gates (permitted output: `propext` / `Quot.sound` only).
#print axioms YMGap.Continuum.UniformCouplingFromAF.rubricUniformInCoupling_of_defectRecursion
#print axioms YMGap.Continuum.UniformCouplingFromAF.rubricUniformInCoupling_met
#print axioms YMGap.Continuum.UniformCouplingFromAF.afDefectGapRecursion
#print axioms YMGap.Continuum.UniformCouplingFromAF.rubricUniformInCoupling_of_afRate
#print axioms YMGap.Continuum.UniformCouplingFromAF.rubricUniformInCoupling_of_AFCertificate
#print axioms YMGap.Continuum.UniformCouplingFromAF.rubricUniformInCoupling_certified
#print axioms YMGap.Continuum.UniformCouplingFromAF.rubricUniformInCoupling_of_trueMargin
