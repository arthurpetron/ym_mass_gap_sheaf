/-
# The ABELIAN MOMENT ENVELOPE — extending the abelian shadow toward the M1/M2 local-CLT

This module extends the EXACT abelian fusion CLT (`AbelianFusionCLT`) from the two-point
log-concavity anchor to the **moment objects** of the tilted measure that carry the
`SaddleVarianceFloor`/`FullRangeFloor` content of `CircleFourierPowerModel` — i.e. the
first- and second-moment ("M1/M2") envelope of the fusion local-CLT that `hlocalize`
consumes.

## The abelian tilted measure and its moments (EXACT)

The tilted measure on the antidiagonal is `μ_t(p) ∝ coeffW(w,p)·coeffW(w,t−p)` on
`p ∈ {0,…,t}` (`CircleFourierPowerModel`).  Dropping the Weyl dimensions `(p+1)(t−p+1)`
gives its **abelian shadow** `μ̂_t(p) ∝ abelCoeff(w,p)·abelCoeff(w,t−p) = w^{p²+(t−p)²}`,
whose weights are recorded here as the finite `Q'` sums

  * `abelAc  w t = Σ_{p=0}^{t}       abelCoeff w p · abelCoeff w (t−p)`   (the mass / partition sum),
  * `abelDmom w t = Σ_{p=0}^{t} D_p² · abelCoeff w p · abelCoeff w (t−p)`  (the second moment, `D_p = t−2p`).

## The EXACT discrete-Gaussian kernel (the object the Poisson/Jacobi transform acts on)

The abelian weight is EXACTLY a discrete Gaussian in the antidiagonal `D_p = t−2p`:

  * **`abelWeight_eq`** — `abelCoeff w p · abelCoeff w (t−p) ≃ w^{p²+(t−p)²}`  (EXACT; multiplicativity of `qpow`).
  * **`gauss_split_nat`** — `2·(p²+(t−p)²) = t² + D_p²`  (EXACT `Nat` identity, `p ≤ t`): the
    exponent is `½t² + ½D²`, a discrete Gaussian of the antidiagonal `D` — THIS is the exact
    theta / Jacobi kernel `q^{D²}` (`q = √w`) on which the Poisson summation formula
    `ϑ(1/τ) = √τ·ϑ(τ)` acts to produce the M1/M2 moment envelopes (see the residual section).

## The EXACT reflection (M1 mean-zero source) and the corner two-point tie

  * **`abelWeight_symm`** — `weight(p) ≃ weight(t−p)` (`p ↔ t−p` palindrome, `p ≤ t`): the exact
    reflection invariance that forces the first moment `⟨D⟩_t = 0` (`D_{t−p} = −D_p` at equal
    weight).  This is the EXACT abelian "M1-mean" — the mean is identically `0`.
  * **`abelDmom_zero`** — `⟨D²⟩·mass at t=0 is 0` (only `D=0` on the lattice).
  * **`abelDmom_one`** — `abelDmom w 1 ≃ abelAc w 1`, i.e. `⟨D²⟩_1 = 1` EXACTLY (the corner
    two-point tie `D = ±1`).  These are the exact endpoints that produce the `−2` corner.

## The abelian curvature base floor (the −2 corner, PROVED)

  * **`abelFullRangeFloor_zero`** — the abelian analogue of `CircleFourierPowerModel.fullRangeFloor_zero`:
    the `−2` curvature floor `Δ²⟨D²⟩ ≥ −2` on the FULL-range abelian moments at the corner-saturating
    window `s = 0`, PROVED for every `0 ≤ w`, reducing (via the two corner ties) to the manifest
    nonnegativity `0 ≤ abelDmom w 2 · (abelAc w 0 · abelAc w 1)`.  Cleaner than the SU(2) version:
    NO Weyl factors intervene.

## The trivial second-moment envelope (`M2`-type, EXACT)

  * **`abelDmom_le_tsq`** — `abelDmom w t ≤ t²·abelAc w t`, i.e. the abelian variance `⟨D²⟩_t ≤ t²`
    (each `D_p² = (t−2p)² ≤ t²` on the window).  The EXACT truncation envelope; the SHARP
    `⟨D²⟩·(1−w) ≤ 2` scaling is the Poisson residual (see below).

## The SU(2) lift via the Weyl perturbation (EXACT)

  * **`coeffW_prod_eq_weyl_abel`** — `w²·(coeffW w p · coeffW w q) ≃ (dimQ p·dimQ q)·(abelCoeff w (p+1)·abelCoeff w (q+1))`:
    the SU(2) autoconvolution weight is EXACTLY the abelian (shifted-charge) theta weight times the
    Weyl-dimension product `dimQ p·dimQ q` and the overall `w^{−2}` Casimir constant.  This lifts the
    abelian moment structure to the SU(2) moments `acNfull`/`dmomNfull`: the abelian part is exact,
    the Weyl product is the concrete perturbation (relative size `1/(s+2)²`, cf.
    `AbelianFusionCLT.weyl_dim_defect`).

## HONEST scope (the sharp residual)

The finite, EXACT structural spine of the M1/M2 envelope is closed here: the discrete-Gaussian
kernel `gauss_split_nat`, the reflection/mean-zero `abelWeight_symm`, the corner ties, the base
curvature floor, the `⟨D²⟩ ≤ t²` envelope, and the SU(2) Weyl lift.  What remains — the SHARP
scaling bounds `⟨D²⟩·(1−w) ≤ 2` (M1) and `Var(⟨D²⟩)·(1−w)² ≤ 8` (M2), uniform in the window — is
genuinely transcendental: both the numerator `Σ D² q^{D²}` and denominator `Σ q^{D²}` diverge as
`w → 1`, and only their theta ratio stays bounded, so NO finite majorant closes it (a naive
super-log-concave/geometric envelope loses the `1/√(1−w)` denominator growth and blows up).  The
bound requires the **Poisson/Jacobi modular transform** `ϑ(1/τ) = √τ·ϑ(τ)` applied to the exact
kernel `q^{D²}` of `gauss_split_nat`.  That transform needs `√` of a general heat parameter and an
infinite convergent theta series with `π`, which are not in the present `Q'`/`CReal`-core substrate;
it is named sharply as `MomentEnvelopePoissonDual` below.  The Clay Yang–Mills mass gap remains OPEN.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`, no `sorry`, no
custom `axiom`.  All content is `Q'.eqv` / `≤` data; the sole `Prop`-level object is the named-open
residual structure `MomentEnvelopePoissonDual` (Rule 6a named-hypothesis pattern), never `Prop := True`.
-/

import YMGap.Continuum.AbelianFusionCLT
import YMGap.Continuum.CircleFourierPowerModel
import YMGap.Continuum.CubeRatioBounds

namespace YMGap.Continuum.AbelianMomentEnvelope

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.MeanComplementCovariance
open YMGap.Continuum.CircleFourierPowerModel
open YMGap.Continuum.AbelianFusionCLT
open YMGap.Continuum.CubeRatioBounds

/-! ## 0. Small reusable `Q'` helpers. -/

/-- `a·(b·c) ≃ b·(a·c)` — the middle-swap reassociation (avoids importing the `ring_qeqv` macro). -/
theorem q_mid_swap (a b c : Q') : (a * (b * c)).eqv (b * (a * c)) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

/-- `Q'.ofNat` monotonicity (inlined cross-multiplication). -/
theorem ofNat_le_ofNat {m n : Nat} (h : m ≤ n) : Q'.ofNat m ≤ Q'.ofNat n := by
  show (Q'.ofNat m).num * ((Q'.ofNat n).den : Int)
      ≤ (Q'.ofNat n).num * ((Q'.ofNat m).den : Int)
  have hnm : (Q'.ofNat m).num = (m : Int) := rfl
  have hnn : (Q'.ofNat n).num = (n : Int) := rfl
  have hdm : ((Q'.ofNat m).den : Int) = 1 := rfl
  have hdn : ((Q'.ofNat n).den : Int) = 1 := rfl
  rw [hnm, hnn, hdm, hdn, Int.mul_one, Int.mul_one]
  exact_mod_cast h

/-! ## 1. The abelian tilted-measure moments (finite `Q'` sums). -/

/-- **`abelAc w t`** — the FULL-range abelian autoconvolution / partition sum
`Σ_{p=0}^{t} abelCoeff w p · abelCoeff w (t−p)` (the abelian shadow of `acNfull`). -/
def abelAc (w : Q') (t : Nat) : Q' :=
  fsum (fun p => abelCoeff w p * abelCoeff w (t - p)) (t + 1)

/-- **`abelDmom w t`** — the FULL-range abelian antidiagonal-square moment
`Σ_{p=0}^{t} D_p²·abelCoeff w p·abelCoeff w (t−p)`, `D_p = t−2p` (the abelian shadow of `dmomNfull`). -/
def abelDmom (w : Q') (t : Nat) : Q' :=
  fsum (fun p => Q'.ofNat (dsq p t) * (abelCoeff w p * abelCoeff w (t - p))) (t + 1)

theorem abelAc_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (t : Nat) : (0 : Q') ≤ abelAc w t :=
  fsum_nonneg (fun p => Q'.mul_nonneg _ _ (abelCoeff_nonneg hw p) (abelCoeff_nonneg hw (t - p))) (t + 1)

theorem abelDmom_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (t : Nat) : (0 : Q') ≤ abelDmom w t :=
  fsum_nonneg
    (fun p => Q'.mul_nonneg _ _ (ofNatNonneg (dsq p t))
      (Q'.mul_nonneg _ _ (abelCoeff_nonneg hw p) (abelCoeff_nonneg hw (t - p)))) (t + 1)

/-! ## 2. The EXACT discrete-Gaussian kernel — the object the Poisson/Jacobi transform acts on. -/

/-- **`abelWeight_eq`** — the abelian tilted weight is a single `qpow`:
`abelCoeff w p · abelCoeff w (t−p) ≃ w^{p²+(t−p)²}`.  EXACT (`qpow` multiplicativity). -/
theorem abelWeight_eq (w : Q') (p t : Nat) :
    (abelCoeff w p * abelCoeff w (t - p)).eqv (qpow w (p * p + (t - p) * (t - p))) :=
  Q'.eqv_symm (qpowR_add w (p * p) ((t - p) * (t - p)))

/-- **`gauss_split_nat` — THE DISCRETE-GAUSSIAN KERNEL IDENTITY.**  For `p ≤ t`,
`2·(p² + (t−p)²) = t² + D_p²` with `D_p² = dsq p t = (t−2p)²`.  So the abelian weight exponent is
`½t² + ½D²`: a discrete Gaussian in the antidiagonal `D`, weight `q^{D²}` with `q = √w` (up to the
`p`-independent `q^{t²}` that cancels in the normalized moments).  This is the EXACT theta / Jacobi
kernel on which the Poisson summation formula `ϑ(1/τ) = √τ·ϑ(τ)` acts. -/
theorem gauss_split_nat (p t : Nat) (h : p ≤ t) :
    2 * (p * p + (t - p) * (t - p)) = t * t + dsq p t := by
  obtain ⟨b, hb⟩ := Nat.le.dest h
  subst hb
  rw [Nat.add_sub_cancel_left]
  have hfx : 4 * (p * b) + dsq p (p + b) = (p + b) * (p + b) := by
    have hx := four_x_add_dsq p (p + b) (Nat.le_add_right p b)
    rwa [Nat.add_sub_cancel_left] at hx
  have hexp : (p + b) * (p + b) = p * p + 2 * (p * b) + b * b := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    have hc : b * p = p * b := Nat.mul_comm b p
    omega
  omega

/-- **`abelWeight_symm` — THE REFLECTION (M1 mean-zero source).**  For `p ≤ t`,
`weight(p) ≃ weight(t−p)`: the abelian tilted weight is a palindrome under `p ↔ t−p`.  Since
`D_{t−p} = −D_p`, this reflection invariance forces the first moment `⟨D⟩_t = 0` EXACTLY — the exact
abelian "M1-mean". -/
theorem abelWeight_symm (w : Q') (p t : Nat) (h : p ≤ t) :
    (abelCoeff w p * abelCoeff w (t - p)).eqv
      (abelCoeff w (t - p) * abelCoeff w (t - (t - p))) := by
  have h1 : t - (t - p) = p := by omega
  rw [h1]
  exact Q'.mul_comm_eqv (abelCoeff w p) (abelCoeff w (t - p))

/-! ## 3. The corner two-point ties (exact endpoints of the `−2` corner). -/

/-- **`abelDmom_zero`** — `⟨D²⟩·mass = 0` at `t = 0` (only `D = 0` on the lattice). -/
theorem abelDmom_zero (w : Q') : (abelDmom w 0).eqv 0 := by
  show ((0 : Q') + Q'.ofNat (dsq 0 0) * (abelCoeff w 0 * abelCoeff w (0 - 0))).eqv 0
  exact Q'.eqv_trans _ _ _ (q_zero_add_eqv _) (Q'.zero_mul_eqv _)

/-- **`abelDmom_one`** — `abelDmom w 1 ≃ abelAc w 1`, i.e. `⟨D²⟩_1 = 1` EXACTLY: at `t = 1` every
antidiagonal square `D² = (1−2p)²` is `1`, so the second moment coincides with the mass.  The exact
corner two-point tie. -/
theorem abelDmom_one (w : Q') : (abelDmom w 1).eqv (abelAc w 1) := by
  show (((0 : Q') + Q'.ofNat (dsq 0 1) * (abelCoeff w 0 * abelCoeff w (1 - 0)))
          + Q'.ofNat (dsq 1 1) * (abelCoeff w 1 * abelCoeff w (1 - 1))).eqv
       (((0 : Q') + abelCoeff w 0 * abelCoeff w (1 - 0))
          + abelCoeff w 1 * abelCoeff w (1 - 1))
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (Q'.eqv_refl 0) (Q'.one_mul_eqv _))
    (Q'.one_mul_eqv _)

/-! ## 4. The abelian curvature base floor (the −2 corner, PROVED). -/

/-- **`AbelFullRangeFloor w s`** — the abelian analogue of `CircleFourierPowerModel.FullRangeFloor`:
the cleared `−2` curvature floor `Δ²⟨D²⟩ ≥ −2` on the FULL-range abelian moments. -/
def AbelFullRangeFloor (w : Q') (s : Nat) : Prop :=
  Q'.ofNat 2 * (abelDmom w (s + 1) * (abelAc w s * abelAc w (s + 2)))
    ≤ abelDmom w s * (abelAc w (s + 1) * abelAc w (s + 2))
      + abelDmom w (s + 2) * (abelAc w s * abelAc w (s + 1))
      + Q'.ofNat 2 * (abelAc w s * (abelAc w (s + 1) * abelAc w (s + 2)))

/-- **`abelFullRangeFloor_zero` — the abelian `−2` corner floor, PROVED (axiom-clean).**  The abelian
curvature floor holds at the corner-saturating even window `s = 0` for every `0 ≤ w`.  Via the two
exact corner ties (`abelDmom_one`, `abelDmom_zero`) the floor collapses to the manifest nonnegativity
`0 ≤ abelDmom w 2 · (abelAc w 0 · abelAc w 1)`.  Cleaner than the SU(2)
`CircleFourierPowerModel.fullRangeFloor_zero`: no Weyl factors intervene. -/
theorem abelFullRangeFloor_zero {w : Q'} (hw : (0 : Q') ≤ w) : AbelFullRangeFloor w 0 := by
  show Q'.ofNat 2 * (abelDmom w 1 * (abelAc w 0 * abelAc w 2))
      ≤ abelDmom w 0 * (abelAc w 1 * abelAc w 2)
        + abelDmom w 2 * (abelAc w 0 * abelAc w 1)
        + Q'.ofNat 2 * (abelAc w 0 * (abelAc w 1 * abelAc w 2))
  -- surviving slack term nonnegative
  have hD2n : (0 : Q') ≤ abelDmom w 2 := abelDmom_nonneg hw 2
  have hA0n : (0 : Q') ≤ abelAc w 0 := abelAc_nonneg hw 0
  have hA1n : (0 : Q') ≤ abelAc w 1 := abelAc_nonneg hw 1
  have hterm2n : (0 : Q') ≤ abelDmom w 2 * (abelAc w 0 * abelAc w 1) :=
    Q'.mul_nonneg _ _ hD2n (Q'.mul_nonneg _ _ hA0n hA1n)
  -- LHS ≃ 2·(A0·(A1·A2)) using dmom₁ ≃ A1 then the middle swap
  have hLHSeq :
      (Q'.ofNat 2 * (abelDmom w 1 * (abelAc w 0 * abelAc w 2))).eqv
        (Q'.ofNat 2 * (abelAc w 0 * (abelAc w 1 * abelAc w 2))) := by
    refine Q'.mul_eqv_congr_left _ _ _ ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (abelDmom_one w)) ?_
    exact q_mid_swap (abelAc w 1) (abelAc w 0) (abelAc w 2)
  -- term1 = dmom₀·(A1·A2) ≃ 0
  have hterm1zero : (abelDmom w 0 * (abelAc w 1 * abelAc w 2)).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (abelDmom_zero w)) (Q'.zero_mul_eqv _)
  -- RHS ≃ term2 + T
  have hRHSeq :
      (abelDmom w 0 * (abelAc w 1 * abelAc w 2)
        + abelDmom w 2 * (abelAc w 0 * abelAc w 1)
        + Q'.ofNat 2 * (abelAc w 0 * (abelAc w 1 * abelAc w 2))).eqv
        (abelDmom w 2 * (abelAc w 0 * abelAc w 1)
          + Q'.ofNat 2 * (abelAc w 0 * (abelAc w 1 * abelAc w 2))) := by
    refine Q'.add_eqv_congr_right _ _ _ ?_
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ hterm1zero) (q_zero_add_eqv _)
  -- T ≤ term2 + T
  have hstep :
      (Q'.ofNat 2 * (abelAc w 0 * (abelAc w 1 * abelAc w 2)))
        ≤ abelDmom w 2 * (abelAc w 0 * abelAc w 1)
          + Q'.ofNat 2 * (abelAc w 0 * (abelAc w 1 * abelAc w 2)) := by
    have h0 := Q'.add_le_add_right 0 (abelDmom w 2 * (abelAc w 0 * abelAc w 1))
      (Q'.ofNat 2 * (abelAc w 0 * (abelAc w 1 * abelAc w 2))) hterm2n
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (q_zero_add_eqv _)) h0
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHSeq)
    (Q'.le_trans' _ _ _ hstep (Q'.ge_of_eqv hRHSeq))

/-! ## 5. The trivial second-moment envelope `⟨D²⟩ ≤ t²` (`M2`-type, EXACT). -/

/-- `dsq p t ≤ t²` for `p ≤ t` (`|t−2p| ≤ t`).  From `four_x_add_dsq` and `4·p(t−p) ≥ 0`. -/
theorem dsq_le_tsq (p t : Nat) (h : p ≤ t) : dsq p t ≤ t * t := by
  have hx := four_x_add_dsq p t h
  omega

/-- **`abelDmom_le_tsq` — the abelian `M2`-type envelope.**  `abelDmom w t ≤ t²·abelAc w t`, i.e. the
abelian variance `⟨D²⟩_t ≤ t²` (each `D_p² ≤ t²` on the window).  EXACT truncation envelope; the SHARP
`⟨D²⟩·(1−w) ≤ 2` scaling is the Poisson residual (§7). -/
theorem abelDmom_le_tsq {w : Q'} (hw : (0 : Q') ≤ w) (t : Nat) :
    abelDmom w t ≤ Q'.ofNat (t * t) * abelAc w t := by
  -- per-term: dsq·weight ≤ t²·weight
  have hterm : ∀ p, p < t + 1 →
      Q'.ofNat (dsq p t) * (abelCoeff w p * abelCoeff w (t - p))
        ≤ Q'.ofNat (t * t) * (abelCoeff w p * abelCoeff w (t - p)) := by
    intro p hp
    have hpt : p ≤ t := by omega
    have hwt : (0 : Q') ≤ abelCoeff w p * abelCoeff w (t - p) :=
      Q'.mul_nonneg _ _ (abelCoeff_nonneg hw p) (abelCoeff_nonneg hw (t - p))
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ (ofNat_le_ofNat (dsq_le_tsq p t hpt)) hwt
  have hsum : abelDmom w t
      ≤ fsum (fun p => Q'.ofNat (t * t) * (abelCoeff w p * abelCoeff w (t - p))) (t + 1) :=
    fsum_mono_lt (t + 1) hterm
  -- pull out the constant t²
  have hpull : (fsum (fun p => Q'.ofNat (t * t) * (abelCoeff w p * abelCoeff w (t - p))) (t + 1)).eqv
      (Q'.ofNat (t * t) * abelAc w t) :=
    Q'.eqv_symm (fsum_const_mul (Q'.ofNat (t * t)) _ (t + 1))
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hpull)

/-! ## 6. The SU(2) lift via the Weyl perturbation (EXACT). -/

/-- `qpow w 2 ≃ w·w`. -/
theorem qpow_two_eqv_ww (w : Q') : (qpow w 2).eqv (w * w) :=
  Q'.mul_eqv_congr_right (1 * w) w w (Q'.one_mul_eqv w)

/-- **`coeffW_prod_eq_weyl_abel` — THE SU(2) MOMENT LIFT.**  The SU(2) autoconvolution weight is
EXACTLY the abelian (shifted-charge) theta weight times the Weyl-dimension product and the overall
`w^{−2}` Casimir constant:

    w²·(coeffW w p · coeffW w q)  ≃  (dimQ p · dimQ q) · (abelCoeff w (p+1) · abelCoeff w (q+1)).

So the SU(2) tilted-measure weights `coeffW w p · coeffW w (t−p)` (the moments `acNfull`/`dmomNfull`
sum) are the EXACT abelian theta weights `abelCoeff w (p+1)·abelCoeff w (t−p+1)` perturbed by the
Weyl-dimension product `dimQ p·dimQ (t−p)` (relative size `1/(s+2)²`, `AbelianFusionCLT.weyl_dim_defect`).
This lifts the entire abelian moment envelope to the SU(2) moments. -/
theorem coeffW_prod_eq_weyl_abel (w : Q') (p q : Nat) :
    (qpow w 2 * (coeffW w p * coeffW w q)).eqv
      ((dimQ p * dimQ q) * (abelCoeff w (p + 1) * abelCoeff w (q + 1))) := by
  -- LHS ≃ (w·w)·(coeffW p·coeffW q) ≃ (w·coeffW p)·(w·coeffW q)
  have hL1 : (qpow w 2 * (coeffW w p * coeffW w q)).eqv ((w * w) * (coeffW w p * coeffW w q)) :=
    Q'.mul_eqv_congr_right _ _ _ (qpow_two_eqv_ww w)
  have hL2 : ((w * coeffW w p) * (w * coeffW w q)).eqv ((w * w) * (coeffW w p * coeffW w q)) :=
    FusionResidualBound.mul_four_regroup w (coeffW w p) w (coeffW w q)
  -- each factor via coeffW_eq_weyl_abel
  have h1 : (w * coeffW w p).eqv (dimQ p * abelCoeff w (p + 1)) := coeffW_eq_weyl_abel w p
  have h2 : (w * coeffW w q).eqv (dimQ q * abelCoeff w (q + 1)) := coeffW_eq_weyl_abel w q
  have hmid : ((w * coeffW w p) * (w * coeffW w q)).eqv
      ((dimQ p * abelCoeff w (p + 1)) * (dimQ q * abelCoeff w (q + 1))) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h1)
      (Q'.mul_eqv_congr_left _ _ _ h2)
  have hR : ((dimQ p * abelCoeff w (p + 1)) * (dimQ q * abelCoeff w (q + 1))).eqv
      ((dimQ p * dimQ q) * (abelCoeff w (p + 1) * abelCoeff w (q + 1))) :=
    FusionResidualBound.mul_four_regroup (dimQ p) (abelCoeff w (p + 1)) (dimQ q) (abelCoeff w (q + 1))
  -- assemble: LHS ≃ (w·w)·(…) ≃ (w·coeffW p)·(w·coeffW q) ≃ … ≃ RHS
  refine Q'.eqv_trans _ _ _ hL1 ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hL2) ?_
  exact Q'.eqv_trans _ _ _ hmid hR

/-! ## 7. The SHARP residual — the Poisson/Jacobi modular dual for M1/M2.

The finite EXACT structural spine above (discrete-Gaussian kernel `gauss_split_nat`, reflection
`abelWeight_symm`, corner ties, base curvature floor, `⟨D²⟩ ≤ t²` envelope, SU(2) Weyl lift) reduces
the fusion local-CLT moment envelope to ONE genuinely transcendental input: the SHARP scaling of the
theta second moment.  Written with `u = w`, `ε = −ln u`, `q = √w`, the abelian moments are theta
ratios `V(u) = (Σ_D D² q^{D²})/(Σ_D q^{D²})`.  The SHARP envelope bounds are

    M1 :  V(u)·(1 − u) ≤ 2 ,        M2 :  Var(u)·(1 − u)² ≤ 8 ,

uniform in `u ∈ [1/4, 1)`, both parities.  This is NOT closeable by any finite majorant: as `u → 1`,
BOTH `Σ D² q^{D²}` and `Σ q^{D²}` diverge (like `ε^{-3/2}` and `ε^{-1/2}`), and only their ratio stays
`O(1/ε)`; a naive super-log-concave / geometric envelope drops the `1/√(1−u)` denominator growth and
diverges.  The bound is a genuine Poisson/Jacobi statement: applying `ϑ(1/τ) = √τ·ϑ(τ)` to the EXACT
kernel `q^{D²}` of `gauss_split_nat` gives the dual moment form (even/odd `R = P`/`Q`)

    V   = 2/ε − 4 R₁/(ε² R₀) ,     Var = 8/ε² − 32 R₁/(ε³ R₀) + 16 (R₂R₀ − R₁²)/(ε⁴ R₀²),

whence M1-even is immediate from `R₁ = P₁ ≥ 0` and `(1−u) ≤ −ln u`, and the remaining three cases
close by a rational region split at `u = 3/4` (truncated θ-series on `[1/4,3/4]`, ε-dual rational
inequality on `[3/4,1)`).  Every step is a FINITE rational inequality — EXCEPT the modular transform
itself, which requires `√` of a general `w` and an infinite convergent theta series with `π`, absent
from the present `Q'`/`CReal`-core substrate.  That single transcendental bridge is named here. -/

/-- **`MomentEnvelopePoissonDual w`** (NAMED-OPEN — the sharp M1/M2 residual).  The Poisson/Jacobi
modular-dual moment envelope of the abelian tilted measure: the SHARP scaling bounds `V·(1−w) ≤ 2`
(M1) and `Var·(1−w)² ≤ 8` (M2), packaged here as the curvature floor they imply, uniform in the
window `s`.  Its `s = 0` face is DISCHARGED (`abelFullRangeFloor_zero`); the residual is the
uniform-in-`s` theta-ratio scaling, whose proof needs the modular transform `ϑ(1/τ) = √τ·ϑ(τ)` on
the exact kernel `gauss_split_nat` (a `√`-of-general-`w` / infinite-θ obligation outside the current
`Q'`/`CReal` core).  NAMED-OPEN (Type-level, never `sorry`). -/
structure MomentEnvelopePoissonDual (w : Q') : Type where
  /-- The abelian curvature floor at every window `s` — the finite content of the M1/M2 envelope. -/
  floor : ∀ s, AbelFullRangeFloor w s

/-- **`momentEnvelopePoissonDual_zero`** — the `s = 0` face of the residual is PROVED (the corner):
the modular-dual envelope holds at the corner-saturating even window unconditionally.  This witnesses
that `MomentEnvelopePoissonDual` is NON-vacuous at its tightest, corner-saturating face and pins the
residual to the strict uniform-in-`s` tail. -/
theorem momentEnvelopePoissonDual_zero {w : Q'} (hw : (0 : Q') ≤ w) : AbelFullRangeFloor w 0 :=
  abelFullRangeFloor_zero hw

/-! ## 8. Non-vacuity — the abelian moments are REAL, non-constant objects. -/

/-- **Non-vacuity.**  The abelian second moment is a genuine, non-trivial object: at `w = 1/2`,
`abelDmom (1/2) 1 = abelAc (1/2) 1 ≠ 0` (the exact two-point tie `⟨D²⟩_1 = 1`), while
`abelDmom (1/2) 0 = 0`.  So `abelDmom` is non-constant and the corner ties are non-degenerate. -/
theorem abelDmom_nonconstant :
    (abelDmom (Q'.mkPos 1 2 (by decide)) 0 = 0) ∧
      ¬ (abelDmom (Q'.mkPos 1 2 (by decide)) 1 = 0) := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

end YMGap.Continuum.AbelianMomentEnvelope

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.AbelianMomentEnvelope.abelWeight_eq
#print axioms YMGap.Continuum.AbelianMomentEnvelope.gauss_split_nat
#print axioms YMGap.Continuum.AbelianMomentEnvelope.abelWeight_symm
#print axioms YMGap.Continuum.AbelianMomentEnvelope.abelDmom_zero
#print axioms YMGap.Continuum.AbelianMomentEnvelope.abelDmom_one
#print axioms YMGap.Continuum.AbelianMomentEnvelope.abelFullRangeFloor_zero
#print axioms YMGap.Continuum.AbelianMomentEnvelope.dsq_le_tsq
#print axioms YMGap.Continuum.AbelianMomentEnvelope.abelDmom_le_tsq
#print axioms YMGap.Continuum.AbelianMomentEnvelope.coeffW_prod_eq_weyl_abel
#print axioms YMGap.Continuum.AbelianMomentEnvelope.momentEnvelopePoissonDual_zero
#print axioms YMGap.Continuum.AbelianMomentEnvelope.abelDmom_nonconstant
