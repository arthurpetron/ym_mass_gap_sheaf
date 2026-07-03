/-
Track B / local-CLT — the TILTED FIRST-MOMENT (mean-exponent) retarget of the fusion-window
`w`-monotonicity residual, with the PRECISE refutation of the competing per-coefficient PF₂/MLR
route and the genuine "mean-of-product = sum-of-means" engine that reduces the log-concavity-defect
monotonicity to a single first-moment convexity datum.

# What this module adds (read first — load-bearing honesty)

The single-window residual `FiniteSMarginWorstcase.CrossRatioMonotone w` is the two-point
cross-ratio `A_s(w)·M_s(wH) ≤ A_s(wH)·M_s(w)`, whose infinitesimal generator is the requirement
that the log-concavity-defect *ratio* `R(w) = A_s(w)/M_s(w)` be nondecreasing in `w`.  Writing
`⟨e⟩_P(w) = w·∂_w log P` for the tilted first moment (mean exponent) of a nonneg-coefficient
polynomial `P`, `R'(w) ≥ 0 ⟺ ⟨e⟩_{A_s} ≥ ⟨e⟩_{M_s}`; and since `A_s = acN_s·acN_{s+2}` (a product)
and `M_s = acN_{s+1}²` (a square), "mean of a product = sum of means" turns that into the MIDPOINT
CONVEXITY of the per-window mean `μ(t) = ⟨e⟩_{acN(s+1,t)}`:

    μ(s) + μ(s+2)  ≥  2·μ(s+1).                                   (`MeanExpConvex`)

This module PROVES the load-bearing "mean-of-product = sum-of-means" engine (`pfmom_split`) at full
generality, uses it to REDUCE `MeanExpConvex` to the first-moment gap `⟨e⟩_{A_s} ≥ ⟨e⟩_{M_s}`
(`AsMsFirstMomentGap`, PROVED reduction), and PRECISELY REFUTES the competing coefficient-array
PF₂/MLR route (`CrossRatioMonotone.ArrayMLR`) for the actual `s=1` arrays: the required
monotone-likelihood-ratio inequality is `24·9 = 216 ≤ 0·24 = 0`, which is FALSE (`noArrayMLR_A1M1`).

# What this module proves (all axiom-clean, `[propext]` / `[propext, Quot.sound]`)

  * `gmass`, `gfmom` — the evaluation (mass) and tilted first moment (mean × mass) of a
    grid-polynomial `Σ_k c_k w^{e_k}`.
  * `prodTerm_eq`, `pmass_eq` — evaluation is multiplicative on the product grid
    (`mass(P·Q) = mass(P)·mass(Q)`).
  * `pfmomTerm_eq`, `pfmom_split` — **THE ENGINE**: the tilted first moment is ADDITIVE under
    polynomial multiplication, `fmom(P·Q) = fmom(P)·mass(Q) + mass(P)·fmom(Q)` (the exact
    "mean-of-product = sum-of-means" identity that makes `MeanExpConvex` the log-concavity-defect
    monotonicity).
  * `coeffProd_eq`, `acN_eq_gmass`, `acnFmom_eq_gfmom` — the bridge realizing the diagonal-band
    autoconvolution `acN` and its tilted moment `acnFmom` as a grid-polynomial and its `gfmom`.
  * `acnProductFirstMoment` — the JUSTIFICATION: the product first moment of `acN_s·acN_{s+2}` is
    exactly `acnFmom_s·acN_{s+2} + acN_s·acnFmom_{s+2}` (engine `+` bridge), so the `fmom_A` used in
    the residuals is the genuine tilted first moment of `A_s`.
  * `midpointToGap`, `firstMomentGap_of_meanExpConvex` — **THE REDUCTION**: `MeanExpConvex w`
    inhabits `AsMsFirstMomentGap w` (multiply the midpoint numerator by `acN_{s+1} ≥ 0`).
  * `noArrayMLR_A1M1` — **THE REFUTATION**: the concrete `s=1` arrays of `A_1`, `M_1` admit NO
    `CrossRatioMonotone.ArrayMLR` witness (`216 ≤ 0` is false); the per-coefficient PF₂/MLR route is
    FALSE, not open, and must be retired from the critical path.
  * `windowAuto_zero_eq_acN`, `lineMass`, `lineFmom` — the shift-family (`n>1`) objects and the
    `r=0` single-window collapse.

# NAMED OPEN (Type-level structures, never `sorry`)

  * `MeanExpConvex w` — the single-window midpoint mean-convexity (the `w`-monotonicity of the
    log-concavity defect); numerically TRUE `∀ s`, `∀ w∈(0,1]`; its `w`-derivative is the tilted
    variance ⇒ a genuine local-CLT / Tate–Zelditch datum.
  * `AsMsFirstMomentGap w` — the first-moment gap `⟨e⟩_{A_s} ≥ ⟨e⟩_{M_s}` (the infinitesimal
    generator of `CrossRatioMonotone`); reduced FROM `MeanExpConvex` here.
  * `ShiftFamilyMeanConvex w n` — the `n>1` aggregate super-modularity (the shift-family analogue),
    whose `n=1` window is `MeanExpConvex`; the honest content of `LineSumLogConcaveCR` re-expressed
    as a first-moment convexity.
  * `MeanToCrossRatio w` — the sole analytic bridge left: integrate the pointwise first-moment gap
    over `[0,wH]` to the two-point `CrossRatioMonotone w` (the FTC / monotonicity step; genuinely
    true, not constructively cheap here).

# HONEST VERDICT

This is a correction + sharper relocation of one Core-B sub-fact: it RETIRES the (false)
per-coefficient PF₂/MLR route and RELOCATES the open content onto the aggregate first-moment
convexity `MeanExpConvex` / `ShiftFamilyMeanConvex`, supplying the genuine "mean-of-product =
sum-of-means" machinery and the PROVED reduction `MeanExpConvex ⟹ AsMsFirstMomentGap`.  It is a
reduction, NOT a closure.  The Clay Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and the reused finite-sum + power algebra (`fsum`, `fsum_add`,
`fsum_eqv_congr`, `fsum_mul_fsum`, `qpow_add`, `mul_swap4`, `ofNat_add_eqv`, `ofNat_two_mul_eqv`),
`acN` / `acN_nonneg`, `BakryEmery.mul_pos`, `HeatKernelRGStep.lt_of_lt_of_le`.  Every load-bearing
declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.CrossRatioMonotone
import YMGap.Continuum.AcNReserveAnalytic

namespace YMGap.Continuum.FusionMarginMonotone

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.FusionCoreStepRoundA
open YMGap.Continuum.FusionCoreStepRoundB
open YMGap.Continuum.FusionGenFunction
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.FiniteSMarginWorstcase
open YMGap.Continuum.CrossRatioMonotone

/-! ## 0. A small two-sided multiplicative congruence. -/

/-- **`mulCongr2`** — two-sided `eqv` congruence for `*` (compose the left/right congruences). -/
private theorem mulCongr2 {a a' b b' : Q'} (ha : a.eqv a') (hb : b.eqv b') :
    (a * b).eqv (a' * b') :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Grid-polynomial mass and tilted first moment -/

/-- **`gmass`** — the evaluation of the grid-polynomial `Σ_{k<L} c_k · w^{e_k}`. -/
def gmass (c : Nat → Q') (e : Nat → Nat) (w : Q') (L : Nat) : Q' :=
  fsum (fun k => c k * qpow w (e k)) L

/-- **`gfmom`** — the tilted first moment `Σ_{k<L} e_k · c_k · w^{e_k} = w·∂_w gmass` (the mean
exponent times the mass; `gfmom / gmass = ⟨e⟩`). -/
def gfmom (c : Nat → Q') (e : Nat → Nat) (w : Q') (L : Nat) : Q' :=
  fsum (fun k => Q'.ofNat (e k) * (c k * qpow w (e k))) L

/-! ## 2. Multiplicativity of the mass and additivity of the first moment (THE ENGINE) -/

/-- **`prodTerm_eq`** — the per-term product rearrangement
`(a_j·m_k)·w^{eA_j+eB_k} ≃ (a_j·w^{eA_j})·(m_k·w^{eB_k})` (`qpow_add` + `mul_swap4`). -/
theorem prodTerm_eq (w : Q') (a m : Nat → Q') (eA eB : Nat → Nat) (j k : Nat) :
    ((a j * m k) * qpow w (eA j + eB k)).eqv
      ((a j * qpow w (eA j)) * (m k * qpow w (eB k))) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (a j * m k) _ _
      (HeatKernelRGStep.qpow_add w (eA j) (eB k))) ?_
  exact mul_swap4 (a j) (m k) (qpow w (eA j)) (qpow w (eB k))

/-- **`pmass_eq`** — evaluation is multiplicative on the product grid:
`Σ_j Σ_k (a_j·m_k)·w^{eA_j+eB_k} ≃ gmass(a,eA)·gmass(m,eB)`. -/
theorem pmass_eq (w : Q') (a m : Nat → Q') (eA eB : Nat → Nat) (LA LB : Nat) :
    (fsum (fun j => fsum (fun k => (a j * m k) * qpow w (eA j + eB k)) LB) LA).eqv
      (gmass a eA w LA * gmass m eB w LB) := by
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr _ _
      (fun j => fsum_eqv_congr _ _ (fun k => prodTerm_eq w a m eA eB j k) LB) LA) ?_
  exact Q'.eqv_symm
    (fsum_mul_fsum (fun j => a j * qpow w (eA j)) (fun k => m k * qpow w (eB k)) LA LB)

/-- **`pfmomTerm_eq`** — the per-term first-moment split
`(eA_j+eB_k)·(a_j·m_k)·w^{eA_j+eB_k} ≃ (eA_j·U)·V + U·(eB_k·V)` with `U = a_j·w^{eA_j}`,
`V = m_k·w^{eB_k}` (`ofNat_add_eqv` distributes the exponent). -/
theorem pfmomTerm_eq (w : Q') (a m : Nat → Q') (eA eB : Nat → Nat) (j k : Nat) :
    (Q'.ofNat (eA j + eB k) * ((a j * m k) * qpow w (eA j + eB k))).eqv
      ((Q'.ofNat (eA j) * (a j * qpow w (eA j))) * (m k * qpow w (eB k))
        + (a j * qpow w (eA j)) * (Q'.ofNat (eB k) * (m k * qpow w (eB k)))) := by
  have h0 : ((a j * m k) * qpow w (eA j + eB k)).eqv
      ((a j * qpow w (eA j)) * (m k * qpow w (eB k))) := prodTerm_eq w a m eA eB j k
  have h1 : (Q'.ofNat (eA j + eB k)).eqv (Q'.ofNat (eA j) + Q'.ofNat (eB k)) :=
    Q'.ofNat_add_eqv (eA j) (eB k)
  have s1 : (Q'.ofNat (eA j + eB k) * ((a j * m k) * qpow w (eA j + eB k))).eqv
      ((Q'.ofNat (eA j) + Q'.ofNat (eB k))
        * ((a j * qpow w (eA j)) * (m k * qpow w (eB k)))) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (eA j + eB k)) _ _ h0)
      (Q'.mul_eqv_congr_right _ _ _ h1)
  have s2 := Q'.add_mul_eqv (Q'.ofNat (eA j)) (Q'.ofNat (eB k))
      ((a j * qpow w (eA j)) * (m k * qpow w (eB k)))
  have s3a : (Q'.ofNat (eA j) * ((a j * qpow w (eA j)) * (m k * qpow w (eB k)))).eqv
      ((Q'.ofNat (eA j) * (a j * qpow w (eA j))) * (m k * qpow w (eB k))) :=
    Q'.eqv_symm
      (Q'.mul_assoc_eqv (Q'.ofNat (eA j)) (a j * qpow w (eA j)) (m k * qpow w (eB k)))
  have s3b : (Q'.ofNat (eB k) * ((a j * qpow w (eA j)) * (m k * qpow w (eB k)))).eqv
      ((a j * qpow w (eA j)) * (Q'.ofNat (eB k) * (m k * qpow w (eB k)))) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (Q'.ofNat (eB k)) ((a j * qpow w (eA j)) * (m k * qpow w (eB k)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (a j * qpow w (eA j)) (m k * qpow w (eB k)) (Q'.ofNat (eB k))) ?_
    exact Q'.mul_eqv_congr_left (a j * qpow w (eA j)) _ _
      (Q'.mul_comm_eqv (m k * qpow w (eB k)) (Q'.ofNat (eB k)))
  exact Q'.eqv_trans _ _ _ s1 (Q'.eqv_trans _ _ _ s2 (Q'.add_eqv_congr' s3a s3b))

/-- **`pfmom`** — the tilted first moment of the product grid (the sum-of-products of `A` and `B`
weighted by the summed exponent). -/
def pfmom (w : Q') (a m : Nat → Q') (eA eB : Nat → Nat) (LA LB : Nat) : Q' :=
  fsum (fun j => fsum (fun k =>
    Q'.ofNat (eA j + eB k) * ((a j * m k) * qpow w (eA j + eB k))) LB) LA

/-- **`pfmom_split` — THE ENGINE: "mean of a product = sum of means".**  The tilted first moment is
ADDITIVE under polynomial multiplication:

    pfmom(A·B)  ≃  gfmom(A)·gmass(B)  +  gmass(A)·gfmom(B).

(`pfmomTerm_eq` per term; the double sum splits by `fsum_add` and each half is a product by
`fsum_mul_fsum`.)  This is the load-bearing identity that turns the log-concavity-defect
`w`-monotonicity into the per-window mean midpoint convexity `MeanExpConvex`. -/
theorem pfmom_split (w : Q') (a m : Nat → Q') (eA eB : Nat → Nat) (LA LB : Nat) :
    (pfmom w a m eA eB LA LB).eqv
      (gfmom a eA w LA * gmass m eB w LB + gmass a eA w LA * gfmom m eB w LB) := by
  have hterm : (pfmom w a m eA eB LA LB).eqv
      (fsum (fun j => fsum (fun k =>
        (Q'.ofNat (eA j) * (a j * qpow w (eA j))) * (m k * qpow w (eB k))
          + (a j * qpow w (eA j)) * (Q'.ofNat (eB k) * (m k * qpow w (eB k)))) LB) LA) :=
    fsum_eqv_congr _ _
      (fun j => fsum_eqv_congr _ _ (fun k => pfmomTerm_eq w a m eA eB j k) LB) LA
  have hsplit : (fsum (fun j => fsum (fun k =>
        (Q'.ofNat (eA j) * (a j * qpow w (eA j))) * (m k * qpow w (eB k))
          + (a j * qpow w (eA j)) * (Q'.ofNat (eB k) * (m k * qpow w (eB k)))) LB) LA).eqv
      (fsum (fun j => fsum (fun k =>
          (Q'.ofNat (eA j) * (a j * qpow w (eA j))) * (m k * qpow w (eB k))) LB) LA
        + fsum (fun j => fsum (fun k =>
          (a j * qpow w (eA j)) * (Q'.ofNat (eB k) * (m k * qpow w (eB k)))) LB) LA) := by
    refine Q'.eqv_trans _ _ _
      (fsum_eqv_congr _ _ (fun j =>
        fsum_add
          (fun k => (Q'.ofNat (eA j) * (a j * qpow w (eA j))) * (m k * qpow w (eB k)))
          (fun k => (a j * qpow w (eA j)) * (Q'.ofNat (eB k) * (m k * qpow w (eB k)))) LB) LA) ?_
    exact fsum_add
      (fun j => fsum (fun k =>
        (Q'.ofNat (eA j) * (a j * qpow w (eA j))) * (m k * qpow w (eB k))) LB)
      (fun j => fsum (fun k =>
        (a j * qpow w (eA j)) * (Q'.ofNat (eB k) * (m k * qpow w (eB k)))) LB) LA
  have hL : (fsum (fun j => fsum (fun k =>
        (Q'.ofNat (eA j) * (a j * qpow w (eA j))) * (m k * qpow w (eB k))) LB) LA).eqv
      (gfmom a eA w LA * gmass m eB w LB) :=
    Q'.eqv_symm (fsum_mul_fsum
      (fun j => Q'.ofNat (eA j) * (a j * qpow w (eA j)))
      (fun k => m k * qpow w (eB k)) LA LB)
  have hR : (fsum (fun j => fsum (fun k =>
        (a j * qpow w (eA j)) * (Q'.ofNat (eB k) * (m k * qpow w (eB k)))) LB) LA).eqv
      (gmass a eA w LA * gfmom m eB w LB) :=
    Q'.eqv_symm (fsum_mul_fsum
      (fun j => a j * qpow w (eA j))
      (fun k => Q'.ofNat (eB k) * (m k * qpow w (eB k))) LA LB)
  exact Q'.eqv_trans _ _ _ hterm
    (Q'.eqv_trans _ _ _ hsplit (Q'.add_eqv_congr' hL hR))

/-! ## 3. The `acN` bridge: realizing the diagonal-band autoconvolution as a grid-polynomial -/

/-- **`acnFmom`** — the tilted first moment (`w·∂_w`) of the diagonal-band autoconvolution
`acN w n t = Σ_{p<n} c_p·c_{t−p}`: each product monomial has exponent `C₄(p)+C₄(t−p)`. -/
def acnFmom (w : Q') (n t : Nat) : Q' :=
  fsum (fun p => Q'.ofNat (c4 p + c4 (t - p)) * (coeffW w p * coeffW w (t - p))) n

/-- **`coeffProd_eq`** — the coefficient-product rearrangement
`c_p·c_{t−p} ≃ (dimQ p·dimQ (t−p))·w^{C₄(p)+C₄(t−p)}` (`mul_swap4` + `qpow_add`). -/
theorem coeffProd_eq (w : Q') (p t : Nat) :
    (coeffW w p * coeffW w (t - p)).eqv
      ((dimQ p * dimQ (t - p)) * qpow w (c4 p + c4 (t - p))) := by
  unfold coeffW
  refine Q'.eqv_trans _ _ _
    (mul_swap4 (dimQ p) (qpow w (c4 p)) (dimQ (t - p)) (qpow w (c4 (t - p)))) ?_
  exact Q'.mul_eqv_congr_left (dimQ p * dimQ (t - p)) _ _
    (Q'.eqv_symm (HeatKernelRGStep.qpow_add w (c4 p) (c4 (t - p))))

/-- **`acN_eq_gmass`** — the autoconvolution is the mass of the grid-polynomial with coefficients
`dimQ p·dimQ (t−p)` and exponents `C₄(p)+C₄(t−p)`. -/
theorem acN_eq_gmass (w : Q') (n t : Nat) :
    (acN w n t).eqv
      (gmass (fun p => dimQ p * dimQ (t - p)) (fun p => c4 p + c4 (t - p)) w n) := by
  show (fsum (fun p => coeffW w p * coeffW w (t - p)) n).eqv
      (fsum (fun p => (dimQ p * dimQ (t - p)) * qpow w (c4 p + c4 (t - p))) n)
  exact fsum_eqv_congr _ _ (fun p => coeffProd_eq w p t) n

/-- **`acnFmom_eq_gfmom`** — the tilted first moment of `acN` is the `gfmom` of the same grid. -/
theorem acnFmom_eq_gfmom (w : Q') (n t : Nat) :
    (acnFmom w n t).eqv
      (gfmom (fun p => dimQ p * dimQ (t - p)) (fun p => c4 p + c4 (t - p)) w n) := by
  show (fsum (fun p => Q'.ofNat (c4 p + c4 (t - p)) * (coeffW w p * coeffW w (t - p))) n).eqv
      (fsum (fun p => Q'.ofNat (c4 p + c4 (t - p))
        * ((dimQ p * dimQ (t - p)) * qpow w (c4 p + c4 (t - p)))) n)
  exact fsum_eqv_congr _ _
    (fun p => Q'.mul_eqv_congr_left (Q'.ofNat (c4 p + c4 (t - p))) _ _ (coeffProd_eq w p t)) n

/-- **`acnProductFirstMoment` — the JUSTIFICATION.**  The product first moment of `A_s =
acN_s·acN_{s+2}` is exactly `acnFmom_s·acN_{s+2} + acN_s·acnFmom_{s+2}` (`pfmom_split` transported
across the `acN`/`acnFmom` bridge).  Hence the `fmom_A` used in the residuals below is the genuine
tilted first moment of the product polynomial `A_s`. -/
theorem acnProductFirstMoment (w : Q') (s : Nat) :
    (pfmom w (fun p => dimQ p * dimQ (s - p)) (fun p => dimQ p * dimQ ((s + 2) - p))
        (fun p => c4 p + c4 (s - p)) (fun p => c4 p + c4 ((s + 2) - p)) (s + 1) (s + 1)).eqv
      (acnFmom w (s + 1) s * acN w (s + 1) (s + 2)
        + acN w (s + 1) s * acnFmom w (s + 1) (s + 2)) := by
  refine Q'.eqv_trans _ _ _ (pfmom_split w _ _ _ _ (s + 1) (s + 1)) ?_
  exact Q'.add_eqv_congr'
    (mulCongr2 (Q'.eqv_symm (acnFmom_eq_gfmom w (s + 1) s))
      (Q'.eqv_symm (acN_eq_gmass w (s + 1) (s + 2))))
    (mulCongr2 (Q'.eqv_symm (acN_eq_gmass w (s + 1) s))
      (Q'.eqv_symm (acnFmom_eq_gfmom w (s + 1) (s + 2))))

/-! ## 4. The named residuals -/

/-- **`MeanExpConvex w`** — the single-window MIDPOINT MEAN-CONVEXITY (`μ(s)+μ(s+2) ≥ 2μ(s+1)` for
`μ(t) = acnFmom_t/acN_t`), cleared of denominators by `acN_s·acN_{s+2}·acN_{s+1}`:

    2·(acnFmom_{s+1}·(acN_s·acN_{s+2}))
      ≤ (acnFmom_s·acN_{s+2} + acN_s·acnFmom_{s+2})·acN_{s+1}.

This is EXACTLY `w·∂_w`(log-concavity defect) `≥ 0` — the `w`-monotonicity of the log-concavity
defect ratio; its `w`-derivative is the tilted variance (a local-CLT / Tate–Zelditch datum).
NAMED-OPEN (never `sorry`). -/
structure MeanExpConvex (w : Q') : Type where
  mec : ∀ s,
    Q'.ofNat 2 * (acnFmom w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2)))
      ≤ (acnFmom w (s + 1) s * acN w (s + 1) (s + 2)
          + acN w (s + 1) s * acnFmom w (s + 1) (s + 2))
        * acN w (s + 1) (s + 1)

/-- **`AsMsFirstMomentGap w`** — the first-moment gap `⟨e⟩_{A_s} ≥ ⟨e⟩_{M_s}` in cross-multiplied
form, with `fmom_A = acnFmom_s·acN_{s+2} + acN_s·acnFmom_{s+2}` (the product first moment,
justified by `acnProductFirstMoment`), `mass_A = acN_s·acN_{s+2}`, `fmom_M = acnFmom_{s+1}·acN_{s+1}
+ acN_{s+1}·acnFmom_{s+1}`, `mass_M = acN_{s+1}²`:

    fmom_M·mass_A  ≤  fmom_A·mass_M.

This is the infinitesimal generator of `CrossRatioMonotone`.  NAMED-OPEN. -/
structure AsMsFirstMomentGap (w : Q') : Type where
  fmg : ∀ s,
    (acnFmom w (s + 1) (s + 1) * acN w (s + 1) (s + 1)
        + acN w (s + 1) (s + 1) * acnFmom w (s + 1) (s + 1))
        * (acN w (s + 1) s * acN w (s + 1) (s + 2))
      ≤ (acnFmom w (s + 1) s * acN w (s + 1) (s + 2)
          + acN w (s + 1) s * acnFmom w (s + 1) (s + 2))
        * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 1))

/-! ## 5. The reduction `MeanExpConvex ⟹ AsMsFirstMomentGap` -/

/-- **`midpointToGap` — the pure-`Q'` algebra core of the reduction.**  From the midpoint-convexity
numerator `2·(Rf·(P·Qc)) ≤ (Pf·Qc + P·Qf)·R` with `0 ≤ R`, multiply both sides by `R` and rearrange
(the extra factor `R` turns the single-window mean convexity into the `A_s`/`M_s` first-moment gap):

    (Rf·R + R·Rf)·(P·Qc)  ≤  (Pf·Qc + P·Qf)·(R·R). -/
theorem midpointToGap {P Qc R Pf Qf Rf : Q'} (hR : (0 : Q') ≤ R)
    (h : Q'.ofNat 2 * (Rf * (P * Qc)) ≤ (Pf * Qc + P * Qf) * R) :
    (Rf * R + R * Rf) * (P * Qc) ≤ (Pf * Qc + P * Qf) * (R * R) := by
  have hstep := Q'.mul_le_mul_of_nonneg_right _ _ R h hR
  -- eqvBR : ((Pf·Qc+P·Qf)·R)·R ≃ (Pf·Qc+P·Qf)·(R·R)
  have eqvBR : (((Pf * Qc + P * Qf) * R) * R).eqv ((Pf * Qc + P * Qf) * (R * R)) :=
    Q'.mul_assoc_eqv (Pf * Qc + P * Qf) R R
  -- eqvLA : (Rf·R + R·Rf)·(P·Qc) ≃ (2·(Rf·(P·Qc)))·R
  have e2 : ((Rf * R) * (P * Qc)).eqv ((Rf * (P * Qc)) * R) :=
    Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv Rf R (P * Qc))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left Rf (R * (P * Qc)) ((P * Qc) * R) (Q'.mul_comm_eqv R (P * Qc)))
        (Q'.eqv_symm (Q'.mul_assoc_eqv Rf (P * Qc) R)))
  have e3 : ((R * Rf) * (P * Qc)).eqv ((Rf * (P * Qc)) * R) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (R * Rf) (Rf * R) (P * Qc) (Q'.mul_comm_eqv R Rf)) e2
  have e1 : ((Rf * R + R * Rf) * (P * Qc)).eqv
      ((Rf * R) * (P * Qc) + (R * Rf) * (P * Qc)) :=
    Q'.add_mul_eqv (Rf * R) (R * Rf) (P * Qc)
  have e4 : (((Rf * (P * Qc)) * R) + ((Rf * (P * Qc)) * R)).eqv
      ((Q'.ofNat 2 * (Rf * (P * Qc))) * R) :=
    Q'.eqv_symm (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ R (ofNat_two_mul_eqv (Rf * (P * Qc))))
      (Q'.add_mul_eqv (Rf * (P * Qc)) (Rf * (P * Qc)) R))
  have eqvLA : ((Rf * R + R * Rf) * (P * Qc)).eqv ((Q'.ofNat 2 * (Rf * (P * Qc))) * R) :=
    Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' e2 e3) e4)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eqvLA)
    (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv eqvBR))

/-- **`firstMomentGap_of_meanExpConvex` — THE REDUCTION.**  A `MeanExpConvex w` witness (with
`0 ≤ w`) inhabits `AsMsFirstMomentGap w`: apply `midpointToGap` per mode with `0 ≤ acN_{s+1}`
(`acN_nonneg`).  This is the honest reduction of the single-window log-concavity-defect
`w`-monotonicity to the first-moment gap. -/
def firstMomentGap_of_meanExpConvex {w : Q'} (hw : (0 : Q') ≤ w)
    (H : MeanExpConvex w) : AsMsFirstMomentGap w where
  fmg := fun s => midpointToGap (acN_nonneg hw (s + 1) (s + 1)) (H.mec s)

/-! ## 6. The precise refutation of the coefficient-array PF₂/MLR route -/

/-- **`aA1`** — the coefficient array of `A_1(w) = 24·w¹⁴ + 16·w¹⁸` on the common grid
`{12,14,16,18}` (`k ↦ 12+2k`): `a₁ = 24` (exp 14), `a₃ = 16` (exp 18), else `0`. -/
def aA1 : Nat → Q' := fun k => if k = 1 then Q'.ofNat 24 else if k = 3 then Q'.ofNat 16 else 0

/-- **`mM1`** — the coefficient array of `M_1(w) = 16·w¹² + 24·w¹⁴ + 9·w¹⁶`: `m₀ = 16`, `m₁ = 24`,
`m₂ = 9`, else `0`. -/
def mM1 : Nat → Q' :=
  fun k => if k = 0 then Q'.ofNat 16 else if k = 1 then Q'.ofNat 24
    else if k = 2 then Q'.ofNat 9 else 0

/-- **`eGrid`** — the common exponent grid `k ↦ 12+2k` (`{12,14,16,18}`). -/
def eGrid : Nat → Nat := fun k => 12 + 2 * k

/-- **`noArrayMLR_A1M1` — THE REFUTATION.**  The concrete `s=1` arrays of `A_1`, `M_1` admit NO
`CrossRatioMonotone.ArrayMLR` witness.  Root cause: the Casimir-gap `C₄(s)=s(s+2)` gives `A_1`, `M_1`
MISMATCHED interleaved supports, so the monotone-likelihood-ratio inequality at `e_k = 14 < e_j = 16`
demands `a₁₄·m₁₆ ≤ a₁₆·m₁₄`, i.e. `24·9 = 216 ≤ 0·24 = 0`, which is FALSE.  The per-coefficient
PF₂/MLR route is thus FALSE (not open) and must be retired from the critical path in favor of the
aggregate first-moment datum `MeanExpConvex`. -/
theorem noArrayMLR_A1M1 (H : ArrayMLR aA1 mM1 eGrid) : False := by
  have hlt : eGrid 1 < eGrid 2 := by decide
  have hle := H.mlr 2 1 hlt
  rw [show aA1 1 = Q'.ofNat 24 from rfl, show mM1 2 = Q'.ofNat 9 from rfl,
      show aA1 2 = (0 : Q') from rfl] at hle
  have hle0 : Q'.ofNat 24 * Q'.ofNat 9 ≤ 0 :=
    Q'.le_trans' _ _ _ hle (Q'.le_of_eqv (Q'.zero_mul_eqv (mM1 1)))
  have hpos : (0 : Q') < Q'.ofNat 24 * Q'.ofNat 9 :=
    BakryEmery.mul_pos (by decide) (by decide)
  exact absurd (HeatKernelRGStep.lt_of_lt_of_le hpos hle0) (by decide)

/-! ## 7. The shift-family (`n>1`) aggregate objects and the single-window collapse -/

/-- **`windowAutoL w s r`** — the windowed autoconvolution `Σ_{p≤s} c_{p+r}·c_{(s−p)+r}` (the
shift-`r` window of the line-sum; the `r=0` window is `acN w (s+1) s`). -/
def windowAutoL (w : Q') (s r : Nat) : Q' :=
  fsum (fun p => coeffW w (p + r) * coeffW w ((s - p) + r)) (s + 1)

/-- **`windowFmom w s r`** — the tilted first moment of `windowAutoL w s r`. -/
def windowFmom (w : Q') (s r : Nat) : Q' :=
  fsum (fun p => Q'.ofNat (c4 (p + r) + c4 ((s - p) + r))
    * (coeffW w (p + r) * coeffW w ((s - p) + r))) (s + 1)

/-- **`lineMass w n s`** — the antidiagonal line-sum `Σ_{r<n} windowAutoL w s r` (the shift-family
sum whose log-concavity is `LineSumLogConcaveCR`). -/
def lineMass (w : Q') (n s : Nat) : Q' := fsum (fun r => windowAutoL w s r) n

/-- **`lineFmom w n s`** — the aggregate tilted first moment `Σ_{r<n} windowFmom w s r`. -/
def lineFmom (w : Q') (n s : Nat) : Q' := fsum (fun r => windowFmom w s r) n

/-- **`windowAuto_zero_eq_acN`** — the `r=0` window IS the diagonal-band autoconvolution:
`windowAutoL w s 0 = acN w (s+1) s` (definitional, `p+0 = p`).  Hence the `n=1` shift-family
collapses to the single-window chain, so `ShiftFamilyMeanConvex w 1` is the aggregate lift of
`MeanExpConvex w`. -/
theorem windowAuto_zero_eq_acN (w : Q') (s : Nat) : windowAutoL w s 0 = acN w (s + 1) s := rfl

/-- **`ShiftFamilyMeanConvex w n`** — the `n>1` AGGREGATE SUPER-MODULARITY: the midpoint convexity
of the shift-family aggregate mean `M(s) = lineFmom_n(s)/lineMass_n(s)`, cleared of denominators:

    2·(lineFmom_{s+1}·(lineMass_s·lineMass_{s+2}))
      ≤ (lineFmom_s·lineMass_{s+2} + lineMass_s·lineFmom_{s+2})·lineMass_{s+1}.

Its `n=1` window is `MeanExpConvex` (via `windowAuto_zero_eq_acN`); for `n>1` it carries genuine
cross-shift covariance (a SUM of tilted means is not the tilted mean of the SUM), so it is the honest
super-modular content of `LineSumLogConcaveCR`, not per-`r` log-concavity.  NAMED-OPEN. -/
structure ShiftFamilyMeanConvex (w : Q') (n : Nat) : Type where
  smc : ∀ s,
    Q'.ofNat 2 * (lineFmom w n (s + 1) * (lineMass w n s * lineMass w n (s + 2)))
      ≤ (lineFmom w n s * lineMass w n (s + 2) + lineMass w n s * lineFmom w n (s + 2))
        * lineMass w n (s + 1)

/-! ## 8. The sole remaining analytic bridge -/

/-- **`MeanToCrossRatio w`** — the sole analytic step between the pointwise first-moment gap and the
two-point `CrossRatioMonotone w`: if the first-moment gap `AsMsFirstMomentGap w'` holds for every
`w' ∈ [0, wH]`, then `R(w) = A_s(w)/M_s(w)` is nondecreasing on `[0,wH]`, i.e.
`CrossRatioMonotone w` holds.  This is the fundamental-theorem-of-calculus / monotonicity-from-
nonnegative-derivative step — genuinely true, but not constructively cheap for these polynomials
without a spacing-uniform modulus.  NAMED-OPEN (never `sorry`). -/
structure MeanToCrossRatio (w : Q') : Type where
  integrate :
    (∀ w', (0 : Q') ≤ w' → w' ≤ wH → AsMsFirstMomentGap w') → CrossRatioMonotone w

/-! ## 9. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `prodTerm_eq`, `pmass_eq` — evaluation is multiplicative on the product grid.
  * `pfmomTerm_eq`, `pfmom_split` — THE ENGINE: first-moment additivity (mean-of-product =
    sum-of-means).
  * `coeffProd_eq`, `acN_eq_gmass`, `acnFmom_eq_gfmom`, `acnProductFirstMoment` — the `acN` bridge
    and the justification of `fmom_A` as the genuine product first moment.
  * `midpointToGap`, `firstMomentGap_of_meanExpConvex` — THE REDUCTION `MeanExpConvex ⟹
    AsMsFirstMomentGap`.
  * `noArrayMLR_A1M1` — THE REFUTATION: the per-coefficient PF₂/MLR route is FALSE for the actual
    `s=1` arrays (`216 ≤ 0`).
  * `windowAuto_zero_eq_acN` — the `n=1` single-window collapse of the shift family.

NAMED OPEN (Type-level structure, never `sorry`):
  * `MeanExpConvex w` — the single-window midpoint mean-convexity (the `w`-monotonicity of the
    log-concavity defect; a tilted-variance / local-CLT datum).
  * `AsMsFirstMomentGap w` — the first-moment gap (reduced FROM `MeanExpConvex`).
  * `ShiftFamilyMeanConvex w n` — the `n>1` aggregate super-modularity (honest content of
    `LineSumLogConcaveCR`).
  * `MeanToCrossRatio w` — the FTC/monotonicity integration to the two-point `CrossRatioMonotone`.

HONEST VERDICT.  This module RETIRES the (false) per-coefficient PF₂/MLR route and RELOCATES the open
content onto the aggregate first-moment convexity, supplying the genuine "mean-of-product =
sum-of-means" engine and the PROVED reduction `MeanExpConvex ⟹ AsMsFirstMomentGap`.  It is a
reduction + refutation + reusable machinery, NOT a closure.  The Clay Yang–Mills mass gap remains
OPEN. -/

end YMGap.Continuum.FusionMarginMonotone

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusionMarginMonotone.prodTerm_eq
#print axioms YMGap.Continuum.FusionMarginMonotone.pmass_eq
#print axioms YMGap.Continuum.FusionMarginMonotone.pfmomTerm_eq
#print axioms YMGap.Continuum.FusionMarginMonotone.pfmom_split
#print axioms YMGap.Continuum.FusionMarginMonotone.coeffProd_eq
#print axioms YMGap.Continuum.FusionMarginMonotone.acN_eq_gmass
#print axioms YMGap.Continuum.FusionMarginMonotone.acnFmom_eq_gfmom
#print axioms YMGap.Continuum.FusionMarginMonotone.acnProductFirstMoment
#print axioms YMGap.Continuum.FusionMarginMonotone.midpointToGap
#print axioms YMGap.Continuum.FusionMarginMonotone.firstMomentGap_of_meanExpConvex
#print axioms YMGap.Continuum.FusionMarginMonotone.noArrayMLR_A1M1
#print axioms YMGap.Continuum.FusionMarginMonotone.windowAuto_zero_eq_acN
