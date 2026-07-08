/-
# The CONSTRUCTIVE Jacobi ϑ₃ SERIES over `CReal` (`ϑ₃(q) = Σ_{n∈ℤ} q^{n²}`)

This module builds the genuine **series** realisation of the Jacobi theta function
`ϑ₃(q) = Σ_{n∈ℤ} q^{n²} = 1 + 2·Σ_{n≥1} q^{n²}` as a convergent `CReal` with an
EXPLICIT geometric convergence modulus, for every rational nome `q ∈ (0,1)`.

## Why this object (the moment-envelope bridge)

`AbelianMomentEnvelope.gauss_split_nat` shows the abelian tilted weight is EXACTLY the
discrete-Gaussian kernel `q^{D²}` (`q = √w`, `D` the antidiagonal).  The sharp M1/M2
moment envelopes `V·(1−w) ≤ 2`, `Var·(1−w)² ≤ 8` (`MomentEnvelopePoissonDual`) are theta
ratios `(Σ_D D² q^{D²})/(Σ_D q^{D²})`.  Their uniform-in-window control is the
Poisson/Jacobi modular inversion `ϑ₃(1/τ) = √τ·ϑ₃(τ)`.  Before that transform can even be
STATED as a `CReal` equality one needs the θ-**series** `Σ_n q^{n²}` as a genuine `CReal`
object.  The repo previously had only the theta **product** (`ThetaConv.thetaConvCReal`,
the Jacobi-triple-product form `∏(1−a^{2k+2})(1+2a^{2k+1}x+a^{4k+2})`); the **series**
`Σ q^{n²}` — the object the modular transform acts on — was absent.  This module supplies
it, over the project's `Q'`/`CReal` core, with a real Cauchy modulus.

## What is genuinely built here (axiom-clean, non-vacuous)

  * `thetaHalf q N = Σ_{n=1}^{N} q^{n²}` and `thetaPartial q N = 1 + 2·thetaHalf q N`
    (the symmetric partial sum `Σ_{|n|≤N} q^{n²}`), plain finite `Q'` sums.
  * `thetaS q hq0 hq1 : CReal` — the convergent series, built through the general-base
    geometric-limit engine `HKConvGen.crealOfGeoIncrementBase` at decay base `r = q²`.
    The single-step increment `2·q^{(N+1)²}` is dominated by `geoIncrBase (2q) q² N`
    because `q^{(N+1)²} ≤ q^{2N+1} = q·(q²)^N` (super-geometric decay of the Gaussian
    kernel; `(N+1)² ≥ 2N+1`).  `thetaS_approx : approx N = thetaPartial q N` (the genuine
    finite truncation); the Cauchy modulus is the base-`q²` telescoped tail.
  * `thetaS_geRat_one : ϑ₃(q) ≥ 1` (the `n=0` term; a genuine, non-vacuous lower bound),
    hence `thetaS_geRat_zero : ϑ₃(q) ≥ 0`.
  * §3b — the **two-sided modular bracket at the SUM level** (no Poisson, no integration):
    `thetaS_geRat_partial` (`ϑ₃ ≥` every partial sum), the load-bearing DIVERGENCE lower
    bound `thetaS_geRat_count : ϑ₃(q) ≥ 1 + 2N·q^{N²}` (choosing `N ∼ 1/√(−ln q)` gives
    `∼ 1/√(1−q) → ∞`, the denominator growth), and the matching geometric upper leg
    `thetaHalf_le_geom`.  Derived from the counting / `pow_base_antitone` domination alone.

## CONSUMER SCHEMA — bounds, NOT the exact identity (see `docs/theta_inversion.md`)

The object that actually consumes the theta transform is the curvature envelope
`R1CurvatureEnvelope.CurvatureEnvelope` (equivalently `AbelFullRangeFloor`):
`Δ²V(s)+2 ≥ (144/25)·w²(1−w²)`.  Its binding face `s=0` is an EXACT perfect square
(proved); the residual is the uniform tail `s ≥ 7`, whose true infimum ratio is
`≥ 7.96` against the required `144/25 = 5.76` — a uniform multiplicative margin `≈ 1.38×`.
Therefore the tail does NOT need the EXACT modular identity `ϑ₃(1/τ)=√τ·ϑ₃(τ)`; TWO-SIDED
bounds `c₁√τ·ϑ₃(τ) ≤ ϑ₃(1/τ) ≤ c₂√τ·ϑ₃(τ)` with looseness under `1.38` suffice.  §3b builds
the sum-level bracket; its lower constant (`2/e ≈ 0.74` of the sharp `√(π/ε)`) is a factor
`≈ 2` loose, i.e. NOT yet inside the `1.38` window — so it SHARPENS the residual from
"exact identity" to "near-sharp two-sided theta bound (constant within `1.38`)".

## HONEST scope (the sharp residual)

This module builds the SERIES object, its convergence modulus, and the sum-level two-sided
bracket.  It does **not** prove the modular inversion `ϑ₃(1/τ) = √τ·ϑ₃(τ)` nor a two-sided
bound tight to within `1.38` in the `q → 1` regime: the sharp constant `√(π/ε)` is the
genuine remaining input (obtainable via the integral test / Gaussian value — the flagged
integration — or a `q → 1` triple-product estimate the codebase does not yet carry; the
existing `ThetaConv.thetaConvCReal` only covers `q ≤ 1/16`).  Consequently
`MomentEnvelopePoissonDual` (`AbelianMomentEnvelope`) and the fusion local-CLT `hlocalize`
remain OPEN, now narrowed to the near-sharp two-sided theta bound.  The Clay Yang–Mills
mass gap remains OPEN.

## Axiom gate (AGENTS.md Rule 1 / Rule 8)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`, no
`sorry`, no custom `axiom`, no `Prop := True`.  All content is `Q'`/`CReal` data.
-/

import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.AbelianMomentEnvelope

namespace YMGap.Continuum.JacobiModularCReal

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.HKConv
open YMGap.Continuum.HKConvGen
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.MeanComplementCovariance

/-! ## 0. The finite partial sums. -/

/-- `thetaHalf q N = Σ_{i<N} q^{(i+1)²} = Σ_{n=1}^{N} q^{n²}` — the positive half of the
theta series. -/
def thetaHalf (q : Q') (N : Nat) : Q' := fsum (fun i => q ^ ((i + 1) * (i + 1))) N

/-- `thetaPartial q N = 1 + 2·Σ_{n=1}^{N} q^{n²} = Σ_{|n|≤N} q^{n²}` — the symmetric
partial sum of `ϑ₃(q)`. -/
def thetaPartial (q : Q') (N : Nat) : Q' := 1 + Q'.ofNat 2 * thetaHalf q N

theorem thetaHalf_nonneg {q : Q'} (hq : (0 : Q') ≤ q) (N : Nat) :
    (0 : Q') ≤ thetaHalf q N :=
  fsum_nonneg (fun i => Q'.pow_nonneg q hq ((i + 1) * (i + 1))) N

/-- Every symmetric partial sum is `≥ 1` (the `n=0` term). -/
theorem thetaPartial_ge_one {q : Q'} (hq : (0 : Q') ≤ q) (N : Nat) :
    (1 : Q') ≤ thetaPartial q N := by
  show (1 : Q') ≤ 1 + Q'.ofNat 2 * thetaHalf q N
  exact Q'.add_le_self_of_nonneg 1 _
    (Q'.mul_nonneg _ _ (ofNatNonneg 2) (thetaHalf_nonneg hq N))

/-- `thetaPartial q (l+1) ≃ thetaPartial q l + 2·q^{(l+1)²}` — the single-step increment. -/
theorem thetaPartial_succ (q : Q') (l : Nat) :
    (thetaPartial q (l + 1)).eqv
      (thetaPartial q l + Q'.ofNat 2 * q ^ ((l + 1) * (l + 1))) := by
  -- thetaHalf (l+1) = thetaHalf l + q^{(l+1)²}  (fsum_succ, definitional)
  show (1 + Q'.ofNat 2 * (thetaHalf q l + q ^ ((l + 1) * (l + 1)))).eqv
       ((1 + Q'.ofNat 2 * thetaHalf q l) + Q'.ofNat 2 * q ^ ((l + 1) * (l + 1)))
  -- 2·(A + t) ≃ 2·A + 2·t
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left 1 _ _
      (Q'.mul_add_eqv (Q'.ofNat 2) (thetaHalf q l) (q ^ ((l + 1) * (l + 1))))) ?_
  -- 1 + (2A + 2t) ≃ (1 + 2A) + 2t
  exact Q'.eqv_symm
    (Q'.add_assoc_eqv 1 (Q'.ofNat 2 * thetaHalf q l) (Q'.ofNat 2 * q ^ ((l + 1) * (l + 1))))

/-! ## 1. `q² < 1` and the geometric increment domination. -/

/-- `q² < 1` for `0 < q < 1` (`q² ≤ q < 1`). -/
theorem q2_lt_one {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) : q ^ 2 < (1 : Q') :=
  Q'.lt_of_le_of_lt
    (HKPos.pow_succ_le_self (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) 1) hq1

/-- `((q²)^l) ≃ q^{2l}` (power-of-a-power over `Q'`). -/
theorem q2pow_eqv (q : Q') (l : Nat) : ((q ^ 2) ^ l).eqv (q ^ (2 * l)) := by
  induction l with
  | zero => exact Q'.eqv_refl _
  | succ l ih =>
      show ((q ^ 2) * (q ^ 2) ^ l).eqv (q ^ (2 * (l + 1)))
      have hidx : 2 * (l + 1) = 2 + 2 * l := by omega
      rw [hidx]
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (q ^ 2) _ _ ih) ?_
      exact Q'.eqv_symm (Q'.pow_add_eqv q 2 (2 * l))

/-- **THE GEOMETRIC INCREMENT DOMINATION.**  For `0 < q < 1`, the theta increment
`2·q^{(l+1)²}` is dominated by the base-`q²` geometric majorant
`geoIncrBase (2q) q² l = (2q)·(q²)^l`, because `q^{(l+1)²} ≤ q^{2l+1} = q·(q²)^l`
(super-geometric decay of the discrete-Gaussian kernel). -/
theorem incr_le {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (l : Nat) :
    Q'.ofNat 2 * q ^ ((l + 1) * (l + 1))
      ≤ geoIncrBase (Q'.ofNat 2 * q) (q ^ 2) l := by
  -- (l+1)² ≥ 2l+1
  have hidx : 2 * l + 1 ≤ (l + 1) * (l + 1) := by
    have hexp : (l + 1) * (l + 1) = l * l + 2 * l + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    rw [hexp]; omega
  -- q^{(l+1)²} ≤ q^{2l+1}
  have hant : q ^ ((l + 1) * (l + 1)) ≤ q ^ (2 * l + 1) :=
    HKConvGen.pow_base_antitone (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) hidx
  -- q^{2l+1} ≃ q·(q²)^l
  have heq : (q ^ (2 * l + 1)).eqv (q * (q ^ 2) ^ l) := by
    have hidx2 : 2 * l + 1 = 1 + 2 * l := by omega
    rw [hidx2]
    refine Q'.eqv_trans _ _ _ (Q'.pow_add_eqv q 1 (2 * l)) ?_
    have hq1e : (q ^ 1).eqv q := by
      show (q * q ^ 0).eqv q
      exact Q'.mul_one_eqv q
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (q ^ (2 * l)) hq1e) ?_
    exact Q'.mul_eqv_congr_left q _ _ (Q'.eqv_symm (q2pow_eqv q l))
  have hq2q : q ^ ((l + 1) * (l + 1)) ≤ q * (q ^ 2) ^ l :=
    Q'.le_trans' _ _ _ hant (Q'.le_of_eqv heq)
  -- ×2 (nonneg) then reassociate to geoIncrBase
  have h2 : Q'.ofNat 2 * q ^ ((l + 1) * (l + 1)) ≤ Q'.ofNat 2 * (q * (q ^ 2) ^ l) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hq2q (ofNatNonneg 2)
  refine Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv ?_)
  -- 2·(q·(q²)^l) ≃ (2·q)·(q²)^l = geoIncrBase (2q) q² l
  exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) q ((q ^ 2) ^ l))

/-! ## 2. The two single-step bounds the engine consumes. -/

theorem thetaPartial_up {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (l : Nat) :
    thetaPartial q (l + 1)
      ≤ thetaPartial q l + geoIncrBase (Q'.ofNat 2 * q) (q ^ 2) l := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (thetaPartial_succ q l)) ?_
  exact Q'.add_le_add_left (thetaPartial q l)
    (Q'.ofNat 2 * q ^ ((l + 1) * (l + 1)))
    (geoIncrBase (Q'.ofNat 2 * q) (q ^ 2) l) (incr_le hq0 hq1 l)

theorem thetaPartial_lo {q : Q'} (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (l : Nat) :
    thetaPartial q l
      ≤ thetaPartial q (l + 1) + geoIncrBase (Q'.ofNat 2 * q) (q ^ 2) l := by
  -- thetaPartial l ≤ thetaPartial (l+1)  (increment ≥ 0)
  have hmono : thetaPartial q l ≤ thetaPartial q (l + 1) := by
    refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (thetaPartial_succ q l))
    exact Q'.add_le_self_of_nonneg (thetaPartial q l) _
      (Q'.mul_nonneg _ _ (ofNatNonneg 2) (Q'.pow_nonneg q (Q'.le_of_lt hq0) _))
  refine Q'.le_trans' _ _ _ hmono ?_
  exact Q'.add_le_self_of_nonneg (thetaPartial q (l + 1)) _
    (geoIncrBase_nonneg
      (Q'.mul_nonneg _ _ (ofNatNonneg 2) (Q'.le_of_lt hq0))
      (Q'.pow_nonneg q (Q'.le_of_lt hq0) 2) l)

/-! ## 3. THE CONSTRUCTIVE ϑ₃ SERIES `CReal` (the deliverable). -/

/-- **THE DELIVERABLE: `ϑ₃(q) = Σ_{n∈ℤ} q^{n²}` as a convergent `CReal`** with explicit
modulus, for every rational nome `0 < q < 1`.  `approx N = thetaPartial q N` (the genuine
symmetric partial sum `Σ_{|n|≤N} q^{n²}`); the Cauchy modulus is the base-`q²` telescoped
geometric tail from `HKConvGen.crealOfGeoIncrementBase`.  This is the SERIES realisation of
`ϑ₃` — the object the Poisson/Jacobi modular transform acts on. -/
def thetaS (q : Q') (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) : CReal :=
  crealOfGeoIncrementBase (thetaPartial q) (Q'.ofNat 2 * q) (q ^ 2)
    (Q'.mul_nonneg _ _ (ofNatNonneg 2) (Q'.le_of_lt hq0))
    (HKPos.pow_pos hq0 2)
    (q2_lt_one hq0 hq1)
    (thetaPartial_up hq0 hq1)
    (thetaPartial_lo hq0 hq1)
    (fun ε hε => by
      -- δ = divPos ε D, D = (2q)·H,  H = divPos 1 (1 + (−q²)) ;  D·δ ≃ ε
      have hqn : 0 < q.num := CReal.num_pos_of_pos hq0
      have hCnum : 0 < (Q'.ofNat 2 * q).num := by
        show 0 < (Q'.ofNat 2).num * q.num
        exact Int.mul_pos (by decide) hqn
      have hHpos : (0 : Q') < HKConv.divPos 1 (1 + (-(q ^ 2))) :=
        HKConv.divPos_pos (by decide)
      have hHnum : 0 < (HKConv.divPos 1 (1 + (-(q ^ 2)))).num := CReal.num_pos_of_pos hHpos
      have hDnum : 0 <
          ((Q'.ofNat 2 * q) * HKConv.divPos 1 (1 + (-(q ^ 2)))).num := by
        show 0 < (Q'.ofNat 2 * q).num * (HKConv.divPos 1 (1 + (-(q ^ 2)))).num
        exact Int.mul_pos hCnum hHnum
      refine ⟨HKConv.divPos ε ((Q'.ofNat 2 * q) * HKConv.divPos 1 (1 + (-(q ^ 2)))),
        HKConv.divPos_pos (CReal.num_pos_of_pos hε), ?_⟩
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_comm_eqv ((Q'.ofNat 2 * q) * HKConv.divPos 1 (1 + (-(q ^ 2))))
          (HKConv.divPos ε ((Q'.ofNat 2 * q) * HKConv.divPos 1 (1 + (-(q ^ 2)))))) ?_
      exact HKConv.divPos_mul_eqv hDnum)

/-- `ϑ₃(q)`'s `N`-th approximation is exactly the symmetric partial sum. -/
@[simp] theorem thetaS_approx (q : Q') (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) (N : Nat) :
    (thetaS q hq0 hq1).approx N = thetaPartial q N := rfl

/-- **`ϑ₃(q) ≥ 1`** — the genuine, non-vacuous lower bound (the `n = 0` term). -/
theorem thetaS_geRat_one (q : Q') (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    ExpPos.geRat (thetaS q hq0 hq1) 1 := by
  apply ExpPos.geRat_of_eventually
  refine ⟨0, fun N _ => ?_⟩
  rw [thetaS_approx]
  exact thetaPartial_ge_one (Q'.le_of_lt hq0) N

/-- **`ϑ₃(q) ≥ 0`** (weaker; from `ϑ₃(q) ≥ 1`). -/
theorem thetaS_geRat_zero (q : Q') (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q')) :
    ExpPos.geRat (thetaS q hq0 hq1) 0 :=
  ExpPos.geRat_mono (thetaS_geRat_one q hq0 hq1) (by decide)

/-! ## 3b. The two-sided modular BRACKET at the SUM level (no integration).

The consumer of `MomentEnvelopePoissonDual` is NOT the exact modular identity
`ϑ₃(1/τ)=√τ·ϑ₃(τ)` but the curvature envelope `Δ²V+2 ≥ (144/25)w²(1−w²)`
(`R1CurvatureEnvelope.CurvatureEnvelope`), whose tail `s ≥ 7` carries a uniform
multiplicative margin (true infimum ratio `≥ 7.96` vs required `144/25 = 5.76`,
i.e. `≈ 1.38×`).  So TWO-SIDED bounds `c₁√τ·ϑ₃(τ) ≤ ϑ₃(1/τ) ≤ c₂√τ·ϑ₃(τ)` suffice
— the exact identity is not required (see `docs/theta_inversion.md`).  The crux the
naive finite-majorant route misses is that the DENOMINATOR `ϑ₃(q)` DIVERGES as
`q → 1` (rate `∼ 1/√(1−q)`); a bounded-below denominator is what keeps the moment
ratio `V = (Σ_D D²q^{D²})/(Σ_D q^{D²})` from blowing up.  This subsection supplies
the genuine SUM-LEVEL divergence lower bound (via the counting/geometric
domination already used for the convergence modulus — NO Poisson, NO integration)
and a clean rational upper bound, bracketing `ϑ₃` two-sidedly.

The lower bound `ϑ₃(q) ≥ 1 + 2N·q^{N²}` (for EVERY `N`) is the load-bearing one:
choosing `N ∼ 1/√(−ln q)` makes the right side `∼ 1/√(1−q) → ∞`, exhibiting the
divergence RATE.  Its constant (`2/e ≈ 0.74` of the sharp `√(π/ε)`) is loose
relative to the `1.38×` envelope margin — so it SHARPENS the residual to a
near-sharp two-sided theta bound (constant within `1.38`) rather than closing it;
that near-sharp constant is the genuine remaining input.
-/

/-- One partial-sum step is nondecreasing: `θ_l ≤ θ_{l+1}` (the increment
`2·q^{(l+1)²}` is `≥ 0`).  Extracted from `thetaPartial_lo`. -/
theorem thetaPartial_step_le {q : Q'} (hq0 : (0 : Q') ≤ q) (l : Nat) :
    thetaPartial q l ≤ thetaPartial q (l + 1) := by
  refine Q'.le_trans' _ _ _ ?_ (Q'.ge_of_eqv (thetaPartial_succ q l))
  exact Q'.add_le_self_of_nonneg (thetaPartial q l) _
    (Q'.mul_nonneg _ _ (ofNatNonneg 2) (Q'.pow_nonneg q hq0 _))

/-- The symmetric partial sums are monotone: `θ_N ≤ θ_{N+d}` (increments `≥ 0`). -/
theorem thetaPartial_mono {q : Q'} (hq0 : (0 : Q') ≤ q) (N d : Nat) :
    thetaPartial q N ≤ thetaPartial q (N + d) := by
  induction d with
  | zero => exact Q'.le_refl' _
  | succ d ih => exact Q'.le_trans' _ _ _ ih (thetaPartial_step_le hq0 (N + d))

/-- **`thetaS_geRat_partial`** — `ϑ₃(q) ≥ θ_N` for every partial sum `θ_N`
(the monotone limit dominates each of its partial sums).  A genuine, non-vacuous
lower-bound family. -/
theorem thetaS_geRat_partial (q : Q') (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (N : Nat) : ExpPos.geRat (thetaS q hq0 hq1) (thetaPartial q N) := by
  apply ExpPos.geRat_of_eventually
  refine ⟨N, fun M hM => ?_⟩
  rw [thetaS_approx]
  obtain ⟨d, rfl⟩ := Nat.le.dest hM
  exact thetaPartial_mono (Q'.le_of_lt hq0) N d

/-- `Σ_{i<N} c ≃ N·c` — a finite constant sum. -/
theorem fsum_const_val (c : Q') (N : Nat) :
    (fsum (fun _ => c) N).eqv (Q'.ofNat N * c) := by
  induction N with
  | zero =>
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c Q'.ofNat_zero_eqv)
          (Q'.zero_mul_eqv c))
  | succ N ih =>
      show (fsum (fun _ => c) N + c).eqv (Q'.ofNat (N + 1) * c)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ c ih) ?_
      -- N·c + c ≃ (N+1)·c
      have hone : ((Q'.ofNat 1) * c).eqv c :=
        Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ c (by decide : (Q'.ofNat 1).eqv 1))
          (Q'.one_mul_eqv c)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ c (Q'.ofNat_add_eqv N 1)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (Q'.ofNat N) (Q'.ofNat 1) c) ?_
      exact Q'.add_eqv_congr_left _ _ _ hone

/-- **`thetaHalf_ge_count`** — the counting lower bound `N·q^{N²} ≤ Σ_{n=1}^{N} q^{n²}`:
each of the `N` terms `q^{(i+1)²}` (`i < N`) is `≥ q^{N²}` (super-geometric decay,
`(i+1)² ≤ N²`, `pow_base_antitone`), so the half-sum dominates `N` copies of the
smallest.  This is the SUM-LEVEL kernel of the `1/√(1−q)` divergence rate. -/
theorem thetaHalf_ge_count {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ 1) (N : Nat) :
    Q'.ofNat N * q ^ (N * N) ≤ thetaHalf q N := by
  have hterm : ∀ i, i < N → q ^ (N * N) ≤ q ^ ((i + 1) * (i + 1)) := by
    intro i hi
    have hexp : (i + 1) * (i + 1) ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
    exact HKConvGen.pow_base_antitone hq0 hq1 hexp
  have hsum : fsum (fun _ => q ^ (N * N)) N ≤ thetaHalf q N :=
    YMGap.Continuum.CubeRatioBounds.fsum_mono_lt N hterm
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv (fsum_const_val (q ^ (N * N)) N)) hsum

/-- **`thetaPartial_ge_count`** — `θ_N ≥ 1 + 2N·q^{N²}` (the counting rate lifted to
the symmetric partial sum). -/
theorem thetaPartial_ge_count {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ 1) (N : Nat) :
    (1 : Q') + Q'.ofNat 2 * (Q'.ofNat N * q ^ (N * N)) ≤ thetaPartial q N := by
  show (1 : Q') + Q'.ofNat 2 * (Q'.ofNat N * q ^ (N * N)) ≤ 1 + Q'.ofNat 2 * thetaHalf q N
  refine Q'.add_le_add_left 1 _ _ ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) (thetaHalf_ge_count hq0 hq1 N)
    (ofNatNonneg 2)

/-- **`thetaS_geRat_count` — THE SUM-LEVEL DIVERGENCE LOWER BOUND.**  For every `N`,
`ϑ₃(q) ≥ 1 + 2N·q^{N²}`.  Choosing `N ∼ 1/√(−ln q)` this right side is `∼ 1/√(1−q)`,
so `ϑ₃` DIVERGES as `q → 1` at rate `≥ order 1/√(1−q)` — the crucial denominator
growth that keeps the moment ratio `V` bounded.  Derived purely at the SUM level
(counting + `pow_base_antitone`); NO Poisson, NO integration.  Its constant is a
factor `≈ 0.74` of the sharp `√(π/ε)`, i.e. loose vs the `1.38×` envelope margin —
so this sharpens the M1/M2 residual to a near-sharp two-sided theta bound, not a
closure. -/
theorem thetaS_geRat_count (q : Q') (hq0 : (0 : Q') < q) (hq1 : q < (1 : Q'))
    (N : Nat) :
    ExpPos.geRat (thetaS q hq0 hq1)
      (1 + Q'.ofNat 2 * (Q'.ofNat N * q ^ (N * N))) :=
  ExpPos.geRat_mono (thetaS_geRat_partial q hq0 hq1 N)
    (thetaPartial_ge_count (Q'.le_of_lt hq0) (Q'.le_of_lt hq1) N)

/-- **`thetaHalf_le_geom`** — the clean geometric UPPER bound
`Σ_{n=1}^{N} q^{n²} ≤ Σ_{i<N} q^{2i+1}`: each `q^{(i+1)²} ≤ q^{2i+1}` since
`(i+1)² ≥ 2i+1`.  The right side is a genuine finite geometric prefix (`q·(q²)^i`),
bounded above (for `0 < q < 1`) by `q/(1−q²)` — supplying the matching upper leg of
the two-sided bracket.  (Here we record the term-domination step; the geometric
closed tail is `HKConvGen.geoTailBase`.) -/
theorem thetaHalf_le_geom {q : Q'} (hq0 : (0 : Q') ≤ q) (hq1 : q ≤ 1) (N : Nat) :
    thetaHalf q N ≤ fsum (fun i => q ^ (2 * i + 1)) N := by
  refine YMGap.Continuum.CubeRatioBounds.fsum_mono_lt N (fun i _ => ?_)
  have hexp : 2 * i + 1 ≤ (i + 1) * (i + 1) := by
    have : (i + 1) * (i + 1) = i * i + 2 * i + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    rw [this]; omega
  exact HKConvGen.pow_base_antitone hq0 hq1 hexp

/-! ## 4. Non-vacuity — `ϑ₃` is a genuine non-constant series.

At `q = 1/2` the first symmetric partial sums already separate:
`thetaPartial (1/2) 0 = 1` while `thetaPartial (1/2) 1 = 1 + 2·(1/2) = 2 ≠ 1`, so
`thetaS` is a genuine non-constant object (its `n=1` term is real). -/
theorem thetaPartial_nonconstant :
    thetaPartial (Q'.mkPos 1 2 (by decide)) 0 = 1 ∧
      ¬ (thetaPartial (Q'.mkPos 1 2 (by decide)) 1 = 1) := by
  refine ⟨by decide, by decide⟩

end YMGap.Continuum.JacobiModularCReal

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.JacobiModularCReal.thetaPartial_succ
#print axioms YMGap.Continuum.JacobiModularCReal.incr_le
#print axioms YMGap.Continuum.JacobiModularCReal.thetaS
#print axioms YMGap.Continuum.JacobiModularCReal.thetaS_approx
#print axioms YMGap.Continuum.JacobiModularCReal.thetaS_geRat_one
#print axioms YMGap.Continuum.JacobiModularCReal.thetaPartial_mono
#print axioms YMGap.Continuum.JacobiModularCReal.thetaS_geRat_partial
#print axioms YMGap.Continuum.JacobiModularCReal.fsum_const_val
#print axioms YMGap.Continuum.JacobiModularCReal.thetaHalf_ge_count
#print axioms YMGap.Continuum.JacobiModularCReal.thetaS_geRat_count
#print axioms YMGap.Continuum.JacobiModularCReal.thetaHalf_le_geom
#print axioms YMGap.Continuum.JacobiModularCReal.thetaPartial_nonconstant
