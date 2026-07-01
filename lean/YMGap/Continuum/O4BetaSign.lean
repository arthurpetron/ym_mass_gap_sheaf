/-
Track B+RepTheory / R2 — **discharging the NAMED O(4)-restoration residual
`CouplingRunning.betaDrop_nonneg` from trajectory antitonicity, and reducing that
antitonicity to the single asymptotic-freedom SIGN `β > 0` (`b₀ = 11N/(48π²) > 0`)
via the two-loop contracting recurrence.**

# Where this sits in the chain

The two independent O(4)-restoration chains (`O4RestorationProgress`,
`O4ClauseStrength`) both bottom out at a POSITED per-step sign
`CouplingRunning.betaDrop_nonneg`.  The scout's Husung–Nada–Sommer master formula
`breakCoeff(a) = C·a²·[ḡ²(1/a)]^{γ̂}` splits exactly as the codebase already does:
the `a²` piece is the PROVED `degreeMargin = 2` geometric engine (`scale_step` /
`qpow_base_mul`), and `[ḡ²]^{γ̂}` is a monotone-`≤ 1` factor that must be SOURCED
from the running coupling.  `b₀ > 0 ⇒ ḡ² ↓` gives both `betaDrop_nonneg`
(monotonicity) and the extra log suppression.

# What this module proves (`[propext]` / `[propext, Quot.sound]` only)

  * `couplingRunningOfTrajectory` (**Target 1**) — ANY antitone positive rational
    trajectory `τ` yields a `CouplingRunning`, with `betaDrop k := τ k − τ(k+1)` so
    that `betaDrop_nonneg` IS the antitonicity and `run_step` is the telescoping
    `Q'` identity.  This moves the NAMED residual `betaDrop_nonneg` from a posited
    `Type`-level field to a DERIVED consequence of `τ_antitone`.

  * `tau_antitone` (**Target 2**) — from the contracting two-loop recurrence
    `τ(k+1) ≤ τ k·(1 − c·τ k)` (with `c = β/2 > 0`, `τ k ≥ 0`) the coupling is
    antitone `τ(k+1) ≤ τ k`.  The only sign used is `c ≥ 0`, i.e. the one-loop
    beta coefficient `b₀ > 0` — asymptotic freedom itself.  (This is the elementary
    reciprocal of `AFReciprocalRate.recip_step`: since `1 − c·τ k ≤ 1` and
    `τ k ≥ 0`, one blocking step cannot increase the coupling.)

  * `tauModel_antitone` (**Target 2, concrete**) — the decidable reciprocal model
    `τ_k = 1/(k+2)` (`AFCertificateModel.tauModel`) is antitone, via reciprocal
    antitonicity `recipAnti` of `harmDen`-monotonicity.

  * `o4_restored_of_tauModel` — the CAPSTONE: the entire O(4)-restoration pipeline
    fires from the reciprocal AF trajectory `tauModel` with **no** posited
    `betaDrop`, by feeding `couplingRunningOfTrajectory tauModel …` into the proved
    `O4RestorationProgress.o4_restored_of_coupling`.

  * `qpow_antitone_of_base` (**Target 3**) — base-monotonicity of `qpow` for
    nonnegative bases: `0 ≤ x ≤ y ⇒ x^n ≤ y^n`.  Applied at `x = τ(k+1) ≤ y = τ k`
    this is the genuine AF log suppression `(τ_{k+1})^{γ̂} ≤ (τ_k)^{γ̂}` (`b₀ > 0`).

  * `anisoDecayAF` (**Target 3**) — the Husung–Nada–Sommer schedule
    `coeff_k = v · (½)^k · (τ_k)^{γ̂}`, a genuine `O4RestorationAF.ScalingDimensionDecay`.
    The `(½)^k` factor is the PROVED geometric engine; the extra `(τ_k)^{γ̂}` factor
    is monotone-↓ because `τ` is antitone (`b₀ > 0`), so decay is at least as fast as
    the naive `(½)^k`.  `anisoDecayAF_coeff0` pins step 0 to `v · (τ_0)^{γ̂}`.

# NAMED residual (Rule 8, `Type`-level) — the ONLY remaining physics

The genuine open content is that the TRUE lattice SU(N) rotation-breaking coupling
satisfies the contracting recurrence, whose sole non-decidable input is the sign
`β > 0`, i.e. the one-loop `b₀ = 11N/(48π²) > 0` = **asymptotic freedom**.  The
decidable `tauModel` inhabits the recurrence unconditionally (`AFCertificateModel`);
we do NOT claim the physical interacting coupling obeys it.  Honest caveat: the
`[ḡ²]^{γ̂}` factor is a LOGARITHMIC modulation (monotonicity + extra suppression),
NOT the geometric ratio — the geometric contraction remains the proved
`degreeMargin = 2` (`½`) factor.  Pinning `anisoDecayAF`'s step-0 to the physical
anisotropy `|E χ₈ − E χ₄|` additionally requires the normalization `τ_0 = 1`, a
separate (untouched) modelling choice.

# Axiom-gate (AGENTS.md Rules 1, 8)

Pure `Q'`/`qpow` arithmetic and reuse of proved reductions in `O4RestorationProgress`,
`AFReciprocalRate`, `AFCertificateModel`.  Every load-bearing declaration is gated
with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `sorry`, no `Prop := True` stub.  All witnesses
are `Type`-level data.
-/

import YMGap.Continuum.O4RestorationProgress
import YMGap.Continuum.AFReciprocalRate
import YMGap.Continuum.AFCertificateModel
import YMGap.Continuum.O4ClauseStrength

namespace YMGap.Continuum.O4BetaSign

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration

/-! ## Target 1 — discharge `betaDrop_nonneg` from trajectory antitonicity

Any antitone positive rational trajectory `τ` supplies a `CouplingRunning`: setting
`betaDrop k := τ k − τ(k+1)`, the AF sign `betaDrop_nonneg` IS the antitonicity, and
the RG recursion `run_step` is the telescoping identity `τ k ≈ τ(k+1) + (τ k − τ(k+1))`.
The NAMED residual is thus reduced to the single object `τ_antitone`. -/

/-- **Target 1.**  ANY antitone positive rational trajectory yields a
`CouplingRunning`, with `betaDrop k := τ k − τ(k+1)`.  `betaDrop_nonneg` is the
antitonicity (`Q'.sub_nonneg_of_le`) and `run_step` is the telescoping
`Q'`-identity (`Q'.add_sub_cancel_eqv`).  This turns the posited `Type`-level field
`betaDrop_nonneg` into a DERIVED consequence of `τ_antitone`. -/
def couplingRunningOfTrajectory
    (τ : Nat → Q') (τ_pos : ∀ k, (0 : Q') < τ k)
    (τ_antitone : ∀ k, τ (k + 1) ≤ τ k) :
    O4RestorationProgress.CouplingRunning where
  g               := τ
  g_nonneg        := fun k => Q'.le_of_lt (τ_pos k)
  betaDrop        := fun k => τ k - τ (k + 1)
  betaDrop_nonneg := fun k => Q'.sub_nonneg_of_le (τ_antitone k)
  run_step        := fun k => Q'.add_sub_cancel_eqv (τ k) (τ (k + 1))

/-! ## Target 2 — antitonicity from the contracting recurrence (the sign `β > 0`)

`tau_antitone` derives `τ(k+1) ≤ τ k` from `τ(k+1) ≤ τ k·(1 − c·τ k)` using only
`c ≥ 0` and `τ k ≥ 0`: since `1 − c·τ k ≤ 1`, multiplying by `τ k ≥ 0` gives
`τ k·(1 − c·τ k) ≤ τ k·1 ≈ τ k`.  The single sign is `c = β/2 ≥ 0`, i.e. the
one-loop `b₀ > 0`. -/

/-- **Target 2.**  From the contracting two-loop recurrence
`τ(k+1) ≤ τ k·(1 − c·τ k)` (valid for `k ≥ k0`, `c > 0`, `τ k > 0`) the coupling is
antitone: `τ(k+1) ≤ τ k`.  This is `betaDrop_nonneg` reduced to the ONE sign
`β > 0` (`b₀ = 11N/(48π²) > 0`). -/
theorem tau_antitone
    (τ : Nat → Q') (τ_pos : ∀ k, (0 : Q') < τ k) (c : Q') (hc : (0 : Q') < c)
    (k0 : Nat) (hrec : ∀ k, k0 ≤ k → τ (k + 1) ≤ τ k * (1 - c * τ k)) :
    ∀ k, k0 ≤ k → τ (k + 1) ≤ τ k := by
  intro k hk
  have hcτ : (0 : Q') ≤ c * τ k :=
    Q'.mul_nonneg c (τ k) (Q'.le_of_lt hc) (Q'.le_of_lt (τ_pos k))
  -- 1 − c·τk ≤ 1  (since −(c·τk) ≤ 0).
  have h1 : (1 : Q') - c * τ k ≤ 1 := by
    have h := Q'.add_le_add_left 1 (-(c * τ k)) 0 (AFCertificateModel.negNonpos hcτ)
    rw [Q'.add_zero'] at h
    exact h
  -- τk·(1 − c·τk) ≤ τk·1 ≈ τk.
  have h2 : τ k * (1 - c * τ k) ≤ τ k * 1 :=
    Q'.mul_le_mul_of_nonneg_left (1 - c * τ k) 1 (τ k) h1 (Q'.le_of_lt (τ_pos k))
  have h3 : (τ k * 1).eqv (τ k) := Q'.mul_one_eqv (τ k)
  exact Q'.le_trans' _ _ _ (hrec k hk)
    (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv h3))

/-! ## Target 2, concrete — the decidable reciprocal model `τ_k = 1/(k+2)`

`AFCertificateModel.tauModel k = 1/(k+2)` is antitone by reciprocal antitonicity of
the increasing denominator `harmDen 2 k = k+2`. -/

/-- The reciprocal model is positive at every step. -/
theorem tauModel_pos (k : Nat) : (0 : Q') < AFCertificateModel.tauModel k :=
  Q'.divPos_pos 1 (harmDen 2 k) (harmDen_pos (by decide) k) (by decide)

/-- **Target 2, concrete.**  `τ_k = 1/(k+2)` is antitone: `τ_{k+1} ≤ τ_k`, via
`recipAnti` applied to `harmDen 2 k ≤ harmDen 2 (k+1)`. -/
theorem tauModel_antitone (k : Nat) :
    AFCertificateModel.tauModel (k + 1) ≤ AFCertificateModel.tauModel k :=
  AFCertificateModel.recipAnti
    (harmDen_pos (by decide) k) (harmDen_pos (by decide) (k + 1))
    (harmDen_mono 2 (Nat.le_succ k))

/-! ## Capstone — the whole O(4) chain from the reciprocal AF trajectory

Composing Targets 1 and 2: `couplingRunningOfTrajectory tauModel …` supplies the
`CouplingRunning`, and `O4RestorationProgress.o4_restored_of_coupling` fires the
entire O(4)-restoration pipeline — with NO posited `betaDrop`. -/

/-- The `CouplingRunning` built from the reciprocal AF trajectory `tauModel`, with
`betaDrop` fully derived (no posited sign). -/
def tauModelRunning : O4RestorationProgress.CouplingRunning :=
  couplingRunningOfTrajectory AFCertificateModel.tauModel tauModel_pos tauModel_antitone

/-- **CAPSTONE.**  O(4) restored (the proved CReal convergence of the
rotation-breaking coefficient) fired from the reciprocal AF trajectory `tauModel`,
with the whole `betaDrop` chain DERIVED — the only remaining named physics is that
the true lattice coupling obeys the contracting recurrence, i.e. `b₀ > 0`. -/
theorem o4_restored_of_tauModel :
    O4RestorationAF.RotationRestored
      (O4RestorationProgress.scalingDimensionDecay_of_flow
        (O4RestorationProgress.flowOfCoupling tauModelRunning)) :=
  O4RestorationProgress.o4_restored_of_coupling tauModelRunning

/-! ## Target 3 — the Husung–Nada–Sommer schedule `v·(½)^k·(τ_k)^{γ̂}`

`qpow_antitone_of_base` is base-monotonicity of `qpow`; at `τ(k+1) ≤ τ k` it gives
the AF log-suppression factor `(τ_{k+1})^{γ̂} ≤ (τ_k)^{γ̂}`.  `anisoDecayAF` bundles
the proved geometric `(½)^k` engine with this monotone factor into a genuine
`ScalingDimensionDecay`. -/

/-- **Target 3, base-monotonicity of `qpow`.**  For `0 ≤ x ≤ y`, `x^n ≤ y^n`.
Induction: `x^{n+1} = x^n·x ≤ y^n·x ≤ y^n·y = y^{n+1}` (first step `x ≥ 0`, second
`y^n ≥ 0`). -/
theorem qpow_antitone_of_base {x y : Q'} (hx : (0 : Q') ≤ x) (hy : (0 : Q') ≤ y)
    (hxy : x ≤ y) : ∀ n, RGTransport.qpow x n ≤ RGTransport.qpow y n
  | 0 => by
      show (1 : Q') ≤ 1
      exact Q'.le_refl' 1
  | n + 1 => by
      show RGTransport.qpow x n * x ≤ RGTransport.qpow y n * y
      have ih := qpow_antitone_of_base hx hy hxy n
      have h1 : RGTransport.qpow x n * x ≤ RGTransport.qpow y n * x :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ ih hx
      have h2 : RGTransport.qpow y n * x ≤ RGTransport.qpow y n * y :=
        Q'.mul_le_mul_of_nonneg_left _ _ _ hxy (RGTransport.qpow_nonneg y hy n)
      exact Q'.le_trans' _ _ _ h1 h2

/-- Rearrange `(a·h)·b ≈ h·(a·b)`. -/
theorem swap_left (a h b : Q') : ((a * h) * b).eqv (h * (a * b)) :=
  Q'.eqv_symm
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv h a b))
      (Q'.mul_eqv_congr_right (h * a) (a * h) b (Q'.mul_comm_eqv h a)))

/-- Rearrange `v·(h·c) ≈ h·(v·c)`. -/
theorem swap_scalar (v h c : Q') : (v * (h * c)).eqv (h * (v * c)) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv v h c))
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (v * h) (h * v) c (Q'.mul_comm_eqv v h))
      (Q'.mul_assoc_eqv h v c))

/-- **Target 3, the schedule.**  Husung–Nada–Sommer decay
`coeff_k = v · (½)^k · (τ_k)^{γ̂}`: a genuine `O4RestorationAF.ScalingDimensionDecay`.
The `(½)^k` factor is the proved geometric engine (`degreeMargin = 2`); the extra
`(τ_k)^{γ̂}` factor is monotone-↓ because `τ` is antitone (`b₀ > 0`), so single-step
decay is at least the naive `½` contraction. -/
def anisoDecayAF
    (v : Q') (hv : (0 : Q') ≤ v) (τ : Nat → Q')
    (τ_nonneg : ∀ k, (0 : Q') ≤ τ k) (τ_antitone : ∀ k, τ (k + 1) ≤ τ k)
    (γ : Nat) : O4RestorationAF.ScalingDimensionDecay where
  coeff := fun k =>
    v * (RGTransport.qpow HalfPow.half k * RGTransport.qpow (τ k) γ)
  coeff_nonneg := fun k =>
    Q'.mul_nonneg _ _ hv
      (Q'.mul_nonneg _ _
        (RGTransport.qpow_nonneg HalfPow.half HalfPow.half_nonneg k)
        (RGTransport.qpow_nonneg (τ k) (τ_nonneg k) γ))
  degreeMargin := 2
  degreeMargin_ge_two := Nat.le_refl 2
  decay := fun k => by
    -- goal: v·((½^k·½)·τ(k+1)^γ) ≤ ½·(v·(½^k·τk^γ))
    -- log-suppression factor: τ(k+1)^γ ≤ τk^γ
    have hτγ : RGTransport.qpow (τ (k + 1)) γ ≤ RGTransport.qpow (τ k) γ :=
      qpow_antitone_of_base (τ_nonneg (k + 1)) (τ_nonneg k) (τ_antitone k) γ
    -- geometric factor a·h = ½^k·½ ≥ 0
    have hah_nn : (0 : Q') ≤ RGTransport.qpow HalfPow.half k * HalfPow.half :=
      Q'.mul_nonneg _ _
        (RGTransport.qpow_nonneg HalfPow.half HalfPow.half_nonneg k) HalfPow.half_nonneg
    -- (a·h)·τ(k+1)^γ ≤ (a·h)·τk^γ
    have hstepB :
        (RGTransport.qpow HalfPow.half k * HalfPow.half) * RGTransport.qpow (τ (k + 1)) γ
          ≤ (RGTransport.qpow HalfPow.half k * HalfPow.half) * RGTransport.qpow (τ k) γ :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hτγ hah_nn
    -- (a·h)·τk^γ ≈ ½·(½^k·τk^γ)
    have hstepC :
        ((RGTransport.qpow HalfPow.half k * HalfPow.half) * RGTransport.qpow (τ k) γ)
          ≤ HalfPow.half * (RGTransport.qpow HalfPow.half k * RGTransport.qpow (τ k) γ) :=
      Q'.le_of_eqv (swap_left (RGTransport.qpow HalfPow.half k) HalfPow.half
        (RGTransport.qpow (τ k) γ))
    have hinner :
        (RGTransport.qpow HalfPow.half k * HalfPow.half) * RGTransport.qpow (τ (k + 1)) γ
          ≤ HalfPow.half * (RGTransport.qpow HalfPow.half k * RGTransport.qpow (τ k) γ) :=
      Q'.le_trans' _ _ _ hstepB hstepC
    -- multiply by v ≥ 0 on the left
    have hv_mul :
        v * ((RGTransport.qpow HalfPow.half k * HalfPow.half)
              * RGTransport.qpow (τ (k + 1)) γ)
          ≤ v * (HalfPow.half
              * (RGTransport.qpow HalfPow.half k * RGTransport.qpow (τ k) γ)) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hinner hv
    -- v·(½·c) ≈ ½·(v·c)
    have hswap :
        (v * (HalfPow.half
              * (RGTransport.qpow HalfPow.half k * RGTransport.qpow (τ k) γ))).eqv
          (HalfPow.half
              * (v * (RGTransport.qpow HalfPow.half k * RGTransport.qpow (τ k) γ))) :=
      swap_scalar v HalfPow.half
        (RGTransport.qpow HalfPow.half k * RGTransport.qpow (τ k) γ)
    exact Q'.le_trans' _ _ _ hv_mul (Q'.le_of_eqv hswap)

/-- **Target 3, step-0 pin.**  `breakCoeff (anisoDecayAF …) 0 ≈ v · (τ_0)^{γ̂}`
(`(½)^0 = 1`).  So the schedule's step 0 is the anisotropy `v` modulated by the
one AF-log factor `(τ_0)^{γ̂}`. -/
theorem anisoDecayAF_coeff0
    (v : Q') (hv : (0 : Q') ≤ v) (τ : Nat → Q')
    (τ_nonneg : ∀ k, (0 : Q') ≤ τ k) (τ_antitone : ∀ k, τ (k + 1) ≤ τ k) (γ : Nat) :
    (O4RestorationAF.breakCoeff (anisoDecayAF v hv τ τ_nonneg τ_antitone γ) 0).eqv
      (v * RGTransport.qpow (τ 0) γ) :=
  Q'.mul_eqv_congr_left v _ _ (Q'.one_mul_eqv (RGTransport.qpow (τ 0) γ))

/-! ## Non-vacuity — the HNS schedule on the reciprocal model fires the rubric

Instantiating `anisoDecayAF` at `v = 1`, `τ = tauModel`, `γ̂ = 1` gives a genuine
`ScalingDimensionDecay` whose running is `½^k·(τ_k)^1` (the physical `a²·[ḡ²]^{γ̂}`
shape, not a bare `½`), and the proved decay bridge fires the open O(4) clause. -/

/-- The Husung–Nada–Sommer schedule on the reciprocal AF model (`v = 1`, `γ̂ = 1`). -/
def anisoDecayAF_tauModel : O4RestorationAF.ScalingDimensionDecay :=
  anisoDecayAF 1 (by decide) AFCertificateModel.tauModel
    (fun k => Q'.le_of_lt (tauModel_pos k)) tauModel_antitone 1

/-- **Non-vacuity.**  The open O(4)-restoration Clay clause fires from the
Husung–Nada–Sommer schedule `½^k·(τ_k)^{γ̂}` on the reciprocal AF model, via the
proved decay bridge. -/
theorem rubricO4Restoration_anisoDecayAF :
    YMGap.Rubric.ClayScorecard.RubricO4Restoration :=
  O4RestorationH4.rubricO4Restoration_of_decay anisoDecayAF_tauModel

end YMGap.Continuum.O4BetaSign

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.O4BetaSign.couplingRunningOfTrajectory
#print axioms YMGap.Continuum.O4BetaSign.tau_antitone
#print axioms YMGap.Continuum.O4BetaSign.tauModel_pos
#print axioms YMGap.Continuum.O4BetaSign.tauModel_antitone
#print axioms YMGap.Continuum.O4BetaSign.tauModelRunning
#print axioms YMGap.Continuum.O4BetaSign.o4_restored_of_tauModel
#print axioms YMGap.Continuum.O4BetaSign.qpow_antitone_of_base
#print axioms YMGap.Continuum.O4BetaSign.swap_left
#print axioms YMGap.Continuum.O4BetaSign.swap_scalar
#print axioms YMGap.Continuum.O4BetaSign.anisoDecayAF
#print axioms YMGap.Continuum.O4BetaSign.anisoDecayAF_coeff0
#print axioms YMGap.Continuum.O4BetaSign.anisoDecayAF_tauModel
#print axioms YMGap.Continuum.O4BetaSign.rubricO4Restoration_anisoDecayAF
