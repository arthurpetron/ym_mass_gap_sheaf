/-
Track B / R2 — ROUTE E: the LARGE-FIELD half of `GapChannelDomination` — the genuine
Bałaban / Magnen–Rivasseau–Sénéor small-field theorem's LARGE-FIELD suppression.

# What this module does (read first)

`HeatKernelSecondCumulant.GapChannelDomination` is the single open physical input of
Route B: the real 4D SU(2) block-spin per-step degradation of the true dimensionless
margin is dominated by the fundamental-channel heat-kernel SECOND CUMULANT
`δ_model = afDefectSeq afr = pMult·chanCumulant 1 (w_k)`.  The Bałaban/MRS proof of that
domination splits the block-spin fluctuation integral `∫ Dξ exp(−S(U·ξ))` into

  * the SMALL-FIELD region `|ξ| ≤ ε` — the Gaussian + cumulant regime that PRODUCES the
    `s = 1` second cumulant `δ_model` (the higher-rep channel-tail refinement of this
    region is the parallel deliverable);
  * the LARGE-FIELD region `|ξ| ≥ ε` — RARE, and the subject of THIS module.

The large-field contribution to the gap degradation must be EXPONENTIALLY SUPPRESSED so
that the small-field `s = 1` cumulant dominates.  This module derives the correct
orientation and constant, proves the resulting GEOMETRIC-SUMMABILITY of the large-field
budget in Lean-core, and reduces the large-field half to the sharpest honest residual.

# THE PHYSICS, correctly oriented (adversarial finding — AGENTS.md Rule 6/9)

The heat kernel is a class function of the plaquette angle `θ ∈ [0,π]` (the fluctuation
field size, `d(1,U) = θ`):

    K_t(θ) = Σ_{n≥1} n·χ_n(θ)·w^{C₄(s)},   n = s+1 = dim,  C₄(s) = s(s+2) = n²−1,

with `w` the heat-kernel weight (`w = e^{−t}`, small-field ↔ `w → 1`).  `K_t` is a
PROBABILITY density for the Haar class measure `dμ(θ) = (2/π)sin²θ dθ` (character
orthogonality: `∫ K_t dμ = 1`).  The LARGE-FIELD fraction is the mass of the rare region

    F(θ₀,w) = ∫_{θ₀}^{π} K_t(θ) dμ(θ) = Prob( plaquette angle ≥ θ₀ ).

The short-time (`w → 1`, `t → 0`) heat-kernel Gaussian asymptotics on the group give

    F(θ₀,w)  ≤  K·exp( − θ₀²/(4t) ),   t = −log w ∼ (1 − w)  as  w → 1,

so the large-field fraction is EXPONENTIALLY small in `1/(1 − w)`, and — this is the
ORIENTATION that matters — the suppression IMPROVES monotonically as `w → 1` (WEAK
coupling, deep UV, large `k` along the AF flow).  At STRONG coupling (`w` small) the
large field is NOT suppressed; that regime is covered separately by the PROVED
fixed-spacing strong-coupling gap.  (`routeE_largefield_numerics.py`, mpmath dps ≥ 40:
`F(π/2,w)` falls from `0.499` at `w = 0.1` to `1.3·10⁻²⁶` at `w = 0.99`, with
`(−log F)·t → 0.60 ≈ (π/2)²/4 = 0.617` — the short-time Gaussian constant `θ₀²/4`.)

Along the asymptotic-freedom trajectory `1 − w_k ∼ A/(k+B)`, hence `1/(1 − w_k) ∼
(k+B)/A`, the large-field fraction is

    F(w_k)  ≤  K·exp( −c·(k+B)/A )  =  K'·r^k,    r = exp(−c/A) ∈ (0,1),

i.e. the per-step large-field defect decays GEOMETRICALLY in `k`.  A geometric sequence
is SUMMABLE with the explicit budget `Σ_k K'·r^k ≤ K'/(1 − r)` — in DECISIVE contrast
with the LINEAR bond-moving crack, whose harmonic budget `Σ 6p·(1 − w_k)` DIVERGES
(`AFRateCalibration.linear_bound_not_summable`).  The large-field half is therefore not
an obstruction: it supplies a FINITE, geometrically-summable ADDITIVE erosion `ε_k`.

# What is GENUINELY PROVED here (axiom-clean `Q'`/`Nat`)

  * `geomSum_le_recip` — **the geometric summability bound** `Σ_{k<N} r^k ≤ 1/(1 − r)`
    on `0 ≤ r < 1`, UNIFORMLY in `N` (from `(1−r)·geomSum = 1 − r^N ≤ 1`).  This is the
    analytic heart: geometric partial sums are bounded, in contrast to harmonic.
  * `geomBudget_le` / `largeFieldSuppression_summable` — **the large-field budget is
    bounded** `Σ_{k<N} δLF_k ≤ K/(1 − r)`, the explicit finite additive-erosion budget
    `Bε = K/(1 − r)` for the geometric (exp-suppressed) large-field defect.
  * `largeFieldBudget` — the budget returned as DATA (`Σ'`, Rule 2): the large-field
    summability constant is COMPUTED, in contrast to the uninhabitable linear
    `BondMovingSummable`.
  * `largeField_epsBudget` — the same budget in `tailSum … 0` form, exactly the `hBε`
    slot of the PROVED adequacy engine `AdditiveErosionAdequacy.additiveErosion_uniform_floor`.
  * **`largeField_additiveErosion_floor`** — THE HONEST REDUCTION (guard-safe conditional):
    with the large-field defect as the additive erosion `ε_k`, and GIVEN the small-field
    multiplicative recursion (the parallel half) + anchor-dominance, the PROVED adequacy
    engine DERIVES the strictly-positive uniform continuum floor.  The large-field half is
    fully discharged INTO that engine — it contributes only a finite geometric `Bε`.

# THE NAMED RESIDUAL (AGENTS.md Rule 6a / Rule 9; UNINHABITED)

`LargeFieldSuppression` carries the sole open large-field physical input: the per-step
large-field defect `δLF_k` is GEOMETRICALLY (exponentially) suppressed, `δLF_k ≤ K·r^k`
with `r ∈ (0,1)` — the correctly-oriented Bałaban large-field bound (`r = exp(−c/A)`,
`c ≈ θ₀²/4` from the heat-kernel Gaussian tail).  This is the honest large-field constant.
It is NOT inhabited for the real 4D flow (the free-field caveat below applies exactly as
to `GapChannelDomination`).  NOTHING here inhabits `GapChannelDomination`,
`SingleStepDefectBound`, or `TrueMarginRecursion*`; NO 4D Yang–Mills mass gap is claimed.

HONESTY CAVEAT (Rule 9(6)): `lf_geom` bounds a FREE `largeFieldDefect : Nat → Q'`, so —
exactly like every other frontier atom in this program — it is vacuously fakeable in
principle (`largeFieldDefect ≡ 0` satisfies it).  The residual is genuine only when
`largeFieldDefect` is the physical large-field mass; the honest protection is the guard +
refusing to land the fake.  The genuinely NON-vacuous content is the PROVED geometric
summability (theorems about the concrete `qpow`/`geomSum` objects) and the reduction into
the proved adequacy engine, which the free field does NOT subsume.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic and structural induction over the PROVED `geomSum` /
`oneSub_pow_factor` / `divPos` / `additiveErosion_uniform_floor` engines.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is
`propext`/`Quot.sound` only.  No `Classical.*`, no `native_decide`, no `sorry`.  All
witnesses are `Type`-level data.
-/

import YMGap.Continuum.HeatKernelSecondCumulant
import YMGap.Continuum.AdditiveErosionAdequacy

namespace YMGap.Continuum.LargeFieldSuppression

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.HeatKernelSecondCumulant

/-! ## 0. Elementary `Q'` helper: `1 − x ≤ 1` for `x ≥ 0`. -/

/-- `1 − x ≤ 1` on `x ≥ 0` (proved via `0 + (−x) ≃ −x ≤ 0 ≃ x + (−x)` and left
add-monotonicity).  Used to bound the geometric numerator `1 − r^N ≤ 1`. -/
theorem oneSub_le_one {x : Q'} (hx : (0 : Q') ≤ x) : (1 : Q') - x ≤ 1 := by
  have hneg : (-x) ≤ (0 : Q') := by
    have hstep : (0 : Q') + (-x) ≤ x + (-x) := Q'.add_le_add_right 0 x (-x) hx
    have hL : ((0 : Q') + (-x)).eqv (-x) := Q'.eqv_of_eq (Q'.zero_add' (-x))
    have hR : (x + (-x)).eqv 0 := Q'.add_neg_self_eqv x
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hL) (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hR))
  show (1 : Q') + (-x) ≤ 1
  have hstep2 : (1 : Q') + (-x) ≤ 1 + 0 := Q'.add_le_add_left 1 (-x) 0 hneg
  exact Q'.le_trans' _ _ _ hstep2 (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1)))

/-! ## 1. The geometric summability bound — the analytic heart of large-field control. -/

/-- **THE GEOMETRIC SUMMABILITY BOUND.**  For `0 ≤ r` and `0 < 1 − r` (i.e. `r < 1`),
the finite geometric sum is bounded UNIFORMLY in `N` by `1/(1 − r)`:

    geomSum r N  =  Σ_{k<N} r^k  ≤  1/(1 − r).

Proof: `geomSum r N·(1 − r) ≃ 1 − r^N ≤ 1` (`oneSub_pow_factor` + `oneSub_le_one`), then
`le_divPos_of_mul_le`.  This is the DECISIVE contrast with the divergent harmonic series
(`AFRateCalibration.harmonic_diverges`): geometric partial sums are bounded. -/
theorem geomSum_le_recip {r : Q'} (h0 : (0 : Q') ≤ r) (h1r : (0 : Q') < 1 - r) (N : Nat) :
    geomSum r N ≤ Q'.divPos 1 (1 - r) h1r := by
  refine Q'.le_divPos_of_mul_le 1 (1 - r) h1r ?_
  -- geomSum r N · (1 − r) ≤ 1
  have hfac : (geomSum r N * (1 - r)).eqv ((1 : Q') - qpow r N) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (geomSum r N) (1 - r)) ?_
    exact Q'.eqv_symm (oneSub_pow_factor r N)
  have hle : (1 : Q') - qpow r N ≤ 1 := oneSub_le_one (qpow_nonneg r h0 N)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfac) hle

/-! ## 2. The large-field defect, its geometric majorant, and the budget. -/

/-- The geometric majorant sequence `k ↦ K·r^k` (the exp-suppressed large-field mass
along the AF flow: `F(w_k) ≤ K·r^k`, `r = exp(−c/A) ∈ (0,1)`). -/
def geomMajorant (K r : Q') (k : Nat) : Q' := K * qpow r k

/-- The partial sum of the geometric majorant equals `K·geomSum r N` (pull the constant
out of the finite sum). -/
theorem lossSum_geomMajorant (K r : Q') :
    ∀ N, (ProductFloor.lossSum (geomMajorant K r) N).eqv (K * geomSum r N)
  | 0 => by
      show ((0 : Q')).eqv (K * geomSum r 0)
      rw [geomSum_zero]
      exact Q'.eqv_symm (Q'.mul_zero_eqv K)
  | N + 1 => by
      have ih := lossSum_geomMajorant K r N
      show (ProductFloor.lossSum (geomMajorant K r) N + K * qpow r N).eqv
          (K * (geomSum r N + qpow r N))
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ (K * qpow r N) ih) ?_
      exact Q'.eqv_symm (Q'.mul_add_eqv K (geomSum r N) (qpow r N))

/-- **THE GEOMETRIC BUDGET BOUND.**  For `0 ≤ K`, `0 ≤ r`, `0 < 1 − r`,

    Σ_{k<N} K·r^k  ≤  K·(1/(1 − r)) ,   UNIFORMLY in `N`.

The bounded geometric budget — the finite additive-erosion constant `Bε = K/(1 − r)`. -/
theorem geomBudget_le {K r : Q'} (hK : (0 : Q') ≤ K) (h0 : (0 : Q') ≤ r)
    (h1r : (0 : Q') < 1 - r) (N : Nat) :
    ProductFloor.lossSum (geomMajorant K r) N ≤ K * Q'.divPos 1 (1 - r) h1r := by
  have heq : (ProductFloor.lossSum (geomMajorant K r) N).eqv (K * geomSum r N) :=
    lossSum_geomMajorant K r N
  have hle : K * geomSum r N ≤ K * Q'.divPos 1 (1 - r) h1r :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (geomSum_le_recip h0 h1r N) hK
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) hle

/-- Termwise monotonicity of the finite loss sum: `f ≤ g` pointwise ⟹
`lossSum f N ≤ lossSum g N`. -/
theorem lossSum_le_termwise {f g : Nat → Q'} (h : ∀ k, f k ≤ g k) :
    ∀ N, ProductFloor.lossSum f N ≤ ProductFloor.lossSum g N
  | 0 => Q'.le_refl' 0
  | N + 1 => by
      show ProductFloor.lossSum f N + f N ≤ ProductFloor.lossSum g N + g N
      exact q_add_le_add (lossSum_le_termwise h N) (h N)

/-! ## 3. The named large-field suppression input (`Type`, Rule 8; UNINHABITED). -/

/-- **`LargeFieldSuppression` — the sole open large-field physical input.**  Carries:

  * `K, r` with `0 ≤ K`, `0 ≤ r`, `0 < 1 − r` (`r ∈ (0,1)`: the geometric ratio
    `r = exp(−c/A)` from the heat-kernel Gaussian large-field tail);
  * `largeFieldDefect k` (`≥ 0`) — the per-step LARGE-FIELD contribution to the gap
    degradation (the additive erosion `ε_k` from the rare `|ξ| ≥ ε` region);
  * **`lf_geom`** — THE BAŁABAN LARGE-FIELD ESTIMATE, correctly oriented:
    `largeFieldDefect k ≤ K·r^k`, i.e. GEOMETRIC (exponential) suppression, improving
    with `k` (weak coupling / deep UV).

This is the honest large-field constant.  It is NOT inhabited for the real 4D flow — it
IS the large-field half of the real Bałaban/MRS small-field theorem.  (Free-field caveat:
see module header — genuine only for the physical `largeFieldDefect`.) -/
structure LargeFieldSuppression (afr : AFRateModulus) : Type where
  /-- The large-field amplitude constant `K ≥ 0`. -/
  K : Q'
  /-- `0 ≤ K`. -/
  K_nonneg : (0 : Q') ≤ K
  /-- The geometric ratio `r = exp(−c/A) ∈ (0,1)`. -/
  r : Q'
  /-- `0 ≤ r`. -/
  r_nonneg : (0 : Q') ≤ r
  /-- `r < 1`, packaged as `0 < 1 − r` (the geometric-summability guard). -/
  oneSubr_pos : (0 : Q') < 1 - r
  /-- The per-step large-field contribution to the gap degradation (additive `ε_k`). -/
  largeFieldDefect : Nat → Q'
  /-- The large-field defect is nonnegative. -/
  lf_nonneg : ∀ k, (0 : Q') ≤ largeFieldDefect k
  /-- **THE OPEN BAŁABAN LARGE-FIELD BOUND** — geometric (exp) suppression, correctly
  oriented (improves as `k → ∞` / `w → 1`): `largeFieldDefect k ≤ K·r^k`. -/
  lf_geom : ∀ k, largeFieldDefect k ≤ K * qpow r k

/-- **THE LARGE-FIELD BUDGET IS BOUNDED (SUMMABLE).**  From a `LargeFieldSuppression`,
the partial sums of the large-field defect are bounded UNIFORMLY by `Bε = K/(1 − r)`:

    ∀ N, Σ_{k<N} δLF_k ≤ K·(1/(1 − r)) .

DECISIVE: unlike the LINEAR bond-moving crack (harmonic, `linear_bound_not_summable`),
the exp-suppressed large-field budget IS finite.  The large-field half is under control. -/
theorem largeFieldSuppression_summable {afr : AFRateModulus} (L : LargeFieldSuppression afr)
    (N : Nat) :
    ProductFloor.lossSum L.largeFieldDefect N
      ≤ L.K * Q'.divPos 1 (1 - L.r) L.oneSubr_pos := by
  have h1 : ProductFloor.lossSum L.largeFieldDefect N
      ≤ ProductFloor.lossSum (geomMajorant L.K L.r) N :=
    lossSum_le_termwise (fun k => L.lf_geom k) N
  exact Q'.le_trans' _ _ _ h1 (geomBudget_le L.K_nonneg L.r_nonneg L.oneSubr_pos N)

/-- **The large-field summability budget, returned as DATA** (Rule 2): the explicit
finite budget `Bε = K/(1 − r)` together with the uniform bound `∀ N, Σ_{k<N} δLF_k ≤ Bε`.
Contrast `BondMovingStep.BondMovingSummable` for the LINEAR crack, which is
UNINHABITABLE (its budget diverges).  Here the budget is COMPUTED. -/
def largeFieldBudget {afr : AFRateModulus} (L : LargeFieldSuppression afr) :
    Σ' R : Q', ∀ N : Nat, ProductFloor.lossSum L.largeFieldDefect N ≤ R :=
  ⟨L.K * Q'.divPos 1 (1 - L.r) L.oneSubr_pos, largeFieldSuppression_summable L⟩

/-! ## 4. THE HONEST REDUCTION — the large-field defect IS the summable additive `ε_k`. -/

/-- `lossSum f N = tailSum f 0 N` (both add `f` at index `N`; the `0 + N` reindex). -/
theorem lossSum_eq_tailSum0 (f : Nat → Q') :
    ∀ N, ProductFloor.lossSum f N = tailSum f 0 N
  | 0 => rfl
  | N + 1 => by
      show ProductFloor.lossSum f N + f N = tailSum f 0 N + f (0 + N)
      rw [lossSum_eq_tailSum0 f N, Nat.zero_add]

/-- **The large-field budget in `tailSum … 0` form** — exactly the `hBε` hypothesis slot
of the PROVED adequacy engine `additiveErosion_uniform_floor`:

    ∀ k, tailSum δLF 0 k ≤ K/(1 − r) = Bε . -/
theorem largeField_epsBudget {afr : AFRateModulus} (L : LargeFieldSuppression afr) (k : Nat) :
    tailSum L.largeFieldDefect 0 k
      ≤ L.K * Q'.divPos 1 (1 - L.r) L.oneSubr_pos := by
  rw [← lossSum_eq_tailSum0 L.largeFieldDefect k]
  exact largeFieldSuppression_summable L k

/-- **THE HONEST LARGE-FIELD REDUCTION (guard-safe conditional).**  Take the large-field
defect as the ADDITIVE erosion `ε_k`.  GIVEN the small-field multiplicative recursion
(the parallel `s = 1` / higher-rep half: the step law `(1 − δ_k)·margin k − δLF_k ≤
margin(k+1)`, the defect budget `Σδ ≤ Bδ`, `δ_k ∈ [0,1]`, `margin 0 ≥ 0`) and the
ANCHOR-DOMINATES-BUDGET inequality `K/(1 − r) < (1 − Bδ)·margin 0`, the PROVED adequacy
engine DERIVES the strictly-positive uniform continuum floor:

    ∀ k, floorWitness ≤ margin k  ∧  0 < floorWitness,   floorWitness = (1 − Bδ)·m₀ − K/(1−r).

The large-field half is thus FULLY DISCHARGED: its only footprint is the FINITE geometric
budget `Bε = K/(1 − r)`, supplied by `largeField_epsBudget`.  This is a CONDITIONAL
producer (open binders on the small-field recursion + anchor-dominance) — it inhabits NO
frontier bundle; it feeds the already-PROVED `additiveErosion_uniform_floor`. -/
theorem largeField_additiveErosion_floor {afr : AFRateModulus} (L : LargeFieldSuppression afr)
    (margin δ : Nat → Q') (Bδ : Q')
    (hstep : ∀ k, (1 - δ k) * margin k - L.largeFieldDefect k ≤ margin (k + 1))
    (hδnn : ∀ k, (0 : Q') ≤ δ k) (hδ1 : ∀ k, δ k ≤ 1)
    (hm0 : (0 : Q') ≤ margin 0)
    (hBδ : ∀ k, tailSum δ 0 k ≤ Bδ)
    (hanchor : L.K * Q'.divPos 1 (1 - L.r) L.oneSubr_pos < (1 - Bδ) * margin 0) :
    ∀ k, (1 - Bδ) * margin 0 - (L.K * Q'.divPos 1 (1 - L.r) L.oneSubr_pos) ≤ margin k
       ∧ (0 : Q') < (1 - Bδ) * margin 0 - (L.K * Q'.divPos 1 (1 - L.r) L.oneSubr_pos) :=
  additiveErosion_uniform_floor margin δ L.largeFieldDefect Bδ
    (L.K * Q'.divPos 1 (1 - L.r) L.oneSubr_pos)
    hstep hδnn hδ1 L.lf_nonneg hm0 hBδ (largeField_epsBudget L) hanchor

/-! ## 5. Doc — PROVED vs NAMED-open (CRITICAL honesty, AGENTS.md Rule 6/9). -/

/-- **PROVED (genuine `Q'` facts, axiom-clean):**
  * `geomSum_le_recip` — geometric partial sums are bounded by `1/(1 − r)` (the analytic
    heart; contrast harmonic divergence).
  * `geomBudget_le` / `largeFieldSuppression_summable` / `largeFieldBudget` — the
    large-field budget is bounded by the explicit finite `Bε = K/(1 − r)` (SUMMABLE),
    returned as data.
  * `largeField_epsBudget` — the budget as the `hBε` slot of the proved adequacy engine.
  * `largeField_additiveErosion_floor` — the guard-safe reduction: the large-field defect,
    as the additive erosion `ε_k`, is DISCHARGED into `additiveErosion_uniform_floor`,
    yielding the positive continuum floor from the parallel small-field half + anchor
    dominance.  Contributes only the finite geometric `Bε`.

**ADVERSARIAL ORIENTATION (documented, validated numerically, not faked):** the large-field
fraction `F(θ₀,w) ≤ K·exp(−θ₀²/(4t))`, `t ∼ (1 − w)`, is EXPONENTIALLY suppressed and the
suppression IMPROVES as `w → 1` (weak coupling, large `k`).  Along AF (`1 − w_k ∼ A/(k+B)`)
this is GEOMETRIC in `k`: `F(w_k) ≤ K'·r^k`, `r = exp(−c/A) ∈ (0,1)`.  Strong coupling
(small `k`, large field not suppressed) is covered by the PROVED fixed-spacing gap.

**NAMED OPEN (NOT inhabited):** `LargeFieldSuppression` — the correctly-oriented geometric
large-field bound `δLF_k ≤ K·r^k`.  This is the honest large-field constant, the
large-field half of the Bałaban/MRS small-field theorem; the parallel deliverable supplies
the higher-rep character-tail (small-field) half.  Together they would discharge
`HeatKernelSecondCumulant.GapChannelDomination`.  NOTHING here inhabits
`GapChannelDomination` / `SingleStepDefectBound` / `TrueMarginRecursion*`; NO 4D
Yang–Mills mass gap is claimed; nothing is faked. -/
theorem routeE_honesty : True := trivial

end YMGap.Continuum.LargeFieldSuppression

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.LargeFieldSuppression.oneSub_le_one
#print axioms YMGap.Continuum.LargeFieldSuppression.geomSum_le_recip
#print axioms YMGap.Continuum.LargeFieldSuppression.lossSum_geomMajorant
#print axioms YMGap.Continuum.LargeFieldSuppression.geomBudget_le
#print axioms YMGap.Continuum.LargeFieldSuppression.lossSum_le_termwise
#print axioms YMGap.Continuum.LargeFieldSuppression.largeFieldSuppression_summable
#print axioms YMGap.Continuum.LargeFieldSuppression.largeFieldBudget
#print axioms YMGap.Continuum.LargeFieldSuppression.lossSum_eq_tailSum0
#print axioms YMGap.Continuum.LargeFieldSuppression.largeField_epsBudget
#print axioms YMGap.Continuum.LargeFieldSuppression.largeField_additiveErosion_floor
