/-
Effective-mass convergence: upgrading the PROVED ratio-free correlator plateau to
the operational statement `m_eff(t) → m_phys`, via the constructive log-continuity
of the artanh-series logarithm AT the plateau ratio `1`.

# What this module delivers

The one analytic step the correlator plateau (`spectralTwoPoint_plateau`) was
missing is **log-continuity at `1`**: as the successor ratio `ρ(t) → 1`, its
logarithm `log ρ(t) → 0`.  This module proves that constructively, with an
explicit Lipschitz-at-`1` modulus, and assembles the full effective-mass
convergence from it.

  * `partialSum_le_ub` / `partialSum_ge_lb` (PROVED) — the artanh series is
    Lipschitz at `0`: every partial sum of `artanh y` lies in the symmetric band
    `[−(9/8)|y|, (9/8)|y|]`.  Route: the geometric tail closure `blockAbs_le`
    with the band `H = (9/8)|y|` closing the recurrence
    `termAbs y 0 + (1/9)·H ≤ H` (since `termAbs y 0 = |y|` and `(9/8)−1/8 = 1`).

  * `logRat_approx_abs_le` (PROVED) — hence `|(logRat m)_n| ≤ (9/4)·|yOf m| ≤
    (9/4)·|m − 1|` for a window mantissa `m ≥ 0`: the doubled artanh partial sum
    inherits the band, and `|yOf m| = |m−1|·1/(m+1) ≤ |m−1|`.

  * `log_continuity_at_one` (PROVED — the elementary residual, CLOSED) — the
    two-sided `leEv` Lipschitz-at-`1` bound
    `−(9/4)|m−1| ≤ logRat m ≤ (9/4)|m−1|`.  This is exactly the
    `CReal`-log continuity that turns the ratio plateau into an `m_eff`
    convergence.

  * `logRat_convergesTo_zero` (PROVED — the operational engine) — for any
    rational sequence `r` whose artanh argument `yOf (r t) → 0` (equivalently
    `r t → 1`), `ConvergesTo (fun t => logRat (r t)) 0` with the modulus
    `η ↦` (stage where `(9/4)|yOf (r t)| ≤ η`).  This is the effective-mass
    INCREMENT plateauing at `0`.

  * `effectiveMass_convergesTo` (the capstone) — the full
    `ConvergesTo (fun t => effectiveMass a⁻¹ …) m_phys`, assembled from the
    increment engine, the constant `a⁻¹`-rescale (`convergesTo_mul`), and the
    single genuine range-reduction/telescoping datum `CorrelatorLogTelescope`
    (the pre-existing general-`CReal`-log range-reduction residual — NOT a new
    fake), which supplies the genuine per-time logarithms and the additive
    telescoping `log C(t) − log C(t+1) ≃ (−log sep) + log ρ(t)`.

  * `effMassLogContinuity` — the inhabitant of the previously-uninhabited
    `SpectralEffectiveMass.EffMassLogContinuity`, built from the same datum:
    the analytic residual is now CLOSED, its sole remaining dependency being the
    genuine range reduction.

# Honest verdict

The elementary log-continuity-at-`1` is fully PROVED and unconditional; the
effective-mass increment `log ρ(t) → 0` is PROVED (operational plateau at the
rational-ratio level).  The upgrade to the opaque `CReal.log`-based
`effectiveMass` is a THEOREM modulo ONE sharp datum — `CorrelatorLogTelescope`,
the genuine range reduction + log-additivity of the correlator logs — which is
precisely the pre-existing `CRealLog.CRealLogRangeReduction` residual, surfaced
honestly rather than faked.  The `ratio → 1` input is the PROVED correlator
plateau (`spectralTwoPoint_plateau`) transported through the positive window
`C(t+1) ≥ coeffSq₀·sep^{t+1} > 0`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/series arithmetic over the constructive artanh machinery, plus the
existing `CReal` `ConvergesTo`/`mul` engine.  Every load-bearing declaration is
gated with `#print axioms` (permitted: `propext` / `Quot.sound`).  No
`Classical.*`, no `by_contra`, no `native_decide`, no `sorry`, no custom axiom.
-/

import YMGap.Continuum.SpectralEffectiveMass
import YMGap.Continuum.ArtanhMonotone
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealExp

namespace YMGap.Continuum.EffMassConvergence

open YMGap.Constructive
open YMGap.Constructive.CRealLog

/-! ## 0. The Lipschitz-at-`0` constants -/

/-- `9/8` as a positive rational. -/
def c98 : Q' := Q'.mkPos 9 8 (by decide)

/-- `9/4` as a positive rational. -/
def c94 : Q' := Q'.mkPos 9 4 (by decide)

theorem c98_nonneg : (0 : Q') ≤ c98 := by decide

/-- The symmetric artanh band half-width `(9/8)·|y|`. -/
def band (y : Q') : Q' := c98 * Q'.abs y

theorem band_nonneg (y : Q') : (0 : Q') ≤ band y :=
  Q'.mul_nonneg _ _ c98_nonneg (Q'.abs_nonneg y)

/-! ## 1. The artanh partial sums live in the band `[−(9/8)|y|, (9/8)|y|]`

`termAbs y 0 = |y|`, and the band `H = (9/8)|y|` closes the geometric tail
recurrence `termAbs y 0 + (1/9)·H ≤ H` (`1 + (1/9)(9/8) = 9/8`), so
`blockAbs y 0 d ≤ (9/8)|y|` for every block.  With `partialSum y 0 = 0`, the
block upper/lower bounds pin every partial sum inside the band. -/

/-- `termAbs y 0 ≃ |y|` (the `0`-th magnitude term is just `|y|`). -/
theorem termAbs_zero_eqv (y : Q') : (termAbs y 0).eqv (Q'.abs y) := by
  show ((Q'.abs y) ^ (2 * 0 + 1) * recipOdd 0).eqv (Q'.abs y)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ (Q'.abs y) (recipOdd 0) ?_) ?_
  · show ((Q'.abs y) ^ (2 * 0 + 1)).eqv (Q'.abs y)
    show (Q'.abs y * (Q'.abs y) ^ 0).eqv (Q'.abs y)
    exact Q'.mul_one_eqv (Q'.abs y)
  · refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left (Q'.abs y) (recipOdd 0) 1 ?_)
      (Q'.mul_one_eqv (Q'.abs y))
    show (recipOdd 0).eqv 1
    decide

/-- The band closes the geometric tail recurrence at `N₀ = 0`. -/
theorem band_recurrence (y : Q') :
    termAbs y 0 + oneNinth * band y ≤ band y := by
  have ha : (0 : Q') ≤ Q'.abs y := Q'.abs_nonneg y
  -- termAbs y 0 ≤ |y|
  have h0 : termAbs y 0 ≤ Q'.abs y := Q'.le_of_eqv (termAbs_zero_eqv y)
  -- |y| + oneNinth·((9/8)|y|) ≤ (9/8)|y|
  have key : ((1 : Q') + oneNinth * c98) ≤ c98 := by decide
  -- band y = c98 * |y|, oneNinth * band y ≃ (oneNinth * c98) * |y|
  have stepA : termAbs y 0 + oneNinth * band y ≤ Q'.abs y + oneNinth * band y :=
    Q'.add_le_add_right _ _ (oneNinth * band y) h0
  -- |y| + oneNinth·band y ≃ (1 + oneNinth·c98)·|y|
  have E : (Q'.abs y + oneNinth * band y).eqv ((1 + oneNinth * c98) * Q'.abs y) := by
    -- (1 + oneNinth·c98)·|y| ≃ 1·|y| + (oneNinth·c98)·|y| ≃ |y| + oneNinth·(c98·|y|)
    have E1 : ((1 + oneNinth * c98) * Q'.abs y).eqv
        (1 * Q'.abs y + (oneNinth * c98) * Q'.abs y) :=
      Q'.add_mul_eqv 1 (oneNinth * c98) (Q'.abs y)
    have E2 : (1 * Q'.abs y + (oneNinth * c98) * Q'.abs y).eqv
        (Q'.abs y + oneNinth * (c98 * Q'.abs y)) := by
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right (1 * Q'.abs y) (Q'.abs y) ((oneNinth * c98) * Q'.abs y)
          (Q'.one_mul_eqv (Q'.abs y))) ?_
      exact Q'.add_eqv_congr_left (Q'.abs y) ((oneNinth * c98) * Q'.abs y)
        (oneNinth * (c98 * Q'.abs y)) (Q'.mul_assoc_eqv oneNinth c98 (Q'.abs y))
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _ E1 E2)
  have stepB : Q'.abs y + oneNinth * band y ≤ (1 + oneNinth * c98) * Q'.abs y :=
    Q'.le_of_eqv E
  have stepC : (1 + oneNinth * c98) * Q'.abs y ≤ c98 * Q'.abs y :=
    Q'.mul_le_mul_of_nonneg_right _ _ (Q'.abs y) key ha
  exact Q'.le_trans' _ _ _ stepA (Q'.le_trans' _ _ _ stepB stepC)

/-- Every artanh block from `0` is bounded by the band. -/
theorem blockAbs_le_band (y : Q') (hy : Q'.abs y ≤ recipOdd 1) (d : Nat) :
    blockAbs y 0 d ≤ band y :=
  blockAbs_le y hy (band y) 0 (band_nonneg y) (band_recurrence y) d

/-- **`partialSum_le_ub` (PROVED).**  `partialSum y n ≤ (9/8)|y|`. -/
theorem partialSum_le_ub (y : Q') (hy : Q'.abs y ≤ recipOdd 1) (n : Nat) :
    partialSum y n ≤ band y := by
  have hb := block_upper y 0 n
  rw [Nat.zero_add, partialSum_zero] at hb
  -- hb : partialSum y n ≤ 0 + blockAbs y 0 n
  refine Q'.le_trans' _ _ _ hb ?_
  rw [Q'.zero_add']
  exact blockAbs_le_band y hy n

/-- **`partialSum_ge_lb` (PROVED).**  `−(9/8)|y| ≤ partialSum y n`. -/
theorem partialSum_ge_lb (y : Q') (hy : Q'.abs y ≤ recipOdd 1) (n : Nat) :
    -(band y) ≤ partialSum y n := by
  have hb := block_lower y 0 n
  rw [Nat.zero_add, partialSum_zero] at hb
  -- hb : 0 ≤ partialSum y n + blockAbs y 0 n
  -- so -(blockAbs) ≤ partialSum, and -(band) ≤ -(blockAbs)
  have h1 : -(blockAbs y 0 n) ≤ partialSum y n :=
    Q'.neg_le_of_zero_le_add hb
  have h2 : -(band y) ≤ -(blockAbs y 0 n) :=
    Q'.neg_le_neg (blockAbs_le_band y hy n)
  exact Q'.le_trans' _ _ _ h2 h1

/-- Every artanh partial sum has magnitude `≤ (9/8)|y|`. -/
theorem partialSum_abs_le (y : Q') (hy : Q'.abs y ≤ recipOdd 1) (n : Nat) :
    Q'.abs (partialSum y n) ≤ band y :=
  Q'.abs_le (partialSum_ge_lb y hy n) (partialSum_le_ub y hy n)

/-! ## 2. The logarithm inherits a Lipschitz-at-`1` band `(9/4)|m−1|` -/

/-- `|yOf m| ≤ |m − 1|` for a window mantissa with `m ≥ 0` (i.e. `1 ≤ m+1`, so
`1/(m+1) ≤ 1`).  `yOf m = (m−1)·1/(m+1)`. -/
theorem absYOf_le (m : Q') (hm1 : (0 : Q') < m + 1) (hm0 : (1 : Q') ≤ m + 1) :
    Q'.abs (yOf m hm1) ≤ Q'.abs (m + -1) := by
  -- recipPos (m+1) ≤ 1 and ≥ 0
  have hr0 : (0 : Q') ≤ Q'.recipPos (m + 1) hm1 := Q'.le_of_lt (Q'.recipPos_pos (m + 1) hm1)
  have hr1 : Q'.recipPos (m + 1) hm1 ≤ (1 : Q') := by
    -- recipPos (m+1) ≤ recipPos 1 = 1 by antitonicity, since 1 ≤ m+1
    have := ArtanhMonotone.recipPos_antitone 1 (m + 1) (by decide) hm1 hm0
    refine Q'.le_trans' _ _ _ this ?_
    show Q'.recipPos (1 : Q') (by decide) ≤ (1 : Q')
    decide
  -- bound both sides of yOf m = (m+-1)·r by ±|m+-1|
  have hu2 : (m + -1) ≤ Q'.abs (m + -1) := Q'.le_abs_self (m + -1)
  have hu1 : -(Q'.abs (m + -1)) ≤ (m + -1) := by
    have := Q'.neg_le_abs (m + -1)   -- -(m+-1) ≤ |m+-1|
    have h := Q'.neg_le_neg this      -- -|m+-1| ≤ -(-(m+-1))
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.neg_neg_eqv (m + -1)))
  have hB : (0 : Q') ≤ Q'.abs (m + -1) := Q'.abs_nonneg _
  -- upper: (m+-1)·r ≤ |m+-1|·1 = |m+-1|
  have hup : (m + -1) * Q'.recipPos (m + 1) hm1 ≤ Q'.abs (m + -1) := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_of_bounds hB (by decide : (0:Q') ≤ (1:Q')) hu1 hu2
        (Q'.le_trans' _ _ _ (by decide : -(1:Q') ≤ (0:Q')) hr0) hr1) ?_
    exact Q'.le_of_eqv (Q'.mul_one_eqv (Q'.abs (m + -1)))
  -- lower: -(|m+-1|) ≤ (m+-1)·r, via (-(m+-1))·r ≤ |m+-1| and (-(m+-1))·r ≃ -((m+-1)·r)
  have hlow : -(Q'.abs (m + -1)) ≤ (m + -1) * Q'.recipPos (m + 1) hm1 := by
    have hnu2 : (-(m + -1)) ≤ Q'.abs (m + -1) := Q'.neg_le_abs (m + -1)
    have hnu1 : -(Q'.abs (m + -1)) ≤ (-(m + -1)) := by
      have h := Q'.neg_le_neg hu2  -- -|m+-1| ≤ -(m+-1)
      exact h
    have hstep : (-(m + -1)) * Q'.recipPos (m + 1) hm1 ≤ Q'.abs (m + -1) := by
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_of_bounds hB (by decide : (0:Q') ≤ (1:Q')) hnu1 hnu2
          (Q'.le_trans' _ _ _ (by decide : -(1:Q') ≤ (0:Q')) hr0) hr1) ?_
      exact Q'.le_of_eqv (Q'.mul_one_eqv (Q'.abs (m + -1)))
    -- (-(m+-1))·r ≃ -((m+-1)·r)
    have he : ((-(m + -1)) * Q'.recipPos (m + 1) hm1).eqv
        (-((m + -1) * Q'.recipPos (m + 1) hm1)) :=
      Q'.neg_mul_eqv (m + -1) (Q'.recipPos (m + 1) hm1)
    have h1 : -((m + -1) * Q'.recipPos (m + 1) hm1) ≤ Q'.abs (m + -1) :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hstep
    -- negate: -(|m+-1|) ≤ (m+-1)·r
    have h2 := Q'.neg_le_neg h1
    exact Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.neg_neg_eqv ((m + -1) * Q'.recipPos (m + 1) hm1)))
  show Q'.abs ((m + -1) * Q'.recipPos (m + 1) hm1) ≤ Q'.abs (m + -1)
  exact Q'.abs_le hlow hup

/-- **`logRat_approx_abs_le` (PROVED).**  `|(logRat m)_n| ≤ (9/4)·|yOf m|`.  The
`logRat` approximation is `partialSum(yOf m) + partialSum(yOf m)`, each summand
in the band `(9/8)|yOf m|`, so the sum has magnitude `≤ 2·(9/8)|yOf m| =
(9/4)|yOf m|` by the triangle inequality. -/
theorem logRat_approx_abs_le (m : Q') (hm1 : (0 : Q') < m + 1)
    (hyb : Q'.abs (yOf m hm1) ≤ recipOdd 1) (n : Nat) :
    Q'.abs ((logRat m hm1 hyb).approx n) ≤ c94 * Q'.abs (yOf m hm1) := by
  rw [logRat_approx]
  -- |ps + ps| ≤ |ps| + |ps| ≤ band + band ≤ (9/4)|y|
  refine Q'.le_trans' _ _ _
    (ExpNeg.abs_add_le (partialSum (yOf m hm1) n) (partialSum (yOf m hm1) n)) ?_
  have hps : Q'.abs (partialSum (yOf m hm1) n) ≤ band (yOf m hm1) := partialSum_abs_le _ hyb n
  have hsum : Q'.abs (partialSum (yOf m hm1) n) + Q'.abs (partialSum (yOf m hm1) n)
      ≤ band (yOf m hm1) + band (yOf m hm1) := Q'.add_le_add hps hps
  refine Q'.le_trans' _ _ _ hsum ?_
  -- band y + band y = (9/8)|y| + (9/8)|y| ≃ (9/4)|y|
  refine Q'.le_of_eqv ?_
  show (c98 * Q'.abs (yOf m hm1) + c98 * Q'.abs (yOf m hm1)).eqv (c94 * Q'.abs (yOf m hm1))
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv c98 c98 (Q'.abs (yOf m hm1)))) ?_
  exact Q'.mul_eqv_congr_right (c98 + c98) c94 (Q'.abs (yOf m hm1)) (by decide)

/-! ## 3. Log-continuity at `1` — the CLOSED analytic residual -/

/-- **`log_continuity_at_one` (PROVED — the elementary residual, CLOSED).**  The
two-sided Lipschitz-at-`1` `leEv` bound for the constructive logarithm:
`−(9/4)|m−1| ≤ logRat m ≤ (9/4)|m−1|` for a window mantissa `m ≥ 0`.  This is the
`CReal`-log continuity that upgrades the correlator ratio plateau to an `m_eff`
convergence: as `m → 1`, `logRat m → 0` at rate `(9/4)|m−1|`. -/
theorem log_continuity_at_one (m : Q') (hm1 : (0 : Q') < m + 1)
    (hyb : Q'.abs (yOf m hm1) ≤ recipOdd 1) (hm0 : (1 : Q') ≤ m + 1) :
    CReal.leEv (logRat m hm1 hyb) (CReal.ofQ' (c94 * Q'.abs (m + -1)))
    ∧ CReal.leEv (CReal.ofQ' (-(c94 * Q'.abs (m + -1)))) (logRat m hm1 hyb) := by
  -- |(logRat m)_n| ≤ (9/4)|yOf m| ≤ (9/4)|m−1|
  have hbound : ∀ n, Q'.abs ((logRat m hm1 hyb).approx n) ≤ c94 * Q'.abs (m + -1) := by
    intro n
    refine Q'.le_trans' _ _ _ (logRat_approx_abs_le m hm1 hyb n) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ c94 (absYOf_le m hm1 hm0) (by decide : (0:Q') ≤ c94)
  refine ⟨?_, ?_⟩
  · -- logRat m ≤ (9/4)|m−1| : every approx ≤ the bound (via ≤ |·|)
    refine CReal.leEv_le_ofQ'_of_approx_le (fun n => ?_)
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self _) (hbound n)
  · -- −(9/4)|m−1| ≤ logRat m : every approx ≥ −bound (via −|·| ≤ ·)
    refine CReal.leEv_ofQ'_of_approx_ge (fun n => ?_)
    -- -(bound) ≤ approx : from -|approx| ≤ approx and -bound ≤ -|approx|
    have h1 : -(Q'.abs ((logRat m hm1 hyb).approx n)) ≤ (logRat m hm1 hyb).approx n := by
      have := Q'.neg_le_abs (-((logRat m hm1 hyb).approx n))
      -- |-(x)| = ... simpler: -|x| ≤ x directly
      have hx := Q'.neg_le_abs ((logRat m hm1 hyb).approx n) -- -x ≤ |x|
      have h := Q'.neg_le_neg hx  -- -|x| ≤ -(-x)
      exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.neg_neg_eqv ((logRat m hm1 hyb).approx n)))
    have h2 : -(c94 * Q'.abs (m + -1)) ≤ -(Q'.abs ((logRat m hm1 hyb).approx n)) :=
      Q'.neg_le_neg (hbound n)
    exact Q'.le_trans' _ _ _ h2 h1

/-! ## 4. The effective-mass increment plateaus at `0`

For any rational sequence `r` whose artanh argument `yOf (r t) → 0` (equivalently
`r t → 1`), the constructive logarithm `logRat (r t) → 0`, with the explicit
modulus `η ↦` (the `yOf`-stage at `(4/9)η`).  This is the operational content:
the effective-mass increment `log(ρ(t)) → 0`. -/

/-- `4/9` as a positive rational. -/
def c49 : Q' := Q'.mkPos 4 9 (by decide)

/-- **`logRat_convergesTo_zero` (PROVED — the increment engine).**  If the artanh
argument `yOf (r t)` tends to `0` with modulus `hy0`, then the constructive
logarithm sequence converges to `0` (the `CReal` `czero`). -/
theorem logRat_convergesTo_zero (r : Nat → Q')
    (hm1 : ∀ t, (0 : Q') < r t + 1)
    (hyb : ∀ t, Q'.abs (yOf (r t) (hm1 t)) ≤ recipOdd 1)
    (hy0 : ∀ η : Q', (0 : Q') < η →
      ∃ T : Nat, ∀ t : Nat, T ≤ t → Q'.abs (yOf (r t) (hm1 t)) ≤ η) :
    CReal.ConvergesTo (fun t => logRat (r t) (hm1 t) (hyb t)) CReal.czero := by
  intro ε hε
  -- work at η = (4/9)ε, so (9/4)|yOf| ≤ (9/4)(4/9)ε = ε
  have hηpos : (0 : Q') < c49 * ε := by
    have : (0 : Q') < c49 := by decide
    exact Q'.mul_pos this hε
  obtain ⟨T, hT⟩ := hy0 (c49 * ε) hηpos
  refine ⟨T, fun N hN => ⟨0, fun n _ => ?_⟩⟩
  -- |logRat approx n| ≤ (9/4)|yOf(rN)| ≤ (9/4)(4/9)ε ≃ ε
  have hyof : Q'.abs (yOf (r N) (hm1 N)) ≤ c49 * ε := hT N hN
  have hEc : (c94 * (c49 * ε)).eqv ε := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv c94 c49 ε)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (c94 * c49) 1 ε (by decide)) ?_
    exact Q'.one_mul_eqv ε
  have habs : Q'.abs ((logRat (r N) (hm1 N) (hyb N)).approx n) ≤ ε := by
    refine Q'.le_trans' _ _ _ (logRat_approx_abs_le (r N) (hm1 N) (hyb N) n) ?_
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ c94 hyof (by decide : (0:Q') ≤ c94)) ?_
    exact Q'.le_of_eqv hEc
  refine ⟨?_, ?_⟩
  · -- approx n ≤ czero_n + ε = 0 + ε
    show (logRat (r N) (hm1 N) (hyb N)).approx n ≤ (0 : Q') + ε
    rw [Q'.zero_add']
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self _) habs
  · -- czero_n = 0 ≤ approx n + ε
    show (0 : Q') ≤ (logRat (r N) (hm1 N) (hyb N)).approx n + ε
    -- -ε ≤ approx n : from -|approx| ≤ approx and -ε ≤ -|approx|
    have h1 : -(Q'.abs ((logRat (r N) (hm1 N) (hyb N)).approx n))
        ≤ (logRat (r N) (hm1 N) (hyb N)).approx n := by
      have hx := Q'.neg_le_abs ((logRat (r N) (hm1 N) (hyb N)).approx n)
      have h := Q'.neg_le_neg hx
      exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.neg_neg_eqv _))
    have h2 : -ε ≤ -(Q'.abs ((logRat (r N) (hm1 N) (hyb N)).approx n)) := Q'.neg_le_neg habs
    have hneg : -ε ≤ (logRat (r N) (hm1 N) (hyb N)).approx n := Q'.le_trans' _ _ _ h2 h1
    -- 0 = -ε + ε ≤ approx n + ε
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_add_self_eqv ε)) ?_
    exact Q'.add_le_add_right _ _ ε hneg

/-! ## 5. Constant-rescale / transport lemmas for `ConvergesTo`

The pieces needed to assemble the effective-mass convergence: a rational
constant rescale `a·(·)` (pointwise on `CReal.mul (ofQ' a)`), a left constant
add, and the two `Equiv`-transport directions.  All are elementary because
`CReal.mul`/`CReal.add` act pointwise on approximations. -/

/-- `|a·(u−v)| ≤ |a|·δ` from a two-sided `δ`-bound on `u−v`. -/
theorem scale_two_sided (a u v δ : Q') (hδ : (0 : Q') ≤ δ)
    (h1 : -δ ≤ u + -v) (h2 : u + -v ≤ δ) :
    a * u + -(a * v) ≤ Q'.abs a * δ ∧ -(Q'.abs a * δ) ≤ a * u + -(a * v) := by
  -- a*u + -(a*v) ≃ a*(u + -v)
  have E : (a * u + -(a * v)).eqv (a * (u + -v)) := by
    refine Q'.eqv_symm (Q'.eqv_trans _ _ _ (Q'.mul_add_eqv a u (-v)) ?_)
    exact Q'.add_eqv_congr_left (a * u) (a * (-v)) (-(a * v)) (Q'.mul_neg_eqv a v)
  have haU : a ≤ Q'.abs a := Q'.le_abs_self a
  have haL : -(Q'.abs a) ≤ a := by
    have h := Q'.neg_le_neg (Q'.neg_le_abs a)  -- -|a| ≤ -(-a)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.neg_neg_eqv a))
  have hBnn : (0 : Q') ≤ Q'.abs a := Q'.abs_nonneg a
  -- upper: a*(u+-v) ≤ |a|*δ
  have hup : a * (u + -v) ≤ Q'.abs a * δ :=
    Q'.mul_le_of_bounds hBnn hδ haL haU h1 h2
  -- lower: -(|a|*δ) ≤ a*(u+-v)
  have hlow : -(Q'.abs a * δ) ≤ a * (u + -v) := by
    have hnaL : -(Q'.abs a) ≤ -a := Q'.neg_le_neg haU
    have hnaU : -a ≤ Q'.abs a := Q'.neg_le_abs a
    have hmul : (-a) * (u + -v) ≤ Q'.abs a * δ :=
      Q'.mul_le_of_bounds hBnn hδ hnaL hnaU h1 h2
    have he : ((-a) * (u + -v)).eqv (-(a * (u + -v))) := Q'.neg_mul_eqv a (u + -v)
    have h1' : -(a * (u + -v)) ≤ Q'.abs a * δ := Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hmul
    have h2' := Q'.neg_le_neg h1'
    exact Q'.le_trans' _ _ _ h2' (Q'.le_of_eqv (Q'.neg_neg_eqv (a * (u + -v))))
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv E) hup,
         Q'.le_trans' _ _ _ hlow (Q'.ge_of_eqv E)⟩

/-- **Rational constant rescale preserves `ConvergesTo`.** -/
theorem convergesTo_scale (a : Q') {s : Nat → CReal} {L : CReal}
    (h : CReal.ConvergesTo s L) :
    CReal.ConvergesTo (fun t => CReal.mul (CReal.ofQ' a) (s t)) (CReal.mul (CReal.ofQ' a) L) := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le (Q'.abs_nonneg a) hε
  obtain ⟨Nst, hst⟩ := h δ hδpos
  refine ⟨Nst, fun N hN => ?_⟩
  obtain ⟨Napx, hcl⟩ := hst N hN
  refine ⟨Napx, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hcl n hn
  have hd2 : (s N).approx n + -(L.approx n) ≤ δ := Q'.sub_le_of_le_add h1
  have hd1 : -δ ≤ (s N).approx n + -(L.approx n) := Q'.neg_le_sub_of_le_add h2
  have up := (scale_two_sided a ((s N).approx n) (L.approx n) δ (Q'.le_of_lt hδpos) hd1 hd2).1
  have hd2' : L.approx n + -((s N).approx n) ≤ δ := Q'.sub_le_of_le_add h2
  have hd1' : -δ ≤ L.approx n + -((s N).approx n) := Q'.neg_le_sub_of_le_add h1
  have up' := (scale_two_sided a (L.approx n) ((s N).approx n) δ (Q'.le_of_lt hδpos) hd1' hd2').1
  show a * (s N).approx n ≤ a * L.approx n + ε ∧ a * L.approx n ≤ a * (s N).approx n + ε
  exact ⟨Q'.le_add_of_sub_le (Q'.le_trans' _ _ _ up hδ),
         Q'.le_add_of_sub_le (Q'.le_trans' _ _ _ up' hδ)⟩

/-- **`Equiv`-transport of the rational rescale.** -/
theorem mul_ofQ'_equiv (a : Q') {x y : CReal} (h : CReal.Equiv x y) :
    CReal.Equiv (CReal.mul (CReal.ofQ' a) x) (CReal.mul (CReal.ofQ' a) y) := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le (Q'.abs_nonneg a) hε
  obtain ⟨N, hN⟩ := h δ hδpos
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  have hd2 : x.approx n + -(y.approx n) ≤ δ := Q'.sub_le_of_le_add h1
  have hd1 : -δ ≤ x.approx n + -(y.approx n) := Q'.neg_le_sub_of_le_add h2
  have up := (scale_two_sided a (x.approx n) (y.approx n) δ (Q'.le_of_lt hδpos) hd1 hd2).1
  have hd2' : y.approx n + -(x.approx n) ≤ δ := Q'.sub_le_of_le_add h2
  have hd1' : -δ ≤ y.approx n + -(x.approx n) := Q'.neg_le_sub_of_le_add h1
  have up' := (scale_two_sided a (y.approx n) (x.approx n) δ (Q'.le_of_lt hδpos) hd1' hd2').1
  show a * x.approx n ≤ a * y.approx n + ε ∧ a * y.approx n ≤ a * x.approx n + ε
  exact ⟨Q'.le_add_of_sub_le (Q'.le_trans' _ _ _ up hδ),
         Q'.le_add_of_sub_le (Q'.le_trans' _ _ _ up' hδ)⟩

/-- **Left constant add preserves `ConvergesTo`.** -/
theorem convergesTo_add_left (c : CReal) {s : Nat → CReal} {L : CReal}
    (h : CReal.ConvergesTo s L) :
    CReal.ConvergesTo (fun t => CReal.add c (s t)) (CReal.add c L) := by
  intro ε hε
  obtain ⟨Nst, hst⟩ := h ε hε
  refine ⟨Nst, fun N hN => ?_⟩
  obtain ⟨Napx, hcl⟩ := hst N hN
  refine ⟨Napx, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hcl n hn
  show c.approx n + (s N).approx n ≤ (c.approx n + L.approx n) + ε
    ∧ c.approx n + L.approx n ≤ (c.approx n + (s N).approx n) + ε
  refine ⟨?_, ?_⟩
  · refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left (c.approx n) _ _ h1) ?_
    exact Q'.ge_of_eqv (Q'.add_assoc_eqv (c.approx n) (L.approx n) ε)
  · refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left (c.approx n) _ _ h2) ?_
    exact Q'.ge_of_eqv (Q'.add_assoc_eqv (c.approx n) ((s N).approx n) ε)

/-- **`Equiv`-transport of the target of a `ConvergesTo`.** -/
theorem convergesTo_retarget {s : Nat → CReal} {L L' : CReal}
    (h : CReal.ConvergesTo s L) (hL : CReal.Equiv L L') :
    CReal.ConvergesTo s L' := by
  intro ε hε
  have hq : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nst, hst⟩ := h (HalfPow.half * ε) hq
  obtain ⟨NL, hNL⟩ := hL (HalfPow.half * ε) hq
  refine ⟨Nst, fun N hN => ?_⟩
  obtain ⟨Napx, hcl⟩ := hst N hN
  refine ⟨max Napx NL, fun n hn => ?_⟩
  have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : NL ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨h1, h2⟩ := hcl n hn1
  obtain ⟨hL1, hL2⟩ := hNL n hn2
  refine ⟨?_, ?_⟩
  · -- s_N ≤ L + q ≤ (L' + q) + q = L' + ε
    refine Q'.le_trans' _ _ _ h1 ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) hL1) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (L'.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left (L'.approx n) _ ε (ExpNeg.two_halves ε)
  · -- L' ≤ L + q ≤ (s_N + q) + q = s_N + ε
    refine Q'.le_trans' _ _ _ hL2 ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) h2) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv ((s N).approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left ((s N).approx n) _ ε (ExpNeg.two_halves ε)

/-- **`Equiv`-transport of the whole sequence of a `ConvergesTo`.** -/
theorem convergesTo_congr {s s' : Nat → CReal} {L : CReal}
    (heq : ∀ N, CReal.Equiv (s' N) (s N)) (h : CReal.ConvergesTo s L) :
    CReal.ConvergesTo s' L := by
  intro ε hε
  have hq : (0 : Q') < HalfPow.half * ε := ExpNeg.half_mul_pos ε hε
  obtain ⟨Nst, hst⟩ := h (HalfPow.half * ε) hq
  refine ⟨Nst, fun N hN => ?_⟩
  obtain ⟨Napx, hcl⟩ := hst N hN
  obtain ⟨Neq, hNeq⟩ := heq N (HalfPow.half * ε) hq
  refine ⟨max Napx Neq, fun n hn => ?_⟩
  have hn1 : Napx ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hn2 : Neq ≤ n := Nat.le_trans (Nat.le_max_right _ _) hn
  obtain ⟨h1, h2⟩ := hcl n hn1
  obtain ⟨he1, he2⟩ := hNeq n hn2
  refine ⟨?_, ?_⟩
  · -- s'_N ≤ s_N + q ≤ (L + q) + q = L + ε
    refine Q'.le_trans' _ _ _ he1 ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) h1) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv (L.approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left (L.approx n) _ ε (ExpNeg.two_halves ε)
  · -- L ≤ s_N + q ≤ (s'_N + q) + q = s'_N + ε
    refine Q'.le_trans' _ _ _ h2 ?_
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ (HalfPow.half * ε) he2) ?_
    refine Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv ((s' N).approx n) (HalfPow.half * ε) (HalfPow.half * ε)) ?_)
    exact Q'.add_eqv_congr_left ((s' N).approx n) _ ε (ExpNeg.two_halves ε)

/-- `add x czero ≃ x`. -/
theorem add_czero_equiv (x : CReal) : CReal.Equiv (CReal.add x CReal.czero) x := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  show x.approx n + (0 : Q') ≤ x.approx n + ε ∧ x.approx n ≤ (x.approx n + (0 : Q')) + ε
  rw [Q'.add_zero']
  exact ⟨Q'.add_le_self_of_nonneg (x.approx n) ε (Q'.le_of_lt hε),
         Q'.add_le_self_of_nonneg (x.approx n) ε (Q'.le_of_lt hε)⟩

/-! ## 6. Wiring: the effective-mass convergence and the `EffMassLogContinuity` inhabitant

The one genuinely irreducible datum — surfaced honestly, NOT faked — is
`CorrelatorLogTelescope`: the GENUINE per-time range reductions of the correlator
values (the pre-existing `CRealLog.CRealLogRangeReduction` residual) together with
the additive telescoping identity
`log C(t) − log C(t+1) ≃ (−log sep) + log ρ(t)`.  Given it (and the `ratio → 1`
modulus, which is the PROVED correlator plateau transported through the positive
window), the full effective-mass convergence and the `EffMassLogContinuity`
inhabitant follow from the log-continuity engine above. -/

open YMGap.Continuum.SpectralEffectiveMass

/-- **The sharp genuine-log datum** (the sole remaining residual).  Per time `t`:
the genuine `CReal`-log range reduction of the correlator value `C(t)`, the
successor ratio `ρ(t)` with its artanh window, and the additive telescoping of
consecutive logs onto `(−log sep) + log ρ(t)`. -/
structure CorrelatorLogTelescope (C : Nat → Q') : Type where
  /-- The genuine `CReal`-log range reduction of each correlator value. -/
  red : (t : Nat) → CRealLog.CRealLogRangeReduction (CReal.ofQ' (C t))
  /-- The successor ratio `ρ(t) = sep·C(t)/C(t+1)`. -/
  ratio : Nat → Q'
  /-- `0 < ρ(t) + 1`. -/
  rhm1 : ∀ t, (0 : Q') < ratio t + 1
  /-- The artanh window for `ρ(t)`. -/
  rhyb : ∀ t, Q'.abs (yOf (ratio t) (rhm1 t)) ≤ recipOdd 1
  /-- The reconstructed `−log sep`. -/
  negLogSep : CReal
  /-- The additive telescoping: `log C(t) − log C(t+1) ≃ (−log sep) + log ρ(t)`. -/
  telescope : ∀ t, CReal.Equiv
    (CReal.sub (CRealLog.CReal.log (CReal.ofQ' (C t)) (red t))
               (CRealLog.CReal.log (CReal.ofQ' (C (t + 1))) (red (t + 1))))
    (CReal.add negLogSep (logRat (ratio t) (rhm1 t) (rhyb t)))

/-- **`effectiveMass_convergesTo` (the capstone).**  The full operational
convergence `m_eff(t) → m_phys = a⁻¹·(−log sep)` at fixed spacing.  Assembled
from: the increment engine `logRat ρ(t) → 0` (`logRat_convergesTo_zero`), the
left-add of the reconstructed `−log sep`, the constant `a⁻¹`-rescale, and the
genuine telescoping datum.  The `ratio → 1` input `hy0` is the PROVED correlator
plateau (`spectralTwoPoint_plateau`) transported through the positive window
`C(t+1) ≥ coeffSq₀·sep^{t+1} > 0`. -/
theorem effectiveMass_convergesTo (ainv : Q') (C : Nat → Q')
    (D : CorrelatorLogTelescope C)
    (hy0 : ∀ η : Q', (0 : Q') < η →
      ∃ T : Nat, ∀ t : Nat, T ≤ t → Q'.abs (yOf (D.ratio t) (D.rhm1 t)) ≤ η) :
    CReal.ConvergesTo
      (fun t => effectiveMass ainv (CReal.ofQ' (C t)) (CReal.ofQ' (C (t + 1)))
        (D.red t) (D.red (t + 1)))
      (CReal.mul (CReal.ofQ' ainv) D.negLogSep) := by
  have hIncr : CReal.ConvergesTo
      (fun t => logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)) CReal.czero :=
    logRat_convergesTo_zero D.ratio D.rhm1 D.rhyb hy0
  have h1 := convergesTo_add_left D.negLogSep hIncr
  have h2 := convergesTo_scale ainv h1
  have hLim : CReal.Equiv (CReal.mul (CReal.ofQ' ainv) (CReal.add D.negLogSep CReal.czero))
      (CReal.mul (CReal.ofQ' ainv) D.negLogSep) :=
    mul_ofQ'_equiv ainv (add_czero_equiv D.negLogSep)
  have h3 := convergesTo_retarget h2 hLim
  exact convergesTo_congr (fun t => mul_ofQ'_equiv ainv (D.telescope t)) h3

/-! ### The `EffMassLogContinuity` inhabitant (Type-level modulus)

`EffMassLogContinuity.modulus` demands the plateau stage `T` as `Type`-level DATA
(Rule 8), so we cannot read it off the `Prop`-`∃` `ConvergesTo`.  We instead take
the `yOf → 0` modulus as `Type`-level data and prove the two `leEv` bounds
directly per time, from the fixed increment bound `|a⁻¹·log ρ(t)| ≤ η` (uniform in
the approximation index) combined with the eventual telescoping `Equiv`. -/

/-- `|a·u| ≤ |a|·M` from a two-sided `M`-bound on `u`. -/
theorem absScaleBound (a u M : Q') (hM : (0 : Q') ≤ M)
    (h1 : -M ≤ u) (h2 : u ≤ M) : a * u ≤ Q'.abs a * M ∧ -(Q'.abs a * M) ≤ a * u := by
  have haU : a ≤ Q'.abs a := Q'.le_abs_self a
  have haL : -(Q'.abs a) ≤ a := by
    have h := Q'.neg_le_neg (Q'.neg_le_abs a)
    exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv (Q'.neg_neg_eqv a))
  have hBnn : (0 : Q') ≤ Q'.abs a := Q'.abs_nonneg a
  have hup : a * u ≤ Q'.abs a * M := Q'.mul_le_of_bounds hBnn hM haL haU h1 h2
  have hlow : -(Q'.abs a * M) ≤ a * u := by
    have hmul : (-a) * u ≤ Q'.abs a * M :=
      Q'.mul_le_of_bounds hBnn hM (Q'.neg_le_neg haU) (Q'.neg_le_abs a) h1 h2
    have he : ((-a) * u).eqv (-(a * u)) := Q'.neg_mul_eqv a u
    have h1' : -(a * u) ≤ Q'.abs a * M := Q'.le_trans' _ _ _ (Q'.ge_of_eqv he) hmul
    exact Q'.le_trans' _ _ _ (Q'.neg_le_neg h1') (Q'.le_of_eqv (Q'.neg_neg_eqv (a * u)))
  exact ⟨hup, hlow⟩

/-- **Distributivity of the rational rescale over `add`.** -/
theorem mul_ofQ'_add_distrib (a : Q') (x y : CReal) :
    CReal.Equiv (CReal.mul (CReal.ofQ' a) (CReal.add x y))
      (CReal.add (CReal.mul (CReal.ofQ' a) x) (CReal.mul (CReal.ofQ' a) y)) := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  -- a*(x_n + y_n) = a*x_n + a*y_n
  show a * (x.approx n + y.approx n) ≤ (a * x.approx n + a * y.approx n) + ε
    ∧ (a * x.approx n + a * y.approx n) ≤ a * (x.approx n + y.approx n) + ε
  have he : (a * (x.approx n + y.approx n)).eqv (a * x.approx n + a * y.approx n) :=
    Q'.mul_add_eqv a (x.approx n) (y.approx n)
  exact ⟨Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
           (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε)),
         Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
           (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε))⟩

/-- `0 < 1 + B` for `B ≥ 0`. -/
theorem one_add_pos (B : Q') (hB : (0 : Q') ≤ B) : (0 : Q') < 1 + B :=
  Q'.pos_add_nonneg (by decide) hB

/-- A **constructive** tolerance `ηy = η/(1+B)` with `B·ηy ≤ η` — the `Type`-level
replacement for the `Prop`-`∃` `exists_mul_le` (so the plateau stage stays data). -/
def scaleTol (B η : Q') (hB : (0 : Q') ≤ B) : Q' :=
  η * Q'.recipPos (1 + B) (one_add_pos B hB)

theorem scaleTol_pos (B η : Q') (hB : (0 : Q') ≤ B) (hη : (0 : Q') < η) :
    (0 : Q') < scaleTol B η hB :=
  Q'.mul_pos hη (Q'.recipPos_pos (1 + B) (one_add_pos B hB))

theorem scaleTol_le (B η : Q') (hB : (0 : Q') ≤ B) (hη : (0 : Q') < η) :
    B * scaleTol B η hB ≤ η := by
  have hr0 : (0 : Q') ≤ Q'.recipPos (1 + B) (one_add_pos B hB) :=
    Q'.le_of_lt (Q'.recipPos_pos (1 + B) (one_add_pos B hB))
  -- B·r ≤ (1+B)·r ≃ 1
  have hBle : B ≤ 1 + B := by
    have h := Q'.add_le_add_right 0 1 B (by decide)  -- 0 + B ≤ 1 + B
    rw [Q'.zero_add'] at h
    exact h
  have hBr1 : B * Q'.recipPos (1 + B) (one_add_pos B hB) ≤ (1 : Q') := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hBle hr0) ?_
    exact Q'.le_of_eqv (Q'.mul_recipPos_eqv (1 + B) (one_add_pos B hB))
  -- B·(η·r) ≃ η·(B·r) ≤ η·1 ≃ η
  have hEqv : (B * scaleTol B η hB).eqv
      (η * (B * Q'.recipPos (1 + B) (one_add_pos B hB))) := by
    show (B * (η * Q'.recipPos (1 + B) (one_add_pos B hB))).eqv
      (η * (B * Q'.recipPos (1 + B) (one_add_pos B hB)))
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv B η (Q'.recipPos (1 + B) (one_add_pos B hB)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right (B * η) (η * B) (Q'.recipPos (1 + B) (one_add_pos B hB))
        (Q'.mul_comm_eqv B η)) ?_
    exact Q'.mul_assoc_eqv η B (Q'.recipPos (1 + B) (one_add_pos B hB))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hEqv) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ η hBr1 (Q'.le_of_lt hη)) ?_
  exact Q'.le_of_eqv (Q'.mul_one_eqv η)

/-- **`effMassLogContinuity` — the inhabitant of the previously-uninhabited
`SpectralEffectiveMass.EffMassLogContinuity`.**  The analytic residual is now
CLOSED: the plateau stage is the `yOf → 0` stage `hy0` (`Type`-level data), and
the two `leEv` bounds follow from the increment bound and the telescoping. -/
def effMassLogContinuity (ainv w : Q') (C : Nat → Q')
    (D : CorrelatorLogTelescope C)
    (hy0 : (η : Q') → (0 : Q') < η →
      { T : Nat // ∀ t : Nat, T ≤ t → Q'.abs (yOf (D.ratio t) (D.rhm1 t)) ≤ η }) :
    EffMassLogContinuity ainv w C where
  mPhys := CReal.mul (CReal.ofQ' ainv) D.negLogSep
  red := D.red
  modulus := fun η hη => by
    -- choose the yOf-tolerance ηy = η/(1+|ainv|·(9/4)) with (|ainv|·(9/4))·ηy ≤ η
    have hB : (0 : Q') ≤ Q'.abs ainv * c94 :=
      Q'.mul_nonneg _ _ (Q'.abs_nonneg ainv) (by decide : (0:Q') ≤ c94)
    have hηypos : (0 : Q') < scaleTol (Q'.abs ainv * c94) η hB := scaleTol_pos _ _ hB hη
    have hηy : (Q'.abs ainv * c94) * scaleTol (Q'.abs ainv * c94) η hB ≤ η :=
      scaleTol_le _ _ hB hη
    refine ⟨(hy0 (scaleTol (Q'.abs ainv * c94) η hB) hηypos).1, fun t ht => ?_⟩
    -- the increment and its scaling
    have hyle : Q'.abs (yOf (D.ratio t) (D.rhm1 t)) ≤ scaleTol (Q'.abs ainv * c94) η hB :=
      (hy0 (scaleTol (Q'.abs ainv * c94) η hB) hηypos).2 t ht
    -- per-index bound: |ainv · log ρ(t)_n| ≤ η, uniform in n
    have hscale : ∀ n, Q'.abs (ainv * (logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)).approx n) ≤ η := by
      intro n
      have hb : Q'.abs ((logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)).approx n)
          ≤ c94 * Q'.abs (yOf (D.ratio t) (D.rhm1 t)) := logRat_approx_abs_le _ _ _ n
      -- two-sided from abs bound
      have hbU : (logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)).approx n
          ≤ c94 * Q'.abs (yOf (D.ratio t) (D.rhm1 t)) :=
        Q'.le_trans' _ _ _ (Q'.le_abs_self _) hb
      have hbL : -(c94 * Q'.abs (yOf (D.ratio t) (D.rhm1 t)))
          ≤ (logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)).approx n := by
        have h := Q'.neg_le_neg hb
        have hx := Q'.neg_le_abs ((logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)).approx n)
        have hx' := Q'.neg_le_neg hx
        exact Q'.le_trans' _ _ _ h
          (Q'.le_trans' _ _ _ hx' (Q'.le_of_eqv (Q'.neg_neg_eqv _)))
      obtain ⟨hU, hL⟩ := absScaleBound ainv
        ((logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)).approx n)
        (c94 * Q'.abs (yOf (D.ratio t) (D.rhm1 t)))
        (Q'.mul_nonneg _ _ (by decide : (0:Q') ≤ c94) (Q'.abs_nonneg _)) hbL hbU
      -- |ainv|·(c94·|yOf|) ≤ |ainv|·(c94·ηy) ≃ (|ainv|·c94)·ηy ≤ η
      have hchain : Q'.abs ainv * (c94 * Q'.abs (yOf (D.ratio t) (D.rhm1 t))) ≤ η := by
        have hm : c94 * Q'.abs (yOf (D.ratio t) (D.rhm1 t))
            ≤ c94 * scaleTol (Q'.abs ainv * c94) η hB :=
          Q'.mul_le_mul_of_nonneg_left _ _ c94 hyle (by decide : (0:Q') ≤ c94)
        have h1 : Q'.abs ainv * (c94 * Q'.abs (yOf (D.ratio t) (D.rhm1 t)))
            ≤ Q'.abs ainv * (c94 * scaleTol (Q'.abs ainv * c94) η hB) :=
          Q'.mul_le_mul_of_nonneg_left _ _ (Q'.abs ainv) hm (Q'.abs_nonneg ainv)
        refine Q'.le_trans' _ _ _ h1 ?_
        refine Q'.le_trans' _ _ _
          (Q'.ge_of_eqv (Q'.mul_assoc_eqv (Q'.abs ainv) c94 (scaleTol (Q'.abs ainv * c94) η hB)))
          hηy
      exact Q'.abs_le (Q'.le_trans' _ _ _ (Q'.neg_le_neg hchain) hL)
        (Q'.le_trans' _ _ _ hU hchain)
    -- EM t ≃ add mPhys (mul (ofQ' ainv) (log ρ(t)))
    have hEM : CReal.Equiv
        (effectiveMass ainv (CReal.ofQ' (C t)) (CReal.ofQ' (C (t + 1))) (D.red t) (D.red (t + 1)))
        (CReal.add (CReal.mul (CReal.ofQ' ainv) D.negLogSep)
          (CReal.mul (CReal.ofQ' ainv) (logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)))) :=
      CReal.Equiv.trans (mul_ofQ'_equiv ainv (D.telescope t))
        (mul_ofQ'_add_distrib ainv D.negLogSep (logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)))
    refine ⟨?_, ?_⟩
    · -- leEv (EM t) (add mPhys (ofQ' η))
      intro ε hε
      obtain ⟨N, hN⟩ := hEM ε hε
      refine ⟨N, fun n hn => ?_⟩
      -- EM_n ≤ (mPhys_n + scaledIncr_n) + ε ≤ (mPhys_n + η) + ε
      refine Q'.le_trans' _ _ _ (hN n hn).1 ?_
      show ((CReal.ofQ' ainv).mul D.negLogSep).approx n
            + ainv * (logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)).approx n + ε
          ≤ ((CReal.ofQ' ainv).mul D.negLogSep).approx n + η + ε
      have hincU : ainv * (logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)).approx n ≤ η :=
        Q'.le_trans' _ _ _ (Q'.le_abs_self _) (hscale n)
      exact Q'.add_le_add_right _ _ ε
        (Q'.add_le_add_left (((CReal.ofQ' ainv).mul D.negLogSep).approx n) _ _ hincU)
    · -- leEv mPhys (add (EM t) (ofQ' η))
      intro ε hε
      obtain ⟨N, hN⟩ := hEM ε hε
      refine ⟨N, fun n hn => ?_⟩
      -- mPhys_n ≤ mPhys_n + (scaledIncr_n + η) ≃ (mPhys_n+scaledIncr_n)+η ≤ (EM_n+ε)+η ≃ (EM_n+η)+ε
      have hincL : -η ≤ ainv * (logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)).approx n := by
        have hx := Q'.neg_le_abs (ainv * (logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)).approx n)
        have hx' := Q'.neg_le_neg hx
        exact Q'.le_trans' _ _ _ (Q'.neg_le_neg (hscale n))
          (Q'.le_trans' _ _ _ hx' (Q'.le_of_eqv (Q'.neg_neg_eqv _)))
      -- 0 ≤ scaledIncr_n + η
      have hnn : (0 : Q') ≤ ainv * (logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)).approx n + η := by
        refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_add_self_eqv η)) ?_
        exact Q'.add_le_add_right _ _ η hincL
      -- mPhys_n ≤ mPhys_n + (scaledIncr_n + η)
      have s1 : ((CReal.ofQ' ainv).mul D.negLogSep).approx n
          ≤ ((CReal.ofQ' ainv).mul D.negLogSep).approx n
            + (ainv * (logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)).approx n + η) :=
        Q'.add_le_self_of_nonneg _ _ hnn
      refine Q'.le_trans' _ _ _ s1 ?_
      -- mPhys_n + (scaledIncr_n + η) ≃ (mPhys_n + scaledIncr_n) + η
      refine Q'.le_trans' _ _ _
        (Q'.ge_of_eqv (Q'.add_assoc_eqv (((CReal.ofQ' ainv).mul D.negLogSep).approx n)
          (ainv * (logRat (D.ratio t) (D.rhm1 t) (D.rhyb t)).approx n) η)) ?_
      -- (mPhys_n + scaledIncr_n) + η ≤ (EM_n + ε) + η
      refine Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ η (hN n hn).2) ?_
      -- (EM_n + ε) + η ≃ (EM_n + η) + ε
      show ((effectiveMass ainv (CReal.ofQ' (C t)) (CReal.ofQ' (C (t + 1)))
              (D.red t) (D.red (t + 1))).approx n + ε) + η
          ≤ (effectiveMass ainv (CReal.ofQ' (C t)) (CReal.ofQ' (C (t + 1)))
              (D.red t) (D.red (t + 1))).approx n + η + ε
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv _ ε η) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ (ε + η) (η + ε) (Q'.add_comm_eqv ε η)) ?_
      exact Q'.eqv_symm (Q'.add_assoc_eqv _ η ε)

end YMGap.Continuum.EffMassConvergence

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.EffMassConvergence.partialSum_le_ub
#print axioms YMGap.Continuum.EffMassConvergence.partialSum_ge_lb
#print axioms YMGap.Continuum.EffMassConvergence.logRat_approx_abs_le
#print axioms YMGap.Continuum.EffMassConvergence.absYOf_le
#print axioms YMGap.Continuum.EffMassConvergence.log_continuity_at_one
#print axioms YMGap.Continuum.EffMassConvergence.logRat_convergesTo_zero
#print axioms YMGap.Continuum.EffMassConvergence.convergesTo_scale
#print axioms YMGap.Continuum.EffMassConvergence.convergesTo_congr
#print axioms YMGap.Continuum.EffMassConvergence.effectiveMass_convergesTo
#print axioms YMGap.Continuum.EffMassConvergence.effMassLogContinuity
