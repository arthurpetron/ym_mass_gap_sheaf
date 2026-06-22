/-
Track B / R2 — Layer 1 of the `(r,d)` theta-asymptotics build: two-sided DISCRETE
bounds for the CENTERED Gaussian-theta partial sums.

# What this module builds — reusable Gaussian-theta-centered infrastructure

The `d`-side of the `p = 2` SU(2) self-fusion factorization is the family of
CENTERED incomplete-theta moments

    Dsum_m(K)  :=  ∑_{0 ≤ d ≤ K}  d^m · σ^{d²},      m ∈ {0, 2},   σ = √w ∈ (0,1),

(`σ^{d²} = w^{d²/2}`).  The full `|d| ≤ K` sum is `2·Dsum_m(K) − [m=0]·1` by
evenness of `d ↦ d^m σ^{d²}` (the `d = 0` term is `1` for `m = 0`, `0` for `m = 2`).

Here `σ` is carried as a GENERIC `Q'` base in `(0, 1]` — these are Gaussian-theta
facts about `∑ d^m σ^{d²}` for ANY such `σ`; the caller instantiates `σ = √w` at
the point of use (the `σ`/CReal bridge lives in `FusionRDFactor`).  Everything here
is DISCRETE (finite `Q'` sums), no CReal integration.

# What is PROVED (axiom-clean two-sided bounds with explicit `Q'` constants)

THE DEFINITIONS:
  * `thetaTerm σ m d  =  ofNat(d^m) · qpow σ (d*d)`  — the centered theta summand
    `d^m σ^{d²}`; `thetaTerm_nonneg`.
  * `thetaCenteredSum σ m K  =  ∑_{d ≤ K} thetaTerm σ m d  =  finSum (thetaTerm σ m) (K+1)`
    — the centered partial sum `Dsum_m(K)`; `thetaCenteredSum_nonneg`,
    monotone (`thetaCenteredSum_mono`).
  * `ThetaMomentLE σ m C  =  ∀ K, thetaCenteredSum σ m K ≤ C` — the full moment
    `thetaMoment_m = ∑_{d≥0} d^m σ^{d²}` realized as a UNIFORM `Q'` bound `C` on every
    partial sum (the bounded-monotone "limit/sup" form, the only constructive shape
    here).

THE SINGLE-TERM INCREMENT (Layer-2 lever, PROVED):
  * `thetaCentered_succ` — `Dsum_m(K+1) − Dsum_m(K) ≃ (K+1)^m · σ^{(K+1)²}`
    (the clean one-term increment).

THE LOWER BOUND (the leading `τ^{−(m+1)/2}` order, PROVED via the Bernoulli head):
  * `thetaTerm_ge_half` — on the head `2·d²·(1−σ) ≤ 1` the floor `σ^{d²} ≥ 1/2`
    (`qpow_ge_bernoulli`), so `d^m σ^{d²} ≥ (1/2)·ofNat(d^m)`.
  * `thetaCentered0_ge` (m=0): `Dsum_0(d₀) ≥ (1/2)·ofNat(d₀+1)`     (`≍ τ^{−1/2}`).
  * `thetaCentered2_ge` (m=2): `Dsum_2(d₀) ≥ (1/2)·ofNat(sumSq d₀)`  and
    `thetaCentered2_ge_cube`: `6·Dsum_2(d₀) ≥ ofNat(d₀³)`            (`≍ τ^{−3/2}`).
  At the head cutoff `d₀ ≍ τ^{−1/2}` (the largest `d₀` with `2 d₀² (1−σ) ≤ 1`, i.e.
  `d₀² ≍ 1/(2(1−σ)) ≍ 1/τ` since `1−σ ≍ τ/2`), these give the leading orders
  `Dsum_0 ≍ τ^{−1/2}`, `Dsum_2 ≍ τ^{−3/2}` — `m+1`/2 in `τ^{−1}` as stated.

THE UPPER BOUND (the full moment is FINITE with an explicit `Q'` constant, PROVED):
  * `thetaTerm_ratio` — the successive-term Gaussian ratio
    `thetaTerm σ m (S+(k+1)) ≤ (2^m·σ^{2S+1})·thetaTerm σ m (S+k)`.
  * `thetaTail_le` — under the cutoff `2^m·σ^{2S+1} ≤ 1/2` and head `thetaTerm σ m S
    ≤ (1/2)^{r+1}`, the TAIL window `∑_{S ≤ d < S+M} thetaTerm σ m d ≤ (1/2)^r`
    (`geom_series_le`).
  * `thetaMoment_le` — assembling head (`∑_{d<S}`) + tail (`≤ 1`), the FULL moment is
    `Dsum_m(K) ≤ (∑_{d<S} thetaTerm σ m d) + 1` for every `K`, an explicit finite
    `Q'` constant.  Leading τ-scaling: the head `∑_{d<S} d^m σ^{d²} ≍ τ^{−(m+1)/2}`
    dominates the `O(1)` tail, so `thetaMoment_m ≍ τ^{−(m+1)/2}·const`.

# Layered scope (honest)

This is Layer 1 — reusable two-sided Gaussian-theta-centered bounds (the `D_m` side),
NOT the Layer-2 ratio/parity (`g_{s+1}/g_s`, the second-difference `Δ²log g`) nor the
Layer-3 DOM/DER local-CLT box inequalities, and NOT a 4D Yang–Mills mass gap.  The
single-term increment `thetaCentered_succ` is the lever Layer 2 consumes.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, decidable facts, reused
`qpow`/`finSum`/`geom_series_le`/`sumSq` lemmas.  Every load-bearing declaration is
`#print axioms`-gated (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide` (only `decide` on decidable `Q'` facts), no `sorry`.  All witnesses
are `Type`-level data.
-/

import YMGap.Continuum.BondMovingScaledNorm
import YMGap.Continuum.MovingCutoff

namespace YMGap.Continuum.RDThetaCentered

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.MovingCutoff

/-! ## 0. The centered theta summand and partial sum -/

/-- **The centered theta summand** `thetaTerm σ m d = d^m · σ^{d²} = ofNat(d^m) ·
qpow σ (d*d)`.  `σ = √w` realizes the half-integer `w`-power `w^{d²/2}`; here `σ`
is a generic `Q'` base. -/
def thetaTerm (σ : Q') (m d : Nat) : Q' := Q'.ofNat (d ^ m) * qpow σ (d * d)

@[simp] theorem thetaTerm_def (σ : Q') (m d : Nat) :
    thetaTerm σ m d = Q'.ofNat (d ^ m) * qpow σ (d * d) := rfl

/-- The centered theta summand is nonnegative for `0 ≤ σ`. -/
theorem thetaTerm_nonneg {σ : Q'} (hσ : (0 : Q') ≤ σ) (m d : Nat) :
    (0 : Q') ≤ thetaTerm σ m d :=
  Q'.mul_nonneg _ _ (zero_le_ofNat _) (qpow_nonneg σ hσ (d * d))

/-- **The centered theta partial sum** `thetaCenteredSum σ m K = ∑_{0 ≤ d ≤ K} d^m
· σ^{d²}` (the `(K+1)`-term `finSum` of `thetaTerm`).  This is `Dsum_m(K)`. -/
def thetaCenteredSum (σ : Q') (m K : Nat) : Q' :=
  RationalTail.finSum (thetaTerm σ m) (K + 1)

/-- `thetaCenteredSum σ m K ≥ 0` for `0 ≤ σ`. -/
theorem thetaCenteredSum_nonneg {σ : Q'} (hσ : (0 : Q') ≤ σ) (m K : Nat) :
    (0 : Q') ≤ thetaCenteredSum σ m K := by
  unfold thetaCenteredSum
  induction (K + 1) with
  | zero => exact Q'.le_refl' 0
  | succ n ih =>
      show (0 : Q') ≤ RationalTail.finSum (thetaTerm σ m) n + thetaTerm σ m n
      exact Q'.le_trans' _ _ _
        (Q'.le_trans' _ _ _ ih (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _)))))
        (Q'.add_le_add_left _ _ _ (thetaTerm_nonneg hσ m n))

/-- `RationalTail.finSum` is monotone in its length for a nonnegative sequence
(prefix monotonicity), local restatement for `thetaTerm`. -/
theorem finSum_le_of_le {f : Nat → Q'} (hf : ∀ i, (0 : Q') ≤ f i) :
    ∀ {p n : Nat}, p ≤ n → RationalTail.finSum f p ≤ RationalTail.finSum f n := by
  intro p n hpn
  induction n with
  | zero =>
      have : p = 0 := Nat.le_zero.mp hpn
      subst this; exact Q'.le_refl' _
  | succ k ih =>
      rcases Nat.lt_or_ge p (k + 1) with hlt | hge
      · have hpk : p ≤ k := Nat.lt_succ_iff.mp hlt
        have h1 : RationalTail.finSum f p ≤ RationalTail.finSum f k := ih hpk
        have h2 : RationalTail.finSum f k ≤ RationalTail.finSum f k + f k := by
          refine Q'.le_trans' _ _ _
            (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _)))) ?_
          exact Q'.add_le_add_left _ _ _ (hf k)
        exact Q'.le_trans' _ _ _ h1 h2
      · have : p = k + 1 := Nat.le_antisymm hpn hge
        subst this; exact Q'.le_refl' _

/-- Monotonicity in the cutoff: `thetaCenteredSum σ m K ≤ thetaCenteredSum σ m (K+1)`
(append one nonnegative term). -/
theorem thetaCenteredSum_mono {σ : Q'} (hσ : (0 : Q') ≤ σ) (m K : Nat) :
    thetaCenteredSum σ m K ≤ thetaCenteredSum σ m (K + 1) := by
  show RationalTail.finSum (thetaTerm σ m) (K + 1)
    ≤ RationalTail.finSum (thetaTerm σ m) (K + 1) + thetaTerm σ m (K + 1)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _)))) ?_
  exact Q'.add_le_add_left _ _ _ (thetaTerm_nonneg hσ m (K + 1))

/-! ## 1. The single-term increment (the Layer-2 lever) -/

/-- **THE SINGLE-TERM INCREMENT.**  `Dsum_m(K+1) − Dsum_m(K) ≃ (K+1)^m · σ^{(K+1)²}`,
i.e. the centered partial sum advances by exactly one theta term.  This is the clean
lever Layer 2 (the consecutive-mode ratio / second-difference) consumes. -/
theorem thetaCentered_succ (σ : Q') (m K : Nat) :
    (thetaCenteredSum σ m (K + 1)
        + -(thetaCenteredSum σ m K)).eqv (thetaTerm σ m (K + 1)) := by
  -- thetaCenteredSum σ m (K+1) = finSum (K+2) = finSum (K+1) + thetaTerm σ m (K+1)
  show (RationalTail.finSum (thetaTerm σ m) (K + 1 + 1)
      + -(RationalTail.finSum (thetaTerm σ m) (K + 1))).eqv (thetaTerm σ m (K + 1))
  show ((RationalTail.finSum (thetaTerm σ m) (K + 1) + thetaTerm σ m (K + 1))
      + -(RationalTail.finSum (thetaTerm σ m) (K + 1))).eqv (thetaTerm σ m (K + 1))
  -- (A + t) + (−A) ≃ t  via commute the first add and cancel A.
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_comm_eqv (RationalTail.finSum (thetaTerm σ m) (K + 1)) (thetaTerm σ m (K + 1)))) ?_
  -- (t + A) + (−A) ≃ t + (A + (−A)) ≃ t + 0 ≃ t
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv (thetaTerm σ m (K + 1)) (RationalTail.finSum (thetaTerm σ m) (K + 1))
      (-(RationalTail.finSum (thetaTerm σ m) (K + 1)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (thetaTerm σ m (K + 1)) _ 0
      (Q'.add_neg_self_eqv (RationalTail.finSum (thetaTerm σ m) (K + 1)))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' (thetaTerm σ m (K + 1)))

/-! ## 2. The LOWER bound — the Bernoulli head floor (the leading `τ^{−(m+1)/2}` order)

On the head `d ≤ d₀` where `2·d²·(1−σ) ≤ 1` the Bernoulli floor gives `σ^{d²} ≥
1/2`, so `d^m σ^{d²} ≥ (1/2)·d^m`.  Summing the closed-form `∑ d^m` (m=0 → count,
m=2 → `sumSq`) yields the leading order. -/

/-- **The Bernoulli head floor at exponent `d²`.**  If `2·d²·(1−σ) ≤ 1` and
`0 ≤ σ ≤ 1`, then `1/2 ≤ σ^{d²}`.  PROOF: Bernoulli `σ^{d²} ≥ 1 − d²·(1−σ)`
(`qpow_ge_bernoulli`), and `d²·(1−σ) ≤ 1/2` from the cutoff. -/
theorem qpow_dsq_half {σ : Q'} (hσ0 : (0 : Q') ≤ σ) (hσ1 : σ ≤ (1 : Q'))
    (d : Nat) (hcut : Q'.ofNat 2 * (Q'.ofNat (d * d) * ((1 : Q') - σ)) ≤ (1 : Q')) :
    HalfPow.half ≤ qpow σ (d * d) := by
  -- d²·(1−σ) ≤ 1/2  from  2·(d²·(1−σ)) ≤ 1
  have hhalf : Q'.ofNat (d * d) * ((1 : Q') - σ) ≤ HalfPow.half := by
    have hr : (Q'.ofNat 2 * (Q'.ofNat (d * d) * ((1 : Q') - σ))) * HalfPow.half
        ≤ (1 : Q') * HalfPow.half :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hcut HalfPow.half_nonneg
    refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (Q'.one_mul_eqv HalfPow.half))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hr
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ HalfPow.half
        (Q'.mul_comm_eqv (Q'.ofNat 2) (Q'.ofNat (d * d) * ((1 : Q') - σ)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat (d * d) * ((1 : Q') - σ)) (Q'.ofNat 2) HalfPow.half) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (d * d) * ((1 : Q') - σ)) _ (1 : Q') ?_) ?_
    · show ((Q'.ofNat 2) * HalfPow.half).eqv (1 : Q'); decide
    · exact Q'.mul_one_eqv (Q'.ofNat (d * d) * ((1 : Q') - σ))
  -- Bernoulli at exponent d²
  have hbern : (1 : Q') - Q'.ofNat (d * d) * ((1 : Q') - σ) ≤ qpow σ (d * d) :=
    qpow_ge_bernoulli hσ0 hσ1 (d * d)
  have hge : HalfPow.half ≤ (1 : Q') - Q'.ofNat (d * d) * ((1 : Q') - σ) := by
    have hsum : HalfPow.half + Q'.ofNat (d * d) * ((1 : Q') - σ) ≤ (1 : Q') := by
      have h1 : HalfPow.half + Q'.ofNat (d * d) * ((1 : Q') - σ)
          ≤ HalfPow.half + HalfPow.half :=
        Q'.add_le_add_left HalfPow.half _ _ hhalf
      refine Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv ?_)
      show (HalfPow.half + HalfPow.half).eqv (1 : Q'); decide
    show HalfPow.half ≤ (1 : Q') + -(Q'.ofNat (d * d) * ((1 : Q') - σ))
    have hstep : (HalfPow.half + Q'.ofNat (d * d) * ((1 : Q') - σ))
          + -(Q'.ofNat (d * d) * ((1 : Q') - σ))
        ≤ (1 : Q') + -(Q'.ofNat (d * d) * ((1 : Q') - σ)) :=
      Q'.add_le_add_right _ _ _ hsum
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) hstep
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv HalfPow.half _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left HalfPow.half _ 0
        (Q'.add_neg_self_eqv (Q'.ofNat (d * d) * ((1 : Q') - σ)))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' HalfPow.half)
  exact Q'.le_trans' _ _ _ hge hbern

/-- **Per-term head lower bound.**  Under the head floor at `d`
(`2·d²·(1−σ) ≤ 1`), `thetaTerm σ m d ≥ (1/2)·ofNat(d^m)`. -/
theorem thetaTerm_ge_half {σ : Q'} (hσ0 : (0 : Q') ≤ σ) (hσ1 : σ ≤ (1 : Q'))
    (m d : Nat) (hcut : Q'.ofNat 2 * (Q'.ofNat (d * d) * ((1 : Q') - σ)) ≤ (1 : Q')) :
    HalfPow.half * Q'.ofNat (d ^ m) ≤ thetaTerm σ m d := by
  have hhalf : HalfPow.half ≤ qpow σ (d * d) := qpow_dsq_half hσ0 hσ1 d hcut
  show HalfPow.half * Q'.ofNat (d ^ m) ≤ Q'.ofNat (d ^ m) * qpow σ (d * d)
  -- (1/2)·ofNat(d^m) ≃ ofNat(d^m)·(1/2) ≤ ofNat(d^m)·σ^{d²}
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv HalfPow.half (Q'.ofNat (d ^ m)))) ?_
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hhalf (zero_le_ofNat _)

/-! ### m = 0: `Dsum_0(d₀) ≥ (1/2)·ofNat(d₀+1)` (the `τ^{−1/2}` order) -/

/-- `∑_{d<n} (1/2)·ofNat(d^0) ≃ (1/2)·ofNat(n)` (the m=0 head; `d^0 = 1`). -/
theorem head0_count (n : Nat) :
    (RationalTail.finSum (fun d => HalfPow.half * Q'.ofNat (d ^ 0)) n).eqv
      (HalfPow.half * Q'.ofNat n) := by
  induction n with
  | zero =>
      show (0 : Q').eqv (HalfPow.half * Q'.ofNat 0)
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left HalfPow.half _ 0 Q'.ofNat_zero_eqv) ?_
      exact QPoly.q_mul_zero HalfPow.half
  | succ k ih =>
      show (RationalTail.finSum (fun d => HalfPow.half * Q'.ofNat (d ^ 0)) k
            + HalfPow.half * Q'.ofNat (k ^ 0)).eqv (HalfPow.half * Q'.ofNat (k + 1))
      have hk0 : k ^ 0 = 1 := rfl
      rw [hk0]
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ ih) ?_
      -- (1/2)·ofNat k + (1/2)·1 ≃ (1/2)·(ofNat k + 1) ≃ (1/2)·ofNat(k+1)
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_add_eqv HalfPow.half (Q'.ofNat k) (Q'.ofNat 1))) ?_
      refine Q'.mul_eqv_congr_left HalfPow.half _ _ ?_
      -- ofNat k + ofNat 1 ≃ ofNat (k+1)
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.ofNat_add_eqv k 1)) ?_
      exact Q'.eqv_refl _

/-- **LOWER BOUND, m = 0 (the `τ^{−1/2}` order).**  If every `d ≤ d₀` satisfies the
head floor `2·d²·(1−σ) ≤ 1`, then

    Dsum_0(d₀)  =  ∑_{d ≤ d₀} σ^{d²}  ≥  (1/2)·ofNat(d₀ + 1).

At the head cutoff `d₀ ≍ τ^{−1/2}` (the largest `d₀` with `2 d₀²(1−σ) ≤ 1`) this is
the leading `Dsum_0 ≍ τ^{−1/2}` order.  PROOF: termwise `σ^{d²} ≥ 1/2`
(`thetaTerm_ge_half`), summed via `head0_count` over the `d₀+1` head terms. -/
theorem thetaCentered0_ge {σ : Q'} (hσ0 : (0 : Q') ≤ σ) (hσ1 : σ ≤ (1 : Q'))
    (d0 : Nat)
    (hfloor : ∀ d, d ≤ d0 → Q'.ofNat 2 * (Q'.ofNat (d * d) * ((1 : Q') - σ)) ≤ (1 : Q')) :
    HalfPow.half * Q'.ofNat (d0 + 1) ≤ thetaCenteredSum σ 0 d0 := by
  show HalfPow.half * Q'.ofNat (d0 + 1)
    ≤ RationalTail.finSum (thetaTerm σ 0) (d0 + 1)
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (head0_count (d0 + 1))) ?_
  refine YMGap.Constructive.finSum_le_lt _ _ (d0 + 1) ?_
  intro d hd
  exact thetaTerm_ge_half hσ0 hσ1 0 d (hfloor d (Nat.lt_succ_iff.mp hd))

/-! ### m = 2: `Dsum_2(d₀) ≥ (1/2)·sumSq d₀ ≥ (1/6)·d₀³` (the `τ^{−3/2}` order) -/

/-- `∑_{d<n} (1/2)·ofNat(d^2) ≃ (1/2)·ofNat(sumSq (n−1))`?  We state the clean form
on the index `n` directly:  `∑_{d<n+1} (1/2)·ofNat(d²) ≃ (1/2)·ofNat(sumSq n)`,
since `∑_{d=0}^{n} d² = ∑_{j=1}^{n} j² = sumSq n` (the `d=0` term vanishes). -/
theorem head2_sumSq (n : Nat) :
    (RationalTail.finSum (fun d => HalfPow.half * Q'.ofNat (d ^ 2)) (n + 1)).eqv
      (HalfPow.half * Q'.ofNat (sumSq n)) := by
  induction n with
  | zero =>
      -- ∑_{d<1} = term at d=0 = (1/2)·ofNat 0 ; sumSq 0 = 0.
      show ((0 : Q') + HalfPow.half * Q'.ofNat (0 ^ 2)).eqv (HalfPow.half * Q'.ofNat (sumSq 0))
      have h00 : (0 : Nat) ^ 2 = 0 := rfl
      have hs0 : sumSq 0 = 0 := rfl
      rw [h00, hs0]
      refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.zero_add' _)) ?_
      exact Q'.eqv_refl _
  | succ k ih =>
      -- ∑_{d<k+2} = ∑_{d<k+1} + (1/2)·ofNat((k+1)²) ; sumSq (k+1) = sumSq k + (k+1)²
      show (RationalTail.finSum (fun d => HalfPow.half * Q'.ofNat (d ^ 2)) (k + 1)
            + HalfPow.half * Q'.ofNat ((k + 1) ^ 2)).eqv
        (HalfPow.half * Q'.ofNat (sumSq (k + 1)))
      have hsidx : sumSq (k + 1) = sumSq k + (k + 1) * (k + 1) := rfl
      have hpow2 : (k + 1) ^ 2 = (k + 1) * (k + 1) := by
        rw [Nat.pow_succ, Nat.pow_one]
      rw [hsidx, hpow2]
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ ih) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_add_eqv HalfPow.half (Q'.ofNat (sumSq k))
          (Q'.ofNat ((k + 1) * (k + 1))))) ?_
      exact Q'.mul_eqv_congr_left HalfPow.half _ _
        (Q'.eqv_symm (Q'.ofNat_add_eqv (sumSq k) ((k + 1) * (k + 1))))

/-- **LOWER BOUND, m = 2 (`sumSq` form).**  If every `d ≤ d₀` satisfies the head
floor, then

    Dsum_2(d₀)  =  ∑_{d ≤ d₀} d²·σ^{d²}  ≥  (1/2)·ofNat(sumSq d₀).

PROOF: termwise `d²σ^{d²} ≥ (1/2)d²` (`thetaTerm_ge_half`), summed via
`head2_sumSq`. -/
theorem thetaCentered2_ge {σ : Q'} (hσ0 : (0 : Q') ≤ σ) (hσ1 : σ ≤ (1 : Q'))
    (d0 : Nat)
    (hfloor : ∀ d, d ≤ d0 → Q'.ofNat 2 * (Q'.ofNat (d * d) * ((1 : Q') - σ)) ≤ (1 : Q')) :
    HalfPow.half * Q'.ofNat (sumSq d0) ≤ thetaCenteredSum σ 2 d0 := by
  show HalfPow.half * Q'.ofNat (sumSq d0)
    ≤ RationalTail.finSum (thetaTerm σ 2) (d0 + 1)
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (head2_sumSq d0)) ?_
  refine YMGap.Constructive.finSum_le_lt _ _ (d0 + 1) ?_
  intro d hd
  exact thetaTerm_ge_half hσ0 hσ1 2 d (hfloor d (Nat.lt_succ_iff.mp hd))

/-- **LOWER BOUND, m = 2 (the `τ^{−3/2}` CUBE order).**  Under the same head floors,

    6·Dsum_2(d₀)  ≥  ofNat(d₀³),     i.e.   Dsum_2(d₀) ≥ (1/6)·ofNat(d₀·d₀·d₀).

At the head cutoff `d₀ ≍ τ^{−1/2}` this is the leading `Dsum_2 ≍ τ^{−3/2}` order.
PROOF: `Dsum_2 ≥ (1/2)·sumSq d₀` (`thetaCentered2_ge`) and `d₀³ ≤ 3·sumSq d₀`
(`sumSq_cube_lb`), so `6·Dsum_2 ≥ 3·sumSq d₀ ≥ d₀³`. -/
theorem thetaCentered2_ge_cube {σ : Q'} (hσ0 : (0 : Q') ≤ σ) (hσ1 : σ ≤ (1 : Q'))
    (d0 : Nat)
    (hfloor : ∀ d, d ≤ d0 → Q'.ofNat 2 * (Q'.ofNat (d * d) * ((1 : Q') - σ)) ≤ (1 : Q')) :
    Q'.ofNat (d0 * d0 * d0) ≤ Q'.ofNat 6 * thetaCenteredSum σ 2 d0 := by
  have hhead : HalfPow.half * Q'.ofNat (sumSq d0) ≤ thetaCenteredSum σ 2 d0 :=
    thetaCentered2_ge hσ0 hσ1 d0 hfloor
  have hcube : d0 * d0 * d0 ≤ 3 * sumSq d0 := sumSq_cube_lb d0
  have h6 : Q'.ofNat 6 * (HalfPow.half * Q'.ofNat (sumSq d0))
      ≤ Q'.ofNat 6 * thetaCenteredSum σ 2 d0 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hhead (zero_le_ofNat 6)
  refine Q'.le_trans' _ _ _ ?_ h6
  have hle : Q'.ofNat (d0 * d0 * d0) ≤ Q'.ofNat (3 * sumSq d0) := ofNat_le_ofNat' hcube
  refine Q'.le_trans' _ _ _ hle ?_
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _ (ofNat_mul_eqv 3 (sumSq d0)) ?_
  refine Q'.eqv_symm ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 6) HalfPow.half (Q'.ofNat (sumSq d0)))) ?_
  refine Q'.mul_eqv_congr_right _ _ (Q'.ofNat (sumSq d0)) ?_
  show ((Q'.ofNat 6) * HalfPow.half).eqv (Q'.ofNat 3)
  decide

/-! ## 3. The UPPER bound — the full moment is finite (`τ^{−(m+1)/2}·const`)

The KEY bridge is `thetaTerm σ m (d+1) ≃ σ · tailTerm σ m d`, because
`(d+1)² = c4 d + 1` (`c4 d = d(d+2) = (d+1)²−1`) and `(d+1)^m` is exactly the
`tailTerm` polynomial weight `dim^m`.  So the upper THETA tail past `S+1` reindexes
to `σ` times the proved Casimir `tailWindow`, whose dyadic smallness is
`tail_modulus`.  The full moment is then `head (finite) + tail (O(1))`. -/

/-- **The shifted-theta ↔ Casimir-tail bridge.**  `thetaTerm σ m (d+1) ≃ σ ·
tailTerm σ m d`.  PROOF: `(d+1)² = c4 d + 1` (since `c4 d = d(d+2) = (d+1)²−1`), so
`σ^{(d+1)²} = σ^{c4 d}·σ`; and `(d+1)^m` is the `tailTerm` polynomial weight. -/
theorem thetaTerm_succ_eq_tailTerm (σ : Q') (m d : Nat) :
    (thetaTerm σ m (d + 1)).eqv (σ * tailTerm σ m d) := by
  -- thetaTerm σ m (d+1) = ofNat((d+1)^m) · qpow σ ((d+1)*(d+1))
  -- tailTerm σ m d      = ofNat((d+1)^m) · qpow σ (c4 d)
  show (Q'.ofNat ((d + 1) ^ m) * qpow σ ((d + 1) * (d + 1))).eqv
      (σ * (Q'.ofNat ((d + 1) ^ m) * qpow σ (c4 d)))
  -- (d+1)*(d+1) = c4 d + 1
  have hidx : (d + 1) * (d + 1) = c4 d + 1 := by
    show (d + 1) * (d + 1) = d * (d + 2) + 1
    -- expand both sides; only d*d is opaque to omega
    have hL : (d + 1) * (d + 1) = d * d + 2 * d + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
    have hR : d * (d + 2) + 1 = d * d + 2 * d + 1 := by
      rw [Nat.mul_add]; omega
    rw [hL, hR]
  rw [hidx]
  -- qpow σ (c4 d + 1) = qpow σ (c4 d) * σ  (definitional fold)
  show (Q'.ofNat ((d + 1) ^ m) * (qpow σ (c4 d) * σ)).eqv
      (σ * (Q'.ofNat ((d + 1) ^ m) * qpow σ (c4 d)))
  -- P·(C·σ) ≃ σ·(P·C):  pure assoc/comm.
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat ((d + 1) ^ m)) (qpow σ (c4 d)) σ)) ?_
  -- (P·C)·σ ≃ σ·(P·C)
  exact Q'.mul_comm_eqv (Q'.ofNat ((d + 1) ^ m) * qpow σ (c4 d)) σ

/-- **The THETA tail window reindexes to `σ`·(Casimir tail window).**  For every
window `M`,

    ∑_{S+1 ≤ d < S+1+M} thetaTerm σ m d
      =  ∑_{0 ≤ k < M} thetaTerm σ m (S + 1 + k)
      ≃  σ · ∑_{S ≤ s < S+M} tailTerm σ m s   =   σ · tailWindow σ m S M.

PROOF: termwise `thetaTerm σ m (S+1+k) = thetaTerm σ m ((S+k)+1) ≃ σ·tailTerm σ m
(S+k)` (`thetaTerm_succ_eq_tailTerm`), then pull the constant `σ` out of the sum
(`const_mul_finSum`). -/
theorem thetaTail_reindex (σ : Q') (m S M : Nat) :
    (RationalTail.finSum (fun k => thetaTerm σ m (S + 1 + k)) M).eqv
      (σ * tailWindow σ m S M) := by
  -- termwise to σ·tailTerm σ m (S+k)
  have hterm : (RationalTail.finSum (fun k => thetaTerm σ m (S + 1 + k)) M).eqv
      (RationalTail.finSum (fun k => σ * tailTerm σ m (S + k)) M) := by
    refine RationalTail.finSum_eqv_congr _ _ ?_ M
    intro k
    have hidx : S + 1 + k = (S + k) + 1 := by omega
    rw [hidx]
    exact thetaTerm_succ_eq_tailTerm σ m (S + k)
  refine Q'.eqv_trans _ _ _ hterm ?_
  -- pull σ out:  ∑ σ·tailTerm ≃ σ·∑ tailTerm
  exact Q'.eqv_symm
    (RationalTail.const_mul_finSum (fun k => tailTerm σ m (S + k)) σ M)

/-- **UPPER BOUND on the theta tail (dyadic).**  Fix `0 < σ < 1`, degree `m`,
precision `r`, and a cutoff `S` with the explicit cutoff and head inequalities of
`tail_modulus` (at degree `m`):

    cutoff:  2^m · σ^{2S+3}  ≤  1/2,     head:  tailTerm σ m S ≤ (1/2)^{r+1}.

Then for every window `M`,

    ∑_{S+1 ≤ d < S+1+M} thetaTerm σ m d   ≤   (1/2)^r.

PROOF.  Reindex to `σ·tailWindow σ m S M` (`thetaTail_reindex`); `tailWindow ≤
(1/2)^r` (`tail_modulus`); and `σ·(1/2)^r ≤ (1/2)^r` since `0 ≤ σ ≤ 1`. -/
theorem thetaTail_le {σ : Q'} (hσ0 : (0 : Q') < σ) (hσ1 : σ < (1 : Q'))
    (m r S : Nat)
    (hcut : Q'.ofNat (2 ^ m) * qpow σ (2 * S + 3) ≤ HalfPow.half)
    (hhead : tailTerm σ m S ≤ dyad (r + 1)) :
    ∀ M, RationalTail.finSum (fun k => thetaTerm σ m (S + 1 + k)) M ≤ dyad r := by
  intro M
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (thetaTail_reindex σ m S M)) ?_
  -- σ·tailWindow ≤ σ·dyad r ≤ 1·dyad r = dyad r
  have htw : tailWindow σ m S M ≤ dyad r := tail_modulus hσ0 hσ1 m r S hcut hhead M
  have hstep : σ * tailWindow σ m S M ≤ σ * dyad r :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ htw (Q'.le_of_lt hσ0)
  refine Q'.le_trans' _ _ _ hstep ?_
  -- σ·dyad r ≤ 1·dyad r = dyad r
  have h1 : σ * dyad r ≤ (1 : Q') * dyad r :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (Q'.le_of_lt hσ1) (dyad_nonneg r)
  exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv (Q'.one_mul_eqv (dyad r)))

/-- **UPPER BOUND on the full centered theta moment (head + tail, explicit `Q'`
constant).**  Under the cutoff/head data of `thetaTail_le`, for EVERY cutoff `K`,

    Dsum_m(K)  =  ∑_{0 ≤ d ≤ K} d^m σ^{d²}
              ≤  (∑_{d < S+1} thetaTerm σ m d)  +  (1/2)^r.

In particular the full moment `thetaMoment_m = ∑_{d≥0} d^m σ^{d²}` is FINITE,
bounded by the explicit `Q'` constant `(∑_{d<S+1} thetaTerm σ m d) + (1/2)^r`.  The
head `∑_{d<S+1} d^m σ^{d²}` carries the leading `τ^{−(m+1)/2}` order; the tail is
`O(1)`.  PROOF: every partial sum either lies within the head `K < S+1` (monotone,
`≤ head ≤ head + (1/2)^r`) or splits as `head + (theta tail window)`
(`finSum_split`), and the tail window is `≤ (1/2)^r` (`thetaTail_le`). -/
theorem thetaMoment_le {σ : Q'} (hσ0 : (0 : Q') < σ) (hσ1 : σ < (1 : Q'))
    (m r S : Nat)
    (hcut : Q'.ofNat (2 ^ m) * qpow σ (2 * S + 3) ≤ HalfPow.half)
    (hhead : tailTerm σ m S ≤ dyad (r + 1)) :
    ∀ K, thetaCenteredSum σ m K
      ≤ RationalTail.finSum (thetaTerm σ m) (S + 1) + dyad r := by
  intro K
  have hσ0' : (0 : Q') ≤ σ := Q'.le_of_lt hσ0
  -- thetaCenteredSum σ m K = finSum (thetaTerm σ m) (K+1)
  show RationalTail.finSum (thetaTerm σ m) (K + 1)
    ≤ RationalTail.finSum (thetaTerm σ m) (S + 1) + dyad r
  rcases Nat.lt_or_ge (K + 1) (S + 1) with hlt | hge
  · -- K+1 < S+1: the partial sum is a prefix of the head; bound by head ≤ head + dyad.
    have hpre : RationalTail.finSum (thetaTerm σ m) (K + 1)
        ≤ RationalTail.finSum (thetaTerm σ m) (S + 1) :=
      finSum_le_of_le (fun i => thetaTerm_nonneg hσ0' m i) (Nat.le_of_lt hlt)
    refine Q'.le_trans' _ _ _ hpre ?_
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _)))) ?_
    exact Q'.add_le_add_left _ _ _ (dyad_nonneg r)
  · -- K+1 ≥ S+1: split at S+1.  K+1 = (S+1) + d, d = K+1-(S+1).
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge  -- K+1 = (S+1) + d
    rw [hd]
    -- finSum (thetaTerm) ((S+1)+d) ≃ finSum (S+1) + finSum (k ↦ thetaTerm (S+1+k)) d
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (YMGap.Constructive.finSum_split (thetaTerm σ m) (S + 1) d)) ?_
    -- head + tailwindow ≤ head + dyad r
    refine Q'.add_le_add_left _ _ _ ?_
    exact thetaTail_le hσ0 hσ1 m r S hcut hhead d

/-! ## 4. The full moment as a uniform bound (the constructive "limit/sup" form)

The full moment `thetaMoment_m = ∑_{d≥0} d^m σ^{d²}` is realized, constructively, as
a UNIFORM `Q'` bound on every partial sum (the bounded-monotone "sup"; no completed
limit is needed for the two-sided estimates).  `ThetaMomentLE σ m C` records such a
bound `C`; `thetaMoment_le` inhabits it with the explicit head + dyadic-tail
constant. -/

/-- **The full-moment uniform bound predicate.**  `C` bounds the centered theta
moment if it bounds every partial sum `Dsum_m(K)`.  The least such `C` is
`thetaMoment_m = ∑_{d≥0} d^m σ^{d²}`. -/
def ThetaMomentLE (σ : Q') (m : Nat) (C : Q') : Prop :=
  ∀ K, thetaCenteredSum σ m K ≤ C

/-- **The full centered theta moment is finite** with the explicit `Q'` constant
`(∑_{d<S+1} thetaTerm σ m d) + (1/2)^r`.  Direct from `thetaMoment_le`. -/
theorem thetaMomentLE_explicit {σ : Q'} (hσ0 : (0 : Q') < σ) (hσ1 : σ < (1 : Q'))
    (m r S : Nat)
    (hcut : Q'.ofNat (2 ^ m) * qpow σ (2 * S + 3) ≤ HalfPow.half)
    (hhead : tailTerm σ m S ≤ dyad (r + 1)) :
    ThetaMomentLE σ m (RationalTail.finSum (thetaTerm σ m) (S + 1) + dyad r) :=
  thetaMoment_le hσ0 hσ1 m r S hcut hhead

end YMGap.Continuum.RDThetaCentered

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.RDThetaCentered.thetaTerm_nonneg
#print axioms YMGap.Continuum.RDThetaCentered.finSum_le_of_le
#print axioms YMGap.Continuum.RDThetaCentered.thetaCenteredSum_nonneg
#print axioms YMGap.Continuum.RDThetaCentered.thetaCenteredSum_mono
#print axioms YMGap.Continuum.RDThetaCentered.thetaCentered_succ
#print axioms YMGap.Continuum.RDThetaCentered.qpow_dsq_half
#print axioms YMGap.Continuum.RDThetaCentered.thetaTerm_ge_half
#print axioms YMGap.Continuum.RDThetaCentered.head0_count
#print axioms YMGap.Continuum.RDThetaCentered.thetaCentered0_ge
#print axioms YMGap.Continuum.RDThetaCentered.head2_sumSq
#print axioms YMGap.Continuum.RDThetaCentered.thetaCentered2_ge
#print axioms YMGap.Continuum.RDThetaCentered.thetaCentered2_ge_cube
#print axioms YMGap.Continuum.RDThetaCentered.thetaTerm_succ_eq_tailTerm
#print axioms YMGap.Continuum.RDThetaCentered.thetaTail_reindex
#print axioms YMGap.Continuum.RDThetaCentered.thetaTail_le
#print axioms YMGap.Continuum.RDThetaCentered.thetaMoment_le
#print axioms YMGap.Continuum.RDThetaCentered.thetaMomentLE_explicit
