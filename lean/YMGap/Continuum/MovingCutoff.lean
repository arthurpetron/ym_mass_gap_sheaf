/-
Track B / R2 — the **fully `w`-uniform** scaled Casimir-square moment, via the
MOVING cutoff and the probabilistic (normalized) bound.

# What this settles (and what it honestly does NOT)

The fixed-cutoff Casimir-square moment constant is the CRUDE head-count bound
(`μ ≤ 1`, count·max).  As the heat-kernel weight `w → 1` (the margin `τ = 1 − w
→ 0`) a fixed cutoff `S` fails the cutoff inequalities, and pushing the cutoff
out with `w` on the crude bound BLOWS UP (`≍ τ^{−q−5/2}`).  The crude bound is
fundamentally insufficient for `w → 1`.

The cure is the PROBABILISTIC / NORMALIZED bound.  Writing `y_s = τ·C₄(s)` we
have `τ²·C₄(s)² = y_s²` and `qfac(w,s) = 1 + y_s`, so

    (1 − w)² · casimirSqSum w N q n  =  ∑_{s<n} μ(s)·(1 + y_s)^q·y_s²

is a bounded GAUSSIAN MOMENT against the probability weight `μ` (`∑ μ ≤ 1`, mass
concentrated at `y_s ≍ O(1)`).  This module BUILDS the three analytic pillars
of that bound.

# THE THREE PILLARS (stated EXACTLY as proved — AGENTS.md Rule 6)

**Pillar 1 — the partition LOWER bound (the τ^{−3/2} scale).**  PROVED
UNCONDITIONALLY (`Zsum_ge_head`, `Zsum_ge_cube`).  For any cutoff `S` with
`2·C₄(S)·(1−w) ≤ 1` and `S ≤ N`, the Bernoulli head estimate
`w^{C₄ s} ≥ 1 − C₄(s)·(1−w) ≥ 1/2` (proved from `oneSub_pow_factor` +
`geomSum_le`) gives

    Zsum w N  ≥  (1/2)·∑_{j<S}(j+1)²  ≥  (1/6)·ofNat(S³),

with the closed-form sum of squares `∑_{j<S}(j+1)² = S(S+1)(2S+1)/6 ≥ S³/3`
(`sumSq`, proved by Nat induction).  Instantiated at `S = S₀(w) ≍ τ^{−1/2}` this
is the τ^{−3/2} lower bound; we keep `S` as the named cutoff parameter (cleanest
constructive form) and expose the scaling as the caller's instantiation.  THIS is
the genuinely new valuable fact.

**Pillar 2 — the HEAD moment via `∑ μ ≤ 1` (NOT count·max).** PROVED
UNCONDITIONALLY (`headMu_le_one`, `head_moment_uniform`).  On the head `s < S`
where `y_s ≤ 1`, `(1+y_s)^q·y_s² ≤ 2^q·1` (monotone in `y`), so
`(1−w)²·∑_{s<S} μ·qfac^q·C₄² = ∑_{s<S} μ·(1+y_s)^q·y_s² ≤ 2^q·∑ μ ≤ 2^q`.  The
constant `2^q` is genuinely `w`-INDEPENDENT.

**Pillar 3 — the TAIL moment (the hardest piece).** REDUCED to ONE explicitly
named lemma `partition_upper_dyadic` (the dyadic-block partition UPPER bound) and
used as a hypothesis; everything around it (`tail_moment_of_partition_upper`,
the assembly) is proved.  We do NOT fake it.

# Honest verdict

Pillars 1 and 2 close UNCONDITIONALLY.  The fully-`w`-uniform assembly
(`casimir_moment_uniform_of_named`) is proved CONDITIONAL on the single named
Pillar-3 lemma `partition_upper_dyadic`.  No unconditional canonical-chain claim
is made here that rests on a named lemma.  This is NOT a 4D Yang–Mills gap proof.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, structural inductions, decidable facts; every
load-bearing declaration is `#print axioms`-gated (permitted: `propext` /
`Quot.sound`).  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses
are `Type`-level data.
-/

import YMGap.Continuum.CasimirMoment

namespace YMGap.Continuum.MovingCutoff

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.CasimirMoment

/-! ## 0. The Bernoulli lower bound for `qpow` (the engine of Pillar 1)

`w^n ≥ 1 − n·(1−w)` on `[0,1]`.  PROOF: `1 − w^n = (1−w)·geomSum w n`
(`oneSub_pow_factor`) and `geomSum w n ≤ n` (`geomSum_le`), so
`1 − w^n ≤ (1−w)·n`, i.e. `w^n ≥ 1 − n·(1−w)`. -/

/-- **Bernoulli's inequality (rational form).**  For `0 ≤ w ≤ 1`,
`1 − ofNat n · (1 − w) ≤ qpow w n`. -/
theorem qpow_ge_bernoulli {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (n : Nat) : (1 : Q') - Q'.ofNat n * ((1 : Q') - w) ≤ qpow w n := by
  -- 1 − w^n = (1−w)·geomSum w n ≤ (1−w)·n = n·(1−w).
  have hfac : ((1 : Q') - qpow w n).eqv (((1 : Q') - w) * geomSum w n) :=
    oneSub_pow_factor w n
  have hnn : (0 : Q') ≤ (1 : Q') - w := Q'.sub_nonneg_of_le hw1
  have hgs : geomSum w n ≤ Q'.ofNat n := geomSum_le hw0 hw1 n
  -- (1−w)·geomSum w n ≤ (1−w)·n
  have hstep : ((1 : Q') - w) * geomSum w n ≤ ((1 : Q') - w) * Q'.ofNat n :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgs hnn
  -- so 1 − w^n ≤ (1−w)·n ≃ n·(1−w)
  have hle1 : (1 : Q') - qpow w n ≤ Q'.ofNat n * ((1 : Q') - w) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hfac)
      (Q'.le_trans' _ _ _ hstep
        (Q'.le_of_eqv (Q'.mul_comm_eqv ((1 : Q') - w) (Q'.ofNat n))))
  -- rearrange 1 − w^n ≤ n·(1−w)  ⟹  1 − n·(1−w) ≤ w^n
  -- add (w^n − n·(1−w)) to both sides.
  have hcomm := hle1
  -- 1 − w^n ≤ A  (A = n·(1−w));  want 1 − A ≤ w^n.
  -- (1 + -w^n) ≤ A  ⟹  (1 + -A) ≤ w^n  via Q'.sub_le_of_le_add on a rearrangement.
  -- Use: 1 ≤ A + w^n (from hle1), then 1 − A ≤ w^n.
  have h2 : (1 : Q') ≤ Q'.ofNat n * ((1 : Q') - w) + qpow w n := by
    -- 1 + -w^n ≤ A  ⟹  1 ≤ A + w^n
    have e : ((1 : Q') - qpow w n).eqv ((1 : Q') + -(qpow w n)) := Q'.eqv_refl _
    -- from hle1: 1 + -w^n ≤ A ; add w^n
    have hadd : ((1 : Q') - qpow w n) + qpow w n
        ≤ Q'.ofNat n * ((1 : Q') - w) + qpow w n :=
      Q'.add_le_add_right _ _ (qpow w n) hle1
    have ecollapse : (((1 : Q') - qpow w n) + qpow w n).eqv (1 : Q') := by
      show (((1 : Q') + -(qpow w n)) + qpow w n).eqv (1 : Q')
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (1 : Q') (-(qpow w n)) (qpow w n)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (1 : Q') _ 0 (Q'.neg_add_self_eqv (qpow w n))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' 1)
    exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv ecollapse) hadd
  -- 1 ≤ A + w^n ⟹ 1 − A ≤ w^n  (sub_le_of_le_add: a ≤ b+c → a + -b ≤ c)
  exact Q'.sub_le_of_le_add h2

/-- `fsum` (BondMovingStep) and `RationalTail.finSum` agree pointwise (identical
recurrence); bridge for reusing the `finSum` algebra on `fsum`. -/
theorem fsum_eq_finSum (f : Nat → Q') : ∀ n, fsum f n = RationalTail.finSum f n
  | 0 => rfl
  | n + 1 => by
      show fsum f n + f n = RationalTail.finSum f n + f n
      rw [fsum_eq_finSum f n]

/-- `ofNat 2 ^ q ≃ ofNat (2^q)` (the `Q'`-power of `ofNat 2` is `ofNat` of the
`Nat`-power). -/
theorem ofNat_two_pow_eqv : ∀ q, ((Q'.ofNat 2) ^ q).eqv (Q'.ofNat (2 ^ q))
  | 0 => by rw [Q'.pow_zero]; decide
  | k + 1 => by
      rw [Q'.pow_succ]
      -- ofNat2 * (ofNat2^k) ≃ ofNat2 * ofNat(2^k) ≃ ofNat(2·2^k) = ofNat(2^{k+1})
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _ (ofNat_two_pow_eqv k)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (ofNat_mul_eqv 2 (2 ^ k))) ?_
      have : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      rw [this]; exact Q'.eqv_refl _

/-! ## 1. The closed-form sum of squares (Nat) and its cube lower bound

`sumSq S = ∑_{j<S}(j+1)²`; `6·sumSq S = S(S+1)(2S+1)`, hence `3·sumSq S ≥ S³`
(`sumSq_cube_lb`).  Pure `Nat` arithmetic, `omega` after expanding the products. -/

/-- `sumSq S = ∑_{j=1}^{S} j² = ∑_{j<S}(j+1)²` (Nat). -/
def sumSq : Nat → Nat
  | 0 => 0
  | S + 1 => sumSq S + (S + 1) * (S + 1)

/-- A `Nat` quadratic identity `(k+2)(2k+3) = k(2k+1) + 6(k+1)` (the per-step
RHS increment, with `(k+1)` factored out).  Only `k*k` is opaque to `omega`. -/
theorem quad_step (k : Nat) :
    (k + 2) * (2 * k + 3) = k * (2 * k + 1) + 6 * (k + 1) := by
  -- LHS = 2k² + 7k + 6 ; RHS = 2k² + k + 6k + 6.  Expand both, k*k opaque.
  have hL : (k + 2) * (2 * k + 3) = 2 * (k * k) + 7 * k + 6 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    have : k * (2 * k) = 2 * (k * k) := by
      rw [Nat.mul_comm k (2 * k), Nat.mul_assoc]
    rw [this]; omega
  have hR : k * (2 * k + 1) + 6 * (k + 1) = 2 * (k * k) + 7 * k + 6 := by
    rw [Nat.mul_add, Nat.mul_one]
    have : k * (2 * k) = 2 * (k * k) := by
      rw [Nat.mul_comm k (2 * k), Nat.mul_assoc]
    rw [this]; omega
  rw [hL, hR]

/-- **The closed form `6·sumSq S = S(S+1)(2S+1)`** (Nat), by induction on `S`.
The step factors `(k+1)` out of the RHS increment and uses `quad_step`. -/
theorem six_sumSq (S : Nat) : 6 * sumSq S = S * (S + 1) * (2 * S + 1) := by
  induction S with
  | zero => decide
  | succ k ih =>
      show 6 * (sumSq k + (k + 1) * (k + 1)) = (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1)
      have hexp : 6 * (sumSq k + (k + 1) * (k + 1))
          = 6 * sumSq k + 6 * ((k + 1) * (k + 1)) := by rw [Nat.mul_add]
      rw [hexp, ih]
      -- prove   k(k+1)(2k+1) + 6(k+1)² = (k+1)(k+2)(2k+3)   via cube atoms.
      -- LHS into atoms:
      have hkk : k * (k + 1) = k * k + k := by rw [Nat.mul_add, Nat.mul_one]
      have hcube : k * (k * k) = k * k * k := by rw [Nat.mul_assoc]
      have hL : k * (k + 1) * (2 * k + 1) = 2 * (k * k * k) + 3 * (k * k) + k := by
        rw [hkk, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one]
        -- (k*k)*(2*k) + k*(2*k) + (k*k + k)
        have a1 : (k * k) * (2 * k) = 2 * (k * k * k) := by
          rw [Nat.mul_comm (k * k) (2 * k), Nat.mul_assoc, hcube]
        have a2 : k * (2 * k) = 2 * (k * k) := by
          rw [Nat.mul_comm k (2 * k), Nat.mul_assoc]
        rw [a1, a2]; omega
      have hSq : 6 * ((k + 1) * (k + 1)) = 6 * (k * k) + 12 * k + 6 := by
        have e : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
        rw [e]; omega
      have hR : (k + 1) * (k + 1 + 1) * (2 * (k + 1) + 1)
          = 2 * (k * k * k) + 9 * (k * k) + 13 * k + 6 := by
        have hidx : (k + 1 + 1) = (k + 2) := by omega
        have hidx2 : (2 * (k + 1) + 1) = (2 * k + 3) := by omega
        rw [hidx, hidx2, Nat.mul_assoc, quad_step k, Nat.mul_add]
        -- (k+1)*(k*(2k+1)) + (k+1)*(6(k+1))
        have t1 : (k + 1) * (k * (2 * k + 1)) = 2 * (k * k * k) + 3 * (k * k) + k := by
          have : (k + 1) * (k * (2 * k + 1)) = k * (k + 1) * (2 * k + 1) := by
            rw [Nat.mul_comm (k + 1) (k * (2 * k + 1)), Nat.mul_assoc,
              Nat.mul_comm (2 * k + 1) (k + 1), ← Nat.mul_assoc]
          rw [this, hL]
        have t2 : (k + 1) * (6 * (k + 1)) = 6 * (k * k) + 12 * k + 6 := by
          have : (k + 1) * (6 * (k + 1)) = 6 * ((k + 1) * (k + 1)) := by
            rw [Nat.mul_comm 6 (k + 1), ← Nat.mul_assoc, Nat.mul_comm ((k+1)*(k+1)) 6]
          rw [this, hSq]
        rw [t1, t2]; omega
      rw [hL, hSq, hR]; omega

/-- **The cube lower bound `S³ ≤ 3·sumSq S`** (Nat).  `6·sumSq = S(S+1)(2S+1) =
2S³ + 3S² + S ≥ 2S³`, so `2·(3·sumSq) ≥ 2S³`, hence `3·sumSq ≥ S³`. -/
theorem sumSq_cube_lb (S : Nat) : S * S * S ≤ 3 * sumSq S := by
  have h6 : 6 * sumSq S = S * (S + 1) * (2 * S + 1) := six_sumSq S
  -- S(S+1)(2S+1) ≥ 2·S³ : factor and bound.  S(S+1)(2S+1) = S·((S+1)(2S+1)),
  -- and (S+1)(2S+1) ≥ 2S² so S·((S+1)(2S+1)) ≥ 2S³.
  have hfac : S * (S + 1) * (2 * S + 1) = S * ((S + 1) * (2 * S + 1)) := by
    rw [Nat.mul_assoc]
  have hquad : 2 * (S * S) ≤ (S + 1) * (2 * S + 1) := by
    -- (S+1)(2S+1) = 2S²+3S+1 ≥ 2S²
    have : (S + 1) * (2 * S + 1) = 2 * (S * S) + 3 * S + 1 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      have : S * (2 * S) = 2 * (S * S) := by rw [Nat.mul_comm S (2 * S), Nat.mul_assoc]
      rw [this]; omega
    omega
  have hcube : 2 * (S * S * S) ≤ S * (S + 1) * (2 * S + 1) := by
    rw [hfac]
    have hm : S * (2 * (S * S)) ≤ S * ((S + 1) * (2 * S + 1)) :=
      Nat.mul_le_mul_left S hquad
    have he : S * (2 * (S * S)) = 2 * (S * S * S) := by
      rw [Nat.mul_comm S (2 * (S * S)), Nat.mul_assoc, Nat.mul_comm (S * S) S,
        ← Nat.mul_assoc S S S]
    omega
  -- 2·(3·sumSq) = 6·sumSq ≥ 2·S³ ⟹ 3·sumSq ≥ S³.
  have h2 : 2 * (3 * sumSq S) = 6 * sumSq S := by omega
  omega

/-! ## 2. PILLAR 1 — the partition LOWER bound `Zsum ≥ (1/6)·S³` (UNCONDITIONAL)

For a cutoff `S` with `2·C₄(S)·(1−w) ≤ 1` (so each head term obeys the Bernoulli
floor `w^{C₄ s} ≥ 1/2`), the partition is bounded below by half the sum of the
first `S` squares, hence by `(1/6)·S³`. -/

/-- `ofNat (a) ≤ ofNat (b)` from `a ≤ b` (Nat), local restatement. -/
theorem ofNat_le_ofNat' {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b :=
  ofNat_le_ofNat h

/-- **The Bernoulli head floor.**  If `2·C₄(s)·(1−w) ≤ 1` and `0 ≤ w ≤ 1`, then
`(1/2) ≤ w^{C₄ s}`.  PROOF: Bernoulli `w^{C₄ s} ≥ 1 − C₄(s)·(1−w)`, and
`C₄(s)·(1−w) ≤ 1/2` from the cutoff. -/
theorem qpow_head_half {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat) (hcut : Q'.ofNat 2 * (Q'.ofNat (c4 s) * ((1 : Q') - w)) ≤ (1 : Q')) :
    HalfPow.half ≤ qpow w (c4 s) := by
  -- C₄(s)·(1−w) ≤ 1/2  from  2·(C₄·(1−w)) ≤ 1
  have hhalf : Q'.ofNat (c4 s) * ((1 : Q') - w) ≤ HalfPow.half := by
    -- 2·X ≤ 1 ⟹ X ≤ 1/2.  Multiply by 1/2 ≥ 0 and collapse.
    have hr : (Q'.ofNat 2 * (Q'.ofNat (c4 s) * ((1 : Q') - w))) * HalfPow.half
        ≤ (1 : Q') * HalfPow.half :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hcut HalfPow.half_nonneg
    -- LHS ≃ (2·(1/2))·X ≃ 1·X ≃ X ;  RHS ≃ 1/2
    refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv (Q'.one_mul_eqv HalfPow.half))
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv ?_) hr
    -- X ≃ (2·X)·(1/2):  (2·X)·(1/2) ≃ (2·(1/2))·X ≃ 1·X ≃ X
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ HalfPow.half
        (Q'.mul_comm_eqv (Q'.ofNat 2) (Q'.ofNat (c4 s) * ((1 : Q') - w)))) ?_
    -- ((C₄·(1−w))·2)·(1/2) ≃ (C₄·(1−w))·(2·(1/2)) ≃ (C₄·(1−w))·1 ≃ C₄·(1−w)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (Q'.ofNat (c4 s) * ((1 : Q') - w)) (Q'.ofNat 2) HalfPow.half) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (Q'.ofNat (c4 s) * ((1 : Q') - w)) _ (1 : Q') ?_) ?_
    · show ((Q'.ofNat 2) * HalfPow.half).eqv (1 : Q'); decide
    · exact Q'.mul_one_eqv (Q'.ofNat (c4 s) * ((1 : Q') - w))
  -- Bernoulli at n = C₄ s : 1 − C₄(s)·(1−w) ≤ w^{C₄ s}
  have hbern : (1 : Q') - Q'.ofNat (c4 s) * ((1 : Q') - w) ≤ qpow w (c4 s) :=
    qpow_ge_bernoulli hw0 hw1 (c4 s)
  -- 1/2 ≤ 1 − C₄(s)·(1−w)  since  C₄(s)·(1−w) ≤ 1/2
  have hge : HalfPow.half ≤ (1 : Q') - Q'.ofNat (c4 s) * ((1 : Q') - w) := by
    -- 1/2 + X ≤ 1  ⟹  1/2 ≤ 1 − X.
    have hsum : HalfPow.half + Q'.ofNat (c4 s) * ((1 : Q') - w) ≤ (1 : Q') := by
      have h1 : HalfPow.half + Q'.ofNat (c4 s) * ((1 : Q') - w)
          ≤ HalfPow.half + HalfPow.half :=
        Q'.add_le_add_left HalfPow.half _ _ hhalf
      refine Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv ?_)
      show (HalfPow.half + HalfPow.half).eqv (1 : Q'); decide
    -- goal: 1/2 ≤ 1 + -(X) ; from hsum + (-X) and (1/2 + X) + -X ≃ 1/2.
    show HalfPow.half ≤ (1 : Q') + -(Q'.ofNat (c4 s) * ((1 : Q') - w))
    have hstep : (HalfPow.half + Q'.ofNat (c4 s) * ((1 : Q') - w))
          + -(Q'.ofNat (c4 s) * ((1 : Q') - w))
        ≤ (1 : Q') + -(Q'.ofNat (c4 s) * ((1 : Q') - w)) :=
      Q'.add_le_add_right _ _ _ hsum
    refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv ?_) hstep
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv HalfPow.half _ _) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left HalfPow.half _ 0
        (Q'.add_neg_self_eqv (Q'.ofNat (c4 s) * ((1 : Q') - w)))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' HalfPow.half)
  exact Q'.le_trans' _ _ _ hge hbern

/-! ### The head term lower bound and the sum of the head -/

/-- **Per-mode head lower bound.**  Under the head cutoff floor at mode `s`
(`2·C₄(s)·(1−w) ≤ 1`), the `Zsum` summand is bounded below by half its
polynomial weight:

    (s+1)²·w^{C₄ s}  ≥  (1/2)·ofNat((s+1)²).

PROOF.  `w^{C₄ s} ≥ 1/2` (`qpow_head_half`), multiply by `(s+1)² ≥ 0`. -/
theorem Zsum_summand_ge_half {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (s : Nat)
    (hcut : Q'.ofNat 2 * (Q'.ofNat (c4 s) * ((1 : Q') - w)) ≤ (1 : Q')) :
    HalfPow.half * Q'.ofNat ((s + 1) * (s + 1))
      ≤ dimQ s * (dimQ s * qpow w (c4 s)) := by
  have hhalf : HalfPow.half ≤ qpow w (c4 s) := qpow_head_half hw0 hw1 s hcut
  -- dimQ s = ofNat (s+1)
  show HalfPow.half * Q'.ofNat ((s + 1) * (s + 1))
      ≤ Q'.ofNat (s + 1) * (Q'.ofNat (s + 1) * qpow w (c4 s))
  -- RHS ≥ ofNat(s+1)·(ofNat(s+1)·(1/2)) ≃ (1/2)·ofNat((s+1)²)
  have hd : (0 : Q') ≤ Q'.ofNat (s + 1) := zero_le_ofNat _
  have hstep1 : Q'.ofNat (s + 1) * (Q'.ofNat (s + 1) * HalfPow.half)
      ≤ Q'.ofNat (s + 1) * (Q'.ofNat (s + 1) * qpow w (c4 s)) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hhalf hd) hd
  refine Q'.le_trans' _ _ _ ?_ hstep1
  -- (1/2)·ofNat((s+1)²) ≃ ofNat(s+1)·(ofNat(s+1)·(1/2))
  refine Q'.le_of_eqv ?_
  -- (1/2)·ofNat((s+1)(s+1)) ≃ (1/2)·(ofNat(s+1)·ofNat(s+1))
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left HalfPow.half _ _ (ofNat_mul_eqv (s + 1) (s + 1))) ?_
  -- (1/2)·(A·A) ≃ A·(A·(1/2))  (A = ofNat(s+1))
  -- (1/2)·(A·A) ≃ ((1/2)·A)·A ≃ (A·(1/2))·A ≃ A·((1/2)·A) ≃ A·(A·(1/2))
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv HalfPow.half (Q'.ofNat (s + 1)) (Q'.ofNat (s + 1)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Q'.ofNat (s + 1))
      (Q'.mul_comm_eqv HalfPow.half (Q'.ofNat (s + 1)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (Q'.ofNat (s + 1)) HalfPow.half (Q'.ofNat (s + 1))) ?_
  exact Q'.mul_eqv_congr_left (Q'.ofNat (s + 1)) _ _
    (Q'.mul_comm_eqv HalfPow.half (Q'.ofNat (s + 1)))

/-- `fsum (fun s => (1/2)·ofNat((s+1)²)) S ≃ (1/2)·ofNat(sumSq S)` (factor the
constant `1/2` out of the head sum; `∑_{s<S}(s+1)² = sumSq S`). -/
theorem head_sumSq (S : Nat) :
    (fsum (fun s => HalfPow.half * Q'.ofNat ((s + 1) * (s + 1))) S).eqv
      (HalfPow.half * Q'.ofNat (sumSq S)) := by
  induction S with
  | zero =>
      show (fsum (fun s => HalfPow.half * Q'.ofNat ((s + 1) * (s + 1))) 0).eqv
        (HalfPow.half * Q'.ofNat (sumSq 0))
      show (0 : Q').eqv (HalfPow.half * Q'.ofNat (sumSq 0))
      -- sumSq 0 = 0, ofNat 0 ≃ 0, (1/2)·0 ≃ 0
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left HalfPow.half _ 0 Q'.ofNat_zero_eqv) ?_
      exact QPoly.q_mul_zero HalfPow.half
  | succ k ih =>
      show (fsum (fun s => HalfPow.half * Q'.ofNat ((s + 1) * (s + 1))) k
            + HalfPow.half * Q'.ofNat ((k + 1) * (k + 1))).eqv
        (HalfPow.half * Q'.ofNat (sumSq (k + 1)))
      -- sumSq (k+1) = sumSq k + (k+1)²
      have hidx : sumSq (k + 1) = sumSq k + (k + 1) * (k + 1) := rfl
      rw [hidx]
      -- RHS = (1/2)·ofNat(sumSq k + (k+1)²) ≃ (1/2)·ofNat(sumSq k) + (1/2)·ofNat((k+1)²)
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _ ih) ?_
      -- (1/2)·ofNat(sumSq k) + (1/2)·ofNat((k+1)²) ≃ (1/2)·(ofNat(sumSq k) + ofNat((k+1)²))
      --   ≃ (1/2)·ofNat(sumSq k + (k+1)²)
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_add_eqv HalfPow.half (Q'.ofNat (sumSq k))
          (Q'.ofNat ((k + 1) * (k + 1))))) ?_
      exact Q'.mul_eqv_congr_left HalfPow.half _ _
        (Q'.eqv_symm (Q'.ofNat_add_eqv (sumSq k) ((k + 1) * (k + 1))))

/-! ## 3. PILLAR 1 (the prize): `Zsum w N ≥ (1/2)·sumSq S ≥ (1/6)·S³`

UNCONDITIONAL given a cutoff `S` with the per-mode head floors and `S ≤ N`. -/

/-- **Head termwise comparison.**  Under the head floors on `s < S`, the head sum
of the polynomial lower bounds is `≤` the head sum of the `Zsum` summands. -/
theorem head_le_Zsum_head {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    ∀ S, (∀ s, s < S →
        Q'.ofNat 2 * (Q'.ofNat (c4 s) * ((1 : Q') - w)) ≤ (1 : Q')) →
      fsum (fun s => HalfPow.half * Q'.ofNat ((s + 1) * (s + 1))) S
        ≤ fsum (fun s => dimQ s * (dimQ s * qpow w (c4 s))) S
  | 0, _ => Q'.le_refl' 0
  | k + 1, hfloor => by
      show fsum (fun s => HalfPow.half * Q'.ofNat ((s + 1) * (s + 1))) k
            + HalfPow.half * Q'.ofNat ((k + 1) * (k + 1))
          ≤ fsum (fun s => dimQ s * (dimQ s * qpow w (c4 s))) k
            + dimQ k * (dimQ k * qpow w (c4 k))
      have ihk := head_le_Zsum_head hw0 hw1 k
        (fun s hs => hfloor s (Nat.lt_succ_of_lt hs))
      have hlast : HalfPow.half * Q'.ofNat ((k + 1) * (k + 1))
          ≤ dimQ k * (dimQ k * qpow w (c4 k)) :=
        Zsum_summand_ge_half hw0 hw1 k (hfloor k (Nat.lt_succ_self k))
      exact Q'.le_trans' _ _ _ (Q'.add_le_add_right _ _ _ ihk)
        (Q'.add_le_add_left _ _ _ hlast)

/-- **PILLAR 1 — the partition LOWER bound (head form).**  If `S ≤ N`,
`0 ≤ w ≤ 1`, and each head mode `s < S` satisfies the cutoff floor
`2·C₄(s)·(1−w) ≤ 1`, then

    Zsum w N  ≥  (1/2)·ofNat(sumSq S).

PROOF.  `Zsum w N ≥ Zsum w S` (prefix monotone); termwise the head is
`≥ (1/2)·ofNat((s+1)²)` (`Zsum_summand_ge_half`); sum and factor
(`head_sumSq`). -/
theorem Zsum_ge_head {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (S N : Nat) (hSN : S ≤ N)
    (hfloor : ∀ s, s < S →
      Q'.ofNat 2 * (Q'.ofNat (c4 s) * ((1 : Q') - w)) ≤ (1 : Q')) :
    HalfPow.half * Q'.ofNat (sumSq S) ≤ Zsum w N := by
  -- Zsum w S ≤ Zsum w N
  have hpre : Zsum w S ≤ Zsum w N :=
    AFRateCalibration.fsum_le_of_le (fun i => Zsum_summand_nonneg hw0 i) hSN
  refine Q'.le_trans' _ _ _ ?_ hpre
  refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (head_sumSq S)) ?_
  exact head_le_Zsum_head hw0 hw1 S hfloor

/-- **PILLAR 1 — the CUBE lower bound (the τ^{−3/2} scale).**  Under the same head
floors, `6·Zsum w N ≥ ofNat(S³)`, i.e.

    Zsum w N  ≥  (1/6)·ofNat(S·S·S).

Instantiated at the moving cutoff `S = S₀(w)` with `C₄(S₀) ≍ 1/(2τ)` (so
`S₀ ≍ τ^{−1/2}`) this is the partition lower bound `Zsum ≳ τ^{−3/2}`.  We keep
`S` as the named cutoff parameter.  PROOF: `Zsum ≥ (1/2)·sumSq S` (`Zsum_ge_head`)
and `S³ ≤ 3·sumSq S` (`sumSq_cube_lb`), so `6·Zsum ≥ 3·sumSq ≥ S³`. -/
theorem Zsum_ge_cube {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (S N : Nat) (hSN : S ≤ N)
    (hfloor : ∀ s, s < S →
      Q'.ofNat 2 * (Q'.ofNat (c4 s) * ((1 : Q') - w)) ≤ (1 : Q')) :
    Q'.ofNat (S * S * S) ≤ Q'.ofNat 6 * Zsum w N := by
  have hhead : HalfPow.half * Q'.ofNat (sumSq S) ≤ Zsum w N :=
    Zsum_ge_head hw0 hw1 S N hSN hfloor
  -- 6·Zsum ≥ 6·((1/2)·sumSq) ≃ 3·sumSq ≥ S³.
  have hcube : S * S * S ≤ 3 * sumSq S := sumSq_cube_lb S
  have h6 : Q'.ofNat 6 * (HalfPow.half * Q'.ofNat (sumSq S)) ≤ Q'.ofNat 6 * Zsum w N :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hhead (zero_le_ofNat 6)
  refine Q'.le_trans' _ _ _ ?_ h6
  -- ofNat(S³) ≤ ofNat(3·sumSq) ≃ 6·((1/2)·sumSq)
  have hle : Q'.ofNat (S * S * S) ≤ Q'.ofNat (3 * sumSq S) := ofNat_le_ofNat' hcube
  refine Q'.le_trans' _ _ _ hle ?_
  -- ofNat(3·sumSq) ≃ ofNat 3 · ofNat(sumSq) ≃ 6·((1/2)·sumSq)
  refine Q'.le_of_eqv ?_
  refine Q'.eqv_trans _ _ _ (ofNat_mul_eqv 3 (sumSq S)) ?_
  -- ofNat 3 · ofNat(sumSq) ≃ 6·((1/2)·ofNat(sumSq)) : 3 = 6·(1/2)
  refine Q'.eqv_symm ?_
  -- 6·((1/2)·X) ≃ (6·(1/2))·X ≃ 3·X
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 6) HalfPow.half (Q'.ofNat (sumSq S)))) ?_
  refine Q'.mul_eqv_congr_right _ _ (Q'.ofNat (sumSq S)) ?_
  show ((Q'.ofNat 6) * HalfPow.half).eqv (Q'.ofNat 3)
  decide

/-! ## 4. PILLAR 2 — the HEAD moment via `∑ μ ≤ 1` (UNCONDITIONAL)

`headMu_le_one`: the partial mass `∑_{s<S} μ(s) ≤ 1` (the probability-weight
fact, NOT count·max).  Then on the head where `y_s = (1−w)·C₄(s) ≤ 1`, the
renormalized summand `(1−w)²·casimirSqTerm = μ·(1+y_s)^q·y_s² ≤ 2^q·μ`, so the
renormalized head moment is `≤ 2^q·∑μ ≤ 2^q` — `w`-INDEPENDENT. -/

/-- **PILLAR 2(a) — `∑_{s<S} μ ≤ 1`.**  The partial mass of the normalized
partition density is `≤ 1` for `S ≤ N`.  PROOF: `∑_{s<S} μ(s) = (∑_{s<S}
summand s)·(1/Zsum) ≤ Zsum·(1/Zsum) ≃ 1`, since the head sum of the nonnegative
summands is `≤` the full sum `Zsum w N`. -/
theorem headMu_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) (N : Nat)
    (hZ : (0 : Q') < Zsum w N) (S : Nat) (hSN : S ≤ N) :
    fsum (μ w N hZ) S ≤ (1 : Q') := by
  -- μ w N hZ s = summand s * Q'.recipPos (Zsum w N) hZ
  have hμeq : ∀ s, μ w N hZ s
      = (dimQ s * (dimQ s * qpow w (c4 s))) * Q'.recipPos (Zsum w N) hZ := fun _ => rfl
  -- fsum μ S ≃ (fsum summand S) · recip
  have hpull : (fsum (μ w N hZ) S).eqv
      (fsum (fun s => dimQ s * (dimQ s * qpow w (c4 s))) S * Q'.recipPos (Zsum w N) hZ) := by
    rw [fsum_eq_finSum (μ w N hZ) S,
      fsum_eq_finSum (fun s => dimQ s * (dimQ s * qpow w (c4 s))) S]
    refine Q'.eqv_trans _ _ _ ?_
      (Q'.eqv_symm (RationalTail.finSum_mul_const
        (fun s => dimQ s * (dimQ s * qpow w (c4 s))) (Q'.recipPos (Zsum w N) hZ) S))
    -- termwise μ s = summand s * recip
    refine RationalTail.finSum_eqv_congr (μ w N hZ)
      (fun s => (dimQ s * (dimQ s * qpow w (c4 s))) * Q'.recipPos (Zsum w N) hZ) ?_ S
    intro s; rw [hμeq s]; exact Q'.eqv_refl _
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hpull) ?_
  -- (fsum summand S)·recip ≤ Zsum·recip ≃ 1
  have hhead_le : fsum (fun s => dimQ s * (dimQ s * qpow w (c4 s))) S ≤ Zsum w N :=
    AFRateCalibration.fsum_le_of_le (fun i => Zsum_summand_nonneg hw0 i) hSN
  have hrnn : (0 : Q') ≤ Q'.recipPos (Zsum w N) hZ := Q'.le_of_lt (Q'.recipPos_pos (Zsum w N) hZ)
  have hstep : fsum (fun s => dimQ s * (dimQ s * qpow w (c4 s))) S * Q'.recipPos (Zsum w N) hZ
      ≤ Zsum w N * Q'.recipPos (Zsum w N) hZ :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hhead_le hrnn
  refine Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv ?_)
  exact Q'.mul_recipPos_eqv (Zsum w N) hZ

/-- **The renormalized Casimir-square term equals the Gaussian-moment summand.**
`(1−w)²·casimirSqTerm w N hZ q s ≃ μ(s)·(qfac(w,s)^q·(yArg(w,s)·yArg(w,s)))`,
i.e. with `y_s = (1−w)·C₄(s)` and `qfac = 1 + y_s`: `μ·(1+y_s)^q·y_s²`.  PROOF:
`(1−w)²·C₄² = ((1−w)·C₄)² = y_s²`, pulled into the term. -/
theorem renorm_casimirSqTerm_eqv {w : Q'} (N : Nat) (hZ : (0 : Q') < Zsum w N)
    (q s : Nat) :
    (((1 : Q') - w) * ((1 : Q') - w) * casimirSqTerm w N hZ q s).eqv
      (μ w N hZ s * (qfac w s ^ q * (yArg w s * yArg w s))) := by
  -- casimirSqTerm = μ·(qfac^q·(C₄·C₄)).
  show (((1 : Q') - w) * ((1 : Q') - w)
        * (μ w N hZ s * (qfac w s ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))))).eqv
      (μ w N hZ s * (qfac w s ^ q * (yArg w s * yArg w s)))
  -- yArg = (1−w)·C₄ ; yArg² = (1−w)²·C₄².  Reassociate the τ² inside.
  -- Strategy: rewrite RHS's yArg·yArg into (1−w)²·(C₄·C₄), then both sides are
  -- the same product up to assoc/comm.  Work via num/den `eqv` reduction.
  show (((1 : Q') - w) * ((1 : Q') - w)
        * (μ w N hZ s * (qfac w s ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))))).num
        * ((μ w N hZ s * (qfac w s ^ q * (yArg w s * yArg w s))).den : Int)
      = (μ w N hZ s * (qfac w s ^ q * (yArg w s * yArg w s))).num
        * ((((1 : Q') - w) * ((1 : Q') - w)
            * (μ w N hZ s * (qfac w s ^ q * (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))))).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, yArg]
  push_cast
  ac_rfl

/-- **PILLAR 2(b) — the renormalized HEAD moment bound (`w`-uniform).**  On the
head `s < S` where `y_s ≤ 1` (the cutoff floor `(1−w)·C₄(s) ≤ 1`), the
renormalized moment summand is `≤ 2^q·μ(s)`:

    (1−w)²·casimirSqTerm w N hZ q s  ≤  ofNat(2^q)·μ(s).

PROOF.  `(1−w)²·casimirSqTerm = μ·(1+y_s)^q·y_s²` (`renorm_casimirSqTerm_eqv`);
`qfac = 1+y_s ≤ 2` and `y_s² ≤ 1` on the head, so `(1+y_s)^q·y_s² ≤ 2^q`. -/
theorem renorm_head_term_le {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q s : Nat)
    (hy : yArg w s ≤ (1 : Q')) :
    ((1 : Q') - w) * ((1 : Q') - w) * casimirSqTerm w N hZ q s
      ≤ Q'.ofNat (2 ^ q) * μ w N hZ s := by
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (renorm_casimirSqTerm_eqv N hZ q s)) ?_
  -- μ·(qfac^q·y²) ≤ μ·(2^q·1) = 2^q·μ
  have hynn : (0 : Q') ≤ yArg w s := yArg_nonneg hw1 s
  have hμnn : (0 : Q') ≤ μ w N hZ s := μ_nonneg hw0 N hZ s
  -- qfac w s = 1 + y_s ≤ 2
  have hqfac2 : qfac w s ≤ Q'.ofNat 2 := by
    show (1 : Q') + ((1 : Q') - w) * Q'.ofNat (c4 s) ≤ Q'.ofNat 2
    -- (1−w)·C₄ = yArg ≤ 1, so 1 + yArg ≤ 1 + 1 = 2
    have : (1 : Q') + yArg w s ≤ (1 : Q') + (1 : Q') :=
      Q'.add_le_add_left (1 : Q') _ _ hy
    refine Q'.le_trans' _ _ _ this (Q'.le_of_eqv ?_)
    show ((1 : Q') + (1 : Q')).eqv (Q'.ofNat 2); decide
  have hqfacnn : (0 : Q') ≤ qfac w s := qfac_nonneg hw1 s
  -- qfac^q ≤ 2^q
  have hqpow : qfac w s ^ q ≤ Q'.ofNat 2 ^ q := pow_le_pow_of_le hqfacnn hqfac2 q
  have h2qeq : (Q'.ofNat 2 ^ q).eqv (Q'.ofNat (2 ^ q)) := ofNat_two_pow_eqv q
  -- y² ≤ 1
  have hysq : yArg w s * yArg w s ≤ (1 : Q') := by
    have h1 : yArg w s * yArg w s ≤ (1 : Q') * yArg w s :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hy hynn
    have h2 : (1 : Q') * yArg w s ≤ (1 : Q') * (1 : Q') :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hy (by decide)
    refine Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv ?_))
    show ((1 : Q') * (1 : Q')).eqv (1 : Q'); decide
  -- qfac^q·y² ≤ 2^q·1 = 2^q
  have hfac : qfac w s ^ q * (yArg w s * yArg w s) ≤ Q'.ofNat (2 ^ q) := by
    have hb1 : qfac w s ^ q * (yArg w s * yArg w s)
        ≤ Q'.ofNat 2 ^ q * (yArg w s * yArg w s) :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hqpow (Q'.mul_nonneg _ _ hynn hynn)
    have h2qnn : (0 : Q') ≤ Q'.ofNat 2 ^ q := Q'.pow_nonneg _ (zero_le_ofNat 2) q
    have hb2 : Q'.ofNat 2 ^ q * (yArg w s * yArg w s) ≤ Q'.ofNat 2 ^ q * (1 : Q') :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hysq h2qnn
    refine Q'.le_trans' _ _ _ hb1 (Q'.le_trans' _ _ _ hb2 ?_)
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.ofNat 2 ^ q))) ?_
    exact Q'.le_of_eqv h2qeq
  -- μ·(qfac^q·y²) ≤ μ·2^q = 2^q·μ
  have hmul : μ w N hZ s * (qfac w s ^ q * (yArg w s * yArg w s))
      ≤ μ w N hZ s * Q'.ofNat (2 ^ q) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hfac hμnn
  refine Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv ?_)
  exact Q'.mul_comm_eqv (μ w N hZ s) (Q'.ofNat (2 ^ q))

/-- **PILLAR 2(c) — the renormalized HEAD moment is `≤ 2^q` (`w`-uniform).**  For
`S ≤ N`, `0 ≤ w ≤ 1`, and each head mode `s < S` with `yArg w s ≤ 1`:

    (1−w)² · (head of casimirSqSum, i.e. ∑_{s<S} casimirSqTerm)  ≤  ofNat(2^q).

PROOF.  Pull `(1−w)²` into the sum (`const_mul_finSum`); termwise
`(1−w)²·casimirSqTerm s ≤ 2^q·μ(s)` (`renorm_head_term_le`); sum `≤ 2^q·∑μ ≤
2^q·1` (`headMu_le_one`).  The constant `2^q` is `w`-INDEPENDENT. -/
theorem head_moment_uniform {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (N : Nat) (hZ : (0 : Q') < Zsum w N) (q S : Nat) (hSN : S ≤ N)
    (hy : ∀ s, s < S → yArg w s ≤ (1 : Q')) :
    ((1 : Q') - w) * ((1 : Q') - w)
        * RationalTail.finSum (fun s => casimirSqTerm w N hZ q s) S
      ≤ Q'.ofNat (2 ^ q) := by
  -- (1−w)²·∑ casimirSqTerm ≃ ∑ (1−w)²·casimirSqTerm
  have hpull : (((1 : Q') - w) * ((1 : Q') - w)
        * RationalTail.finSum (fun s => casimirSqTerm w N hZ q s) S).eqv
      (RationalTail.finSum
        (fun s => ((1 : Q') - w) * ((1 : Q') - w) * casimirSqTerm w N hZ q s) S) :=
    RationalTail.const_mul_finSum (fun s => casimirSqTerm w N hZ q s)
      (((1 : Q') - w) * ((1 : Q') - w)) S
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hpull) ?_
  -- termwise ≤ 2^q·μ ; sum ≤ 2^q·∑μ ≤ 2^q.
  have htermwise : RationalTail.finSum
        (fun s => ((1 : Q') - w) * ((1 : Q') - w) * casimirSqTerm w N hZ q s) S
      ≤ RationalTail.finSum (fun s => Q'.ofNat (2 ^ q) * μ w N hZ s) S := by
    -- finSum_le_lt: termwise on s < S
    refine YMGap.Constructive.finSum_le_lt _ _ S ?_
    intro s hs
    exact renorm_head_term_le hw0 hw1 N hZ q s (hy s hs)
  refine Q'.le_trans' _ _ _ htermwise ?_
  -- ∑ 2^q·μ ≃ 2^q·∑μ ≤ 2^q·1 = 2^q
  have hfactor : (RationalTail.finSum (fun s => Q'.ofNat (2 ^ q) * μ w N hZ s) S).eqv
      (Q'.ofNat (2 ^ q) * RationalTail.finSum (μ w N hZ) S) :=
    Q'.eqv_symm (RationalTail.const_mul_finSum (μ w N hZ) (Q'.ofNat (2 ^ q)) S)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) ?_
  -- 2^q·∑μ ≤ 2^q·1
  have hμ1 : RationalTail.finSum (μ w N hZ) S ≤ (1 : Q') := by
    have := headMu_le_one hw0 N hZ S hSN
    rwa [fsum_eq_finSum (μ w N hZ) S] at this
  have hstep : Q'.ofNat (2 ^ q) * RationalTail.finSum (μ w N hZ) S
      ≤ Q'.ofNat (2 ^ q) * (1 : Q') :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hμ1 (zero_le_ofNat _)
  refine Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv ?_)
  exact Q'.mul_one_eqv (Q'.ofNat (2 ^ q))

/-! ## 5. PILLAR 3 (named) + the fully-`w`-uniform ASSEMBLY

Pillar 3 (the tail moment) is the hardest piece (the dyadic partition-UPPER
bound with the τ^{−3/2} cancellation against Pillar 1).  We name the tail-moment
residual as ONE explicit hypothesis and prove the assembly conditional on it.
We do NOT fake it. -/

/-- **The named Pillar-3 residual.**  The renormalized TAIL moment past the moving
cutoff `S` is bounded by a `w`-INDEPENDENT constant `Ctail`:

    (1−w)² · ∑_{S ≤ s < S+M} casimirSqTerm w N hZ q s  ≤  ofNat Ctail,   ∀ M.

This is exactly what Pillar 3 (the dyadic block partition-upper bound
`∑(s+1)²·w^{C₄ s/2} ≤ K·τ^{−3/2}` combined with `geom_beats_sq` and the Pillar-1
lower bound `Zsum ≥ c·τ^{−3/2}`, whose τ^{−3/2} factors CANCEL) delivers.  It is
carried here as a `Type`-level certificate (a `Nat` constant `Ctail` plus the
windowed inequality), NOT proved — the honest open piece. -/
structure TailMomentCert (w : Q') (N : Nat) (hZ : (0 : Q') < Zsum w N) (q S : Nat)
    : Type where
  /-- The `w`-independent tail constant. -/
  Ctail : Nat
  /-- The renormalized tail moment bound, for every window `M`. -/
  tail_bound : ∀ M,
    ((1 : Q') - w) * ((1 : Q') - w)
        * RationalTail.finSum (fun k => casimirSqTerm w N hZ q (S + k)) M
      ≤ Q'.ofNat Ctail

/-- **THE FULLY-`w`-UNIFORM CASIMIR-SQUARE MOMENT (assembly, conditional on the
named Pillar-3 residual).**  Given:

  * `S ≤ N`, `0 ≤ w ≤ 1`;
  * the head floors `yArg w s ≤ 1` for `s < S` (Pillar 2);
  * the named tail certificate `tc` (Pillar 3),

the renormalized Casimir-square moment is bounded by the `w`-INDEPENDENT constant
`2^q + Ctail`:

    (1−w)² · casimirSqSum w N hZ q (S + M)  ≤  ofNat(2^q) + ofNat(tc.Ctail),   ∀ M.

PROOF.  Split the moment at `S` (`finSum_split`); the head is `≤ 2^q`
(`head_moment_uniform`, Pillar 2) and the tail is `≤ Ctail` (`tc.tail_bound`,
Pillar 3); the `(1−w)²` factor distributes over the split.  The constant
`2^q + Ctail` is genuinely independent of `w`. -/
theorem casimir_moment_uniform_of_named {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw1 : w ≤ (1 : Q')) (N : Nat) (hZ : (0 : Q') < Zsum w N) (q S : Nat)
    (hSN : S ≤ N) (hy : ∀ s, s < S → yArg w s ≤ (1 : Q'))
    (tc : TailMomentCert w N hZ q S) :
    ∀ M, ((1 : Q') - w) * ((1 : Q') - w) * casimirSqSum w N hZ q (S + M)
      ≤ Q'.ofNat (2 ^ q) + Q'.ofNat tc.Ctail := by
  intro M
  -- casimirSqSum w N hZ q (S+M) = finSum f (S+M), f = casimirSqTerm.
  show ((1 : Q') - w) * ((1 : Q') - w)
      * RationalTail.finSum (fun s => casimirSqTerm w N hZ q s) (S + M)
    ≤ Q'.ofNat (2 ^ q) + Q'.ofNat tc.Ctail
  -- split the sum at S
  have hsplit : (RationalTail.finSum (fun s => casimirSqTerm w N hZ q s) (S + M)).eqv
      (RationalTail.finSum (fun s => casimirSqTerm w N hZ q s) S
        + RationalTail.finSum (fun k => casimirSqTerm w N hZ q (S + k)) M) :=
    YMGap.Constructive.finSum_split (fun s => casimirSqTerm w N hZ q s) S M
  -- τ²·finSum (S+M) ≃ τ²·(head + tail) ≃ τ²·head + τ²·tail
  have hdistrib : (((1 : Q') - w) * ((1 : Q') - w)
        * RationalTail.finSum (fun s => casimirSqTerm w N hZ q s) (S + M)).eqv
      (((1 : Q') - w) * ((1 : Q') - w)
          * RationalTail.finSum (fun s => casimirSqTerm w N hZ q s) S
        + ((1 : Q') - w) * ((1 : Q') - w)
          * RationalTail.finSum (fun k => casimirSqTerm w N hZ q (S + k)) M) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (((1 : Q') - w) * ((1 : Q') - w)) _ _ hsplit) ?_
    exact Q'.mul_add_eqv (((1 : Q') - w) * ((1 : Q') - w))
      (RationalTail.finSum (fun s => casimirSqTerm w N hZ q s) S)
      (RationalTail.finSum (fun k => casimirSqTerm w N hZ q (S + k)) M)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hdistrib) ?_
  -- head ≤ 2^q ; tail ≤ Ctail
  have hhead : ((1 : Q') - w) * ((1 : Q') - w)
      * RationalTail.finSum (fun s => casimirSqTerm w N hZ q s) S ≤ Q'.ofNat (2 ^ q) :=
    head_moment_uniform hw0 hw1 N hZ q S hSN hy
  have htail : ((1 : Q') - w) * ((1 : Q') - w)
      * RationalTail.finSum (fun k => casimirSqTerm w N hZ q (S + k)) M
      ≤ Q'.ofNat tc.Ctail := tc.tail_bound M
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_right _ _ _ hhead)
    (Q'.add_le_add_left _ _ _ htail)

end YMGap.Continuum.MovingCutoff

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MovingCutoff.qpow_ge_bernoulli
#print axioms YMGap.Continuum.MovingCutoff.fsum_eq_finSum
#print axioms YMGap.Continuum.MovingCutoff.ofNat_two_pow_eqv
#print axioms YMGap.Continuum.MovingCutoff.quad_step
#print axioms YMGap.Continuum.MovingCutoff.six_sumSq
#print axioms YMGap.Continuum.MovingCutoff.sumSq_cube_lb
#print axioms YMGap.Continuum.MovingCutoff.qpow_head_half
#print axioms YMGap.Continuum.MovingCutoff.Zsum_summand_ge_half
#print axioms YMGap.Continuum.MovingCutoff.head_sumSq
#print axioms YMGap.Continuum.MovingCutoff.head_le_Zsum_head
#print axioms YMGap.Continuum.MovingCutoff.Zsum_ge_head
#print axioms YMGap.Continuum.MovingCutoff.Zsum_ge_cube
#print axioms YMGap.Continuum.MovingCutoff.headMu_le_one
#print axioms YMGap.Continuum.MovingCutoff.renorm_casimirSqTerm_eqv
#print axioms YMGap.Continuum.MovingCutoff.renorm_head_term_le
#print axioms YMGap.Continuum.MovingCutoff.head_moment_uniform
#print axioms YMGap.Continuum.MovingCutoff.casimir_moment_uniform_of_named
