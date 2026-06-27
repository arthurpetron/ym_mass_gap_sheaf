/-
Track B / R2 — the CORRECTED bond-moving retune to the rational surrogate of
`w^{1/p}`, and the re-derived all-`s` quadratic per-mode bound at the corrected base.

# Why this module exists — the retune had to be fixed

The previous retune `BondMovingQuadratic.renormTau p w = C₄(1)·(1 − w)` is
`p`-INDEPENDENT (the marginal-flow retuning matching the `s = 1` coefficient).  It
forces the renormalized heat-kernel weight `K_τ` to decay too FAST: the
bond-moved/heat-kernel RELATIVE residual `bmc(s)/K_τ(s) − 1` BLOWS UP at high modes,
because the equal-split fusion channel decays like `~ w^{s²/p}` and `K_τ` must
DOMINATE it.  The genuine satisfiability criterion is

    renormW^p ≥ w        (so `K_τ` decays slowly enough to dominate fusion).

The exact fix is the bond-moving inverse `renormW = w^{1/p}`, which is irrational and
has no closed form in this substrate.  Its RATIONAL surrogate

    renormW p w  :=  1 − (1 − w)/p

satisfies the criterion `renormW^p ≥ w` by Bernoulli's inequality
`(1 − t)^p ≥ 1 − p·t` at `t = (1 − w)/p` (giving `(1 − (1−w)/p)^p ≥ 1 − (1−w) = w`).

# What is PROVED here (genuine `Q'`/`Nat` arithmetic, axiom-clean)

  * `renormTauFix` / `renormWFix` — the corrected `p`-DEPENDENT retune
    `τ = (1 − w)/p`, `renormW = 1 − τ`.
  * `bernoulli_oneSub` — the general Bernoulli inequality `(1 − t)^p ≥ 1 − p·t` on
    `t ∈ [0,1]`, by induction on `p` with the exact product identity
    `(1 − t)·(1 − p·t) ≃ (1 − (p+1)·t) + p·t²`.
  * `renormWFix_pow_ge_w` — THE SATISFIABILITY CRITERION `w ≤ renormW^p` (the payoff
    of the corrected retune: `K_τ` dominates the slow fusion channel).
  * Gap properties: nonneg / pos / `≤ 1` / `< 1` for both `renormTauFix` and
    `renormWFix`; the gap margin is `renormTauFix = (1 − w)/p > 0` for `w < 1`.
  * `renormWFix_decay_dom` — the per-mode decay control `w^n ≤ renormW^{p·n}`.
  * `modeDefectFix` / `modeDefectFix_quadratic` — the re-derived all-`s` quadratic
    per-mode bound AT THE CORRECTED BASE `renormWFix p hp w`, mirroring the existing
    second-order-remainder template.  Corollary `modeDefectFix_quadratic_margin`
    rewrites `1 − renormWFix ≃ renormTauFix = (1 − w)/p`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, reusing the second-order Taylor engine, the qpow
monotonicity and iterated-power laws.  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.  No `Classical.*`,
no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.FullModeQuadratic

namespace YMGap.Continuum.BondMovingRetuneFix

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.FullModeQuadratic

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The corrected `p`-dependent retune `renormW = 1 − (1 − w)/p` -/

/-- The corrected heat-kernel-time retuning shift `τ = (1 − w)/p` (the `p`-dependent
margin that makes `renormW^p ≥ w`).  `renormTauFix = (1 − w)·(1/p)`. -/
def renormTauFix (p : Nat) (hp : 0 < p) (w : Q') : Q' :=
  ((1 : Q') - w) * Q'.mkPos 1 p hp

/-- **The corrected retune** `renormW = 1 − (1 − w)/p = 1 − renormTauFix p hp w` —
the rational surrogate of `w^{1/p}`, satisfying `renormW^p ≥ w`. -/
def renormWFix (p : Nat) (hp : 0 < p) (w : Q') : Q' :=
  (1 : Q') - renormTauFix p hp w

/-! ## 2. The rational fact `ofNat p · (1/p) ≃ 1` -/

/-- **`ofNat p · mkPos 1 p hp ≃ 1`** — the key rational cancellation `p · (1/p) = 1`.
PROOF: the product is `⟨p·1, 1·p − 1⟩ = ⟨p, p − 1⟩` (numerator `p`, denominator `p`),
which is `≃ 1` by cross-multiplication `p·1 = 1·p`. -/
theorem ofNat_mul_mkPos_one (p : Nat) (hp : 0 < p) :
    (Q'.ofNat p * Q'.mkPos 1 p hp) ≈ (1 : Q') := by
  -- eqv reduces to  prod.num * (1).den = (1).num * prod.den
  show (Q'.ofNat p * Q'.mkPos 1 p hp).num * (((1 : Q').den : Int))
     = ((1 : Q').num) * (((Q'.ofNat p * Q'.mkPos 1 p hp).den : Int))
  -- (1).num = 1, (1).den = 1
  have h1num : ((1 : Q').num) = (1 : Int) := rfl
  have h1den : ((1 : Q').den : Int) = (1 : Int) := rfl
  rw [h1num, h1den, Int.mul_one, Int.one_mul]
  -- prod.num = (ofNat p).num * (mkPos 1 p hp).num = p * 1 = p
  have hnum : (Q'.ofNat p * Q'.mkPos 1 p hp).num = (p : Int) := by
    show (Q'.ofNat p).num * (Q'.mkPos 1 p hp).num = (p : Int)
    rw [Q'.mkPos_num]
    show (Int.ofNat p) * (1 : Int) = (p : Int)
    rw [Int.mul_one]
    rfl
  -- prod.den = (ofNat p).den * (mkPos 1 p hp).den (cast) = 1 * p = p
  have hden : ((Q'.ofNat p * Q'.mkPos 1 p hp).den : Int) = (p : Int) := by
    -- den = denPred + 1 ; denPred of mul = (ofNat p).den * (mkPos 1 p).den - 1
    show (((Q'.ofNat p).den * (Q'.mkPos 1 p hp).den - 1) + 1 : Nat) = (p : Int)
    rw [Q'.mkPos_den]
    -- (ofNat p).den = 1
    have hod : (Q'.ofNat p).den = 1 := rfl
    rw [hod]
    -- (1 * p - 1) + 1 = p   (Nat), with p ≥ 1
    have : (1 * p - 1) + 1 = p := by omega
    rw [this]
  rw [hnum, hden]

/-! ## 3. Bernoulli's inequality `(1 − t)^p ≥ 1 − p·t` -/

/-- **The exact product identity** `(1 − t)·(1 − u) ≃ (1 − (u + t)) + u·t`.
Both sides reduce to the normal form `((1 + −u) + −t) + u·t`.  (The engine of the
Bernoulli induction step.) -/
theorem oneSub_mul_oneSub (t u : Q') :
    (((1 : Q') - t) * ((1 : Q') - u))
      ≈ (((1 : Q') - (u + t)) + u * t) := by
  -- normal form NF := ((1 + -u) + -t) + u*t
  -- ── LHS → NF ──
  -- (1 + -t)*(1 + -u) ≈ 1*(1+-u) + (-t)*(1+-u)
  have hL1 : (((1 : Q') + (-t)) * ((1 : Q') + (-u)))
      ≈ ((1 : Q') * ((1 : Q') + (-u)) + (-t) * ((1 : Q') + (-u))) :=
    Q'.add_mul_eqv (1 : Q') (-t) ((1 : Q') + (-u))
  -- 1*(1+-u) ≈ 1+-u
  have hL2 : ((1 : Q') * ((1 : Q') + (-u))) ≈ ((1 : Q') + (-u)) :=
    Q'.one_mul_eqv ((1 : Q') + (-u))
  -- (-t)*(1+-u) ≈ (-t)*1 + (-t)*(-u)
  have hL3 : ((-t) * ((1 : Q') + (-u))) ≈ ((-t) * (1 : Q') + (-t) * (-u)) :=
    Q'.mul_add_eqv (-t) (1 : Q') (-u)
  -- (-t)*1 ≈ -t
  have hL4 : ((-t) * (1 : Q')) ≈ (-t) := Q'.mul_one_eqv (-t)
  -- (-t)*(-u) ≈ u*t  :  (-t)*(-u) ≈ -(t*(-u)) ≈ -(-(t*u)) ≈ t*u ≈ u*t
  have hL5 : ((-t) * (-u)) ≈ (u * t) := by
    refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv t (-u)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv t u)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_neg_eqv (t * u)) ?_
    exact Q'.mul_comm_eqv t u
  -- combine: (-t)*(1+-u) ≈ -t + u*t
  have hL6 : ((-t) * ((1 : Q') + (-u))) ≈ ((-t) + u * t) :=
    Q'.eqv_trans _ _ _ hL3 (Q'.add_eqv_congr' hL4 hL5)
  -- LHS ≈ (1+-u) + (-t + u*t)
  have hL7 : (((1 : Q') + (-t)) * ((1 : Q') + (-u)))
      ≈ (((1 : Q') + (-u)) + ((-t) + u * t)) :=
    Q'.eqv_trans _ _ _ hL1 (Q'.add_eqv_congr' hL2 hL6)
  -- (1+-u) + (-t + u*t) ≈ ((1+-u) + -t) + u*t   [add_assoc symm]
  have hL8 : (((1 : Q') + (-u)) + ((-t) + u * t))
      ≈ ((((1 : Q') + (-u)) + (-t)) + u * t) :=
    Q'.eqv_symm (Q'.add_assoc_eqv ((1 : Q') + (-u)) (-t) (u * t))
  have hLNF : (((1 : Q') - t) * ((1 : Q') - u))
      ≈ ((((1 : Q') + (-u)) + (-t)) + u * t) :=
    Q'.eqv_trans _ _ _ hL7 hL8
  -- ── RHS → NF ──
  -- (1 - (u+t)) + u*t = (1 + -(u+t)) + u*t
  -- -(u+t) ≈ -u + -t
  have hR1 : (-(u + t)) ≈ ((-u) + (-t)) := Q'.neg_add_eqv u t
  -- 1 + -(u+t) ≈ 1 + (-u + -t) ≈ (1 + -u) + -t
  have hR2 : ((1 : Q') + (-(u + t))) ≈ ((1 : Q') + ((-u) + (-t))) :=
    Q'.add_eqv_congr_left (1 : Q') _ _ hR1
  have hR3 : ((1 : Q') + ((-u) + (-t))) ≈ (((1 : Q') + (-u)) + (-t)) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-u) (-t))
  have hR4 : (((1 : Q') - (u + t)) + u * t)
      ≈ ((((1 : Q') + (-u)) + (-t)) + u * t) :=
    Q'.add_eqv_congr_right _ _ (u * t) (Q'.eqv_trans _ _ _ hR2 hR3)
  -- chain: LHS ≈ NF ≈ RHS
  exact Q'.eqv_trans _ _ _ hLNF (Q'.eqv_symm hR4)

/-- `ofNat (p+1)·t ≃ ofNat p·t + t` (split the successor factor). -/
theorem ofNat_succ_mul (p : Nat) (t : Q') :
    (Q'.ofNat (p + 1) * t) ≈ (Q'.ofNat p * t + t) := by
  -- ofNat (p+1) ≈ ofNat p + 1
  have hps : (Q'.ofNat (p + 1)) ≈ (Q'.ofNat p + (1 : Q')) := by
    refine Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv p 1) ?_
    exact Q'.eqv_refl _
  -- (ofNat (p+1))·t ≈ (ofNat p + 1)·t ≈ ofNat p·t + 1·t ≈ ofNat p·t + t
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ t hps) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (Q'.ofNat p) (1 : Q') t) ?_
  exact Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv t)

/-- **Bernoulli's inequality** `(1 − t)^p ≥ 1 − p·t` on `t ∈ [0,1]`, for every `p`. -/
theorem bernoulli_oneSub (t : Q') (ht0 : (0 : Q') ≤ t) (ht1 : t ≤ (1 : Q')) :
    ∀ p : Nat, (1 : Q') - Q'.ofNat p * t ≤ qpow ((1 : Q') - t) p
  | 0 => by
      -- 1 - ofNat 0 · t ≤ qpow (1-t) 0 = 1
      show (1 : Q') + -(Q'.ofNat 0 * t) ≤ qpow ((1 : Q') - t) 0
      have hz : (Q'.ofNat 0 * t) ≈ (0 : Q') := by
        refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ t Q'.ofNat_zero_eqv) ?_
        exact Q'.zero_mul_eqv t
      -- 1 + -(ofNat 0 · t) ≈ 1 + -0 ≈ 1, and qpow (1-t) 0 = 1
      have hstep : ((1 : Q') + -(Q'.ofNat 0 * t)) ≈ (1 : Q') := by
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (1 : Q') _ _ (Q'.neg_eqv_congr _ _ hz)) ?_
        -- 1 + -0 ≈ 1
        refine Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left (1 : Q') _ _ ?_) (Q'.eqv_of_eq (Q'.add_zero' (1 : Q')))
        -- -0 ≈ 0
        show (-(0 : Q')) ≈ (0 : Q')
        exact Q'.eqv_of_eq (by rfl)
      -- qpow (1-t) 0 = 1
      have hq : qpow ((1 : Q') - t) 0 = (1 : Q') := rfl
      rw [hq]
      exact Q'.le_of_eqv hstep
  | p + 1 => by
      have ihp : (1 : Q') - Q'.ofNat p * t ≤ qpow ((1 : Q') - t) p :=
        bernoulli_oneSub t ht0 ht1 p
      have hnn : (0 : Q') ≤ (1 : Q') - t := Q'.sub_nonneg_of_le ht1
      -- RGTransport.qpow recurses on the RIGHT: qpow (1-t)(p+1) = qpow(1-t)p · (1-t)
      -- (1 - ofNat p·t)·(1-t) ≤ qpow(1-t)p · (1-t) = qpow(1-t)(p+1)
      have hmul : ((1 : Q') - Q'.ofNat p * t) * ((1 : Q') - t)
          ≤ qpow ((1 : Q') - t) p * ((1 : Q') - t) :=
        Q'.mul_le_mul_of_nonneg_right _ _ _ ihp hnn
      have hqsucc : qpow ((1 : Q') - t) p * ((1 : Q') - t)
          = qpow ((1 : Q') - t) (p + 1) := by rfl
      -- 1 - ofNat(p+1)·t ≤ (1 - ofNat p·t)·(1-t)
      -- identity: (1 - ofNat p·t)·(1-t) ≈ (1 - (t + ofNat p·t)) + t·(ofNat p·t)
      have hid : (((1 : Q') - Q'.ofNat p * t) * ((1 : Q') - t))
          ≈ (((1 : Q') - (t + Q'.ofNat p * t)) + t * (Q'.ofNat p * t)) :=
        oneSub_mul_oneSub (Q'.ofNat p * t) t
      -- t + ofNat p·t ≈ ofNat(p+1)·t, so 1 - (t + ofNat p·t) ≈ 1 - ofNat(p+1)·t
      have hsum : (t + Q'.ofNat p * t) ≈ (Q'.ofNat (p + 1) * t) := by
        refine Q'.eqv_trans _ _ _ (Q'.add_comm_eqv t (Q'.ofNat p * t)) ?_
        exact Q'.eqv_symm (ofNat_succ_mul p t)
      have hbase : ((1 : Q') - (t + Q'.ofNat p * t)) ≈ ((1 : Q') - Q'.ofNat (p + 1) * t) := by
        show ((1 : Q') + -(t + Q'.ofNat p * t)) ≈ ((1 : Q') + -(Q'.ofNat (p + 1) * t))
        exact Q'.add_eqv_congr_left (1 : Q') _ _ (Q'.neg_eqv_congr _ _ hsum)
      -- t·(ofNat p·t) ≥ 0
      have hsq : (0 : Q') ≤ t * (Q'.ofNat p * t) :=
        Q'.mul_nonneg _ _ ht0 (Q'.mul_nonneg _ _ (zero_le_ofNat p) ht0)
      -- 1 - ofNat(p+1)·t ≤ (1 - (t + ofNat p·t)) + t·(ofNat p·t)
      have hle1 : ((1 : Q') - Q'.ofNat (p + 1) * t)
          ≤ (((1 : Q') - (t + Q'.ofNat p * t)) + t * (Q'.ofNat p * t)) := by
        refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv hbase) ?_
        exact Q'.add_le_self_of_nonneg ((1 : Q') - (t + Q'.ofNat p * t)) _ hsq
      -- combine: 1 - ofNat(p+1)·t ≤ (1 - ofNat p·t)·(1-t)
      have hle2 : ((1 : Q') - Q'.ofNat (p + 1) * t)
          ≤ ((1 : Q') - Q'.ofNat p * t) * ((1 : Q') - t) :=
        Q'.le_trans' _ _ _ hle1 (Q'.ge_of_eqv hid)
      -- chain to qpow (1-t) (p+1)
      have : ((1 : Q') - Q'.ofNat (p + 1) * t) ≤ qpow ((1 : Q') - t) (p + 1) := by
        rw [← hqsucc]
        exact Q'.le_trans' _ _ _ hle2 hmul
      exact this

/-! ## 4. The satisfiability criterion `renormW^p ≥ w` -/

/-- `0 ≤ 1/p` (the surrogate step has nonnegative numerator). -/
theorem mkPos_one_p_nonneg (p : Nat) (hp : 0 < p) : (0 : Q') ≤ Q'.mkPos 1 p hp := by
  rw [Q'.zero_le_iff_num_nonneg, Q'.mkPos_num]
  decide

/-- `1/p ≤ 1` for `p ≥ 1` (cross-mult `1·1 ≤ 1·p`). -/
theorem mkPos_one_p_le_one (p : Nat) (hp : 0 < p) : Q'.mkPos 1 p hp ≤ (1 : Q') := by
  show (Q'.mkPos 1 p hp).num * (((1 : Q').den : Int)) ≤ ((1 : Q').num) * ((Q'.mkPos 1 p hp).den : Int)
  rw [Q'.mkPos_num, Q'.mkPos_den]
  show (1 : Int) * (1 : Int) ≤ (1 : Int) * (p : Int)
  rw [Int.one_mul, Int.one_mul]
  -- 1 ≤ p
  exact Int.ofNat_le.mpr hp

/-- `0 ≤ renormTauFix p hp w` on `w ≤ 1`. -/
theorem renormTauFix_nonneg {w : Q'} (hw1 : w ≤ (1 : Q')) (p : Nat) (hp : 0 < p) :
    (0 : Q') ≤ renormTauFix p hp w :=
  Q'.mul_nonneg _ _ (Q'.sub_nonneg_of_le hw1) (mkPos_one_p_nonneg p hp)

/-- `1 − w ≤ 1` on `0 ≤ w`. -/
theorem oneSub_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) : (1 : Q') - w ≤ (1 : Q') := by
  show (1 : Q') + -w ≤ (1 : Q')
  have hneg : (-w) ≤ (0 : Q') :=
    Q'.le_trans' _ _ _ (Q'.neg_le_neg hw0) (Q'.le_of_eqv (Q'.eqv_of_eq (by rfl)))
  have hstep : (1 : Q') + -w ≤ (1 : Q') + 0 :=
    Q'.add_le_add_left (1 : Q') (-w) 0 hneg
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (1 : Q'))))

/-- `renormTauFix p hp w ≤ 1` on `0 ≤ w ≤ 1`:  `(1−w)·(1/p) ≤ 1·(1/p) ≤ 1`. -/
theorem renormTauFix_le_one {w : Q'} (hw0 : (0 : Q') ≤ w) (p : Nat) (hp : 0 < p) :
    renormTauFix p hp w ≤ (1 : Q') := by
  -- (1-w)·(1/p) ≤ 1·(1/p) ≈ 1/p ≤ 1
  have h1 : ((1 : Q') - w) * Q'.mkPos 1 p hp ≤ (1 : Q') * Q'.mkPos 1 p hp :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ (oneSub_le_one hw0) (mkPos_one_p_nonneg p hp)
  have h2 : (1 : Q') * Q'.mkPos 1 p hp ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv (Q'.mkPos 1 p hp))) (mkPos_one_p_le_one p hp)
  exact Q'.le_trans' _ _ _ h1 h2

/-- `0 ≤ renormWFix p hp w` (from `renormTauFix ≤ 1`). -/
theorem renormWFix_nonneg {w : Q'} (hw0 : (0 : Q') ≤ w) (p : Nat) (hp : 0 < p) :
    (0 : Q') ≤ renormWFix p hp w :=
  Q'.sub_nonneg_of_le (renormTauFix_le_one hw0 p hp)

/-- `renormWFix p hp w ≤ 1` (from `renormTauFix ≥ 0`). -/
theorem renormWFix_le_one {w : Q'} (hw1 : w ≤ (1 : Q')) (p : Nat) (hp : 0 < p) :
    renormWFix p hp w ≤ (1 : Q') :=
  oneSub_le_one (renormTauFix_nonneg hw1 p hp)

/-- Product of positives is positive (local, mirrors the `Sqrt` engine). -/
theorem q_mul_pos {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) :
    (0 : Q') < a * b := by
  show (0 : Int) * ((a * b).den : Int) < (a * b).num * ((0 : Q').den : Int)
  have h0d : ((0 : Q').den : Int) = 1 := rfl
  rw [Int.zero_mul, h0d, Int.mul_one]
  exact Int.mul_pos (CReal.num_pos_of_pos ha) (CReal.num_pos_of_pos hb)

/-- `0 < 1/p`. -/
theorem mkPos_one_p_pos (p : Nat) (hp : 0 < p) : (0 : Q') < Q'.mkPos 1 p hp := by
  apply CReal.pos_of_num_pos
  have : (Q'.mkPos 1 p hp).num = (1 : Int) := Q'.mkPos_num 1 p hp
  rw [this]
  decide

/-- **`0 < renormTauFix p hp w`** for `w < 1` — the gap margin is strictly positive. -/
theorem renormTauFix_pos {w : Q'} (hw1 : w < (1 : Q')) (p : Nat) (hp : 0 < p) :
    (0 : Q') < renormTauFix p hp w :=
  q_mul_pos (ProductFloor.oneSubR_pos w hw1) (mkPos_one_p_pos p hp)

/-- **`renormWFix p hp w < 1`** for `w < 1` (since `renormTauFix > 0`). -/
theorem renormWFix_lt_one {w : Q'} (hw1 : w < (1 : Q')) (p : Nat) (hp : 0 < p) :
    renormWFix p hp w < (1 : Q') := by
  -- renormWFix = 1 - τ ; goal (1-τ).num < (1-τ).den  ⇐  0 < τ.num
  have hτpos : (0 : Q') < renormTauFix p hp w := renormTauFix_pos hw1 p hp
  have hτnum : (0 : Int) < (renormTauFix p hp w).num := CReal.num_pos_of_pos hτpos
  show (renormWFix p hp w).num * (((1 : Q').den : Int))
     < ((1 : Q').num) * ((renormWFix p hp w).den : Int)
  have hn : (1 : Q').num = 1 := rfl
  have hd : ((1 : Q').den : Int) = 1 := rfl
  rw [hn, hd, Int.mul_one, Int.one_mul]
  -- renormWFix = 1 - τ ;  (1-τ).num = τ.den - τ.num ,  (1-τ).den = τ.den
  show ((1 : Q') - renormTauFix p hp w).num
     < (((1 : Q') - renormTauFix p hp w).den : Int)
  have enum : ((1 : Q') - renormTauFix p hp w).num
      = ((renormTauFix p hp w).den : Int) + (-(renormTauFix p hp w).num) := by
    show ((1 : Q').num * ((-(renormTauFix p hp w)).den : Int)
          + (-(renormTauFix p hp w)).num * ((1 : Q').den : Int))
       = ((renormTauFix p hp w).den : Int) + (-(renormTauFix p hp w).num)
    rw [hn, hd, Int.one_mul, Int.mul_one]
    rfl
  have eden : (((1 : Q') - renormTauFix p hp w).den : Int)
      = ((renormTauFix p hp w).den : Int) := by
    show ((((1 : Q').den * (-(renormTauFix p hp w)).den - 1) + 1 : Nat) : Int)
       = ((renormTauFix p hp w).den : Int)
    have e1 : (-(renormTauFix p hp w)).den = (renormTauFix p hp w).den := rfl
    rw [e1]
    have e2 : (1 : Q').den = 1 := rfl
    rw [e2]
    have hdpos : 0 < (renormTauFix p hp w).den := Q'.den_pos _
    have : (1 * (renormTauFix p hp w).den - 1) + 1 = (renormTauFix p hp w).den := by omega
    rw [this]
  rw [enum, eden]
  -- τ.den + (-τ.num) < τ.den  ⇐  0 < τ.num
  omega

/-! ## 5. The satisfiability criterion `w ≤ renormW^p`  (THE NEW CONTENT) -/

/-- `ofNat p · renormTauFix p hp w ≃ 1 − w`  (the `p`-scaled shift collapses the
`1/p`):  `ofNat p · ((1−w)·(1/p)) ≃ (1−w)·(ofNat p · (1/p)) ≃ (1−w)·1 ≃ 1−w`. -/
theorem ofNat_mul_renormTauFix (p : Nat) (hp : 0 < p) (w : Q') :
    (Q'.ofNat p * renormTauFix p hp w) ≈ ((1 : Q') - w) := by
  show (Q'.ofNat p * (((1 : Q') - w) * Q'.mkPos 1 p hp)) ≈ ((1 : Q') - w)
  -- p·((1−w)·(1/p)) ≈ ((1−w)·(1/p))·p  ≈ (1−w)·((1/p)·p) ≈ (1−w)·(p·(1/p)) ≈ (1−w)·1 ≈ 1−w
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv (Q'.ofNat p) (((1 : Q') - w) * Q'.mkPos 1 p hp)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv ((1 : Q') - w) (Q'.mkPos 1 p hp) (Q'.ofNat p)) ?_
  -- (1−w)·((1/p)·p) ; rewrite inner to p·(1/p) ≈ 1
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left ((1 : Q') - w) _ _
      (Q'.mul_comm_eqv (Q'.mkPos 1 p hp) (Q'.ofNat p))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left ((1 : Q') - w) _ _ (ofNat_mul_mkPos_one p hp)) ?_
  exact Q'.mul_one_eqv ((1 : Q') - w)

/-- **THE SATISFIABILITY CRITERION** `w ≤ renormWFix p hp w ^ p`.  The corrected
retune decays slowly enough to dominate the equal-split fusion channel.  PROOF:
Bernoulli at `t = renormTauFix` gives `1 − p·t ≤ (1 − t)^p = renormW^p`; and
`1 − p·t ≃ 1 − (1 − w) ≃ w`. -/
theorem renormWFix_pow_ge_w (p : Nat) (hp : 0 < p) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) :
    w ≤ qpow (renormWFix p hp w) p := by
  -- Bernoulli at t := renormTauFix p hp w
  have ht0 : (0 : Q') ≤ renormTauFix p hp w := renormTauFix_nonneg hw1 p hp
  have ht1 : renormTauFix p hp w ≤ (1 : Q') := renormTauFix_le_one hw0 p hp
  have hbern : (1 : Q') - Q'.ofNat p * renormTauFix p hp w
      ≤ qpow ((1 : Q') - renormTauFix p hp w) p :=
    bernoulli_oneSub (renormTauFix p hp w) ht0 ht1 p
  -- (1 - renormTauFix) = renormWFix definitionally
  have hbern' : (1 : Q') - Q'.ofNat p * renormTauFix p hp w
      ≤ qpow (renormWFix p hp w) p := hbern
  -- w ≈ 1 - ofNat p · renormTauFix
  have hweq : w ≈ ((1 : Q') - Q'.ofNat p * renormTauFix p hp w) := by
    -- 1 - ofNat p · renormTauFix ≈ 1 - (1-w) ≈ w
    have h1 : ((1 : Q') - Q'.ofNat p * renormTauFix p hp w)
        ≈ ((1 : Q') - ((1 : Q') - w)) := by
      show ((1 : Q') + -(Q'.ofNat p * renormTauFix p hp w))
        ≈ ((1 : Q') + -((1 : Q') - w))
      exact Q'.add_eqv_congr_left (1 : Q') _ _
        (Q'.neg_eqv_congr _ _ (ofNat_mul_renormTauFix p hp w))
    -- 1 - (1 - w) ≈ w
    have h2 : ((1 : Q') - ((1 : Q') - w)) ≈ w := by
      -- 1 + -(1 + -w) ≈ 1 + (-1 + w) ≈ (1 + -1) + w ≈ 0 + w ≈ w
      show ((1 : Q') + -((1 : Q') + (-w))) ≈ w
      have ha : (-((1 : Q') + (-w))) ≈ ((-1 : Q') + w) := by
        refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (1 : Q') (-w)) ?_
        exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv w)
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (1 : Q') _ _ ha) ?_
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-1) w)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ w (Q'.add_neg_self_eqv (1 : Q'))) ?_
      exact q_zero_add_eqv w
    exact Q'.eqv_symm (Q'.eqv_trans _ _ _ h1 h2)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hweq) hbern'

/-! ## 6. Per-mode decay control — `K_τ` dominates the slow fusion channel -/

/-- **The per-mode decay domination** `w^n ≤ renormW^{p·n}`.  The corrected retune
decays slowly enough: the `p·n`-th power of `renormW` dominates the `n`-th power of
`w`.  PROOF: `qpow_mono` on `w ≤ renormW^p` (satisfiability criterion) gives
`w^n ≤ (renormW^p)^n`; then `(renormW^p)^n ≃ renormW^{p·n}` (`qpow_qpow`). -/
theorem renormWFix_decay_dom (p : Nat) (hp : 0 < p) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (n : Nat) :
    qpow w n ≤ qpow (renormWFix p hp w) (p * n) := by
  -- w ≤ renormW^p
  have hbase : w ≤ qpow (renormWFix p hp w) p := renormWFix_pow_ge_w p hp w hw0 hw1
  -- w^n ≤ (renormW^p)^n
  have hmono : qpow w n ≤ qpow (qpow (renormWFix p hp w) p) n :=
    qpow_mono hw0 hbase n
  -- (renormW^p)^n ≃ renormW^{p·n}
  have hpp : (qpow (qpow (renormWFix p hp w) p) n) ≈ (qpow (renormWFix p hp w) (p * n)) :=
    qpow_qpow (renormWFix p hp w) p n
  exact Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv hpp)

/-! ## 7. The re-derived all-`s` quadratic per-mode bound AT THE CORRECTED BASE -/

/-- **The per-mode renormalized transverse defect at the corrected base.**  Same shape
as `FullModeQuadratic.modeDefect` but with base `renormWFix p hp w`:

    δ_s^fix(p,w) = dimQ s · ( C₄(s)·(1 − renormW) − (1 − renormW^{C₄(s)}) ). -/
def modeDefectFix (p : Nat) (hp : 0 < p) (w : Q') (s : Nat) : Q' :=
  dimQ s * ((Q'.ofNat (c4 s) * ((1 : Q') - renormWFix p hp w))
    - ((1 : Q') - qpow (renormWFix p hp w) (c4 s)))

/-- **THE RE-DERIVED ALL-`s` QUADRATIC BOUND AT THE CORRECTED BASE.**  On `0 ≤ w ≤ 1`,
for EVERY mode `s`,

    modeDefectFix p hp w s
      ≤ dimQ s · ( C₄(s)² · ((1 − renormW)·(1 − renormW)) ),

i.e. the per-mode renormalized residual at the corrected base `renormWFix p hp w` is
QUADRATIC in `1 − renormW` with explicit Casimir polynomial `C₄(s)²`.  PROOF mirrors
`FullModeQuadratic.modeDefect_quadratic`: `secondOrder_qpow` at base `renormWFix p hp w`
(needs `0 ≤ renormWFix ≤ 1`) and `n = C₄(s)`, scaled by `dimQ s ≥ 0`. -/
theorem modeDefectFix_quadratic (p : Nat) (hp : 0 < p) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat) :
    modeDefectFix p hp w s
      ≤ dimQ s * ((Q'.ofNat (c4 s) * Q'.ofNat (c4 s))
          * (((1 : Q') - renormWFix p hp w) * ((1 : Q') - renormWFix p hp w))) := by
  have hb0 : (0 : Q') ≤ renormWFix p hp w := renormWFix_nonneg hw0 p hp
  have hb1 : renormWFix p hp w ≤ (1 : Q') := renormWFix_le_one hw1 p hp
  -- inner bracket: the second-order overshoot at n = C₄(s), base renormWFix
  have hquad :
      (Q'.ofNat (c4 s) * ((1 : Q') - renormWFix p hp w))
        - ((1 : Q') - qpow (renormWFix p hp w) (c4 s))
      ≤ (Q'.ofNat (c4 s) * Q'.ofNat (c4 s))
          * (((1 : Q') - renormWFix p hp w) * ((1 : Q') - renormWFix p hp w)) :=
    secondOrder_qpow hb0 hb1 (c4 s)
  -- scale by dimQ s ≥ 0 on the left
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hquad (dimQ_nonneg s)

/-- **The quadratic margin form.**  Since `1 − renormWFix = renormTauFix = (1 − w)/p`,
the per-mode bound is `dimQ s · C₄(s)² · renormTauFix²`. -/
theorem modeDefectFix_quadratic_margin (p : Nat) (hp : 0 < p) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (s : Nat) :
    modeDefectFix p hp w s
      ≤ dimQ s * ((Q'.ofNat (c4 s) * Q'.ofNat (c4 s))
          * (renormTauFix p hp w * renormTauFix p hp w)) := by
  -- 1 − renormWFix = 1 − (1 − τ) ≃ τ = renormTauFix
  have hmargin : ((1 : Q') - renormWFix p hp w) ≈ renormTauFix p hp w := by
    -- 1 - (1 - τ) ≈ τ   (same chain as `1 - (1 - w) ≈ w`)
    show ((1 : Q') + -((1 : Q') + (-(renormTauFix p hp w)))) ≈ renormTauFix p hp w
    have ha : (-((1 : Q') + (-(renormTauFix p hp w)))) ≈ ((-1 : Q') + renormTauFix p hp w) := by
      refine Q'.eqv_trans _ _ _ (Q'.neg_add_eqv (1 : Q') (-(renormTauFix p hp w))) ?_
      exact Q'.add_eqv_congr_left _ _ _ (Q'.neg_neg_eqv (renormTauFix p hp w))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left (1 : Q') _ _ ha) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv (1 : Q') (-1) (renormTauFix p hp w))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (renormTauFix p hp w) (Q'.add_neg_self_eqv (1 : Q'))) ?_
    exact q_zero_add_eqv (renormTauFix p hp w)
  -- rewrite the RHS of modeDefectFix_quadratic via hmargin
  refine Q'.le_trans' _ _ _ (modeDefectFix_quadratic p hp w hw0 hw1 s) ?_
  refine Q'.le_of_eqv ?_
  -- dimQ s · (C² · ((1-rW)·(1-rW))) ≈ dimQ s · (C² · (τ·τ))
  refine Q'.mul_eqv_congr_left (dimQ s) _ _ ?_
  refine Q'.mul_eqv_congr_left (Q'.ofNat (c4 s) * Q'.ofNat (c4 s)) _ _ ?_
  -- (1-rW)·(1-rW) ≈ τ·(1-rW) ≈ τ·τ
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ ((1 : Q') - renormWFix p hp w) hmargin) ?_
  exact Q'.mul_eqv_congr_left (renormTauFix p hp w) _ _ hmargin

end YMGap.Continuum.BondMovingRetuneFix

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BondMovingRetuneFix.ofNat_mul_mkPos_one
#print axioms YMGap.Continuum.BondMovingRetuneFix.oneSub_mul_oneSub
#print axioms YMGap.Continuum.BondMovingRetuneFix.ofNat_succ_mul
#print axioms YMGap.Continuum.BondMovingRetuneFix.bernoulli_oneSub
#print axioms YMGap.Continuum.BondMovingRetuneFix.mkPos_one_p_nonneg
#print axioms YMGap.Continuum.BondMovingRetuneFix.mkPos_one_p_le_one
#print axioms YMGap.Continuum.BondMovingRetuneFix.renormTauFix_nonneg
#print axioms YMGap.Continuum.BondMovingRetuneFix.oneSub_le_one
#print axioms YMGap.Continuum.BondMovingRetuneFix.renormTauFix_le_one
#print axioms YMGap.Continuum.BondMovingRetuneFix.renormWFix_nonneg
#print axioms YMGap.Continuum.BondMovingRetuneFix.renormWFix_le_one
#print axioms YMGap.Continuum.BondMovingRetuneFix.q_mul_pos
#print axioms YMGap.Continuum.BondMovingRetuneFix.mkPos_one_p_pos
#print axioms YMGap.Continuum.BondMovingRetuneFix.renormTauFix_pos
#print axioms YMGap.Continuum.BondMovingRetuneFix.renormWFix_lt_one
#print axioms YMGap.Continuum.BondMovingRetuneFix.ofNat_mul_renormTauFix
#print axioms YMGap.Continuum.BondMovingRetuneFix.renormWFix_pow_ge_w
#print axioms YMGap.Continuum.BondMovingRetuneFix.renormWFix_decay_dom
#print axioms YMGap.Continuum.BondMovingRetuneFix.modeDefectFix_quadratic
#print axioms YMGap.Continuum.BondMovingRetuneFix.modeDefectFix_quadratic_margin
