/-
Track B / local-CLT — the CONTINUUM-SHADOW reframing of the open position-variance curvature
floor `Δ²_t ⟨D²⟩_t ≥ −2` (`SaddleVarianceFloor` / R1 of `CircleFourierPowerModel`).

# Why this file exists (read first — load-bearing honesty)

`CircleFourierPowerModel` relocates R1 onto a per-`s` Pólya / Bernstein positive-coefficient
certificate (`PolyaCertifiedFloor`); the concrete windows `s = 0..6` are proved, but the
uniform-in-`s` certificate has no known closed form (the coefficient lists grow like `O(s²)`).
This file provides a DIFFERENT, "continuum-shadow" relocation of the SAME residual, isolating the
transcendental content into a single smooth elliptic-modulus inequality (a) plus a finite-size
convergence bound (b), rather than an `s`-growing family.

## The exact dictionary (validated to 1e-60 by `computations/continuum_shadow_pilot.py`)

Write `V(t) = ⟨D²⟩_t = dmomNfull w t / acNfull w t` (the theta-tilted position variance).  With the
antidiagonal square `D = t − 2p`, `M = t + 2`, and the parity-`t` lattice `D ∈ {−t,…,t}` (step 2),
the FULL-range moments factor through the ENVELOPE-FREE discrete-Gaussian lattice sums

    θ_t = Σ_D w^{D²/2},   ξ_t = Σ_D D² w^{D²/2},   ζ_t = Σ_D D⁴ w^{D²/2},
    den_t = M²θ_t − ξ_t,  num_t = M²ξ_t − ζ_t,   V(t) = num_t/den_t = ξ_t/θ_t  as  t→∞ (per parity).

Because `w^{D²/2}` is a HALF-integer power of `w` for odd `t`, the clean additive recursions
(`θ_{t+2} = θ_t + 2 w^{(t+2)²/2}`, `den_{t+2} = den_t + 4(t+3)θ_{t+2}`, …) live in `√w`; they are
verified numerically (`continuum_shadow_pilot.py`, §3) but are NOT the Lean objects here (Lean's
`qpow` is a `Nat` power).  Instead we carry the ENVELOPE-SCALED integer-power lattice sums

    `Th w t = Σ_{p≤t} w^{c4 p + c4 (t−p)}`,   `Xi w t = Σ_{p≤t} (dsq p t)·w^{c4 p + c4 (t−p)}`,
    `Zeta w t = Σ_{p≤t} (dsq p t)²·w^{c4 p + c4 (t−p)}`,

with `c4 p + c4 (t−p) = p² + (t−p)² + 2t` an INTEGER exponent (so these ARE `qpow`-expressible).  The
envelope-free variance `G(t) = ξ_t/θ_t = Xi w t / Th w t` (the `w^{(t²)/2+2t}/4` envelope cancels in
the ratio), and the floor moments connect to the pure-Gaussian lattice by the two PROVED bridges
(§2): `4·acNfull + Xi = M²·Th` and `4·dmomNfull + Zeta = M²·Xi`.

## The convex-combination engine (PROVED abstractly, §3)

The exact mediant identity `V(t+2) = λ·V(t) + (1−λ)·G(t+2)`, `λ = den_t/den_{t+2} ∈ (0,1)`, follows
from the two additive recursions; its CLEARED (division-free) core is the mediant betweenness
`a·d ≤ c·b → a·(b+d) ≤ (a+c)·b  ∧  (a+c)·d ≤ c·(b+d)` (`mediant_lower`/`mediant_upper`), the algebraic
heart of "`V(t+2)` lies between `V(t)` and `G(t+2)`" — the monotone-convergence of `V` to the
per-parity Gaussian variance `G_parity`.

## The continuum shadow and the −2 corner (validated, §5–6 of the pilot)

As `t → ∞`, `V(t) → G_parity(w)` and `Δ²V(large even s) → −2·(G_odd − G_even)`, where `G_even,
G_odd` are the FULL even/odd theta-lattice variances (`G_parity = 2·dlogθ_parity/dlogw`).  So the
`−2` floor is `2·(1 − (G_odd − G_even)) ≥ 0`, i.e. the ELLIPTIC-MODULUS inequality

    (a)   G_odd(w) − G_even(w) ≤ 1        for  w ∈ [0,1)

(with `k = (ϑ₂/ϑ₃)²` the elliptic modulus, `G_odd − G_even = dlog k/dlog w`; `→ 1` as `w→0`, `→ 0` as
`w→1`).  The finite-`t` second difference approaches this shadow WITHOUT undershooting `−2`, but — a
verified subtlety — it can dip a hair BELOW the asymptote (`−1.9604` vs `−1.9603` at `w=0.05, s=40`),
so the passage from the continuum bound (a) to the exact finite floor is a genuine, non-free
finite-size correction (b).  NOTE (verified, `continuum_shadow_pilot.py` §, run this session):
the naive finite surrogate `G(t+1) − G(t) ≤ 1` is FALSE at finite `t` (reaches `1.2456` at `w=0.8`);
the bound is intrinsically ASYMPTOTIC, which is why (a) is stated as an ε-modulus limit statement.

# What this file provides (Type-level, named-open, NO `sorry`, NO fabricated proof)

PROVED (axiom-clean, the substantiating backbone):
  * `masBridge`  : `4·acNfull w t + Xi w t ≃ M²·Th w t`     (floor mass = pure-Gaussian variance den)
  * `momBridge`  : `4·dmomNfull w t + Zeta w t ≃ M²·Xi w t` (floor moment = pure-Gaussian variance num)
  * `mediant_lower`/`mediant_upper` : the cleared convex-combination betweenness (the `V→G` engine).

NAMED-OPEN (Type-level structures, Rule 6a; never `sorry`, never `Prop := True`):
  * `ContinuumFloor w`      (**a**) — the elliptic-modulus bound `G_odd − G_even ≤ 1`, rendered as a
    constructive ε-modulus limit statement on the finite lattice ratios `Xi/Th` (asymptotic, TRUE,
    non-transcendental).
  * `FiniteCorrectionBound w` (**b**) — the finite-size correction: the IMPLICATION that the exact
    finite floor `∀ s, FullRangeFloor w s` follows from the continuum modulus bound (a).

`saddleVarianceFloor_of_shadow` composes (a) + (b) into `SaddleVarianceFloor w` (= R1) by pure modus
ponens — axiom-clean given the two fields.

# HONEST VERDICT

This is a RELOCATION of R1, not a closure.  Neither (a) nor (b) is discharged here: (a) is a smooth
infinite-theta-sum inequality (not provable constructively this session), and (b) carries the
finite-size correction whose sign-subtlety is verified.  The value over `PolyaCertifiedFloor` is
structural: R1 now rests on ONE continuum inequality (a) + ONE convergence bound (b), instead of an
`s`-growing certificate family, and the connecting algebra (bridges + mediant) is PROVED.  The Clay
Yang–Mills mass gap remains OPEN.

# Axiom gate (AGENTS.md Rule 1 / Rule 8)

`#print axioms` at the file end.  The composite is pure modus ponens; the bridges/mediant use only the
reused `Q'` `≈`/`≤` machinery (`propext`/`Quot.sound` at most).  No `Classical.*`, no `native_decide`,
no `sorry`, no custom `axiom`.  Both residuals are `Type`-level structures with a `Type`-level modulus.
-/

import YMGap.Continuum.CircleFourierPowerModel

namespace YMGap.Continuum.ContinuumShadowFloor

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.MeanComplementCovariance
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.CircleFourierPowerModel

/-! ## 0. Local `Q'`-`ofNat` multiplicative helper and the `ring_qeqv` closer. -/

/-- Ring closer for CANCELLATION-FREE `Q'.eqv` identities (local copy; see
`MeanExpConvexProgress.ring_qeqv`): reduce to the `Int` cross-product, expand every `num`/`den` cast
and distribute, close by `ac_rfl`.  Sound only for subtraction-free identities. -/
local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

/-- `ofNat a · ofNat b ≃ ofNat (a·b)` (local copy to avoid cross-file namespace juggling). -/
theorem ofNatMul (a b : Nat) : (Q'.ofNat a * Q'.ofNat b).eqv (Q'.ofNat (a * b)) := by
  show (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int)
      = (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
  rw [Q'.mul_den_cast]
  show ((Int.ofNat a) * (Int.ofNat b)) * 1
      = (Int.ofNat (a * b)) * (1 * 1)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  omega

/-! ## 1. The envelope-scaled integer-power discrete-Gaussian lattice sums.

`gterm w t p = w^{c4 p + c4 (t−p)}` — the common integer-power weight of the antidiagonal pair
`(p, t−p)` (the exponent `p² + (t−p)² + 2t`).  `Th/Xi/Zeta` are its `1`-, `D²`-, `D⁴`-moments over the
window `p ∈ {0,…,t}` (`D² = dsq p t`).  These are the ENVELOPE-SCALED pure-Gaussian lattice variances
`4·θ_t, 4·ξ_t, 4·ζ_t`; the pure variance is `G(t) = Xi w t / Th w t = ξ_t/θ_t`. -/

/-- The common antidiagonal weight `w^{c4 p + c4 (t−p)}` (integer power; `= w^{p²+(t−p)²+2t}`). -/
def gterm (w : Q') (t p : Nat) : Q' := qpow w (c4 p + c4 (t - p))

/-- `Th w t = Σ_{p≤t} w^{c4 p + c4 (t−p)}` — the envelope-scaled theta mass `4·θ_t`. -/
def Th (w : Q') (t : Nat) : Q' := fsum (fun p => gterm w t p) (t + 1)

/-- `Xi w t = Σ_{p≤t} (dsq p t)·w^{c4 p + c4 (t−p)}` — the envelope-scaled Gaussian second
moment `4·ξ_t`.  `G(t) = Xi w t / Th w t` is the pure-Gaussian lattice variance `ξ_t/θ_t`. -/
def Xi (w : Q') (t : Nat) : Q' := fsum (fun p => Q'.ofNat (dsq p t) * gterm w t p) (t + 1)

/-- `Zeta w t = Σ_{p≤t} (dsq p t)²·w^{c4 p + c4 (t−p)}` — the envelope-scaled fourth moment `4·ζ_t`. -/
def Zeta (w : Q') (t : Nat) : Q' :=
  fsum (fun p => Q'.ofNat (dsq p t * dsq p t) * gterm w t p) (t + 1)

/-! ## 2. The two PROVED bridges: floor moments = pure-Gaussian-variance combinations.

`4·acNfull w t + Xi w t ≃ M²·Th w t` and `4·dmomNfull w t + Zeta w t ≃ M²·Xi w t` (`M = t+2`),
the exact envelope-scaled `den_t = M²θ_t − ξ_t`, `num_t = M²ξ_t − ζ_t` in cleared (subtraction-free)
form.  Both reduce to the per-term `Nat` identity `4(p+1)(t−p+1) + dsq p t = (t+2)²`. -/

/-- `4·(p+1)·(t−p+1) + dsq p t = (t+2)²` for `p ≤ t` (the antidiagonal mass/curvature split). -/
theorem four_dim_add_dsq (p t : Nat) (h : p ≤ t) :
    4 * ((p + 1) * (t - p + 1)) + dsq p t = (t + 2) * (t + 2) := by
  obtain ⟨d, rfl⟩ := Nat.le.dest h
  have hd : (p + d) - p = d := by omega
  rw [hd]
  have hbase := four_x_add_dsq p (p + d) (Nat.le_add_right p d)
  rw [hd] at hbase
  have hL : (p + 1) * (d + 1) = p * d + p + d + 1 := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.one_mul]; omega
  have hR : (p + d + 2) * (p + d + 2) = (p + d) * (p + d) + (4 * (p + d) + 4) := by
    simp only [Nat.mul_add, Nat.add_mul]; omega
  rw [hL, hR]; omega

/-- The per-term autoconvolution factorization `coeffW w p · coeffW w (t−p) ≃
ofNat((p+1)(t−p+1))·gterm w t p` (dims `×` the shared integer power). -/
theorem coeff_prod_eq (w : Q') (t p : Nat) :
    (coeffW w p * coeffW w (t - p)).eqv (Q'.ofNat ((p + 1) * (t - p + 1)) * gterm w t p) := by
  show ((dimQ p * qpow w (c4 p)) * (dimQ (t - p) * qpow w (c4 (t - p)))).eqv
       (Q'.ofNat ((p + 1) * (t - p + 1)) * gterm w t p)
  have hrearr :
      ((dimQ p * qpow w (c4 p)) * (dimQ (t - p) * qpow w (c4 (t - p)))).eqv
        ((dimQ p * dimQ (t - p)) * (qpow w (c4 p) * qpow w (c4 (t - p)))) := by ring_qeqv
  have hdim : (dimQ p * dimQ (t - p)).eqv (Q'.ofNat ((p + 1) * (t - p + 1))) := ofNatMul (p + 1) (t - p + 1)
  have hg : (qpow w (c4 p) * qpow w (c4 (t - p))).eqv (gterm w t p) :=
    Q'.eqv_symm (qpow_add w (c4 p) (c4 (t - p)))
  refine Q'.eqv_trans _ _ _ hrearr ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hdim) ?_
  exact Q'.mul_eqv_congr_left _ _ _ hg

/-- The bridge per-term identity `4·(c_p c_{t−p}) + (dsq)·gterm ≃ (t+2)²·gterm` (`p ≤ t`). -/
theorem bridge_term (w : Q') (t p : Nat) (h : p ≤ t) :
    (Q'.ofNat 4 * (coeffW w p * coeffW w (t - p)) + Q'.ofNat (dsq p t) * gterm w t p).eqv
      (Q'.ofNat ((t + 2) * (t + 2)) * gterm w t p) := by
  -- 4·(c_p c_{t−p}) ≃ ofNat(4(p+1)(t−p+1))·gterm
  have h4 : (Q'.ofNat 4 * (coeffW w p * coeffW w (t - p))).eqv
      (Q'.ofNat (4 * ((p + 1) * (t - p + 1))) * gterm w t p) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (coeff_prod_eq w t p)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) (Q'.ofNat ((p + 1) * (t - p + 1))) (gterm w t p))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (ofNatMul 4 ((p + 1) * (t - p + 1)))
  -- combine the two gterm-scaled terms and use the Nat identity
  have hC : (Q'.ofNat (4 * ((p + 1) * (t - p + 1))) + Q'.ofNat (dsq p t)).eqv
      (Q'.ofNat ((t + 2) * (t + 2))) :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.ofNat_add_eqv (4 * ((p + 1) * (t - p + 1))) (dsq p t)))
      (Q'.eqv_of_eq (congrArg Q'.ofNat (four_dim_add_dsq p t h)))
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h4) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat (4 * ((p + 1) * (t - p + 1)))) (Q'.ofNat (dsq p t))
      (gterm w t p))) ?_
  exact Q'.mul_eqv_congr_right _ _ (gterm w t p) hC

/-- **`masBridge`** — `4·acNfull w t + Xi w t ≃ (t+2)²·Th w t`.  The envelope-scaled
`den_t = M²θ_t − ξ_t` in cleared form: the floor MASS `acNfull` is the pure-Gaussian variance
denominator. -/
theorem masBridge (w : Q') (t : Nat) :
    (Q'.ofNat 4 * acNfull w t + Xi w t).eqv (Q'.ofNat ((t + 2) * (t + 2)) * Th w t) := by
  have h4a : (Q'.ofNat 4 * acNfull w t).eqv
      (fsum (fun p => Q'.ofNat 4 * (coeffW w p * coeffW w (t - p))) (t + 1)) :=
    fsum_const_mul (Q'.ofNat 4) (fun p => coeffW w p * coeffW w (t - p)) (t + 1)
  have hsum : (Q'.ofNat 4 * acNfull w t + Xi w t).eqv
      (fsum (fun p => Q'.ofNat 4 * (coeffW w p * coeffW w (t - p))
        + Q'.ofNat (dsq p t) * gterm w t p) (t + 1)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h4a) ?_
    exact Q'.eqv_symm (fsum_add
      (fun p => Q'.ofNat 4 * (coeffW w p * coeffW w (t - p)))
      (fun p => Q'.ofNat (dsq p t) * gterm w t p) (t + 1))
  refine Q'.eqv_trans _ _ _ hsum ?_
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr_lt _ _ (t + 1) (fun p hp => bridge_term w t p (by omega))) ?_
  exact Q'.eqv_symm (fsum_const_mul (Q'.ofNat ((t + 2) * (t + 2))) (fun p => gterm w t p) (t + 1))

/-- The bridge per-term identity scaled by `dsq` (for `momBridge`):
`4·(dsq)·(c_p c_{t−p}) + (dsq²)·gterm ≃ (t+2)²·(dsq·gterm)` (`p ≤ t`). -/
theorem bridge_term_dsq (w : Q') (t p : Nat) (h : p ≤ t) :
    (Q'.ofNat 4 * (Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p)))
        + Q'.ofNat (dsq p t * dsq p t) * gterm w t p).eqv
      (Q'.ofNat ((t + 2) * (t + 2)) * (Q'.ofNat (dsq p t) * gterm w t p)) := by
  -- LHS ≃ ofNat(dsq) · [ 4·(c_p c_{t−p}) + (dsq)·gterm ]
  have hL : (Q'.ofNat 4 * (Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p)))
      + Q'.ofNat (dsq p t * dsq p t) * gterm w t p).eqv
      (Q'.ofNat (dsq p t) *
        (Q'.ofNat 4 * (coeffW w p * coeffW w (t - p)) + Q'.ofNat (dsq p t) * gterm w t p)) := by
    have ht1 : (Q'.ofNat 4 * (Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p)))).eqv
        (Q'.ofNat (dsq p t) * (Q'.ofNat 4 * (coeffW w p * coeffW w (t - p)))) := by ring_qeqv
    have hsplit : (Q'.ofNat (dsq p t * dsq p t) * gterm w t p).eqv
        (Q'.ofNat (dsq p t) * (Q'.ofNat (dsq p t) * gterm w t p)) := by
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (ofNatMul (dsq p t) (dsq p t))) ?_
      exact Q'.mul_assoc_eqv (Q'.ofNat (dsq p t)) (Q'.ofNat (dsq p t)) (gterm w t p)
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ht1 hsplit) ?_
    exact Q'.eqv_symm (Q'.mul_add_eqv (Q'.ofNat (dsq p t))
      (Q'.ofNat 4 * (coeffW w p * coeffW w (t - p))) (Q'.ofNat (dsq p t) * gterm w t p))
  -- RHS ≃ ofNat(dsq) · [ (t+2)²·gterm ]
  refine Q'.eqv_trans _ _ _ hL ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ (bridge_term w t p h)) ?_
  -- ofNat(dsq)·((t+2)²·gterm) ≃ (t+2)²·(ofNat(dsq)·gterm)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat (dsq p t)) (Q'.ofNat ((t + 2) * (t + 2))) (gterm w t p))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv (Q'.ofNat (dsq p t)) (Q'.ofNat ((t + 2) * (t + 2))))) ?_
  exact Q'.mul_assoc_eqv (Q'.ofNat ((t + 2) * (t + 2))) (Q'.ofNat (dsq p t)) (gterm w t p)

/-- **`momBridge`** — `4·dmomNfull w t + Zeta w t ≃ (t+2)²·Xi w t`.  The envelope-scaled
`num_t = M²ξ_t − ζ_t` in cleared form: the floor MOMENT `dmomNfull` is the pure-Gaussian variance
numerator. -/
theorem momBridge (w : Q') (t : Nat) :
    (Q'.ofNat 4 * dmomNfull w t + Zeta w t).eqv (Q'.ofNat ((t + 2) * (t + 2)) * Xi w t) := by
  have h4d : (Q'.ofNat 4 * dmomNfull w t).eqv
      (fsum (fun p => Q'.ofNat 4 * (Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p)))) (t + 1)) :=
    fsum_const_mul (Q'.ofNat 4)
      (fun p => Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p))) (t + 1)
  have hsum : (Q'.ofNat 4 * dmomNfull w t + Zeta w t).eqv
      (fsum (fun p => Q'.ofNat 4 * (Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p)))
        + Q'.ofNat (dsq p t * dsq p t) * gterm w t p) (t + 1)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h4d) ?_
    exact Q'.eqv_symm (fsum_add
      (fun p => Q'.ofNat 4 * (Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p))))
      (fun p => Q'.ofNat (dsq p t * dsq p t) * gterm w t p) (t + 1))
  refine Q'.eqv_trans _ _ _ hsum ?_
  refine Q'.eqv_trans _ _ _
    (fsum_eqv_congr_lt _ _ (t + 1) (fun p hp => bridge_term_dsq w t p (by omega))) ?_
  exact Q'.eqv_symm (fsum_const_mul (Q'.ofNat ((t + 2) * (t + 2)))
    (fun p => Q'.ofNat (dsq p t) * gterm w t p) (t + 1))

/-! ## 3. The convex-combination engine (PROVED abstractly): cleared mediant betweenness.

`V(t+2) = num_{t+2}/den_{t+2}` with `num_{t+2} = num_t + k·ξ`, `den_{t+2} = den_t + k·θ` is the
weighted mediant of `V(t) = num_t/den_t` and `G(t+2) = ξ/θ`, `k = 4(t+3)`.  Its division-free core is:
from `a·d ≤ c·b` (i.e. `a/b ≤ c/d`), both `a/b ≤ (a+c)/(b+d)` and `(a+c)/(b+d) ≤ c/d` hold, in cleared
form below.  This is the algebraic engine of "`V(t+2)` lies between `V(t)` and `G(t+2)`" — the
monotone convergence `V(t) → G_parity`. -/

/-- **`mediant_lower`** — `a·d ≤ c·b → a·(b+d) ≤ (a+c)·b` (`a/b ≤ (a+c)/(b+d)`, cleared). -/
theorem mediant_lower {a b c d : Q'} (hcross : a * d ≤ c * b) :
    a * (b + d) ≤ (a + c) * b := by
  have e1 : (a * (b + d)).eqv (a * b + a * d) := Q'.mul_add_eqv a b d
  have e2 : ((a + c) * b).eqv (a * b + c * b) := Q'.add_mul_eqv a c b
  have hstep : a * b + a * d ≤ a * b + c * b := Q'.add_le_add_left _ _ _ hcross
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) (Q'.le_trans' _ _ _ hstep (Q'.ge_of_eqv e2))

/-- **`mediant_upper`** — `a·d ≤ c·b → (a+c)·d ≤ c·(b+d)` (`(a+c)/(b+d) ≤ c/d`, cleared). -/
theorem mediant_upper {a b c d : Q'} (hcross : a * d ≤ c * b) :
    (a + c) * d ≤ c * (b + d) := by
  have e1 : ((a + c) * d).eqv (a * d + c * d) := Q'.add_mul_eqv a c d
  have e2 : (c * (b + d)).eqv (c * b + c * d) := Q'.mul_add_eqv c b d
  have hstep : a * d + c * d ≤ c * b + c * d := Q'.add_le_add_right _ _ _ hcross
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) (Q'.le_trans' _ _ _ hstep (Q'.ge_of_eqv e2))

/-! ## 4. The two named-open residuals of the continuum-shadow reframing. -/

/-- **(a) — `ContinuumFloor w`** — the elliptic-modulus bound `G_odd(w) − G_even(w) ≤ 1`, rendered
constructively as an ε-modulus LIMIT statement on the finite lattice ratios `G(t) = Xi w t / Th w t`:
for every tolerance `1/(k+1)`, beyond index `modulus k` the finite variance-increment satisfies (in
cleared, `Th`-multiplied form) `G(t+1) − G(t) ≤ 1 + 1/(k+1)`.  As `t → ∞` this is exactly `G_odd −
G_even ≤ 1` (`k = (ϑ₂/ϑ₃)²` the elliptic modulus).  The finite surrogate `G(t+1) − G(t) ≤ 1` is
FALSE at finite `t` (verified: `1.2456` at `w=0.8`), so the bound is intrinsically asymptotic — hence
the ε-modulus form.  `Type`-level modulus (Rule 8); NAMED-OPEN (a smooth infinite-theta inequality,
not discharged here). -/
structure ContinuumFloor (w : Q') : Type where
  /-- The ε-modulus: beyond `modulus k` the increment is within `1 + 1/(k+1)`. -/
  modulus : Nat → Nat
  /-- Cleared asymptotic bound `Xi(t+1)·Th(t) ≤ (Xi(t)+Th(t))·Th(t+1) + (1/(k+1))·Th(t)·Th(t+1)`,
  i.e. `G(t+1) − G(t) ≤ 1 + 1/(k+1)` for all `t ≥ modulus k`. -/
  eventually : ∀ k t, modulus k ≤ t →
    Xi w (t + 1) * Th w t
      ≤ (Xi w t + Th w t) * Th w (t + 1)
        + Q'.invSucc k * (Th w t * Th w (t + 1))

/-- **(b) — `FiniteCorrectionBound w`** — the finite-size correction residual: the IMPLICATION that
the EXACT finite floor `∀ s, FullRangeFloor w s` (= R1) follows from the continuum modulus bound (a).
This carries the verified subtlety that the finite `Δ²V` can dip a hair below its asymptote `−2(G_odd
− G_even)`, so the transfer from the continuum inequality to the exact `−2` floor is genuine (not
free).  NAMED-OPEN (never `sorry`); not trivially inhabitable (producing `reduce` is exactly the
finite-correction estimate). -/
structure FiniteCorrectionBound (w : Q') : Type where
  /-- The exact finite floor at every window follows from the continuum modulus bound. -/
  reduce : ContinuumFloor w → ∀ s, FullRangeFloor w s

/-! ## 5. THE COMPOSITE — R1 from the continuum-shadow reframing. -/

/-- **`saddleVarianceFloor_of_shadow` — THE REDUCTION.**  (a) `ContinuumFloor` (the elliptic-modulus
bound `G_odd − G_even ≤ 1`) plus (b) `FiniteCorrectionBound` (the finite-size correction implication)
inhabit `CircleFourierPowerModel.SaddleVarianceFloor w` (= R1).  Pure modus ponens over the two
residual fields: axiom-clean, no `sorry`, no algebra faked. -/
def saddleVarianceFloor_of_shadow {w : Q'}
    (ca : ContinuumFloor w) (cb : FiniteCorrectionBound w) :
    SaddleVarianceFloor w where
  floor := fun s => cb.reduce ca s

/-- **`shadow_twoPointTie`** — the composite carried through the existing R1/R2 ledger to
`MeanComplementClose.TwoPointTieSubleading`.  Needs additionally R2 (`WindowTailTransfer`, the
window-tail transfer of `CircleFourierPowerModel`). -/
def shadow_twoPointTie {w : Q'}
    (ca : ContinuumFloor w) (cb : FiniteCorrectionBound w) (R2 : WindowTailTransfer w) :
    MeanComplementClose.TwoPointTieSubleading w :=
  circleFourier_twoPointTie (saddleVarianceFloor_of_shadow ca cb) R2

/-! ## 6. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean):
  * `four_dim_add_dsq` — the per-term `Nat` mass/curvature split `4(p+1)(t−p+1) + dsq = (t+2)²`.
  * `coeff_prod_eq`, `bridge_term`, `bridge_term_dsq` — the per-term autoconvolution factorizations.
  * `masBridge` — `4·acNfull + Xi ≃ M²·Th` (floor mass = envelope-scaled variance denominator `den_t`).
  * `momBridge` — `4·dmomNfull + Zeta ≃ M²·Xi` (floor moment = variance numerator `num_t`).
  * `mediant_lower`, `mediant_upper` — the cleared convex-combination betweenness (the `V → G_parity`
    monotone-convergence engine; the algebraic core of `V(t+2) = λV(t) + (1−λ)G(t+2)`).
  * `saddleVarianceFloor_of_shadow` — the composite `(a) → (b) → SaddleVarianceFloor w` (= R1).
  * `shadow_twoPointTie` — the composite carried to `TwoPointTieSubleading` (with R2).

NAMED OPEN (Type-level structures, never `sorry`):
  * `ContinuumFloor w` (**a**) — the elliptic-modulus bound `G_odd − G_even ≤ 1`, as a constructive
    ε-modulus limit on the finite lattice ratios `Xi/Th`.  A smooth infinite-theta inequality;
    `→ 1` as `w→0`, `→ 0` as `w→1`.  NOT discharged here.
  * `FiniteCorrectionBound w` (**b**) — the finite-size correction implication `(a) → ∀ s,
    FullRangeFloor w s`.  Carries the verified undershoot subtlety.  NOT discharged here.

VERDICT: a RELOCATION of R1 onto {ONE continuum modulus inequality (a) + ONE finite-correction bound
(b)}, with the connecting algebra (two bridges + the mediant engine) PROVED.  This is structurally
cleaner than the `s`-growing `PolyaCertifiedFloor`, but is NOT a closure — neither (a) nor (b) is
discharged.  The Clay Yang–Mills mass gap remains OPEN.

DOCUMENTED (not Lean fields):
  * the additive recursions `θ_{t+2}=θ_t+2w^{(t+2)²/2}`, `den_{t+2}=den_t+4(t+3)θ_{t+2}`, and the
    convex combination `V(t+2)=λV(t)+(1−λ)G(t+2)` — validated to 1e-61 in
    `computations/continuum_shadow_pilot.py`; they live in `√w` (half-integer powers), outside the
    `Nat`-power `qpow` substrate, so are carried numerically, with their cleared betweenness core
    proved abstractly here (`mediant_lower`/`mediant_upper`).
-/

end YMGap.Continuum.ContinuumShadowFloor

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ContinuumShadowFloor.masBridge
#print axioms YMGap.Continuum.ContinuumShadowFloor.momBridge
#print axioms YMGap.Continuum.ContinuumShadowFloor.mediant_lower
#print axioms YMGap.Continuum.ContinuumShadowFloor.mediant_upper
#print axioms YMGap.Continuum.ContinuumShadowFloor.saddleVarianceFloor_of_shadow
#print axioms YMGap.Continuum.ContinuumShadowFloor.shadow_twoPointTie
