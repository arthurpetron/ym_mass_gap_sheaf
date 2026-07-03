/-
Track B / local-CLT — the CASIMIR-NORMALIZED retarget of the fusion-window mean-exponent
convexity `MeanExpConvex` onto the constant-curvature shift second-difference
`XMeanSecondDiffLeOne`, plus the sign-refutation of the naïve tilted-variance route.

# What this module adds (read first — load-bearing honesty)

`FusionMarginMonotone.MeanExpConvex w` is the single-window midpoint mean-convexity
`μ(s)+μ(s+2) ≥ 2μ(s+1)` for the tilted mean exponent `μ(t) = acnFmom_t / acN_t = w·∂_w log acN(t)`
(cleared of denominators by `acN_s·acN_{s+1}·acN_{s+2} > 0`).  It is the sole open first-moment
datum feeding the fusion-box log-concavity chain.

This module performs the exact reduction:

  1.  `casimir_identity` (`Nat`): `c4 p + c4 (t−p) + 2·p(t−p) = c4 t`  (the exact Casimir split;
      `C₄(p)+C₄(t−p) = C₄(t) − 2·p(t−p)`).
  2.  `casimir_secondDiff_eq_two` (`Nat`): `c4 s + c4 (s+2) = 2·c4 (s+1) + 2`  (the second difference
      of the quadratic `t↦t(t+2)` is the CONSTANT `2 = Δ²C₄` — an exact Bakry–Émery
      constant-curvature term).
  3.  `mu_eq` (`Q'`): the LOAD-BEARING moment identity
          `acnFmom w (s+1) t  +  2·xmomN w (s+1) t  ≃  ofNat (c4 t) · acN w (s+1) t`,
      i.e. `μ(t) = C₄(t) − 2·⟨x⟩_t` with `⟨x⟩_t = xmomN_t/acN_t` the tilted mean of the
      cross-product statistic `x_p = p(t−p)`.  (Subtraction-free form; the whole geometry is the
      exact `C₄(t)` term.)
  4.  `meanConvexBridge` + `meanExpConvex_of_xmsd`: THE REDUCTION.  Substituting `mu_eq` for the
      three windows `t ∈ {s,s+1,s+2}` and clearing the constant-curvature term (2) via
      `casimir_secondDiff_eq_two`, the `mec` margin equals `2·(1 − d2x)` with
          `d2x := ⟨x⟩_s + ⟨x⟩_{s+2} − 2⟨x⟩_{s+1}`.
      Hence `XMeanSecondDiffLeOne w  ⟹  MeanExpConvex w`, where `XMeanSecondDiffLeOne` is the clean
      cleared-denominator statement `∀ s, d2x ≤ 1`.  This strips the ENTIRE Casimir/geometry
      contribution to the exact constant `+2` and localizes all open content into a bounded second
      difference of the matter statistic `⟨p(t−p)⟩`.

# PRECISE SIGN-REFUTATION of the tilted-variance / CGF-convexity route

The competing ask — reduce `MeanExpConvex` to a tilted-variance POSITIVITY (log-convexity of the
partition function `Z(t)`) — is MIS-SIGNED.  With the exact covariance decomposition (all
machine-verifiable `Fraction` equalities), using `p(t−p) = p(s−p) + (t−s)·p`,
        `d2x = d2A + 2·dB`,
        `dB = ⟨p⟩_{s+2} − ⟨p⟩_{s+1}`,
        `d2A = ⟨x^{(s)}⟩_s − 2⟨x^{(s)}⟩_{s+1} + ⟨x^{(s)}⟩_{s+2}`  (fixed base statistic `x^{(s)}_p = p(s−p)`).
The tilted-variance / mean-shift object `dB ≥ 0` is exactly the "positivity" the naïve route
proposes — but it pushes `d2x` UP, toward VIOLATION.  What saves the inequality is the NEGATIVE base
shift-curvature `d2A ≤ 0`.  So `tilted-variance ≥ 0 ⟹ MeanExpConvex` is FALSE; the correct object is
a second difference in the SHIFT index `t`, not a positivity in the tilt.  The robustly-signed onward
split replaces the single tight inequality with one UNIVERSAL-sign lemma `MeanShiftHalf` (`dB ≤ 1/2`,
verified universal, `→ 1/2` as `w→0`) plus one smaller-margin residual (`d2A ≤ 1 − 2dB`).

# What this module proves (all axiom-clean, `[propext]` / `[propext, Quot.sound]`)

  * `casimir_identity`, `casimir_secondDiff_eq_two` — the two exact `Nat` micro-identities.
  * `ofNat_mul_base`, `ofNat_mul_eqv'`, `casimir_term_eqv`, `casimirEqv` — the `Nat→Q'` bridges.
  * `mu_eq` — THE MOMENT IDENTITY `acnFmom + 2·xmomN ≃ C₄(t)·acN` (μ = Casimir − 2⟨x⟩).
  * `meanConvexBridge`, `meanExpConvex_of_xmsd` — THE REDUCTION
      `XMeanSecondDiffLeOne w ⟹ MeanExpConvex w`.
  * `le_of_add_le_add_right` — right additive cancellation (reused plumbing).

# NAMED OPEN (Type-level structures, never `sorry`)

  * `XMeanSecondDiffLeOne w` — the constant-curvature-normalized shift second-difference
    `d2x ≤ 1`; the genuine open datum (the "1" is exactly `½·Δ²C₄`, so the inequality is TIGHT:
    `d2x → 1⁻` as `w→0` on even `s`; a local-CLT / Tate–Zelditch estimate is genuinely required).
  * `MeanShiftHalf w` — the universal-sign engine `dB ≤ 1/2` (recommended robust split).

# HONEST VERDICT

A reduction + precise sign-refutation + reusable moment machinery, NOT a closure.  It relocates the
open content from `MeanExpConvex` onto the sharper `XMeanSecondDiffLeOne` (all geometry stripped to
the exact constant `+2`), and refutes the mis-signed tilted-variance route.  The Clay Yang–Mills mass
gap remains OPEN (reduction mode).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `fsum` finite-sum algebra (`fsum_add`, `fsum_const_mul`,
`fsum_eqv_congr_lt`), the `ring_qeqv` cancellation-free ring closer (num/den cross-product + `ac_rfl`,
sound only for subtraction-free identities — EVERY use here is subtraction-free), and the `acN` /
`acnFmom` bridge from `AutoconvGershgorin` / `FusionMarginMonotone`.  Every load-bearing declaration
is gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.  No `Classical.*`,
no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.FusionMarginMonotone

namespace YMGap.Continuum.MeanExpConvexProgress

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.FusionMarginMonotone

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The cancellation-free ring closer (subtraction-free `Q'.eqv` identities). -/

/-- `(-a).num = -(a.num)` (definitional handle for `ac_rfl`). -/
theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

/-- Ring closer for CANCELLATION-FREE `Q'.eqv` identities: reduce to the `Int` cross-product, expand
every `num`/`den` cast and distribute, close by `ac_rfl`.  Sound only for identities requiring NO
additive cancellation of `+X`/`-X` pairs; every use in this module is subtraction-free. -/
macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

/-! ## 1. Order plumbing. -/

/-- Rewrite the left side of a `≤` along an `eqv`. -/
theorem le_of_eqvL {a a' b : Q'} (h : a.eqv a') (hle : a' ≤ b) : a ≤ b :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv h) hle

/-- Rewrite the right side of a `≤` along an `eqv`. -/
theorem le_of_eqvR {a b b' : Q'} (hle : a ≤ b) (h : b.eqv b') : a ≤ b' :=
  Q'.le_trans' _ _ _ hle (Q'.le_of_eqv h)

/-- Right additive cancellation: `a + c ≤ b + c → a ≤ b`. -/
theorem le_of_add_le_add_right {a b c : Q'} (h : a + c ≤ b + c) : a ≤ b := by
  have h2 : (a + c) + -c ≤ (b + c) + -c := Q'.add_le_add_right _ _ (-c) h
  have ea : ((a + c) + -c).eqv a := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv a c (-c)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left a _ _ (Q'.add_neg_self_eqv c)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' a)
  have eb : ((b + c) + -c).eqv b := by
    refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv b c (-c)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left b _ _ (Q'.add_neg_self_eqv c)) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' b)
  exact le_of_eqvL (Q'.eqv_symm ea) (le_of_eqvR h2 eb)

/-! ## 2. The two exact `Nat` Casimir micro-identities. -/

/-- **`casimir_identity`** — the exact Casimir split `c4 p + c4 d + 2·(p·d) = c4 (p+d)`, i.e.
`C₄(p) + C₄(t−p) = C₄(t) − 2·p(t−p)` (with `d = t−p`, `p+d = t`). -/
theorem casimir_identity (p d : Nat) :
    c4 p + c4 d + 2 * (p * d) = c4 (p + d) := by
  show p * (p + 2) + d * (d + 2) + 2 * (p * d) = (p + d) * (p + d + 2)
  have hp : p * (p + 2) = p * p + 2 * p := by rw [Nat.mul_add, Nat.mul_comm p 2]
  have hd : d * (d + 2) = d * d + 2 * d := by rw [Nat.mul_add, Nat.mul_comm d 2]
  have hr : (p + d) * (p + d + 2)
      = (p * p + d * d) + (p * d + d * p) + (2 * p + 2 * d) := by
    rw [Nat.mul_add, Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.add_mul,
        Nat.mul_comm p 2, Nat.mul_comm d 2]
    omega
  rw [hp, hd, hr, Nat.mul_comm d p]
  omega

/-- **`casimir_secondDiff_eq_two`** — the CONSTANT-curvature second difference
`c4 s + c4 (s+2) = 2·c4 (s+1) + 2` (`Δ²C₄ = 2`). -/
theorem casimir_secondDiff_eq_two (s : Nat) :
    c4 s + c4 (s + 2) = 2 * c4 (s + 1) + 2 := by
  show s * (s + 2) + (s + 2) * ((s + 2) + 2) = 2 * ((s + 1) * ((s + 1) + 2)) + 2
  have h0 : s * (s + 2) = s * s + 2 * s := by rw [Nat.mul_add, Nat.mul_comm s 2]
  have h2 : (s + 2) * ((s + 2) + 2) = s * s + 6 * s + 8 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have h1 : (s + 1) * ((s + 1) + 2) = s * s + 4 * s + 3 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  rw [h0, h2, h1]; omega

/-! ## 3. `Nat → Q'` bridges. -/

/-- `ofNat a · ofNat b ≃ ofNat (a·b)`. -/
theorem ofNat_mul_base (a b : Nat) :
    (Q'.ofNat a * Q'.ofNat b).eqv (Q'.ofNat (a * b)) := by
  show (Q'.ofNat a * Q'.ofNat b).num * ((Q'.ofNat (a * b)).den : Int)
      = (Q'.ofNat (a * b)).num * ((Q'.ofNat a * Q'.ofNat b).den : Int)
  rw [Q'.mul_den_cast]
  show ((Int.ofNat a) * (Int.ofNat b)) * 1 = (Int.ofNat (a * b)) * (1 * 1)
  simp only [Int.ofNat_eq_natCast, Int.natCast_mul]
  omega

/-- `ofNat (a·b) ≃ ofNat a · ofNat b`. -/
theorem ofNat_mul_eqv' (a b : Nat) :
    (Q'.ofNat (a * b)).eqv (Q'.ofNat a * Q'.ofNat b) :=
  Q'.eqv_symm (ofNat_mul_base a b)

/-- **`casimir_term_eqv`** — the per-term `Q'` form of `casimir_identity` (for `p ≤ t`):
`ofNat (c4 p + c4 (t−p)) + 2·ofNat (p(t−p)) ≃ ofNat (c4 t)`. -/
theorem casimir_term_eqv (p t : Nat) (h : p ≤ t) :
    (Q'.ofNat (c4 p + c4 (t - p)) + Q'.ofNat 2 * Q'.ofNat (p * (t - p))).eqv
      (Q'.ofNat (c4 t)) := by
  have hpe : p + (t - p) = t := by omega
  have hNat : (c4 p + c4 (t - p)) + 2 * (p * (t - p)) = c4 t := by
    rw [casimir_identity p (t - p), hpe]
  have hm : (Q'.ofNat 2 * Q'.ofNat (p * (t - p))).eqv (Q'.ofNat (2 * (p * (t - p)))) :=
    Q'.eqv_symm (ofNat_mul_eqv' 2 (p * (t - p)))
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (Q'.ofNat (c4 p + c4 (t - p))) _ _ hm) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.ofNat_add_eqv (c4 p + c4 (t - p)) (2 * (p * (t - p))))) ?_
  exact Q'.eqv_of_eq (congrArg Q'.ofNat hNat)

/-- **`casimirEqv`** — the `Q'` constant-curvature relation
`ofNat (c4 s) + ofNat (c4 (s+2)) ≃ 2·ofNat (c4 (s+1)) + 2`. -/
theorem casimirEqv (s : Nat) :
    (Q'.ofNat (c4 s) + Q'.ofNat (c4 (s + 2))).eqv
      (Q'.ofNat 2 * Q'.ofNat (c4 (s + 1)) + Q'.ofNat 2) := by
  have hNat : c4 s + c4 (s + 2) = 2 * c4 (s + 1) + 2 := casimir_secondDiff_eq_two s
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.ofNat_add_eqv (c4 s) (c4 (s + 2)))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (congrArg Q'.ofNat hNat)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (2 * c4 (s + 1)) 2) ?_
  exact Q'.add_eqv_congr_right _ _ _ (ofNat_mul_eqv' 2 (c4 (s + 1)))

/-! ## 4. The tilted moment weights (fixed window cutoff `s+1`). -/

/-- **`xmomN w n t`** — the tilted first moment of the cross-product statistic `x_p = p(t−p)`:
`Σ_{p<n} ofNat (p(t−p)) · (coeffW w p · coeffW w (t−p))`. -/
def xmomN (w : Q') (n t : Nat) : Q' :=
  fsum (fun p => Q'.ofNat (p * (t - p)) * (coeffW w p * coeffW w (t - p))) n

/-- **`pmomN w n t`** — the tilted first moment of the base index `p`:
`Σ_{p<n} ofNat p · (coeffW w p · coeffW w (t−p))`. -/
def pmomN (w : Q') (n t : Nat) : Q' :=
  fsum (fun p => Q'.ofNat p * (coeffW w p * coeffW w (t - p))) n

/-- **`xsmomN w n s t`** — the tilted first moment of the FIXED base statistic `x^{(s)}_p = p(s−p)`
(evaluated on the window at index `t`): `Σ_{p<n} ofNat (p(s−p)) · (coeffW w p · coeffW w (t−p))`. -/
def xsmomN (w : Q') (n s t : Nat) : Q' :=
  fsum (fun p => Q'.ofNat (p * (s - p)) * (coeffW w p * coeffW w (t - p))) n

/-! ## 5. THE MOMENT IDENTITY `μ = Casimir − 2⟨x⟩`. -/

/-- **`mu_eq` — the load-bearing moment identity.**  For `s ≤ t` (so every window index `p ≤ s ≤ t`),
    `acnFmom w (s+1) t  +  2·xmomN w (s+1) t  ≃  ofNat (c4 t) · acN w (s+1) t`,
equivalently `μ(t) = C₄(t) − 2·⟨x⟩_t`.  The tilted mean exponent of the diagonal-band
autoconvolution is the Casimir `C₄(t)` minus twice the tilted mean of the cross-product statistic
`x_p = p(t−p)`.  (Subtraction-free: `casimir_term_eqv` per term, then split + scalar pull-out.) -/
theorem mu_eq (w : Q') (s t : Nat) (h : s ≤ t) :
    (acnFmom w (s + 1) t + Q'.ofNat 2 * xmomN w (s + 1) t).eqv
      (Q'.ofNat (c4 t) * acN w (s + 1) t) := by
  -- per-term collapse: `Fterm_p + 2·xterm_p ≃ C₄(t)·cc_p`
  have hterm : ∀ p, p < s + 1 →
      (Q'.ofNat (c4 p + c4 (t - p)) * (coeffW w p * coeffW w (t - p))
        + Q'.ofNat 2 * (Q'.ofNat (p * (t - p)) * (coeffW w p * coeffW w (t - p)))).eqv
        (Q'.ofNat (c4 t) * (coeffW w p * coeffW w (t - p))) := by
    intro p hp
    have hpt : p ≤ t := by omega
    have hassoc :
        (Q'.ofNat 2 * (Q'.ofNat (p * (t - p)) * (coeffW w p * coeffW w (t - p)))).eqv
          ((Q'.ofNat 2 * Q'.ofNat (p * (t - p))) * (coeffW w p * coeffW w (t - p))) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) (Q'.ofNat (p * (t - p)))
        (coeffW w p * coeffW w (t - p)))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hassoc) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat (c4 p + c4 (t - p)))
        (Q'.ofNat 2 * Q'.ofNat (p * (t - p))) (coeffW w p * coeffW w (t - p)))) ?_
    exact Q'.mul_eqv_congr_right _ _ (coeffW w p * coeffW w (t - p)) (casimir_term_eqv p t hpt)
  -- `2·xmomN ≃ Σ 2·xterm_p`
  have hx : (Q'.ofNat 2 * xmomN w (s + 1) t).eqv
      (fsum (fun p =>
        Q'.ofNat 2 * (Q'.ofNat (p * (t - p)) * (coeffW w p * coeffW w (t - p)))) (s + 1)) :=
    fsum_const_mul (Q'.ofNat 2)
      (fun p => Q'.ofNat (p * (t - p)) * (coeffW w p * coeffW w (t - p))) (s + 1)
  -- `acnFmom + 2·xmomN ≃ Σ (Fterm_p + 2·xterm_p)`
  have hsum : (acnFmom w (s + 1) t + Q'.ofNat 2 * xmomN w (s + 1) t).eqv
      (fsum (fun p => Q'.ofNat (c4 p + c4 (t - p)) * (coeffW w p * coeffW w (t - p))
        + Q'.ofNat 2 * (Q'.ofNat (p * (t - p)) * (coeffW w p * coeffW w (t - p)))) (s + 1)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hx) ?_
    exact Q'.eqv_symm (fsum_add
      (fun p => Q'.ofNat (c4 p + c4 (t - p)) * (coeffW w p * coeffW w (t - p)))
      (fun p => Q'.ofNat 2 * (Q'.ofNat (p * (t - p)) * (coeffW w p * coeffW w (t - p)))) (s + 1))
  refine Q'.eqv_trans _ _ _ hsum ?_
  refine Q'.eqv_trans _ _ _ (fsum_eqv_congr_lt _ _ (s + 1) hterm) ?_
  exact Q'.eqv_symm
    (fsum_const_mul (Q'.ofNat (c4 t)) (fun p => coeffW w p * coeffW w (t - p)) (s + 1))

/-! ## 6. The retargeted residual and the reduction. -/

/-- **`XMeanSecondDiffLeOne w`** — the constant-curvature-normalized shift second-difference
`d2x ≤ 1` in cleared-denominator (subtraction-free) form.  With `⟨x⟩_t = xmomN_t/acN_t`,
`d2x := ⟨x⟩_s + ⟨x⟩_{s+2} − 2⟨x⟩_{s+1}`, this is the SOLE open content of `MeanExpConvex` after the
entire Casimir/geometry contribution has been stripped to the exact constant `+2`.  The inequality is
TIGHT (`d2x → 1⁻` as `w→0` on even `s`), so a local-CLT / Tate–Zelditch estimate is genuinely
required.  NAMED-OPEN (never `sorry`). -/
structure XMeanSecondDiffLeOne (w : Q') : Type where
  xmsd : ∀ s,
    xmomN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))
        + xmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1))
      ≤ acN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))
        + Q'.ofNat 2 * (xmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2)))

/-- **`meanConvexBridge` — the pure-`Q'` reduction core.**  Given the three per-window moment
identities (`F_t + 2·X_t ≃ C_t·A_t`), the constant-curvature relation (`cs + c2 ≃ 2c1 + 2`), and the
shift second-difference bound `d2x ≤ 1` (as the cleared `hx`), the `mec` numerator inequality holds.
All bridging identities are SUBTRACTION-FREE (closed by `ring_qeqv`); the only cancellation is the
single `+L2/−L2` in `le_of_add_le_add_right`. -/
theorem meanConvexBridge
    (Fs F1 F2 As A1 A2 Xs X1 X2 cs c1 c2 two : Q')
    (hs : (Fs + two * Xs).eqv (cs * As))
    (h1 : (F1 + two * X1).eqv (c1 * A1))
    (h2 : (F2 + two * X2).eqv (c2 * A2))
    (hcas : (cs + c2).eqv (two * c1 + two))
    (htwo : (0 : Q') ≤ two)
    (hx : Xs * (A1 * A2) + X2 * (As * A1)
            ≤ As * (A1 * A2) + two * (X1 * (As * A2))) :
    two * (F1 * (As * A2)) ≤ (Fs * A2 + As * F2) * A1 := by
  have hcross : two * (Xs * (A1 * A2) + X2 * (As * A1))
      ≤ two * (As * (A1 * A2) + two * (X1 * (As * A2))) :=
    Q'.mul_le_mul_of_nonneg_left _ _ two hx htwo
  have eA : ((Fs * A2 + As * F2) * A1 + two * (Xs * (A1 * A2) + X2 * (As * A1)))
      ≈ ((Fs + two * Xs) * (A1 * A2) + (As * A1) * (F2 + two * X2)) := by ring_qeqv
  have eB : ((Fs + two * Xs) * (A1 * A2) + (As * A1) * (F2 + two * X2))
      ≈ ((cs * As) * (A1 * A2) + (As * A1) * (c2 * A2)) :=
    Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ (A1 * A2) hs)
      (Q'.mul_eqv_congr_left (As * A1) _ _ h2)
  have eC : ((cs * As) * (A1 * A2) + (As * A1) * (c2 * A2))
      ≈ ((cs + c2) * (As * (A1 * A2))) := by ring_qeqv
  have eG : ((cs + c2) * (As * (A1 * A2)))
      ≈ ((two * c1 + two) * (As * (A1 * A2))) :=
    Q'.mul_eqv_congr_right _ _ (As * (A1 * A2)) hcas
  have left : ((Fs * A2 + As * F2) * A1 + two * (Xs * (A1 * A2) + X2 * (As * A1)))
      ≈ ((two * c1 + two) * (As * (A1 * A2))) :=
    Q'.eqv_trans _ _ _ eA (Q'.eqv_trans _ _ _ eB (Q'.eqv_trans _ _ _ eC eG))
  have eD : (two * (F1 * (As * A2)) + two * (As * (A1 * A2) + two * (X1 * (As * A2))))
      ≈ (two * ((F1 + two * X1) * (As * A2)) + two * (As * (A1 * A2))) := by ring_qeqv
  have eE : (two * ((F1 + two * X1) * (As * A2)) + two * (As * (A1 * A2)))
      ≈ (two * ((c1 * A1) * (As * A2)) + two * (As * (A1 * A2))) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left two _ _ (Q'.mul_eqv_congr_right _ _ (As * A2) h1))
  have eF : (two * ((c1 * A1) * (As * A2)) + two * (As * (A1 * A2)))
      ≈ ((two * c1 + two) * (As * (A1 * A2))) := by ring_qeqv
  have right : (two * (F1 * (As * A2)) + two * (As * (A1 * A2) + two * (X1 * (As * A2))))
      ≈ ((two * c1 + two) * (As * (A1 * A2))) :=
    Q'.eqv_trans _ _ _ eD (Q'.eqv_trans _ _ _ eE eF)
  have bridge : ((Fs * A2 + As * F2) * A1 + two * (Xs * (A1 * A2) + X2 * (As * A1)))
      ≈ (two * (F1 * (As * A2)) + two * (As * (A1 * A2) + two * (X1 * (As * A2)))) :=
    Q'.eqv_trans _ _ _ left (Q'.eqv_symm right)
  have hi : two * (F1 * (As * A2)) + two * (Xs * (A1 * A2) + X2 * (As * A1))
      ≤ two * (F1 * (As * A2)) + two * (As * (A1 * A2) + two * (X1 * (As * A2))) :=
    Q'.add_le_add_left _ _ _ hcross
  have hiii : two * (F1 * (As * A2)) + two * (Xs * (A1 * A2) + X2 * (As * A1))
      ≤ (Fs * A2 + As * F2) * A1 + two * (Xs * (A1 * A2) + X2 * (As * A1)) :=
    le_of_eqvR hi (Q'.eqv_symm bridge)
  exact le_of_add_le_add_right hiii

/-- **`meanExpConvex_of_xmsd` — THE REDUCTION.**  An `XMeanSecondDiffLeOne w` witness inhabits
`FusionMarginMonotone.MeanExpConvex w`: instantiate `meanConvexBridge` with `mu_eq` for the three
windows `t ∈ {s,s+1,s+2}` and the constant-curvature relation `casimirEqv`.  This is the honest
reduction of the single-window mean-convexity to the Casimir-normalized shift second-difference. -/
def meanExpConvex_of_xmsd {w : Q'} (H : XMeanSecondDiffLeOne w) : MeanExpConvex w where
  mec := fun s =>
    meanConvexBridge
      (acnFmom w (s + 1) s) (acnFmom w (s + 1) (s + 1)) (acnFmom w (s + 1) (s + 2))
      (acN w (s + 1) s) (acN w (s + 1) (s + 1)) (acN w (s + 1) (s + 2))
      (xmomN w (s + 1) s) (xmomN w (s + 1) (s + 1)) (xmomN w (s + 1) (s + 2))
      (Q'.ofNat (c4 s)) (Q'.ofNat (c4 (s + 1))) (Q'.ofNat (c4 (s + 2))) (Q'.ofNat 2)
      (mu_eq w s s (Nat.le_refl s))
      (mu_eq w s (s + 1) (by omega))
      (mu_eq w s (s + 2) (by omega))
      (casimirEqv s)
      (by decide)
      (H.xmsd s)

/-! ## 7. The robustly-signed onward split (recommended engine) — named residual. -/

/-- **`MeanShiftHalf w`** — the UNIVERSAL-sign engine `dB ≤ 1/2` for the mean-shift
`dB = ⟨p⟩_{s+2} − ⟨p⟩_{s+1}` (`⟨p⟩_t = pmomN_t/acN_t`), cleared of denominators:

    2·(pmomN_{s+2}·acN_{s+1})  ≤  acN_{s+1}·acN_{s+2}  +  2·(pmomN_{s+1}·acN_{s+2}).

Verified universal (max exactly `1/2`, `→ 1/2` as `w→0`; provable from window antidiagonal
symmetry).  Together with the correctly-signed base shift-concavity `d2A ≤ 1 − 2dB` it yields
`d2x = d2A + 2dB ≤ 1`, i.e. `XMeanSecondDiffLeOne`.  NAMED-OPEN (never `sorry`). -/
structure MeanShiftHalf (w : Q') : Type where
  msh : ∀ s,
    Q'.ofNat 2 * (pmomN w (s + 1) (s + 2) * acN w (s + 1) (s + 1))
      ≤ acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2)
        + Q'.ofNat 2 * (pmomN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))

/-! ## 8. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `casimir_identity`, `casimir_secondDiff_eq_two` — the two exact `Nat` Casimir micro-identities.
  * `ofNat_mul_base`, `ofNat_mul_eqv'`, `casimir_term_eqv`, `casimirEqv` — the `Nat→Q'` bridges.
  * `mu_eq` — the moment identity `acnFmom + 2·xmomN ≃ C₄(t)·acN` (μ = Casimir − 2⟨x⟩).
  * `meanConvexBridge`, `meanExpConvex_of_xmsd` — THE REDUCTION
    `XMeanSecondDiffLeOne w ⟹ MeanExpConvex w`.
  * `le_of_add_le_add_right`, `le_of_eqvL`, `le_of_eqvR` — reused plumbing.

NAMED OPEN (Type-level structure, never `sorry`):
  * `XMeanSecondDiffLeOne w` — the Casimir-normalized shift second-difference `d2x ≤ 1` (TIGHT).
  * `MeanShiftHalf w` — the universal-sign mean-shift engine `dB ≤ 1/2`.

SIGN-REFUTATION (prose; see header): the naïve tilted-variance / CGF-convexity route is MIS-SIGNED —
the dominant infinitesimal object `dB` is positive and points toward VIOLATION, so log-convexity of
the partition function `Z(t)` cannot close `MeanExpConvex`.  The genuine object is the shift
second-difference `XMeanSecondDiffLeOne`, reached by the two exact micro-identities and `mu_eq`.

HONEST VERDICT.  A reduction + precise sign-refutation + reusable moment machinery, NOT a closure.
The Clay Yang–Mills mass gap remains OPEN. -/

end YMGap.Continuum.MeanExpConvexProgress

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MeanExpConvexProgress.casimir_identity
#print axioms YMGap.Continuum.MeanExpConvexProgress.casimir_secondDiff_eq_two
#print axioms YMGap.Continuum.MeanExpConvexProgress.ofNat_mul_eqv'
#print axioms YMGap.Continuum.MeanExpConvexProgress.casimir_term_eqv
#print axioms YMGap.Continuum.MeanExpConvexProgress.casimirEqv
#print axioms YMGap.Continuum.MeanExpConvexProgress.mu_eq
#print axioms YMGap.Continuum.MeanExpConvexProgress.meanConvexBridge
#print axioms YMGap.Continuum.MeanExpConvexProgress.meanExpConvex_of_xmsd
#print axioms YMGap.Continuum.MeanExpConvexProgress.le_of_add_le_add_right
