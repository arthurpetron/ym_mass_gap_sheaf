/-
Track B / local-CLT — the EXACT antidiagonal-variance (covariance) recast of the complement-half
leaf `MeanShiftComplementHalf.msch`.

# What this module adds (read first — load-bearing honesty)

`XMeanSecondDiffProgress.MeanShiftComplementHalf w` is the sole missing leaf feeding the
fusion-window mean-convexity chain (its companion `MeanShiftHalf` is already discharged).  Its field
`msch` is the cleared, subtraction-free `×2` form of `d2x − dB ≤ 1/2`, phrased opaquely in the tilted
cross-product moment `xmomN` (of the statistic `x_p = p(t−p)`).

This module introduces the ANTIDIAGONAL-SQUARE moment `⟨D²⟩ = dmomN` (of the Nat-safe statistic
`D²_p = (t−2p)²`) and proves the exact moment identity

    4·⟨x⟩_t + ⟨D²⟩_t  =  t²·A_t                          (`dsq_moment_eq`, cleared over `acN`),

i.e. `4·p(t−p) + (t−2p)² = t²` per term (`four_x_add_dsq`).  Substituting this and the exact
`t²`-second-difference `Δ²(t²) = 2` (`sq_secondDiff_eq_two`) into `2·msch`, the pure `A_s·A_{s+1}·A_{s+2}`
terms CANCEL IDENTICALLY (the `t²`-second-difference coefficient is `s² + (s+2)² − 2(s+1)² = 2 = 2`
matched by the same constant on the other side), and `msch` becomes EXACTLY the antidiagonal-variance
residual

    2·⟨D²⟩_{s+1} + 4·⟨p⟩_{s+1}  ≤  ⟨D²⟩_s + ⟨D²⟩_{s+2} + 4·⟨p⟩_{s+2}     (`DShiftCovResidual.dcov`),

cleared over `A_s·A_{s+1}·A_{s+2}`.  The equivalence `msch ⟺ dcov` is a genuine ring-level `↔`
(`msch_iff_dcov`), both directions proved with no nonnegativity and no analysis — this is the honest
covariance identity, losslessly relocating the opaque `xmomN`-form onto the transparent
antidiagonal-variance `dmomN`-form.

# What this module proves (all axiom-clean, `[propext]` / `[propext, Quot.sound]`)

  * `nat_sq_add`, `sq_two_mul`, `sq_two_add`, `sq_secondDiff_eq_two`, `four_x_add_dsq` — the exact
    `Nat` micro-identities (the antidiagonal-square split and `Δ²(t²)=2`).
  * `dmomN`, `dmomN_nonneg`, `dsq_moment_eq` — the antidiagonal-variance tilted moment, its
    nonnegativity, and THE MOMENT IDENTITY `4·⟨x⟩ + ⟨D²⟩ = t²·A`.
  * `four_eq_two_two`, `momentTwoTwo`, `sqEqv` — the `Q'` bridges (numeric doubling, the `two·(two·⟨x⟩)`
    form, and the `t²` constant-curvature relation).
  * `msch_iff_dcov_core`, `msch_iff_dcov` — THE EXACT RECAST: the opaque `msch` inequality is a
    ring-level `↔` with the antidiagonal-variance residual `dcov`.
  * `mschComplement_of_dcov`, `dcov_of_mschComplement` — the STRUCTURE-LEVEL relocation: the named
    open leaf `MeanShiftComplementHalf w` and the named residual `DShiftCovResidual w` are
    inter-derivable (the atom is relocated, not closed).

# NAMED OPEN (Type-level structure, never `sorry`)

  * `DShiftCovResidual w` — the antidiagonal-variance form of the complement half.  After the
    `⟨D²⟩ = 4·Var(p) + ⟨D⟩²` split its irreducible content is a MIDPOINT-CONCAVITY / Tate–Zelditch
    curvature bound on the tilted position variance (`Δ²_t Var_t(p) ≥ −½ − bracket/4`), NOT a bare
    nonnegativity.  It saturates at the same even-`s`, `w→0` two-point tie as `MeanShiftComplementHalf`.

# HONEST VERDICT

An EXACT covariance identity + reusable moment machinery, NOT a closure.  It converts `msch` losslessly
into the antidiagonal-variance residual `dcov`; it does NOT discharge it and it does NOT reduce to any
nonnegativity (the residual is a genuine local-CLT curvature datum).  The Clay Yang–Mills mass gap
remains OPEN (reduction mode).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` arithmetic, the reused `fsum` finite-sum algebra, the imported subtraction-free
`ring_qeqv` closer (EVERY use here is subtraction-free), and the `acN`/`xmomN`/`pmomN` bridge.  Every
load-bearing declaration is gated with `#print axioms`; permitted output is `propext` / `Quot.sound`
only.  No `Classical.*`, no `native_decide`, no `sorry`.  All witnesses are `Type`-level data.
-/

import YMGap.Continuum.XMeanSecondDiffProgress

namespace YMGap.Continuum.MeanComplementCovariance

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AutoconvGershgorin
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CubeRatioBounds
open YMGap.Continuum.AcNReserveAnalytic
open YMGap.Continuum.MeanExpConvexProgress
open YMGap.Continuum.XMeanSecondDiffProgress

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. A local `ofNat` nonnegativity. -/

/-- `0 ≤ ofNat n`. -/
theorem ofNatNonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

/-! ## 1. The exact `Nat` micro-identities. -/

/-- `(a+b)² = a² + 2ab + b²`. -/
theorem nat_sq_add (a b : Nat) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm b a]
  omega

/-- `(2a)² = 4a²`. -/
theorem sq_two_mul (a : Nat) : (2 * a) * (2 * a) = 4 * (a * a) := by
  rw [Nat.mul_assoc 2 a (2 * a), ← Nat.mul_assoc a 2 a, Nat.mul_comm a 2, Nat.mul_assoc 2 a a]
  omega

/-- `(2a+b)² = 4a² + 4ab + b²`. -/
theorem sq_two_add (a b : Nat) :
    (2 * a + b) * (2 * a + b) = 4 * (a * a) + 4 * (a * b) + b * b := by
  rw [nat_sq_add (2 * a) b, sq_two_mul a, Nat.mul_assoc 2 a b]
  omega

/-- **`sq_secondDiff_eq_two`** — the constant `t²`-second-difference `Δ²(t²) = 2`:
`s² + (s+2)² = 2·(s+1)² + 2`. -/
theorem sq_secondDiff_eq_two (s : Nat) :
    s * s + (s + 2) * (s + 2) = 2 * ((s + 1) * (s + 1)) + 2 := by
  have h2 : (s + 2) * (s + 2) = s * s + 4 * s + 4 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have h1 : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  rw [h2, h1]; omega

/-- **`dsq p t`** — the antidiagonal-square statistic `D²_p = (t−2p)²` in Nat-truncation-safe form
(`(t−2p)² + (2p−t)²`; exactly one summand is nonzero and it equals the integer square `(t−2p)²`). -/
def dsq (p t : Nat) : Nat := (t - 2 * p) * (t - 2 * p) + (2 * p - t) * (2 * p - t)

/-- **`four_x_add_dsq`** — the per-term identity `4·p(t−p) + (t−2p)² = t²` (for `p ≤ t`), the exact
covariance bridge `4·⟨x⟩ + ⟨D²⟩ = t²` at the summand level. -/
theorem four_x_add_dsq (p t : Nat) (h : p ≤ t) :
    4 * (p * (t - p)) + dsq p t = t * t := by
  show 4 * (p * (t - p)) + ((t - 2 * p) * (t - 2 * p) + (2 * p - t) * (2 * p - t)) = t * t
  obtain ⟨f, hf⟩ := Nat.le.dest h
  subst hf
  have r0 : (p + f) - p = f := by omega
  rw [r0]
  rcases Nat.lt_or_ge p f with hpf | hge
  · obtain ⟨k, hk⟩ := Nat.le.dest (Nat.le_of_lt hpf)
    subst hk
    have s1 : (p + (p + k)) - 2 * p = k := by omega
    have s2 : 2 * p - (p + (p + k)) = 0 := by omega
    have s3 : p + (p + k) = 2 * p + k := by omega
    rw [s1, s2, s3, sq_two_add p k, Nat.mul_add p p k]
    omega
  · obtain ⟨k, hk⟩ := Nat.le.dest hge
    subst hk
    have s1 : ((f + k) + f) - 2 * (f + k) = 0 := by omega
    have s2 : 2 * (f + k) - ((f + k) + f) = k := by omega
    have s3 : (f + k) + f = 2 * f + k := by omega
    rw [s1, s2, s3, sq_two_add f k, Nat.add_mul f k f, Nat.mul_comm k f]
    omega

/-! ## 2. The antidiagonal-variance tilted moment and the moment identity. -/

/-- **`dmomN w n t`** — the tilted first moment of the antidiagonal-square statistic `D²_p = (t−2p)²`:
`Σ_{p<n} ofNat (dsq p t) · (coeffW w p · coeffW w (t−p))` (i.e. `⟨D²⟩_t`, cleared of the mass). -/
def dmomN (w : Q') (n t : Nat) : Q' :=
  fsum (fun p => Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p))) n

/-- **`dmomN_nonneg`** — on `0 ≤ w`, `⟨D²⟩_t = dmomN w n t ≥ 0` (a finite sum of nonneg products). -/
theorem dmomN_nonneg {w : Q'} (hw : (0 : Q') ≤ w) (n t : Nat) : (0 : Q') ≤ dmomN w n t := by
  unfold dmomN
  exact fsum_nonneg
    (fun p => Q'.mul_nonneg _ _ (ofNatNonneg (dsq p t))
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw p) (coeffW_nonneg hw (t - p)))) n

/-- **`dsq_moment_eq` — THE MOMENT IDENTITY.**  For `s ≤ t` (so every window index `p ≤ s ≤ t`),
    `4·xmomN w (s+1) t  +  dmomN w (s+1) t  ≃  ofNat (t·t) · acN w (s+1) t`,
i.e. `4·⟨x⟩_t + ⟨D²⟩_t = t²` cleared over the mass `A_t`.  (Subtraction-free: `four_x_add_dsq` per
term, then split + scalar pull-out — the exact analogue of `mu_eq`.) -/
theorem dsq_moment_eq (w : Q') (s t : Nat) (h : s ≤ t) :
    (Q'.ofNat 4 * xmomN w (s + 1) t + dmomN w (s + 1) t).eqv
      (Q'.ofNat (t * t) * acN w (s + 1) t) := by
  have hterm : ∀ p, p < s + 1 →
      (Q'.ofNat 4 * (Q'.ofNat (p * (t - p)) * (coeffW w p * coeffW w (t - p)))
        + Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p))).eqv
        (Q'.ofNat (t * t) * (coeffW w p * coeffW w (t - p))) := by
    intro p hp
    have hpt : p ≤ t := by omega
    have hA : (Q'.ofNat 4 * (Q'.ofNat (p * (t - p)) * (coeffW w p * coeffW w (t - p)))).eqv
        (Q'.ofNat (4 * (p * (t - p))) * (coeffW w p * coeffW w (t - p))) :=
      Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 4) (Q'.ofNat (p * (t - p)))
          (coeffW w p * coeffW w (t - p))))
        (Q'.mul_eqv_congr_right _ _ (coeffW w p * coeffW w (t - p))
          (ofNat_mul_base 4 (p * (t - p))))
    have hC : (Q'.ofNat (4 * (p * (t - p))) + Q'.ofNat (dsq p t)).eqv (Q'.ofNat (t * t)) :=
      Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.ofNat_add_eqv (4 * (p * (t - p))) (dsq p t)))
        (Q'.eqv_of_eq (congrArg Q'.ofNat (four_x_add_dsq p t hpt)))
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hA) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.add_mul_eqv (Q'.ofNat (4 * (p * (t - p)))) (Q'.ofNat (dsq p t))
        (coeffW w p * coeffW w (t - p)))) ?_
    exact Q'.mul_eqv_congr_right _ _ (coeffW w p * coeffW w (t - p)) hC
  have h4x : (Q'.ofNat 4 * xmomN w (s + 1) t).eqv
      (fsum (fun p => Q'.ofNat 4 * (Q'.ofNat (p * (t - p)) * (coeffW w p * coeffW w (t - p))))
        (s + 1)) :=
    fsum_const_mul (Q'.ofNat 4)
      (fun p => Q'.ofNat (p * (t - p)) * (coeffW w p * coeffW w (t - p))) (s + 1)
  have hsum : (Q'.ofNat 4 * xmomN w (s + 1) t + dmomN w (s + 1) t).eqv
      (fsum (fun p => Q'.ofNat 4 * (Q'.ofNat (p * (t - p)) * (coeffW w p * coeffW w (t - p)))
        + Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p))) (s + 1)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ h4x) ?_
    exact Q'.eqv_symm (fsum_add
      (fun p => Q'.ofNat 4 * (Q'.ofNat (p * (t - p)) * (coeffW w p * coeffW w (t - p))))
      (fun p => Q'.ofNat (dsq p t) * (coeffW w p * coeffW w (t - p))) (s + 1))
  refine Q'.eqv_trans _ _ _ hsum ?_
  refine Q'.eqv_trans _ _ _ (fsum_eqv_congr_lt _ _ (s + 1) hterm) ?_
  exact Q'.eqv_symm
    (fsum_const_mul (Q'.ofNat (t * t)) (fun p => coeffW w p * coeffW w (t - p)) (s + 1))

/-! ## 3. The `Q'` bridges. -/

/-- Numeric doubling `2·(2·X) ≃ 4·X`. -/
theorem four_eq_two_two (X : Q') :
    (Q'.ofNat 2 * (Q'.ofNat 2 * X)).eqv (Q'.ofNat 4 * X) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) (Q'.ofNat 2) X)) ?_
  exact Q'.mul_eqv_congr_right _ _ X (ofNat_mul_base 2 2)

/-- The moment identity in `2·(2·⟨x⟩)` form: `2·(2·xmomN) + dmomN ≃ ofNat(t²)·acN`. -/
theorem momentTwoTwo (w : Q') (s t : Nat) (h : s ≤ t) :
    (Q'.ofNat 2 * (Q'.ofNat 2 * xmomN w (s + 1) t) + dmomN w (s + 1) t).eqv
      (Q'.ofNat (t * t) * acN w (s + 1) t) :=
  Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ (dmomN w (s + 1) t) (four_eq_two_two (xmomN w (s + 1) t)))
    (dsq_moment_eq w s t h)

/-- **`sqEqv`** — the `Q'` `t²`-second-difference relation
`ofNat(s²) + ofNat((s+2)²) ≃ 2·ofNat((s+1)²) + 2`. -/
theorem sqEqv (s : Nat) :
    (Q'.ofNat (s * s) + Q'.ofNat ((s + 2) * (s + 2))).eqv
      (Q'.ofNat 2 * Q'.ofNat ((s + 1) * (s + 1)) + Q'.ofNat 2) := by
  have hNat : s * s + (s + 2) * (s + 2) = 2 * ((s + 1) * (s + 1)) + 2 := sq_secondDiff_eq_two s
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.ofNat_add_eqv (s * s) ((s + 2) * (s + 2)))) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (congrArg Q'.ofNat hNat)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv (2 * ((s + 1) * (s + 1))) 2) ?_
  exact Q'.add_eqv_congr_right _ _ _ (ofNat_mul_eqv' 2 ((s + 1) * (s + 1)))

/-! ## 4. The exact ring-level covariance recast (pure-`Q'` core). -/

/-- **`msch_iff_dcov_core`** — the abstract ring-level equivalence between the `msch` inequality and
the antidiagonal-variance residual, given the three per-window moment identities (`2·(2·X)+D ≃ c·A`)
and the constant-curvature relation (`cs + c2 ≃ 2·c1 + 2`).  Both directions are proved by adding a
common term, rewriting through the identities, and cancelling (a positive factor `two` and an additive
common term).  All bridging identities are SUBTRACTION-FREE (`ring_qeqv`); the moment/curvature inputs
enter only as congruences.  NO nonnegativity, NO analysis — this is the honest covariance identity. -/
theorem msch_iff_dcov_core
    (A0 A1 A2 X0 X1 X2 P1 P2 D0 D1 D2 cs c1 c2 two : Q')
    (htwo0 : (0 : Q') ≤ two) (htwo_pos : (0 : Q') < two)
    (hM0 : (two * (two * X0) + D0).eqv (cs * A0))
    (hM1 : (two * (two * X1) + D1).eqv (c1 * A1))
    (hM2 : (two * (two * X2) + D2).eqv (c2 * A2))
    (hcas : (cs + c2).eqv (two * c1 + two)) :
    ( two * (X0 * (A1 * A2)) + two * (X2 * (A0 * A1)) + two * (P1 * (A0 * A2))
        ≤ A0 * (A1 * A2) + two * (two * (X1 * (A0 * A2))) + two * (P2 * (A0 * A1)) )
    ↔
    ( two * (D1 * (A0 * A2)) + two * (two * (P1 * (A0 * A2)))
        ≤ D0 * (A1 * A2) + D2 * (A0 * A1) + two * (two * (P2 * (A0 * A1))) ) := by
  have eqvL :
      (two * (two * (X0 * (A1 * A2)) + two * (X2 * (A0 * A1)) + two * (P1 * (A0 * A2)))
        + (D0 * (A1 * A2) + D2 * (A0 * A1) + two * (D1 * (A0 * A2)))).eqv
      ((two * (D1 * (A0 * A2)) + two * (two * (P1 * (A0 * A2))))
        + (two * c1 + two) * (A0 * (A1 * A2))) := by
    have sA :
        (two * (two * (X0 * (A1 * A2)) + two * (X2 * (A0 * A1)) + two * (P1 * (A0 * A2)))
          + (D0 * (A1 * A2) + D2 * (A0 * A1) + two * (D1 * (A0 * A2)))).eqv
        ((two * (two * X0) + D0) * (A1 * A2) + (two * (two * X2) + D2) * (A0 * A1)
          + (two * (two * (P1 * (A0 * A2))) + two * (D1 * (A0 * A2)))) := by ring_qeqv
    have sB :
        ((two * (two * X0) + D0) * (A1 * A2) + (two * (two * X2) + D2) * (A0 * A1)
          + (two * (two * (P1 * (A0 * A2))) + two * (D1 * (A0 * A2)))).eqv
        ((cs * A0) * (A1 * A2) + (c2 * A2) * (A0 * A1)
          + (two * (two * (P1 * (A0 * A2))) + two * (D1 * (A0 * A2)))) :=
      Q'.add_eqv_congr'
        (Q'.add_eqv_congr'
          (Q'.mul_eqv_congr_right _ _ (A1 * A2) hM0)
          (Q'.mul_eqv_congr_right _ _ (A0 * A1) hM2))
        (Q'.eqv_of_eq rfl)
    have sC :
        ((cs * A0) * (A1 * A2) + (c2 * A2) * (A0 * A1)
          + (two * (two * (P1 * (A0 * A2))) + two * (D1 * (A0 * A2)))).eqv
        ((two * (D1 * (A0 * A2)) + two * (two * (P1 * (A0 * A2))))
          + (cs + c2) * (A0 * (A1 * A2))) := by ring_qeqv
    have sD :
        ((two * (D1 * (A0 * A2)) + two * (two * (P1 * (A0 * A2))))
          + (cs + c2) * (A0 * (A1 * A2))).eqv
        ((two * (D1 * (A0 * A2)) + two * (two * (P1 * (A0 * A2))))
          + (two * c1 + two) * (A0 * (A1 * A2))) :=
      Q'.add_eqv_congr_left _ _ _ (Q'.mul_eqv_congr_right _ _ (A0 * (A1 * A2)) hcas)
    exact Q'.eqv_trans _ _ _ sA (Q'.eqv_trans _ _ _ sB (Q'.eqv_trans _ _ _ sC sD))
  have eqvR :
      (two * (A0 * (A1 * A2) + two * (two * (X1 * (A0 * A2))) + two * (P2 * (A0 * A1)))
        + (D0 * (A1 * A2) + D2 * (A0 * A1) + two * (D1 * (A0 * A2)))).eqv
      ((D0 * (A1 * A2) + D2 * (A0 * A1) + two * (two * (P2 * (A0 * A1))))
        + (two * c1 + two) * (A0 * (A1 * A2))) := by
    have sA :
        (two * (A0 * (A1 * A2) + two * (two * (X1 * (A0 * A2))) + two * (P2 * (A0 * A1)))
          + (D0 * (A1 * A2) + D2 * (A0 * A1) + two * (D1 * (A0 * A2)))).eqv
        (two * (A0 * (A1 * A2)) + two * ((two * (two * X1) + D1) * (A0 * A2))
          + (D0 * (A1 * A2) + D2 * (A0 * A1) + two * (two * (P2 * (A0 * A1))))) := by ring_qeqv
    have sB :
        (two * (A0 * (A1 * A2)) + two * ((two * (two * X1) + D1) * (A0 * A2))
          + (D0 * (A1 * A2) + D2 * (A0 * A1) + two * (two * (P2 * (A0 * A1))))).eqv
        (two * (A0 * (A1 * A2)) + two * ((c1 * A1) * (A0 * A2))
          + (D0 * (A1 * A2) + D2 * (A0 * A1) + two * (two * (P2 * (A0 * A1))))) :=
      Q'.add_eqv_congr'
        (Q'.add_eqv_congr' (Q'.eqv_of_eq rfl)
          (Q'.mul_eqv_congr_left two _ _ (Q'.mul_eqv_congr_right _ _ (A0 * A2) hM1)))
        (Q'.eqv_of_eq rfl)
    have sC :
        (two * (A0 * (A1 * A2)) + two * ((c1 * A1) * (A0 * A2))
          + (D0 * (A1 * A2) + D2 * (A0 * A1) + two * (two * (P2 * (A0 * A1))))).eqv
        ((D0 * (A1 * A2) + D2 * (A0 * A1) + two * (two * (P2 * (A0 * A1))))
          + (two * c1 + two) * (A0 * (A1 * A2))) := by ring_qeqv
    exact Q'.eqv_trans _ _ _ sA (Q'.eqv_trans _ _ _ sB sC)
  constructor
  · intro h
    have h2 :
        two * (two * (X0 * (A1 * A2)) + two * (X2 * (A0 * A1)) + two * (P1 * (A0 * A2)))
          ≤ two * (A0 * (A1 * A2) + two * (two * (X1 * (A0 * A2))) + two * (P2 * (A0 * A1))) :=
      Q'.mul_le_mul_of_nonneg_left _ _ two h htwo0
    have h3 := Q'.add_le_add_right _ _
      (D0 * (A1 * A2) + D2 * (A0 * A1) + two * (D1 * (A0 * A2))) h2
    have h4 := le_of_eqvR (le_of_eqvL (Q'.eqv_symm eqvL) h3) eqvR
    exact le_of_add_le_add_right h4
  · intro h
    have h4 := Q'.add_le_add_right _ _ ((two * c1 + two) * (A0 * (A1 * A2))) h
    have h3 := le_of_eqvR (le_of_eqvL eqvL h4) (Q'.eqv_symm eqvR)
    have h2 := le_of_add_le_add_right h3
    exact Q'.le_of_mul_le_mul_left h2 htwo_pos

/-- **`msch_iff_dcov` — THE EXACT RECAST (over the genuine objects).**  The opaque complement-half
inequality `msch` (in the cross-product moment `xmomN`) is EXACTLY the antidiagonal-variance residual
`dcov` (in `dmomN`/`pmomN`).  A ring-level `↔`, both directions, over the genuine `acN`/`xmomN`/`pmomN`
/`dmomN`; no nonnegativity, no analysis. -/
theorem msch_iff_dcov (w : Q') (s : Nat) :
    ( Q'.ofNat 2 * (xmomN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2)))
        + Q'.ofNat 2 * (xmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1)))
        + Q'.ofNat 2 * (pmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2)))
      ≤ acN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))
        + Q'.ofNat 2 * (Q'.ofNat 2
            * (xmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2))))
        + Q'.ofNat 2 * (pmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1))) )
    ↔
    ( Q'.ofNat 2 * (dmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2)))
        + Q'.ofNat 2 * (Q'.ofNat 2
            * (pmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2))))
      ≤ dmomN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))
        + dmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1))
        + Q'.ofNat 2 * (Q'.ofNat 2
            * (pmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1)))) ) :=
  msch_iff_dcov_core
    (acN w (s + 1) s) (acN w (s + 1) (s + 1)) (acN w (s + 1) (s + 2))
    (xmomN w (s + 1) s) (xmomN w (s + 1) (s + 1)) (xmomN w (s + 1) (s + 2))
    (pmomN w (s + 1) (s + 1)) (pmomN w (s + 1) (s + 2))
    (dmomN w (s + 1) s) (dmomN w (s + 1) (s + 1)) (dmomN w (s + 1) (s + 2))
    (Q'.ofNat (s * s)) (Q'.ofNat ((s + 1) * (s + 1))) (Q'.ofNat ((s + 2) * (s + 2)))
    (Q'.ofNat 2)
    (by decide) (by decide)
    (momentTwoTwo w s s (Nat.le_refl s))
    (momentTwoTwo w s (s + 1) (by omega))
    (momentTwoTwo w s (s + 2) (by omega))
    (sqEqv s)

/-! ## 5. The structure-level relocation of the named open leaf. -/

/-- **`DShiftCovResidual w`** — the antidiagonal-variance form of the complement half, cleared over
`acN_s·acN_{s+1}·acN_{s+2}`:

    2·⟨D²⟩_{s+1} + 4·⟨p⟩_{s+1}  ≤  ⟨D²⟩_s + ⟨D²⟩_{s+2} + 4·⟨p⟩_{s+2}.

Exactly equivalent to `MeanShiftComplementHalf` (via `msch_iff_dcov`).  Its irreducible content, after
the `⟨D²⟩ = 4·Var(p) + ⟨D⟩²` split, is a midpoint-concavity / Tate–Zelditch curvature bound on the
tilted position variance — NOT a bare nonnegativity.  NAMED-OPEN (never `sorry`). -/
structure DShiftCovResidual (w : Q') : Type where
  dcov : ∀ s,
    Q'.ofNat 2 * (dmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2)))
        + Q'.ofNat 2 * (Q'.ofNat 2
            * (pmomN w (s + 1) (s + 1) * (acN w (s + 1) s * acN w (s + 1) (s + 2))))
      ≤ dmomN w (s + 1) s * (acN w (s + 1) (s + 1) * acN w (s + 1) (s + 2))
        + dmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1))
        + Q'.ofNat 2 * (Q'.ofNat 2
            * (pmomN w (s + 1) (s + 2) * (acN w (s + 1) s * acN w (s + 1) (s + 1))))

/-- **`mschComplement_of_dcov`** — the antidiagonal-variance residual inhabits the complement-half
leaf (`msch_iff_dcov` backward, per window). -/
def mschComplement_of_dcov {w : Q'} (D : DShiftCovResidual w) : MeanShiftComplementHalf w where
  msch := fun s => (msch_iff_dcov w s).mpr (D.dcov s)

/-- **`dcov_of_mschComplement`** — the complement-half leaf inhabits the antidiagonal-variance
residual (`msch_iff_dcov` forward, per window).  Together with `mschComplement_of_dcov` this shows the
opaque leaf and the transparent covariance residual are INTER-DERIVABLE: the atom is relocated, not
closed. -/
def dcov_of_mschComplement {w : Q'} (M : MeanShiftComplementHalf w) : DShiftCovResidual w where
  dcov := fun s => (msch_iff_dcov w s).mp (M.msch s)

/-! ## 6. Doc-section — PROVED vs. NAMED-open (CRITICAL honesty)

PROVED (axiom-clean, `[propext]` / `[propext, Quot.sound]`):
  * `nat_sq_add`, `sq_two_mul`, `sq_two_add`, `sq_secondDiff_eq_two`, `four_x_add_dsq` — the exact
    `Nat` micro-identities.
  * `dmomN_nonneg`, `dsq_moment_eq` — the antidiagonal-variance moment nonnegativity and THE MOMENT
    IDENTITY `4·⟨x⟩ + ⟨D²⟩ = t²·A`.
  * `four_eq_two_two`, `momentTwoTwo`, `sqEqv` — the `Q'` bridges.
  * `msch_iff_dcov_core`, `msch_iff_dcov` — THE EXACT RECAST `msch ⟺ dcov` (ring-level `↔`).
  * `mschComplement_of_dcov`, `dcov_of_mschComplement` — the structure-level relocation.

NAMED OPEN (Type-level structure, never `sorry`):
  * `DShiftCovResidual w` — the antidiagonal-variance form of the complement half; a midpoint-concavity
    / Tate–Zelditch curvature datum, NOT a nonnegativity.

HONEST VERDICT.  An EXACT covariance identity + reusable moment machinery, NOT a closure.  `msch` is
losslessly relocated onto the antidiagonal-variance residual `dcov`; it is neither discharged nor
reduced to any nonnegativity, and it saturates at the same even-`s`, `w→0` two-point tie.  The Clay
Yang–Mills mass gap remains OPEN. -/

end YMGap.Continuum.MeanComplementCovariance

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MeanComplementCovariance.four_x_add_dsq
#print axioms YMGap.Continuum.MeanComplementCovariance.sq_secondDiff_eq_two
#print axioms YMGap.Continuum.MeanComplementCovariance.dmomN_nonneg
#print axioms YMGap.Continuum.MeanComplementCovariance.dsq_moment_eq
#print axioms YMGap.Continuum.MeanComplementCovariance.momentTwoTwo
#print axioms YMGap.Continuum.MeanComplementCovariance.sqEqv
#print axioms YMGap.Continuum.MeanComplementCovariance.msch_iff_dcov_core
#print axioms YMGap.Continuum.MeanComplementCovariance.msch_iff_dcov
#print axioms YMGap.Continuum.MeanComplementCovariance.mschComplement_of_dcov
#print axioms YMGap.Continuum.MeanComplementCovariance.dcov_of_mschComplement
