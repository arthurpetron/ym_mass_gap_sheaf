/-
Track B / R2 — the **summability capstone**: composing the four proved pieces of
the renormalized bond-moving crack into ONE chain, and instantiating it on the
canonical asymptotic-freedom rate for an UNCONDITIONAL dominant-mode positive
product floor.

# What this module composes (and ONLY composes)

Four already-proved engines are chained here:

  1. The renormalized QUADRATIC defect on the dominant `s = 1` mode, in its
     inverse-square form `δ_ren(w) ≤ C_p·(r·r)` whenever `1 − w ≤ r`.
  2. The asymptotic-freedom rate interface `1 − w_k ≤ A/(k+B)`.
  3. The constructive inverse-square SUMMABILITY endpoint `∑_{k=N}^{N+M} δ ≤
     A/(N+B−1)` for `δ ≤ A·1/(k+B)²`.
  4. The exponential PRODUCT FLOOR `∏(1 − δ_k) ≥ e^{−2R} > 0` from a uniform
     loss-sum bound `∑ δ ≤ R`.

Composed: an AF rate (named or canonical) + the renormalized quadratic defect
gives a per-step INVERSE-SQUARE bound (`renDefect_invSq`); that feeds the
inverse-square summability endpoint, giving a UNIFORM tail bound on the
renormalized defect (`renDefect_summable`); on the tail `k ≥ k₀` where the defect
is `≤ 1/2`, the exponential product floor then yields a strictly POSITIVE floor
for the running product of the renormalized dominant-mode per-block rates
(`renormalized_gap_of_AFRate`).  Instantiated on the canonical AF inhabitant this
is UNCONDITIONAL (`renormalized_gap_canonical`).

# SCOPE — what this is and is NOT (CRITICAL honesty)

This is COMPOSITION of proved pieces.  Its scope is exactly the scope of the
weakest input, the renormalized quadratic defect:

  * DOMINANT MODE ONLY (`s = 1`): the renormalized defect `bondMovingDeltaRen` is
    the `s = 1` transverse residual; the FULL-mode (all `s`) renormalized defect
    is NOT addressed.
  * RENORMALIZED defect: the marginal/linear coupling drift is absorbed by the
    `s = 1` retuning `renormW`; only the genuine transverse `O((1−w)²)` residual
    is bounded.
  * FINITE fusion degree `N` (the dominant-mode value is `N`-independent).
  * TAIL `k ≥ k₀`: the product floor is taken over the tail where the defect has
    dropped below `1/2`; the finite head is honestly excluded.

The FULL-mode (all `s`) renormalized-defect quadratic bound and the uniformity
along the GENUINE 4D asymptotic-freedom trajectory remain the open 4D content.
This module does NOT solve 4D Yang–Mills.  It shows that the marginal/quadratic
SEPARATION makes the dominant-mode renormalized defect genuinely SUMMABLE, and
that summability closes the product-floor chain on that mode — including
UNCONDITIONALLY on the canonical (non-4D) AF inhabitant.

# An honest offset adapter

The summability endpoint uses an INTEGER offset `B' ≥ 2`; the AF rate carries a
`Q'` offset `B`.  We align them to the fixed integer offset `B' = 2` and absorb
the mismatch into the rate constant: the per-step bound becomes
`δ_ren ≤ C_p·(M·A)²·1/(k+2)²` with the integer inflation `M = 2·B.den` (chosen so
`2 ≤ M·B`, hence `(k+2) ≤ M·(k+B)`).  This constant inflation is stated openly and
costs nothing analytically (it is a fixed finite factor).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure composition over `Q'`/`Nat`; every load-bearing declaration is gated with
`#print axioms` (permitted: `propext` / `Quot.sound`).  No `Classical.*`, no
`native_decide`, no `sorry`.  All constants and moduli are `Type`-level data.
-/

import YMGap.Continuum.AFRateCalibration
import YMGap.Continuum.BondMovingQuadratic
import YMGap.Continuum.SummableInverseSquare
import YMGap.Continuum.ExpProductFloor

namespace YMGap.Continuum.SummabilityCapstone

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.BondMovingQuadratic
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.ProductFloor
open YMGap.Continuum.ExpProductFloor

/-! ## 0. Abbreviations: the quadratic constant, the rate-scaled term, the defect

`Cp p` is the renormalized quadratic-defect constant `p·dimQ 1·C₄(1)² = 18p` from
`bondMovingDeltaRen_quadratic`.  We bound the per-step defect along an AF rate by
a fixed-offset (`B' = 2`) inverse-square majorant. -/

/-- The renormalized quadratic-defect constant `C_p = p·dimQ 1·C₄(1)² = 18p`. -/
def Cp (p : Nat) : Q' := Q'.ofNat p * (dimQ 1 * (Q'.ofNat (c4 1) * Q'.ofNat (c4 1)))

theorem Cp_nonneg (p : Nat) : (0 : Q') ≤ Cp p :=
  Q'.mul_nonneg _ _ (zero_le_ofNat p)
    (Q'.mul_nonneg _ _ (dimQ_nonneg 1)
      (Q'.mul_nonneg _ _ (zero_le_ofNat (c4 1)) (zero_le_ofNat (c4 1))))

/-- The integer offset-inflation factor `M = 2·B.den`: chosen so that `2 ≤ M·B`
(hence `(k+2) ≤ M·(k+B)`), aligning the `Q'` rate offset `B` to the integer
endpoint offset `B' = 2`. -/
def inflM (afr : AFRateModulus) : Nat := 2 * afr.B.den

/-- `1 ≤ inflM afr` (`B.den ≥ 1`). -/
theorem inflM_ge_one (afr : AFRateModulus) : 1 ≤ inflM afr := by
  show 1 ≤ 2 * afr.B.den
  have := afr.B.den_pos
  omega

/-- The second denominator `k + 2` as a `Q'` (the integer endpoint offset). -/
def harmDen2 (k : Nat) : Q' := Q'.ofNat k + Q'.ofNat 2

/-! ## 1. The offset adapter — `2 ≤ M·B`, then `(k+2) ≤ M·(k+B)` -/

/-- `2 ≤ M·B` with `M = 2·B.den`: at the cross-product level
`2·B.den ≤ (2·B.den)·B.num`, true since `B.num ≥ 1`. -/
theorem two_le_inflM_mul_B (afr : AFRateModulus) :
    Q'.ofNat 2 ≤ Q'.ofNat (inflM afr) * afr.B := by
  have hbn : 1 ≤ afr.B.num := Q'.num_pos_of_pos afr.B_pos
  -- cross product: (ofNat 2).num·(M·B).den ≤ (M·B).num·(ofNat 2).den.
  show (Q'.ofNat 2).num * ((Q'.ofNat (inflM afr) * afr.B).den : Int)
      ≤ (Q'.ofNat (inflM afr) * afr.B).num * ((Q'.ofNat 2).den : Int)
  -- (ofNat 2).num = 2, (ofNat 2).den = 1.
  have h2n : (Q'.ofNat 2).num = 2 := rfl
  have h2d : ((Q'.ofNat 2).den : Int) = 1 := rfl
  -- (M·B).num = M·B.num ; (M·B).den = 1·B.den = B.den.
  have hmbn : (Q'.ofNat (inflM afr) * afr.B).num
      = ((inflM afr : Nat) : Int) * afr.B.num := by
    show (Q'.ofNat (inflM afr)).num * afr.B.num = ((inflM afr : Nat) : Int) * afr.B.num
    rfl
  have hmbd : ((Q'.ofNat (inflM afr) * afr.B).den : Int) = (afr.B.den : Int) := by
    show (((Q'.ofNat (inflM afr)).den * afr.B.den : Nat) : Int) = (afr.B.den : Int)
    have : (Q'.ofNat (inflM afr)).den = 1 := rfl
    rw [this, Nat.one_mul]
  rw [h2n, h2d, hmbn, hmbd, Int.mul_one]
  -- 2·B.den ≤ (M = 2·B.den)·B.num.
  show (2 : Int) * (afr.B.den : Int)
      ≤ ((2 * afr.B.den : Nat) : Int) * afr.B.num
  have hMcast : ((2 * afr.B.den : Nat) : Int) = 2 * (afr.B.den : Int) := by
    push_cast; rfl
  rw [hMcast]
  have hdpos : (0 : Int) < (afr.B.den : Int) := by exact_mod_cast afr.B.den_pos
  -- 2·B.den · 1 ≤ 2·B.den · B.num  (B.num ≥ 1)
  have hdnn : (0 : Int) ≤ 2 * (afr.B.den : Int) := by omega
  have hstep : (2 : Int) * (afr.B.den : Int) * 1 ≤ 2 * (afr.B.den : Int) * afr.B.num :=
    Int.mul_le_mul_of_nonneg_left hbn hdnn
  rw [Int.mul_one] at hstep
  exact hstep

/-- The core adapter inequality `(k+2) ≤ M·(k+B)`, i.e.
`harmDen2 k ≤ ofNat M · harmDen B k`.  From `k ≤ M·k` (`M ≥ 1`) and
`2 ≤ M·B`. -/
theorem harmDen2_le_inflM_harmDen (afr : AFRateModulus) (k : Nat) :
    harmDen2 k ≤ Q'.ofNat (inflM afr) * harmDen afr.B k := by
  -- ofNat M · harmDen B k = ofNat M · (ofNat k + B) ≃ ofNat M·ofNat k + ofNat M·B.
  have hdist : (Q'.ofNat (inflM afr) * harmDen afr.B k).eqv
      (Q'.ofNat (inflM afr) * Q'.ofNat k + Q'.ofNat (inflM afr) * afr.B) := by
    show (Q'.ofNat (inflM afr) * (Q'.ofNat k + afr.B)).eqv
        (Q'.ofNat (inflM afr) * Q'.ofNat k + Q'.ofNat (inflM afr) * afr.B)
    exact Q'.mul_add_eqv (Q'.ofNat (inflM afr)) (Q'.ofNat k) afr.B
  -- k ≤ M·k : ofNat k ≤ ofNat M · ofNat k.
  have hk : Q'.ofNat k ≤ Q'.ofNat (inflM afr) * Q'.ofNat k := by
    -- ofNat k ≃ ofNat (1·k) = ofNat (1*k) ≤ ofNat (M*k) ≃ ofNat M · ofNat k.
    have he1 : (Q'.ofNat k).eqv (Q'.ofNat (1 * k)) := by
      rw [Nat.one_mul]; exact Q'.eqv_refl _
    have hle : Q'.ofNat (1 * k) ≤ Q'.ofNat (inflM afr * k) := by
      apply CReal.ofNat_le_ofNat
      have hpos : 0 < inflM afr := inflM_ge_one afr
      have hkm : k ≤ inflM afr * k := Nat.le_mul_of_pos_left k hpos
      omega
    have he2 : (Q'.ofNat (inflM afr * k)).eqv (Q'.ofNat (inflM afr) * Q'.ofNat k) :=
      ofNat_mul_eqv (inflM afr) k
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he1)
      (Q'.le_trans' _ _ _ hle (Q'.le_of_eqv he2))
  -- 2 ≤ M·B.
  have h2 : Q'.ofNat 2 ≤ Q'.ofNat (inflM afr) * afr.B := two_le_inflM_mul_B afr
  -- harmDen2 k = ofNat k + ofNat 2 ≤ M·k + M·B ≃ M·(k+B).
  have hsum : harmDen2 k ≤ Q'.ofNat (inflM afr) * Q'.ofNat k + Q'.ofNat (inflM afr) * afr.B :=
    q_add_le_add hk h2
  exact Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv hdist)

/-! ## 2. The per-step inverse-square defect along an AF rate

`renDefect afr p k = bondMovingDeltaRen N p (afr.w k)` (the dominant-mode value is
`N`-independent; we carry `N = 1`).  Chaining the AF rate `1 − w_k ≤ A/(k+B)` with
the offset adapter gives `1 − w_k ≤ (M·A)·1/(k+2)`, hence the inverse-square form
`δ_ren ≤ C_p·(M·A)²·1/(k+2)²`. -/

/-- The renormalized dominant-mode defect along the AF trajectory:
`δ_ren(w_k)`.  Carries `N = 1` (the dominant-mode value is `N`-independent). -/
def renDefect (afr : AFRateModulus) (p : Nat) (k : Nat) : Q' :=
  bondMovingDeltaRen 1 p (afr.w k)

theorem renDefect_nonneg (afr : AFRateModulus) (p : Nat) (k : Nat) :
    (0 : Q') ≤ renDefect afr p k :=
  bondMovingDeltaRen_nonneg (afr.w_nonneg k) (Q'.le_of_lt (afr.w_lt_one k)) 1 p

/-- The rate-scaled inverse-square term constant `A_scaled = M·A` and the term
`A_scaled · 1/(k+2)`.  We prove the rate margin is dominated by it. -/
def rateScaled (afr : AFRateModulus) : Q' := Q'.ofNat (inflM afr) * afr.A

theorem rateScaled_nonneg (afr : AFRateModulus) : (0 : Q') ≤ rateScaled afr :=
  Q'.mul_nonneg _ _ (zero_le_ofNat (inflM afr)) (Q'.le_of_lt afr.A_pos)

/-- `harmDen2 k > 0`. -/
theorem harmDen2_pos (k : Nat) : (0 : Q') < harmDen2 k := by
  show (0 : Q') < Q'.ofNat k + Q'.ofNat 2
  have h : (0 : Q') < Q'.ofNat 2 + Q'.ofNat k :=
    Q'.pos_add_nonneg (by decide) (zero_le_ofNat k)
  exact lt_of_lt_of_le h (Q'.le_of_eqv (Q'.add_comm_eqv (Q'.ofNat 2) (Q'.ofNat k)))

/-- **The margin is dominated by the fixed-offset scaled term.**
`1 − w_k ≤ (M·A)·1/(k+2) = divPos (M·A) (k+2)`.  From the AF rate
`1 − w_k ≤ A/(k+B)` and the adapter `(k+2) ≤ M·(k+B)`. -/
theorem margin_le_scaled (afr : AFRateModulus) (k : Nat) :
    (1 : Q') - afr.w k
      ≤ Q'.divPos (rateScaled afr) (harmDen2 k) (harmDen2_pos k) := by
  -- 1 − w_k ≤ divPos A (harmDen B k) ≤ divPos (M·A) (harmDen2 k).
  have hrate : (1 : Q') - afr.w k
      ≤ Q'.divPos afr.A (harmDen afr.B k) (harmDen_pos afr.B_pos k) :=
    afr.rate_upper k
  -- divPos A (harmDen B k) ≤ divPos (M·A) (harmDen2 k):
  --   by divPos_le_of_le_mul, suffices A ≤ divPos(M·A)(harmDen2 k) · harmDen B k.
  refine Q'.le_trans' _ _ _ hrate ?_
  refine Q'.divPos_le_of_le_mul afr.A (harmDen afr.B k) (harmDen_pos afr.B_pos k) ?_
  -- A ≤ divPos(M·A)(harmDen2 k) · harmDen B k.
  -- Let D := divPos(M·A)(harmDen2 k).  Have D·harmDen2 k ≃ M·A.
  -- Cross strategy: A·harmDen2 k ≤ (M·A)·harmDen B k ≃ (D·harmDen B k)·harmDen2 k,
  -- then cancel harmDen2 k > 0.
  let D := Q'.divPos (rateScaled afr) (harmDen2 k) (harmDen2_pos k)
  -- hcross : A·harmDen2 k ≤ (M·A)·harmDen B k.
  have hcross : afr.A * harmDen2 k ≤ rateScaled afr * harmDen afr.B k := by
    -- A·harmDen2 k ≤ A·(M·harmDen B k)  (harmDen2 k ≤ M·harmDen B k, mult A ≥ 0 left)
    have h1 : afr.A * harmDen2 k
        ≤ afr.A * (Q'.ofNat (inflM afr) * harmDen afr.B k) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (harmDen2_le_inflM_harmDen afr k)
        (Q'.le_of_lt afr.A_pos)
    -- A·(M·harmDen B k) ≃ (A·M)·harmDen B k ≃ (M·A)·harmDen B k = rateScaled·harmDen B k
    have h2 : (afr.A * (Q'.ofNat (inflM afr) * harmDen afr.B k)).eqv
        (rateScaled afr * harmDen afr.B k) := by
      refine Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.mul_assoc_eqv afr.A (Q'.ofNat (inflM afr)) (harmDen afr.B k))) ?_
      exact Q'.mul_eqv_congr_right _ _ (harmDen afr.B k)
        (Q'.mul_comm_eqv afr.A (Q'.ofNat (inflM afr)))
    exact Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h2)
  -- (M·A)·harmDen B k ≃ (D·harmDen B k)·harmDen2 k.
  have hDeq : (rateScaled afr).eqv (D * harmDen2 k) :=
    Q'.eqv_symm (Q'.divPos_mul_eqv (rateScaled afr) (harmDen2 k) (harmDen2_pos k))
  have hrhs : (rateScaled afr * harmDen afr.B k).eqv ((D * harmDen afr.B k) * harmDen2 k) := by
    -- (M·A)·harmDen B k ≃ (D·harmDen2 k)·harmDen B k ≃ (D·harmDen B k)·harmDen2 k.
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ (harmDen afr.B k) hDeq) ?_
    -- (D·harmDen2 k)·harmDen B k ≃ D·(harmDen2 k·harmDen B k) ≃ D·(harmDen B k·harmDen2 k)
    --   ≃ (D·harmDen B k)·harmDen2 k.
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv D (harmDen2 k) (harmDen afr.B k)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left D _ _ (Q'.mul_comm_eqv (harmDen2 k) (harmDen afr.B k))) ?_
    exact Q'.eqv_symm (Q'.mul_assoc_eqv D (harmDen afr.B k) (harmDen2 k))
  -- A·harmDen2 k ≤ (D·harmDen B k)·harmDen2 k, cancel harmDen2 k > 0.
  have hfinal : afr.A * harmDen2 k ≤ (D * harmDen afr.B k) * harmDen2 k :=
    Q'.le_trans' _ _ _ hcross (Q'.le_of_eqv hrhs)
  exact q_le_of_mul_le_mul_right afr.A (D * harmDen afr.B k) (harmDen2 k)
    (harmDen2_pos k) hfinal

/-! ## 3. The per-step inverse-square majorant — `renDefect_invSq`

`δ_ren(w_k) ≤ C_p·(r·r)` (from `bondMovingDeltaRen_invSq`, with `r` the scaled
margin), and `r·r ≤ rateScaled²·invSqTerm 2 k` (both equal `(M·A)²/(k+2)²`,
proved by cancelling the positive `(k+2)²`).  Hence the fixed-offset (`B' = 2`)
inverse-square bound the summability endpoint consumes:

    renDefect afr p k  ≤  (C_p · rateScaled²) · invSqTerm 2 k. -/

/-- The per-step inverse-square constant `Aconst = C_p·(M·A)² = 18p·(M·A)²`. -/
def Aconst (afr : AFRateModulus) (p : Nat) : Q' :=
  Cp p * (rateScaled afr * rateScaled afr)

theorem Aconst_nonneg (afr : AFRateModulus) (p : Nat) : (0 : Q') ≤ Aconst afr p :=
  Q'.mul_nonneg _ _ (Cp_nonneg p)
    (Q'.mul_nonneg _ _ (rateScaled_nonneg afr) (rateScaled_nonneg afr))

/-- `(r·r)·(D·D) ≃ a·a` for `r = divPos a D`, `D = harmDen2 k`. -/
theorem rr_mul_DD_eqv (afr : AFRateModulus) (k : Nat) :
    (((Q'.divPos (rateScaled afr) (harmDen2 k) (harmDen2_pos k))
        * (Q'.divPos (rateScaled afr) (harmDen2 k) (harmDen2_pos k)))
      * (harmDen2 k * harmDen2 k)).eqv (rateScaled afr * rateScaled afr) := by
  let a := rateScaled afr
  let hpos := harmDen2_pos k
  have hXD : (Q'.divPos a (harmDen2 k) hpos * harmDen2 k).eqv a :=
    Q'.divPos_mul_eqv a (harmDen2 k) hpos
  have hregroup :
      (((Q'.divPos a (harmDen2 k) hpos) * (Q'.divPos a (harmDen2 k) hpos))
          * (harmDen2 k * harmDen2 k)).eqv
        ((Q'.divPos a (harmDen2 k) hpos * harmDen2 k)
          * (Q'.divPos a (harmDen2 k) hpos * harmDen2 k)) := by
    show (((Q'.divPos a (harmDen2 k) hpos * Q'.divPos a (harmDen2 k) hpos)
          * (harmDen2 k * harmDen2 k)).num
        * (((Q'.divPos a (harmDen2 k) hpos * harmDen2 k)
            * (Q'.divPos a (harmDen2 k) hpos * harmDen2 k)).den : Int))
      = (((Q'.divPos a (harmDen2 k) hpos * harmDen2 k)
          * (Q'.divPos a (harmDen2 k) hpos * harmDen2 k)).num
        * (((Q'.divPos a (harmDen2 k) hpos * Q'.divPos a (harmDen2 k) hpos)
            * (harmDen2 k * harmDen2 k)).den : Int))
    simp only [Q'.mul_num_cast, Q'.mul_den_cast]
    push_cast
    ac_rfl
  refine Q'.eqv_trans _ _ _ hregroup ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hXD)
    (Q'.mul_eqv_congr_left a _ _ hXD)

/-- `invSqTerm 2 k · (D·D) ≃ 1` for `D = harmDen2 k`: `1/(k+2)² · (k+2)² ≃ 1`. -/
theorem invSqTerm_mul_DD_eqv (k : Nat) :
    (invSqTerm 2 (by decide) k * (harmDen2 k * harmDen2 k)).eqv 1 := by
  have hDnum : (harmDen2 k).num = ((k + 2 : Nat) : Int) := by
    show (Q'.ofNat k).num * ((Q'.ofNat 2).den : Int)
        + (Q'.ofNat 2).num * ((Q'.ofNat k).den : Int) = ((k + 2 : Nat) : Int)
    have e1 : (Q'.ofNat k).num = (k : Int) := rfl
    have e2 : ((Q'.ofNat 2).den : Int) = 1 := rfl
    have e3 : (Q'.ofNat 2).num = 2 := rfl
    have e4 : ((Q'.ofNat k).den : Int) = 1 := rfl
    rw [e1, e2, e3, e4, Int.mul_one, Int.mul_one]
    push_cast; omega
  have hDden : (harmDen2 k).den = 1 := rfl
  show (invSqTerm 2 (by decide) k * (harmDen2 k * harmDen2 k)).num * ((1 : Q').den : Int)
      = (1 : Q').num * ((invSqTerm 2 (by decide) k * (harmDen2 k * harmDen2 k)).den : Int)
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]
  rw [Q'.mul_num_cast, Q'.mul_den_cast, Q'.mul_num_cast, Q'.mul_den_cast]
  have hUn : (invSqTerm 2 (by decide) k).num = 1 := rfl
  have hUd : (invSqTerm 2 (by decide) k).den = (k + 2) * (k + 2) := rfl
  rw [hUn, hDnum, hDden, hUd]
  push_cast
  ac_rfl

/-- The square of the scaled margin is `≤ rateScaled² · invSqTerm 2 k`
(equal, in fact — both are `(M·A)²/(k+2)²`; the inequality is the form the
majorant needs).  Proved by multiplying by the positive `(D·D)` and cancelling. -/
theorem scaledMargin_sq_le_invSq (afr : AFRateModulus) (k : Nat) :
    (Q'.divPos (rateScaled afr) (harmDen2 k) (harmDen2_pos k))
        * (Q'.divPos (rateScaled afr) (harmDen2 k) (harmDen2_pos k))
      ≤ (rateScaled afr * rateScaled afr) * invSqTerm 2 (by decide) k := by
  let a := rateScaled afr
  have hDD_pos : (0 : Q') < harmDen2 k * harmDen2 k :=
    Q'.mul_pos (harmDen2_pos k) (harmDen2_pos k)
  have hRHS_DD : (((a * a) * invSqTerm 2 (by decide) k) * (harmDen2 k * harmDen2 k)).eqv
      (a * a) := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv (a * a) (invSqTerm 2 (by decide) k) (harmDen2 k * harmDen2 k)) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (a * a) _ _ (invSqTerm_mul_DD_eqv k)) ?_
    exact Q'.mul_one_eqv (a * a)
  have hLHS_DD := rr_mul_DD_eqv afr k
  have hle : ((Q'.divPos a (harmDen2 k) (harmDen2_pos k))
        * (Q'.divPos a (harmDen2 k) (harmDen2_pos k))) * (harmDen2 k * harmDen2 k)
      ≤ ((a * a) * invSqTerm 2 (by decide) k) * (harmDen2 k * harmDen2 k) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS_DD) (Q'.ge_of_eqv hRHS_DD)
  exact q_le_of_mul_le_mul_right _ _ (harmDen2 k * harmDen2 k) hDD_pos hle

/-- **The per-step inverse-square defect bound.**  Along an AF rate,

    renDefect afr p k  ≤  Aconst afr p · invSqTerm 2 k   ( = 18p·(M·A)²·1/(k+2)² ),

composing `bondMovingDeltaRen_invSq` with the offset adapter `margin_le_scaled`
and the square-to-inverse-square bound. -/
theorem renDefect_invSq (afr : AFRateModulus) (p : Nat) (k : Nat) :
    renDefect afr p k ≤ Aconst afr p * invSqTerm 2 (by decide) k := by
  let r := Q'.divPos (rateScaled afr) (harmDen2 k) (harmDen2_pos k)
  have hquad : renDefect afr p k ≤ Cp p * (r * r) :=
    bondMovingDeltaRen_invSq (afr.w_nonneg k) (Q'.le_of_lt (afr.w_lt_one k))
      (margin_le_scaled afr k) 1 p
  have hmul : Cp p * (r * r)
      ≤ Cp p * ((rateScaled afr * rateScaled afr) * invSqTerm 2 (by decide) k) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ (scaledMargin_sq_le_invSq afr k) (Cp_nonneg p)
  have hassoc : (Cp p * ((rateScaled afr * rateScaled afr) * invSqTerm 2 (by decide) k)).eqv
      (Aconst afr p * invSqTerm 2 (by decide) k) :=
    Q'.eqv_symm
      (Q'.mul_assoc_eqv (Cp p) (rateScaled afr * rateScaled afr) (invSqTerm 2 (by decide) k))
  exact Q'.le_trans' _ _ _ hquad (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv hassoc))

/-! ## 4. Summability of the renormalized defect — `renDefect_summable`

The inverse-square per-step bound feeds `summableBound_of_invSq` (offset `B' = 2`):
every tail window of the renormalized defect is bounded by `Aconst·pot 2 N =
Aconst/(N+1)`.  The total-defect bound on the tail `k ≥ k₀` is the single constant
`R(k₀) = Aconst·pot 2 k₀ = Aconst/(k₀+1)`. -/

/-- **The uniform tail bound for the renormalized defect.**
`∑_{k=N}^{N+M} renDefect ≤ Aconst·pot 2 N` for every window `(N, M)`. -/
theorem renDefect_summable (afr : AFRateModulus) (p : Nat) (N M : Nat) :
    tailSum (renDefect afr p) N M ≤ Aconst afr p * pot 2 (by decide) N :=
  summableBound_of_invSq 2 (by decide) (Aconst afr p) (Aconst_nonneg afr p)
    (renDefect afr p) (renDefect_invSq afr p) N M

/-! ## 5. The tail product floor — restricting to `k ≥ k₀` where `δ_ren ≤ 1/2`

The renormalized defect → 0, so for large `k` it drops below `1/2`.  We restrict to
the tail `k ≥ k₀` (the finite head is honestly excluded), with
`k₀ = 2·Aconst.num.toNat`, where `renDefect k ≤ Aconst·1/(k+2)² ≤ Aconst·1/(k+2) ≤
1/2`.  The shifted rate `ρ_j = 1 − renDefect(k₀+j)` then feeds
`sum_loss_to_productFloor_exp`. -/

/-- The defect head-cutoff `k₀ = 2·Aconst.num.toNat`: for `k ≥ k₀`,
`renDefect k ≤ 1/2`. -/
def defectCutoff (afr : AFRateModulus) (p : Nat) : Nat := 2 * (Aconst afr p).num.toNat

/-- For `k ≥ k₀`, the renormalized defect is `≤ 1/2`.  Chain:
`renDefect ≤ Aconst·1/(k+2)² ≤ Aconst·1/(k+2) ≤ 1/2` (the last from
`2·Aconst.num ≤ k+2`). -/
theorem renDefect_le_half (afr : AFRateModulus) (p : Nat) {k : Nat}
    (hk : defectCutoff afr p ≤ k) :
    renDefect afr p k ≤ HalfPow.half := by
  have hAnn : (0 : Q') ≤ Aconst afr p := Aconst_nonneg afr p
  have hAnum : 0 ≤ (Aconst afr p).num := (Q'.zero_le_iff_num_nonneg _).mp hAnn
  -- renDefect ≤ Aconst·invSqTerm 2 k.
  have h1 : renDefect afr p k ≤ Aconst afr p * invSqTerm 2 (by decide) k :=
    renDefect_invSq afr p k
  -- invSqTerm 2 k ≤ unit (k+2) : 1/(k+2)² ≤ 1/(k+2).
  have hk2 : 0 < k + 2 := by omega
  have hk2sq : 0 < (k + 2) * (k + 2) := Nat.mul_pos hk2 hk2
  have hanti : unit ((k + 2) * (k + 2)) hk2sq ≤ unit (k + 2) hk2 := by
    refine unit_antitone hk2 hk2sq ?_
    calc k + 2 = (k + 2) * 1 := by omega
      _ ≤ (k + 2) * (k + 2) := Nat.mul_le_mul_left (k + 2) (by omega)
  have h2 : Aconst afr p * invSqTerm 2 (by decide) k ≤ Aconst afr p * unit (k + 2) hk2 := by
    show Aconst afr p * unit ((k + 2) * (k + 2)) _ ≤ Aconst afr p * unit (k + 2) hk2
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hanti hAnn
  -- Aconst·unit(k+2) ≤ half : cross product 2·Aconst.num ≤ Aconst.den·(k+2).
  have h3 : Aconst afr p * unit (k + 2) hk2 ≤ HalfPow.half := by
    show (Aconst afr p * unit (k + 2) hk2).num * (HalfPow.half.den : Int)
        ≤ HalfPow.half.num * ((Aconst afr p * unit (k + 2) hk2).den : Int)
    have hhn : HalfPow.half.num = 1 := rfl
    have hhd : (HalfPow.half.den : Int) = 2 := rfl
    rw [hhn, hhd, Int.one_mul]
    -- (A·unit).num = A.num·1 = A.num ; (A·unit).den = A.den·(k+2).
    have hLn : (Aconst afr p * unit (k + 2) hk2).num = (Aconst afr p).num := by
      show (Aconst afr p).num * (unit (k + 2) hk2).num = (Aconst afr p).num
      rw [unit_num, Int.mul_one]
    have hLd : ((Aconst afr p * unit (k + 2) hk2).den : Int)
        = ((Aconst afr p).den : Int) * ((k + 2 : Nat) : Int) := by
      rw [Q'.mul_den_cast, unit_den]
    rw [hLn, hLd]
    -- A.num·2 ≤ A.den·(k+2).  Have k ≥ 2·A.num.toNat, A.den ≥ 1, A.num ≥ 0.
    have htoNat : ((Aconst afr p).num.toNat : Int) = (Aconst afr p).num :=
      Int.toNat_of_nonneg hAnum
    have hkge : 2 * (Aconst afr p).num.toNat ≤ k := hk
    have hden1 : (1 : Int) ≤ ((Aconst afr p).den : Int) := by
      have := (Aconst afr p).den_pos; exact_mod_cast this
    -- 2·A.num ≤ (k+2) ≤ A.den·(k+2).
    have hstepA : (Aconst afr p).num * 2 ≤ ((k + 2 : Nat) : Int) := by
      have hc : (2 * (Aconst afr p).num.toNat : Nat) ≤ k + 2 := by omega
      have hc' : ((2 * (Aconst afr p).num.toNat : Nat) : Int) ≤ ((k + 2 : Nat) : Int) := by
        exact_mod_cast hc
      have : ((2 * (Aconst afr p).num.toNat : Nat) : Int) = (Aconst afr p).num * 2 := by
        push_cast [htoNat]; omega
      rw [this] at hc'; exact hc'
    have hkpos : (0 : Int) ≤ ((k + 2 : Nat) : Int) := by exact_mod_cast Nat.zero_le _
    have hstepB : ((k + 2 : Nat) : Int) ≤ ((Aconst afr p).den : Int) * ((k + 2 : Nat) : Int) := by
      have := Int.mul_le_mul_of_nonneg_right hden1 hkpos
      rwa [Int.one_mul] at this
    exact Int.le_trans hstepA hstepB
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 h3)

/-- The shifted (tail) renormalized per-block rate `ρ_j = 1 − renDefect(k₀+j)`. -/
def tailRate (afr : AFRateModulus) (p k0 : Nat) (j : Nat) : Q' :=
  1 - renDefect afr p (k0 + j)

/-- `lossSum (renDefect∘(k₀+·)) n = tailSum renDefect k₀ n` (both recursions add
`renDefect (k₀+n)` at the step). -/
theorem lossSum_shift_eq (afr : AFRateModulus) (p k0 : Nat) :
    ∀ n, lossSum (fun j => renDefect afr p (k0 + j)) n = tailSum (renDefect afr p) k0 n
  | 0 => rfl
  | n + 1 => by
    show lossSum (fun j => renDefect afr p (k0 + j)) n + renDefect afr p (k0 + n)
        = tailSum (renDefect afr p) k0 n + renDefect afr p (k0 + n)
    rw [lossSum_shift_eq afr p k0 n]

/-- `1 − tailRate j ≃ renDefect (k₀+j)` (from `1 − (1 − x) ≃ x`). -/
theorem one_sub_tailRate_eqv (afr : AFRateModulus) (p k0 j : Nat) :
    ((1 : Q') - tailRate afr p k0 j).eqv (renDefect afr p (k0 + j)) :=
  one_sub_one_sub_eqv (renDefect afr p (k0 + j))

/-- `lossSum (1 − tailRate) n ≃ lossSum (renDefect∘(k₀+·)) n` (termwise eqv lifts
through the `Q'` sum). -/
theorem lossSum_oneSub_tailRate_eqv (afr : AFRateModulus) (p k0 : Nat) :
    ∀ n, (lossSum (fun j => 1 - tailRate afr p k0 j) n).eqv
      (lossSum (fun j => renDefect afr p (k0 + j)) n)
  | 0 => Q'.eqv_refl 0
  | n + 1 => by
    show (lossSum (fun j => 1 - tailRate afr p k0 j) n + (1 - tailRate afr p k0 n)).eqv
        (lossSum (fun j => renDefect afr p (k0 + j)) n + renDefect afr p (k0 + n))
    exact Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (1 - tailRate afr p k0 n)
        (lossSum_oneSub_tailRate_eqv afr p k0 n))
      (Q'.add_eqv_congr_left _ _ _ (one_sub_tailRate_eqv afr p k0 n))

/-- The tail total-defect bound `R(k₀) = Aconst·pot 2 k₀`. -/
def tailR (afr : AFRateModulus) (p k0 : Nat) : Q' := Aconst afr p * pot 2 (by decide) k0

/-- `lossSum (1 − tailRate) n ≤ R(k₀)` for all `n` (the tail loss sum is the
defect's tailSum, bounded by `renDefect_summable`). -/
theorem lossSum_tailRate_le (afr : AFRateModulus) (p k0 : Nat) (n : Nat) :
    lossSum (fun j => 1 - tailRate afr p k0 j) n ≤ tailR afr p k0 := by
  have heqv : (lossSum (fun j => 1 - tailRate afr p k0 j) n).eqv
      (tailSum (renDefect afr p) k0 n) := by
    refine Q'.eqv_trans _ _ _ (lossSum_oneSub_tailRate_eqv afr p k0 n) ?_
    exact Q'.eqv_of_eq (lossSum_shift_eq afr p k0 n)
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv) ?_
  exact renDefect_summable afr p k0 n

/-! ## 6. The capstone theorems — conditional and unconditional -/

/-- **The conditional capstone.**  Along ANY AF rate `afr` (and any bond-moving
multiplicity `p`), the running product of the renormalized dominant-mode per-block
rates `ρ_j = 1 − δ_ren(w_{k₀+j})` over the tail `k ≥ k₀` has a STRICTLY POSITIVE
floor: there is a constructive-real constant `floor` with a positive rational
lower bound `ε > 0`, and `floor ≤ ∏_{j<n} ρ_j` for every prefix `n`.

This composes: AF rate ⇒ renormalized quadratic defect (PROVED, dominant `s = 1`
mode) ⇒ inverse-square per-step (`renDefect_invSq`) ⇒ summable
(`renDefect_summable`) ⇒ exponential product floor `e^{−2R} > 0`
(`sum_loss_to_productFloor_exp`).  SCOPE: dominant `s = 1` mode; renormalized
defect (marginal flow absorbed by `renormW`); finite fusion degree `N = 1`; tail
`k ≥ k₀ = defectCutoff afr p`.  The floor is on `RGGapPersistence.prodPrefix` of
the tail renormalized rates. -/
def renormalized_gap_of_AFRate (afr : AFRateModulus) (p : Nat) :
    Σ' (floor : CReal) (ε : Q'),
      (0 : Q') < ε ∧ ExpPos.geRat floor ε
      ∧ ∀ n, CReal.leRat floor
          (RGGapPersistence.prodPrefix (tailRate afr p (defectCutoff afr p)) n) := by
  let k0 := defectCutoff afr p
  -- tail rates: 0 ≤ ρ_j ≤ 1, and 1 − ρ_j ≤ 1/2.
  have hρ0 : ∀ j, (0 : Q') ≤ tailRate afr p k0 j := by
    intro j
    -- 0 ≤ 1 − renDefect(k0+j)  ⟸  renDefect(k0+j) ≤ 1 (since ≤ 1/2 ≤ 1).
    show (0 : Q') ≤ 1 - renDefect afr p (k0 + j)
    have hhalf : renDefect afr p (k0 + j) ≤ HalfPow.half :=
      renDefect_le_half afr p (by omega)
    have hle1 : renDefect afr p (k0 + j) ≤ 1 :=
      Q'.le_trans' _ _ _ hhalf (by decide)
    have hstep := Q'.add_le_add_right (renDefect afr p (k0 + j)) 1 (-(renDefect afr p (k0 + j))) hle1
    refine Q'.le_trans' _ _ _ ?_ hstep
    exact Q'.ge_of_eqv (Q'.add_neg_self_eqv (renDefect afr p (k0 + j)))
  have hρ1 : ∀ j, tailRate afr p k0 j ≤ 1 := by
    intro j
    -- 1 − renDefect ≤ 1  ⟸  0 ≤ renDefect.
    show (1 : Q') - renDefect afr p (k0 + j) ≤ 1
    have hnn : (0 : Q') ≤ renDefect afr p (k0 + j) := renDefect_nonneg afr p (k0 + j)
    have hnegle : (-(renDefect afr p (k0 + j))) ≤ (0 : Q') := by
      have h : (0 : Q') + (-(renDefect afr p (k0 + j)))
          ≤ renDefect afr p (k0 + j) + (-(renDefect afr p (k0 + j))) :=
        Q'.add_le_add_right 0 (renDefect afr p (k0 + j)) (-(renDefect afr p (k0 + j))) hnn
      refine Q'.le_trans' _ _ _ ?_ (Q'.le_trans' _ _ _ h
        (Q'.le_of_eqv (Q'.add_neg_self_eqv (renDefect afr p (k0 + j)))))
      exact Q'.ge_of_eqv (Q'.eqv_of_eq (Q'.zero_add' (-(renDefect afr p (k0 + j)))))
    show (1 : Q') + (-(renDefect afr p (k0 + j))) ≤ 1
    refine Q'.le_trans' _ _ _ (Q'.add_le_add_left 1 _ 0 hnegle) ?_
    exact Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' 1))
  have hρhalf : ∀ j, (1 - tailRate afr p k0 j) ≤ HalfPow.half := by
    intro j
    -- 1 − ρ_j ≃ renDefect(k0+j) ≤ 1/2.
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (one_sub_tailRate_eqv afr p k0 j)) ?_
    exact renDefect_le_half afr p (by omega)
  -- feed the exponential product floor with R = tailR.
  exact sum_loss_to_productFloor_exp (tailRate afr p k0) hρ0 hρ1 hρhalf
    (tailR afr p k0) (lossSum_tailRate_le afr p k0)

/-- **The UNCONDITIONAL instantiation.**  On the canonical AF inhabitant (a
concrete, non-4D witness `w_k = 1 − 1/(k+1)`), the conditional capstone fires with
NO hypotheses: a strictly-positive floor for the renormalized dominant-mode tail
product.  This is an honest, unconditional positive product floor for the
renormalized dominant-mode defect along a concrete AF trajectory — NOT a 4D
Yang–Mills mass gap (the full-mode / genuine-AF-trajectory content is open). -/
def renormalized_gap_canonical (p : Nat) :
    Σ' (floor : CReal) (ε : Q'),
      (0 : Q') < ε ∧ ExpPos.geRat floor ε
      ∧ ∀ n, CReal.leRat floor
          (RGGapPersistence.prodPrefix
            (tailRate afRateModulus_canonical p
              (defectCutoff afRateModulus_canonical p)) n) :=
  renormalized_gap_of_AFRate afRateModulus_canonical p

/-! ## 7. Doc-section — exact scope (CRITICAL honesty)

This module is a COMPOSITION of already-proved pieces:

  * AF rate (named `AFRateModulus`, or the canonical inhabitant) — interface.
  * Renormalized quadratic defect — PROVED (dominant `s = 1` mode, marginal flow
    absorbed by the `s = 1` retuning `renormW`).
  * Inverse-square per-step bound (`renDefect_invSq`) — composed (with the honest
    integer offset-inflation `M = 2·B.den` aligning the `Q'` offset to `B' = 2`,
    a fixed finite constant cost).
  * Inverse-square summability (`renDefect_summable`) — PROVED endpoint.
  * Exponential product floor `e^{−2R} > 0` — PROVED.
  * Positive product floor on the tail renormalized rates
    (`renormalized_gap_of_AFRate`, unconditional `renormalized_gap_canonical`).

SCOPE / RESTRICTIONS (each is load-bearing, none is hidden):
  (i)   DOMINANT MODE ONLY (`s = 1`).  The full-mode (all `s`) renormalized defect
        is the open 4D content.
  (ii)  RENORMALIZED defect — only the genuine `O((1−w)²)` transverse residual;
        the marginal linear drift is reparametrized away by the `s = 1` retuning.
  (iii) FINITE fusion degree (`N = 1`; the dominant-mode value is `N`-independent).
  (iv)  TAIL `k ≥ k₀` — the finite head (where the defect may exceed `1/2`) is
        honestly excluded; the floor is over the tail prefix product.
  (v)   The canonical instantiation uses a CONCRETE non-4D AF inhabitant.  It is a
        genuine unconditional result about that trajectory, NOT a 4D YM mass gap.

The FULL-mode (all `s`) renormalized-defect quadratic bound and the uniformity
along the GENUINE 4D asymptotic-freedom trajectory remain open.  This module shows
the marginal/quadratic SEPARATION makes the dominant-mode renormalized defect
genuinely SUMMABLE, closing the product-floor chain on that mode. -/

end YMGap.Continuum.SummabilityCapstone

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SummabilityCapstone.Cp_nonneg
#print axioms YMGap.Continuum.SummabilityCapstone.two_le_inflM_mul_B
#print axioms YMGap.Continuum.SummabilityCapstone.harmDen2_le_inflM_harmDen
#print axioms YMGap.Continuum.SummabilityCapstone.renDefect_nonneg
#print axioms YMGap.Continuum.SummabilityCapstone.margin_le_scaled
#print axioms YMGap.Continuum.SummabilityCapstone.rr_mul_DD_eqv
#print axioms YMGap.Continuum.SummabilityCapstone.invSqTerm_mul_DD_eqv
#print axioms YMGap.Continuum.SummabilityCapstone.scaledMargin_sq_le_invSq
#print axioms YMGap.Continuum.SummabilityCapstone.renDefect_invSq
#print axioms YMGap.Continuum.SummabilityCapstone.renDefect_summable
#print axioms YMGap.Continuum.SummabilityCapstone.renDefect_le_half
#print axioms YMGap.Continuum.SummabilityCapstone.lossSum_shift_eq
#print axioms YMGap.Continuum.SummabilityCapstone.lossSum_oneSub_tailRate_eqv
#print axioms YMGap.Continuum.SummabilityCapstone.lossSum_tailRate_le
#print axioms YMGap.Continuum.SummabilityCapstone.renormalized_gap_of_AFRate
#print axioms YMGap.Continuum.SummabilityCapstone.renormalized_gap_canonical
