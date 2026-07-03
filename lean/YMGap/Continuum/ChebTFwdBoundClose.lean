/-
# Closing the `FwdSummable` leaf of the theta `C¹` inputs (Chain B), and the
  honest reduction of the `ChebTFwdBound` leaf (Chain A)

`ThetaSeriesC1Close` reduced the load-bearing `fdbound` field of the series-side
theta derivative to exactly two per-term residuals: `ChebTFwdBound x` (the
forward Taylor bracket bound) and `FwdSummable a KT` (the Gaussian-weighted
partial-sum bound).  This module GENUINELY DISCHARGES `FwdSummable` under the
single robust hypothesis that the majorant `KT` obeys a one-step `Nat` ratio
bound `KT (n+1) ≤ c · KT n` — precisely the exponential-envelope form that the
`ChebTFwdBound` engine (Chain A) produces.

## What is GENUINELY proved here (new, axiom-clean content)

* **`step_ratio`** — the per-term step-ratio `f (n+1) ≤ (a^{2n+3}·c)·f n` for the
  Gaussian-weighted summand `f n = a^{(n+1)²}·KT n`.  Splits the exponent
  `(n+2)² = (n+1)² + (2n+3)` (`Q'.pow_add_eqv`) and carries `KT`'s ratio through
  `ofNat` monotonicity.  (Atom N1.)

* **`finSum_shift_eqv` / `shift_split`** — the exact prefix/tail split of a
  finite sum at a cut index `n0`, and its `≤`-form for nonnegative summands.
  (Atom N2.)

* **`FwdSummable_of_ratio`** — **THE CLOSE.**  From `0 < a < 1`, `1 ≤ c`, and the
  ratio bound `KT (n+1) ≤ c·KT n`, the Gaussian decay `a^{(n+1)²}` crushes the
  (possibly exponential) `KT`: past the cut `n0` where `a^{2n+3}·c ≤ ½`, the tail
  is geometric (`CharacterTail.geom_series_le`), so every partial sum is `≤ Csum`.
  A fully constructive `FwdSummable a KT`.

## The honest residual that remains (Chain A, AGENTS.md Rule 6)

* **`ChebTFwdRatioData x`** — bundles the `ChebTFwdBound x` engine output together
  with the one-step `Nat` ratio bound its majorant satisfies.  Constructing it is
  the forward-`T` Taylor / wider-box majorant obligation (A1 ladder algebra, A2
  wider `[−3/2,3/2]` box re-run, A3 recurrence ratio-envelope) — NOT closed here.
  `thetaSeriesC1_of_ratio` shows this single residual, fed through
  `FwdSummable_of_ratio`, assembles the full series-side theta derivative.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`.
-/

import YMGap.Continuum.ThetaSeriesC1Close

namespace YMGap.Continuum.ChebTFwdBoundClose

open YMGap.Constructive
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Small `Q'`/`ofNat` helpers re-proved locally (no heavy imports) -/

/-- `0 ≤ ofNat n`. -/
theorem ofNat_nonneg (n : Nat) : (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg n

/-- `ofNat (a·b) ≃ ofNat a · ofNat b` (the multiplicative homomorphism). -/
theorem ofNat_mul_eqv (a b : Nat) :
    (Q'.ofNat (a * b)) ≈ (Q'.ofNat a * Q'.ofNat b) := by
  show ((a * b : Nat) : Int) * ((Q'.ofNat a * Q'.ofNat b).den : Int)
     = (((a : Nat) : Int) * ((b : Nat) : Int)) * ((Q'.ofNat (a * b)).den : Int)
  show ((a * b : Nat) : Int) * (1 : Int)
     = (((a : Nat) : Int) * ((b : Nat) : Int)) * (1 : Int)
  rw [Int.mul_one, Int.mul_one, Int.natCast_mul]

/-- `ofNat` is monotone in `Nat`. -/
theorem ofNat_le_ofNat {a b : Nat} (h : a ≤ b) : Q'.ofNat a ≤ Q'.ofNat b := by
  show (Q'.ofNat a).num * ((Q'.ofNat b).den : Int)
      ≤ (Q'.ofNat b).num * ((Q'.ofNat a).den : Int)
  rw [Q'.ofNat_num_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast, Q'.ofNat_den_cast,
      Int.mul_one, Int.mul_one]
  exact_mod_cast h

/-- The 4-factor commutative rearrangement `(A·B)·(C·D) ≈ (B·C)·(A·D)`. -/
theorem mul4_rearr (A B C D : Q') :
    ((A * B) * (C * D)) ≈ ((B * C) * (A * D)) := by
  -- canonical form `A·(B·(C·D))`
  have lhs : ((A * B) * (C * D)) ≈ (A * (B * (C * D))) := Q'.mul_assoc_eqv A B (C * D)
  have rhs : ((B * C) * (A * D)) ≈ (A * (B * (C * D))) := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv B C (A * D)) ?_
    have hin : (C * (A * D)) ≈ (A * (C * D)) := by
      refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv C A D)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ D (Q'.mul_comm_eqv C A)) ?_
      exact Q'.mul_assoc_eqv A C D
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left B _ _ hin) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv B A (C * D))) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ (C * D) (Q'.mul_comm_eqv B A)) ?_
    exact Q'.mul_assoc_eqv A B (C * D)
  exact Q'.eqv_trans _ _ _ lhs (Q'.eqv_symm rhs)

/-- `½·(t + t) ≈ t`. -/
theorem half_double_eqv (t : Q') : HalfPow.half * (t + t) ≈ t := by
  have hd : (HalfPow.half + HalfPow.half) ≈ (1 : Q') := by decide
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv HalfPow.half t t) ?_
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_mul_eqv HalfPow.half HalfPow.half t)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ t hd) ?_
  exact Q'.one_mul_eqv t

/-- Nonnegative summands give nonnegative finite sums. -/
theorem finSum_nonneg (p : Nat → Q') (hp : ∀ k, (0 : Q') ≤ p k) :
    ∀ n, (0 : Q') ≤ RationalTail.finSum p n
  | 0 => Q'.le_refl' 0
  | n + 1 => by
    show (0 : Q') ≤ RationalTail.finSum p n + p n
    exact Q'.le_trans' _ _ _ (finSum_nonneg p hp n)
      (Q'.add_le_self_of_nonneg _ _ (hp n))

/-! ## 1. The Gaussian-weighted summand and its step ratio (Atom N1) -/

/-- The `FwdSummable` summand `a^{(n+1)²}·KT n` (defeq to `partial_le`'s body). -/
def fCoef (a : Q') (KT : Nat → Nat) (n : Nat) : Q' :=
  a ^ ((n + 1) * (n + 1)) * Q'.ofNat (KT n)

theorem fCoef_nonneg {a : Q'} (ha0 : (0 : Q') < a) (KT : Nat → Nat) (n : Nat) :
    (0 : Q') ≤ fCoef a KT n :=
  Q'.mul_nonneg _ _ (Q'.pow_nonneg a (Q'.le_of_lt ha0) _) (ofNat_nonneg (KT n))

/-- **The per-term step ratio.**  `f (n+1) ≤ (a^{2n+3}·c)·f n` for the
Gaussian-weighted summand, from `(n+2)² = (n+1)² + (2n+3)` and `KT`'s ratio. -/
theorem step_ratio {a : Q'} (ha0 : (0 : Q') < a) (KT : Nat → Nat) (c : Nat)
    (hratio : ∀ n, KT (n + 1) ≤ c * KT n) (n : Nat) :
    fCoef a KT (n + 1) ≤ (a ^ (2 * n + 3) * Q'.ofNat c) * fCoef a KT n := by
  have hexp : (n + 1 + 1) * (n + 1 + 1) = (n + 1) * (n + 1) + (2 * n + 3) := by
    rw [Nat.mul_succ (n + 1 + 1) (n + 1), Nat.succ_mul (n + 1) (n + 1)]; omega
  have hcoef_nn : (0 : Q') ≤ a ^ ((n + 1) * (n + 1)) * a ^ (2 * n + 3) :=
    Q'.mul_nonneg _ _ (Q'.pow_nonneg a (Q'.le_of_lt ha0) _)
      (Q'.pow_nonneg a (Q'.le_of_lt ha0) _)
  show a ^ ((n + 1 + 1) * (n + 1 + 1)) * Q'.ofNat (KT (n + 1))
      ≤ (a ^ (2 * n + 3) * Q'.ofNat c) * fCoef a KT n
  rw [hexp]
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_right _ _ (Q'.ofNat (KT (n + 1)))
      (Q'.pow_add_eqv a ((n + 1) * (n + 1)) (2 * n + 3)))) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (ofNat_le_ofNat (hratio n)) hcoef_nn) ?_
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ (ofNat_mul_eqv c (KT n)))) ?_
  exact Q'.le_of_eqv
    (mul4_rearr (a ^ ((n + 1) * (n + 1))) (a ^ (2 * n + 3))
      (Q'.ofNat c) (Q'.ofNat (KT n)))

/-! ## 2. The prefix/tail split at a cut index (Atom N2) -/

/-- **The exact prefix/tail split** of a finite sum at a cut `n0`:
`Σ_{i<n0+K} p = Σ_{i<n0} p + Σ_{k<K} p(n0+k)`. -/
theorem finSum_shift_eqv (p : Nat → Q') (n0 : Nat) :
    ∀ K, RationalTail.finSum p (n0 + K)
        ≈ RationalTail.finSum p n0
            + RationalTail.finSum (fun k => p (n0 + k)) K
  | 0 => by
    show RationalTail.finSum p n0 ≈ RationalTail.finSum p n0 + (0 : Q')
    rw [Q'.add_zero']
    exact Q'.eqv_refl _
  | K + 1 => by
    show RationalTail.finSum p (n0 + K) + p (n0 + K)
        ≈ RationalTail.finSum p n0
            + (RationalTail.finSum (fun k => p (n0 + k)) K + p (n0 + K))
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ (p (n0 + K)) (finSum_shift_eqv p n0 K)) ?_
    exact Q'.add_assoc_eqv (RationalTail.finSum p n0)
      (RationalTail.finSum (fun k => p (n0 + k)) K) (p (n0 + K))

/-- **The `≤`-form of the split** for nonnegative summands: every partial sum is
bounded by the prefix plus the shifted tail. -/
theorem shift_split (p : Nat → Q') (hp : ∀ k, (0 : Q') ≤ p k) (n0 : Nat) :
    ∀ M, RationalTail.finSum p M
        ≤ RationalTail.finSum p n0
            + RationalTail.finSum (fun k => p (n0 + k)) M := by
  intro M
  rcases Nat.lt_or_ge M n0 with hlt | hge
  · refine Q'.le_trans' _ _ _
      (RationalTail.finSum_monotone_of_nonneg p hp M n0 (Nat.le_of_lt hlt)) ?_
    exact Q'.add_le_self_of_nonneg _ _
      (finSum_nonneg (fun k => p (n0 + k)) (fun k => hp (n0 + k)) M)
  · obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hge
    refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (finSum_shift_eqv p n0 K)) ?_
    refine Q'.add_le_add_left _ _ _ ?_
    exact RationalTail.finSum_monotone_of_nonneg (fun k => p (n0 + k))
      (fun k => hp (n0 + k)) K (n0 + K) (by omega)

/-! ## 3. THE CLOSE — `FwdSummable` from a `Nat` ratio bound -/

/-- **`FwdSummable` from a one-step ratio bound.**  For `0 < a < 1`, `1 ≤ c`, and
`KT (n+1) ≤ c·KT n`, the Gaussian weight `a^{(n+1)²}` beats the (possibly
exponential) majorant `KT`: choose the cut `n0` past which `a^{2n+3}·c ≤ ½`, so
the tail from `n0` is geometric with ratio `½` and every partial sum is bounded.
Genuinely constructive — no open input. -/
def FwdSummable_of_ratio {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (KT : Nat → Nat) (c : Nat) (hc : 1 ≤ c)
    (hratio : ∀ n, KT (n + 1) ≤ c * KT n) :
    ThetaSeriesC1Close.FwdSummable a KT := by
  have hcpos : 0 < c := Nat.lt_of_lt_of_le (by decide) hc
  have hcnum : 0 < (Q'.ofNat c).num := by
    rw [Q'.ofNat_num_cast]; exact_mod_cast hcpos
  have hnn : ∀ n, (0 : Q') ≤ fCoef a KT n := fun n => fCoef_nonneg ha0 KT n
  -- The cut (as computable `Nat` data, not a `Prop`-∃): `a^m ≤ ½/c` for `m ≥ n0`.
  have hδ : (0 : Q') < HKConv.divPos HalfPow.half (Q'.ofNat c) :=
    HKConv.divPos_pos (CReal.num_pos_of_pos ThetaSeriesC1Close.half_pos)
  let n0 : Nat := HKConvGen.powBaseCutoff a (HKConv.divPos HalfPow.half (Q'.ofNat c))
  have hN : ∀ m, n0 ≤ m →
      a ^ m ≤ HKConv.divPos HalfPow.half (Q'.ofNat c) := fun m hm =>
    Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone (Q'.le_of_lt ha0) (Q'.le_of_lt ha1) hm)
      (HKConvGen.pow_base_le_cutoff ha0 ha1 hδ)
  -- Past the cut the step-ratio coefficient is `≤ ½`.
  have hcoef : ∀ k, a ^ (2 * (n0 + k) + 3) * Q'.ofNat c ≤ HalfPow.half := by
    intro k
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (hN _ (by omega)) (ofNat_nonneg c)) ?_
    exact Q'.le_of_eqv (HKConv.divPos_mul_eqv hcnum)
  -- Geometric domination of the shifted tail with ratio `½`.
  have hdom : ∀ k,
      fCoef a KT (n0 + (k + 1)) ≤ HalfPow.half * fCoef a KT (n0 + k) := by
    intro k
    have hidx : n0 + (k + 1) = (n0 + k) + 1 := by omega
    rw [hidx]
    exact Q'.le_trans' _ _ _ (step_ratio ha0 KT c hratio (n0 + k))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (hcoef k) (hnn (n0 + k)))
  have hfnn0 : (0 : Q') ≤ fCoef a KT n0 := hnn n0
  have hH : (0 : Q') ≤ fCoef a KT n0 + fCoef a KT n0 :=
    Q'.le_trans' _ _ _ hfnn0 (Q'.add_le_self_of_nonneg _ _ hfnn0)
  have hrec : fCoef a KT n0 + HalfPow.half * (fCoef a KT n0 + fCoef a KT n0)
      ≤ (fCoef a KT n0 + fCoef a KT n0) :=
    Q'.le_of_eqv (Q'.add_eqv_congr_left _ _ _ (half_double_eqv (fCoef a KT n0)))
  -- `∀ N, Σ_{k<N} f(n0+k) ≤ f n0 + f n0`.
  have geomBound := CharacterTail.geom_series_le (fun k => fCoef a KT (n0 + k))
    (fCoef a KT n0) HalfPow.half (fCoef a KT n0 + fCoef a KT n0)
    (Q'.le_of_lt ThetaSeriesC1Close.half_pos) hH
    (Q'.le_refl' (fCoef a KT n0)) hdom hrec
  refine
    { Csum := (RationalTail.finSum (fCoef a KT) n0
                + (fCoef a KT n0 + fCoef a KT n0)) + 1
      Csum_pos := ?_
      partial_le := ?_ }
  · -- `0 < X + 1`
    have hXnn : (0 : Q') ≤ RationalTail.finSum (fCoef a KT) n0
        + (fCoef a KT n0 + fCoef a KT n0) :=
      Q'.le_trans' _ _ _ (finSum_nonneg (fCoef a KT) hnn n0)
        (Q'.add_le_self_of_nonneg _ _ hH)
    have h1le : (1 : Q') ≤ (RationalTail.finSum (fCoef a KT) n0
        + (fCoef a KT n0 + fCoef a KT n0)) + 1 := by
      have hh := Q'.add_le_add hXnn (Q'.le_refl' (1 : Q'))
      rw [Q'.zero_add'] at hh
      exact hh
    exact Q'.pos_of_lt_of_le (by decide) h1le
  · intro M
    refine Q'.le_trans' _ _ _ (shift_split (fCoef a KT) hnn n0 M) ?_
    refine Q'.le_trans' _ _ _
      (Q'.add_le_add_left (RationalTail.finSum (fCoef a KT) n0)
        (RationalTail.finSum (fun k => fCoef a KT (n0 + k)) M)
        (fCoef a KT n0 + fCoef a KT n0) (geomBound M)) ?_
    exact Q'.add_le_self_of_nonneg _ (1 : Q') Q'.zero_le_one

/-! ## 4. The Chain-A residual and the assembled capstone -/

/-- **The Chain-A residual (honest).**  Bundles the forward-`T` Taylor engine
output `ChebTFwdBound x` with the one-step `Nat` ratio bound `KT (n+1) ≤ c·KT n`
its (exponential) majorant satisfies.  Constructing it is the A1/A2/A3 obligation
(forward-`T` ladder, wider `[−3/2,3/2]` box majorant re-run, recurrence
ratio-envelope) — NOT closed here. -/
structure ChebTFwdRatioData (x : Q') : Type where
  /-- The forward Taylor bracket engine. -/
  fb : ThetaSeriesC1Close.ChebTFwdBound x
  /-- The ratio cap. -/
  c : Nat
  /-- The cap is positive. -/
  hc : 1 ≤ c
  /-- The one-step majorant ratio bound. -/
  hratio : ∀ n : Nat, fb.KT (n + 1) ≤ c * fb.KT n

/-- **`FwdSummable` from the Chain-A residual**, via `FwdSummable_of_ratio`. -/
def fwdSummable_of_data {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (d : ChebTFwdRatioData x) :
    ThetaSeriesC1Close.FwdSummable a d.fb.KT :=
  FwdSummable_of_ratio ha0 ha1 d.fb.KT d.c d.hc d.hratio

/-- **THE ASSEMBLED SERIES-SIDE THETA DERIVATIVE (Chain B discharged).**  From the
`F`-entangled pointwise data and the single Chain-A residual `ChebTFwdRatioData`,
the `K_t`-side series is a `CReal`-valued finite-difference derivative of the
common `F` at `x`.  The summability leaf `FwdSummable` is genuinely discharged
here (`fwdSummable_of_data`); only the forward-`T` Taylor / ratio data remains. -/
def thetaSeriesC1_of_ratio {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal)
    (pt : ThetaSeriesC1Close.ThetaPtwiseData a x F)
    (d : ChebTFwdRatioData x) :
    TsumDeriv.FDDerivDataC F (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) x :=
  ThetaSeriesC1Close.thetaSeriesC1 ha0 ha1 hx hx1 F pt d.fb
    (fwdSummable_of_data ha0 ha1 d)

end YMGap.Continuum.ChebTFwdBoundClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ChebTFwdBoundClose.mul4_rearr
#print axioms YMGap.Continuum.ChebTFwdBoundClose.half_double_eqv
#print axioms YMGap.Continuum.ChebTFwdBoundClose.step_ratio
#print axioms YMGap.Continuum.ChebTFwdBoundClose.finSum_shift_eqv
#print axioms YMGap.Continuum.ChebTFwdBoundClose.shift_split
#print axioms YMGap.Continuum.ChebTFwdBoundClose.FwdSummable_of_ratio
#print axioms YMGap.Continuum.ChebTFwdBoundClose.fwdSummable_of_data
#print axioms YMGap.Continuum.ChebTFwdBoundClose.thetaSeriesC1_of_ratio
