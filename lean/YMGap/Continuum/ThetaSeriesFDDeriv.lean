/-
# The series-side CReal C¹-uniform-limit engine and the theta series derivative

This module builds the **CReal-valued** analogue of the `Q'`-valued Bishop
C¹-uniform-limit engine `TsumDeriv.fdDeriv_of_unif`, and applies it to the
`K_t`-side heat-kernel Chebyshev series.

## What is GENUINELY closed here (new, axiom-clean, reusable content)

* **`C1InputsC`** — the CReal-valued analogue of `TsumDeriv.C1Inputs`.  The
  function family `f, f' : Nat → Q' → Q'` is a family of RATIONAL truncations
  (and their termwise derivatives), but the LIMIT `F : Q' → CReal` and the limit
  derivative value `d : CReal` are genuine `CReal`s.  The pointwise / uniform
  convergence are stated as `CReal.leRat` bounds (the natural CReal convergence),
  and the finite-difference equicontinuity `fdbound` is the `Q'`-level bound of the
  truncations (verbatim reuse of the `Q'` engine's `fdbound` field).

* **`fdDeriv_of_unifC` (CLOSED)** — THE ENGINE.  From `C1InputsC f f' F d θ`, the
  CReal limit `F` has CReal-valued finite-difference derivative `d` at `θ`, i.e. a
  `TsumDeriv.FDDerivDataC F d θ`, with explicit modulus `δ ε := delStar (ε/4)`.  The
  proof is the SAME four-piece Bishop triangle as the `Q'` engine, but discharged
  **per approximation index `n`**: at each `n`, `(fdRemC F d θ h).approx n` is the
  `Q'` remainder of the `n`-th approximations (`TsumDeriv.fdRemC_approx`), and the
  generic `TsumDeriv.telescope6` identity splits it into four `Q'` pieces, each
  bounded by `(ε/4)·|h|` (up to a vanishing `tol` slack) using the per-index
  consequences of the four `CReal.leRat` convergence hypotheses.  This is exactly
  the "mechanical index-wise transfer" of the `Q'` engine to the `CReal` layer.

* **`chebTTrunc`** — the finite Chebyshev-`T` truncation
  `Σ_{n<M} a^{(n+1)²}·T_{n+1}(y)` whose termwise `y`-derivative is the `K_t`-side
  partial sum `dPartial a x M` (since `d/dy T_{n+1} = (n+1)·U_n`).

* **`thetaSeriesFDDeriv`** — the deliverable: given the theta C¹ inputs
  `C1InputsC (chebTTrunc a) (dPartial a) F (dSeriesCReal …) x` over a common
  `F = ϑ₃`, the series side `dSeriesCReal` is a `FDDerivDataC F (dSeriesCReal …) x`.
  Paired with the product-side `FDDerivDataC F Rhalf x`, this is exactly the
  `DiffProduct.C1UniqInputsCRealDeriv` that `ThetaFDDerivAssembly` names as the sole
  open input to `K_t ≥ 0`.

## The honest residual (AGENTS.md Rule 6)

The engine is COMPLETE.  What is NOT discharged here is the CONSTRUCTION of the
theta `C1InputsC` instance — namely (a) the two undifferentiated Jacobi/theta
pointwise limits `ofQ'(chebTTrunc a M y) → F y` (the `ptθ`/`ptθh` fields),
(b) the finite Chebyshev-Taylor remainder for `chebTTrunc` uniform in `M` (the
`fdbound` field), and (c) the `unif` field (`dPartial → dSeriesCReal`).  These are
the genuine remaining series-side analytic inputs; they are named as the fields of
`C1InputsC` and consumed by `thetaSeriesFDDeriv`, NOT faked.

Note on `unif`: `dSeriesCReal.approx M = dPartial a x M` is `rfl` and the base-`a`
geometric convergence is built into `dSeriesCReal`, so `unif` is the mere Cauchy
self-convergence of `dSeriesCReal`.  It is NOT discharged as `Type`-level data in
this module only because extracting the stage-modulus `Mg` from the bare `CReal`'s
`Prop`-level `cauchy` field would need `Classical.choice` (forbidden); supplying it
means threading `dSeriesCReal`'s explicit `HKConvGen` geometric modulus, which is
left to the residual's constructor.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`.
-/

import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.JTPIdentity
import YMGap.Continuum.ChebyshevBound
import YMGap.Constructive.Reals
import YMGap.Constructive.CRealLe
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.CRealMul
import YMGap.Constructive.RegularCRealArith
import YMGap.Constructive.RationalTail

namespace YMGap.Continuum.ThetaSeriesFDDeriv

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Two `Q'` regrouping helpers for the four-piece estimate -/

/-- Pairwise regroup: `(x+y)+(x+y) ≈ (x+x)+(y+y)`. -/
theorem add_pair_regroup (x y : Q') :
    ((x + y) + (x + y)) ≈ ((x + x) + (y + y)) := by
  -- (x+y)+(x+y) ≈ x+(y+(x+y)) ≈ x+(x+(y+y)) ≈ (x+x)+(y+y)
  have e1 : ((x + y) + (x + y)) ≈ (x + (y + (x + y))) := Q'.add_assoc_eqv x y (x + y)
  refine Q'.eqv_trans _ _ _ e1 ?_
  have einner : (y + (x + y)) ≈ (x + (y + y)) := by
    have s2 : (y + (x + y)) ≈ ((y + x) + y) := Q'.eqv_symm (Q'.add_assoc_eqv y x y)
    have s3 : ((y + x) + y) ≈ ((x + y) + y) :=
      Q'.add_eqv_congr_right _ _ y (Q'.add_comm_eqv y x)
    have s4 : ((x + y) + y) ≈ (x + (y + y)) := Q'.add_assoc_eqv x y y
    exact Q'.eqv_trans _ _ _ s2 (Q'.eqv_trans _ _ _ s3 s4)
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left x _ _ einner) ?_
  exact Q'.eqv_symm (Q'.add_assoc_eqv x x (y + y))

/-- Four-fold regroup: `(((A+A)+A)+A) ≈ (((a+a)+a)+a) + (((b+b)+b)+b)` for `A = a+b`. -/
theorem add4_regroup (a b : Q') :
    ((((a + b) + (a + b)) + (a + b)) + (a + b))
      ≈ ((((a + a) + a) + a) + (((b + b) + b) + b)) := by
  -- ((A+A)+A)+A ≈ (A+A)+(A+A) ≈ ((a+a)+(b+b)) + ((a+a)+(b+b)) ≈ (X+X)+(Y+Y) ≈ target
  have s1 : ((((a + b) + (a + b)) + (a + b)) + (a + b))
      ≈ (((a + b) + (a + b)) + ((a + b) + (a + b))) :=
    Q'.add_assoc_eqv ((a + b) + (a + b)) (a + b) (a + b)
  refine Q'.eqv_trans _ _ _ s1 ?_
  have s2 : (((a + b) + (a + b)) + ((a + b) + (a + b)))
      ≈ (((a + a) + (b + b)) + ((a + a) + (b + b))) :=
    TsumDeriv.Q'.add_eqv_congr (add_pair_regroup a b) (add_pair_regroup a b)
  refine Q'.eqv_trans _ _ _ s2 ?_
  have s3 : (((a + a) + (b + b)) + ((a + a) + (b + b)))
      ≈ (((a + a) + (a + a)) + ((b + b) + (b + b))) :=
    add_pair_regroup (a + a) (b + b)
  refine Q'.eqv_trans _ _ _ s3 ?_
  have s4 : ((a + a) + (a + a)) ≈ (((a + a) + a) + a) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (a + a) a a)
  have s5 : ((b + b) + (b + b)) ≈ (((b + b) + b) + b) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (b + b) b b)
  exact TsumDeriv.Q'.add_eqv_congr s4 s5

/-- `4·t ≈ s` with `t = ¼s`: `(((t+t)+t)+t) ≈ s`. -/
theorem four_quarter_eqv (s : Q') :
    (((HalfPow.half * (HalfPow.half * s) + HalfPow.half * (HalfPow.half * s))
        + HalfPow.half * (HalfPow.half * s)) + HalfPow.half * (HalfPow.half * s))
      ≈ s := by
  have hqq : (HalfPow.half * (HalfPow.half * s) + HalfPow.half * (HalfPow.half * s))
      ≈ (HalfPow.half * s) := ExpNeg.two_halves (HalfPow.half * s)
  have e1 : (((HalfPow.half * (HalfPow.half * s) + HalfPow.half * (HalfPow.half * s))
        + HalfPow.half * (HalfPow.half * s)) + HalfPow.half * (HalfPow.half * s))
      ≈ ((HalfPow.half * (HalfPow.half * s) + HalfPow.half * (HalfPow.half * s))
        + (HalfPow.half * (HalfPow.half * s) + HalfPow.half * (HalfPow.half * s))) :=
    Q'.add_assoc_eqv _ _ _
  refine Q'.eqv_trans _ _ _ e1 ?_
  refine Q'.eqv_trans _ _ _ (TsumDeriv.Q'.add_eqv_congr hqq hqq) ?_
  exact ExpNeg.two_halves s

/-! ## 1. The CReal-valued convergence data (analogue of `PtwiseConvAt`/`UnifDerivConvAt`) -/

/-- **Pointwise convergence of RATIONAL truncations to a CReal limit.**  Past stage
`Nθ ε`, the lifted truncation `ofQ' (f M p)` is within `ε` of the CReal `F p`
(as a `CReal.leRat` bound on the CReal absolute difference). -/
structure PtwiseConvC (f : Nat → Q' → Q') (F : Q' → CReal) (p : Q') : Type where
  /-- The pointwise-convergence stage modulus at `p`. -/
  Nθ : Q' → Nat
  /-- Past `Nθ ε`, `ofQ' (f M p)` is within `ε` of `F p`. -/
  conv : ∀ ε : Q', (0 : Q') < ε → ∀ M : Nat, Nθ ε ≤ M →
    CReal.leRat (CReal.abs (CReal.add (F p) (CReal.neg (CReal.ofQ' (f M p))))) ε

/-- **Uniform convergence of the RATIONAL derivative family to a CReal value.**
Past stage `Mg ε`, the lifted derivative `ofQ' (f' M θ)` is within `ε` of `d`. -/
structure UnifDerivConvC (f' : Nat → Q' → Q') (d : CReal) (θ : Q') : Type where
  /-- The uniform derivative-convergence stage modulus. -/
  Mg : Q' → Nat
  /-- Past `Mg ε`, `ofQ' (f' M θ)` is within `ε` of `d`. -/
  conv : ∀ ε : Q', (0 : Q') < ε → ∀ M : Nat, Mg ε ≤ M →
    CReal.leRat (CReal.abs (CReal.add d (CReal.neg (CReal.ofQ' (f' M θ))))) ε

/-- **The bundled CReal C¹-limit hypotheses.**  `f, f'` are rational truncations,
`F` is the CReal pointwise limit, `d` is the CReal derivative value at `θ`. -/
structure C1InputsC (f f' : Nat → Q' → Q') (F : Q' → CReal) (d : CReal) (θ : Q') :
    Type where
  /-- Pointwise convergence of `f M` to `F` at the base point. -/
  ptθ : PtwiseConvC f F θ
  /-- Pointwise convergence of `f M` to `F` at every perturbed point. -/
  ptθh : ∀ h : Q', PtwiseConvC f F (θ + h)
  /-- Uniform convergence of the derivative family `f' M θ → d`. -/
  unif : UnifDerivConvC f' d θ
  /-- A common finite-difference modulus for all `f M` past stage `mStar`. -/
  delStar : Q' → Q'
  /-- `delStar` is positive for positive tolerance. -/
  delStar_pos : ∀ ε : Q', (0 : Q') < ε → (0 : Q') < delStar ε
  /-- The stage past which the common modulus is valid. -/
  mStar : Q' → Nat
  /-- For `M ≥ mStar ε'`, `f M` has the cleared finite-difference bound with `delStar`. -/
  fdbound : ∀ ε' : Q', (0 : Q') < ε' → ∀ M : Nat, mStar ε' ≤ M →
    ∀ h : Q', (0 : Q') < Q'.abs h → Q'.abs h ≤ delStar ε' →
      Q'.abs (TsumDeriv.fdRem (f M) (f' M θ) θ h) ≤ ε' * Q'.abs h

/-! ## 2. THE CReal C¹-UNIFORM-LIMIT THEOREM (the reusable engine) -/

/-- **THE CReal C¹-UNIFORM-LIMIT THEOREM (constructive, data-carrying, CLOSED).**

From `C1InputsC f f' F d θ`, the CReal pointwise limit `F` has CReal-valued
finite-difference derivative `d` at `θ`, with modulus `δ ε := delStar (ε/4)`.  The
proof is the four-piece Bishop triangle discharged per approximation index `n`. -/
def fdDeriv_of_unifC {f f' : Nat → Q' → Q'} {F : Q' → CReal} {d : CReal} {θ : Q'}
    (H : C1InputsC f f' F d θ) :
    TsumDeriv.FDDerivDataC F d θ where
  δ ε := H.delStar (HalfPow.half * (HalfPow.half * ε))
  δ_pos ε hε := H.delStar_pos _
    (ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε))
  bound := by
    intro ε hε h hpos hle
    let q : Q' := HalfPow.half * (HalfPow.half * ε)
    have hqpos : (0 : Q') < q := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos ε hε)
    have hqh_pos : (0 : Q') < q * Q'.abs h := TsumDeriv.Q'.mul_pos' hqpos hpos
    -- the common stage M past all four moduli
    let M : Nat :=
      max (H.mStar q)
        (max (H.unif.Mg q)
          (max ((H.ptθ).Nθ (q * Q'.abs h)) ((H.ptθh h).Nθ (q * Q'.abs h))))
    have hMstar : H.mStar q ≤ M := Nat.le_max_left _ _
    have hMg : H.unif.Mg q ≤ M :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have hNθ : (H.ptθ).Nθ (q * Q'.abs h) ≤ M :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        (Nat.le_max_right _ _)
    have hNθh : (H.ptθh h).Nθ (q * Q'.abs h) ≤ M :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        (Nat.le_max_right _ _)
    -- the CReal convergence leRat's at stage M
    have lr1 := (H.ptθh h).conv (q * Q'.abs h) hqh_pos M hNθh
    have lr3 := (H.ptθ).conv (q * Q'.abs h) hqh_pos M hNθ
    have lr4 := H.unif.conv q hqpos M hMg
    -- the Q' finite-difference bound of the M-th truncation
    have hP2 : Q'.abs (TsumDeriv.fdRem (f M) (f' M θ) θ h) ≤ q * Q'.abs h :=
      H.fdbound q hqpos M hMstar h hpos hle
    -- unfold the leRat goal at tolerance tol
    intro tol htol
    let u : Q' := HalfPow.half * (HalfPow.half * tol)
    have hupos : (0 : Q') < u := ExpNeg.half_mul_pos _ (ExpNeg.half_mul_pos tol htol)
    have hunn : (0 : Q') ≤ u := Q'.le_of_lt hupos
    -- the P4 slack: sf·|h| ≈ u
    let sf : Q' := Q'.divPos u (Q'.abs h) hpos
    have hsfpos : (0 : Q') < sf := Q'.divPos_pos u (Q'.abs h) hpos hupos
    have hsfh_eqv : (sf * Q'.abs h) ≈ u := Q'.divPos_mul_eqv u (Q'.abs h) hpos
    -- extract per-index bounds from the three CReal leRat's
    obtain ⟨N1, hN1⟩ := lr1 u hupos
    obtain ⟨N3, hN3⟩ := lr3 u hupos
    obtain ⟨N4, hN4⟩ := lr4 sf hsfpos
    refine ⟨max N1 (max N3 N4), fun n hn => ?_⟩
    have hn1 : N1 ≤ n := Nat.le_trans (Nat.le_max_left _ _) hn
    have hn3 : N3 ≤ n :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
    have hn4 : N4 ≤ n :=
      Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn
    -- Piece 1 : |F(θ+h)_n − f_M(θ+h)| ≤ q|h| + u  (defeq unfold of the CReal approx)
    have b1 : Q'.abs ((F (θ + h)).approx n + (-(f M (θ + h)))) ≤ q * Q'.abs h + u :=
      hN1 n hn1
    -- Piece 3 : |f_M θ − F θ_n| ≤ q|h| + u
    have b3raw : Q'.abs ((F θ).approx n + (-(f M θ))) ≤ q * Q'.abs h + u := hN3 n hn3
    have b3 : Q'.abs ((f M θ) + (-((F θ).approx n))) ≤ q * Q'.abs h + u :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv (TsumDeriv.Q'.abs_sub_comm (f M θ) ((F θ).approx n))) b3raw
    -- Piece 2 : the M-th truncation finite-difference remainder ≤ q|h| ≤ q|h| + u
    have b2 : Q'.abs (((f M (θ + h)) + (-(f M θ))) + (-((f' M θ) * h)))
        ≤ q * Q'.abs h + u :=
      Q'.le_trans' _ _ _ hP2 (Q'.add_le_self_of_nonneg (q * Q'.abs h) u hunn)
    -- Piece 4 : |f'_M θ·h − d_n·h| ≤ q|h| + u
    have b4v : Q'.abs ((f' M θ) + (-(d.approx n))) ≤ q + sf :=
      Q'.le_trans' _ _ _
        (Q'.le_of_eqv (TsumDeriv.Q'.abs_sub_comm (f' M θ) (d.approx n))) (hN4 n hn4)
    have b4 : Q'.abs (((f' M θ) * h) + (-((d.approx n) * h))) ≤ q * Q'.abs h + u := by
      -- refold : (f'_M θ·h) − (d_n·h) ≈ (f'_M θ − d_n)·h
      have hrefold : (((f' M θ) * h) + (-((d.approx n) * h)))
          ≈ (((f' M θ) + (-(d.approx n))) * h) := by
        refine Q'.eqv_symm ?_
        refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv (f' M θ) (-(d.approx n)) h) ?_
        exact Q'.add_eqv_congr_left ((f' M θ) * h) _ _ (Q'.neg_mul_eqv (d.approx n) h)
      -- |refold| ≤ |f'_M θ − d_n|·|h| ≤ (q+sf)·|h| = q|h| + sf|h| ≈ q|h| + u
      refine Q'.le_trans' _ _ _
        (Q'.le_of_eqv (TsumDeriv.Q'.abs_eqv_congr hrefold)) ?_
      refine Q'.le_trans' _ _ _
        (TsumDeriv.Q'.abs_mul_le ((f' M θ) + (-(d.approx n))) h) ?_
      refine Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ b4v (Q'.abs_nonneg h)) ?_
      -- (q+sf)·|h| ≈ q|h| + sf|h| ≈ q|h| + u
      refine Q'.le_of_eqv ?_
      refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv q sf (Q'.abs h)) ?_
      exact Q'.add_eqv_congr_left (q * Q'.abs h) _ _ hsfh_eqv
    -- assemble the four pieces via the generic telescope identity at index n
    have hsplit := TsumDeriv.telescope6 ((F (θ + h)).approx n) (f M (θ + h))
      (f M θ) ((f' M θ) * h) ((F θ).approx n) ((d.approx n) * h)
    have hfour := TsumDeriv.abs_four_le
      (z := (F (θ + h)).approx n + (-((F θ).approx n))) (w := (d.approx n) * h)
      hsplit b1 b2 b3 b4
    -- the goal LHS IS this Q' remainder (fdRemC is index-wise)
    show Q'.abs ((TsumDeriv.fdRemC F d θ h).approx n) ≤ ε * Q'.abs h + tol
    rw [TsumDeriv.fdRemC_approx]
    refine Q'.le_trans' _ _ _ hfour ?_
    -- (((B+B)+B)+B) ≈ (4·q|h|) + (4·u) ≈ ε|h| + tol
    refine Q'.le_of_eqv ?_
    refine Q'.eqv_trans _ _ _ (add4_regroup (q * Q'.abs h) u) ?_
    exact TsumDeriv.Q'.add_eqv_congr (TsumDeriv.four_q_eqv ε h) (four_quarter_eqv tol)

/-! ## 3. The finite Chebyshev-`T` truncation (Link 1) -/

/-- The finite Chebyshev-`T` truncation `Σ_{n<M} a^{(n+1)²}·T_{n+1}(y)`, a genuine
`Q'`-polynomial in `y`.  Its termwise `y`-derivative is the `K_t`-side partial sum
`JTPIdentity.dPartial a x M` (since `d/dy T_{n+1}(y) = (n+1)·U_n(y)` and
`dTerm a x n = (n+1)·a^{(n+1)²}·U_n(x)`). -/
def chebTTrunc (a : Q') (M : Nat) : Q' → Q' :=
  fun y => RationalTail.finSum
    (fun n => a ^ ((n + 1) * (n + 1)) * Cheb.T (n + 1) y) M

/-- The termwise-derivative truncation family in the engine's argument order
`Nat → Q' → Q'`: `dPartialFam a M y = Σ_{n<M} dTerm a y n` (the `K_t`-side partial
sum at the point `y`).  This is `JTPIdentity.dPartial` with its point / cutoff
arguments in the order the engine expects. -/
def dPartialFam (a : Q') (M : Nat) (y : Q') : Q' := JTPIdentity.dPartial a y M

/-! ## 4. The series-side theta derivative (deliverable) -/

/-- **The theta series C¹ inputs** (named `Type`): the CReal C¹-limit hypotheses for
the `K_t`-side heat-kernel Chebyshev series — the finite Chebyshev-`T` truncations
`chebTTrunc a` converging to the common `F = ϑ₃`, with termwise derivatives
`dPartial a` converging to `dSeriesCReal`.  Supplying it (over the SAME common `F`
the product side uses) closes the series half of `C1UniqInputsCRealDeriv`. -/
def ThetaSeriesC1Inputs {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal) : Type :=
  C1InputsC (chebTTrunc a) (dPartialFam a) F
    (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) x

/-- **THE SERIES-SIDE THETA DERIVATIVE.**  From the theta C¹ inputs over a common
`F = ϑ₃`, the `K_t`-side series `dSeriesCReal` is a CReal-valued finite-difference
derivative of `F` at `x`: `FDDerivDataC F (dSeriesCReal …) x`.  This is exactly the
`Dser` field that `DiffProduct.C1UniqInputsCRealDeriv` demands, produced by the
genuine CReal C¹ engine `fdDeriv_of_unifC`. -/
def thetaSeriesFDDeriv {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal)
    (H : ThetaSeriesC1Inputs ha0 ha1 hx hx1 F) :
    TsumDeriv.FDDerivDataC F (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) x :=
  fdDeriv_of_unifC H

end YMGap.Continuum.ThetaSeriesFDDeriv

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ThetaSeriesFDDeriv.add4_regroup
#print axioms YMGap.Continuum.ThetaSeriesFDDeriv.four_quarter_eqv
#print axioms YMGap.Continuum.ThetaSeriesFDDeriv.fdDeriv_of_unifC
#print axioms YMGap.Continuum.ThetaSeriesFDDeriv.chebTTrunc
#print axioms YMGap.Continuum.ThetaSeriesFDDeriv.thetaSeriesFDDeriv
