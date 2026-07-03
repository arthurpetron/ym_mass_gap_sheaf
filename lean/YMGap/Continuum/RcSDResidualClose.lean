/-
# Inhabiting `RcSDResidual`: the missing sine small-angle atom, the product
magnitude bounds, and the honest algebraic residual

`RcQuadResidualClose.RcSDResidual q k θ` is the sole uninhabited object gating the
per-factor sub-chain

    RcSDResidual → RcQuadResidual → JacobiQuadResidual → FDDerivDataC.

Its two Type-level fields are `step0` (`fdRemC ≃ (amp+amp)·Rc`) and `sdBound`
(`|Rc| ≤ (16/3)·(|h|·|h|)` on `|h| ≤ ½`).  This module supplies the analytic heart
of `sdBound` and reduces the remainder to a single honest algebraic residual.

## What is GENUINELY proved here

* **`sinFull_small_angle_leRat`** — the ONE genuinely-missing analytic atom
  (advertised in `RcQuadResidualClose`'s docstring but never defined): the CReal
  small-angle bound `|sinFull B − ofQ' B| ≤ 2·termAbs |B| 3 = |B|³/3` for `|B| ≤ 1`.
  Mirror of `cosFull_small_angle_leRat`, with the two sine-specific wrinkles handled
  (the odd `sinFull` sign branch, and `sinTerm |B| 0 ≈ |B|` — an `eqv`, not `=`).

* **`cosBlock_leRat` / `sinBlock_leRat`** — the two product magnitude bounds
  `|cosFull A·(cosFull B − 1)| ≤ 2·termAbs |B| 2` and
  `|sinFull A·(sinFull B − B)| ≤ 2·termAbs |B| 3`, via `abs_mul_equiv`,
  `CReal.leRat_mul`, the `|cos|,|sin| ≤ 1` amplitude bounds, and the small-angle
  atoms (`cosFull_small_angle_leRat` and the new `sinFull_small_angle_leRat`).

* **`absTwoH_le_one`** — `|2h| ≤ 1` from `|h| ≤ ½` (the small-angle precondition).

* **`rcSDResidual_of_alg`** — the assembly proving BOTH fields of `RcSDResidual`
  from the algebraic residual `RcAlgResidual`: `sdBound` is the regroup Equiv +
  triangle (`leRat_abs_add`) + the two product bounds + the rational fold; `step0`
  is passed through directly.  All the small-angle / amplitude analysis is
  discharged here.

## The honest residual (AGENTS.md Rule 6)

`RcAlgResidual` — the purely *algebraic* obligations that remain: the two index-wise
ring-identity `CReal.Equiv`s (`step0`: `fdRemC ≃ (amp+amp)·Rc`; `regroup`:
`Rc ≃ cosFull A·(cosFull B−1) − sinFull A·(sinFull B−B)`), plus the single rational
fold `2·termAbs|2h|2 + 2·termAbs|2h|3 ≤ (16/3)·(|h|·|h|)` on `|h| ≤ ½`.  No trig /
analytic content survives in the residual; inhabiting it closes the whole per-factor
chain (`rcQuadResidual_of_alg`, `fdderiv_of_alg`).

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.
-/

import YMGap.Continuum.RcQuadResidualClose

namespace YMGap.Continuum.RcSDResidualClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.TsumDeriv
open YMGap.Continuum.JacobiFactorFDDeriv (Fk dk)
open YMGap.Continuum.JTPInstance (amp)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. The small-angle precondition `|2h| ≤ 1` -/

/-- `|2h| ≤ 1` from `|h| ≤ ½`: `|2h| ≈ 2·|h| ≤ 2·½ = 1`. -/
theorem absTwoH_le_one {h : Q'} (hle : Q'.abs h ≤ HalfPow.half) :
    Q'.abs ((2 : Q') * h) ≤ 1 := by
  have habs2 : Q'.abs (2 : Q') = 2 := by unfold Q'.abs; rw [if_pos (by decide)]
  have e1 : (Q'.abs ((2 : Q') * h)) ≈ ((2 : Q') * Q'.abs h) := by
    refine Q'.eqv_trans _ _ _ (RcQuadResidualClose.q_abs_mul_eqv 2 h) ?_
    rw [habs2]; exact Q'.eqv_refl _
  have h2 : (2 : Q') * Q'.abs h ≤ (2 : Q') * HalfPow.half :=
    Q'.mul_le_mul_of_nonneg_left (Q'.abs h) HalfPow.half 2 hle (by decide)
  have h3 : ((2 : Q') * HalfPow.half) ≤ 1 := Q'.le_of_eqv (by decide)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) (Q'.le_trans' _ _ _ h2 h3)

/-! ## 1. The genuinely-missing sine small-angle atom -/

/-- **`sinFull_small_angle_leRat`.**  `|sinFull B − ofQ' B| ≤ 2·termAbs |B| 3` as a
`CReal.leRat`, for `|B| ≤ 1`.  Mirror of `cosFull_small_angle_leRat`; the truncation
bound `sin_small_angle` is landed per-index by `leRat_of_eventually`, with a sign
case-split on `B` and the `sinTerm |B| 0 ≈ |B|` swap. -/
theorem sinFull_small_angle_leRat {B : Q'} (hB1 : Q'.abs B ≤ 1) :
    CReal.leRat (CReal.abs (CReal.add (TrigAdd.sinFull B) (CReal.neg (CReal.ofQ' B))))
      (ExpNeg.termAbs (Q'.abs B) 3 + ExpNeg.termAbs (Q'.abs B) 3) := by
  refine CReal.leRat_of_eventually ⟨1, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, n = 1 + d := ⟨n - 1, by omega⟩
  have hsa := TrigAdd.sin_small_angle (Q'.abs B) (Q'.abs_nonneg B) hB1 d
  have hterm : (Trig.sinTerm (Q'.abs B) 0) ≈ (Q'.abs B) := Trig.sinTerm_zero_eqv (Q'.abs B)
  by_cases hpos : (0 : Q') ≤ B
  · -- `sinFull B = sinNN |B|`, `|B| = B`.
    have habsB : Q'.abs B = B := TrigAdd.abs_of_nonneg hpos
    have hsf : TrigAdd.sinFull B = Trig.sinNN (Q'.abs B) (Q'.abs_nonneg B) :=
      TrigAdd.sinFull_of_nonneg hpos
    rw [hsf]
    show Q'.abs (Trig.sinPartial (Q'.abs B) (1 + d) + -B)
        ≤ ExpNeg.termAbs (Q'.abs B) 3 + ExpNeg.termAbs (Q'.abs B) 3
    have hterm2 : (Trig.sinTerm (Q'.abs B) 0) ≈ B :=
      Q'.eqv_trans _ _ _ hterm (YMGap.Constructive.Q'.eqv_of_eq habsB)
    have heqv : (Trig.sinPartial (Q'.abs B) (1 + d) + -B)
        ≈ (Trig.sinPartial (Q'.abs B) (1 + d) + -(Trig.sinTerm (Q'.abs B) 0)) :=
      Q'.add_eqv_congr_left _ _ _ (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hterm2))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (YMGap.Constructive.Q'.abs_eqv_congr heqv)) hsa
  · -- `sinFull B = neg (sinNN |B|)`, `|B| = -B`.
    have habsB : Q'.abs B = -B := by unfold Q'.abs; rw [if_neg hpos]
    have hsf : TrigAdd.sinFull B = CReal.neg (Trig.sinNN (Q'.abs B) (Q'.abs_nonneg B)) := by
      unfold TrigAdd.sinFull; rw [if_neg hpos]
    rw [hsf]
    show Q'.abs (-(Trig.sinPartial (Q'.abs B) (1 + d)) + -B)
        ≤ ExpNeg.termAbs (Q'.abs B) 3 + ExpNeg.termAbs (Q'.abs B) 3
    have hterm2 : (Trig.sinTerm (Q'.abs B) 0) ≈ (-B) :=
      Q'.eqv_trans _ _ _ hterm (YMGap.Constructive.Q'.eqv_of_eq habsB)
    have eB : B ≈ (-(Trig.sinTerm (Q'.abs B) 0)) := by
      refine Q'.eqv_symm ?_
      exact Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hterm2) (Q'.neg_neg_eqv B)
    have e1 : (-(Trig.sinPartial (Q'.abs B) (1 + d)) + -B)
        ≈ (-(Trig.sinPartial (Q'.abs B) (1 + d) + B)) :=
      Q'.eqv_symm (Q'.neg_add_eqv (Trig.sinPartial (Q'.abs B) (1 + d)) B)
    have e2 := YMGap.Constructive.Q'.abs_eqv_congr e1
    have e3 : (Q'.abs (-(Trig.sinPartial (Q'.abs B) (1 + d) + B)))
        ≈ (Q'.abs (Trig.sinPartial (Q'.abs B) (1 + d) + B)) :=
      Q'.abs_neg' _
    have e4 : (Trig.sinPartial (Q'.abs B) (1 + d) + B)
        ≈ (Trig.sinPartial (Q'.abs B) (1 + d) + -(Trig.sinTerm (Q'.abs B) 0)) :=
      Q'.add_eqv_congr_left _ _ _ eB
    have e5 := YMGap.Constructive.Q'.abs_eqv_congr e4
    have hchain := Q'.eqv_trans _ _ _ e2 (Q'.eqv_trans _ _ _ e3 e5)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hchain) hsa

/-! ## 2. The two product magnitude bounds -/

/-- **Cosine product block bound.**  `|cosFull A·(cosFull B − 1)| ≤ 2·termAbs |B| 2`
via `abs_mul_equiv`, `leRat_mul`, `|cosFull A| ≤ 1` and `cosFull_small_angle_leRat`. -/
theorem cosBlock_leRat (A : Q') {B : Q'} (hB1 : Q'.abs B ≤ 1) :
    CReal.leRat (CReal.abs (CReal.mul (TrigAdd.cosFull A)
        (CReal.add (TrigAdd.cosFull B) (CReal.neg (CReal.ofQ' 1)))))
      (ExpNeg.termAbs (Q'.abs B) 2 + ExpNeg.termAbs (Q'.abs B) 2) := by
  have hnn : (0 : Q') ≤ ExpNeg.termAbs (Q'.abs B) 2 + ExpNeg.termAbs (Q'.abs B) 2 :=
    Q'.zero_le_add _ _ (ExpNeg.termAbs_nonneg _ (Q'.abs_nonneg B) 2)
      (ExpNeg.termAbs_nonneg _ (Q'.abs_nonneg B) 2)
  have hprod : CReal.leRat
      (CReal.mul (CReal.abs (TrigAdd.cosFull A))
        (CReal.abs (CReal.add (TrigAdd.cosFull B) (CReal.neg (CReal.ofQ' 1)))))
      ((1 : Q') * (ExpNeg.termAbs (Q'.abs B) 2 + ExpNeg.termAbs (Q'.abs B) 2)) :=
    CReal.leRat_mul
      (JacobiQuadResidualClose.abs_cosFull_leRat_one A)
      (RcQuadResidualClose.cosFull_small_angle_leRat hB1)
      (RcQuadResidualClose.geRat_abs _)
      (RcQuadResidualClose.geRat_abs _)
      (by decide) hnn
  have hmono : CReal.leRat
      (CReal.mul (CReal.abs (TrigAdd.cosFull A))
        (CReal.abs (CReal.add (TrigAdd.cosFull B) (CReal.neg (CReal.ofQ' 1)))))
      (ExpNeg.termAbs (Q'.abs B) 2 + ExpNeg.termAbs (Q'.abs B) 2) :=
    CReal.leRat_mono hprod (Q'.le_of_eqv (Q'.one_mul_eqv _))
  exact CReal.leRat_of_equiv
    (RcQuadResidualClose.abs_mul_equiv (TrigAdd.cosFull A)
      (CReal.add (TrigAdd.cosFull B) (CReal.neg (CReal.ofQ' 1)))) hmono

/-- **Sine product block bound.**  `|sinFull A·(sinFull B − B)| ≤ 2·termAbs |B| 3`
via `abs_mul_equiv`, `leRat_mul`, `|sinFull A| ≤ 1` and the new
`sinFull_small_angle_leRat`. -/
theorem sinBlock_leRat (A : Q') {B : Q'} (hB1 : Q'.abs B ≤ 1) :
    CReal.leRat (CReal.abs (CReal.mul (TrigAdd.sinFull A)
        (CReal.add (TrigAdd.sinFull B) (CReal.neg (CReal.ofQ' B)))))
      (ExpNeg.termAbs (Q'.abs B) 3 + ExpNeg.termAbs (Q'.abs B) 3) := by
  have hnn : (0 : Q') ≤ ExpNeg.termAbs (Q'.abs B) 3 + ExpNeg.termAbs (Q'.abs B) 3 :=
    Q'.zero_le_add _ _ (ExpNeg.termAbs_nonneg _ (Q'.abs_nonneg B) 3)
      (ExpNeg.termAbs_nonneg _ (Q'.abs_nonneg B) 3)
  have hprod : CReal.leRat
      (CReal.mul (CReal.abs (TrigAdd.sinFull A))
        (CReal.abs (CReal.add (TrigAdd.sinFull B) (CReal.neg (CReal.ofQ' B)))))
      ((1 : Q') * (ExpNeg.termAbs (Q'.abs B) 3 + ExpNeg.termAbs (Q'.abs B) 3)) :=
    CReal.leRat_mul
      (JacobiQuadResidualClose.abs_sinFull_leRat_one A)
      (sinFull_small_angle_leRat hB1)
      (RcQuadResidualClose.geRat_abs _)
      (RcQuadResidualClose.geRat_abs _)
      (by decide) hnn
  have hmono : CReal.leRat
      (CReal.mul (CReal.abs (TrigAdd.sinFull A))
        (CReal.abs (CReal.add (TrigAdd.sinFull B) (CReal.neg (CReal.ofQ' B)))))
      (ExpNeg.termAbs (Q'.abs B) 3 + ExpNeg.termAbs (Q'.abs B) 3) :=
    CReal.leRat_mono hprod (Q'.le_of_eqv (Q'.one_mul_eqv _))
  exact CReal.leRat_of_equiv
    (RcQuadResidualClose.abs_mul_equiv (TrigAdd.sinFull A)
      (CReal.add (TrigAdd.sinFull B) (CReal.neg (CReal.ofQ' B)))) hmono

/-! ## 3. The honest algebraic residual and the `RcSDResidual` assembly -/

/-- The regrouped `Rc`: `cosFull(2θ)·(cosFull(2h) − 1)`. -/
abbrev cosTerm2 (θ h : Q') : CReal :=
  CReal.mul (TrigAdd.cosFull ((2 : Q') * θ))
    (CReal.add (TrigAdd.cosFull ((2 : Q') * h)) (CReal.neg (CReal.ofQ' 1)))

/-- The regrouped `Rc`: `sinFull(2θ)·(sinFull(2h) − 2h)`. -/
abbrev sinTerm2 (θ h : Q') : CReal :=
  CReal.mul (TrigAdd.sinFull ((2 : Q') * θ))
    (CReal.add (TrigAdd.sinFull ((2 : Q') * h)) (CReal.neg (CReal.ofQ' ((2 : Q') * h))))

/-- **The honest algebraic residual.**  Everything analytic in `RcSDResidual` is
proved elsewhere in this module; what remains are three purely algebraic facts:

* `step0` — the index-wise ring identity `fdRemC ≃ (amp+amp)·Rc`;
* `regroup` — the index-wise ring identity
  `Rc ≃ cosFull(2θ)·(cosFull(2h)−1) − sinFull(2θ)·(sinFull(2h)−2h)`
  (the `cosFull_add_signed` rewrite plus the elementary product regrouping);
* `fold` — the rational fold `2·termAbs|2h|2 + 2·termAbs|2h|3 ≤ (16/3)·(|h|·|h|)`
  on `|h| ≤ ½` (equivalently `2|h| ≤ 1`).

No trig/analytic content survives; inhabiting this closes the per-factor chain. -/
structure RcAlgResidual (q : Q') (k : Nat) (θ : Q') : Type where
  /-- The `step0` ring identity `fdRemC ≃ (amp+amp)·Rc`. -/
  step0 : ∀ h : Q',
    CReal.Equiv (fdRemC (Fk q k) (dk q k θ) θ h)
      (CReal.mul (CReal.ofQ' (amp q k + amp q k)) (RcQuadResidualClose.Rc θ h))
  /-- The `regroup` ring identity `Rc ≃ cosBlock − sinBlock`. -/
  regroup : ∀ h : Q',
    CReal.Equiv (RcQuadResidualClose.Rc θ h)
      (CReal.add (cosTerm2 θ h) (CReal.neg (sinTerm2 θ h)))
  /-- The rational fold `2·termAbs|2h|2 + 2·termAbs|2h|3 ≤ (16/3)·(|h|·|h|)`. -/
  fold : ∀ h : Q', (0 : Q') < Q'.abs h → Q'.abs h ≤ HalfPow.half →
    ((ExpNeg.termAbs (Q'.abs ((2 : Q') * h)) 2 + ExpNeg.termAbs (Q'.abs ((2 : Q') * h)) 2)
      + (ExpNeg.termAbs (Q'.abs ((2 : Q') * h)) 3 + ExpNeg.termAbs (Q'.abs ((2 : Q') * h)) 3))
      ≤ JacobiQuadResidualClose.kFactor * (Q'.abs h * Q'.abs h)

/-- **From the algebraic residual to `RcSDResidual`.**  `step0` passes through;
`sdBound` is `regroup` (transferring `abs`) + triangle (`leRat_abs_add`) + the two
proved product magnitude bounds + `fold`. -/
def rcSDResidual_of_alg {q : Q'} (k : Nat) (θ : Q') (H : RcAlgResidual q k θ) :
    RcQuadResidualClose.RcSDResidual q k θ where
  step0 := H.step0
  sdBound := by
    intro h hpos hle
    have hB1 : Q'.abs ((2 : Q') * h) ≤ 1 := absTwoH_le_one hle
    have hT1 := cosBlock_leRat ((2 : Q') * θ) hB1
    have hT2 := sinBlock_leRat ((2 : Q') * θ) hB1
    have hnegT2 : CReal.leRat (CReal.abs (CReal.neg (sinTerm2 θ h)))
        (ExpNeg.termAbs (Q'.abs ((2 : Q') * h)) 3 + ExpNeg.termAbs (Q'.abs ((2 : Q') * h)) 3) :=
      CReal.leRat_of_equiv (JacobiQuadResidualClose.absneg_equiv (sinTerm2 θ h)) hT2
    have htri := RcQuadResidualClose.leRat_abs_add hT1 hnegT2
    have hRc := CReal.leRat_of_equiv (CReal.abs_equiv_congr (H.regroup h)) htri
    exact CReal.leRat_mono hRc (H.fold h hpos hle)

/-! ## 4. Downstream wiring: the per-factor chain, unconditional on `RcAlgResidual` -/

/-- `RcAlgResidual → RcQuadResidual` (through the proved `rcQuadResidual_of_sd`). -/
def rcQuadResidual_of_alg {q : Q'} (hq : (0 : Q') < q) (k : Nat) (θ : Q')
    (H : RcAlgResidual q k θ) :
    JacobiQuadResidualClose.RcQuadResidual q k θ :=
  RcQuadResidualClose.rcQuadResidual_of_sd hq k θ (rcSDResidual_of_alg k θ H)

/-- `RcAlgResidual → FDDerivDataC` — the full per-factor finite-difference
derivative, closed once the algebraic residual is inhabited. -/
def fdderiv_of_alg {q : Q'} (hq : (0 : Q') < q) (k : Nat) (θ : Q')
    (H : RcAlgResidual q k θ) :
    FDDerivDataC (Fk q k) (dk q k θ) θ :=
  JacobiQuadResidualClose.jacobiFactorFDDeriv_of_rc hq k θ (rcQuadResidual_of_alg hq k θ H)

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms absTwoH_le_one
#print axioms sinFull_small_angle_leRat
#print axioms cosBlock_leRat
#print axioms sinBlock_leRat
#print axioms rcSDResidual_of_alg
#print axioms rcQuadResidual_of_alg
#print axioms fdderiv_of_alg

end YMGap.Continuum.RcSDResidualClose
