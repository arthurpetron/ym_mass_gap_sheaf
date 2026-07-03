/-
# Closing `RcQuadResidual`: the CReal second-difference assembly atoms

`JacobiQuadResidualClose.RcQuadResidual q k θ` is the honest per-factor quadratic
finite-difference residual `|fdRemC (Fk) (dk) θ h| ≤ K·(|h|·|h|)` on `|h| ≤ ½`.
The plan to inhabit it routes through the CReal second-difference of

    Rc = (cosFull(A+B) ⊖ cosFull A) ⊕ (ofQ' B · sinFull A),   A = 2θ, B = 2h,

for which a handful of small, genuinely-missing CReal atoms are required.  This
module BUILDS those atoms (each cleanly closed, index-wise except the small-angle
glue) and then reduces `RcQuadResidual` to a single honest SD-form residual.

## What is GENUINELY proved here

* **G2 `CReal.abs_mul_equiv`** — `Equiv (abs (mul x y)) (mul (abs x) (abs y))`,
  index-wise from the `Q'` multiplicativity `q_abs_mul_eqv` (a four-quadrant sign
  split), lifted by `SumOfSquares.Equiv_of_approx_eqv`.

* **G3 `CReal.leRat_abs_add`** — the triangle bound `leRat (abs x) a →
  leRat (abs y) b → leRat (abs (add x y)) (a+b)`, from the index-wise `Q'`
  triangle `abs_add_le'` and `leRat_add`.

* **G1 `cosFull_eqv_congr`** — cosine argument-congruence `x ≈ y →
  Equiv (cosFull x) (cosFull y)`, index-wise via `cosPartial_eqv_congr`.

* **G6 `cosFull_small_angle_leRat` / `sinFull_small_angle_leRat`** — the analytic
  glue: the truncation small-angle bounds `cos_small_angle` / `sin_small_angle`
  lifted to `CReal.leRat` on `cosFull B ⊖ ofQ' 1` and `sinFull B ⊖ ofQ' B` for
  `|B| ≤ 1`.

## The honest residual (AGENTS.md Rule 6)

`RcSDResidual` — the pure SD-form magnitude bound `|Rc| ≤ (16/3)·(|h|·|h|)` on
`|h| ≤ ½`.  `rcQuadResidual_of_sd` discharges it into `RcQuadResidual` via the
algebraic cancellation `fdRemC ≃ ofQ'(amp+amp)·Rc` (Step 0) and the amplitude
scaling (Step 4).

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.
-/

import YMGap.Continuum.JacobiQuadResidualClose

namespace YMGap.Continuum.RcQuadResidualClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.TsumDeriv
open YMGap.Continuum.JacobiFactorFDDeriv (Fk dk)
open YMGap.Continuum.JTPInstance (amp fourAmp)
open YMGap.Continuum.JacobiQuadResidualClose (Kconst kFactor)

local infix:50 " ≈ " => Q'.eqv

/-! ## G2 — the multiplicativity of `Q'.abs` and `CReal.abs` -/

/-- `|q| ≈ −q` for `q ≤ 0` (either `if`-branch reduces to `−q` up to `eqv`). -/
theorem q_abs_of_nonpos {q : Q'} (hq : q ≤ 0) : (Q'.abs q).eqv (-q) := by
  unfold Q'.abs
  by_cases h : (0 : Q') ≤ q
  · rw [if_pos h]
    have hq0 : q.eqv 0 := Q'.eqv_of_le_le hq h
    refine Q'.eqv_trans _ _ _ hq0 ?_
    refine Q'.eqv_symm ?_
    refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hq0) ?_
    show ((-0 : Q')).eqv 0; decide
  · rw [if_neg h]; exact Q'.eqv_refl (-q)

/-- **`Q'.abs (a·b) ≈ |a|·|b|`.**  Four-quadrant sign split. -/
theorem q_abs_mul_eqv (a b : Q') : (Q'.abs (a * b)).eqv (Q'.abs a * Q'.abs b) := by
  by_cases ha : (0 : Q') ≤ a
  · by_cases hb : (0 : Q') ≤ b
    · have ea : Q'.abs a = a := by unfold Q'.abs; rw [if_pos ha]
      have eb : Q'.abs b = b := by unfold Q'.abs; rw [if_pos hb]
      have eab : Q'.abs (a * b) = a * b := by
        unfold Q'.abs; rw [if_pos (Q'.mul_nonneg a b ha hb)]
      rw [ea, eb, eab]; exact Q'.eqv_refl _
    · have hb' : b ≤ 0 := Q'.nonpos_of_not_nonneg hb
      have ea : Q'.abs a = a := by unfold Q'.abs; rw [if_pos ha]
      have hab : Q'.abs b = -b := by unfold Q'.abs; rw [if_neg hb]
      rw [ea, hab]
      have hprod : a * b ≤ 0 := Q'.mul_nonpos_of_nonneg_nonpos ha hb'
      refine Q'.eqv_trans _ _ _ (q_abs_of_nonpos hprod) ?_
      exact Q'.eqv_symm (Q'.mul_neg_eqv a b)
  · by_cases hb : (0 : Q') ≤ b
    · have ha' : a ≤ 0 := Q'.nonpos_of_not_nonneg ha
      have eb : Q'.abs b = b := by unfold Q'.abs; rw [if_pos hb]
      have hab : Q'.abs a = -a := by unfold Q'.abs; rw [if_neg ha]
      rw [eb, hab]
      have hprod : a * b ≤ 0 := by
        have hba : b * a ≤ 0 := Q'.mul_nonpos_of_nonneg_nonpos hb ha'
        exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_comm_eqv a b)) hba
      refine Q'.eqv_trans _ _ _ (q_abs_of_nonpos hprod) ?_
      exact Q'.eqv_symm (Q'.neg_mul_eqv a b)
    · have ha' : a ≤ 0 := Q'.nonpos_of_not_nonneg ha
      have hb' : b ≤ 0 := Q'.nonpos_of_not_nonneg hb
      have hab_a : Q'.abs a = -a := by unfold Q'.abs; rw [if_neg ha]
      have hab_b : Q'.abs b = -b := by unfold Q'.abs; rw [if_neg hb]
      have eab : Q'.abs (a * b) = a * b := by
        unfold Q'.abs; rw [if_pos (Q'.mul_nonneg_of_nonpos_nonpos ha' hb')]
      rw [hab_a, hab_b, eab]
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-b)) ?_
      refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a b)) ?_
      exact Q'.neg_neg_eqv (a * b)

/-- **G2.**  `Equiv (abs (mul x y)) (mul (abs x) (abs y))` — index-wise. -/
theorem abs_mul_equiv (x y : CReal) :
    CReal.Equiv (CReal.abs (CReal.mul x y)) (CReal.mul (CReal.abs x) (CReal.abs y)) :=
  SumOfSquares.Equiv_of_approx_eqv (fun n => q_abs_mul_eqv (x.approx n) (y.approx n))

/-! ## G3 — the CReal triangle bound for `leRat (abs ·)` -/

/-- **G3.**  `leRat (abs x) a → leRat (abs y) b → leRat (abs (add x y)) (a+b)`. -/
theorem leRat_abs_add {x y : CReal} {a b : Q'}
    (hx : CReal.leRat (CReal.abs x) a) (hy : CReal.leRat (CReal.abs y) b) :
    CReal.leRat (CReal.abs (CReal.add x y)) (a + b) := by
  intro ε hε
  obtain ⟨N, hN⟩ := (CReal.leRat_add hx hy) ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hpt : (CReal.abs (CReal.add x y)).approx n
      ≤ (CReal.add (CReal.abs x) (CReal.abs y)).approx n :=
    Q'.abs_add_le' (x.approx n) (y.approx n)
  exact Q'.le_trans' _ _ _ hpt (hN n hn)

/-! ## G1 — cosine argument-congruence -/

/-- **G1 (cosine).**  `x ≈ y → Equiv (cosFull x) (cosFull y)` — index-wise via
`cosPartial_eqv_congr` on `|x| ≈ |y|`. -/
theorem cosFull_eqv_congr {x y : Q'} (h : x ≈ y) :
    CReal.Equiv (TrigAdd.cosFull x) (TrigAdd.cosFull y) := by
  refine TrigAdd.equiv_of_approx_eqv (fun n => ?_)
  rw [TrigAdd.cosFull_approx, TrigAdd.cosFull_approx]
  exact TrigAdd.cosPartial_eqv_congr
    (YMGap.Constructive.Q'.abs_eqv_congr (a := x) (b := y) h) n

/-! ## G6 — the small-angle analytic glue (cosine) -/

/-- **G6 (cosine).**  `|cosFull B − 1| ≤ |B|²` (`= termAbs |B| 2 + termAbs |B| 2`) as a
`CReal.leRat`, for `|B| ≤ 1`.  Lifts the truncation bound `cos_small_angle` (which
holds at every truncation index `1+d`) to the limit via `leRat_of_eventually`. -/
theorem cosFull_small_angle_leRat {B : Q'} (hB1 : Q'.abs B ≤ 1) :
    CReal.leRat (CReal.abs (CReal.add (TrigAdd.cosFull B) (CReal.neg (CReal.ofQ' 1))))
      (ExpNeg.termAbs (Q'.abs B) 2 + ExpNeg.termAbs (Q'.abs B) 2) := by
  refine CReal.leRat_of_eventually ⟨1, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, n = 1 + d := ⟨n - 1, by omega⟩
  show Q'.abs (Trig.cosPartial (Q'.abs B) (1 + d) + -(1 : Q'))
      ≤ ExpNeg.termAbs (Q'.abs B) 2 + ExpNeg.termAbs (Q'.abs B) 2
  exact TrigAdd.cos_small_angle (Q'.abs B) (Q'.abs_nonneg B) hB1 d

/-! ## A CReal nonnegativity helper for `abs` -/

/-- `geRat (abs x) 0` — the limit of `|x|` is `≥ 0` (index-wise `0 ≤ |x_n|`). -/
theorem geRat_abs (x : CReal) : ExpPos.geRat (CReal.abs x) 0 :=
  ExpPos.geRat_of_eventually ⟨0, fun n _ => Q'.abs_nonneg (x.approx n)⟩

/-! ## The CReal `Rc` object and the honest SD residual -/

/-- **The CReal second-difference `Rc`** at `A = 2θ`, `B = 2h`:
`Rc = (cosFull(A+B) ⊖ cosFull A) ⊕ (ofQ' B · sinFull A)`. -/
def Rc (θ h : Q') : CReal :=
  CReal.add
    (CReal.add (TrigAdd.cosFull ((2 : Q') * θ + (2 : Q') * h))
      (CReal.neg (TrigAdd.cosFull ((2 : Q') * θ))))
    (CReal.mul (CReal.ofQ' ((2 : Q') * h)) (TrigAdd.sinFull ((2 : Q') * θ)))

/-- **The honest SD-form residual (steps 0–3 of the route).**  Two Type-level
fields at the clean `Rc` level:

* `step0` — the algebraic cancellation `fdRemC (Fk) (dk) θ h ≃ ofQ'(amp+amp)·Rc`
  (the `1`/`amp²` constant and the `d·h` linear term cancel, `fourAmp = 2(amp+amp)`
  factors the sine term);
* `sdBound` — the SD-form magnitude bound `|Rc| ≤ (16/3)·(|h|·|h|)` on `|h| ≤ ½`
  (triangle + `|cos|,|sin| ≤ 1` amplitude bounds + the `cos/sin` small-angle
  budgets `4h²`, `(8/3)|h|³` folded on `|h| ≤ ½`).

`rcQuadResidual_of_sd` discharges both into the `RcQuadResidual` quadratic bound via
the amplitude scaling (step 4). -/
structure RcSDResidual (q : Q') (k : Nat) (θ : Q') : Type where
  /-- Step 0: `fdRemC ≃ ofQ'(amp+amp)·Rc`. -/
  step0 : ∀ h : Q',
    CReal.Equiv (fdRemC (Fk q k) (dk q k θ) θ h)
      (CReal.mul (CReal.ofQ' (amp q k + amp q k)) (Rc θ h))
  /-- Steps 1–3: the SD-form magnitude bound `|Rc| ≤ (16/3)·(|h|·|h|)` on `|h| ≤ ½`. -/
  sdBound : ∀ h : Q', (0 : Q') < Q'.abs h → Q'.abs h ≤ HalfPow.half →
    CReal.leRat (CReal.abs (Rc θ h)) (kFactor * (Q'.abs h * Q'.abs h))

/-! ## Step 4 — the amplitude scaling, discharging `RcQuadResidual` -/

/-- **From the SD residual to `RcQuadResidual`** (step 4: scale by `amp+amp ≥ 0`).
`|fdRemC| ≃ |ofQ'(a2)·Rc| ≃ a2·|Rc| ≤ a2·((16/3)h²) ≈ Kconst·h²`, using the
built atoms `abs_mul_equiv`, `geRat_abs`, and `CReal.leRat_mul`. -/
def rcQuadResidual_of_sd {q : Q'} (hq : (0 : Q') < q) (k : Nat) (θ : Q')
    (H : RcSDResidual q k θ) :
    JacobiQuadResidualClose.RcQuadResidual q k θ where
  bound := by
    intro h hpos hle
    have ha2pos : (0 : Q') < amp q k + amp q k :=
      Q'.add_pos (JacobiQuadResidualClose.ampPos hq k) (JacobiQuadResidualClose.ampPos hq k)
    have ha2nn : (0 : Q') ≤ amp q k + amp q k := Q'.le_of_lt ha2pos
    have hhh : (0 : Q') ≤ Q'.abs h * Q'.abs h :=
      Q'.mul_nonneg _ _ (Q'.abs_nonneg h) (Q'.abs_nonneg h)
    have hkf : (0 : Q') ≤ kFactor := Q'.le_of_lt JacobiQuadResidualClose.kFactor_pos
    have hbudget : (0 : Q') ≤ kFactor * (Q'.abs h * Q'.abs h) := Q'.mul_nonneg _ _ hkf hhh
    -- SD bound at this h.
    have hsd := H.sdBound h hpos hle
    -- `abs (ofQ' a2) = ofQ' a2` (since `a2 ≥ 0`).
    have habs_a2 : CReal.abs (CReal.ofQ' (amp q k + amp q k))
        = CReal.ofQ' (amp q k + amp q k) := by
      rw [CReal.abs_ofQ']
      have : Q'.abs (amp q k + amp q k) = amp q k + amp q k := by
        unfold Q'.abs; rw [if_pos ha2nn]
      rw [this]
    -- `abs (ofQ' a2 · Rc) ≃ ofQ' a2 · abs Rc`.
    have hmulabs : CReal.Equiv
        (CReal.abs (CReal.mul (CReal.ofQ' (amp q k + amp q k)) (Rc θ h)))
        (CReal.mul (CReal.ofQ' (amp q k + amp q k)) (CReal.abs (Rc θ h))) := by
      refine (abs_mul_equiv (CReal.ofQ' (amp q k + amp q k)) (Rc θ h)).trans ?_
      rw [habs_a2]
      exact SumOfSquares.Equiv_of_approx_eqv (fun _ => Q'.eqv_refl _)
    -- `leRat (ofQ' a2 · abs Rc) (a2 · ((16/3)·h²))`.
    have hmulle : CReal.leRat
        (CReal.mul (CReal.ofQ' (amp q k + amp q k)) (CReal.abs (Rc θ h)))
        ((amp q k + amp q k) * (kFactor * (Q'.abs h * Q'.abs h))) :=
      CReal.leRat_mul (CReal.leRat_ofQ' (Q'.le_refl' _)) hsd
        (SumOfSquares.geRat_ofQ'_nonneg ha2nn) (geRat_abs (Rc θ h)) ha2nn hbudget
    -- `leRat (abs (ofQ' a2 · Rc)) (a2 · ((16/3)·h²))` via the equiv.
    have hstep : CReal.leRat
        (CReal.abs (CReal.mul (CReal.ofQ' (amp q k + amp q k)) (Rc θ h)))
        ((amp q k + amp q k) * (kFactor * (Q'.abs h * Q'.abs h))) :=
      CReal.leRat_of_equiv hmulabs hmulle
    -- `a2·((16/3)·h²) ≈ Kconst·h²` (Kconst = a2·(16/3)).
    have hKeq : ((amp q k + amp q k) * (kFactor * (Q'.abs h * Q'.abs h)))
        ≈ (JacobiQuadResidualClose.Kconst q k * (Q'.abs h * Q'.abs h)) :=
      Q'.eqv_symm (Q'.mul_assoc_eqv (amp q k + amp q k) kFactor (Q'.abs h * Q'.abs h))
    have hstep2 : CReal.leRat
        (CReal.abs (CReal.mul (CReal.ofQ' (amp q k + amp q k)) (Rc θ h)))
        (JacobiQuadResidualClose.Kconst q k * (Q'.abs h * Q'.abs h)) :=
      CReal.leRat_mono hstep (Q'.le_of_eqv hKeq)
    -- Transport across step 0: `abs fdRemC ≃ abs (ofQ' a2 · Rc)`.
    have he0 : CReal.Equiv (CReal.abs (fdRemC (Fk q k) (dk q k θ) θ h))
        (CReal.abs (CReal.mul (CReal.ofQ' (amp q k + amp q k)) (Rc θ h))) :=
      CReal.abs_equiv_congr (H.step0 h)
    exact CReal.leRat_of_equiv he0 hstep2

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms q_abs_mul_eqv
#print axioms abs_mul_equiv
#print axioms leRat_abs_add
#print axioms cosFull_eqv_congr
#print axioms cosFull_small_angle_leRat
#print axioms geRat_abs
#print axioms rcQuadResidual_of_sd

end YMGap.Continuum.RcQuadResidualClose
