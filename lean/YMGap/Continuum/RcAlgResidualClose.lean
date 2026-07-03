/-
# Closing the rational `fold` of `RcAlgResidual`, and reducing the per-factor
chain to a pure CReal ring residual

`RcSDResidualClose.RcAlgResidual q k θ` has three Type-level fields:

* `step0`   — the index-wise CReal ring identity `fdRemC ≃ (amp+amp)·Rc`;
* `regroup` — the index-wise CReal ring identity
  `Rc ≃ cosFull(2θ)·(cosFull(2h)−1) − sinFull(2θ)·(sinFull(2h)−2h)`;
* `fold`    — the *purely rational* budget
  `2·termAbs|2h|2 + 2·termAbs|2h|3 ≤ (16/3)·(|h|·|h|)` on `|h| ≤ ½`.

## What is GENUINELY proved here

* **`fold_bound`** — the `fold` field, discharged UNCONDITIONALLY.  This is
  strictly rational: `|2h| ≈ 2|h|`, `termAbs (2|h|) 2 ≈ 2|h|²`,
  `termAbs (2|h|) 3 ≈ (4/3)|h|³`, so the left side is `4|h|² + (8/3)|h|³`; the
  right side is `(16/3)|h|² = 4|h|² + (4/3)|h|²`, and `(8/3)|h|³ ≤ (4/3)|h|²`
  follows from `2|h| ≤ 1` (`mul_le_mul_of_nonneg_left`).  All constant
  combinations are closed and discharged by `decide`; the only variable content
  is factored through the reusable `cmul_gen` monomial-rearrangement lemma and
  `TrigAdd.termAbs_eqv_congr`.

  Supporting reusable atoms proved here: `cmul_gen`, `add_mul_eqv`,
  `termAbs_two_eqv`, `termAbs_three_eqv`, `t2eq`, `t3eq`, `fold_bound_core`.

## The honest residual (AGENTS.md Rule 6)

`RcRingResidual` — the two *pure CReal ring identities* `step0` and `regroup`
that remain.  No analytic or rational content survives in it (the analytic heart
was discharged in `RcSDResidualClose`/`RcQuadResidualClose`, the rational `fold`
here).  Inhabiting `RcRingResidual` closes the whole per-factor chain
(`rcAlgResidual_of_ring → RcAlgResidual → FDDerivDataC`).

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.
-/

import YMGap.Continuum.RcSDResidualClose

namespace YMGap.Continuum.RcAlgResidualClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.TsumDeriv
open YMGap.Continuum.JacobiFactorFDDeriv (Fk dk)
open YMGap.Continuum.JTPInstance (amp)

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Reusable rational rearrangement atoms -/

/-- **`cmul_gen`.**  `(k1·x)·(k2·y) ≈ (k1·k2)·(x·y)` — the monomial/coefficient
rearrangement, by associativity+commutativity only. -/
theorem cmul_gen (k1 k2 x y : Q') : ((k1 * x) * (k2 * y)) ≈ ((k1 * k2) * (x * y)) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv k1 x (k2 * y)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left k1 _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv x k2 y))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left k1 _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv x k2))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left k1 _ _ (Q'.mul_assoc_eqv k2 x y)) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv k1 k2 (x * y))

/-- **`add_mul_eqv`.**  `(x+y)·c ≈ x·c + y·c` (right-distributivity from the
left-distributivity `mul_add_eqv` plus commutativity). -/
theorem add_mul_eqv (x y c : Q') : ((x + y) * c) ≈ (x * c + y * c) := by
  refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv (x + y) c) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv c x y) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.mul_comm_eqv c x)) ?_
  exact Q'.add_eqv_congr_left _ _ _ (Q'.mul_comm_eqv c y)

/-! ## 2. The two `termAbs` value lemmas -/

/-- `termAbs c 2 ≈ (c·c)·(1/2)`. -/
theorem termAbs_two_eqv (c : Q') :
    (ExpNeg.termAbs c 2) ≈ ((c * c) * Q'.mkPos 1 2 (by decide)) := by
  have s2 : ExpNeg.termAbs c 2
      = (1 : Q') * (c * Q'.mkPos 1 1 (by decide)) * (c * Q'.mkPos 1 2 (by decide)) := rfl
  rw [s2]
  -- (1 * (c * M1)) * (c * M2) ≈ (c*c) * M2
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv (c * Q'.mkPos 1 1 (by decide)))) ?_
  -- (c * M1) * (c * M2) ≈ (c*c) * M2
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left c (Q'.mkPos 1 1 (by decide)) 1 (by decide))) ?_
  -- (c * 1) * (c * M2) ≈ (c*c) * M2
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_one_eqv c)) ?_
  -- c * (c * M2) ≈ (c*c) * M2
  exact Q'.eqv_symm (Q'.mul_assoc_eqv c c (Q'.mkPos 1 2 (by decide)))

/-- `termAbs c 3 ≈ ((c·c)·c)·(1/6)`. -/
theorem termAbs_three_eqv (c : Q') :
    (ExpNeg.termAbs c 3) ≈ (((c * c) * c) * Q'.mkPos 1 6 (by decide)) := by
  have s3 : ExpNeg.termAbs c 3
      = ExpNeg.termAbs c 2 * (c * Q'.mkPos 1 3 (by decide)) := rfl
  rw [s3]
  -- termAbs c 2 * (c * M3) ≈ ((c*c)*c) * M6
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (termAbs_two_eqv c)) ?_
  -- ((c*c)*M2) * (c*M3) ≈ ((c*c)*c) * M6
  refine Q'.eqv_trans _ _ _
    (cmul_gen (c * c) c (Q'.mkPos 1 2 (by decide)) (Q'.mkPos 1 3 (by decide))) ?_
  -- ((c*c)*c) * (M2*M3) ≈ ((c*c)*c) * M6
  exact Q'.mul_eqv_congr_left _ _ _ (by decide)

/-! ## 3. The two normalized `termAbs (2a)` values -/

/-- `termAbs (2a) 2 ≈ 2·(a·a)`. -/
theorem t2eq (a : Q') : (ExpNeg.termAbs ((2 : Q') * a) 2) ≈ ((2 : Q') * (a * a)) := by
  refine Q'.eqv_trans _ _ _ (termAbs_two_eqv (2 * a)) ?_
  -- ((2a)*(2a)) * M2 ≈ 2*(a*a)
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ (cmul_gen 2 2 a a)) ?_
  -- ((2*2)*(a*a)) * M2 ≈ 2*(a*a)
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv (2 * 2) (a * a) (Q'.mkPos 1 2 (by decide))) ?_
  -- (2*2) * ((a*a) * M2) ≈ 2*(a*a)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_comm_eqv (a * a) (Q'.mkPos 1 2 (by decide)))) ?_
  -- (2*2) * (M2 * (a*a)) ≈ 2*(a*a)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (2 * 2) (Q'.mkPos 1 2 (by decide)) (a * a))) ?_
  -- ((2*2)*M2) * (a*a) ≈ 2*(a*a)
  exact Q'.mul_eqv_congr_right _ _ _ (by decide)

/-- `termAbs (2a) 3 ≈ (4/3)·((a·a)·a)`. -/
theorem t3eq (a : Q') :
    (ExpNeg.termAbs ((2 : Q') * a) 3) ≈ ((Q'.mkPos 4 3 (by decide)) * ((a * a) * a)) := by
  refine Q'.eqv_trans _ _ _ (termAbs_three_eqv (2 * a)) ?_
  -- (((2a)*(2a))*(2a)) * M6 ≈ mkPos43 * ((a*a)*a)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ _ (cmul_gen 2 2 a a))
        (cmul_gen (2 * 2) 2 (a * a) a))) ?_
  -- (((2*2)*2)*((a*a)*a)) * M6 ≈ mkPos43 * ((a*a)*a)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv ((2 * 2) * 2) ((a * a) * a) (Q'.mkPos 1 6 (by decide))) ?_
  -- ((2*2)*2) * (((a*a)*a) * M6) ≈ mkPos43 * ((a*a)*a)
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv ((a * a) * a) (Q'.mkPos 1 6 (by decide)))) ?_
  -- ((2*2)*2) * (M6 * ((a*a)*a)) ≈ mkPos43 * ((a*a)*a)
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv ((2 * 2) * 2) (Q'.mkPos 1 6 (by decide)) ((a * a) * a))) ?_
  -- (((2*2)*2)*M6) * ((a*a)*a) ≈ mkPos43 * ((a*a)*a)
  exact Q'.mul_eqv_congr_right _ _ _ (by decide)

/-! ## 4. The rational fold, general and instantiated -/

/-- **`fold_bound_core`.**  The rational budget in a value-generic form: for any
`a ≥ 0` with `2a ≤ 1` and any `B ≈ 2a`,
`2·termAbs B 2 + 2·termAbs B 3 ≤ (16/3)·(a·a)`. -/
theorem fold_bound_core (a B : Q') (haa_nn : (0 : Q') ≤ a) (h2a : (2 : Q') * a ≤ 1)
    (hB : B ≈ (2 : Q') * a) :
    ((ExpNeg.termAbs B 2 + ExpNeg.termAbs B 2) + (ExpNeg.termAbs B 3 + ExpNeg.termAbs B 3))
      ≤ JacobiQuadResidualClose.kFactor * (a * a) := by
  have haa : (0 : Q') ≤ a * a := Q'.mul_nonneg _ _ haa_nn haa_nn
  -- termAbs B k ≈ termAbs (2a) k, then to closed values
  have hb2 : (ExpNeg.termAbs B 2) ≈ (ExpNeg.termAbs ((2 : Q') * a) 2) :=
    YMGap.Constructive.TrigAdd.termAbs_eqv_congr hB 2
  have hb3 : (ExpNeg.termAbs B 3) ≈ (ExpNeg.termAbs ((2 : Q') * a) 3) :=
    YMGap.Constructive.TrigAdd.termAbs_eqv_congr hB 3
  have hT2 : (ExpNeg.termAbs B 2) ≈ ((2 : Q') * (a * a)) := Q'.eqv_trans _ _ _ hb2 (t2eq a)
  have hT3 : (ExpNeg.termAbs B 3) ≈ ((Q'.mkPos 4 3 (by decide)) * ((a * a) * a)) :=
    Q'.eqv_trans _ _ _ hb3 (t3eq a)
  -- 2·termAbs B 2 ≈ 4·(a·a)
  have hsum2 : ((ExpNeg.termAbs B 2) + (ExpNeg.termAbs B 2)) ≈ ((4 : Q') * (a * a)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hT2) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hT2) ?_
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (add_mul_eqv 2 2 (a * a))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  -- 2·termAbs B 3 ≈ (8/3)·((a·a)·a)
  have hsum3 : ((ExpNeg.termAbs B 3) + (ExpNeg.termAbs B 3))
      ≈ ((Q'.mkPos 8 3 (by decide)) * ((a * a) * a)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hT3) ?_
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hT3) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (add_mul_eqv (Q'.mkPos 4 3 (by decide)) (Q'.mkPos 4 3 (by decide)) ((a * a) * a))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  -- LHS ≈ 4·(a·a) + (8/3)·((a·a)·a)
  have hLHS : (((ExpNeg.termAbs B 2 + ExpNeg.termAbs B 2)
      + (ExpNeg.termAbs B 3 + ExpNeg.termAbs B 3)))
      ≈ (((4 : Q') * (a * a)) + ((Q'.mkPos 8 3 (by decide)) * ((a * a) * a))) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ hsum2) ?_
    exact Q'.add_eqv_congr_left _ _ _ hsum3
  -- cube bound: (8/3)·((a·a)·a) ≤ (4/3)·(a·a)
  have hc_nn : (0 : Q') ≤ (Q'.mkPos 4 3 (by decide)) * (a * a) :=
    Q'.mul_nonneg _ _ (by decide) haa
  have hcube : ((Q'.mkPos 8 3 (by decide)) * ((a * a) * a))
      ≤ ((Q'.mkPos 4 3 (by decide)) * (a * a)) := by
    have e1 : ((Q'.mkPos 8 3 (by decide)) * ((a * a) * a))
        ≈ (((Q'.mkPos 4 3 (by decide)) * (a * a)) * ((2 : Q') * a)) := by
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _ _ _ (cmul_gen (Q'.mkPos 4 3 (by decide)) 2 (a * a) a) ?_
      exact Q'.mul_eqv_congr_right _ _ _ (by decide)
    have hmul : (((Q'.mkPos 4 3 (by decide)) * (a * a)) * ((2 : Q') * a))
        ≤ (((Q'.mkPos 4 3 (by decide)) * (a * a)) * (1 : Q')) :=
      Q'.mul_le_mul_of_nonneg_left ((2 : Q') * a) 1
        ((Q'.mkPos 4 3 (by decide)) * (a * a)) h2a hc_nn
    have e2' : (((Q'.mkPos 4 3 (by decide)) * (a * a)) * (1 : Q'))
        ≈ ((Q'.mkPos 4 3 (by decide)) * (a * a)) := Q'.mul_one_eqv _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) (Q'.le_trans' _ _ _ hmul (Q'.le_of_eqv e2'))
  -- RHS split: 4·(a·a) + (4/3)·(a·a) ≈ (16/3)·(a·a)
  have hRHS : (((4 : Q') * (a * a)) + ((Q'.mkPos 4 3 (by decide)) * (a * a)))
      ≈ (JacobiQuadResidualClose.kFactor * (a * a)) := by
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (add_mul_eqv 4 (Q'.mkPos 4 3 (by decide)) (a * a))) ?_
    exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  -- combine
  have hstep : (((4 : Q') * (a * a)) + ((Q'.mkPos 8 3 (by decide)) * ((a * a) * a)))
      ≤ (((4 : Q') * (a * a)) + (Q'.mkPos 4 3 (by decide)) * (a * a)) :=
    Q'.add_le_add_left _ _ _ hcube
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hLHS) ?_
  exact Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hRHS)

/-- **`fold_bound`.**  The `fold` field of `RcAlgResidual`, proved unconditionally. -/
theorem fold_bound {θ : Q'} (h : Q') (hpos : (0 : Q') < Q'.abs h)
    (hle : Q'.abs h ≤ HalfPow.half) :
    ((ExpNeg.termAbs (Q'.abs ((2 : Q') * h)) 2 + ExpNeg.termAbs (Q'.abs ((2 : Q') * h)) 2)
      + (ExpNeg.termAbs (Q'.abs ((2 : Q') * h)) 3 + ExpNeg.termAbs (Q'.abs ((2 : Q') * h)) 3))
      ≤ JacobiQuadResidualClose.kFactor * (Q'.abs h * Q'.abs h) := by
  have habs2 : Q'.abs (2 : Q') = 2 := by unfold Q'.abs; rw [if_pos (by decide)]
  have hB : (Q'.abs ((2 : Q') * h)) ≈ ((2 : Q') * Q'.abs h) := by
    refine Q'.eqv_trans _ _ _ (RcQuadResidualClose.q_abs_mul_eqv 2 h) ?_
    rw [habs2]; exact Q'.eqv_refl _
  have h2a : (2 : Q') * Q'.abs h ≤ 1 := by
    have s1 : (2 : Q') * Q'.abs h ≤ (2 : Q') * HalfPow.half :=
      Q'.mul_le_mul_of_nonneg_left (Q'.abs h) HalfPow.half 2 hle (by decide)
    exact Q'.le_trans' _ _ _ s1 (Q'.le_of_eqv (by decide))
  exact fold_bound_core (Q'.abs h) (Q'.abs ((2 : Q') * h)) (Q'.abs_nonneg h) h2a hB

/-! ## 5. The honest CReal ring residual and the per-factor chain -/

/-- **The honest residual: the two pure CReal ring identities.**  Everything
rational (`fold`) is proved above; everything analytic is proved in
`RcSDResidualClose`/`RcQuadResidualClose`.  What remains are the two index-wise
CReal ring identities. -/
structure RcRingResidual (q : Q') (k : Nat) (θ : Q') : Type where
  /-- `step0` — the ring identity `fdRemC ≃ (amp+amp)·Rc`. -/
  step0 : ∀ h : Q',
    CReal.Equiv (fdRemC (Fk q k) (dk q k θ) θ h)
      (CReal.mul (CReal.ofQ' (amp q k + amp q k)) (RcQuadResidualClose.Rc θ h))
  /-- `regroup` — the ring identity `Rc ≃ cosBlock − sinBlock`. -/
  regroup : ∀ h : Q',
    CReal.Equiv (RcQuadResidualClose.Rc θ h)
      (CReal.add (RcSDResidualClose.cosTerm2 θ h) (CReal.neg (RcSDResidualClose.sinTerm2 θ h)))

/-- **From the ring residual to `RcAlgResidual`** — the rational `fold` field is
supplied by the proved `fold_bound`. -/
def rcAlgResidual_of_ring {q : Q'} (k : Nat) (θ : Q') (H : RcRingResidual q k θ) :
    RcSDResidualClose.RcAlgResidual q k θ where
  step0 := H.step0
  regroup := H.regroup
  fold := fun h hpos hle => fold_bound (θ := θ) h hpos hle

/-- **`RcRingResidual → RcQuadResidual`** (through the proved assembly chain). -/
def rcQuadResidual_of_ring {q : Q'} (hq : (0 : Q') < q) (k : Nat) (θ : Q')
    (H : RcRingResidual q k θ) :
    JacobiQuadResidualClose.RcQuadResidual q k θ :=
  RcSDResidualClose.rcQuadResidual_of_alg hq k θ (rcAlgResidual_of_ring k θ H)

/-- **`RcRingResidual → FDDerivDataC`** — the per-factor finite-difference
derivative, closed once the two CReal ring identities are supplied. -/
def fdderiv_of_ring {q : Q'} (hq : (0 : Q') < q) (k : Nat) (θ : Q')
    (H : RcRingResidual q k θ) :
    FDDerivDataC (Fk q k) (dk q k θ) θ :=
  RcSDResidualClose.fdderiv_of_alg hq k θ (rcAlgResidual_of_ring k θ H)

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms cmul_gen
#print axioms add_mul_eqv
#print axioms termAbs_two_eqv
#print axioms termAbs_three_eqv
#print axioms t2eq
#print axioms t3eq
#print axioms fold_bound_core
#print axioms fold_bound
#print axioms rcAlgResidual_of_ring
#print axioms rcQuadResidual_of_ring
#print axioms fdderiv_of_ring

end YMGap.Continuum.RcAlgResidualClose
