/-
# Closing the two structural walls under `JacobiFactorFDDeriv.JacobiQuadResidual`

The per-factor `FDDerivDataC` for the Jacobi theta product is produced by
`JacobiFactorFDDeriv.jacobiFactorFDDeriv` FROM a `JacobiQuadResidual` — the honest
per-factor quadratic finite-difference bound `|fdRemC (Fk) (dk) θ h| ≤ K·h²` on
`|h| ≤ ½` (with `K = (32/3)·q^{2k+1}`).  That residual rests on the trig
second-difference bound of `Rc = cosFull(2θ+2h) − cosFull 2θ + 2h·sinFull 2θ`,
whose assembly the route reduces to TWO genuinely-missing structural CReal lemmas.

## What is GENUINELY proved here

* **Lemma A — the all-sign cosine addition law at the CReal level**
  (`cosFull_add_signed`): `cosFull (A+B) ≃ cosProdMinus A B` for *arbitrary* signed
  rational angles `A, B`.  A four-quadrant case split assembling the already-proved
  nonneg / negneg / posneg / negpos cores, with the mixed-sign cores fed by
  `PythFull.pythFull_of_reflection` (axiom-clean) through
  `oppositeSignCosCore_of_pyth`.  This removes the "the addition formula holds only
  per-quadrant" wall: the whole `Rc` rewrite `Rc ≃ cos·(cos−1) − sin·(sin−ofQ')` is
  now available for a *free* `θ`.

* **Lemma B — arbitrary-argument amplitude bounds at the CReal level**
  (`abs_cosFull_leRat_one`, `abs_sinFull_leRat_one`): `|cosFull x| ≤ 1` and
  `|sinFull x| ≤ 1` (as `CReal.leRat (abs ·) 1`) for *every* signed rational `x`.
  Proved from the CReal Pythagorean identity `cos²+sin² ≃ 1`
  (`pythFull_of_reflection`), the rational square-nonnegativity
  `SumOfSquares.q_mul_self_nonneg`, and the elementary `Q'` fact
  `t² ≤ B ∧ 1 ≤ B → |t| ≤ B` (`abs_le_of_mul_self_le`), extended to all `x` by
  `cosFull_even` / `sinFull_neg`.  This is the CORRECTED source (the `[0,1]`-only
  `abs_cosFull_approx_le_two` shortcut is unsound for a free `2θ`).

* **The `K = (32/3)·q^{2k+1}` coefficient and its positivity** (`Kconst`,
  `Kconst_num_pos`): the L4 constant is discharged concretely from `q > 0 ⇒
  q^{2k+1} > 0` (`ampPos`, a genuine `Q'.pow_pos`).

* **The wiring** (`jacobiQuadResidual_of_rc`, `jacobiFactorFDDeriv_of_rc`): from the
  pure quadratic `Rc`-bound residual, a `JacobiQuadResidual` (hence
  `jacobiFactorFDDeriv`) with the explicit `K` and proved `Knum`.

## The honest residual (AGENTS.md Rule 6)

`RcQuadResidual` — the pure trig second-difference quadratic bound (steps 0 and 4 of
the route: the `1`/`amp²` and `d·h` cancellation reducing `fdRemC` to `(amp+amp)·Rc`,
and the triangle+product magnitude bound of `Rc` using Lemma A, Lemma B and the
small-angle atoms `cos_small_angle`/`sin_small_angle`).  Everything the assembly
consumes — the all-sign addition law and the arbitrary-argument amplitude bounds —
is proved above; the residual is exactly their assembly into the `CReal.leRat`
quadratic bound, from which the target closes with the explicit `K` and `Knum`.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`, no custom axiom.
-/

import YMGap.Continuum.JacobiFactorFDDeriv
import YMGap.Constructive.PythFull
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.Sqrt
import YMGap.Constructive.ExpAdd

namespace YMGap.Continuum.JacobiQuadResidualClose

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.TsumDeriv
open YMGap.Continuum.JacobiFactorFDDeriv (Fk dk)
open YMGap.Continuum.JTPInstance (amp)

local infix:50 " ≈ " => Q'.eqv

/-! ## 0. Small `Q'` helpers -/

/-- `q^n > 0` for `q > 0` (genuine `Q'` power positivity, induction on `n`). -/
theorem powPos {q : Q'} (hq : (0 : Q') < q) : ∀ n : Nat, (0 : Q') < q ^ n
  | 0 => by
    show (0 : Q') < (1 : Q')
    exact CReal.pos_of_num_pos (by decide)
  | n + 1 => by
    show (0 : Q') < q * q ^ n
    exact Q'.mul_pos hq (powPos hq n)

/-- `amp q k = q^{2k+1} > 0` for `q > 0`. -/
theorem ampPos {q : Q'} (hq : (0 : Q') < q) (k : Nat) : (0 : Q') < amp q k :=
  powPos hq (2 * k + 1)

/-- `(-t)·(-t) ≈ t·t` (pure `Q'` sign algebra). -/
theorem negmul_self_eqv (t : Q') : ((-t) * (-t)) ≈ (t * t) := by
  refine Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv t (-t)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv t t)) ?_
  exact Q'.neg_neg_eqv (t * t)

/-- `|t|·|t| ≈ t·t`. -/
theorem abs_mul_self_eqv (t : Q') : (Q'.abs t * Q'.abs t) ≈ (t * t) := by
  by_cases ht : (0 : Q') ≤ t
  · have hat : Q'.abs t = t := by unfold Q'.abs; rw [if_pos ht]
    rw [hat]; exact Q'.eqv_refl (t * t)
  · have hat : Q'.abs t = -t := by unfold Q'.abs; rw [if_neg ht]
    rw [hat]; exact negmul_self_eqv t

/-- **`t² ≤ B` and `1 ≤ B` give `|t| ≤ B`.**  If `|t| ≤ 1` then `|t| ≤ 1 ≤ B`;
otherwise `1 ≤ |t|` so `|t| ≤ |t|·|t| = t·t ≤ B`.  Decidable case split, no LEM. -/
theorem abs_le_of_mul_self_le {t B : Q'} (hB1 : (1 : Q') ≤ B) (h : t * t ≤ B) :
    Q'.abs t ≤ B := by
  by_cases hb : Q'.abs t ≤ (1 : Q')
  · exact Q'.le_trans' _ _ _ hb hB1
  · have h1t : (1 : Q') ≤ Q'.abs t := TrigSignedAddFull.le_of_not_le hb
    have hnn : (0 : Q') ≤ Q'.abs t := Q'.abs_nonneg t
    have hstep : Q'.abs t ≤ Q'.abs t * Q'.abs t := by
      refine Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.one_mul_eqv (Q'.abs t))) ?_
      exact Q'.mul_le_mul_of_nonneg_right 1 (Q'.abs t) (Q'.abs t) h1t hnn
    have heq : (Q'.abs t * Q'.abs t) ≈ (t * t) := abs_mul_self_eqv t
    exact Q'.le_trans' _ _ _ hstep (Q'.le_trans' _ _ _ (Q'.le_of_eqv heq) h)

/-! ## 1. Lemma A — the all-sign cosine addition law -/

/-- **Lemma A (all-sign cosine addition law).**  For *arbitrary* signed rational
angles `A, B`, `cosFull (A+B) ≃ cosProdMinus A B` — the CReal cosine addition
formula with no sign restriction.  A four-quadrant case split (`0 ≤ A`, `0 ≤ B`)
assembling the already-proved quadrant cores; the two mixed-sign quadrants are fed
the opposite-sign core `oppositeSignCosCore_of_pyth pythFull_of_reflection`
(axiom-clean). -/
theorem cosFull_add_signed (A B : Q') :
    CReal.Equiv (TrigAdd.cosFull (A + B)) (TrigAdd.cosProdMinus A B) := by
  have oc : TrigSignedAdd.OppositeSignCosCore :=
    TrigSignedAddFull.oppositeSignCosCore_of_pyth PythFullProof.pythFull_of_reflection
  by_cases hA : (0 : Q') ≤ A
  · by_cases hB : (0 : Q') ≤ B
    · exact TrigAdd.cos_add_equiv_nonneg A B hA hB
    · exact TrigSignedAddFull.cos_add_equiv_posneg oc hA (TrigSignedAddFull.le_of_not_le hB)
  · by_cases hB : (0 : Q') ≤ B
    · exact TrigSignedAddFull.cos_add_equiv_negpos oc (TrigSignedAddFull.le_of_not_le hA) hB
    · exact TrigSignedAdd.cos_add_equiv_negneg
        (TrigSignedAddFull.le_of_not_le hA) (TrigSignedAddFull.le_of_not_le hB)

/-! ## 2. Lemma B — arbitrary-argument amplitude bounds `|cosFull|,|sinFull| ≤ 1` -/

/-- `Equiv (abs (neg x)) (abs x)` (index-wise `|−x_n| = |x_n|`). -/
theorem absneg_equiv (x : CReal) :
    CReal.Equiv (CReal.abs (CReal.neg x)) (CReal.abs x) := by
  intro ε hε
  refine ⟨0, fun n _ => ?_⟩
  have he : (Q'.abs (-(x.approx n))).eqv (Q'.abs (x.approx n)) := Q'.abs_neg' (x.approx n)
  refine ⟨?_, ?_⟩
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε))
  · exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv he)
      (Q'.add_le_self_of_nonneg _ ε (Q'.le_of_lt hε))

/-- **`|cosFull A| ≤ 1` for `A ≥ 0`.**  From `cos²+sin² ≃ 1` and `sin² ≥ 0`. -/
theorem abs_cosFull_leRat_one_nonneg {A : Q'} (hA : (0 : Q') ≤ A) :
    CReal.leRat (CReal.abs (TrigAdd.cosFull A)) 1 := by
  intro ε hε
  obtain ⟨N, hN⟩ := PythFullProof.pythFull_of_reflection.pyth A hA ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hpe : (TrigAdd.cosFull A).approx n * (TrigAdd.cosFull A).approx n
      + (TrigAdd.sinFull A).approx n * (TrigAdd.sinFull A).approx n ≤ 1 + ε := (hN n hn).1
  have hss : (0 : Q') ≤ (TrigAdd.sinFull A).approx n * (TrigAdd.sinFull A).approx n :=
    SumOfSquares.q_mul_self_nonneg _
  have hcc : (TrigAdd.cosFull A).approx n * (TrigAdd.cosFull A).approx n ≤ 1 + ε :=
    Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg _ _ hss) hpe
  have h1B : (1 : Q') ≤ 1 + ε := Q'.add_le_self_of_nonneg 1 ε (Q'.le_of_lt hε)
  exact abs_le_of_mul_self_le h1B hcc

/-- **`|sinFull A| ≤ 1` for `A ≥ 0`.**  From `cos²+sin² ≃ 1` and `cos² ≥ 0`. -/
theorem abs_sinFull_leRat_one_nonneg {A : Q'} (hA : (0 : Q') ≤ A) :
    CReal.leRat (CReal.abs (TrigAdd.sinFull A)) 1 := by
  intro ε hε
  obtain ⟨N, hN⟩ := PythFullProof.pythFull_of_reflection.pyth A hA ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hpe : (TrigAdd.cosFull A).approx n * (TrigAdd.cosFull A).approx n
      + (TrigAdd.sinFull A).approx n * (TrigAdd.sinFull A).approx n ≤ 1 + ε := (hN n hn).1
  have hcc : (0 : Q') ≤ (TrigAdd.cosFull A).approx n * (TrigAdd.cosFull A).approx n :=
    SumOfSquares.q_mul_self_nonneg _
  -- sin² ≤ cos²+sin² ≤ 1+ε
  have hss : (TrigAdd.sinFull A).approx n * (TrigAdd.sinFull A).approx n ≤ 1 + ε := by
    -- sin² ≤ sin²+cos² ≈ cos²+sin² ≤ 1+ε
    have h1 : (TrigAdd.sinFull A).approx n * (TrigAdd.sinFull A).approx n
        ≤ (TrigAdd.sinFull A).approx n * (TrigAdd.sinFull A).approx n
          + (TrigAdd.cosFull A).approx n * (TrigAdd.cosFull A).approx n :=
      Q'.add_le_self_of_nonneg _ _ hcc
    have h2 : ((TrigAdd.sinFull A).approx n * (TrigAdd.sinFull A).approx n
          + (TrigAdd.cosFull A).approx n * (TrigAdd.cosFull A).approx n)
        ≈ ((TrigAdd.cosFull A).approx n * (TrigAdd.cosFull A).approx n
          + (TrigAdd.sinFull A).approx n * (TrigAdd.sinFull A).approx n) :=
      Q'.add_comm_eqv _ _
    exact Q'.le_trans' _ _ _ (Q'.le_trans' _ _ _ h1 (Q'.le_of_eqv h2)) hpe
  have h1B : (1 : Q') ≤ 1 + ε := Q'.add_le_self_of_nonneg 1 ε (Q'.le_of_lt hε)
  exact abs_le_of_mul_self_le h1B hss

/-- **Lemma B (cosine).**  `|cosFull x| ≤ 1` for EVERY signed rational `x`, extending
the nonneg core by evenness `cosFull_even`. -/
theorem abs_cosFull_leRat_one (x : Q') :
    CReal.leRat (CReal.abs (TrigAdd.cosFull x)) 1 := by
  by_cases hx : (0 : Q') ≤ x
  · exact abs_cosFull_leRat_one_nonneg hx
  · have hx' : (0 : Q') ≤ -x := Q'.nonneg_neg_of_nonpos (TrigSignedAddFull.le_of_not_le hx)
    -- Equiv (abs (cosFull x)) (abs (cosFull (-x)))  via evenness
    have he : CReal.Equiv (CReal.abs (TrigAdd.cosFull x)) (CReal.abs (TrigAdd.cosFull (-x))) :=
      (CReal.abs_equiv_congr (TrigAdd.cosFull_even x)).symm
    exact CReal.leRat_of_equiv he (abs_cosFull_leRat_one_nonneg hx')

/-- **Lemma B (sine).**  `|sinFull x| ≤ 1` for EVERY signed rational `x`, extending
the nonneg core by oddness `sinFull_neg`. -/
theorem abs_sinFull_leRat_one (x : Q') :
    CReal.leRat (CReal.abs (TrigAdd.sinFull x)) 1 := by
  by_cases hx : (0 : Q') ≤ x
  · exact abs_sinFull_leRat_one_nonneg hx
  · have hx' : (0 : Q') ≤ -x := Q'.nonneg_neg_of_nonpos (TrigSignedAddFull.le_of_not_le hx)
    -- Equiv (abs (sinFull (-x))) (abs (sinFull x)) via sinFull_neg + abs_neg
    have e1 : CReal.Equiv (CReal.abs (TrigAdd.sinFull (-x)))
        (CReal.abs (CReal.neg (TrigAdd.sinFull x))) :=
      CReal.abs_equiv_congr (TrigSignedAdd.sinFull_neg x)
    have e2 : CReal.Equiv (CReal.abs (CReal.neg (TrigAdd.sinFull x)))
        (CReal.abs (TrigAdd.sinFull x)) := absneg_equiv (TrigAdd.sinFull x)
    have he : CReal.Equiv (CReal.abs (TrigAdd.sinFull x))
        (CReal.abs (TrigAdd.sinFull (-x))) := (e1.trans e2).symm
    exact CReal.leRat_of_equiv he (abs_sinFull_leRat_one_nonneg hx')

/-! ## 3. The `K = (32/3)·q^{2k+1}` coefficient and its positivity (L4) -/

/-- The scalar factor `16/3` (the `4h² + (8/3)|h|³ ≤ (16/3)h²` fold constant). -/
def kFactor : Q' := Q'.mkPos 16 3 (by decide)

theorem kFactor_pos : (0 : Q') < kFactor := by
  refine CReal.pos_of_num_pos ?_
  show (0 : Int) < (Q'.mkPos 16 3 (by decide)).num
  rw [Q'.mkPos_num]; decide

/-- The per-factor quadratic coefficient `K_k = (amp+amp)·(16/3) = (32/3)·q^{2k+1}`. -/
def Kconst (q : Q') (k : Nat) : Q' := (amp q k + amp q k) * kFactor

theorem Kconst_pos {q : Q'} (hq : (0 : Q') < q) (k : Nat) : (0 : Q') < Kconst q k :=
  Q'.mul_pos (Q'.add_pos (ampPos hq k) (ampPos hq k)) kFactor_pos

theorem Kconst_num_pos {q : Q'} (hq : (0 : Q') < q) (k : Nat) : 0 < (Kconst q k).num :=
  Q'.num_pos_of_pos (Kconst_pos hq k)

/-! ## 4. The honest residual and the wiring to the target -/

/-- **The pure trig second-difference quadratic residual (steps 0 + 4).**  The
`CReal.leRat` quadratic bound `|fdRemC (Fk) (dk) θ h| ≤ K·(|h|·|h|)` on `|h| ≤ ½`
with the explicit `K = Kconst q k`.  Everything its proof consumes — the all-sign
addition law (`cosFull_add_signed`) and the arbitrary-argument amplitude bounds
(`abs_cosFull_leRat_one` / `abs_sinFull_leRat_one`) — is proved above; the residual
is exactly the `(amp+amp)·Rc` reduction plus the triangle+product magnitude bound. -/
structure RcQuadResidual (q : Q') (k : Nat) (θ : Q') : Type where
  /-- The quadratic bound on `|h| ≤ ½` with coefficient `Kconst q k`. -/
  bound : ∀ h : Q', (0 : Q') < Q'.abs h → Q'.abs h ≤ HalfPow.half →
    CReal.leRat (CReal.abs (fdRemC (Fk q k) (dk q k θ) θ h))
      (Kconst q k * (Q'.abs h * Q'.abs h))

/-- **From the `Rc` residual to `JacobiQuadResidual`** with the explicit `K` and the
proved positivity `Knum` (the L4 discharge). -/
def jacobiQuadResidual_of_rc {q : Q'} (hq : (0 : Q') < q) (k : Nat) (θ : Q')
    (H : RcQuadResidual q k θ) :
    JacobiFactorFDDeriv.JacobiQuadResidual q k θ where
  K := Kconst q k
  Knum := Kconst_num_pos hq k
  bound := H.bound

/-- **The per-factor `FDDerivDataC`, closed from the `Rc` residual.**  Feeds the
`Rc` residual (with `K`, `Knum` discharged here) into the already-proved
`jacobiFactorFDDeriv` modulus assembly. -/
def jacobiFactorFDDeriv_of_rc {q : Q'} (hq : (0 : Q') < q) (k : Nat) (θ : Q')
    (H : RcQuadResidual q k θ) :
    FDDerivDataC (Fk q k) (dk q k θ) θ :=
  JacobiFactorFDDeriv.jacobiFactorFDDeriv k θ (jacobiQuadResidual_of_rc hq k θ H)

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms powPos
#print axioms abs_le_of_mul_self_le
#print axioms cosFull_add_signed
#print axioms abs_cosFull_leRat_one
#print axioms abs_sinFull_leRat_one
#print axioms Kconst_num_pos
#print axioms jacobiQuadResidual_of_rc
#print axioms jacobiFactorFDDeriv_of_rc

end YMGap.Continuum.JacobiQuadResidualClose
