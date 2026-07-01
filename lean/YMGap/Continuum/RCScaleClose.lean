/-
Closing the `RCScaleResidualPlus` residual: the `RC`-by-`Q'` scaling
`RCscale s = ofQ' s · (·)`, its monotonicity for nonnegative scalars, and the
scale-over-finite-sum law `s · Σ fᵢ = Σ s · fᵢ`.

# Which residual this closes (GENUINE, discharged)

`Continuum/SelfAdjointHamiltonian.lean` recorded `RCScaleResidual` (the `RC`
scaling with monotonicity) and `Continuum/HamiltonianScalar.lean` strengthened
it to `RCScaleResidualPlus` (adding `RCscale_finSum`).  Both were left as named
`Type`-level data awaiting an analytic (division) Cauchy modulus.  In fact NO
division is needed: `RCscale s := ofQ' s · (·)` is the honest scalar action,

  * **well-defined** on the quotient `RC = CReal/Equiv` by the *sign-free*
    right-congruence `Pivot2.mul_congr_right` (works for negative `s` too);
  * **monotone** for `0 ≤ s` by the pointwise `mul_le_mul_of_nonneg_left`
    estimate `leEv_smul_nonneg` (a near-verbatim clone of `leRat_smul_nonneg`);
  * **additive** (`RCscale_RCadd`) and **zero-preserving** (`RCscale_RCzero`)
    by the pointwise `Q'` distributivity `mul_add_eqv` / `mul_zero_eqv` through
    `Equiv_of_approx_eqv`, which by induction gives the finite-sum law
    `RCscale_finSum`.

`rcScaleResidualPlus` bundles these into an inhabitant of `RCScaleResidualPlus`.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.HamiltonianScalar
import YMGap.Continuum.Pivot2Moments
import YMGap.Constructive.SumOfSquares
import YMGap.Constructive.CRealLog
import YMGap.Constructive.CRealMul
import YMGap.Constructive.RationalsMul

open YMGap.Constructive

namespace YMGap.Constructive.CReal

/-! ## The `RC`-by-`Q'` scaling and its structural laws -/

/-- **The `Q'`-scaling of a real.**  `RCscale s ⟦A⟧ = ⟦ofQ' s · A⟧`.  Well-defined
on `RC = CReal/Equiv` by the sign-free right-congruence `mul_congr_right` (so it
is valid for negative `s` as well). -/
def RCscale (s : Q') : RC → RC :=
  Quotient.lift (fun A => Quotient.mk crealSetoid (mul (ofQ' s) A))
    (fun _ _ h => Quotient.sound (YMGap.Continuum.Pivot2.mul_congr_right h))

@[simp] theorem RCscale_mk (s : Q') (A : CReal) :
    RCscale s (Quotient.mk crealSetoid A) = Quotient.mk crealSetoid (mul (ofQ' s) A) := rfl

/-- **Pointwise nonnegative-scalar monotonicity of `leEv`.**  For `0 ≤ s`,
`leEv A B → leEv (s·A) (s·B)`.  Clone of `leRat_smul_nonneg`:
`s·Aₙ ≤ s·(Bₙ+δ) ≃ s·Bₙ + s·δ ≤ s·Bₙ + ε`. -/
theorem leEv_smul_nonneg {s : Q'} (hs : (0 : Q') ≤ s) {A B : CReal}
    (h : leEv A B) : leEv (mul (ofQ' s) A) (mul (ofQ' s) B) := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := exists_mul_le hs hε
  obtain ⟨N, hN⟩ := h δ hδpos
  refine ⟨N, fun n hn => ?_⟩
  have hAB : A.approx n ≤ B.approx n + δ := hN n hn
  -- `(mul (ofQ' s) A).approx n = s * A.approx n` definitionally.
  show s * A.approx n ≤ s * B.approx n + ε
  have s1 : s * A.approx n ≤ s * (B.approx n + δ) :=
    Q'.mul_le_mul_of_nonneg_left (A.approx n) (B.approx n + δ) s hAB hs
  have e1 : (s * (B.approx n + δ)).eqv (s * B.approx n + s * δ) :=
    Q'.mul_add_eqv s (B.approx n) δ
  have s2 : s * B.approx n + s * δ ≤ s * B.approx n + ε :=
    Q'.add_le_add_left (s * B.approx n) (s * δ) ε hδ
  exact Q'.le_trans' _ _ _ s1 (Q'.le_trans' _ _ _ (Q'.le_of_eqv e1) s2)

/-- **`RCscale` is monotone for `0 ≤ s`.**  Descends `leEv_smul_nonneg` through
the quotient. -/
theorem RCscale_mono {s : Q'} (hs : (0 : Q') ≤ s) {a b : RC} (hab : RCle a b) :
    RCle (RCscale s a) (RCscale s b) := by
  revert hab
  refine Quotient.inductionOn₂ a b ?_
  intro x y hab
  exact leEv_smul_nonneg hs hab

/-- **`RCscale` distributes over `RCadd`.**  `s·(a+b) = s·a + s·b`, pointwise
`Q'` left-distributivity through `Equiv_of_approx_eqv`. -/
theorem RCscale_RCadd (s : Q') (a b : RC) :
    RCscale s (RCadd a b) = RCadd (RCscale s a) (RCscale s b) := by
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  show Quotient.mk crealSetoid (mul (ofQ' s) (add x y))
      = Quotient.mk crealSetoid (add (mul (ofQ' s) x) (mul (ofQ' s) y))
  exact Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.mul_add_eqv s (x.approx n) (y.approx n)))

/-- **`RCscale` preserves zero.**  `s·0 = 0`, pointwise `q·0 ≃ 0`. -/
theorem RCscale_RCzero (s : Q') : RCscale s RCzero = RCzero := by
  show Quotient.mk crealSetoid (mul (ofQ' s) czero) = Quotient.mk crealSetoid czero
  exact Quotient.sound
    (SumOfSquares.Equiv_of_approx_eqv (fun n => CRealLog.mul_zero_eqv s))

/-- **`RCscale` pulls out of a finite `RCfinSum`.**  `s·Σ fᵢ = Σ s·fᵢ`, by
induction on the length using `RCscale_RCadd` (step) and `RCscale_RCzero`
(base). -/
theorem RCscale_finSum (s : Q') :
    {k : Nat} → (f : Fin k → RC) →
      RCscale s (RCfinSum k f) = RCfinSum k (fun i => RCscale s (f i))
  | 0, _ => RCscale_RCzero s
  | (k + 1), f => by
      show RCscale s (RCadd (RCfinSum k (fun i => f i.castSucc)) (f (Fin.last k)))
          = RCadd (RCfinSum k (fun i => RCscale s (f i.castSucc)))
              (RCscale s (f (Fin.last k)))
      rw [RCscale_RCadd, RCscale_finSum s (fun i => f i.castSucc)]

end YMGap.Constructive.CReal

/-! ## The inhabitant of `RCScaleResidualPlus` -/

namespace YMGap.Continuum.RCScaleClose

open YMGap.Constructive

/-- **`RCScaleResidualPlus` is inhabited.**  The concrete scalar action
`RCscale s = ofQ' s · (·)` discharges every field: the `RCScaleResidual` base
(`RCscale` + nonnegative-scalar monotonicity) and the scale-over-sum law
`RCscale_finSum`. -/
def rcScaleResidualPlus : YMGap.Continuum.HamiltonianScalar.RCScaleResidualPlus where
  toRCScaleResidual :=
    { RCscale := CReal.RCscale
      RCscale_mono := fun {s} hs {a b} hab => CReal.RCscale_mono hs hab }
  RCscale_finSum := fun s {k} f => CReal.RCscale_finSum s f

end YMGap.Continuum.RCScaleClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.CReal.RCscale
#print axioms YMGap.Constructive.CReal.RCscale_mono
#print axioms YMGap.Constructive.CReal.RCscale_finSum
#print axioms YMGap.Continuum.RCScaleClose.rcScaleResidualPlus
