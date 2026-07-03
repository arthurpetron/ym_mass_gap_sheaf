/-
# Closing the series-side `unif` field of the theta `C¹` inputs

`ThetaSeriesFDDeriv.thetaSeriesFDDeriv` reduces the series-side finite-difference
derivative `Dser` ENTIRELY to constructing the residual data fields of a
`ThetaSeriesFDDeriv.C1InputsC (chebTTrunc a) (dPartialFam a) F (dSeriesCReal …) x`.
Of those fields exactly ONE is fully `F`-independent and closable constructively:
the uniform derivative-convergence field

    `unif : UnifDerivConvC (dPartialFam a) (dSeriesCReal …) x`.

This module CLOSES that field genuinely, `[propext]`/`[propext, Quot.sound]`-clean.

## What is genuinely proved here

* **`geoTailBase_le_of_cutoff_gen`** — the base-general cutoff: for `0 < C`,
  `0 < r < 1`, `0 < ε`, `geoTailBase C r M ≤ ε` once `M` clears the
  `powBaseCutoff r (ε/(C·H))` threshold (`H = 1/(1−r)`).  A parametric
  generalisation of `ThetaUnifDerivModulus.geoTailBase_le_of_cutoff` off its
  hard-wired base `q·q` / constant `CmajTail q`.

* **`Cmaj_pos`** — the geometric-majorant constant `Cmaj a > 0`.

* **`dPartial_step_up` / `dPartial_step_lo`** — the two single-step increment
  bounds `|dPartial(l+1) − dPartial(l)| ≤ Cmaj·aˡ` (the anonymous `hup`/`hlo`
  lambdas of `dSeriesCReal`, extracted as named lemmas).

* **`dSeries_self_conv`** (Lemma A) — the self-convergence at the geometric tail:
  `|dSeriesCReal ⊖ ofQ'(dPartial M)| ≤ geoTailBase (Cmaj a) a M`, via
  `leRat_of_eventually` at threshold `M`, the two telescoped tail bounds, and
  `CReal.abs_sub_le_of_bounds`.

* **`seriesUnif`** — THE closed `unif` field: `UnifDerivConvC (dPartialFam a)
  (dSeriesCReal …) x`, modulus `Mg ε = powBaseCutoff a (ε/(Cmaj a·H))`.

## The honest residual (AGENTS.md Rule 6)

The two undifferentiated pointwise theta limits `ptθ`/`ptθh` and the finite
Chebyshev-`T` second-difference remainder `fdbound` are the genuine remaining
series-side inputs; they are `F`-entangled (they need the common `F = ϑ₃`) and are
NOT closed here.  They are packaged as the named `Type`-level residual
`ThetaSeriesResidual`, and `thetaSeriesFDDeriv_of_residual` assembles the full
`Dser` from `seriesUnif` (proved) + `ThetaSeriesResidual` (the residual), a sharp
honest reduction of the whole series-side derivative to those `F`-entangled fields.

## Axiom gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `native_decide`,
no `sorry`.
-/

import YMGap.Continuum.ThetaSeriesFDDeriv
import YMGap.Continuum.JTPIdentity
import YMGap.Continuum.HeatKernelConvGen
import YMGap.Continuum.KPLimit
import YMGap.Constructive.CRealLe
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealAdd
import YMGap.Constructive.CRealExp
import YMGap.Constructive.Reals

namespace YMGap.Continuum.ThetaSeriesFieldsClose

open YMGap.Constructive
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The base-general geometric-tail cutoff (Lemma B) -/

/-- **The base-general derivative-tail cutoff.**  For `0 < C`, `0 < r < 1`,
`0 < ε`, the telescoped geometric tail satisfies `geoTailBase C r M ≤ ε` for ALL
`M ≥ powBaseCutoff r (ε/(C·H))`, `H = 1/(1−r)`.  A parametric copy of
`ThetaUnifDerivModulus.geoTailBase_le_of_cutoff` off its fixed base/constant. -/
theorem geoTailBase_le_of_cutoff_gen {C r : Q'} (hCpos : (0 : Q') < C)
    (hr0 : (0 : Q') < r) (hr1 : r < (1 : Q'))
    {ε : Q'} (hε : (0 : Q') < ε) (M : Nat)
    (hM : HKConvGen.powBaseCutoff r
      (HKConv.divPos ε (C * HKConv.divPos 1 (1 + (-r)))) ≤ M) :
    HKConvGen.geoTailBase C r M ≤ ε := by
  have hHpos : (0 : Q') < HKConv.divPos 1 (1 + (-r)) :=
    HKConv.divPos_pos (by decide : (0 : Int) < (1 : Q').num)
  have hKpos : (0 : Q') < C * HKConv.divPos 1 (1 + (-r)) := HKPos.q_mul_pos hCpos hHpos
  have hKnum : 0 < (C * HKConv.divPos 1 (1 + (-r))).num := CReal.num_pos_of_pos hKpos
  have hδpos : (0 : Q') < HKConv.divPos ε (C * HKConv.divPos 1 (1 + (-r))) :=
    HKConv.divPos_pos (CReal.num_pos_of_pos hε)
  -- K · (ε/K) ≈ ε
  have hCδ : ((C * HKConv.divPos 1 (1 + (-r)))
      * HKConv.divPos ε (C * HKConv.divPos 1 (1 + (-r)))) ≈ ε := by
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv (C * HKConv.divPos 1 (1 + (-r)))
        (HKConv.divPos ε (C * HKConv.divPos 1 (1 + (-r))))) ?_
    exact HKConv.divPos_mul_eqv hKnum
  -- r^M ≤ ε/K
  have hpow : r ^ M ≤ HKConv.divPos ε (C * HKConv.divPos 1 (1 + (-r))) := by
    refine Q'.le_trans' _ _ _
      (HKConvGen.pow_base_antitone (Q'.le_of_lt hr0) (Q'.le_of_lt hr1) hM) ?_
    exact HKConvGen.pow_base_le_cutoff hr0 hr1 hδpos
  -- geoTailBase C r M ≈ K · r^M
  have he : (HKConvGen.geoTailBase C r M)
      ≈ ((C * HKConv.divPos 1 (1 + (-r))) * r ^ M) := by
    show ((C * r ^ M) * HKConv.divPos 1 (1 + (-r)))
        ≈ ((C * HKConv.divPos 1 (1 + (-r))) * r ^ M)
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv C (r ^ M) (HKConv.divPos 1 (1 + (-r)))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left C _ _
        (Q'.mul_comm_eqv (r ^ M) (HKConv.divPos 1 (1 + (-r))))) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv C (HKConv.divPos 1 (1 + (-r))) (r ^ M))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv he) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left (r ^ M)
      (HKConv.divPos ε (C * HKConv.divPos 1 (1 + (-r))))
      (C * HKConv.divPos 1 (1 + (-r))) hpow (Q'.le_of_lt hKpos)) ?_
  exact Q'.le_of_eqv hCδ

/-! ## 2. `Cmaj a > 0` and the two single-step increment bounds -/

/-- The geometric-majorant constant `Cmaj a > 0` (all factors positive). -/
theorem Cmaj_pos {a : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q')) :
    (0 : Q') < JTPIdentity.Cmaj a := by
  have hHH : (0 : Q') <
      HKConv.divPos 1 (JTPIdentity.gA a) * HKConv.divPos 1 (JTPIdentity.gA a) :=
    HKPos.q_mul_pos (JTPIdentity.invG_pos ha1) (JTPIdentity.invG_pos ha1)
  have hInvaa : (0 : Q') < HKConv.divPos 1 (a * a) :=
    HKConv.divPos_pos (by decide : (0 : Int) < (1 : Q').num)
  exact HKPos.q_mul_pos (HKPos.q_mul_pos ha0 hHH) hInvaa

/-- **Upper single-step increment** `dPartial(l+1) ≤ dPartial(l) + Cmaj·aˡ`. -/
theorem dPartial_step_up {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (l : Nat) :
    JTPIdentity.dPartial a x (l + 1)
      ≤ JTPIdentity.dPartial a x l + HKConvGen.geoIncrBase (JTPIdentity.Cmaj a) a l := by
  rw [JTPIdentity.dPartial_succ]
  exact Q'.add_le_add_left (JTPIdentity.dPartial a x l) (JTPIdentity.dTerm a x l)
    (HKConvGen.geoIncrBase (JTPIdentity.Cmaj a) a l)
    (JTPIdentity.dTerm_le ha0 ha1 hx hx1 l)

/-- **Lower single-step increment** `dPartial(l) ≤ dPartial(l+1) + Cmaj·aˡ`. -/
theorem dPartial_step_lo {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (l : Nat) :
    JTPIdentity.dPartial a x l
      ≤ JTPIdentity.dPartial a x (l + 1) + HKConvGen.geoIncrBase (JTPIdentity.Cmaj a) a l := by
  rw [JTPIdentity.dPartial_succ]
  refine Q'.le_trans' _ _ _ ?_
    (Q'.le_of_eqv (Q'.eqv_symm
      (Q'.add_assoc_eqv (JTPIdentity.dPartial a x l) (JTPIdentity.dTerm a x l)
        (HKConvGen.geoIncrBase (JTPIdentity.Cmaj a) a l))))
  refine Q'.add_le_self_of_nonneg (JTPIdentity.dPartial a x l)
    (JTPIdentity.dTerm a x l + HKConvGen.geoIncrBase (JTPIdentity.Cmaj a) a l) ?_
  have hlo := JTPIdentity.neg_dTerm_le ha0 ha1 hx hx1 l
  have hlo' : -(JTPIdentity.Cmaj a * a ^ l) ≤ JTPIdentity.dTerm a x l := by
    have h1 : -(JTPIdentity.dTerm a x l) ≤ JTPIdentity.Cmaj a * a ^ l := hlo
    have h2 := Q'.neg_le_neg h1
    refine Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv (Q'.neg_neg_eqv (JTPIdentity.dTerm a x l)))
  have h3 : -(JTPIdentity.Cmaj a * a ^ l) + JTPIdentity.Cmaj a * a ^ l
      ≤ JTPIdentity.dTerm a x l + HKConvGen.geoIncrBase (JTPIdentity.Cmaj a) a l :=
    Q'.add_le_add_right _ _ (JTPIdentity.Cmaj a * a ^ l) hlo'
  refine Q'.le_trans' _ _ _ ?_ h3
  exact Q'.ge_of_eqv (Q'.neg_add_self_eqv (JTPIdentity.Cmaj a * a ^ l))

/-! ## 3. Lemma A — self-convergence of `dSeriesCReal` at the geometric tail -/

/-- **Lemma A.**  The `K_t`-side series `CReal` is within its own geometric tail of
each partial sum: `|dSeriesCReal ⊖ ofQ'(dPartial M)| ≤ geoTailBase (Cmaj a) a M`.
`leRat_of_eventually` at threshold `M`; at `n = M+d` the CReal difference unfolds
(defeq) to `|dPartial(M+d) − dPartial(M)|`, bounded by `abs_sub_le_of_bounds` fed
by the two telescoped tail bounds. -/
theorem dSeries_self_conv {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) (M : Nat) :
    CReal.leRat
      (CReal.abs (CReal.add (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1)
        (CReal.neg (CReal.ofQ' (JTPIdentity.dPartial a x M)))))
      (HKConvGen.geoTailBase (JTPIdentity.Cmaj a) a M) := by
  apply CReal.leRat_of_eventually
  refine ⟨M, fun n hn => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  show Q'.abs (JTPIdentity.dPartial a x (M + d) + -(JTPIdentity.dPartial a x M))
      ≤ HKConvGen.geoTailBase (JTPIdentity.Cmaj a) a M
  refine CReal.abs_sub_le_of_bounds ?_ ?_
  · -- dPartial (M+d) ≤ dPartial M + geoTailBase
    refine Q'.le_trans' _ _ _
      (telescope_up (JTPIdentity.dPartial a x)
        (HKConvGen.geoIncrBase (JTPIdentity.Cmaj a) a)
        (dPartial_step_up ha0 ha1 hx hx1) M d) ?_
    exact Q'.add_le_add_left (JTPIdentity.dPartial a x M) _
      (HKConvGen.geoTailBase (JTPIdentity.Cmaj a) a M)
      (HKConvGen.geoTailBase_series_le (JTPIdentity.Cmaj_nonneg ha0 ha1) ha0 ha1 M d)
  · -- dPartial M ≤ dPartial (M+d) + geoTailBase
    refine Q'.le_trans' _ _ _
      (telescope_lo (JTPIdentity.dPartial a x)
        (HKConvGen.geoIncrBase (JTPIdentity.Cmaj a) a)
        (dPartial_step_lo ha0 ha1 hx hx1) M d) ?_
    exact Q'.add_le_add_left (JTPIdentity.dPartial a x (M + d)) _
      (HKConvGen.geoTailBase (JTPIdentity.Cmaj a) a M)
      (HKConvGen.geoTailBase_series_le (JTPIdentity.Cmaj_nonneg ha0 ha1) ha0 ha1 M d)

/-! ## 4. THE CLOSED `unif` FIELD -/

/-- **THE CLOSED `unif` FIELD.**  The uniform derivative-convergence data
`UnifDerivConvC (dPartialFam a) (dSeriesCReal …) x`, with the explicit base-`a`
modulus `Mg ε = powBaseCutoff a (ε/(Cmaj a·H))`.  `conv` = Lemma A monotone-lifted
through the base-general cutoff `geoTailBase_le_of_cutoff_gen`. -/
def seriesUnif {a x : Q'} (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    ThetaSeriesFDDeriv.UnifDerivConvC (ThetaSeriesFDDeriv.dPartialFam a)
      (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) x where
  Mg := fun ε => HKConvGen.powBaseCutoff a
    (HKConv.divPos ε (JTPIdentity.Cmaj a * HKConv.divPos 1 (1 + (-a))))
  conv := fun ε hε M hM =>
    CReal.leRat_mono (dSeries_self_conv ha0 ha1 hx hx1 M)
      (geoTailBase_le_of_cutoff_gen (Cmaj_pos ha0 ha1) ha0 ha1 hε M hM)

/-! ## 5. The honest residual and the assembled series-side derivative -/

/-- **The named `Type`-level residual**: the `F`-entangled / analytic fields of the
theta `C¹` inputs NOT closed here — the two undifferentiated pointwise theta limits
`ptθ`/`ptθh` (needing the common `F = ϑ₃`) and the finite Chebyshev-`T`
second-difference remainder `fdbound`. -/
structure ThetaSeriesResidual {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal) : Type where
  /-- Pointwise convergence of the Chebyshev truncations to `F` at `x`. -/
  ptθ : ThetaSeriesFDDeriv.PtwiseConvC (ThetaSeriesFDDeriv.chebTTrunc a) F x
  /-- Pointwise convergence of the Chebyshev truncations to `F` at every `x+h`. -/
  ptθh : ∀ h : Q', ThetaSeriesFDDeriv.PtwiseConvC (ThetaSeriesFDDeriv.chebTTrunc a) F (x + h)
  /-- The common finite-difference modulus. -/
  delStar : Q' → Q'
  /-- `delStar` is positive for positive tolerance. -/
  delStar_pos : ∀ ε : Q', (0 : Q') < ε → (0 : Q') < delStar ε
  /-- The stage past which the common modulus is valid. -/
  mStar : Q' → Nat
  /-- The cleared finite-difference bound for the Chebyshev truncations. -/
  fdbound : ∀ ε' : Q', (0 : Q') < ε' → ∀ M : Nat, mStar ε' ≤ M →
    ∀ h : Q', (0 : Q') < Q'.abs h → Q'.abs h ≤ delStar ε' →
      Q'.abs (TsumDeriv.fdRem (ThetaSeriesFDDeriv.chebTTrunc a M)
        (ThetaSeriesFDDeriv.dPartialFam a M x) x h) ≤ ε' * Q'.abs h

/-- **Assemble the theta `C¹` inputs** from the proved `seriesUnif` and the named
residual: the sole open fields are the `F`-entangled `ptθ`/`ptθh` and the analytic
`fdbound`, all carried by `ThetaSeriesResidual`. -/
def thetaSeriesC1Inputs_of_residual {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal) (res : ThetaSeriesResidual ha0 ha1 hx hx1 F) :
    ThetaSeriesFDDeriv.ThetaSeriesC1Inputs ha0 ha1 hx hx1 F :=
  { ptθ := res.ptθ
    ptθh := res.ptθh
    unif := seriesUnif ha0 ha1 hx hx1
    delStar := res.delStar
    delStar_pos := res.delStar_pos
    mStar := res.mStar
    fdbound := res.fdbound }

/-- **THE ASSEMBLED SERIES-SIDE DERIVATIVE (reduced to the residual).**  From the
`F`-entangled residual, the `K_t`-side series `dSeriesCReal` is a CReal-valued
finite-difference derivative of `F` at `x` — the `Dser` field of
`C1UniqInputsCRealDeriv`, with the `unif` field genuinely discharged here. -/
def thetaSeriesFDDeriv_of_residual {a x : Q'}
    (ha0 : (0 : Q') < a) (ha1 : a < (1 : Q'))
    (hx : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q'))
    (F : Q' → CReal) (res : ThetaSeriesResidual ha0 ha1 hx hx1 F) :
    TsumDeriv.FDDerivDataC F (JTPIdentity.dSeriesCReal ha0 ha1 hx hx1) x :=
  ThetaSeriesFDDeriv.thetaSeriesFDDeriv ha0 ha1 hx hx1 F
    (thetaSeriesC1Inputs_of_residual ha0 ha1 hx hx1 F res)

end YMGap.Continuum.ThetaSeriesFieldsClose

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ThetaSeriesFieldsClose.geoTailBase_le_of_cutoff_gen
#print axioms YMGap.Continuum.ThetaSeriesFieldsClose.Cmaj_pos
#print axioms YMGap.Continuum.ThetaSeriesFieldsClose.dPartial_step_up
#print axioms YMGap.Continuum.ThetaSeriesFieldsClose.dPartial_step_lo
#print axioms YMGap.Continuum.ThetaSeriesFieldsClose.dSeries_self_conv
#print axioms YMGap.Continuum.ThetaSeriesFieldsClose.seriesUnif
#print axioms YMGap.Continuum.ThetaSeriesFieldsClose.thetaSeriesC1Inputs_of_residual
#print axioms YMGap.Continuum.ThetaSeriesFieldsClose.thetaSeriesFDDeriv_of_residual
