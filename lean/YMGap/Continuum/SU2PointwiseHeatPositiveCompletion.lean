/-
# SU(2) pointwise heat positivity: exact completion bridge and honest fence

For every rational nome `0 < w < 1` and class coordinate `x ∈ [-1,1]`,
`SU2PointwiseHeatSpacingCompletion` constructs the completed character series

    K_w(x) = Σ_{n≥0} (n+1) w^{n(n+2)} U_n(x).

`JTPIdentity` independently constructs

    D_w(x) = Σ_{n≥0} (n+1) w^{(n+1)^2} U_n(x).

This module proves, constructively and without an analytic positivity premise,
the exact relation

    w · K_w(x) ≃ D_w(x).

The finite identity is just `n(n+2)+1 = (n+1)^2`.  At the completed level the
two implementations use different approximation offsets, so the proof compares
the spacing completion with a cofinal shift of the differentiated-JTP
completion and invokes uniqueness of constructive limits.

The existing product positivity in `JTPIdentity` does not by itself prove
`D_w ≥ 0`: that transfer requires the still-open differentiated Jacobi identity

    DiffJTP : D_w ≃ (1/2) · theta₃ · S.

Accordingly, the final theorem below is an honest implication
`DiffJTP → pointwiseHeatCReal ≥ 0`.  No inhabitant of `DiffJTP` is introduced.

## Constructivity

There is no `Classical.*`, `Real`, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.SU2PointwiseHeatSpacingCompletion
import YMGap.Continuum.JTPIdentity
import YMGap.Continuum.CRealContinuumAlg

namespace YMGap.Continuum.SU2PointwiseHeatPositiveCompletion

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2PointwiseHeatSpacingCompletion

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact finite-prefix identification -/

/-- Multiplication by the nome changes the heat exponent
`n(n+2)` into `(n+1)^2`. -/
theorem nome_mul_pointwiseHeatTerm_eqv_dTerm
    (w x : Q') (n : Nat) :
    w * pointwiseHeatTerm w x n ≈
      JTPIdentity.dTerm w x n := by
  have hexponent :
      c4 n + 1 = (n + 1) * (n + 1) := by
    have e1 :
        (n + 1) * (n + 1) =
          n * n + (2 * n + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      omega
    have e2 :
        c4 n = n * n + 2 * n := by
      unfold c4
      rw [Nat.mul_add]
      omega
    rw [e1, e2]
    omega
  have hpower :
      qpow w (c4 n) * w ≈
        w ^ ((n + 1) * (n + 1)) := by
    rw [← hexponent]
    exact qpow_eqv_pow w (c4 n + 1)
  have hcoefficient :
      w * coeffW w n ≈
        Q'.ofNat (n + 1) *
          w ^ ((n + 1) * (n + 1)) := by
    unfold coeffW dimQ
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv
        w
        (Q'.ofNat (n + 1) * qpow w (c4 n))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv
        (Q'.ofNat (n + 1))
        (qpow w (c4 n)) w) ?_
    exact Q'.mul_eqv_congr_left
      (Q'.ofNat (n + 1)) _ _ hpower
  unfold pointwiseHeatTerm JTPIdentity.dTerm
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        w (coeffW w n) (Cheb.U n x))) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    hcoefficient

/-- Every ordinary finite character prefix, after multiplication by `w`,
is exactly the corresponding differentiated-JTP prefix. -/
theorem nome_mul_standardPointwiseHeatPartial_eqv_dPartial
    (w x : Q') :
    ∀ N : Nat,
      w * standardPointwiseHeatPartial w x N ≈
        JTPIdentity.dPartial w x N
  | 0 => Q'.mul_zero_eqv w
  | N + 1 => by
      unfold standardPointwiseHeatPartial JTPIdentity.dPartial
      change
        w *
            (finSum (pointwiseHeatTerm w x) N +
              pointwiseHeatTerm w x N) ≈
          finSum (JTPIdentity.dTerm w x) N +
            JTPIdentity.dTerm w x N
      refine Q'.eqv_trans _ _ _
        (Q'.mul_add_eqv
          w
          (finSum (pointwiseHeatTerm w x) N)
          (pointwiseHeatTerm w x N)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_right _ _ _
          (nome_mul_standardPointwiseHeatPartial_eqv_dPartial
            w x N)) ?_
      exact Q'.add_eqv_congr_left _ _ _
        (nome_mul_pointwiseHeatTerm_eqv_dTerm w x N)

/-- The raw spacing-dependent prefix therefore agrees with a cofinal
`dPartial` prefix at the same absolute label cutoff. -/
theorem nome_mul_spacingPointwiseHeatPartial_eqv_dPartial
    (w x : Q') (M : Nat) :
    w * spacingPointwiseHeatPartial w x M ≈
      JTPIdentity.dPartial
        w x (spacingLabelCutoff w + M) := by
  unfold spacingPointwiseHeatPartial
  exact
    nome_mul_standardPointwiseHeatPartial_eqv_dPartial
      w x (spacingLabelCutoff w + M)

/-! ## 2. Completion-level identification -/

/-- The completed pointwise heat kernel multiplied by its nome. -/
def nomeScaledPointwiseHeatCReal
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CReal :=
  CReal.mul
    (CReal.ofQ' w)
    (pointwiseHeatCReal hw0 hw1 hxLower hxUpper)

@[simp] theorem nomeScaledPointwiseHeatCReal_approx
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (M : Nat) :
    (nomeScaledPointwiseHeatCReal
      hw0 hw1 hxLower hxUpper).approx M =
        w * spacingPointwiseHeatPartial w x M := rfl

private theorem convergesTo_add_shift
    {sequence : Nat → CReal} {limit : CReal}
    (h : CReal.ConvergesTo sequence limit)
    (shift : Nat) :
    CReal.ConvergesTo
      (fun N => sequence (shift + N)) limit := by
  intro ε hε
  obtain ⟨stage, hstage⟩ := h ε hε
  refine ⟨stage, fun N hN => ?_⟩
  exact hstage (shift + N) (by omega)

private theorem equiv_ofQ'_of_eqv
    {a b : Q'} (h : a ≈ b) :
    CReal.Equiv (CReal.ofQ' a) (CReal.ofQ' b) :=
  SumOfSquares.Equiv_of_approx_eqv
    (fun _ => h)

/-- The independently completed objects satisfy the exact relation
`w · K_w(x) ≃ D_w(x)` for every rational `0 < w < 1`. -/
theorem nomeScaledPointwiseHeatCReal_equiv_dSeriesCReal
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CReal.Equiv
      (nomeScaledPointwiseHeatCReal
        hw0 hw1 hxLower hxUpper)
      (JTPIdentity.dSeriesCReal
        hw0 hw1 hxLower hxUpper) := by
  exact CReal.Equiv_of_limit_of_equal
    (fun M =>
      equiv_ofQ'_of_eqv
        (nome_mul_spacingPointwiseHeatPartial_eqv_dPartial
          w x M))
    (CReal.convergesTo_self
      (nomeScaledPointwiseHeatCReal
        hw0 hw1 hxLower hxUpper))
    (convergesTo_add_shift
      (CReal.convergesTo_self
        (JTPIdentity.dSeriesCReal
          hw0 hw1 hxLower hxUpper))
      (spacingLabelCutoff w))

/-! ## 3. Positive rational cancellation and the honest positivity fence -/

/-- The explicit positive rational inverse nome used to undo the scaling. -/
def inverseNome (w : Q') : Q' :=
  HKConv.divPos 1 w

/-- The inverse nome is nonnegative. -/
theorem inverseNome_nonnegative (w : Q') :
    (0 : Q') ≤ inverseNome w :=
  HKConv.divPos_nonneg (by decide)

/-- The inverse nome cancels the nome when `w > 0`. -/
theorem inverseNome_mul_nome_eqv
    {w : Q'} (hw0 : (0 : Q') < w) :
    inverseNome w * w ≈ (1 : Q') := by
  exact HKConv.divPos_mul_eqv
    (CReal.num_pos_of_pos hw0)

/-- Solving `w · K_w ≃ D_w` for `K_w` gives
`K_w ≃ w⁻¹ · D_w`, constructively. -/
theorem pointwiseHeatCReal_equiv_inverseNome_mul_dSeriesCReal
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q')) :
    CReal.Equiv
      (pointwiseHeatCReal hw0 hw1 hxLower hxUpper)
      (CReal.mul
        (CReal.ofQ' (inverseNome w))
        (JTPIdentity.dSeriesCReal
          hw0 hw1 hxLower hxUpper)) := by
  let K :=
    pointwiseHeatCReal hw0 hw1 hxLower hxUpper
  let D :=
    JTPIdentity.dSeriesCReal hw0 hw1 hxLower hxUpper
  let R := CReal.ofQ' (inverseNome w)
  let W := CReal.ofQ' w
  have hscaled :
      CReal.Equiv (CReal.mul W K) D :=
    nomeScaledPointwiseHeatCReal_equiv_dSeriesCReal
      hw0 hw1 hxLower hxUpper
  have hrwQ :
      inverseNome w * w ≈ (1 : Q') :=
    inverseNome_mul_nome_eqv hw0
  have hrwC :
      CReal.Equiv (CReal.mul R W) CReal.cone := by
    refine CReal.Equiv.trans
      (CReal.Equiv.symm
        (CRealAlg.ofQ'_mul (inverseNome w) w)) ?_
    exact equiv_ofQ'_of_eqv hrwQ
  have hcollapse :
      CReal.Equiv
        (CReal.mul R (CReal.mul W K)) K := by
    refine CReal.Equiv.trans
      (CReal.Equiv.symm
        (CRealAlg.cmul_assoc R W K)) ?_
    refine CReal.Equiv.trans
      (CRealContinuumAlg.cmul_congr_left hrwC) ?_
    exact CRealAlg.cone_mul K
  refine CReal.Equiv.trans
    (CReal.Equiv.symm hcollapse) ?_
  exact CRealContinuumAlg.cmul_congr_right hscaled

/-- **Honest general-nome positivity fence.**  The existing differentiated
Jacobi identity is exactly the missing analytic input.  Given that input,
product nonnegativity transfers to `dSeriesCReal`, and positive rational
cancellation transfers it to the completed pointwise heat kernel. -/
theorem pointwiseHeatCReal_geRat_zero_of_diffJTP
    {w x : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hxLower : (-(1 : Q')) ≤ x) (hxUpper : x ≤ (1 : Q'))
    (hDiff :
      JTPIdentity.DiffJTP
        hw0 hw1 hxLower hxUpper) :
    ExpPos.geRat
      (pointwiseHeatCReal
        hw0 hw1 hxLower hxUpper) 0 := by
  have hD :
      ExpPos.geRat
        (JTPIdentity.dSeriesCReal
          hw0 hw1 hxLower hxUpper) 0 :=
    JTPIdentity.Kt_geRat_zero_of_diff
      hw0 hw1 hxLower hxUpper hDiff
  have hscaled :
      ExpPos.geRat
        (CReal.mul
          (CReal.ofQ' (inverseNome w))
          (JTPIdentity.dSeriesCReal
            hw0 hw1 hxLower hxUpper))
        (inverseNome w * 0) :=
    SU3CharFactor.geRat_smul_nonneg
      (inverseNome_nonnegative w) hD
  have hscaledZero :
      ExpPos.geRat
        (CReal.mul
          (CReal.ofQ' (inverseNome w))
          (JTPIdentity.dSeriesCReal
            hw0 hw1 hxLower hxUpper))
        0 :=
    ExpPos.geRat_mono hscaled
      (Q'.ge_of_eqv
        (Q'.mul_zero_eqv (inverseNome w)))
  exact SU3CharFactor.geRat_of_equiv
    (pointwiseHeatCReal_equiv_inverseNome_mul_dSeriesCReal
      hw0 hw1 hxLower hxUpper)
    hscaledZero

end YMGap.Continuum.SU2PointwiseHeatPositiveCompletion

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SU2PointwiseHeatPositiveCompletion.nome_mul_pointwiseHeatTerm_eqv_dTerm
#print axioms YMGap.Continuum.SU2PointwiseHeatPositiveCompletion.nome_mul_standardPointwiseHeatPartial_eqv_dPartial
#print axioms YMGap.Continuum.SU2PointwiseHeatPositiveCompletion.nome_mul_spacingPointwiseHeatPartial_eqv_dPartial
#print axioms YMGap.Continuum.SU2PointwiseHeatPositiveCompletion.nomeScaledPointwiseHeatCReal_equiv_dSeriesCReal
#print axioms YMGap.Continuum.SU2PointwiseHeatPositiveCompletion.pointwiseHeatCReal_equiv_inverseNome_mul_dSeriesCReal
#print axioms YMGap.Continuum.SU2PointwiseHeatPositiveCompletion.pointwiseHeatCReal_geRat_zero_of_diffJTP
