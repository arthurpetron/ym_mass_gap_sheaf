/-
The fixed-spacing, finite-volume Wilson GNS reconstruction capstone.

# What this module delivers

Over the excited-tower spectral gap
`G := excitedCharSpectralGapData op w hw0 hw1 N` (with
`G.gap.sep = heatKernelSep w = w³`), the structure `WilsonGNSReconstruction`
carries — SIMULTANEOUSLY, as `Type`-level data (Rule 8) — the five finite-volume
reconstruction deliverables:

  1. the vector-space / scalar structure on the completion (`VectorScalingResidual`,
     PROVED);
  2. the strictly-positive mass gap `Δ = −log sep > 0`, a genuine `CReal`,
     UNCONDITIONAL in `sep` (built from the range-reduction internals of the
     unconditional gap theorem);
  3. the operator-form gap on `vac⊥`, `⟨Tx,x⟩ ≤ sep·⟨x,x⟩`
     (`TransferFormGapResidual`);
  4. the located spectral infimum, attained at `i = 0` (`SpectrumInfResidual`);
  5. the self-adjoint additive Hamiltonian `H` with `e^{−H}=T`
     (`BoundedFunctionalCalculusResidual`).

`wilson_gns_reconstruction_gap` assembles the whole bundle from exactly TWO honest
inputs:

  * **RESIDUAL A** — the diagonal Schur / Peter–Weyl (Osterwalder–Seiler)
    identities `schur_self` / `schur_T`, realized as finite algebraic identities
    inside `cinner` (NOT an integral wall), carried as `Type`-level premises with
    the finite character coordinate map `coord`;
  * **RESIDUAL B** — the `BoundedFunctionalCalculusResidual` datum `H` (the single
    irreducibly-hard node: self-adjoint additive bounded `H` with `e^{−H}=T` via a
    BOUNDED functional-calculus surrogate, never polynomial approximation of the
    unbounded `−log`).

Everything else is discharged by reusing existing proofs verbatim.  In particular
the scalar-order monotonicity of the `RC`-scaling (`Rscalar`, needed only for the
form-gap composition) is DISCHARGED here by the new lemma
`CReal.RCscale_mono_scalar`, so it is NOT an exposed premise.

## Honesty guardrail

This is the self-adjoint-**form** Hamiltonian reconstruction: `H = −log T` is NOT
built as a bounded operator (it is unbounded at `0`).  The deliverable is the
form-gap `Δ = −log sep` together with the `BoundedFunctionalCalculusResidual`
datum.  Scope is **fixed-spacing finite-volume** (`excitedCharSpectralGapData`)
only; there is no physical Wilson `T` construction and no `a → 0` limit.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.HamiltonianAllSep
import YMGap.Continuum.HamiltonianSpectrumInf
import YMGap.Continuum.HamiltonianScalar
import YMGap.Continuum.SelfAdjointHamiltonian
import YMGap.Continuum.RCScaleClose
import YMGap.Continuum.CharacterDiagResolutionProof

open YMGap.Constructive
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ReflectionPositivity
open YMGap.Continuum.WilsonSpectralBridge
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.CharacterDiagResolutionProof
open YMGap.Continuum.HamiltonianAllSep

/-! ## 0a. The scalar-monotonicity of `RCscale` (discharges `Rscalar`) -/

namespace YMGap.Constructive.CReal

/-- **`RCscale` monotone in its SCALAR for a nonnegative argument.**
`s ≤ t`, `RCnonneg c` ⟹ `RCle (RCscale s c) (RCscale t c)`.  Pointwise
`s·aₙ ≤ t·aₙ + ε`: with `aₙ ≥ −δ` (eventual nonnegativity) and `(t−s)·δ ≤ ε`,
the product `(t−s)·(aₙ+δ) ≥ 0` expands to `(t−s)·aₙ + ε ≥ 0`, which rearranges to
the target through the sign-free `Q'` distributivity identities. -/
theorem RCscale_mono_scalar {s t : Q'} (hst : s ≤ t)
    {c : CReal.RC} (hc : CReal.RCnonneg c) :
    CReal.RCle (CReal.RCscale s c) (CReal.RCscale t c) := by
  revert hc
  refine Quotient.inductionOn c ?_
  intro A hc
  have hcA : CReal.leEv CReal.czero A := hc
  show CReal.leEv (CReal.mul (CReal.ofQ' s) A) (CReal.mul (CReal.ofQ' t) A)
  intro ε hε
  have hd : (0 : Q') ≤ t + -s := Q'.sub_nonneg_of_le hst
  obtain ⟨δ, hδpos, hδ⟩ := CReal.exists_mul_le hd hε
  obtain ⟨Nn, hN⟩ := hcA δ hδpos
  refine ⟨Nn, fun n hn => ?_⟩
  show s * A.approx n ≤ t * A.approx n + ε
  have hAδ : (0 : Q') ≤ A.approx n + δ := hN n hn
  have hprod : (0 : Q') ≤ (t + -s) * (A.approx n + δ) :=
    Q'.mul_nonneg (t + -s) (A.approx n + δ) hd hAδ
  have eprod : ((t + -s) * (A.approx n + δ)).eqv
      ((t + -s) * A.approx n + (t + -s) * δ) :=
    Q'.mul_add_eqv (t + -s) (A.approx n) δ
  have hpos0 : (0 : Q') ≤ (t + -s) * A.approx n + (t + -s) * δ :=
    Q'.le_trans' 0 _ _ hprod (Q'.le_of_eqv eprod)
  have hstep : (t + -s) * A.approx n + (t + -s) * δ
      ≤ (t + -s) * A.approx n + ε :=
    Q'.add_le_add_left ((t + -s) * A.approx n) ((t + -s) * δ) ε hδ
  have hpos : (0 : Q') ≤ (t + -s) * A.approx n + ε :=
    Q'.le_trans' 0 _ _ hpos0 hstep
  -- transport `(t−s)·aₙ + ε  ≃  (t·aₙ + ε) + −(s·aₙ)`
  have e_a : ((t + -s) * A.approx n).eqv (t * A.approx n + -(s * A.approx n)) :=
    Q'.eqv_trans _ _ _
      (Q'.add_mul_eqv t (-s) (A.approx n))
      (Q'.add_eqv_congr_left (t * A.approx n) ((-s) * A.approx n) (-(s * A.approx n))
        (Q'.neg_mul_eqv s (A.approx n)))
  have e1 : ((t + -s) * A.approx n + ε).eqv
      ((t * A.approx n + -(s * A.approx n)) + ε) :=
    Q'.add_eqv_congr_right ((t + -s) * A.approx n)
      (t * A.approx n + -(s * A.approx n)) ε e_a
  have e2 : ((t * A.approx n + -(s * A.approx n)) + ε).eqv
      (t * A.approx n + (-(s * A.approx n) + ε)) :=
    Q'.add_assoc_eqv (t * A.approx n) (-(s * A.approx n)) ε
  have e3 : (t * A.approx n + (-(s * A.approx n) + ε)).eqv
      (t * A.approx n + (ε + -(s * A.approx n))) :=
    Q'.add_eqv_congr_left (t * A.approx n) (-(s * A.approx n) + ε)
      (ε + -(s * A.approx n)) (Q'.add_comm_eqv (-(s * A.approx n)) ε)
  have e4 : (t * A.approx n + (ε + -(s * A.approx n))).eqv
      ((t * A.approx n + ε) + -(s * A.approx n)) :=
    Q'.eqv_symm (Q'.add_assoc_eqv (t * A.approx n) ε (-(s * A.approx n)))
  have efull : ((t + -s) * A.approx n + ε).eqv
      ((t * A.approx n + ε) + -(s * A.approx n)) :=
    Q'.eqv_trans _ _ _ e1 (Q'.eqv_trans _ _ _ e2 (Q'.eqv_trans _ _ _ e3 e4))
  have hpos_t : (0 : Q') ≤ (t * A.approx n + ε) + -(s * A.approx n) :=
    Q'.le_trans' 0 _ _ hpos (Q'.le_of_eqv efull)
  exact Q'.le_of_sub_nonneg hpos_t

end YMGap.Constructive.CReal

namespace YMGap.Continuum.ReconstructionCapstone

/-! ## 0b. The `heatKernelSep w = w³` positivity helper -/

/-- `0 < (heatKernelSep w).num` when `0 < w` (needed for the unconditional gap).
`heatKernelSep w = qpow w 3 = ((1·w)·w)·w`, a threefold product of the positive
`w` with the positive `1`. -/
theorem heatKernelSep_num_pos (w : Q') (hwpos : (0 : Q') < w) :
    0 < (heatKernelSep w).num := by
  have h01 : (0 : Q') < (1 : Q') := by decide
  have hp1 : (0 : Q') < qpow w 1 := Q'.mul_pos h01 hwpos
  have hp2 : (0 : Q') < qpow w 2 := Q'.mul_pos hp1 hwpos
  have hp3 : (0 : Q') < qpow w 3 := Q'.mul_pos hp2 hwpos
  exact Q'.num_pos_of_pos hp3

/-! ## 1. The finite-volume Wilson GNS reconstruction bundle -/

/-- **The finite-volume Wilson GNS reconstruction bundle.**  Carries, over the
excited-tower spectral gap `G := excitedCharSpectralGapData op w hw0 hw1 N`
(with `G.gap.sep = heatKernelSep w = w³`), the FIVE reconstruction deliverables
simultaneously as data. -/
structure WilsonGNSReconstruction
    (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (L : AdditiveTransferOperator D.toGNSData)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w)
    (N : Nat) : Type where
  /-- (1) vector-space + scalar structure on the completion (PROVED). -/
  vspace : VectorScalingResidual D.toGNSData
  /-- (2a) the strictly-positive mass gap `Δ`, a genuine `CReal` (UNCONDITIONAL in sep). -/
  Δ : CReal
  /-- (2b) `Δ > 0`. -/
  Δ_pos : CReal.IsPositive Δ
  /-- (2c) honest pin `Δ ≃ −log sep` through the genuine range reduction. -/
  Δ_isLog : ∃ red : CRealLogRangeReduction
      (CReal.ofQ' (excitedCharSpectralGapData op w hw0 hw1 N).gap.sep),
    CReal.Equiv Δ (CReal.neg (CReal.log
      (CReal.ofQ' (excitedCharSpectralGapData op w hw0 hw1 N).gap.sep) red))
  /-- (3) operator-form gap on `vac⊥`:  `⟨Tx,x⟩ ≤ sep·⟨x,x⟩`. -/
  formGap : TransferFormGapResidual (excitedCharSpectralGapData op w hw0 hw1 N)
  /-- (4) `Δ` is the located inf of the reconstructed spectrum (attained at i=0). -/
  specInf : SpectrumInfResidual (excitedCharSpectralGapData op w hw0 hw1 N)
  /-- (5) the self-adjoint additive Hamiltonian `H` with `e^{−H}=T` (NAMED RESIDUAL). -/
  hamiltonian :
    BoundedFunctionalCalculusResidual (excitedCharSpectralGapData op w hw0 hw1 N) L

/-! ## 2. The capstone constructor -/

/-- **`wilson_gns_reconstruction_gap`.**  Assemble the full finite-volume Wilson
GNS reconstruction from exactly TWO honest inputs — RESIDUAL A (the diagonal
Schur / Peter–Weyl identities `schur_self` / `schur_T` with the finite character
coordinate map `coord`) and RESIDUAL B (the `BoundedFunctionalCalculusResidual`
datum `H`).  Everything else is discharged by reusing existing proofs verbatim;
in particular the scalar monotonicity `Rscalar` is discharged by
`CReal.RCscale_mono_scalar` and is NOT an exposed premise. -/
def wilson_gns_reconstruction_gap
    (D : SmulGNSData)
    (op : TransferOperator D.toGNSData.gnsComplete)
    (L : AdditiveTransferOperator D.toGNSData)
    (w t : Q') (ht : (0 : Q') ≤ t)
    (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (hwpos : (0 : Q') < w) (N : Nat)
    (hwin : Q'.abs (yOf (excitedCharSpectralGapData op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excitedCharSpectralGapData op w hw0 hw1 N).gap)) ≤ recipOdd 1)
    (coord : (D.toGNSData.gnsComplete).hilbert.carrier → Fin N → Q')
    (schur_self : ∀ x, (D.toGNSData.gnsComplete).hilbert.cinner x x
        = CReal.RCfinSum N (fun i =>
            Quotient.mk CReal.crealSetoid
              (CReal.mul (reflWeight t ht (i.val + 1))
                (CReal.ofQ' (coord x i * coord x i)))))
    (schur_T : ∀ x, (D.toGNSData.gnsComplete).hilbert.cinner (op.T x) x
        = CReal.RCfinSum N (fun i =>
            Quotient.mk CReal.crealSetoid
              (CReal.mul (CReal.ofQ' (qpow w (c4 (i.val + 1))))
                (CReal.mul (reflWeight t ht (i.val + 1))
                  (CReal.ofQ' (coord x i * coord x i))))))
    (H : BoundedFunctionalCalculusResidual
          (excitedCharSpectralGapData op w hw0 hw1 N) L) :
    WilsonGNSReconstruction D op L w hw0 hw1 hwpos N :=
  let G := excitedCharSpectralGapData op w hw0 hw1 N
  let hsepnum : 0 < G.gap.sep.num := heatKernelSep_num_pos w hwpos
  let h1 : G.gap.sep.num < (G.gap.sep.den : Int) := by
    have h : G.gap.sep.num * (1 : Int) < (1 : Int) * (G.gap.sep.den : Int) :=
      G.gap.sep_lt_one
    omega
  let be := binExpOf G.gap.sep hsepnum h1
  let hm1 := mant_pos G.gap.sep be.k hsepnum
  let hyb := mant_window G.gap.sep be hsepnum
  let red := reductionOf G.gap.sep be hsepnum
  { vspace := D.vectorScalingResidual
    Δ := hamiltonianGapRealAll (mant G.gap.sep be.k) be.k hm1 hyb
    Δ_pos := hamiltonianGapRealAll_pos (mant G.gap.sep be.k) be.k hm1
      (mant_lt_one G.gap.sep be.k be.hlt) hyb
    Δ_isLog := ⟨red, TrigAdd.equiv_of_approx_eqv (fun n =>
      add_neg_eqv_neg_neg_add ((kLog2 be.k).approx n)
        ((logRat (mant G.gap.sep be.k) hm1 hyb).approx n))⟩
    formGap := wilsonFormGap op w t ht hw0 hw1 N
      CReal.RCscale_mono_scalar coord schur_self schur_T
    specInf := HamiltonianSpectrumInf.spectrumInfResidual op w hw0 hw1 N hwin
    hamiltonian := H }

/-! ## 3. Optional strengthening: the located-inf lower bound -/

/-- Optional strengthening: `Δ ≤ E_i` for every in-window excited mode `i` (the
located-inf LOWER bound, attained at `i = 0`), gated on the two named
monotonicity data `Y` / `A`.  Offered separately, NOT a bundle field. -/
theorem wilson_reconstruction_inf_lower_bound
    (D : SmulGNSData) (op : TransferOperator D.toGNSData.gnsComplete)
    (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat)
    (Y : HamiltonianSpectrumInf.YOfMonotone)
    (A : HamiltonianSpectrumInf.ArtanhMonotoneWindow)
    (hwin : Q'.abs (yOf (excitedCharSpectralGapData op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excitedCharSpectralGapData op w hw0 hw1 N).gap)) ≤ recipOdd 1)
    (i : Nat)
    (hm1i : (0 : Q') < (excitedCharModel w hw0 N).lam i + 1)
    (hwini : Q'.abs (yOf ((excitedCharModel w hw0 N).lam i) hm1i) ≤ recipOdd 1) :
    CReal.leEv ((excitedCharSpectralGapData op w hw0 hw1 N).hamiltonianGapReal hwin)
      (CReal.neg (logRat ((excitedCharModel w hw0 N).lam i) hm1i hwini)) :=
  HamiltonianSpectrumInf.hamiltonianGap_le_energy op w hw0 hw1 N Y A hwin i hm1i hwini

end YMGap.Continuum.ReconstructionCapstone

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Constructive.CReal.RCscale_mono_scalar
#print axioms YMGap.Continuum.ReconstructionCapstone.heatKernelSep_num_pos
#print axioms YMGap.Continuum.ReconstructionCapstone.WilsonGNSReconstruction
#print axioms YMGap.Continuum.ReconstructionCapstone.wilson_gns_reconstruction_gap
#print axioms YMGap.Continuum.ReconstructionCapstone.wilson_reconstruction_inf_lower_bound
