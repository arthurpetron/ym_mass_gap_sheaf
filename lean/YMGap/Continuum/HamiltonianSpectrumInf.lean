/-
The reconstructed Hamiltonian's spectrum-infimum, identified as the located gap,
attained at the top excited transfer eigenvalue.

# What this module delivers

For the excited character model `S = excitedCharModel w hw0 N` and its located
gap `g = excitedCharLocatedGap w hw0 hw1 N` (`sep = heatKernelSep w = w³`), the
reconstructed energies are `E_i = −log λ_i` with `λ_i = qpow w (c4 (i+1))`.
Because `−log` is antitone and `λ₀ = qpow w (c4 1) = qpow w 3 = sep` is the LARGEST
excited eigenvalue (`c4 (i+1) ≥ 3`, `casimir_qpow_le`), the located minimum of the
energy image is

    inf_i E_i  =  −log sep  =  G.hamiltonianGapReal hwin ,

attained at model index `i = 0` (physics spin `s = 1`).

This is the *content* of the previously-deferred `SpectrumInfResidual`
(`GNSHamiltonian.lean`): the module both DISCHARGES that named residual (with
`infSpec := G.hamiltonianGapReal hwin`) and proves the auxiliary located-inf
theorem that is its mathematical justification.

## Genuine content proved here (elementary assembly, axiom-clean)

  * `le_specMaxAux` / `lam_le_specMax` — the dual of `specMaxAux_le_iff`: every
    entry `λ_j` (`j < n`) is `≤ specMaxAux`; hence `sep = λ₀ ≤ specMax S`, which
    with `LocatedSpectralGap.located` pins `specMax S = sep`, ATTAINED at `0`.
  * `CReal.neg_leEv_neg` — negation is `leEv`-antitone (`−log` antitone,
    Lemma B), off `Q'.neg_le_neg_add`.
  * `scaleTwo_leEv` — the doubling `x ↦ 2x` is `leEv`-monotone (Lemma A3), off
    `CReal.leEv_add`.
  * `Equiv.refl` — reflexivity of `CReal.Equiv` (local; used for the residual
    discharge via definitional proof-irrelevance of the window certificate).
  * `energyZero_eq_gap` — the attainment identity `E₀ = G.hamiltonianGapReal hwin`
    (a `rfl`-chain: `c4 1 = 3`, `qpow w 3 = heatKernelSep w = sep`).
  * `hamiltonianGap_le_energy` — the located-inf LOWER bound: for every in-window
    excited index `i`, `G.hamiltonianGapReal hwin ≤ E_i` (via B ∘ A3 ∘ the
    monotonicity primitives).  Assembled from the two named analytic residuals.
  * `spectrumInfResidual` — the DISCHARGE of `SpectrumInfResidual`.

## The honest residuals (the sharp analytic wall)

The load-bearing new analytic work is the monotonicity of the artanh series on
the window (odd-power monotonicity of the signed terms) and the monotonicity of
the artanh argument `yOf`.  These are carried as two named `Type`-level data
(Rule 8), `YOfMonotone` and `ArtanhMonotoneWindow`, and the located-inf lower
bound is assembled GENUINELY from them together with the elementary Lemmas B/A3.

Scope caveat (matches `HGapBelowWindowResidual`): the lower bound `Δ ≤ E_i`
requires `E_i = −log λ_i` to be defined, i.e. `λ_i` in the artanh window
`|yOf λ_i| ≤ 1/3`; the finite located inf is honestly stated over the in-window
eigenvalue image.  The infimum is ATTAINED at the largest eigenvalue `λ₀ = sep`
(window membership `hwin`); smaller-λ (larger-gap) modes only raise energies and
cannot lower the inf.

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`,
no `native_decide`, no custom `axiom`.
-/

import YMGap.Continuum.WilsonSpectralBridge
import YMGap.Continuum.GNSHamiltonian

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.WilsonSpectralBridge

namespace YMGap.Continuum.HamiltonianSpectrumInf

/-! ## `max'` lower bounds (from the local `max'_le_iff`) -/

/-- `a ≤ max' a b` (via `max'_le_iff` at `max' a b`). -/
theorem le_max'_left (a b : Q') : a ≤ Q'.max' a b :=
  ((max'_le_iff a b (Q'.max' a b)).mp (Q'.le_refl' _)).1

/-- `b ≤ max' a b`. -/
theorem le_max'_right (a b : Q') : b ≤ Q'.max' a b :=
  ((max'_le_iff a b (Q'.max' a b)).mp (Q'.le_refl' _)).2

/-! ## Lemma C — the dual `specMax` bound (attainment) -/

/-- **Every prefix entry is `≤ specMaxAux`.**  Dual to `specMaxAux_le_iff`; a
`specMaxAux` induction off `le_max'_left` / `le_max'_right`. -/
theorem le_specMaxAux (lam : Nat → Q') :
    ∀ n j, j < n → lam j ≤ specMaxAux lam n
  | 0, j, hj => absurd hj (Nat.not_lt_zero j)
  | n + 1, j, hj => by
      show lam j ≤ Q'.max' (specMaxAux lam n) (lam n)
      rcases Nat.lt_or_ge j n with hjn | hjn
      · exact Q'.le_trans' _ _ _ (le_specMaxAux lam n j hjn)
          (le_max'_left (specMaxAux lam n) (lam n))
      · have hje : j = n := Nat.le_antisymm (Nat.lt_succ_iff.mp hj) hjn
        subst hje
        exact le_max'_right (specMaxAux lam j) (lam j)

/-- **`λ_j ≤ specMax S`** for every in-range mode `j` — the located top-of-
spectrum is genuinely an upper bound attained by the spectrum. -/
theorem lam_le_specMax (S : SpectralModel) (j : Nat) (hj : j < S.k) :
    S.lam j ≤ specMax S :=
  le_specMaxAux S.lam S.k j hj

/-! ## Lemma B — negation is `leEv`-antitone (`−log` antitone) -/

/-- **`leEv` antitone under negation.**  `leEv x y → leEv (neg y) (neg x)`.
Pointwise: `x_n ≤ y_n + ε ⟹ −y_n ≤ −x_n + ε` (`Q'.neg_le_neg_add`). -/
theorem neg_leEv_neg {x y : CReal} (h : CReal.leEv x y) :
    CReal.leEv (CReal.neg y) (CReal.neg x) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  show (CReal.neg y).approx n ≤ (CReal.neg x).approx n + ε
  rw [CReal.neg_approx, CReal.neg_approx]
  exact Q'.neg_le_neg_add (hN n hn)

/-! ## Lemma A3 — doubling is `leEv`-monotone -/

/-- **`scaleTwo` (`x ↦ x + x`) is `leEv`-monotone.**  Descends `CReal.leEv_add`
on the diagonal. -/
theorem scaleTwo_leEv {x y : CReal} (h : CReal.leEv x y) :
    CReal.leEv (scaleTwo x) (scaleTwo y) :=
  CReal.leEv_add h h

/-! ## `CReal.Equiv` reflexivity (for the residual discharge) -/

/-- Reflexivity of `CReal.Equiv` (local). -/
theorem Equiv.refl (x : CReal) : CReal.Equiv x x :=
  fun ε hε => ⟨0, fun n _ =>
    ⟨Q'.add_le_self_of_nonneg (x.approx n) ε (Q'.le_of_lt hε),
     Q'.add_le_self_of_nonneg (x.approx n) ε (Q'.le_of_lt hε)⟩⟩

/-! ## The two analytic residuals (the sharp monotonicity wall, Rule 8)

The load-bearing new analytic work.  `YOfMonotone` is the monotonicity of the
artanh argument `yOf m = (m−1)/(m+1)`; `ArtanhMonotoneWindow` is the
monotonicity of the artanh series `Σ y^{2k+1}/(2k+1)` on the window (odd-power
monotonicity of the signed terms).  Together they give `logRat` monotone, hence
(via Lemma B) `−log` antitone — the content of the located-inf lower bound. -/

/-- **`yOf` monotone (Lemma A1, named).**  `a ≤ b ⟹ yOf a ≤ yOf b`. -/
structure YOfMonotone : Type where
  mono : ∀ (a b : Q') (ha : (0 : Q') < a + 1) (hb : (0 : Q') < b + 1),
    a ≤ b → yOf a ha ≤ yOf b hb

/-- **`artanh` monotone on the window (Lemma A2, named — the load-bearing new
analytic work).**  `y ≤ y' ⟹ leEv (artanh y) (artanh y')` for window arguments.
Its content is the odd-power monotonicity of each signed term
`y^{2k+1}/(2k+1)`, hence of every partial sum. -/
structure ArtanhMonotoneWindow : Type where
  mono : ∀ (y y' : Q') (hy : Q'.abs y ≤ recipOdd 1) (hy' : Q'.abs y' ≤ recipOdd 1),
    y ≤ y' → CReal.leEv (artanh y hy) (artanh y' hy')

/-- **`logRat` monotone on the window (Lemma A, assembled).**  From the two
analytic primitives + Lemma A3: `a ≤ b ⟹ leEv (logRat a) (logRat b)`. -/
theorem logRat_leEv_of_le (Y : YOfMonotone) (A : ArtanhMonotoneWindow)
    {a b : Q'} (ha : (0 : Q') < a + 1) (hb : (0 : Q') < b + 1)
    (hwa : Q'.abs (yOf a ha) ≤ recipOdd 1) (hwb : Q'.abs (yOf b hb) ≤ recipOdd 1)
    (hab : a ≤ b) :
    CReal.leEv (logRat a ha hwa) (logRat b hb hwb) :=
  scaleTwo_leEv (A.mono (yOf a ha) (yOf b hb) hwa hwb (Y.mono a b ha hb hab))

/-- **`−log` antitone on the window (Lemma B ∘ A, assembled).**
`a ≤ b ⟹ leEv (neg (logRat b)) (neg (logRat a))`. -/
theorem neg_logRat_antitone (Y : YOfMonotone) (A : ArtanhMonotoneWindow)
    {a b : Q'} (ha : (0 : Q') < a + 1) (hb : (0 : Q') < b + 1)
    (hwa : Q'.abs (yOf a ha) ≤ recipOdd 1) (hwb : Q'.abs (yOf b hb) ≤ recipOdd 1)
    (hab : a ≤ b) :
    CReal.leEv (CReal.neg (logRat b hb hwb)) (CReal.neg (logRat a ha hwa)) :=
  neg_leEv_neg (logRat_leEv_of_le Y A ha hb hwa hwb hab)

/-! ## The concrete excited-tower `SpectralGapData` and its located inf -/

/-- The excited-tower spectral-gap data over `op`. -/
def excG {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat) : SpectralGapData H :=
  excitedCharSpectralGapData op w hw0 hw1 N

/-- **Attainment (rational).**  The model-index-`0` eigenvalue is exactly the
separator: `S.lam 0 = qpow w (c4 1) = qpow w 3 = heatKernelSep w = gap.sep`. -/
theorem lam_zero_eq_sep (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q')) (N : Nat) :
    (excitedCharModel w hw0 N).lam 0 = (excitedCharLocatedGap w hw0 hw1 N).sep :=
  rfl

/-- **The attainment identity as reconstructed energies.**  With `λ₀ = sep`, the
`0`-mode energy `E₀ = neg (logRat λ₀)` is `hamiltonianGapReal hwin` (up to the
definitionally-irrelevant window/positivity proofs). -/
theorem energyZero_eq_gap {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat)
    (hwin : Q'.abs (yOf (excG op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excG op w hw0 hw1 N).gap)) ≤ recipOdd 1) :
    CReal.Equiv
      (CReal.neg (logRat (excG op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excG op w hw0 hw1 N).gap) hwin))
      ((excG op w hw0 hw1 N).hamiltonianGapReal hwin) :=
  Equiv.refl _

/-- **The located-inf LOWER bound.**  For every excited mode `i` that lies in the
artanh window (carrying its own `hm1_i`, `hwin_i`), the reconstructed gap
`Δ = −log sep` is `≤` the mode energy `E_i = −log λ_i`.  Assembled from the two
analytic residuals via the monotone chain (Lemmas A, B).  Because `λ_i ≤ sep`
(`casimir_qpow_le`), `E_i ≥ Δ`; equality holds at `i = 0`.  Hence `Δ` is the
located minimum of the in-window energy image. -/
theorem hamiltonianGap_le_energy {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat) (Y : YOfMonotone) (A : ArtanhMonotoneWindow)
    (hwin : Q'.abs (yOf (excG op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excG op w hw0 hw1 N).gap)) ≤ recipOdd 1)
    (i : Nat)
    (hm1i : (0 : Q') < (excitedCharModel w hw0 N).lam i + 1)
    (hwini : Q'.abs (yOf ((excitedCharModel w hw0 N).lam i) hm1i) ≤ recipOdd 1) :
    CReal.leEv ((excG op w hw0 hw1 N).hamiltonianGapReal hwin)
      (CReal.neg (logRat ((excitedCharModel w hw0 N).lam i) hm1i hwini)) := by
  have hle : (excitedCharModel w hw0 N).lam i ≤ (excG op w hw0 hw1 N).gap.sep :=
    casimir_qpow_le hw0 (Q'.le_of_lt hw1) i
  -- `neg (logRat sep) ≤ neg (logRat λ_i)` since `λ_i ≤ sep` and `−log` antitone.
  exact neg_logRat_antitone Y A hm1i (sepPlusOne_pos (excG op w hw0 hw1 N).gap)
    hwini hwin hle

/-! ## Discharge of `SpectrumInfResidual` -/

/-- **The discharge.**  `SpectrumInfResidual (excG)` with `infSpec := Δ = −log sep`.
The `agrees` field is reflexivity of `CReal.Equiv`: `hamiltonianGapReal hwin` and
`hamiltonianGapReal hwin'` are DEFINITIONALLY equal (definitional proof-
irrelevance of the window certificate), so `infSpec` agrees with every witness. -/
def spectrumInfResidual {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat)
    (hwin : Q'.abs (yOf (excG op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excG op w hw0 hw1 N).gap)) ≤ recipOdd 1) :
    SpectrumInfResidual (excG op w hw0 hw1 N) where
  infSpec := (excG op w hw0 hw1 N).hamiltonianGapReal hwin
  agrees := fun _ => Equiv.refl _

end YMGap.Continuum.HamiltonianSpectrumInf

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.HamiltonianSpectrumInf.le_specMaxAux
#print axioms YMGap.Continuum.HamiltonianSpectrumInf.lam_le_specMax
#print axioms YMGap.Continuum.HamiltonianSpectrumInf.neg_leEv_neg
#print axioms YMGap.Continuum.HamiltonianSpectrumInf.scaleTwo_leEv
#print axioms YMGap.Continuum.HamiltonianSpectrumInf.Equiv.refl
#print axioms YMGap.Continuum.HamiltonianSpectrumInf.logRat_leEv_of_le
#print axioms YMGap.Continuum.HamiltonianSpectrumInf.neg_logRat_antitone
#print axioms YMGap.Continuum.HamiltonianSpectrumInf.lam_zero_eq_sep
#print axioms YMGap.Continuum.HamiltonianSpectrumInf.energyZero_eq_gap
#print axioms YMGap.Continuum.HamiltonianSpectrumInf.hamiltonianGap_le_energy
#print axioms YMGap.Continuum.HamiltonianSpectrumInf.spectrumInfResidual
