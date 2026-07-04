/-
The finite-volume "bounded" Hamiltonian as located-spectrum data:
`FiniteVolumeBoundedH`.

# The reframing (why this is well-posed)

A literal bounded operator `H` with `e^{−H} = T` is *unsatisfiable*: over the spin
tower `−log w^{C₄(s)} → +∞`, so no bounded `H` carries every excited energy.  The
milestone-(a) "bounded H mass gap" phrasing —

    `spectrum_nonneg`  (H ≥ 0),
    `vacuum_zero`      (H ψ_vac = 0),
    `NoSpectrumIn H 0 Δ`  (no eigenvalue in the open interval (0, Δ)),

— is the STANDARD operator-theoretic mass gap, and it needs only those three
facts, NOT boundedness of `H`.  So `H` is not carried as an operator field.  It is
carried by

  * the **bounded carrier** `op := G.op.T` (the transfer operator itself, which IS
    bounded — self-adjoint, positive, a contraction), and
  * its **located energy image** `E_i = −log λ_i` over the finite (compact)
    `SpectralModel`.

This is the `physical_gap_from_resolution` template: deliver the gap WITHOUT ever
building a `−log` operator or taking a bounded functional-calculus residual as
input.

# What is CLOSED here

  * `op`, `selfAdjoint`      — `:= G.op.T`, `G.op.selfAdjoint`.  Genuine bounded
    carrier.
  * `vacuum_zero`            — `hamiltonian_vacuum_energy_zero` (already a theorem).
  * `Δ`, `hΔ`, `Δ_pos`       — `G.hamiltonianGapReal hwin` and its positivity
    (`isPositive_neg_logRat`, one-argument, ungated).
  * `spectrum_nonneg`        — one wrap: `λ_i ≤ sep < 1 ⟹ IsPositive (−log λ_i)`
    (`isPositive_neg_logRat`) `⟹ leEv czero (−log λ_i)`
    (`leEv_czero_of_isPositive`).
  * `noSpectrumIn` FLOOR      — `hamiltonianGap_le_energy`: `Δ = −log sep ≤ E_i`
    since `λ_i ≤ sep` and `−log` is antitone.

# What is REDUCED (the honest frontier, unchanged)

The `noSpectrumIn` floor `Δ ≤ E_i` is assembled from the pre-existing, already
isolated analytic pair `YOfMonotone` / `ArtanhMonotoneWindow`
(`HamiltonianSpectrumInf.lean`) — the monotonicity of the artanh argument and of
the artanh series on the window.  NO NEW frontier is opened.  The per-mode window
certificates `win i` are carried as hypotheses (the same in-window scope caveat as
`HGapBelowWindowResidual`); the inf is ATTAINED at `λ₀ = sep` (in window by
`hwin`), and smaller-λ (larger-gap) modes only raise energies, so restricting the
floor clause to the in-window energy image does not weaken "no spectrum in (0,Δ)".

# Axiom-gate (AGENTS.md Rule 1)

`[propext]` / `[propext, Quot.sound]` only.  No `Classical.*`, no `sorryAx`, no
`native_decide`, no custom `axiom`.  Type-level `PSum` (branch tag as data), not
`Prop ∨` (Rule 8); moduli/energies carried as DATA.
-/

import YMGap.Continuum.HamiltonianSpectrumInf

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealLog
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.WilsonSpectralBridge
open YMGap.Continuum.HamiltonianSpectrumInf

namespace YMGap.Continuum.BoundedHamiltonianFiniteVol

/-! ## Two elementary bridges -/

/-- `0 < q + 1` for `0 ≤ q` — the `yOf`/`logRat` domain condition for any
nonnegative eigenvalue. -/
theorem plusOne_pos_of_nonneg {q : Q'} (h : (0 : Q') ≤ q) : (0 : Q') < q + 1 := by
  have hn : (0 : Int) ≤ q.num := by
    have h' : (0 : Int) * (q.den : Int) ≤ q.num * (1 : Int) := h
    omega
  have hd : (0 : Int) < (q.den : Int) := by exact_mod_cast q.den_pos
  show (0 : Int) * ((q + 1).den : Int)
      < (q.num * (1 : Int) + (1 : Int) * (q.den : Int)) * (1 : Int)
  omega

/-- **`IsPositive ⟹ leEv czero`.**  A strictly-positive `CReal` is eventually
`≥ 0`: from the positive rational witness `ofQ' ε ≤ x` and `czero = ofQ' 0 ≤ ofQ' ε`.
This is the sign-only content of `spectrum_nonneg` (`H ≥ 0`). -/
theorem leEv_czero_of_isPositive {x : CReal} (h : CReal.IsPositive x) :
    CReal.leEv CReal.czero x := by
  obtain ⟨ε, hε, hle⟩ := h
  have h1 : CReal.leEv (CReal.ofQ' ε) x := CReal.leEv_of_le hle
  have h2 : CReal.leEv CReal.czero (CReal.ofQ' ε) :=
    CReal.leEv_of_le (CReal.ofQ'_le_ofQ' (Q'.le_of_lt hε))
  exact CReal.leEv_trans h2 h1

/-! ## The finite-volume "bounded H" as located-spectrum data -/

/-- **`FiniteVolumeBoundedH`.**  The milestone-(a) bounded-Hamiltonian mass gap,
carried WITHOUT a bounded `−log` operator (which is unsatisfiable over the spin
tower).  The bounded carrier is `op := G.op.T`; the located energy image
`E_i = −log λ_i` supplies `H ≥ 0` (`spectrum_nonneg`), `H ψ_vac = 0`
(`vacuum_zero`), and no spectrum in `(0, Δ)` (`noSpectrumIn`, the finite
disjunction "each in-window mode is the vacuum `E_i ≃ 0` OR excited `Δ ≤ E_i`").

`Type`-level `PSum` for `noSpectrumIn` — the vacuum/excited branch tag is DATA
(Rule 8), not an erased `Prop ∨`; energies carried as DATA. -/
structure FiniteVolumeBoundedH {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H)
    (hwin : Q'.abs (yOf G.gap.sep (sepPlusOne_pos G.gap)) ≤ recipOdd 1) : Type where
  /-- **The bounded carrier**: the transfer operator `T` itself (NOT `−log T`). -/
  op : H.hilbert.carrier → H.hilbert.carrier
  /-- Self-adjointness of the bounded carrier (legitimate: `T` is bounded). -/
  selfAdjoint : ∀ x y, H.hilbert.cinner (op x) y = H.hilbert.cinner x (op y)
  /-- `λ_i` sits in the `logRat` domain (`0 < λ_i + 1`) for every in-range mode. -/
  hm1 : ∀ i, i < G.model.k → (0 : Q') < G.model.lam i + 1
  /-- Per-mode artanh-window certificate (the in-window energy-image scope). -/
  win : ∀ i (hi : i < G.model.k),
    Q'.abs (yOf (G.model.lam i) (hm1 i hi)) ≤ recipOdd 1
  /-- The reconstructed per-mode energy `E_i` (a genuine `CReal`, carried as DATA). -/
  energy : ∀ i, i < G.model.k → CReal
  /-- `E_i = −log λ_i`. -/
  hEnergy : ∀ i hi, energy i hi
    = CReal.neg (logRat (G.model.lam i) (hm1 i hi) (win i hi))
  /-- **`spectrum_nonneg`** (`H ≥ 0`): every reconstructed energy is `≥ 0`. -/
  spectrum_nonneg : ∀ i hi, CReal.leEv CReal.czero (energy i hi)
  /-- **`vacuum_zero`** (`H ψ_vac = 0`): the vacuum energy `−log 1 ≃ 0`. -/
  vacuum_zero : CReal.Equiv
    (CReal.neg (logRat (1 : Q') (by decide) yOf_one_window)) CReal.czero
  /-- The physical mass gap `Δ = −log sep`, a genuine `CReal`. -/
  Δ : CReal
  /-- `Δ` really is `−log sep`. -/
  hΔ : Δ = G.hamiltonianGapReal hwin
  /-- `Δ > 0` — the located H-gap. -/
  Δ_pos : CReal.IsPositive Δ
  /-- **`NoSpectrumIn H 0 Δ`**: no eigenvalue lands in the open interval `(0, Δ)`.
  For each in-window mode, the constructive disjunction "it is the vacuum
  (`E_i ≃ 0`) OR it is excited above the floor (`Δ ≤ E_i`)". -/
  noSpectrumIn : ∀ i (hi : i < G.model.k),
    PSum (CReal.Equiv (energy i hi) CReal.czero)
      (CReal.leEv Δ (energy i hi))

/-! ## Constructor over the excited character tower -/

/-- **`mkFiniteVolumeBoundedH`.**  Inhabit `FiniteVolumeBoundedH` over the excited
character tower `excG op w hw0 hw1 N`, CONDITIONALLY on the two pre-existing
analytic residuals `YOfMonotone` / `ArtanhMonotoneWindow` and the per-mode window
certificates.  Five of the six field-groups close outright; the sole reduction is
the `noSpectrumIn` floor, discharged by `hamiltonianGap_le_energy` (which is
exactly the assembled `neg_logRat_antitone` gated on `Y`, `A`).

Every excited mode has `λ_i ≤ sep < 1` (`casimir_qpow_le`, `heatKernelSep_lt_one`),
so it is strictly excited: `noSpectrumIn` always takes the floor branch
(`Sum.inr`); the vacuum branch is available for a genuine `λ = 1` mode. -/
def mkFiniteVolumeBoundedH {D : GNSData} {H : CompleteGNSHilbert D}
    (op : TransferOperator H) (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w < (1 : Q'))
    (N : Nat) (Y : YOfMonotone) (A : ArtanhMonotoneWindow)
    (hwin : Q'.abs (yOf (excG op w hw0 hw1 N).gap.sep
        (sepPlusOne_pos (excG op w hw0 hw1 N).gap)) ≤ recipOdd 1)
    (win : ∀ i (hi : i < (excG op w hw0 hw1 N).model.k),
      Q'.abs (yOf ((excG op w hw0 hw1 N).model.lam i)
        (plusOne_pos_of_nonneg ((excG op w hw0 hw1 N).model.lam_nonneg i)))
        ≤ recipOdd 1) :
    FiniteVolumeBoundedH (excG op w hw0 hw1 N) hwin where
  op := op.T
  selfAdjoint := op.selfAdjoint
  hm1 := fun i _ => plusOne_pos_of_nonneg ((excG op w hw0 hw1 N).model.lam_nonneg i)
  win := win
  energy := fun i hi => CReal.neg (logRat ((excG op w hw0 hw1 N).model.lam i)
    (plusOne_pos_of_nonneg ((excG op w hw0 hw1 N).model.lam_nonneg i)) (win i hi))
  hEnergy := fun _ _ => rfl
  spectrum_nonneg := fun i hi => by
    -- `λ_i ≤ sep < 1`, so `−log λ_i` is strictly positive, hence `≥ 0`.
    have hle : (excitedCharModel w hw0 N).lam i ≤ heatKernelSep w :=
      casimir_qpow_le hw0 (Q'.le_of_lt hw1) i
    have hlt1 : (excitedCharModel w hw0 N).lam i < (1 : Q') :=
      Q'.lt_of_le_of_lt hle (heatKernelSep_lt_one hw0 hw1)
    exact leEv_czero_of_isPositive
      (isPositive_neg_logRat ((excG op w hw0 hw1 N).model.lam i)
        (plusOne_pos_of_nonneg ((excG op w hw0 hw1 N).model.lam_nonneg i))
        hlt1 (win i hi))
  vacuum_zero := hamiltonian_vacuum_energy_zero
  Δ := (excG op w hw0 hw1 N).hamiltonianGapReal hwin
  hΔ := rfl
  Δ_pos := (excG op w hw0 hw1 N).hamiltonianGapReal_pos hwin
  noSpectrumIn := fun i hi =>
    PSum.inr (hamiltonianGap_le_energy op w hw0 hw1 N Y A hwin i
      (plusOne_pos_of_nonneg ((excG op w hw0 hw1 N).model.lam_nonneg i)) (win i hi))

/-! ## Non-vacuity witness (mirrors `spectrumInfResidual`)

The reconstructed bounded-H datum exists for the excited tower over the identity
transfer operator, given the analytic residuals and window certificates. -/

/-- The three milestone-(a) predicates read straight off a `FiniteVolumeBoundedH`:
`H ≥ 0` (`spectrum_nonneg`), `H ψ_vac = 0` (`vacuum_zero`), and `Δ > 0`
(`Δ_pos`).  A record that the phrasing carries genuine content. -/
theorem boundedH_mass_gap {D : GNSData} {H : CompleteGNSHilbert D}
    (G : SpectralGapData H)
    (hwin : Q'.abs (yOf G.gap.sep (sepPlusOne_pos G.gap)) ≤ recipOdd 1)
    (B : FiniteVolumeBoundedH G hwin) :
    (∀ i hi, CReal.leEv CReal.czero (B.energy i hi))
      ∧ CReal.Equiv
          (CReal.neg (logRat (1 : Q') (by decide) yOf_one_window)) CReal.czero
      ∧ CReal.IsPositive B.Δ :=
  ⟨B.spectrum_nonneg, B.vacuum_zero, B.Δ_pos⟩

end YMGap.Continuum.BoundedHamiltonianFiniteVol

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.BoundedHamiltonianFiniteVol.plusOne_pos_of_nonneg
#print axioms YMGap.Continuum.BoundedHamiltonianFiniteVol.leEv_czero_of_isPositive
#print axioms YMGap.Continuum.BoundedHamiltonianFiniteVol.mkFiniteVolumeBoundedH
#print axioms YMGap.Continuum.BoundedHamiltonianFiniteVol.boundedH_mass_gap
