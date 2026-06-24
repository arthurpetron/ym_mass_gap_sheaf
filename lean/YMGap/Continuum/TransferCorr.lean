/-
Wall-2a closure — INHABITING `WilsonConnCorr.WilsonGMatchesAbstract` via the
TRANSFER-MATRIX route, NOT `eqv_refl`.

# Why this module exists (what it de-fakes)

`Continuum/WilsonConnCorr.lean` carries the named Type-level obligation
`WilsonGMatchesAbstract w` (fields `absCorr : Nat → Nat → Q'` and
`matchesAbs : ∀ M n, (wilsonG w (M+1) n).eqv (absCorr M n)`) with NO inhabitant:
the identity tying the REAL connected character double-sum `wilsonG` to the
abstract spectral `corr` of a reconstructed transfer operator.  It is explicitly
NOT faked as `eqv_refl` (contrast `WilsonCorrelator.genuineRealCorrelatorLink`,
whose `matches_abstract` IS reflexivity only because its correlator is DEFINED to
be the abstract `corr`).

This module GENUINELY inhabits `WilsonGMatchesAbstract` for the SINGLE-LINE
connecting-chain geometry, through the transfer-matrix identity.  The single-edge
heat-kernel transfer operator on class functions is DIAGONAL in the SU(2)
characters with eigenvalues `coeffW w r`; on the excited subspace (reps `r ≥ 1`)
its connected two-point function at separation `n` is exactly the proved
`wilsonG_collapse` right-hand side

    connSum w M n  =  Σ_{r=1}^{M} (coeffW w r)^{n+1}.

We reconstruct that diagonal transfer operator as a multi-mode
`SpectralModel`, prove its abstract `corr` equals `connSum`, and compose with the
ALREADY-PROVED `wilsonG_collapse` to inhabit `WilsonGMatchesAbstract`.

# The reconstructed transfer operator (the weight / eigenvalue split)

`SpectralModel.corr S n = Σ_{i<k} (S.w i) · (S.lam i)^n`, while a connected chain
of `n + 1` plaquettes at common excited rep `r = i + 1` contributes
`(coeffW w (i+1))^{n+1}`.  Writing
`(coeffW w (i+1))^{n+1} = coeffW w (i+1) · (coeffW w (i+1))^n` splits the chain
into ONE end factor (the spectral WEIGHT) times the `n`-fold transfer (the
EIGENVALUE).  Hence the reconstructed operator has, for the `M` excited modes
`i = 0, …, M-1` (so `r = i + 1` ranges over `1, …, M`):

    k = M,   w i = coeffW w (i + 1),   lam i = coeffW w (i + 1),

and `corr (reconTransfer w hw M) n = Σ_{i<M} coeffW w (i+1) · (coeffW w (i+1))^n
= Σ_{i<M} (coeffW w (i+1))^{n+1} = connSum w M n` termwise (the `Q'.pow_succ`
split).  This is the diagonal Källén–Lehmann form of the single-edge transfer
operator restricted to its excited (vacuum-subtracted) eigenspace.

# M-indexing

`wilsonG_collapse w M n : (wilsonG w (M+1) n).eqv (connSum w M n)` carries the
`M+1`/`M` shift (the `M+1` cutoff so the vacuum row `a = 0` is the head and the
excited window is `1, …, M`).  We keep the SAME convention: `absCorr M n :=
corr (reconTransfer w hw M) n` reconstructs the `M` excited modes, and
`matchesAbs M n` is `wilsonG w (M+1) n ≃ connSum w M n ≃ corr (reconTransfer …) n`
— `wilsonG_collapse` composed (via `eqv_trans`) with the reconstructed-operator
identity `reconTransfer_corr_eq_connSum`.

# What is PROVED here (all genuine — no fakes)

  * `reconTransfer w hw M : SpectralModel` — the reconstructed diagonal transfer
    operator on the `M` excited modes (`k = M`, weight = eigenvalue =
    `coeffW w (i+1)`), with `w_nonneg` / `lam_nonneg` from `coeffW_nonneg`.
  * `reconTransfer_corr_eq_connSum` — `corr (reconTransfer w hw M) n ≃ connSum w M n`,
    a `finSum` termwise congruence (`(coeffW w (i+1))^{n+1} = coeffW w (i+1)·…^n`).
  * `wilsonGMatchesAbstract_transfer w hw : WilsonConnCorr.WilsonGMatchesAbstract w`
    — THE CLOSURE: `absCorr := corr (reconTransfer …)`, and `matchesAbs` is the
    PROVED `wilsonG_collapse` composed with `reconTransfer_corr_eq_connSum`.  The
    obligation is now GENUINELY inhabited — its `matchesAbs` is derived content
    (the single-rep collapse + the reconstructed-operator identity), NOT
    `eqv_refl`.

# NAMED-open residual (NOT touched here)

This de-fakes `WilsonGMatchesAbstract` for the SINGLE-LINE connecting chain only.
The FULL interacting multi-plaquette / loopy connected correlator (the general
connected geometry, the Mayer / Dobrushin-ratio induction) stays the separate
named wall — it is NOT addressed by this transfer-matrix identity, which is the
single-line geometry whose `wilsonG` collapses to one excited rep along the chain.

# Constructive contract (AGENTS.md Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` arithmetic and a single structural `finSum`
termwise congruence over the reused proved `wilsonG_collapse` and `coeffW_nonneg`.
No `Classical.*`, no `Real`, no `native_decide`, no `decide` on non-decidable
props, no `sorry` / `admit` / new `axiom`, no `Prop := True`.  The inhabitant of
`WilsonGMatchesAbstract` is GENUINE: `matchesAbs` is the proved single-rep
collapse composed with a real `finSum` congruence, NOT reflexivity.  Witnesses are
`Type`-level data.  Every load-bearing declaration is gated with `#print axioms`
(permitted: `propext` / `Quot.sound`).
-/

import YMGap.Continuum.WilsonConnCorr
import YMGap.Continuum.SpectralGap

namespace YMGap.Continuum.TransferCorr

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.WilsonConnCorr

/-! ## 1. The reconstructed diagonal transfer operator on the excited modes

The single-edge heat-kernel transfer operator on SU(2) class functions is
diagonal in the characters with eigenvalues `coeffW w r`.  Restricted to the
excited (vacuum-subtracted, `r ≥ 1`) eigenspace and reconstructed as a finite
`SpectralModel`, it has `M` modes `i = 0, …, M-1` carrying rep `r = i + 1`, each
with spectral weight AND eigenvalue `coeffW w (i + 1)` (the weight is the single
end factor splitting `(coeffW w r)^{n+1} = coeffW w r · (coeffW w r)^n`). -/

/-- **The reconstructed transfer operator** as a finite multi-mode
`SpectralModel`: `M` excited modes `i = 0, …, M-1` (rep `r = i + 1`), with
spectral weight `w i = coeffW w (i+1)` and transfer eigenvalue
`lam i = coeffW w (i+1)`.  Nonnegativity of both is `coeffW_nonneg`.  Its abstract
`corr` is the connected single-rep chain sum `connSum` (`reconTransfer_corr_eq_connSum`). -/
def reconTransfer (w : Q') (hw : (0 : Q') ≤ w) (M : Nat) : SpectralModel where
  k := M
  w := fun i => coeffW w (i + 1)
  lam := fun i => coeffW w (i + 1)
  w_nonneg := fun i => coeffW_nonneg hw (i + 1)
  lam_nonneg := fun i => coeffW_nonneg hw (i + 1)

/-! ## 2. The reconstructed operator's `corr` is the connected chain sum

`corr (reconTransfer w hw M) n = Σ_{i<M} coeffW w (i+1) · (coeffW w (i+1))^n`,
and `connSum w M n = Σ_{i<M} connChain w (1+i) n = Σ_{i<M} (coeffW w (1+i))^{n+1}`.
Termwise, `coeffW w (i+1) · (coeffW w (i+1))^n = (coeffW w (i+1))^{n+1}` by
`Q'.pow_succ`, and `i + 1 = 1 + i`, so the two finite sums coincide up to `eqv`. -/

/-- The reconstructed transfer operator's `n`-th term equals the `i`-th connected
chain summand of `connSum`: `coeffW w (i+1) · (coeffW w (i+1))^n ≃ connChain w (1+i) n`
(the end-factor / eigenvalue split, `Q'.pow_succ`, and `i+1 = 1+i`). -/
theorem reconTransfer_term_eqv (w : Q') (i n : Nat) :
    (coeffW w (i + 1) * (coeffW w (i + 1)) ^ n).eqv (connChain w (1 + i) n) := by
  -- coeffW w (i+1) · (coeffW w (i+1))^n = (coeffW w (i+1))^{n+1} = connChain w (i+1) n
  have hidx : (i + 1 : Nat) = 1 + i := by omega
  unfold connChain
  rw [hidx]
  -- goal: (coeffW w (1+i) * (coeffW w (1+i))^n).eqv ((coeffW w (1+i))^(n+1))
  rw [Q'.pow_succ]
  exact Q'.eqv_refl _

/-- **`reconTransfer_corr_eq_connSum` (PROVED).**  The reconstructed transfer
operator's abstract two-point function is exactly the connected single-rep chain
sum:

    corr (reconTransfer w hw M) n  ≃  connSum w M n.

A `finSum` termwise congruence (`reconTransfer_term_eqv`): the diagonal
Källén–Lehmann sum `Σ_{i<M} w_i·λ_i^n` of the reconstructed operator coincides
with the collapsed connected correlator `Σ_{r=1}^{M} (coeffW w r)^{n+1}`. -/
theorem reconTransfer_corr_eq_connSum (w : Q') (hw : (0 : Q') ≤ w) (M n : Nat) :
    (corr (reconTransfer w hw M) n).eqv (connSum w M n) := by
  -- corr = Σ_{i<M} (coeffW w (i+1)) · (coeffW w (i+1))^n ; connSum = Σ_{i<M} connChain w (1+i) n
  show (finSum (fun i => coeffW w (i + 1) * (coeffW w (i + 1)) ^ n) M).eqv
      (finSum (fun k => connChain w (1 + k) n) M)
  exact finSum_eqv_of_termwise _ _ (fun i => reconTransfer_term_eqv w i n) M

/-! ## 3. THE CLOSURE — inhabiting `WilsonGMatchesAbstract` via the transfer matrix

`wilsonG_collapse w M n : (wilsonG w (M+1) n).eqv (connSum w M n)` is the proved
single-rep collapse.  Composing it (`eqv_trans`) with the reconstructed-operator
identity `reconTransfer_corr_eq_connSum` (`connSum ≃ corr (reconTransfer …)`, via
`eqv_symm`) gives

    wilsonG w (M+1) n  ≃  corr (reconTransfer w hw M) n,

which is EXACTLY the `matchesAbs` field of `WilsonGMatchesAbstract` with
`absCorr M n := corr (reconTransfer w hw M) n`.  This GENUINELY inhabits the named
wall — `matchesAbs` is the proved `wilsonG_collapse` plus a real `finSum`
congruence, NOT `eqv_refl`. -/

/-- The genuine `matchesAbs` proof: `wilsonG w (M+1) n ≃ corr (reconTransfer w hw M) n`,
the proved single-rep collapse `wilsonG_collapse` composed with the
reconstructed-operator identity `reconTransfer_corr_eq_connSum`. -/
theorem wilsonG_eqv_reconTransfer_corr (w : Q') (hw : (0 : Q') ≤ w) (M n : Nat) :
    (wilsonG w (M + 1) n).eqv (corr (reconTransfer w hw M) n) :=
  Q'.eqv_trans _ _ _
    (wilsonG_collapse w M n)
    (Q'.eqv_symm (reconTransfer_corr_eq_connSum w hw M n))

/-- **`wilsonGMatchesAbstract_transfer` — THE Wall-2a CLOSURE (PROVED).**

A GENUINE inhabitant of `WilsonConnCorr.WilsonGMatchesAbstract w` via the
transfer-matrix route: the abstract correlator family is the diagonal
Källén–Lehmann `corr` of the reconstructed single-edge transfer operator
`reconTransfer w hw M`, and the `matchesAbs` identity is the PROVED single-rep
collapse `wilsonG_collapse` composed with the reconstructed-operator identity
`reconTransfer_corr_eq_connSum`.

This INHABITS the previously-uninhabited named wall GENUINELY — `matchesAbs` is
derived content (`wilsonG w (M+1) n ≃ connSum w M n ≃ corr (reconTransfer …) n`),
NOT `eqv_refl` (contrast `WilsonCorrelator.genuineRealCorrelatorLink`, whose
`matches_abstract` is reflexivity because its correlator is DEFINED as the
abstract `corr`).  It de-fakes `WilsonGMatchesAbstract` for the SINGLE-LINE
connecting chain; the FULL multi-plaquette / loopy correlator stays the separate
named wall. -/
def wilsonGMatchesAbstract_transfer (w : Q') (hw : (0 : Q') ≤ w) :
    WilsonConnCorr.WilsonGMatchesAbstract w where
  absCorr := fun M n => corr (reconTransfer w hw M) n
  matchesAbs := fun M n => wilsonG_eqv_reconTransfer_corr w hw M n

/-! ## 4. Documentation: PROVED vs NAMED-open (AGENTS.md Rule 6)

PROVED (genuine, axiom-clean — Wall-2a closed for the single-line chain):

  * `reconTransfer` — the reconstructed single-edge transfer operator as a finite
    multi-mode `SpectralModel` (`M` excited modes, weight = eigenvalue =
    `coeffW w (i+1)`), diagonal in the SU(2) characters;
  * `reconTransfer_term_eqv`, `reconTransfer_corr_eq_connSum` — the reconstructed
    operator's diagonal two-point function `corr (reconTransfer …) n` equals the
    connected single-rep chain sum `connSum w M n` (the `finSum` termwise
    end-factor / eigenvalue split);
  * `wilsonG_eqv_reconTransfer_corr` — `wilsonG w (M+1) n ≃ corr (reconTransfer …) n`,
    the proved `wilsonG_collapse` composed with the reconstructed-operator identity;
  * `wilsonGMatchesAbstract_transfer` — THE CLOSURE: a GENUINE inhabitant of
    `WilsonConnCorr.WilsonGMatchesAbstract w` (NOT `eqv_refl`), its `matchesAbs`
    the proved single-rep collapse plus the real `finSum` congruence.

NAMED-open (NOT addressed here):

  * the FULL interacting multi-plaquette / loopy connected correlator (the general
    connected geometry, Mayer / Dobrushin-ratio induction) — a SEPARATE wall, not
    the single-line transfer-matrix identity closed here.

This module de-fakes `WilsonGMatchesAbstract` via the single-edge transfer-matrix
identity (the single-line geometry whose `wilsonG` collapses to one excited rep
along the chain).  It is NOT the full interacting correlator and NOT a 4D
Yang–Mills mass gap. -/

end YMGap.Continuum.TransferCorr

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TransferCorr.reconTransfer
#print axioms YMGap.Continuum.TransferCorr.reconTransfer_term_eqv
#print axioms YMGap.Continuum.TransferCorr.reconTransfer_corr_eq_connSum
#print axioms YMGap.Continuum.TransferCorr.wilsonG_eqv_reconTransfer_corr
#print axioms YMGap.Continuum.TransferCorr.wilsonGMatchesAbstract_transfer
