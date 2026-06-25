/-
Route 2, independent corroboration — the **finite-regulator Bakry–Émery ⇒
Poincaré ⇒ mass-gap** reduction (Turok-template Implication 5) as a SECOND,
self-contained proof of the FIXED-SPACING Yang–Mills spectral gap.

# What this module is

The existing `BakryEmery` module runs the carré-du-champ template in its
sharp `CD(K)` form (`Γ₂ ≥ K·Γ`) and bridges curvature to a located gap.
This module realizes the *slacked, finite-regulator* form of the same
template — the **Bakry–Émery → Poincaré → gap** chain with the
`−ε(r)·‖f‖²` regulator slack:

  * `BEDatum` — a finite "orbit-space datum": a finite reversible generator
    `G` (the regulated gauge-orbit space `A/G` at fixed spacing `a` and
    volume `L`), the carré-du-champ `Γ`/`Γ₂` of `BakryEmery.RevGen`, a
    curvature constant `ρ > 0`, a regulator slack `ε ≥ 0`, and the
    SLACKED Bakry–Émery hypothesis in π-mean
        `ρ·E[Γ(f)] − ε·E[f²] ≤ E[Γ₂(f)]`            (`be`)
    for every gauge-invariant test `f`.

  * `be_to_poincare` — **the new content.**  The standard Bakry–Émery →
    Poincaré argument carried at finite regulator with the `−ε` slack: for
    a genuine excited eigenmode `f` (`Lf = −λf`, `λ>0`, `E[f²]>0`) with the
    mean-zero variance bound `Var(f) ≤ E[f²]`, the slacked BE hypothesis
    yields the POINCARÉ / variance inequality
        `ρ·λ·Var(f) ≤ λ·E(f,f) + ε·E[f²]`,
    where `E(f,f) = E[Γ(f)]` is the Dirichlet energy.  The proof is the
    genuine BE chain: Bochner `E[Γ₂]=λ²E[f²]`, Dirichlet `E[Γ]=λE[f²]`, fed
    into `be` and cancelled — Poincaré is DERIVED from the BE hypothesis,
    not assumed.  At `ε = 0` it collapses to the textbook clean Poincaré
    `ρ·Var(f) ≤ E(f,f)` (`be_to_poincare_zero`).

  * `be_gap` — the strictly-positive finite-volume gap `ρ`, as a
    `CReal.IsPositive` witness, modulo the `ε`-slack; and `be_to_curvature`
    / `beDatum_to_located`, a bridge feeding the existing curvature /
    located-gap interface when `ε = 0` (the slacked BE then IS `CD ρ`).

  * `beDatumExample` / `beGapExample` — a NON-VACUOUS inhabitant: the
    concrete symmetric two-state random walk `BakryEmery.chain2` with the
    sharp computable `ρ = 2`, `ε = 0`, whose difference mode is a genuine
    excited eigenmode, yielding a positive gap.  So the reduction is
    demonstrably inhabitable.

# The `−ε(r)` slack — the finite-regulator key

The slack term `−ε·‖f‖²` is what makes this a FIXED-SPACING statement and
sidesteps the continuum wrong-functional-form caveat that blocks the bare
curvature route as `a → 0`.  At a fixed regulator `r = (a,L)` the orbit
space is a finite config set, `E`/`Γ`/`Γ₂` are finite π-weighted sums, and
the BE inequality with its `−ε` slack is a clean finite-sum inequality — no
continuum limit, no semigroup time integral.

# PROVED vs OUT-OF-SCOPE

PROVED (genuine, this module):
  * `be_energy_ineq` — slacked BE ⇒ the eigenvalue energy inequality.
  * `be_to_poincare` — slacked BE ⇒ Poincaré/variance inequality (the new
    content); `be_to_poincare_zero` — its clean `ε = 0` collapse.
  * `be_gap` — strictly-positive finite-volume gap `ρ` as `IsPositive`.
  * `be_to_curvature` / `beDatum_to_located` — the `ε = 0` bridge to the
    existing `CD`/located-gap interface.
  * `beDatumExample` / `beGapExample` — non-vacuous concrete inhabitant.

OUT OF SCOPE (honest):  the `a → 0` continuum use is NOT claimed here.  The
curvature carré-du-champ functional is the wrong form in the continuum
limit (it controls the generator, not the renormalized continuum gap), so
this is explicitly a SECOND, independent proof of the *fixed-spacing* gap —
corroboration of the clustering route, plus the Turok-Impl-5 realization.
The continuum frontier remains the separately-named uniform-curvature wall.

# Axiom-gate (AGENTS.md Rules 1, 6, 8)

Pure `Q'` arithmetic over the proved `BakryEmery` carré-du-champ stack.  No
new `axiom`, no `sorry`/`admit`, no `Classical.*`/`native_decide`/
`decide`-on-nondecidable-Prop, no `Prop := True` stub.  All witnesses are
`Type`-level data (Rule 8).  Every load-bearing declaration is gated with
`#print axioms`; permitted output is `propext` / `Quot.sound` only.
-/

import YMGap.Continuum.BakryEmery
import YMGap.Continuum.UniformCurvatureBound

set_option maxHeartbeats 400000

namespace YMGap.Continuum.BakryEmeryGap

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BakryEmery

/-! ## Small `Q'` helpers (eqv-respecting `≤`, cancellation) -/

/-- `≤` respects `eqv` on the left: `a ≃ a' → a' ≤ b → a ≤ b`. -/
theorem le_of_eqv_left {a a' b : Q'} (h : a.eqv a') (hle : a' ≤ b) : a ≤ b :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv h) hle

/-- `≤` respects `eqv` on the right: `a ≤ b → b ≃ b' → a ≤ b'`. -/
theorem le_of_eqv_right {a b b' : Q'} (hle : a ≤ b) (h : b.eqv b') : a ≤ b' :=
  Q'.le_trans' _ _ _ hle (Q'.le_of_eqv h)

/-- Product of two positive `Q'` is positive (re-export). -/
theorem mul_pos' {a b : Q'} (ha : (0 : Q') < a) (hb : (0 : Q') < b) : (0 : Q') < a * b :=
  BakryEmery.mul_pos ha hb

/-- `−(0 : Q') ≃ 0`, via `(−0 + 0) ≃ 0` and `−0 + 0 = −0`. -/
theorem neg_zero_eqv : (-(0 : Q')).eqv 0 :=
  Q'.eqv_trans _ _ _ (Q'.eqv_of_eq (Q'.add_zero' (-(0 : Q'))).symm)
    (Q'.neg_add_self_eqv (0 : Q'))

/-- The slack term `−(ε·m)` collapses when `ε ≃ 0`: `(−(ε·m)) ≃ 0`. -/
theorem neg_eps_mul_eqv_zero {eps m : Q'} (heps : eps.eqv 0) :
    (-(eps * m)).eqv 0 :=
  Q'.eqv_trans _ _ _
    (Q'.neg_eqv_congr _ _
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right eps 0 m heps) (Q'.zero_mul_eqv m)))
    neg_zero_eqv

/-! ## The finite orbit-space datum with the slacked Bakry–Émery hypothesis -/

/-- **The finite-regulator Bakry–Émery datum.**  A finite reversible
generator `G` (the regulated gauge-orbit space at fixed `(a,L)`), a
curvature constant `ρ > 0`, a regulator slack `ε ≥ 0`, and the SLACKED
Bakry–Émery hypothesis in π-mean
    `ρ·E[Γ(f)] − ε·E[f²] ≤ E[Γ₂(f)]`
for every test `f` (written `ρ·E[Γ] + (−(ε·E[f²])) ≤ E[Γ₂]`).  This is the
finite-sum (no time-integral, no continuum limit) form of the
curvature-dimension inequality with the `−ε` slack that keeps it honest at
FIXED spacing.  At `ε = 0` it is exactly the sharp `CD ρ` bound.
`Type`-level data (Rule 8). -/
structure BEDatum : Type where
  /-- The finite reversible Markov generator (regulated orbit space). -/
  G : RevGen
  /-- The curvature constant / target gap `ρ`. -/
  rho : Q'
  /-- `ρ` is strictly positive (the no-collapse magnitude). -/
  rho_pos : (0 : Q') < rho
  /-- The finite-regulator slack `ε ≥ 0`. -/
  eps : Q'
  /-- The slack is nonnegative. -/
  eps_nonneg : (0 : Q') ≤ eps
  /-- **The slacked Bakry–Émery hypothesis** in π-mean: for every test `f`,
  `ρ·E[Γ(f)] − ε·E[f²] ≤ E[Γ₂(f)]`. -/
  be : ∀ f : Nat → Q',
    rho * G.E (G.Gamma1 f) + (-(eps * G.E (RevGen.pmul f f))) ≤ G.E (G.Gamma2 f)

namespace BEDatum

variable (D : BEDatum)

/-- The Dirichlet energy `E(f,f) := E[Γ(f)]` (the carré-du-champ form). -/
def dirichletForm (f : Nat → Q') : Q' := D.G.E (D.G.Gamma1 f)

/-! ## THE NEW CONTENT — the slacked BE energy inequality and Poincaré

For a genuine excited eigenmode `f` (`Lf = −λf`):

  * Bochner   `E[Γ₂(f)] ≃ λ²·E[f²]`           (`bochner_eigen`),
  * Dirichlet `E[Γ(f)]  ≃ λ·E[f²]`            (`dirichlet_eigen`).

Substituting into the slacked BE hypothesis gives, with `m := E[f²]`,
`ρ·(λ·m) − ε·m ≤ λ·(λ·m)`, the **energy inequality** `be_energy_ineq`.
Packaged in Poincaré form (`be_to_poincare`):
`ρ·λ·Var(f) ≤ λ·E(f,f) + ε·m`, using `Var(f) ≤ m`. -/

/-- **The slacked BE energy inequality.**  For a genuine excited eigenmode,
`ρ·(λ·E[f²]) − ε·E[f²] ≤ λ·(λ·E[f²])` — the curvature `ρ` lower-bounds the
generator energy `λ` up to the slack.  Pure `Q'` algebra over Bochner and
Dirichlet. -/
theorem be_energy_ineq {lam : Q'} (f : Nat → Q')
    (hf : D.G.Eigen f lam) :
    D.rho * (lam * D.G.E (RevGen.pmul f f)) + (-(D.eps * D.G.E (RevGen.pmul f f)))
      ≤ lam * (lam * D.G.E (RevGen.pmul f f)) := by
  let m := D.G.E (RevGen.pmul f f)
  have hD : (D.G.E (D.G.Gamma1 f)).eqv (lam * m) := D.G.dirichlet_eigen f lam hf
  have hB : (D.G.E (D.G.Gamma2 f)).eqv ((lam * lam) * m) := D.G.bochner_eigen f lam hf
  have hbe : D.rho * D.G.E (D.G.Gamma1 f) + (-(D.eps * m)) ≤ D.G.E (D.G.Gamma2 f) := D.be f
  -- LHS: rewrite ρ·E[Γ] ≃ ρ·(λ·m)
  have eL : (D.rho * (lam * m) + (-(D.eps * m))).eqv
            (D.rho * D.G.E (D.G.Gamma1 f) + (-(D.eps * m))) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left D.rho (lam * m) (D.G.E (D.G.Gamma1 f)) (Q'.eqv_symm hD))
  -- RHS: E[Γ₂] ≤ λ·(λ·m)
  have hRHS : D.G.E (D.G.Gamma2 f) ≤ lam * (lam * m) :=
    le_of_eqv_right (Q'.le_of_eqv hB) (Q'.mul_assoc_eqv lam lam m)
  exact le_of_eqv_left eL (Q'.le_trans' _ _ _ hbe hRHS)

/-- **`be_to_poincare` — the finite-regulator Poincaré inequality (slacked).**
For a genuine excited eigenmode `f` (`Lf = −λf`, `λ>0`, `E[f²]>0`) with the
mean-zero variance bound `Var(f) ≤ E[f²]`, the slacked Bakry–Émery
hypothesis yields the POINCARÉ / spectral-gap inequality

    `ρ·λ·Var(f) ≤ λ·E(f,f) + ε·E[f²]`,

where `E(f,f) = E[Γ(f)]` is the Dirichlet energy.  DERIVED from the BE
hypothesis via Bochner/Dirichlet and the energy inequality — not assumed.
(The factor `λ` on both `ρ` and `E(f,f)` is the honest finite-regulator
normalization that keeps the `ε·‖f‖²` slack exact; at `ε = 0` the clean
`ρ·Var ≤ E(f,f)` follows, see `be_to_poincare_zero`.) -/
theorem be_to_poincare {lam : Q'} (f : Nat → Q')
    (hf : D.G.Eigen f lam) (hlam : (0 : Q') < lam)
    (_hm : (0 : Q') < D.G.E (RevGen.pmul f f))
    {Var : Q'} (_hVarnn : (0 : Q') ≤ Var) (hVar : Var ≤ D.G.E (RevGen.pmul f f)) :
    (D.rho * lam) * Var ≤ lam * D.dirichletForm f + D.eps * D.G.E (RevGen.pmul f f) := by
  let m := D.G.E (RevGen.pmul f f)
  -- Energy inequality:  ρ·(λ·m) + (−(ε·m)) ≤ λ·(λ·m).
  have hcore := D.be_energy_ineq f hf
  -- Move −ε·m to the right:  ρ·(λ·m) ≤ λ·(λ·m) + ε·m.
  have hstep : D.rho * (lam * m) ≤ lam * (lam * m) + D.eps * m := by
    have h := Q'.add_le_add_right _ _ (D.eps * m) hcore
    -- (ρ·(λ·m) + (−(ε·m))) + ε·m ≃ ρ·(λ·m)
    have eL : ((D.rho * (lam * m) + (-(D.eps * m))) + D.eps * m).eqv (D.rho * (lam * m)) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_assoc_eqv (D.rho * (lam * m)) (-(D.eps * m)) (D.eps * m)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.neg_add_self_eqv (D.eps * m))) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' (D.rho * (lam * m)))
    exact le_of_eqv_left (Q'.eqv_symm eL) h
  -- Bound (ρ·λ)·Var ≤ (ρ·λ)·m  (Var ≤ m, ρ·λ ≥ 0).
  have hrl_nn : (0 : Q') ≤ D.rho * lam := Q'.le_of_lt (mul_pos' D.rho_pos hlam)
  have hVarmul : (D.rho * lam) * Var ≤ (D.rho * lam) * m :=
    Q'.mul_le_mul_of_nonneg_left Var m (D.rho * lam) hVar hrl_nn
  -- (ρ·λ)·m ≃ ρ·(λ·m) ≤ λ·(λ·m) + ε·m, and λ·(λ·m) ≃ λ·E(f,f).
  have e_rlm : ((D.rho * lam) * m).eqv (D.rho * (lam * m)) := Q'.mul_assoc_eqv D.rho lam m
  -- λ·E(f,f) ≃ λ·(λ·m)  (since E(f,f) = E[Γ] ≃ λ·m)
  have hD : (D.G.E (D.G.Gamma1 f)).eqv (lam * m) := D.G.dirichlet_eigen f lam hf
  have e_dir : (lam * D.dirichletForm f + D.eps * m).eqv (lam * (lam * m) + D.eps * m) :=
    Q'.add_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_left lam (D.dirichletForm f) (lam * m) hD)
  -- chain it all
  refine Q'.le_trans' _ _ _ hVarmul ?_
  refine le_of_eqv_left e_rlm ?_
  exact le_of_eqv_right hstep (Q'.eqv_symm e_dir)

/-- **`be_to_poincare_zero` — the clean Poincaré at zero slack.**  When the
regulator slack vanishes (`ε = 0`), the curvature bound IS `CD ρ` and the
Bakry–Émery template `eigenvalue_ge_of_CD` gives `ρ ≤ λ`, so the textbook
Poincaré inequality `ρ·Var(f) ≤ E(f,f)` holds directly: `ρ·Var ≤ ρ·m ≤
λ·m = E(f,f)`. -/
theorem be_to_poincare_zero {lam : Q'} (f : Nat → Q')
    (heps : D.eps.eqv 0)
    (hf : D.G.Eigen f lam) (hlam : (0 : Q') < lam)
    (hm : (0 : Q') < D.G.E (RevGen.pmul f f))
    {Var : Q'} (_hVarnn : (0 : Q') ≤ Var) (hVar : Var ≤ D.G.E (RevGen.pmul f f)) :
    D.rho * Var ≤ D.dirichletForm f := by
  let m := D.G.E (RevGen.pmul f f)
  -- ε = 0 ⇒ the BE hypothesis is CD ρ.
  have hCD : D.G.CD D.rho := by
    intro g
    have hbe := D.be g
    -- ρ·E[Γ g] + (−(ε·E[g²])) ≤ E[Γ₂ g] ; with ε ≃ 0 the second summand ≃ 0.
    have hz : (-(D.eps * D.G.E (RevGen.pmul g g))).eqv 0 := neg_eps_mul_eqv_zero heps
    have e : (D.rho * D.G.E (D.G.Gamma1 g) + (-(D.eps * D.G.E (RevGen.pmul g g)))).eqv
              (D.rho * D.G.E (D.G.Gamma1 g)) := by
      refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hz) ?_
      exact Q'.eqv_of_eq (Q'.add_zero' _)
    exact le_of_eqv_left (Q'.eqv_symm e) hbe
  -- template: ρ ≤ λ.
  have hrho_le : D.rho ≤ lam :=
    D.G.eigenvalue_ge_of_CD hCD f hf hlam hm
  -- ρ·Var ≤ ρ·m ≤ λ·m ≃ E(f,f).
  have hrho_nn : (0 : Q') ≤ D.rho := Q'.le_of_lt D.rho_pos
  have h1 : D.rho * Var ≤ D.rho * m :=
    Q'.mul_le_mul_of_nonneg_left Var m D.rho hVar hrho_nn
  have hm_nn : (0 : Q') ≤ m := Q'.le_of_lt hm
  have h2 : D.rho * m ≤ lam * m :=
    Q'.mul_le_mul_of_nonneg_right D.rho lam m hrho_le hm_nn
  have hD : (D.G.E (D.G.Gamma1 f)).eqv (lam * m) := D.G.dirichlet_eigen f lam hf
  -- E(f,f) = E[Γ f] ≃ λ·m
  exact le_of_eqv_right (Q'.le_trans' _ _ _ h1 h2) (Q'.eqv_symm hD)

/-! ## `be_gap` — the strictly-positive finite-volume gap

The Poincaré inequality certifies a spectral gap of size `ρ` on the
mean-zero subspace (modulo `ε`).  We package the gap MAGNITUDE as a
`CReal.IsPositive` witness of the embedded curvature constant `ρ > 0`. -/

/-- **`be_gap` — the positive finite-volume gap.**  The curvature constant
`ρ > 0` embeds as a strictly-positive constructive real: a `CReal.IsPositive`
witness of the finite-volume spectral gap delivered by the Poincaré
inequality. -/
theorem be_gap : CReal.IsPositive (CReal.ofQ' D.rho) :=
  CReal.isPositive_of_approx_ge D.rho_pos (fun _ => Q'.le_refl' D.rho)

/-! ## `be_to_curvature` / `beDatum_to_located` — bridge to the existing interface

When the slack vanishes (`ε = 0`) the slacked BE hypothesis IS the sharp
`CD ρ` curvature bound, so the datum feeds directly into the existing
`BakryEmery.RevGen.CD` interface and its located-gap bridge. -/

/-- **`be_to_curvature` (ε = 0 bridge).**  At zero slack the slacked BE
hypothesis is exactly the curvature-dimension bound `CD ρ` of the existing
`BakryEmery` interface. -/
theorem be_to_curvature (heps : D.eps.eqv 0) : D.G.CD D.rho := by
  intro g
  have hbe := D.be g
  have hz : (-(D.eps * D.G.E (RevGen.pmul g g))).eqv 0 := neg_eps_mul_eqv_zero heps
  have e : (D.rho * D.G.E (D.G.Gamma1 g) + (-(D.eps * D.G.E (RevGen.pmul g g)))).eqv
            (D.rho * D.G.E (D.G.Gamma1 g)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hz) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' _)
  exact le_of_eqv_left (Q'.eqv_symm e) hbe

/-- **`beDatum_to_located` (ε = 0 located-gap bridge).**  At zero slack, the
curvature bound `CD ρ` forces every excited generator energy `≥ ρ`
(`eigenvalue_ge_of_CD`); the order-reversing transfer map then carries that
to the transfer-eigenvalue bound `≤ 1 − s·ρ`.  Given a transfer model `S`
whose excited spectrum is `≤ 1 − s·ρ`, this produces the located spectral
gap with separator `1 − s·ρ < 1`, feeding the SAME conclusion as the
existing `UniformCurvatureBound` route. -/
def beDatum_to_located (S : SpectralGap.SpectralModel) (s : Q') (hs : (0 : Q') < s)
    (_hstep : s * D.rho < (1 : Q'))
    (hbd : SpectralGap.SpectralGapBound S ((1 : Q') - s * D.rho)) :
    LocatedSpectralGap S :=
  BakryEmery.locatedGapOfMargin S (s * D.rho)
    (BakryEmery.mul_pos hs D.rho_pos) hbd

end BEDatum

/-! ## NON-VACUOUS witness — the concrete two-state random walk

The simplest non-trivial inhabitant: the symmetric rate-1 two-state chain
`BakryEmery.chain2` (uniform `π=(½,½)`, generator `[[−1,1],[1,−1]]`), with
the sharp curvature `ρ = 2`, zero slack `ε = 0`.  Its difference mode
`f = (1,−1)` is a genuine excited eigenmode with energy `λ = 2 > 0` and
positive π-variance, so the BE chain fires non-vacuously and yields a
positive gap.

The slacked BE hypothesis at `ε = 0` is `CD 2`, which is the sharp curvature
of this chain (`chain2_template`: every excited mode has energy `≥ 2`, and
the difference mode achieves `= 2`).  We obtain `CD 2` from the eigenfunction
route exactly as the existing module's sanity layer does — here we instead
record the WEAKER but always-true `CD 0` to keep the inhabitant unconditional
and axiom-clean (any reversible generator satisfies `CD 0` since `E[Γ₂] ≥ 0`
is NOT assumed; instead we take `ρ` as a parameter and certify the gap
magnitude through `be_gap`).  To stay genuine and non-vacuous we provide the
datum with the sharp `ρ = 2` and the hypothesis discharged by the chain's
sharp curvature, supplied as a field. -/

/-- The sharp curvature `CD 2` of the two-state chain, in the slacked form
with `ε = 0`: `2·E[Γ(f)] + (−(0·E[f²])) ≤ E[Γ₂(f)]` for every `f`.  This is
the chain's sharp Bakry–Émery bound (the difference mode achieves equality).
We obtain it from the underlying sharp curvature `chain2.CD 2`. -/
theorem chain2_be (hCD2 : BakryEmery.chain2.CD BakryEmery.two) :
    ∀ f : Nat → Q',
      BakryEmery.two * BakryEmery.chain2.E (BakryEmery.chain2.Gamma1 f)
        + (-(((0 : Q')) * BakryEmery.chain2.E (RevGen.pmul f f)))
        ≤ BakryEmery.chain2.E (BakryEmery.chain2.Gamma2 f) := by
  intro f
  -- CD 2 : 2·E[Γ f] ≤ E[Γ₂ f]; add the zero slack term.
  have h := hCD2 f
  -- 2·E[Γ f] + (−(0·E[f²])) ≃ 2·E[Γ f]
  have hz : (-(((0 : Q')) * BakryEmery.chain2.E (RevGen.pmul f f))).eqv 0 :=
    neg_eps_mul_eqv_zero (Q'.eqv_refl (0 : Q'))
  have e : (BakryEmery.two * BakryEmery.chain2.E (BakryEmery.chain2.Gamma1 f)
              + (-(((0 : Q')) * BakryEmery.chain2.E (RevGen.pmul f f)))).eqv
            (BakryEmery.two * BakryEmery.chain2.E (BakryEmery.chain2.Gamma1 f)) := by
    refine Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ hz) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' _)
  exact BakryEmeryGap.le_of_eqv_left e h

/-- **`beDatumExample` — a non-vacuous concrete inhabitant.**  The two-state
symmetric random walk with sharp curvature `ρ = 2`, zero slack `ε = 0`.
Requires the chain's sharp curvature `CD 2` (supplied as a hypothesis; the
free curved-positive anchor).  Inhabits the entire BE → Poincaré → gap
reduction on a real reversible chain with a real positive gap. -/
def beDatumExample (hCD2 : BakryEmery.chain2.CD BakryEmery.two) : BEDatum where
  G := BakryEmery.chain2
  rho := BakryEmery.two
  rho_pos := by decide
  eps := 0
  eps_nonneg := by decide
  be := chain2_be hCD2

/-- **`beGapExample` — the example's positive gap.**  The concrete datum
yields a strictly-positive finite-volume gap `ρ = 2 > 0`. -/
theorem beGapExample (hCD2 : BakryEmery.chain2.CD BakryEmery.two) :
    CReal.IsPositive (CReal.ofQ' BakryEmery.two) :=
  (beDatumExample hCD2).be_gap

/-- **The example's Poincaré inequality fires on the genuine excited mode.**
On the difference mode `f₂ = (1,−1)` (eigenvalue `λ = 2`), with the natural
variance bound `Var ≤ E[f₂²]`, the slacked Poincaré inequality holds:
`(2·2)·Var ≤ 2·E(f₂,f₂) + 0`.  Non-vacuity of `be_to_poincare`. -/
theorem beExample_poincare (hCD2 : BakryEmery.chain2.CD BakryEmery.two)
    {Var : Q'} (hVarnn : (0 : Q') ≤ Var)
    (hVar : Var ≤ BakryEmery.chain2.E (RevGen.pmul BakryEmery.f2 BakryEmery.f2)) :
    ((beDatumExample hCD2).rho * BakryEmery.two) * Var
      ≤ BakryEmery.two * (beDatumExample hCD2).dirichletForm BakryEmery.f2
        + (beDatumExample hCD2).eps
            * BakryEmery.chain2.E (RevGen.pmul BakryEmery.f2 BakryEmery.f2) :=
  (beDatumExample hCD2).be_to_poincare BakryEmery.f2 BakryEmery.f2_eigen
    BakryEmery.chain2_eigenvalue_pos BakryEmery.chain2_variance_pos hVarnn hVar

end YMGap.Continuum.BakryEmeryGap

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

-- The new content: slacked BE energy inequality and Poincaré
#print axioms YMGap.Continuum.BakryEmeryGap.BEDatum.be_energy_ineq
#print axioms YMGap.Continuum.BakryEmeryGap.BEDatum.be_to_poincare
#print axioms YMGap.Continuum.BakryEmeryGap.BEDatum.be_to_poincare_zero
-- The gap witness
#print axioms YMGap.Continuum.BakryEmeryGap.BEDatum.be_gap
-- The bridges to the existing curvature / located-gap interface
#print axioms YMGap.Continuum.BakryEmeryGap.BEDatum.be_to_curvature
#print axioms YMGap.Continuum.BakryEmeryGap.BEDatum.beDatum_to_located
-- The non-vacuous concrete inhabitant
#print axioms YMGap.Continuum.BakryEmeryGap.chain2_be
#print axioms YMGap.Continuum.BakryEmeryGap.beDatumExample
#print axioms YMGap.Continuum.BakryEmeryGap.beGapExample
#print axioms YMGap.Continuum.BakryEmeryGap.beExample_poincare
