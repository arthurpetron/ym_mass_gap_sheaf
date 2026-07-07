/-
YMGap.Continuum.SimonLiebCorrelation
====================================

**The Simon–Lieb / finite-volume correlation-inequality route to the
spacing-uniform correlation decay `UniformPhysicalCorrelationDecay` — does the
crossover correlation structure construct the uniform mass gap, or is it the
9th confirmation of `singleStep` (in correlation form)?**

# Why this module exists (read first)

The primary open continuum input is `UniformCorrelationDecay.UniformPhysicalCorrelationDecay`:
the connected correlator `⟨O(x)O(0)⟩ ≤ A·e^{−m|x|} + ε` with `m > 0` UNIFORM in the
lattice spacing `a`.  The FIXED-spacing decay is genuinely PROVED
(`WilsonConnCorr.wilsonG_decay`, rate `ρ = 2w³ < 1` at strong coupling).  The
`a → 0` UNIFORMITY of the rate is the residual.

This module tries the classic constructive method for a finite correlation length:
the **Simon–Lieb inequality**.  For a two-point function with a subadditive /
submultiplicative structure and a single-step correlation `ρ < 1`, the correlator
decays geometrically and the correlation length `ξ = 1/m` is finite with `m > 0`.

# What is PROVED here (genuine new content — the Simon–Lieb subadditivity)

  * `connChain_succ` — the per-link factorization `connChain w r (n+1) ≃ coeffW w r ·
    connChain w r n` (one extra plaquette = one extra character factor).
  * `connChain_simonLieb_step` — the TERMWISE Simon–Lieb contraction: at strong
    coupling `0 ≤ w ≤ 1/2`, each single-rep chain term contracts by the single-step
    correlation `ρ = coeffW w 1`: `connChain w (1+k) (n+1) ≤ ρ · connChain w (1+k) n`
    (excited base `≤` head, `coeffW_excited_le_one`).
  * `connSum_simonLieb_step` — **THE SIMON–LIEB SUBADDITIVITY** for the collapsed
    connected sum: `connSum w M (n+1) ≤ ρ · connSum w M n`.  The correlator contracts
    by the single-step correlation `ρ` at every step — the finite-volume subadditivity
    the Simon–Lieb criterion needs.
  * `wilsonG_simonLieb_step` — the same contraction for the REAL Wilson connected
    correlator (transported through `wilsonG_collapse`): `wilsonG w (M+1) (n+1) ≤ ρ ·
    wilsonG w (M+1) n`.
  * `simonLieb_criterion_holds_strong` — the Simon–Lieb CRITERION at strong coupling:
    the single-step correlation `ρ = 2w³ < 1` for `0 ≤ w ≤ 1/2` (`ρ ≤ 1/4`,
    `rho_lt_one`) — hence a finite correlation length and a fixed-spacing gap
    `m = −log ρ ≥ log 4 > 0`.

# THE CROSSOVER (task points 2–3) — the character Simon–Lieb FAILS at `w → 1`

  * `simonLieb_criterion_fails_at_one` — at the continuum end `w = 1` the single-step
    character correlation is `ρ = coeffW 1 1 = 2 ≥ 1`: the criterion FAILS.
  * `simonLieb_criterion_fails_weak` — already at `w = 9/10 > 2^{−1/3} ≈ 0.7937` the
    correlation is `ρ = 2·(9/10)³ = 1.458 ≥ 1`.

So the character single-step correlation crosses `1` at `w* = 2^{−1/3}`: `ρ < 1` on
the strong-coupling side (Simon–Lieb applies, gap), `ρ > 1` on the weak-coupling
(continuum) side (Simon–Lieb gives no gap — the strong-coupling / character expansion
has left its radius of convergence).  Along the AF trajectory `w_k → 1` (i.e. `a → 0`)
the character correlation `ρ_k = 2w_k³ → 2 > 1`, so the CHARACTER-basis Simon–Lieb is
NOT spacing-uniform — exactly the crossover every prior route hit.

# THE DECISIVE CHECK (task point 3–4) — the PHYSICAL Simon–Lieb uniformity IS `singleStep`

A spacing-uniform Simon–Lieb bound must live in the PHYSICAL (renormalized)
correlation, where the single-step correlation is measured over one PHYSICAL distance
(many lattice steps) and must stay `< 1` UNIFORMLY in `a`.  That uniform physical
single-step contraction is exactly the residual: `ContinuumSimonLieb :=
SingleStepDefectReduction.SingleStepDefectBound` (proved identity `rfl`, Rule 9.8),
UNINHABITED.  `massGap_floor_of_continuumSimonLieb` shows it WOULD give the full
continuum floor — but it is the open Clay core, not constructed.

# HONEST verdict

The Simon–Lieb / correlation-inequality method supplies a genuine new
FIXED-SPACING subadditivity (the single-step contraction `connSum(n+1) ≤ ρ·connSum(n)`
and the criterion `ρ = 2w³ < 1`), and pinpoints the crossover `w* = 2^{−1/3}` at
which the CHARACTER single-step correlation crosses `1`.  It does NOT construct the
spacing-uniform bound: the character Simon–Lieb fails at `w → 1` (`ρ → 2 > 1`), and
the spacing-uniform PHYSICAL Simon–Lieb is `singleStep`.  This is the NINTH
independent confirmation of the same irreducible core, in correlation-inequality form.
No guarded frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap
remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` / `Nat` composition over the proved `wilsonG` / `connSum` / `coeffW`
machinery and the `finSum` toolkit (`const_mul_finSum`, `finSum_le_finSum`).  No
`Classical.*`, no `native_decide`, no `sorry`, no custom axiom.  Every load-bearing
declaration is gated with `#print axioms` (permitted: `propext` / `Quot.sound`).
Type-level witnesses are `Type` data.  The one `noncomputable`
(`massGap_floor_of_continuumSimonLieb`) is a re-export of the upstream constructive
extraction `fullFloor_of_singleStep` behind a Σ projection.
-/

import YMGap.Continuum.WilsonConnCorr
import YMGap.Continuum.PlaquetteActivity
import YMGap.Continuum.CosPiEnclosure
import YMGap.Continuum.SingleStepDefectReduction
import YMGap.Continuum.UniformCorrelationDecay

namespace YMGap.Continuum.SimonLiebCorrelation

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.PlaquetteActivity
open YMGap.Continuum.WilsonConnCorr
open YMGap.Continuum.CosPiEnclosure

/-! ## 1. The per-link factorization of the single-rep chain

`connChain w r n = (coeffW w r)^{n+1}` is the connected chain of `n+1` plaquettes at
common rep `r`.  Adding one link multiplies by one more character factor:
`connChain w r (n+1) = coeffW w r · connChain w r n`.  This is the local structure
the Simon–Lieb inequality iterates. -/

/-- **The per-link factorization** `connChain w r (n+1) ≃ coeffW w r · connChain w r
n`.  One extra plaquette on the connecting chain = one extra character factor
`coeffW w r`.  (`(coeffW w r)^{n+2} = coeffW w r · (coeffW w r)^{n+1}`.) -/
theorem connChain_succ (w : Q') (r : Nat) (n : Nat) :
    (connChain w r (n + 1)).eqv (coeffW w r * connChain w r n) := by
  show ((coeffW w r) ^ (n + 1 + 1)).eqv (coeffW w r * (coeffW w r) ^ (n + 1))
  rw [Q'.pow_succ]
  exact Q'.eqv_refl _

/-! ## 2. The termwise Simon–Lieb contraction

At strong coupling `0 ≤ w ≤ 1/2` every excited base `coeffW w (1+k)` is `≤ coeffW w 1
= ρ` (`coeffW_excited_le_one`), so each single-rep chain term contracts by `ρ` per
step:  `connChain w (1+k) (n+1) ≤ ρ · connChain w (1+k) n`.  `ρ = coeffW w 1 = 2w³` is
the single-step correlation. -/

/-- **The TERMWISE Simon–Lieb contraction.**  At strong coupling `0 ≤ w ≤ 1/2`, each
collapsed single-rep chain term contracts by the single-step correlation `ρ =
rho w = coeffW w 1`:
    `connChain w (1+k) (n+1) ≤ rho w · connChain w (1+k) n`.
(Factorize one link, bound the excited base by the head `coeffW_excited_le_one`.) -/
theorem connChain_simonLieb_step {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (k n : Nat) :
    connChain w (1 + k) (n + 1) ≤ rho w * connChain w (1 + k) n := by
  have hsucc : (connChain w (1 + k) (n + 1)).eqv
      (coeffW w (1 + k) * connChain w (1 + k) n) := connChain_succ w (1 + k) n
  have hcoeff : coeffW w (1 + k) ≤ coeffW w 1 := coeffW_excited_le_one hw0 hw k
  have hnn : (0 : Q') ≤ connChain w (1 + k) n := connChain_nonneg hw0 (1 + k) n
  have hmul : coeffW w (1 + k) * connChain w (1 + k) n
      ≤ coeffW w 1 * connChain w (1 + k) n :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcoeff hnn
  -- rho w := coeffW w 1 (defeq), so `coeffW w 1 * connChain` matches the goal RHS.
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsucc) hmul

/-! ## 3. THE SIMON–LIEB SUBADDITIVITY — `connSum w M (n+1) ≤ ρ · connSum w M n`

Summing the termwise contraction over the excited reps `r = 1, …, M` and pulling the
constant `ρ` out of the finite sum gives the single-step subadditivity of the whole
collapsed connected correlator.  This is the finite-volume Simon–Lieb bound: the
correlator contracts by the single-step correlation `ρ` at every step. -/

/-- **THE SIMON–LIEB SUBADDITIVITY (single-step contraction).**  At strong coupling
`0 ≤ w ≤ 1/2` the collapsed connected sum contracts by the single-step correlation
`ρ = rho w = coeffW w 1 = 2w³`:
    `connSum w M (n+1) ≤ rho w · connSum w M n`.
Termwise contraction (`connChain_simonLieb_step`) summed and the constant pulled out
(`const_mul_finSum`).  Iterating gives geometric decay; the criterion `ρ < 1`
(strong coupling) yields a finite correlation length `ξ = 1/(−log ρ)`. -/
theorem connSum_simonLieb_step {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (M n : Nat) :
    connSum w M (n + 1) ≤ rho w * connSum w M n := by
  show finSum (fun k => connChain w (1 + k) (n + 1)) M
      ≤ rho w * finSum (fun k => connChain w (1 + k) n) M
  have hterm : ∀ k, connChain w (1 + k) (n + 1) ≤ rho w * connChain w (1 + k) n :=
    fun k => connChain_simonLieb_step hw0 hw k n
  have hle : finSum (fun k => connChain w (1 + k) (n + 1)) M
      ≤ finSum (fun k => rho w * connChain w (1 + k) n) M :=
    finSum_le_finSum _ _ hterm M
  have hpull : (finSum (fun k => rho w * connChain w (1 + k) n) M).eqv
      (rho w * finSum (fun k => connChain w (1 + k) n) M) :=
    Q'.eqv_symm (const_mul_finSum (fun k => connChain w (1 + k) n) (rho w) M)
  exact Q'.le_trans' _ _ _ hle (Q'.le_of_eqv hpull)

/-- **The Simon–Lieb contraction for the REAL Wilson connected correlator.**
Transporting `connSum_simonLieb_step` through the single-rep collapse
(`wilsonG_collapse`):
    `wilsonG w (M+1) (n+1) ≤ rho w · wilsonG w (M+1) n`.
The genuine correlator contracts by the single-step correlation `ρ` each step. -/
theorem wilsonG_simonLieb_step {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half)
    (M n : Nat) :
    wilsonG w (M + 1) (n + 1) ≤ rho w * wilsonG w (M + 1) n := by
  have h1 : wilsonG w (M + 1) (n + 1) ≤ connSum w M (n + 1) :=
    Q'.le_of_eqv (wilsonG_collapse w M (n + 1))
  have h2 : connSum w M (n + 1) ≤ rho w * connSum w M n :=
    connSum_simonLieb_step hw0 hw M n
  have h3 : (rho w * connSum w M n).eqv (rho w * wilsonG w (M + 1) n) :=
    Q'.mul_eqv_congr_left (rho w) _ _ (Q'.eqv_symm (wilsonG_collapse w M n))
  exact Q'.le_trans' _ _ _ h1 (Q'.le_trans' _ _ _ h2 (Q'.le_of_eqv h3))

/-! ## 4. The Simon–Lieb criterion `ρ < 1` and the crossover `w* = 2^{−1/3}`

The single-step correlation is `ρ = rho w = coeffW w 1 = 2w³`.  The Simon–Lieb finite
-volume criterion is `ρ < 1`, equivalently `w < w* = 2^{−1/3} ≈ 0.7937`.  It HOLDS on
the strong-coupling side and FAILS on the weak-coupling (continuum) side. -/

/-- **The single-step correlation** of the Simon–Lieb inequality: `ρ = rho w =
coeffW w 1 = 2w³`.  The Simon–Lieb criterion is `simonLiebCorrelation w < 1`. -/
def simonLiebCorrelation (w : Q') : Q' := rho w

/-- **The Simon–Lieb criterion HOLDS at strong coupling** `0 ≤ w ≤ 1/2`: the
single-step correlation `ρ = 2w³ < 1` (`ρ ≤ 1/4`).  Hence a finite correlation length
and a positive fixed-spacing gap `m = −log ρ ≥ log 4 > 0`. -/
theorem simonLieb_criterion_holds_strong {w : Q'} (hw0 : (0 : Q') ≤ w) (hw : w ≤ half) :
    simonLiebCorrelation w < (1 : Q') :=
  rho_lt_one hw0 hw

/-- The strong-coupling anchor `w = 1/2`: `ρ = 1/4 < 1` explicitly (`ρ ≤ 1/4`). -/
theorem simonLiebCorrelation_half_le : simonLiebCorrelation half ≤ Q'.mkPos 1 4 (by decide) :=
  rho_le_quarter (by decide) (Q'.le_refl' half)

/-- **The Simon–Lieb criterion FAILS at the continuum end** `w = 1`: the single-step
character correlation is `ρ = coeffW 1 1 = 2 ≥ 1` — the character / strong-coupling
expansion has left its radius of convergence `w* = 2^{−1/3}`, so the CHARACTER-basis
Simon–Lieb gives NO gap.  This is the crossover: `ρ` crosses `1` between `w = 1/2`
(`ρ = 1/4`) and `w = 1` (`ρ = 2`). -/
theorem simonLieb_criterion_fails_at_one : (1 : Q') ≤ simonLiebCorrelation (1 : Q') := by
  show (1 : Q') ≤ rho (1 : Q')
  show (1 : Q') ≤ coeffW (1 : Q') 1
  rw [coeffW_one_eq]
  decide

/-- **The criterion FAILS already past the crossover** `w = 9/10 > 2^{−1/3} ≈
0.7937`: `ρ = 2·(9/10)³ = 1458/1000 ≥ 1`.  Concrete evidence that the character
single-step correlation exceeds `1` on the weak-coupling side. -/
theorem simonLieb_criterion_fails_weak :
    (1 : Q') ≤ simonLiebCorrelation (Q'.mkPos 9 10 (by decide)) := by
  show (1 : Q') ≤ rho (Q'.mkPos 9 10 (by decide))
  show (1 : Q') ≤ coeffW (Q'.mkPos 9 10 (by decide)) 1
  rw [coeffW_one_eq]
  decide

/-! ## 5. THE DECISIVE CHECK — the spacing-uniform PHYSICAL Simon–Lieb IS `singleStep`

A spacing-uniform Simon–Lieb bound must measure the single-step correlation over one
PHYSICAL distance (many lattice steps as `a → 0`) and keep it `< 1` UNIFORMLY in `a`.
That uniform physical single-step contraction is exactly the open residual: it is
`SingleStepDefectReduction.SingleStepDefectBound` (the per-step true-margin RG
estimate `realδ_k ≤ δ_model_k`), the same core as the RG / OS / OPE / reflection
routes.  Carried as a def-alias — a PROVED identity (Rule 9.8), UNINHABITED. -/

/-- **`ContinuumSimonLieb` — the spacing-uniform physical Simon–Lieb contraction, =
`singleStep`.**  The physical (renormalized) single-step correlation stays `< 1`
uniformly in `a` iff the true dimensionless margin does not erode faster than the
transverse model per RG step — i.e. `SingleStepDefectBound`.  UNINHABITED (it IS the
open continuum core). -/
def ContinuumSimonLieb : Type := SingleStepDefectReduction.SingleStepDefectBound

/-- **`continuumSimonLieb_is_singleStep` — the 9th-confirmation identity (`rfl`).**
The spacing-uniform physical Simon–Lieb contraction IS `singleStep`, proved by
definitional equality (Rule 9.8), not prose. -/
theorem continuumSimonLieb_is_singleStep :
    ContinuumSimonLieb = SingleStepDefectReduction.SingleStepDefectBound := rfl

/-- **`massGap_floor_of_continuumSimonLieb` — the conditional producer.**  A physical
Simon–Lieb contraction (= `ContinuumSimonLieb` = `SingleStepDefectBound`) yields the
ENTIRE positive continuum floor for the true margin (`fullFloor_of_singleStep`): the
uniform single-step contraction `< 1` gives the spacing-uniform decay `m > 0`.  This
is the honest "Simon–Lieb WOULD construct the gap" — GIVEN the uninhabited uniform
physical contraction. -/
theorem massGap_floor_of_continuumSimonLieb (S : ContinuumSimonLieb) :
    (0 : Q') < (SingleStepDefectReduction.defectRecursion_of_singleStep S).prodFloor
      ∧ ∀ k : Nat,
        (SingleStepDefectReduction.defectRecursion_of_singleStep S).prodFloor
          ≤ S.trueMargin k :=
  SingleStepDefectReduction.fullFloor_of_singleStep S

/-! ## 6. Verdict bundle (informational — PROVED facts only) -/

/-- **`SimonLiebVerdict`** — an informational bundle of the PROVED facts of this
route.  It carries the Simon–Lieb subadditivity, the strong-coupling criterion, the
crossover failure at `w → 1`, and the `singleStep` identity.  It inhabits NONE of the
guarded frontier bundles. -/
structure SimonLiebVerdict : Type where
  /-- The Simon–Lieb single-step contraction for the real correlator (strong coupling). -/
  subadditivity : ∀ {w : Q'}, (0 : Q') ≤ w → w ≤ half → ∀ M n : Nat,
    wilsonG w (M + 1) (n + 1) ≤ rho w * wilsonG w (M + 1) n
  /-- The Simon–Lieb criterion `ρ < 1` holds at strong coupling (fixed-spacing gap). -/
  criterion_strong : ∀ {w : Q'}, (0 : Q') ≤ w → w ≤ half →
    simonLiebCorrelation w < (1 : Q')
  /-- The criterion FAILS at the continuum end `w = 1` (`ρ = 2 ≥ 1`): the crossover. -/
  crossover_fail : (1 : Q') ≤ simonLiebCorrelation (1 : Q')
  /-- The spacing-uniform physical Simon–Lieb contraction IS `singleStep`. -/
  uniform_is_singleStep :
    ContinuumSimonLieb = SingleStepDefectReduction.SingleStepDefectBound

/-- **`simon_lieb_verdict`** — the verdict, all fields discharged by the PROVED
theorems above.  No frontier bundle inhabited; `ContinuumSimonLieb` (= `singleStep`)
UNINHABITED. -/
def simon_lieb_verdict : SimonLiebVerdict where
  subadditivity := fun hw0 hw M n => wilsonG_simonLieb_step hw0 hw M n
  criterion_strong := fun hw0 hw => simonLieb_criterion_holds_strong hw0 hw
  crossover_fail := simonLieb_criterion_fails_at_one
  uniform_is_singleStep := continuumSimonLieb_is_singleStep

/-! ## 7. Documentation: PROVED vs OPEN (AGENTS.md Rule 6)

PROVED (GREEN, axiom-clean — the genuine new fixed-spacing Simon–Lieb content):

  * `connChain_succ` — per-link factorization of the single-rep chain;
  * `connChain_simonLieb_step` — the termwise single-step contraction by `ρ`;
  * `connSum_simonLieb_step` — **the Simon–Lieb subadditivity** `connSum(n+1) ≤
    ρ·connSum(n)`;
  * `wilsonG_simonLieb_step` — the same for the REAL Wilson connected correlator;
  * `simonLieb_criterion_holds_strong`, `simonLiebCorrelation_half_le` — the criterion
    `ρ = 2w³ < 1` at strong coupling (`ρ ≤ 1/4`) — a fixed-spacing gap;
  * `simonLieb_criterion_fails_at_one`, `simonLieb_criterion_fails_weak` — **the
    crossover**: the character single-step correlation `ρ` crosses `1` at
    `w* = 2^{−1/3}` and is `≥ 1` on the weak-coupling (continuum) side;
  * `continuumSimonLieb_is_singleStep`, `massGap_floor_of_continuumSimonLieb` — the
    reduction: the spacing-uniform PHYSICAL Simon–Lieb IS `singleStep` and WOULD give
    the full continuum floor.

OPEN (UNINHABITED — the same irreducible core, correlation-inequality form):

  * `ContinuumSimonLieb := SingleStepDefectReduction.SingleStepDefectBound` — the
    spacing-uniform physical single-step contraction `< 1` (uniform in `a`).  The
    character-basis Simon–Lieb fails at `w → 1` (`ρ → 2 > 1`, radius of convergence
    `w* = 2^{−1/3}`); the physical-basis uniformity is `singleStep`.

The Simon–Lieb / correlation-inequality route is the NINTH independent confirmation
of the same core `singleStep` — a genuine new fixed-spacing subadditivity plus a
sharp crossover, but NOT the spacing-uniform construction.  It does NOT close 4D
Yang–Mills. -/

end YMGap.Continuum.SimonLiebCorrelation

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SimonLiebCorrelation.connChain_succ
#print axioms YMGap.Continuum.SimonLiebCorrelation.connChain_simonLieb_step
#print axioms YMGap.Continuum.SimonLiebCorrelation.connSum_simonLieb_step
#print axioms YMGap.Continuum.SimonLiebCorrelation.wilsonG_simonLieb_step
#print axioms YMGap.Continuum.SimonLiebCorrelation.simonLieb_criterion_holds_strong
#print axioms YMGap.Continuum.SimonLiebCorrelation.simonLiebCorrelation_half_le
#print axioms YMGap.Continuum.SimonLiebCorrelation.simonLieb_criterion_fails_at_one
#print axioms YMGap.Continuum.SimonLiebCorrelation.simonLieb_criterion_fails_weak
#print axioms YMGap.Continuum.SimonLiebCorrelation.continuumSimonLieb_is_singleStep
#print axioms YMGap.Continuum.SimonLiebCorrelation.massGap_floor_of_continuumSimonLieb
#print axioms YMGap.Continuum.SimonLiebCorrelation.simon_lieb_verdict
