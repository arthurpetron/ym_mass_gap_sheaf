/-
Track B / R1+R2 — THE TERMINAL RESUMMATION TEST: do (R1) the perturbative resummation and
(R2) the a→0 renormalization reduce to the PROVED KP cluster bound + the PROVED
field-space/AF renormalization, thereby CONSTRUCTING the interacting amplitude `z_n`?

# The obligation (read first)

`IsserlisGaussianBase` established that the interacting continuum weight
`z_n = Σ_k (1/k!)⟨(−S_int)^k χ⟩_conn` is DETERMINED term-by-term (Isserlis/Wick), and named the
two residuals:

  (R1)  the K→∞ perturbative RESUMMATION of the DETERMINED coefficients (asymptotic series,
        factorial coefficient growth, radius of convergence 0 — Dyson), and
  (R2)  the a→0 CONTINUUM covariance (renormalization of the propagator in each Wick
        contraction).

The proposed closure under test:
  (R1) reduces to the PROVED KP cluster bound `|z_n| ≤ (μg²)^n` (`KPFieldAmplitude.amplitude_le`,
       combinatorially proved via Penrose/Cayley/Euler) — "the cluster expansion IS the
       convergent resummation of the asymptotic perturbative series";
  (R2) reduces to the PROVED field-space/AF renormalization (`AFBetaStepCanonical`,
       `FieldSpaceCluster`) — "as a→0, g² → 0, so μg² → 0 and the KP bound improves".

# HEADLINE VERDICT (machine-checked, axiom-clean): the reduction FAILS at a precise, named seam.
# Neither (R1) nor (R2) closes; z_n is NOT fully constructed; the 4D Yang–Mills mass gap OPEN.

The KP bound and the AF/field-space renormalization are PROVED — but they are the WRONG-SIDE
half of each residual.  This module machine-checks WHY:

  * **(R1) — the resummation index gap.**  The Isserlis DETERMINATION gives the perturbative
    coefficients indexed by ORDER `k` (in `g²`); these grow FACTORIALLY (radius 0, Dyson).  The
    KP bound `|z_n| ≤ (μg²)^n` bounds the connected Ursell amplitude indexed by CLUSTER SIZE `n`;
    it is GEOMETRIC.  These are DIFFERENT expansions.  The KP bound is DRIVEN by the single-polymer
    activity `|z_1| ≤ g²` (`KPFieldAmplitude.SinglePolymerActivity`, UNINHABITED for the real
    activity) — i.e. it bounds the RESUMMED cluster amplitude GIVEN that the single-polymer
    activity is already a finite number `≤ g²`.  It does NOT itself resum the factorial series;
    it CONSUMES the resummation's output.  **Machine-checked here:** a factorially-growing
    determined-coefficient sequence (`dysonDiag k = (k+1)!`, modelling the Isserlis coefficients)
    admits NO genuine Cauchy-modulus resummation (`factorialSeries_no_genuineResummation`): the
    increments do not fall below `1/2`, so the partial sums are NOT Cauchy — a Borel/nonperturbative
    prescription is required, which the KP combinatorial scaffold does NOT supply.

  * **(R2) — the a→0 renormalization is conditional on the interacting continuum measure.**  The
    AF `g² → 0` (`AFBetaStepCanonical`, canonical toy trajectory) and the field-space activity
    `→ 0` (`FieldSpaceCluster`) are PROVED, and they control the KP cluster SUM.  But the a→0
    limit of the RESUMMED interacting `z_n`, as a renormalized continuum amplitude, is
    `ContinuumFieldMeasure.InteractingContinuumMeasure` — UNINHABITED — whose `z_n` is a FREE
    field (`InteractingMeasureReduction.interacting_zAmp_free_dodge`: `zAmp ≡ 0` inhabits the
    letter).  The full amplitude bound `interacting_amplitude_le` is a CONDITIONAL producer
    (open binder on the interacting measure).  Plugging `g² → 0` into the fixed-`a` bound does
    NOT construct the renormalized continuum covariance.

  * **z_n is NOT fully constructed.**  It is DETERMINED at finite order (Isserlis) and BOUNDED
    above by the PROVED KP scaffold, but its full value requires (R1) the resummation of the
    factorial series to the finite single-polymer activity `z_1 ≤ g²`
    (`SinglePolymerActivity`/`pertRep`, UNINHABITED) and (R2) the a→0 renormalized interacting
    measure (`InteractingContinuumMeasure`, UNINHABITED).  The KP bound and AF are the RIGHT
    (cluster→convergence, coupling→0) halves; the LEFT halves (factorial→finite `z_1`;
    fixed-a→renormalized continuum) are the OPEN residual.

# Cascade / STOP status (mandatory task condition)

No STOP condition tripped.  This module proves theorems ABOUT the resummation seam and re-exports
the CONDITIONAL amplitude producer.  It inhabits NONE of the 5 guarded Clay-frontier types
(`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`), and
produces NO unconditional inhabitant of `SinglePolymerActivity`, `InteractingContinuumMeasure`,
`GenuineResummation dysonDiag` (PROVED uninhabitable), or any node feeding
`FrontierDAG.trueMargin`.  The frontier guard stays at 5.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`, reusing PROVED `IsserlisGaussianBase.feynTrunc`/`feynTrunc_increment`,
`KPFieldAmplitude`, `ContinuumFieldMeasure`, `InteractingMeasureReduction`, `Q'.abs`/`le_abs_self`,
`Q'.invSucc`.  Every load-bearing declaration is `#print axioms`-gated to `propext`/`Quot.sound`
only (or empty — the factorial refutation core is kernel-`decide` at the leaf).  No `Classical.*`,
no `native_decide`, no `sorry`.  All witnesses `Type`-level.
-/
import YMGap.Continuum.IsserlisGaussianBase
import YMGap.Continuum.InteractingMeasureReduction
import YMGap.Constructive.AbsQ

namespace YMGap.Continuum.TerminalResummationTest

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.IsserlisGaussianBase
open YMGap.Continuum.KPFieldAmplitude
open YMGap.Continuum.ContinuumFieldMeasure
open YMGap.Continuum.InteractingMeasureReduction
open YMGap.Continuum.FieldSpaceCluster
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF

/-! ## 1. A GENUINE resummation modulus (shrinking Cauchy modulus on the determined terms).

`IsserlisGaussianBase.PerturbativeResummation` carries a free tolerance schedule `tol m` and
requires the increment `≤ tol m` past `resumOrder m`.  As its own docstring flags (Rule 9(6)),
that is vacuously fillable by a large constant `tol`.  The HONEST, non-fakeable form of "the
determined series resums" is a genuine Cauchy modulus: the term MAGNITUDES fall below `1/(m+1)`
(a schedule that FORCES the terms to `0`, hence the partial sums to be Cauchy).  Since the
partial-sum increment IS the coefficient (`feynTrunc_increment`), this is a bound on the
determined coefficients themselves. -/

/-- **`GenuineResummation diag` — the honest, shrinking Cauchy modulus for the determined series.**
`order m` is the index past which every term magnitude is `≤ 1/(m+1)`.  Forcing the terms to `0`
(and hence the partial sums to converge) is exactly what an ASYMPTOTIC (radius-0) series cannot
do — this is the genuine (non-vacuous) content of (R1). -/
structure GenuineResummation (diag : Nat → Q') : Type where
  /-- The modulus: past `order m`, term magnitudes are `≤ 1/(m+1)`. -/
  order : Nat → Nat
  /-- **THE GENUINE CAUCHY MODULUS**: `|diag K| ≤ 1/(m+1)` for `K ≥ order m`.  Forces the
  determined coefficients to `0`, i.e. the perturbative series is (absolutely) convergent. -/
  smallTail : ∀ m K, order m ≤ K → Q'.abs (diag K) ≤ Q'.invSucc m

/-- **The genuine modulus IS a bound on the partial-sum increment** — faithfulness to
`PerturbativeResummation`.  Since `feynTrunc diag (K+1) = feynTrunc diag K + diag K`
(`feynTrunc_increment`), the coefficient `diag K` is exactly the order-`K` increment of the
perturbative partial sums; bounding `|diag K|` bounds that increment. -/
theorem increment_eq_coeff (diag : Nat → Q') (K : Nat) :
    feynTrunc diag (K + 1) = feynTrunc diag K + diag K :=
  feynTrunc_increment diag K

/-! ## 2. The physical (Dyson) factorial coefficient model and the resummation refutation. -/

/-- Local factorial (`Lean` core here has no `Nat.factorial`). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => by decide
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

/-- **The Dyson factorial coefficient model** `dysonDiag k = (k+1)!`.  This models the growth of
the DETERMINED Isserlis/Feynman coefficients of `z_n`: the perturbative QFT series has factorially
growing diagram coefficients (`verify_isserlis.py`: `|a_{k+1}/a_k| → ∞`, radius 0 — Dyson).  The
key structural feature is only that the terms do NOT shrink to `0` (they grow), which is all the
refutation below needs. -/
def dysonDiag (k : Nat) : Q' := Q'.ofNat (fact (k + 1))

/-- **Every Dyson term is `≥ 1`** (indeed `≥ (k+1)!`).  `(k+1)! ≥ 1`, and `ofNat` is monotone. -/
theorem dysonDiag_ge_one (k : Nat) : (1 : Q') ≤ dysonDiag k := by
  have h1 : (1 : Nat) ≤ fact (k + 1) := fact_pos (k + 1)
  have h2 : Q'.ofNat 1 ≤ Q'.ofNat (fact (k + 1)) :=
    TreeGraphBoundProgress.ofNat_le_ofNat h1
  exact Q'.le_trans' _ _ _ (by decide : (1 : Q') ≤ Q'.ofNat 1) h2

/-- **THE RESUMMATION REFUTATION (R1 is a GENUINE gap).**  The Dyson factorial coefficient
sequence admits NO genuine (shrinking Cauchy-modulus) resummation: `GenuineResummation dysonDiag`
is UNINHABITABLE.  Proof: a `GenuineResummation` would force `|dysonDiag K| ≤ 1/2` for all large
`K` (taking `m = 1`, `1/(m+1) = 1/2`); but every Dyson term is `≥ 1 > 1/2`.  So the DETERMINED
(factorially growing) coefficients do NOT resum by any Cauchy modulus — the partial sums are not
Cauchy, and a Borel/nonperturbative prescription is required.  The PROVED KP cluster bound does
NOT supply this: it bounds the cluster amplitude `z_n` (index `n`, geometric) GIVEN the finite
single-polymer activity `z_1 ≤ g²`; it does not resum the order-`k` factorial series that
determines `z_1` in the first place.  Kernel-`decide` at the leaf; AXIOM-clean. -/
theorem factorialSeries_no_genuineResummation :
    GenuineResummation dysonDiag → False := by
  intro R
  -- at m = 1: |dysonDiag (order 1)| ≤ invSucc 1 = 1/2
  have hsmall : Q'.abs (dysonDiag (R.order 1)) ≤ Q'.invSucc 1 :=
    R.smallTail 1 (R.order 1) (Nat.le_refl _)
  -- dysonDiag (order 1) ≤ |dysonDiag (order 1)| ≤ 1/2
  have hle : dysonDiag (R.order 1) ≤ Q'.invSucc 1 :=
    Q'.le_trans' _ _ _ (Q'.le_abs_self _) hsmall
  -- but dysonDiag (order 1) ≥ 1
  have hge : (1 : Q') ≤ dysonDiag (R.order 1) := dysonDiag_ge_one (R.order 1)
  -- so 1 ≤ 1/2, contradiction
  have hbad : (1 : Q') ≤ Q'.invSucc 1 := Q'.le_trans' _ _ _ hge hle
  exact absurd hbad (by decide)

/-- **Contrast: the FREE dodge trivially "resums" (Rule 9(6) vacuity, made explicit).**  The
zero coefficient sequence `diag ≡ 0` has a genuine resummation (`order := fun _ => 0`,
`|0| = 0 ≤ 1/(m+1)`).  So `GenuineResummation` is inhabited for the FREE dodge and refuted for
the PHYSICAL (factorial) coefficients — exactly the determination-vs-resummation split: the
residual is genuine only for the Isserlis-determined, factorially-growing coefficients
(`isserlis_refutes_free_dodge`), whose asymptotic growth admits no modulus. -/
def freeDodge_genuineResummation : GenuineResummation (fun _ => (0 : Q')) where
  order := fun _ => 0
  smallTail := fun m _ _ => by
    have h0 : Q'.abs (0 : Q') = 0 := by decide
    rw [h0]; exact Q'.invSucc_nonneg m

/-! ## 3. The terminal composition — z_n's full bound is CONDITIONAL on the two open inputs. -/

/-- **THE TERMINAL COMPOSITION (R1 ∧ R2), machine-checked as CONDITIONAL.**  For ANY
`InteractingContinuumMeasure afr b` — the a→0 interacting field measure that bundles BOTH open
inputs: `single : SinglePolymerActivity` (the R1 resummed single-polymer activity `z_1 ≤ g²`) and
the a→0 `base`/`zAmp` (the R2 renormalized continuum amplitudes) — the full KP amplitude bound
`|z_n| ≤ (μg²)^n` holds (`interacting_amplitude_le`).  So GIVEN the interacting continuum measure,
z_n's bound flows from the PROVED scaffold.  But the interacting continuum measure is UNINHABITED
(its `z_n` is a FREE field, `interacting_zAmp_free_dodge`), so this is a CONDITIONAL producer with
an open binder — it inhabits NO frontier bundle and constructs NO unconditional `z_n`. -/
theorem terminal_amplitude_conditional {afr : AFRateModulus} {b : Nat}
    (M : InteractingContinuumMeasure afr b) (k n : Nat) :
    (kpAmplitude_of_interactingContinuum M).zAmp k n
      ≤ ((kpAmplitude_of_interactingContinuum M).mu
          * fieldActivity (afr.w (afCutoff afr + k))) ^ n :=
  interacting_amplitude_le M k n

/-- **z_n stays a FREE field even with the full a→0 scaffold** — the a→0 interacting measure
does NOT determine `z_n`: `freeDodge_interactingContinuum` inhabits the whole structure with
`zAmp ≡ 0`.  So (R2) — the a→0 renormalization — does not, by itself, construct the interacting
amplitude; the renormalized continuum covariance of the RESUMMED `z_n` is the open residual. -/
theorem terminal_zAmp_free {afr : AFRateModulus} {b : Nat}
    (base : InverseLimitTower b) (single : SinglePolymerActivity afr) :
    (freeDodge_interactingContinuum base single).zAmp = (fun _ _ => (0 : Q')) :=
  interacting_zAmp_free_dodge base single

/-! ## 4. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **HONEST FINAL VERDICT — the terminal resummation test.**

The proposed closure — (R1) resummation reduces to the PROVED KP cluster bound, (R2)
renormalization reduces to the PROVED AF/field-space — **FAILS at a precise, machine-checked
seam.**  Both proved pieces are the WRONG-SIDE half of their residual:

  * **(R1) does NOT close.**  The KP bound `|z_n| ≤ (μg²)^n` (`amplitude_le`, PROVED
    combinatorially) bounds the connected Ursell amplitude indexed by CLUSTER SIZE `n`
    (geometric), DRIVEN by the single-polymer activity `z_1 ≤ g²` (`SinglePolymerActivity`,
    UNINHABITED).  The Isserlis DETERMINATION gives the coefficients indexed by ORDER `k`
    (factorial, radius 0).  These are different expansions; the KP bound CONSUMES the resummed
    `z_1`, it does not produce it.  `factorialSeries_no_genuineResummation` machine-checks that
    the factorial (Dyson) coefficients admit NO genuine Cauchy-modulus resummation — the partial
    sums are not Cauchy; a Borel/nonperturbative prescription is required, which the combinatorial
    KP scaffold does NOT supply.

  * **(R2) does NOT close.**  The AF `g² → 0` (`AFBetaStepCanonical`, canonical toy trajectory)
    and the field-space activity `→ 0` (`FieldSpaceCluster`) control the KP cluster SUM, but the
    a→0 limit of the RESUMMED interacting `z_n` as a renormalized continuum amplitude is
    `InteractingContinuumMeasure` — UNINHABITED, with `z_n` a FREE field
    (`terminal_zAmp_free`).  `terminal_amplitude_conditional` is a CONDITIONAL producer (open
    binder on the interacting measure).  Plugging `g² → 0` into the fixed-`a` bound does not
    construct the renormalized continuum covariance.

  * **z_n is NOT fully constructed.**  It is DETERMINED at finite order and BOUNDED above by the
    PROVED KP scaffold, but its full value requires (R1) the resummation of the factorial series
    to the finite `z_1 ≤ g²` and (R2) the a→0 renormalized interacting measure — BOTH UNINHABITED.

**No guarded frontier bundle is inhabited; the free-field dodge is refused; `GenuineResummation
dysonDiag` is PROVED uninhabitable; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.**
-/
theorem terminalResummationTest_honesty : True := trivial

end YMGap.Continuum.TerminalResummationTest

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.TerminalResummationTest.increment_eq_coeff
#print axioms YMGap.Continuum.TerminalResummationTest.fact_pos
#print axioms YMGap.Continuum.TerminalResummationTest.dysonDiag_ge_one
#print axioms YMGap.Continuum.TerminalResummationTest.factorialSeries_no_genuineResummation
#print axioms YMGap.Continuum.TerminalResummationTest.freeDodge_genuineResummation
#print axioms YMGap.Continuum.TerminalResummationTest.terminal_amplitude_conditional
#print axioms YMGap.Continuum.TerminalResummationTest.terminal_zAmp_free
