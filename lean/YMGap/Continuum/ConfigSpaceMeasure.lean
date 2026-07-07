/-
Track B / R2 — THE CONSTRUCTIVE CONFIGURATION-SPACE FIELD MEASURE, assembled: the Gaussian
base (the general all-order Isserlis moment functional), the finite-order interacting
expansion, and the Kotecký–Preiss resummation GIVEN a finite single-polymer activity `z_1`;
with `z_1` (the renormalon-obeying single-polymer activity) ISOLATED as the sole foundational
input.

# The obligation (read first)

The mass-gap construction needs a constructive config-space field measure
`∫ e^{−S(φ)} O(φ) Dφ / Z` with three layers:

  (a) THE GAUSSIAN BASE — the free field's Wick/Isserlis moments `⟨∏φ_i⟩ = Σ_{pairings}
      ∏ C(·,·)`.  `IsserlisGaussianBase` PROVED the SCALAR double-factorial moments
      `⟨x^{2n}⟩ = (2n−1)!!·s^{2n}` and the 4-point `wick4`; this module builds the GENERAL
      ALL-ORDER Isserlis moment functional `wickMoment V m` (any number `m` of legs, even AND
      odd), as a concrete `Q'`-valued functional, and PROVES it obeys Wick/Isserlis:
      even-`2n` moment `= (2n−1)!!·V^n` (the PROVED `numPairings` double factorial), odd
      moments `= 0`, and nonnegativity on a nonnegative covariance.  The Gaussian expectation of
      an even-polynomial observable is then the concrete finite sum `Σ_n c_n·wickMoment V (2n)`
      (`gaussBaseExpectation`).  **CONSTRUCTIBLE — the free field, proved moments.**

  (b) THE FINITE-ORDER INTERACTION — `e^{−S_int} = Σ_n (−S_int)^n/n!`, each term a Gaussian
      moment (Isserlis).  Reuses `IsserlisGaussianBase.feynTrunc`: the finite-order truncation
      `Σ_{k<K} diag k` of DETERMINED coefficients `diag k` (each a Wick contraction), with the
      increment `= diag K` (`feynTrunc_increment`).  **CONSTRUCTIBLE order-by-order.**  The GAP
      (proved elsewhere): the SERIES diverges factorially (`ConnectedActivityAssembly`,
      renormalon).

  (c) THE KP RESUMMATION GIVEN A FINITE `z_1` — if `|z_1| ≤ g²` (`SinglePolymerActivity`), the
      KP cluster expansion `Σ_n z_n` converges geometrically `≤ 1/(1−μg²)`
      (`KPFieldAmplitude.clusterSum_le`, PROVED combinatorially).  **CONSTRUCTIBLE GIVEN `z_1`.**

`ConfigSpaceMeasure` BUNDLES (a)+(b)+(c) into ONE object whose partition sum is a bounded
constructible `Q'` GIVEN `z_1`, and whose SOLE genuinely-open field is `single :
SinglePolymerActivity afr` — the renormalon-obeying `z_1`.

# HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

The Gaussian base (general all-order Isserlis functional), the finite-order interacting
expansion, and the KP resummation GIVEN `z_1` are ALL constructed / reduced to PROVED machinery.
The assembled `ConfigSpaceMeasure` has a bounded partition sum `Σ_n z_n ≤ 1/(1−μg²)`
(`partition_bounded`) as a concrete constructible `Q'`, GIVEN the single foundational input
`single : SinglePolymerActivity afr` (`|z_1| ≤ g²`).  Building the measure GIVEN `z_1` CLOSES
NOTHING — `z_1` is the INPUT; it ISOLATES `z_1` as the sole residual.  And `z_1` IS the
renormalon: its order-`k` connected perturbative series admits NO Cauchy-modulus resummation
(`ConnectedActivityAssembly.connected_reorg_no_resummation`, re-exported), while the physical
finite-order coefficients are strictly nonzero (`IsserlisGaussianBase.isserlis_refutes_free_dodge`,
re-exported) — so `z_1` is neither the free dodge nor perturbatively summable.  This is the
config-space-measure form of the SAME irreducible core `singleStep`/the renormalon.  No guarded
frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.

# Cascade / STOP status (mandatory task condition)

No STOP condition tripped.  This module builds constructive functionals and PROVES theorems
about them, then packages the KP-given-`z_1` bound and RE-EXPORTS the renormalon refutation.
`ConfigSpaceMeasure` carries `single : SinglePolymerActivity afr` as an OPEN field (Rule 6a) —
it is the config-space measure residual, deliberately UNINHABITED.  Producers are CONDITIONAL
(open binder on `ConfigSpaceMeasure`).  It inhabits NONE of the 5 guarded Clay-frontier types
(`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`) and
produces NO unconditional inhabitant of `SinglePolymerActivity`.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat`, reusing PROVED `IsserlisGaussianBase.{numPairings, numPairings_succ,
gaussMoment, pow_two_succ, wick4, feynTrunc, feynTrunc_increment, isserlis_refutes_free_dodge}`,
`SU3CharFactor.ofNat_mul_eqv`, `KPFieldAmplitude.{KPAmplitude, kpAmplitude_of_singlePolymer,
amplitude_le, clusterSum_le, SinglePolymerActivity}`,
`ConnectedActivityAssembly.{connLB, connected_reorg_no_resummation}`, `ExpGeomBound.ofNat_nonneg`,
the `Q'` `pow`/`mul`/`finSum` eqv algebra.  Every load-bearing declaration is `#print axioms`-
gated to `propext`/`Quot.sound` only (or empty — the numeric bridges are kernel-`decide`).  No
`Classical.*`, no `native_decide`, no `sorry`.  All witnesses `Type`-level.
-/
import YMGap.Continuum.IsserlisGaussianBase
import YMGap.Continuum.KPFieldAmplitude
import YMGap.Continuum.ConnectedActivityAssembly
import YMGap.Constructive.FinSumAlg
import YMGap.Constructive.Geometric

namespace YMGap.Continuum.ConfigSpaceMeasure

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.UniformCouplingFromAF
open YMGap.Continuum.FieldSpaceCluster
open YMGap.Continuum.KPFieldAmplitude
open YMGap.Continuum.IsserlisGaussianBase

/-! ## 1. THE GAUSSIAN BASE — the general all-order Isserlis moment functional. -/

/-- **THE GENERAL ISSERLIS MOMENT FUNCTIONAL** `wickMoment V m` — the Gaussian expectation
`⟨φ^m⟩` of the mean-zero single-mode Gaussian with variance `⟨φ²⟩ = V`, for ANY number `m` of
legs (even AND odd).  Wick/Isserlis by CONSTRUCTION: the head leg pairs with one of the
remaining `m−1` legs (factor `(m−1)` = number of partners, each contributing the 2-point `V`),
leaving `m−2` legs — the perfect-matching recursion.  Odd moments vanish automatically (an odd
count eventually hits the one-leg base case `= 0`); the even moments are the double factorial
`(2n−1)!!·V^n` (`wickMoment_even_eq`).  This GENERALISES `IsserlisGaussianBase.wick4` (the
`m = 4` case) to all orders as a concrete `Q'`-valued functional — the free-field base measure. -/
def wickMoment (V : Q') : Nat → Q'
  | 0 => 1
  | 1 => 0
  | (m + 2) => Q'.ofNat (m + 1) * (V * wickMoment V m)

/-- `⟨φ⁰⟩ = 1` (the normalisation). -/
theorem wickMoment_zero (V : Q') : wickMoment V 0 = 1 := rfl
/-- `⟨φ¹⟩ = 0` (mean-zero). -/
theorem wickMoment_one (V : Q') : wickMoment V 1 = 0 := rfl
/-- **THE PERFECT-MATCHING RECURSION** `⟨φ^{m+2}⟩ = (m+1)·V·⟨φ^m⟩`: the head leg pairs with one
of the `m+1` other legs, each pairing contributing the 2-point `V`. -/
theorem wickMoment_succ2 (V : Q') (m : Nat) :
    wickMoment V (m + 2) = Q'.ofNat (m + 1) * (V * wickMoment V m) := rfl

/-- A 4-element multiplicative shuffle `A·(V·(B·P)) ≃ (A·B)·(V·P)` (the reassembly for the
double-factorial recursion; Lean-core `Q'.eqv` algebra, no `ring`). -/
theorem shuffle4 (A B V P : Q') : (A * (V * (B * P))).eqv ((A * B) * (V * P)) := by
  have e1 : (V * (B * P)).eqv (B * (V * P)) := by
    refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv V B P)) ?_
    refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right (V * B) (B * V) P (Q'.mul_comm_eqv V B)) ?_
    exact Q'.mul_assoc_eqv B V P
  refine Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left A (V * (B * P)) (B * (V * P)) e1) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv A B (V * P))

/-- **THE ISSERLIS DOUBLE-FACTORIAL MOMENT** `⟨φ^{2n}⟩ = (2n−1)!!·V^n`.  The general functional
`wickMoment` on `2n` legs equals the PROVED perfect-matching count `numPairings n = (2n−1)!!`
(`IsserlisGaussianBase.numPairings`) times `V^n`.  PROVED by induction on `n` via the recursion
`wickMoment_succ2`, the PROVED `numPairings_succ`, `SU3CharFactor.ofNat_mul_eqv`, and the
`shuffle4` reassembly — the genuine Wick/Isserlis structure for ALL orders. -/
theorem wickMoment_even_eq (V : Q') :
    ∀ n, (wickMoment V (2 * n)).eqv (Q'.ofNat (numPairings n) * V ^ n)
  | 0 => by
      have h : (wickMoment V (2 * 0)) = (1 : Q') := rfl
      have hr : (Q'.ofNat (numPairings 0) * V ^ 0) = (Q'.ofNat 1 * (1 : Q')) := rfl
      rw [h, hr]; decide
  | (n + 1) => by
      have hidx : 2 * (n + 1) = (2 * n) + 2 := by omega
      have hlhs : wickMoment V (2 * (n + 1))
          = Q'.ofNat (2 * n + 1) * (V * wickMoment V (2 * n)) := by
        rw [hidx]; exact wickMoment_succ2 V (2 * n)
      have ih := wickMoment_even_eq V n
      rw [hlhs]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat (2 * n + 1)) _ _
          (Q'.mul_eqv_congr_left V _ _ ih)) ?_
      refine Q'.eqv_trans _ _ _
        (shuffle4 (Q'.ofNat (2 * n + 1)) (Q'.ofNat (numPairings n)) V (V ^ n)) ?_
      have hV : (V * V ^ n) = V ^ (n + 1) := (Q'.pow_succ V n).symm
      rw [hV]
      have hnp : numPairings (n + 1) = (2 * n + 1) * numPairings n := numPairings_succ n
      rw [hnp]
      exact Q'.mul_eqv_congr_right _ _ (V ^ (n + 1))
        (Q'.eqv_symm (SU3CharFactor.ofNat_mul_eqv (2 * n + 1) (numPairings n)))

/-- **THE ODD MOMENTS VANISH** `⟨φ^{2n+1}⟩ = 0` (mean-zero symmetry).  Proved by induction on
`n`: the base is `⟨φ¹⟩ = 0`; the step propagates the zero through the recursion
(`wickMoment_succ2`, `Q'.mul_zero_eqv`). -/
theorem wickMoment_odd_zero (V : Q') :
    ∀ n, (wickMoment V (2 * n + 1)).eqv 0
  | 0 => by
      show (wickMoment V 1).eqv 0
      rw [wickMoment_one]; exact Q'.eqv_refl 0
  | (n + 1) => by
      have hidx : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
      rw [hidx, wickMoment_succ2]
      have ih := wickMoment_odd_zero V n
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat (2 * n + 1 + 1)) _ _
          (Q'.mul_eqv_congr_left V _ _ ih)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (Q'.ofNat (2 * n + 1 + 1)) (V * 0) 0 (Q'.mul_zero_eqv V)) ?_
      exact Q'.mul_zero_eqv (Q'.ofNat (2 * n + 1 + 1))

/-- **THE GAUSSIAN BASE IS NONNEGATIVE** on a nonnegative covariance: `⟨φ^m⟩ ≥ 0` for `V ≥ 0`.
Two-step structural induction on `m` via the recursion (`Q'.mul_nonneg`, `ExpGeomBound.ofNat_nonneg`). -/
theorem wickMoment_nonneg (V : Q') (hV : (0 : Q') ≤ V) :
    ∀ m, (0 : Q') ≤ wickMoment V m
  | 0 => by rw [wickMoment_zero]; decide
  | 1 => by rw [wickMoment_one]; exact Q'.le_refl' 0
  | (m + 2) => by
      rw [wickMoment_succ2]
      exact Q'.mul_nonneg _ _ (ofNat_nonneg (m + 1))
        (Q'.mul_nonneg _ _ hV (wickMoment_nonneg V hV m))

/-! ### Numeric bridges to the PROVED `IsserlisGaussianBase` objects (kernel-`decide`). -/

/-- The general functional AGREES with the PROVED 4-point `wick4` at order 4:
`⟨φ⁴⟩ = wickMoment 1 4 ≃ wick4 (const 1) = 3` (the 3 pairings of 4 legs).  Kernel-`decide`,
AXIOM-FREE — ties the general all-order functional to the proved multi-mode contraction. -/
theorem wickMoment_four_eq_wick4 :
    (wickMoment (1 : Q') 4).eqv (wick4 (fun _ _ => (1 : Q')) 0 1 2 3) := by decide

/-- `⟨φ⁴⟩ = 3` at unit variance (the Isserlis value the library base FAILED, now via the
general functional).  Kernel-`decide`, AXIOM-FREE. -/
theorem wickMoment_four_val : (wickMoment (1 : Q') 4).eqv (Q'.ofNat 3) := by decide

/-- `(s·s)^n ≃ s^{2n}` — the square-power collapse (induction, `IsserlisGaussianBase.pow_two_succ`). -/
theorem sq_pow (s : Q') : ∀ n, ((s * s) ^ n).eqv (s ^ (2 * n))
  | 0 => Q'.eqv_of_eq rfl
  | (n + 1) => by
      show ((s * s) * (s * s) ^ n).eqv (s ^ (2 * (n + 1)))
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (s * s) ((s * s) ^ n) (s ^ (2 * n)) (sq_pow s n)) ?_
      exact Q'.eqv_symm (pow_two_succ s n)

/-- The `2n`-leg moment at `V = s²` is the PROVED scalar Isserlis moment
`IsserlisGaussianBase.gaussMoment s n = (2n−1)!!·s^{2n}`.  Bridges the general functional to the
proved scalar double-factorial moment via `(s·s)^n ≃ s^{2n}` (`sq_pow`). -/
theorem wickMoment_even_eq_gaussMoment (s : Q') (n : Nat) :
    (wickMoment (s * s) (2 * n)).eqv (gaussMoment s n) := by
  refine Q'.eqv_trans _ _ _ (wickMoment_even_eq (s * s) n) ?_
  exact Q'.mul_eqv_congr_left (Q'.ofNat (numPairings n)) _ _ (sq_pow s n)

/-- **THE GAUSSIAN EXPECTATION OF AN EVEN-POLYNOMIAL OBSERVABLE** — the concrete `Q'`-valued free
-field functional `⟨O⟩_Gauss = Σ_{n<N} c_n·⟨φ^{2n}⟩ = Σ_n c_n·(2n−1)!!·V^n`, where `c_n` is the
coefficient of `φ^{2n}` in the observable `O`.  A genuine finite sum of the PROVED Isserlis
moments — the constructible Gaussian base measure evaluated on observables. -/
def gaussBaseExpectation (V : Q') (c : Nat → Q') (N : Nat) : Q' :=
  finSum (fun n => c n * wickMoment V (2 * n)) N

/-- The Gaussian base expectation of a nonnegative observable (`c_n ≥ 0`) on a nonnegative
covariance (`V ≥ 0`) is nonnegative — a genuine constructive positivity of the free-field
functional. -/
theorem gaussBaseExpectation_nonneg (V : Q') (c : Nat → Q')
    (hV : (0 : Q') ≤ V) (hc : ∀ n, (0 : Q') ≤ c n) :
    ∀ N, (0 : Q') ≤ gaussBaseExpectation V c N
  | 0 => Q'.le_refl' 0
  | (N + 1) => by
      show (0 : Q') ≤ finSum (fun n => c n * wickMoment V (2 * n)) N + c N * wickMoment V (2 * N)
      exact Q'.zero_le_add _ _ (gaussBaseExpectation_nonneg V c hV hc N)
        (Q'.mul_nonneg _ _ (hc N) (wickMoment_nonneg V hV (2 * N)))

/-! ## 2. THE FINITE-ORDER INTERACTION — `e^{−S_int} = Σ_n (−S_int)^n/n!` (reused). -/

/-- **THE FINITE-ORDER INTERACTING EXPANSION** `Σ_{k<K} diag k` of the DETERMINED order-`k`
coefficients `diag k` (each an Isserlis/Wick Gaussian moment).  Re-exports
`IsserlisGaussianBase.feynTrunc`: order-by-order the perturbative expansion of `e^{−S_int}`
against the Gaussian base is a UNIQUE constructible value (not an upper bound). -/
def interactingTrunc (diag : Nat → Q') (K : Nat) : Q' := feynTrunc diag K

/-- The order-`K` increment of the finite-order expansion IS the order-`K` coefficient `diag K`
(`Σ_{k<K+1} − Σ_{k<K} = diag K`).  Reuses `IsserlisGaussianBase.feynTrunc_increment`; isolates
the (open) resummation to the ASYMPTOTIC behaviour of the DETERMINED coefficients. -/
theorem interactingTrunc_increment (diag : Nat → Q') (K : Nat) :
    interactingTrunc diag (K + 1) = interactingTrunc diag K + diag K :=
  feynTrunc_increment diag K

/-! ## 3. THE ASSEMBLED CONFIG-SPACE MEASURE — Gaussian base + finite-order + KP-given-`z_1`. -/

/-- **`ConfigSpaceMeasure afr` — the constructive configuration-space field measure (`Type`,
Rule 6a).**  Bundles the three layers, with the single-polymer activity `z_1` as the SOLE
genuinely-open field:

  * **Gaussian base (constructible):** `siteVar k` = per-scale variance `⟨φ²⟩ = s_k²` (`≥ 0`),
    against which the Gaussian expectation `gaussBaseExpectation (siteVar k) obsCoeff` is a
    concrete `Q'` (the PROVED all-order Isserlis moments);
  * **finite-order interaction (constructible):** `obsCoeff n` = the even-polynomial observable
    coefficients feeding the Gaussian base;
  * **KP substrate (reduced to PROVED machinery):** `mu` (connectivity growth), `zAmp k n`
    (connected `n`-cluster amplitudes `|z_n|`), `treeDom` (`|z_n| ≤ μ^n·(z_1)^n` — the Wick
    tree-domination, PROVED reducible via `WickTreeDomination`/`IsserlisPenroseReduction`);
  * **THE SOLE RESIDUAL:** `single : SinglePolymerActivity afr` — the single-polymer activity
    `|z_1| ≤ g²`, the renormalon-obeying config-space quantity.

GIVEN `single`, the whole KP resummation is bounded (`partition_bounded`).  Building the measure
GIVEN `z_1` closes nothing — it ISOLATES `z_1`.  HONESTY CAVEAT (Rule 9(6)): `treeDom`/`zAmp`
bound FREE functions, vacuously fakeable (`zAmp ≡ 0`); the residual is genuine only for the
PHYSICAL amplitudes (nonzero leading Isserlis contraction, `free_dodge_refuted`).  UNINHABITED. -/
structure ConfigSpaceMeasure (afr : AFRateModulus) : Type where
  /-- Per-scale Gaussian base variance `⟨φ²⟩ = s_k²`. -/
  siteVar : Nat → Q'
  /-- `⟨φ²⟩ ≥ 0`. -/
  siteVar_nonneg : ∀ k, (0 : Q') ≤ siteVar k
  /-- Even-polynomial observable coefficients `c_n` (coefficient of `φ^{2n}`). -/
  obsCoeff : Nat → Q'
  /-- `c_n ≥ 0`. -/
  obsCoeff_nonneg : ∀ n, (0 : Q') ≤ obsCoeff n
  /-- Connectivity growth constant `μ = 3K` (PROVED-bounded by `combGrowth_le`). -/
  mu : Q'
  /-- `μ ≥ 0`. -/
  mu_nonneg : (0 : Q') ≤ mu
  /-- Connected `n`-cluster amplitudes `|z_n(w_k)|`. -/
  zAmp : Nat → Nat → Q'
  /-- `|z_n| ≥ 0`. -/
  zAmp_nonneg : ∀ k n, (0 : Q') ≤ zAmp k n
  /-- **THE SOLE RESIDUAL** — the single-polymer activity `|z_1| ≤ g²` (the renormalon). -/
  single : SinglePolymerActivity afr
  /-- **The Wick tree-domination** `|z_n| ≤ μ^n·(z_1)^n` (PROVED reducible, config-space Wick). -/
  treeDom : ∀ k n, zAmp k n ≤ mu ^ n * (single.z1 k) ^ n

/-- **The config-space measure's KP amplitude datum**, built from the single-polymer activity
`z_1` and the tree domination (reusing `KPFieldAmplitude.kpAmplitude_of_singlePolymer`). -/
def ConfigSpaceMeasure.toKP {afr : AFRateModulus} (C : ConfigSpaceMeasure afr) :
    KPAmplitude afr :=
  kpAmplitude_of_singlePolymer C.mu C.mu_nonneg C.single C.zAmp C.zAmp_nonneg C.treeDom

/-- **THE GAUSSIAN BASE FUNCTIONAL of the config measure at scale `k`** — the concrete
constructible free-field expectation `⟨O⟩_Gauss = Σ_{n<N} c_n·⟨φ^{2n}⟩` at variance `siteVar k`. -/
def ConfigSpaceMeasure.gaussBase {afr : AFRateModulus} (C : ConfigSpaceMeasure afr)
    (k N : Nat) : Q' :=
  gaussBaseExpectation (C.siteVar k) C.obsCoeff N

/-- The Gaussian base functional is nonnegative (constructive positivity of the free field). -/
theorem ConfigSpaceMeasure.gaussBase_nonneg {afr : AFRateModulus} (C : ConfigSpaceMeasure afr)
    (k N : Nat) : (0 : Q') ≤ C.gaussBase k N :=
  gaussBaseExpectation_nonneg (C.siteVar k) C.obsCoeff (C.siteVar_nonneg k) C.obsCoeff_nonneg N

/-- **THE AMPLITUDE BOUND** `|z_n(w_k)| ≤ (μ·g²)^n` — the connected `n`-cluster amplitude is
KP-bounded GIVEN the single-polymer activity `z_1`.  Reuses PROVED `amplitude_le`. -/
theorem ConfigSpaceMeasure.amplitude_bounded {afr : AFRateModulus} (C : ConfigSpaceMeasure afr)
    (k n : Nat) :
    C.zAmp k n ≤ (C.mu * fieldActivity (afr.w (afCutoff afr + k))) ^ n :=
  amplitude_le C.toKP k n

/-- **THE KP RESUMMATION GIVEN A FINITE `z_1` — the config-space measure's partition sum is a
BOUNDED constructible `Q'`.**  When the KP small-activity gate holds (`0 < 1 − μ·g²`), the
interacting cluster partition sum is bounded UNIFORMLY in `N`:

    Σ_{n<N} |z_n(w_k)|  ≤  1/(1 − μ·g²) .

PROVED by reusing `KPFieldAmplitude.clusterSum_le` on `C.toKP`.  This is the constructive
interacting measure GIVEN the single foundational input `z_1` — the whole KP-resummed
config-space measure, modulo `z_1`. -/
theorem ConfigSpaceMeasure.partition_bounded {afr : AFRateModulus} (C : ConfigSpaceMeasure afr)
    (k : Nat)
    (hsmall : (0 : Q') < 1 - C.mu * fieldActivity (afr.w (afCutoff afr + k))) (N : Nat) :
    finSum (C.zAmp k) N
      ≤ Q'.divPos 1 (1 - C.mu * fieldActivity (afr.w (afCutoff afr + k))) hsmall :=
  clusterSum_le C.toKP k hsmall N

/-- **THE SOLE RESIDUAL, extracted.**  The config-space measure's only genuinely-open input is
its `single` field — the single-polymer activity `z_1` (`SinglePolymerActivity afr`).  Everything
else (Gaussian base moments, finite-order coefficients, KP resummation) is constructed / PROVED-
reducible.  This projection MAKES the isolation explicit: `configMeasure = KP(z_1)`, `z_1` the
only foundational datum. -/
def ConfigSpaceMeasure.residual {afr : AFRateModulus} (C : ConfigSpaceMeasure afr) :
    SinglePolymerActivity afr := C.single

/-! ## 4. `z_1` IS THE RENORMALON — the isolation is the SAME irreducible core. -/

/-- **`z_1`'s ORDER-`k` CONNECTED PERTURBATIVE SERIES DOES NOT RESUM (the renormalon).**  The
exact φ⁴ connected 2-point coefficients (the perturbative determination of `z_1`) grow super-
geometrically (`connLB`, ratio `≥ 32`, radius 0) and admit NO Cauchy-modulus resummation.  So
`z_1` is NOT produced by resumming its determined perturbative coefficients — it is the genuine
non-perturbative (Borel/renormalon) input.  Re-exports
`ConnectedActivityAssembly.connected_reorg_no_resummation`; the sole residual `z_1` of the
config-space measure IS the renormalon. -/
theorem configMeasure_z1_is_renormalon :
    YMGap.Continuum.TerminalResummationTest.GenuineResummation
      ConnectedActivityAssembly.connLB → False :=
  ConnectedActivityAssembly.connected_reorg_no_resummation

/-- **THE PHYSICAL `z_1` IS NOT THE FREE DODGE.**  With the leading coefficient set to the
genuine Isserlis contraction (`wick4 = 3 > 0`), the finite-order interacting truncation is
strictly APART from `0` — so the physical interacting amplitude `z_n ≢ 0`.  Re-exports
`IsserlisGaussianBase.isserlis_refutes_free_dodge`: the residual `z_1` is a genuine nonzero
interacting object, not the vacuous free-field `z_n ≡ 0`.  Together with
`configMeasure_z1_is_renormalon`, `z_1` is neither the free dodge nor perturbatively summable —
the SAME irreducible core `singleStep`/the renormalon, in explicit config-space measure form. -/
theorem configMeasure_free_dodge_refuted :
    ¬ (interactingTrunc leadingIsserlisDiag 2).eqv 0 :=
  isserlis_refutes_free_dodge

/-! ## 5. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **HONEST FINAL VERDICT.**

The constructive configuration-space field measure is ASSEMBLED, with `z_1` isolated as the sole
residual:

  * **(a) The Gaussian base is BUILT** as the general all-order Isserlis moment functional
    `wickMoment V m` — even moments `= (2n−1)!!·V^n` (`wickMoment_even_eq`, the PROVED
    `numPairings` double factorial), odd moments `= 0` (`wickMoment_odd_zero`), nonneg on a
    nonneg covariance (`wickMoment_nonneg`), agreeing with the PROVED `wick4` at order 4
    (`wickMoment_four_eq_wick4`) and the PROVED scalar `gaussMoment` at `V = s²`
    (`wickMoment_even_eq_gaussMoment`).  The Gaussian expectation of an even-polynomial
    observable is the concrete finite sum `gaussBaseExpectation` (nonneg,
    `gaussBaseExpectation_nonneg`).  CONSTRUCTIBLE — the free field, proved moments.

  * **(b) The finite-order interaction is CONSTRUCTIBLE order-by-order** (`interactingTrunc`, the
    reused `feynTrunc`; increment `= diag K`).

  * **(c) The KP resummation GIVEN `z_1` is BOUNDED** (`ConfigSpaceMeasure.partition_bounded`:
    `Σ_n |z_n| ≤ 1/(1−μg²)`), a concrete constructible `Q'` GIVEN the single foundational input
    `single : SinglePolymerActivity afr`.

  * **(d) `z_1` is ISOLATED as the sole residual** (`ConfigSpaceMeasure.residual`).  Building the
    measure GIVEN `z_1` CLOSES NOTHING — `z_1` is the INPUT.  And `z_1` IS the renormalon: its
    order-`k` connected perturbative series admits NO Cauchy-modulus resummation
    (`configMeasure_z1_is_renormalon`), while the physical finite-order coefficients are strictly
    nonzero (`configMeasure_free_dodge_refuted`).  So `z_1` is neither the free dodge nor
    perturbatively summable — the config-space-measure form of the SAME irreducible core
    `singleStep`/the renormalon.

The constructive substrate now built: the Gaussian base (all-order Isserlis functional), the
finite-order amplitudes, and the KP-resummed partition bound GIVEN `z_1`.  The sole residual: the
single-polymer activity `z_1` = `singleStep` = the renormalon — the genuine non-perturbative
config-space input.  No guarded frontier bundle is inhabited; the free-field dodge is REFUTED;
nothing is faked; the 4D Yang–Mills mass gap remains OPEN. -/
theorem configSpaceMeasure_honesty : True := trivial

end YMGap.Continuum.ConfigSpaceMeasure

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.ConfigSpaceMeasure.wickMoment_succ2
#print axioms YMGap.Continuum.ConfigSpaceMeasure.shuffle4
#print axioms YMGap.Continuum.ConfigSpaceMeasure.wickMoment_even_eq
#print axioms YMGap.Continuum.ConfigSpaceMeasure.wickMoment_odd_zero
#print axioms YMGap.Continuum.ConfigSpaceMeasure.wickMoment_nonneg
#print axioms YMGap.Continuum.ConfigSpaceMeasure.wickMoment_four_eq_wick4
#print axioms YMGap.Continuum.ConfigSpaceMeasure.wickMoment_four_val
#print axioms YMGap.Continuum.ConfigSpaceMeasure.wickMoment_even_eq_gaussMoment
#print axioms YMGap.Continuum.ConfigSpaceMeasure.gaussBaseExpectation_nonneg
#print axioms YMGap.Continuum.ConfigSpaceMeasure.interactingTrunc_increment
#print axioms YMGap.Continuum.ConfigSpaceMeasure.ConfigSpaceMeasure.gaussBase_nonneg
#print axioms YMGap.Continuum.ConfigSpaceMeasure.ConfigSpaceMeasure.amplitude_bounded
#print axioms YMGap.Continuum.ConfigSpaceMeasure.ConfigSpaceMeasure.partition_bounded
#print axioms YMGap.Continuum.ConfigSpaceMeasure.configMeasure_z1_is_renormalon
#print axioms YMGap.Continuum.ConfigSpaceMeasure.configMeasure_free_dodge_refuted
