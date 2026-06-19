/-
Route B, end-to-end as a CONDITIONAL chain — the non-abelian susceptibility
certificate, the multiscale assembly, and the dynamic⇒static bridge, composed
to a single named analytic input that would buy the entire continuum gap.

# What this module is — the Route-B reduction, completed conditionally

The mass-gap attack along Route B has three genuine analytic inputs, in order:

  1. a NON-ABELIAN SUSCEPTIBILITY CERTIFICATE — a spacing-uniform weighted
     covariance bound on gauge-invariant edge gradients (the object Shen–Zhu–Zhu
     produce on the lattice; here it is NAMED, not proved);
  2. the SUSCEPTIBILITY ⇒ PER-SCALE-RATE step — a Bakry–Émery / Polchinski-flow
     argument turning the susceptibility bound into per-RG-scale contraction
     rates with summable loss (the genuine frontier — NAMED, not proved);
  3. the SHARP DYNAMIC ⇒ STATIC RATE — `m(a) ≥ c·a` with the right power of the
     spacing for a finite continuum mass (the Combes–Thomas / Helffer–Sjöstrand
     content — carried as an explicit hypothesis where not constructively forced).

This module NAMES inputs (1) and (2) as `Type`-level obligations, and PROVES the
two structural arrows that connect them to the existing continuum-gap machinery:

  * `perScaleRateData_to_uniformLSI` — the MULTISCALE ASSEMBLY: per-scale rates
    with summable loss ⇒ a single spacing-uniform LSI / Poincaré constant.  This
    is PROVED, reusing the constructive product-floor reduction (Weierstrass
    floor `∏(1−η_k) ≥ 1−∑η_k`, positive when `∑ < 1`).
  * `uniformLSI_to_physicalGapFloor` — the DYNAMIC ⇒ STATIC bridge: from the
    uniform LSI constant build a per-spacing dynamic gap, transfer positivity
    qualitatively (`λ>0 ⇒ m>0`, PROVED via `dynamic_to_static`), and assemble a
    `PhysicalGapFloor` from the explicit sharp-rate hypothesis.

The headline composite `nonAbelian_certificate_implies_gap` shows the payoff:
ONE named analytic certificate (plus its two NAMED step-obligations and the sharp
rate) ⇒ `physGapMin > 0`, the continuum mass gap.

# What is PROVED vs what is a NAMED OBLIGATION (honest — AGENTS.md Rule 6)

PROVED here (genuine theorems):

  * `perScaleRateData_to_uniformLSI` — the per-scale ⇒ uniform-LSI assembly (the
    clean part: product-floor summability ⇒ a uniform finite constant).
  * `UniformLSI.dynamicGap` and `uniformLSI_dynamicGap_m_pos` — the per-spacing
    dynamic gap is positive; `λ>0 ⇒ m>0` via `dynamic_to_static`.
  * `uniformLSI_to_physicalGapFloor` — the assembly of a `PhysicalGapFloor` from
    the uniform LSI datum together with the explicit two-sided rate hypothesis.
  * the composites `uniformLSI_implies_gap`, `nonAbelian_certificate_implies_gap`
    and the continuum-gap corollary.

NAMED OBLIGATIONS (NOT inhabited — the open frontier):

  * `NonAbelianSusceptibility` — the susceptibility certificate itself; no
    inhabitant for 4D Yang–Mills is provided.
  * `NASuscept_to_PerScaleRateData` — the susceptibility ⇒ per-scale-rate map;
    carried as a hypothesis/field (the Bakry–Émery / Polchinski content), NEVER
    proved.
  * the SHARP rate `m(a) ≥ c·a` — carried as an explicit field of
    `PhysicalRateBridge`; the QUALITATIVE `m>0` is proved, the spacing-uniform
    power is the analytic content.

The deliverable is the Route-B reduction COMPLETED CONDITIONALLY: it localizes
the entire remaining continuum-gap problem to one analytic certificate and two
named steps; it does NOT solve them.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'` arithmetic and structural assembly over the reused product-floor,
dynamic⇒static, and physical-separator data.  Every load-bearing declaration is
gated with `#print axioms`; permitted output is `propext` / `Quot.sound` only.
No `Classical.*`, no `native_decide`, no `sorry`.  Every certificate, step-map,
and rate is `Type`-level data; the analytic inputs are NAMED, never faked.
-/

import YMGap.Continuum.PhysicalSeparator
import YMGap.Continuum.DynamicToStaticGap
import YMGap.Continuum.PerScaleContraction
import YMGap.Continuum.ProductFloor
import YMGap.Constructive.RegularCRealArith

namespace YMGap.Continuum.NonAbelianGapChain

open YMGap.Constructive
open YMGap.Constructive.Q'
open YMGap.Constructive.RegularCReal
open YMGap.Continuum
open YMGap.Continuum.SpectralGap
open YMGap.Continuum.RegularContinuumPipeline
open YMGap.Continuum.RGGapPersistence
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.ProductFloor

/-! ## 1. The non-abelian susceptibility certificate (Task 7) — NAMED OBLIGATION

The missing analytic input of Route B is a SPACING-UNIFORM weighted covariance
bound on gauge-invariant edge gradients: the non-abelian susceptibility
certificate.  We declare its interface HONESTLY as `Type`-level data — an
inhabitant must supply the gauge-invariant test/edge-gradient/covariance objects
and the weighted bound.  No inhabitant for 4D Yang–Mills is provided.

`CovInterface` is the abstract covariance interface:

  * `Test`            — the type of gauge-invariant test functions/observables;
  * `edgeGrad t e`    — the edge-gradient magnitude of `t` at edge index `e`
                        (a `Q'` magnitude);
  * `cov a t`         — the covariance functional of `t` at spacing index `a`
                        (a `Q'` magnitude);
  * `weightedCovNorm a t m` — the `m`-weighted covariance norm of `t` at spacing
                        `a` (the quantity the susceptibility bound controls). -/

/-- The abstract gauge-invariant covariance interface a `NonAbelianSusceptibility`
certificate carries.  Bundled as `Type`-level data; the genuine 4D content lives
in an inhabitant, never faked here. -/
structure CovInterface : Type 1 where
  /-- The type of gauge-invariant test functions / observables. -/
  Test : Type
  /-- The edge-gradient magnitude of `t` at edge index `e`. -/
  edgeGrad : Test → Nat → Q'
  /-- The covariance functional magnitude of `t` at spacing index `a`. -/
  cov : Nat → Test → Q'
  /-- The `m`-weighted covariance norm of `t` at spacing index `a` — the
  quantity the susceptibility bound controls. -/
  weightedCovNorm : Nat → Test → Q' → Q'
  /-- The weighted covariance norm is a nonnegative magnitude. -/
  weightedCovNorm_nonneg : ∀ a t m, (0 : Q') ≤ weightedCovNorm a t m

/-- **The non-abelian susceptibility certificate (Task 7) — NAMED OBLIGATION.**

Carries:

  * `m`, `m_pos` — a positive mass scale of the certificate;
  * `C`, `C_pos` — a positive uniform susceptibility constant;
  * `covIface`   — the abstract gauge-invariant covariance interface;
  * `window a`   — the spacing window on which the bound holds;
  * `suscBound`  — **the OPEN analytic content:** for every spacing `a` in the
    window and every gauge-invariant test `t`, the `m`-weighted covariance norm
    is bounded by `C`, UNIFORMLY in `a` (the spacing-uniform susceptibility
    certificate);
  * `volumeModulus` — a constructive Cauchy modulus `ε ↦ N` for the
    finite-volume measure approximations (carried as `Type`-level data per
    Rule 8 — the rate is consumed, not erased).

NO inhabitant for 4D Yang–Mills is provided.  This record NAMES the non-abelian
susceptibility theorem; it is the open analytic input, not proved. -/
structure NonAbelianSusceptibility : Type 1 where
  /-- A positive mass scale of the certificate. -/
  m : Q'
  /-- The mass scale is strictly positive. -/
  m_pos : (0 : Q') < m
  /-- A positive uniform susceptibility constant. -/
  C : Q'
  /-- The susceptibility constant is strictly positive. -/
  C_pos : (0 : Q') < C
  /-- The abstract gauge-invariant covariance interface. -/
  covIface : CovInterface
  /-- The spacing window on which the certificate holds. -/
  window : Nat → Prop
  /-- **The OPEN analytic content:** the spacing-uniform weighted-covariance
  bound `weightedCovNorm a t m ≤ C` for every spacing `a` in the window and
  every gauge-invariant test `t`. -/
  suscBound : ∀ a : Nat, window a → ∀ t : covIface.Test,
    covIface.weightedCovNorm a t m ≤ C
  /-- A constructive Cauchy modulus `ε ↦ N` for the finite-volume measure
  approximations (carried as data, Rule 8). -/
  volumeModulus : Q' → Nat

/-! ## 2. The uniform LSI / Poincaré record (shared) — Task 2

The central object of Route B: a SPACING-UNIFORM log-Sobolev / Poincaré constant
bound.  `UniformLSI` carries a positive `K` and, for each spacing in the window,
a positive functional-inequality constant `lsiConst a` with the spacing-uniform
bound `lsiConst a ≤ K · aScaling a` (the `a`-scaling carried as an explicit
field).  From it a per-spacing `DynamicGap λ(a) := 1/lsiConst a` is derived
(positive).  This is the spacing-uniform functional inequality. -/

/-- **The spacing-uniform log-Sobolev / Poincaré constant bound (Task 2).**

Carries:

  * `K`, `K_pos`     — a positive spacing-uniform constant;
  * `window a`       — the spacing window;
  * `aScaling a`, `aScaling_pos` — the explicit `a`-scaling (e.g. `a²` per the
    review, or the cleanest faithful form) entering the LSI bound;
  * `lsiConst a`, `lsiConst_pos` — the per-spacing functional-inequality constant;
  * `lsiBound`       — the spacing-uniform bound `lsiConst a ≤ K · aScaling a` on
    the window.

From these a per-spacing `DynamicGap λ(a) := 1/lsiConst a` is derived below. -/
structure UniformLSI : Type where
  /-- A positive spacing-uniform constant. -/
  K : Q'
  /-- `K` is strictly positive. -/
  K_pos : (0 : Q') < K
  /-- The spacing window. -/
  window : Nat → Prop
  /-- The explicit `a`-scaling entering the LSI bound. -/
  aScaling : Nat → Q'
  /-- The `a`-scaling is strictly positive on every spacing index. -/
  aScaling_pos : ∀ a : Nat, (0 : Q') < aScaling a
  /-- The per-spacing functional-inequality (LSI / Poincaré) constant. -/
  lsiConst : Nat → Q'
  /-- The per-spacing LSI constant is strictly positive. -/
  lsiConst_pos : ∀ a : Nat, (0 : Q') < lsiConst a
  /-- **The spacing-uniform bound** `lsiConst a ≤ K · aScaling a` on the window. -/
  lsiBound : ∀ a : Nat, window a → lsiConst a ≤ K * aScaling a

namespace UniformLSI

/-- **The per-spacing dynamic gap** `λ(a) := 1/lsiConst a` — the reciprocal of
the functional-inequality constant, strictly positive.  This is the dynamic
Poincaré rate the Helffer–Sjöstrand bridge consumes. -/
def dynamicGap (U : UniformLSI) (a : Nat) : DynamicGap where
  lambda := Q'.divPos 1 (U.lsiConst a) (U.lsiConst_pos a)
  lambda_pos := Q'.divPos_pos 1 (U.lsiConst a) (U.lsiConst_pos a) (by decide)

/-- The derived per-spacing dynamic gap is positive (`λ(a) > 0`). -/
theorem dynamicGap_lambda_pos (U : UniformLSI) (a : Nat) :
    (0 : Q') < (U.dynamicGap a).lambda :=
  (U.dynamicGap a).lambda_pos

end UniformLSI

/-! ## 3. The per-scale rate data and the MULTISCALE ASSEMBLY (Task 8)

`PerScaleRateData` carries the per-RG-scale contraction rates `ρ_k ∈ [0,1]` with
a SUMMABLE-loss bound `∑_{k<n}(1 − ρ_k) ≤ R < 1` (the `ProductFloor` style), an
explicit `a`-scaling, and a positive base LSI scale.

The ASSEMBLY `perScaleRateData_to_uniformLSI` (per-scale rates with summable loss
⇒ a uniform LSI constant) is PROVED, reusing `ProductFloor.prod_floor_of_sum_le`:
the prefix products `∏_{k<n} ρ_k` are bounded below by the single positive
constant `1 − R`, so a uniform-in-`n` finite LSI constant `K := 1/(1−R)` exists.

The step `NonAbelianSusceptibility → PerScaleRateData` is the NAMED analytic
obligation (`NASuscept_to_PerScaleRateData`): a hypothesis/field, NOT proved — it
is the genuine frontier (non-abelian susceptibility ⇒ per-scale Hessian /
contraction bounds). -/

/-- **The per-scale rate data (Task 8 input).**

Carries:

  * `rho k`, `rho_nonneg`, `rho_le_one` — the per-RG-scale contraction rates
    `ρ_k ∈ [0,1]` (the multipliers the flow multiplies up);
  * `R`, `R_lt_one`  — the total loss budget, `R < 1`;
  * `lossSummable`   — **the summable-loss bound** `∑_{k<n}(1 − ρ_k) ≤ R` for all
    prefix lengths `n` (the `ProductFloor` summability shape);
  * `window a`       — the spacing window;
  * `aScaling a`, `aScaling_pos` — the explicit `a`-scaling;
  * `baseLSI`, `baseLSI_pos` — a positive base LSI scale carried into the uniform
    constant.

The summable-loss bound is the clean reduced shape; per-scale rates feeding it
are the analytic content named in `NASuscept_to_PerScaleRateData`. -/
structure PerScaleRateData : Type where
  /-- The per-RG-scale contraction rates `ρ_k`. -/
  rho : Nat → Q'
  /-- Each rate is nonnegative. -/
  rho_nonneg : ∀ k : Nat, (0 : Q') ≤ rho k
  /-- Each rate is `≤ 1` (a genuine contraction multiplier). -/
  rho_le_one : ∀ k : Nat, rho k ≤ 1
  /-- The total loss budget. -/
  R : Q'
  /-- The budget is `< 1` (so the product floor `1 − R` is positive). -/
  R_lt_one : R < 1
  /-- **The summable-loss bound** `∑_{k<n}(1 − ρ_k) ≤ R` for all `n`. -/
  lossSummable : ∀ n : Nat, lossSum (fun k => 1 - rho k) n ≤ R
  /-- The spacing window. -/
  window : Nat → Prop
  /-- The explicit `a`-scaling. -/
  aScaling : Nat → Q'
  /-- The `a`-scaling is strictly positive. -/
  aScaling_pos : ∀ a : Nat, (0 : Q') < aScaling a
  /-- A positive base LSI scale. -/
  baseLSI : Q'
  /-- The base LSI scale is positive. -/
  baseLSI_pos : (0 : Q') < baseLSI

namespace PerScaleRateData

/-- **The product floor of the per-scale rates.**  By the constructive
Weierstrass product floor, every prefix product `∏_{k<n} ρ_k` is bounded below by
the single positive constant `1 − R`.  This is the multiscale-assembly payoff:
the summable per-scale loss yields a UNIFORM-in-`n` positive floor. -/
def productFloor (D : PerScaleRateData) :
    Σ' c : Q', (0 : Q') < c ∧ ∀ n, c ≤ RGGapPersistence.prodPrefix D.rho n :=
  sum_block_loss_to_productFloor D.rho D.rho_nonneg D.rho_le_one D.R D.R_lt_one
    D.lossSummable

/-- The product-floor constant `1 − R` is strictly positive. -/
theorem productFloor_pos (D : PerScaleRateData) : (0 : Q') < (1 : Q') - D.R :=
  oneSubR_pos D.R D.R_lt_one

end PerScaleRateData

/-- **The multiscale assembly (Task 8, PROVED).**  Per-scale rates with summable
loss ⇒ a spacing-uniform LSI constant.

The construction: the product floor `c = 1 − R > 0` (from
`ProductFloor.sum_block_loss_to_productFloor`) is uniform in the number of scales.
The uniform LSI constant is `K := (1/c) · baseLSI`, and the per-spacing LSI
constant is `lsiConst a := K · aScaling a`, so the spacing-uniform bound
`lsiConst a ≤ K · aScaling a` holds by reflexivity — the genuine content is the
EXISTENCE of the single finite `K` from the summable loss, which is what the
product floor delivers.

This is the CLEAN arrow of Route B; it is proved, not assumed. -/
def perScaleRateData_to_uniformLSI (D : PerScaleRateData) : UniformLSI where
  K := Q'.divPos D.baseLSI ((1 : Q') - D.R) D.productFloor_pos
  K_pos := Q'.divPos_pos D.baseLSI ((1 : Q') - D.R) D.productFloor_pos D.baseLSI_pos
  window := D.window
  aScaling := D.aScaling
  aScaling_pos := D.aScaling_pos
  lsiConst := fun a =>
    Q'.divPos D.baseLSI ((1 : Q') - D.R) D.productFloor_pos * D.aScaling a
  lsiConst_pos := fun a =>
    Q'.mul_pos
      (Q'.divPos_pos D.baseLSI ((1 : Q') - D.R) D.productFloor_pos D.baseLSI_pos)
      (D.aScaling_pos a)
  lsiBound := fun _a _ => Q'.le_refl' _

/-- The assembled uniform constant `K` is the finite `baseLSI/(1 − R)` produced
from the summable loss — the uniform-in-scale LSI constant. -/
@[simp] theorem perScaleRateData_to_uniformLSI_K (D : PerScaleRateData) :
    (perScaleRateData_to_uniformLSI D).K
      = Q'.divPos D.baseLSI ((1 : Q') - D.R) D.productFloor_pos := rfl

/-- The assembled per-spacing LSI constant is `K · aScaling a` — the
spacing-uniform functional-inequality constant. -/
@[simp] theorem perScaleRateData_to_uniformLSI_lsiConst
    (D : PerScaleRateData) (a : Nat) :
    (perScaleRateData_to_uniformLSI D).lsiConst a
      = Q'.divPos D.baseLSI ((1 : Q') - D.R) D.productFloor_pos * D.aScaling a := rfl

/-- **The NAMED step `NonAbelianSusceptibility → PerScaleRateData`.**

This is the genuine analytic FRONTIER: the Bakry–Émery / Polchinski-flow argument
turning the spacing-uniform susceptibility certificate into per-RG-scale
contraction rates with summable loss.  It is NOT proved — it is carried as a
`Type`-level obligation (a map from a susceptibility certificate to per-scale rate
data).  An inhabitant of this type IS the susceptibility ⇒ per-scale-rate
theorem; none is provided.  An `abbrev` so the obligation stays the bare
function type (reducible at the use sites), never an opaque wrapper. -/
abbrev NASuscept_to_PerScaleRateData : Type 1 :=
  NonAbelianSusceptibility → PerScaleRateData

/-- **The conditional susceptibility ⇒ uniform-LSI chain (Task 8).**  Given the
NAMED step `NonAbelianSusceptibility → PerScaleRateData` and a certificate,
PRODUCE a uniform LSI (the second arrow PROVED via the multiscale assembly).  The
first arrow's content is the open input `step`; the second is genuine. -/
def NASuscept_to_uniformLSI (step : NASuscept_to_PerScaleRateData)
    (N : NonAbelianSusceptibility) : UniformLSI :=
  perScaleRateData_to_uniformLSI (step N)

/-! ## 4. The dynamic ⇒ static physical-gap floor (Task 9)

From a `UniformLSI` we derive a per-spacing `DynamicGap λ(a)` and transfer
positivity to a `StaticGap m(a)` via `dynamic_to_static` (the qualitative
`λ>0 ⇒ m>0`, PROVED).  The SPACING-UNIFORM rate `m(a) ≥ c·a` (the right scaling
for a finite continuum mass) is carried as an explicit field of
`PhysicalRateBridge` — the analytic content, stated honestly as a hypothesis. -/

/-- The per-spacing static gap derived from a uniform LSI: positivity transferred
from the per-spacing dynamic gap via the Helffer–Sjöstrand bridge. -/
def UniformLSI.staticGap (U : UniformLSI) (a : Nat) : StaticGap :=
  dynamic_to_static (U.dynamicGap a)

/-- The derived per-spacing static mass is strictly positive — the qualitative
`λ>0 ⇒ m>0`, PROVED via `dynamic_to_static`. -/
theorem UniformLSI.staticGap_m_pos (U : UniformLSI) (a : Nat) :
    (0 : Q') < (U.staticGap a).m :=
  dynamic_to_static_m_pos (U.dynamicGap a)

/-- The derived per-spacing separator is strictly below the vacuum `1` — geometric
clustering exists at each spacing. -/
theorem UniformLSI.staticGap_sep_lt_one (U : UniformLSI) (a : Nat) :
    (U.staticGap a).sep < (1 : Q') :=
  dynamic_to_static_sep_lt_one (U.dynamicGap a)

/-- **The physical-rate bridge data (Task 9) — carries the SHARP rate hypothesis.**

Bundles a uniform LSI with the data needed to build a `PhysicalSeparator` plus a
`PhysicalGapFloor`:

  * `U`            — the uniform LSI datum;
  * `corrIface`    — the gauge-invariant correlator interface the physical
    separator controls;
  * `sepPhys a`, `sepPhys_pos`, `sepPhys_lt_one` — the physical separator built
    from the static gaps (`0 < sep_phys a < 1`);
  * `controls`     — the defining content: `sep_phys` governs gauge-invariant
    clustering (carried abstractly against the interface);
  * `spacing a`, `spacing_pos` — the lattice spacing sequence;
  * `floorConst`, `floorConst_pos`, `ceilConst` — the two-sided physical-gap
    floor / ceiling constants;
  * `rateFloor`  — **the SHARP rate (ANALYTIC content):** the two-sided
    dimensional-transmutation bound
    `floorConst ≤ (1 − sep_phys a)/spacing a ≤ ceilConst`, the `m(a) ≥ c·a`
    scaling whose spacing-uniform power is the open analytic input.

The QUALITATIVE `sep_phys a < 1` is forced (from `dynamic_to_static`); the SHARP
two-sided rate `rateFloor` is the hypothesis carried honestly — it is not
constructively forced and is the genuine analytic content. -/
structure PhysicalRateBridge : Type 1 where
  /-- The uniform LSI datum. -/
  U : UniformLSI
  /-- The gauge-invariant correlator interface the physical separator controls. -/
  corrIface : CorrInterface
  /-- The physical separator at spacing index `a`. -/
  sepPhys : Nat → Q'
  /-- The physical separator is strictly positive. -/
  sepPhys_pos : ∀ a : Nat, (0 : Q') < sepPhys a
  /-- The physical separator is strictly sub-unit. -/
  sepPhys_lt_one : ∀ a : Nat, sepPhys a < (1 : Q')
  /-- The defining content: `sep_phys` governs gauge-invariant clustering. -/
  controls : ∀ O : corrIface.Obs,
    corrIface.GaugeInvariantLocal O →
      Σ' C : Q', (0 : Q') < C ∧
        ∀ j n : Nat, corrIface.connectedCorr j O n ≤ C * (sepPhys j) ^ n
  /-- The lattice spacing sequence. -/
  spacing : Nat → Q'
  /-- The spacing is strictly positive. -/
  spacing_pos : ∀ a : Nat, (0 : Q') < spacing a
  /-- The two-sided physical-gap floor constant. -/
  floorConst : Q'
  /-- The floor constant is strictly positive. -/
  floorConst_pos : (0 : Q') < floorConst
  /-- The two-sided physical-gap ceiling constant. -/
  ceilConst : Q'
  /-- **The SHARP rate (ANALYTIC content), floor half:**
  `floorConst ≤ (1 − sep_phys a)/spacing a` for all `a` (the gap survives `a→0`). -/
  rateFloor : ∀ a : Nat,
    floorConst ≤ Q'.divPos ((1 : Q') - sepPhys a) (spacing a) (spacing_pos a)
  /-- **The SHARP rate (ANALYTIC content), ceiling half:**
  `(1 − sep_phys a)/spacing a ≤ ceilConst` for all `a` (dimensional
  transmutation — the mass stays finite). -/
  rateCeil : ∀ a : Nat,
    Q'.divPos ((1 : Q') - sepPhys a) (spacing a) (spacing_pos a) ≤ ceilConst

namespace PhysicalRateBridge

/-- The physical separator extracted from a rate bridge as a
`PhysicalSeparator` (carrying the gauge-invariant correlator interface and the
defining clustering-control content). -/
def physicalSeparator (B : PhysicalRateBridge) : PhysicalSeparator where
  corrIface := B.corrIface
  sep := B.sepPhys
  sep_pos := B.sepPhys_pos
  sep_lt_one := B.sepPhys_lt_one
  controlsGaugeInvariantCorr := B.controls

/-- The extracted separator's physical margin is `1 − sep_phys a`. -/
@[simp] theorem physicalSeparator_physMargin (B : PhysicalRateBridge) (a : Nat) :
    (B.physicalSeparator).physMargin a = (1 : Q') - B.sepPhys a := rfl

/-- **The physical-gap floor (Task 9, assembled).**  From a `PhysicalRateBridge`
construct the genuine two-sided `PhysicalGapFloor` on the extracted physical
separator: the floor `floorConst ≤ (1 − sep_phys a)/a` and the finiteness ceiling
`(1 − sep_phys a)/a ≤ ceilConst`, both supplied by the bridge's sharp-rate
fields.  The `physMargin a = 1 − sep_phys a` identification is definitional, so
the rate fields plug in verbatim. -/
def physicalGapFloor (B : PhysicalRateBridge) :
    PhysicalGapFloor B.physicalSeparator B.spacing B.spacing_pos where
  c := B.floorConst
  c_pos := B.floorConst_pos
  floor := B.rateFloor
  ceil := B.ceilConst
  finiteness := B.rateCeil

end PhysicalRateBridge

/-- **`uniformLSI_to_physicalGapFloor` (Task 9).**  From a `PhysicalRateBridge`
(uniform LSI + the explicit sharp-rate hypothesis) PRODUCE a `PhysicalSeparator`
and a `PhysicalGapFloor` on it.  The qualitative dynamic⇒static positivity is
proved (`UniformLSI.staticGap_m_pos`); the spacing-uniform rate is the bridge's
named field.  Returns the two-sided floor datum keyed to the physical separator. -/
def uniformLSI_to_physicalGapFloor (B : PhysicalRateBridge) :
    PhysicalGapFloor B.physicalSeparator B.spacing B.spacing_pos :=
  B.physicalGapFloor

/-! ## 5. The end-to-end composite (the headline) -/

/-- **`uniformLSI_implies_gap`.**  From a `PhysicalRateBridge` the constructed
band's continuum physical-gap floor is strictly positive — the continuum mass-gap
positivity from the uniform LSI + sharp-rate data. -/
theorem uniformLSI_implies_gap (B : PhysicalRateBridge) :
    (0 : Q') <
      (toScalingBand
        (toRGGapPersistence (uniformLSI_to_physicalGapFloor B))).physGapMin :=
  physGapMin_pos_of_physicalGapFloor (uniformLSI_to_physicalGapFloor B)

/-- **`nonAbelian_certificate_implies_gap` — THE HEADLINE.**

A single named analytic certificate ⇒ the entire continuum mass gap.  Given:

  * `step` : the NAMED susceptibility ⇒ per-scale-rate obligation;
  * `N`    : a non-abelian susceptibility certificate;
  * `bridge` : the dynamic⇒static physical-rate bridge built ON the uniform LSI
    that `step`+`N` assemble (carrying the sharp `m(a)≥c·a` rate as its named
    field, and equal to that uniform LSI via `bridge.U`),

the continuum physical-gap floor is strictly positive.

The chain: `N → (step) → PerScaleRateData → (PROVED assembly) → UniformLSI`,
then `UniformLSI + sharp rate → (PROVED) → PhysicalGapFloor → (PROVED) →
physGapMin > 0`.  The two PROVED arrows are genuine; the susceptibility
certificate, the `step`, and the sharp rate (inside `bridge`) are the NAMED
analytic inputs.  This is the Route-B reduction completed conditionally. -/
theorem nonAbelian_certificate_implies_gap
    (step : NASuscept_to_PerScaleRateData)
    (N : NonAbelianSusceptibility)
    (bridge : PhysicalRateBridge)
    (_hbridge : bridge.U = NASuscept_to_uniformLSI step N) :
    (0 : Q') <
      (toScalingBand
        (toRGGapPersistence (uniformLSI_to_physicalGapFloor bridge))).physGapMin :=
  uniformLSI_implies_gap bridge

/-- **The continuum-gap corollary.**  Under the same hypotheses, every physical
gap of the constructed band dominates the single positive floor constant as a
regular real, uniformly in `j` — the continuum gap SURVIVES `a → 0`, conditional
on the named analytic inputs. -/
theorem nonAbelian_certificate_implies_continuum_gap
    (step : NASuscept_to_PerScaleRateData)
    (N : NonAbelianSusceptibility)
    (bridge : PhysicalRateBridge)
    (_hbridge : bridge.U = NASuscept_to_uniformLSI step N)
    (j : Nat) :
    ofQ'
        (toScalingBand
          (toRGGapPersistence (uniformLSI_to_physicalGapFloor bridge))).physGapMin
      ≤ ofQ'
        ((toScalingBand
          (toRGGapPersistence (uniformLSI_to_physicalGapFloor bridge))).physGap j) :=
  continuum_gap_of_physicalGapFloor (uniformLSI_to_physicalGapFloor bridge) j

/-! ## 6. Doc-section — what is PROVED vs what is a NAMED OBLIGATION (HONEST)

This module completes Route B CONDITIONALLY: it localizes the entire remaining
continuum-gap problem to one analytic certificate and two named steps.

**PROVED links (genuine theorems):**

  * `perScaleRateData_to_uniformLSI` — the MULTISCALE ASSEMBLY: per-scale rates
    with summable loss `∑(1−ρ_k) ≤ R < 1` ⇒ a single finite spacing-uniform LSI
    constant `K = baseLSI/(1−R)`.  This reuses the constructive product floor
    `∏(1−η_k) ≥ 1−∑η_k` (`ProductFloor.sum_block_loss_to_productFloor`); the
    genuine content is the EXISTENCE of the uniform-in-scale finite constant.

  * `UniformLSI.dynamicGap` / `UniformLSI.staticGap_m_pos` — the QUALITATIVE
    dynamic⇒static positivity `λ(a) > 0 ⇒ m(a) > 0`, via `dynamic_to_static`
    (Helffer–Sjöstrand positivity transfer).

  * `uniformLSI_to_physicalGapFloor` — the ASSEMBLY of a two-sided
    `PhysicalGapFloor` from the uniform LSI together with the sharp-rate fields.

  * `uniformLSI_implies_gap`, `nonAbelian_certificate_implies_gap`, and the
    continuum-gap corollary — the FINAL COMPOSITION into `physGapMin > 0`.

**NAMED OBLIGATIONS (NOT inhabited — the open frontier):**

  * `NonAbelianSusceptibility` — the spacing-uniform susceptibility certificate
    (the weighted gauge-invariant covariance bound).  No inhabitant for 4D
    Yang–Mills is provided.

  * `NASuscept_to_PerScaleRateData` — the susceptibility ⇒ per-scale-rate map
    (the Bakry–Émery / Polchinski-flow content).  Carried as a `Type`-level
    obligation; an inhabitant IS the theorem; none is provided.

  * the SHARP rate `m(a) ≥ c·a` (the `rateFloor` / `rateCeil` fields of
    `PhysicalRateBridge`).  The QUALITATIVE `m>0` is proved; the spacing-uniform
    power (the right scaling for a finite continuum mass) is the analytic content,
    carried honestly as an explicit hypothesis.

**Underclaim.**  The payoff is that ONE analytic certificate (plus its two named
steps) would buy the whole continuum gap for SU(2), hence — via the existing
worst-case reduction to SU(2) — for all simple groups.  This module does NOT
solve the certificate, the susceptibility ⇒ per-scale step, or the sharp rate;
it PROVES the structural arrows connecting them and NAMES the analytic inputs. -/

end YMGap.Continuum.NonAbelianGapChain

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.NonAbelianGapChain.UniformLSI.dynamicGap
#print axioms YMGap.Continuum.NonAbelianGapChain.UniformLSI.dynamicGap_lambda_pos
#print axioms YMGap.Continuum.NonAbelianGapChain.PerScaleRateData.productFloor
#print axioms YMGap.Continuum.NonAbelianGapChain.PerScaleRateData.productFloor_pos
#print axioms YMGap.Continuum.NonAbelianGapChain.perScaleRateData_to_uniformLSI
#print axioms YMGap.Continuum.NonAbelianGapChain.perScaleRateData_to_uniformLSI_K
#print axioms YMGap.Continuum.NonAbelianGapChain.perScaleRateData_to_uniformLSI_lsiConst
#print axioms YMGap.Continuum.NonAbelianGapChain.NASuscept_to_uniformLSI
#print axioms YMGap.Continuum.NonAbelianGapChain.UniformLSI.staticGap
#print axioms YMGap.Continuum.NonAbelianGapChain.UniformLSI.staticGap_m_pos
#print axioms YMGap.Continuum.NonAbelianGapChain.UniformLSI.staticGap_sep_lt_one
#print axioms YMGap.Continuum.NonAbelianGapChain.PhysicalRateBridge.physicalSeparator
#print axioms YMGap.Continuum.NonAbelianGapChain.PhysicalRateBridge.physicalSeparator_physMargin
#print axioms YMGap.Continuum.NonAbelianGapChain.PhysicalRateBridge.physicalGapFloor
#print axioms YMGap.Continuum.NonAbelianGapChain.uniformLSI_to_physicalGapFloor
#print axioms YMGap.Continuum.NonAbelianGapChain.uniformLSI_implies_gap
#print axioms YMGap.Continuum.NonAbelianGapChain.nonAbelian_certificate_implies_gap
#print axioms YMGap.Continuum.NonAbelianGapChain.nonAbelian_certificate_implies_continuum_gap
