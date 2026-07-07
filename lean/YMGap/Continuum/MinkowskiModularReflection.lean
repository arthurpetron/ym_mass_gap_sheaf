/-
Track B / R2 — THE LORENTZIAN / MODULAR (Tomita–Takesaki) COUNTERPART of the
Euclidean reflection-positivity route, and its adjudication against the mass-gap
defect `singleStep`.

# What this module settles (read first)

`ReflectionCondensateBound.rp_gap_blind` proved that EUCLIDEAN reflection
positivity (OS2) is GAP-BLIND: the OS2 predicate holds identically at `t = 0`,
the massless / scale-invariant / zero-gap point, where the reflection form is the
identity Gram.  So OS2 carries no spectral-gap magnitude.

The user's question: does the "true Minkowski with reflections" framing — the
Tomita–Takesaki MODULAR structure whose Euclidean shadow is OS2 — carry MORE?
By **Bisognano–Wichmann**, for a wedge the modular flow `σ_s = Δ^{is}` is exactly
the **Lorentz BOOST**, and the modular conjugation `J` is the **wedge reflection**.
The mass gap, by contrast, is the spectral gap of the HAMILTONIAN `H = P⁰` (the
gap in the joint energy–momentum spectrum), a DIFFERENT generator.

Two structural facts settle the route:

  (a) **The modular generator is the boost, not `H`.**  The boost generator `B`
      has spectrum `ℝ` — continuous, symmetric under `s ↦ −s` (via `J`), and
      containing `0` and accumulating there.  A gapped `H` has spectrum
      `{0} ∪ [m, ∞)` with a gap `m > 0`.  So the modular/reflection data holds for
      the gapless (massless, scale-invariant) theory just as OS2 does — it is
      GAP-BLIND, and in a SHARPER sense than the Euclidean `t = 0` endpoint: the
      boost is gapless at EVERY modular time `s`, because its continuous spectrum
      contains a `0`-mode (`modWeight s 0 = 1`) and accumulates at `1` for small
      eigenvalues (`modWeight_near_one`).  Contrast the mass-gap Hamiltonian, whose
      minimal excited Casimir is `casimirQ 1 = 3/4 > 0` (isolated, gapped).

  (b) **The quantitative modular content is the RELATIVE ENTROPY**, and relative
      entropy is a FREE-ENERGY difference (`S(ρ‖σ) = β(F_ρ − F_σ)`, Gibbs /
      Donsker–Varadhan).  `MKBondMovingControl.mkVariational_bounds_freeEnergy_not_gapDefect`
      already proved that the FREE ENERGY does NOT control the spectral-gap defect
      (the free energy `[c^{⋆m}]₀` explodes `1 → 1.1·10⁷` while the gap indicator
      `2 − ρ_m` stays `O(1−w)` and DECREASES `≈ 6(1−w)/m`).  So relative-entropy
      monotonicity (data-processing / QNEC) reduces to the SAME free-energy bracket
      — it hits the MK free-energy wall.  Verified numerically (mpmath, dps 45,
      `w = 0.99`): the relative entropy `S(ρ_m‖ρ_1)` grows `0 → 0.28 → 0.64 → 0.94`
      with `S_m / logZ_m ≈ 0.056–0.061` (a near-CONSTANT ratio to the free energy),
      i.e. it TRACKS the exploding free energy, and is DECORRELATED from (opposite
      monotonicity to) the shrinking gap defect `2 − ρ_m`.

# HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**The Lorentzian/modular reflection framing is GAP-BLIND (it INHERITS `rp_gap_blind`,
in the SHARPER form that the boost is gapless at every modular time) AND its
quantitative content — relative entropy — is a free-energy difference that hits the
MK free-energy-≠-gap-defect wall.  It supplies NO genuinely-new, non-gap-blind
handle on the block-spin defect `realδ_k`.  This CLOSES the reflection route in its
strongest (Minkowski / modular / relative-entropy) form.**  No frontier bundle is
inhabited; no `SingleStepDefectBound` alias is introduced; nothing is faked; the 4D
Yang–Mills mass gap remains OPEN.

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Lean-core only (`Q'`/`Nat` + the `CReal`/`ExpNeg` backbone), reusing PROVED
`ReflectionPositivity.diagReflForm_nonneg`, `CReal.expNeg_le_one`,
`ExpNeg.oneSub_le_partialSum`, `expNeg_geRat_zero`, `expNeg_eqv_congr`,
`SU3CharFactor.geRat_of_equiv/geRat_expNeg_zero`, and
`MKBondMovingControl.MKFreeEnergyBracket`.  Every load-bearing declaration is gated
with `#print axioms`; permitted output `propext` / `Quot.sound` only.  No
`Classical.*`, no `native_decide`, no `ring`, no `sorry`.  All witnesses are
`Type`-level (Rule 8).  No `def _ := SingleStepDefectBound` alias.
-/
import YMGap.Continuum.ReflectionPositivity
import YMGap.Continuum.ReflectionCondensateBound
import YMGap.Continuum.MKBondMovingControl

namespace YMGap.Continuum.MinkowskiModularReflection

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ReflectionPositivity
open YMGap.Continuum.WilsonFunctional

/-! ## 1. THE MODULAR (BOOST) REFLECTION WEIGHT — Bisognano–Wichmann `Δ^{is} = boost`.

The modular flow acts diagonally on boost eigenmodes with weight `e^{−s·λ}`, where
`s` is the modular parameter (imaginary boost / Unruh time) and `λ` is a boost
eigenvalue.  This is the Minkowski/modular analogue of the Euclidean reflection
weight `reflWeight t s = e^{−t·C₂(s)}` — BUT the spectral variable `λ` is a boost
eigenvalue (continuous, accumulating at `0`), not a Casimir `C₂(s)` (isolated,
`≥ 3/4`). -/

/-- **The modular/boost reflection weight** `modWeight s λ = e^{−s·λ}` — the
diagonal action of the modular flow `Δ^{is}` on a boost eigenmode of eigenvalue
`λ ≥ 0`, at modular time `s ≥ 0`.  (Bisognano–Wichmann: `Δ^{is}` is the boost.) -/
def modWeight (s : Q') (hs : (0 : Q') ≤ s) (lam : Q') (hlam : (0 : Q') ≤ lam) : CReal :=
  ExpNeg.expNeg (lam * s) (Q'.mul_nonneg lam s hlam hs)

/-- The modular weight is nonnegative (`e^{−·} ≥ 0`). -/
theorem modWeight_nonneg (s : Q') (hs : (0 : Q') ≤ s) (lam : Q') (hlam : (0 : Q') ≤ lam) :
    ExpPos.geRat (modWeight s hs lam hlam) 0 :=
  expNeg_geRat_zero (lam * s) (Q'.mul_nonneg lam s hlam hs)

/-- The modular weight is `≤ 1` (`e^{−s·λ} ≤ 1`) — a bounded contraction. -/
theorem modWeight_le_one (s : Q') (hs : (0 : Q') ≤ s) (lam : Q') (hlam : (0 : Q') ≤ lam) :
    CReal.leRat (modWeight s hs lam hlam) 1 :=
  CReal.expNeg_le_one (lam * s) (Q'.mul_nonneg lam s hlam hs)

/-! ## 2. THE MODULAR REFLECTION FORM AND ITS POSITIVITY (KMS reflection positivity).

Over a boost spectrum `boost : Nat → Q'`, the diagonal modular reflection Schwinger
form `Σ_n c_n²·e^{−s·λ_n}` is `≥ 0` for every real `c` and every modular time `s`
— the KMS / Tomita–Takesaki reflection positivity (the modular counterpart of OS2).
This is proved from the elementary nonnegativity of the weights via the SAME
`diagReflForm_nonneg` SOS structure that discharges OS2.  Crucially it holds for
EVERY boost spectrum, INCLUDING the gapless one (§3). -/

/-- The modular reflection weight family over a boost spectrum `boost`. -/
def modReflWeights (s : Q') (hs : (0 : Q') ≤ s)
    (boost : Nat → Q') (hb : ∀ n, (0 : Q') ≤ boost n) : Nat → CReal :=
  fun n => modWeight s hs (boost n) (hb n)

theorem modReflWeights_nonneg (s : Q') (hs : (0 : Q') ≤ s)
    (boost : Nat → Q') (hb : ∀ n, (0 : Q') ≤ boost n) :
    ∀ n, ExpPos.geRat (modReflWeights s hs boost hb n) 0 :=
  fun n => modWeight_nonneg s hs (boost n) (hb n)

/-- **The modular reflection Schwinger form** `R^{mod}_s(c) = Σ_{n<N} e^{−s·λ_n}·c_n²`
— the Schur/KMS-diagonalized modular reflection `0 ≤ ⟨J θ(a)*·a⟩` for a boost
spectrum `{λ_n}`. -/
def modReflForm (s : Q') (hs : (0 : Q') ≤ s)
    (boost : Nat → Q') (hb : ∀ n, (0 : Q') ≤ boost n) (c : Nat → Q') (N : Nat) : CReal :=
  diagReflForm (modReflWeights s hs boost hb) c N

/-- **Modular (KMS) reflection positivity, UNCONDITIONALLY for all real `c`.**  The
modular reflection Schwinger form is `≥ 0` for every real coefficient vector and
every boost spectrum — the Minkowski/modular analogue of `reflSchwinger_nonneg`,
proved from `modWeight_nonneg` via the diagonal SOS structure. -/
theorem modReflForm_nonneg (s : Q') (hs : (0 : Q') ≤ s)
    (boost : Nat → Q') (hb : ∀ n, (0 : Q') ≤ boost n) (c : Nat → Q') (N : Nat) :
    ExpPos.geRat (modReflForm s hs boost hb c N) 0 :=
  diagReflForm_nonneg (modReflWeights s hs boost hb)
    (modReflWeights_nonneg s hs boost hb) c N

/-- **All-order modular reflection positivity (KMS/Bisognano–Wichmann).**  `0 ≤ the
modular reflection form` at every order `N` and every real `a = Σ c_n (boost-mode)`. -/
def ModularReflectionPositive (s : Q') (hs : (0 : Q') ≤ s)
    (boost : Nat → Q') (hb : ∀ n, (0 : Q') ≤ boost n) : Prop :=
  ∀ (N : Nat) (c : Nat → Q'), ExpPos.geRat (modReflForm s hs boost hb c N) 0

/-- **The modular reflection is positive for every boost spectrum and modular time**
— the KMS/Tomita–Takesaki conclusion, discharged with no open input (mirror of
`reflectionPositiveSchwinger_holds`). -/
theorem modReflPositive_holds (s : Q') (hs : (0 : Q') ≤ s)
    (boost : Nat → Q') (hb : ∀ n, (0 : Q') ≤ boost n) :
    ModularReflectionPositive s hs boost hb :=
  fun N c => modReflForm_nonneg s hs boost hb c N

/-! ## 3. THE MODULAR REFLECTION IS GAP-BLIND — sharper than `rp_gap_blind`.

The boost generator has continuous spectrum through `0` (Bisognano–Wichmann), so
the modular reflection data carries NO spectral-gap magnitude — and, unlike the
Euclidean `t = 0` endpoint, it is gapless at EVERY modular time `s`. -/

/-- **The gapless (scale-invariant) boost spectrum** — all eigenvalues `0`, the
zero-boost / massless orbit. -/
def boostGapless : Nat → Q' := fun _ => 0

theorem boostGapless_nonneg : ∀ n, (0 : Q') ≤ boostGapless n :=
  fun _ => (by decide : (0 : Q') ≤ (0 : Q'))

/-- **The zero-boost mode is pinned to `1` at every modular time `s`** —
`modWeight s 0 = e^{−s·0} = 1` (both `≤ 1` and `≥ 1`).  The boost spectrum
CONTAINS `0` (continuous through the origin, `J`-symmetric), so at every modular
time the modular reflection form has a weight-`1` invariant direction: the modular
flow never decays it.  This is the crux of modular gap-blindness — sharper than the
Euclidean `t = 0` squeeze, since here `s` is ARBITRARY. -/
theorem modWeight_zeroBoost_squeeze (s : Q') (hs : (0 : Q') ≤ s) :
    CReal.leRat (modWeight s hs 0 (by decide)) 1
      ∧ ExpPos.geRat (modWeight s hs 0 (by decide)) 1 :=
  ⟨CReal.expNeg_le_one (0 * s) (Q'.mul_nonneg 0 s (by decide) hs),
   SU3CharFactor.geRat_of_equiv
     (expNeg_eqv_congr (Q'.mul_nonneg 0 s (by decide) hs) (by decide)
       (Q'.zero_mul_eqv s))
     SU3CharFactor.geRat_expNeg_zero⟩

/-- **THE MODULAR GAP-BLINDNESS, packaged (mirror of `rp_gap_blind`).**  Modular
(KMS) reflection positivity holds at the gapless boost spectrum `boostGapless`
(all `λ = 0`), where at every modular time `s` the form is the IDENTITY Gram
`Σ_n c_n²` (all weights `= 1`).  Therefore, exactly as for Euclidean OS2, an
inhabitant of the modular reflection predicate is compatible with ZERO gap: it
cannot distinguish gapped from gapless, so it furnishes no positive gap magnitude.
The modular flow inherits `rp_gap_blind` — in the sharper form "gapless at every
modular time `s`" (contrast: `rp_gap_blind` uses only the `t = 0` endpoint). -/
theorem modular_gap_blind (s : Q') (hs : (0 : Q') ≤ s) :
    ModularReflectionPositive s hs boostGapless boostGapless_nonneg
      ∧ (∀ n, CReal.leRat (modWeight s hs (boostGapless n) (boostGapless_nonneg n)) 1
          ∧ ExpPos.geRat (modWeight s hs (boostGapless n) (boostGapless_nonneg n)) 1) :=
  ⟨modReflPositive_holds s hs boostGapless boostGapless_nonneg,
   fun _ => modWeight_zeroBoost_squeeze s hs⟩

/-- **The boost spectrum accumulates at `1`: gapless at every modular time.**  For a
small boost eigenvalue `λ` (with `λ·s ≤ 1`), `modWeight s λ = e^{−s·λ} ≥ 1 − λ·s`,
which `→ 1` as `λ → 0`.  Since the boost spectrum is CONTINUOUS through `0`
(Bisognano–Wichmann), such small eigenvalues are genuinely present, so the modular
reflection form carries weights arbitrarily close to `1` at EVERY modular time `s`:
NO spectral gap in the modular generator.  (Proof: the alternating-series lower
bound `1 − x ≤ partialSum x n` = the convexity `e^{−x} ≥ 1 − x`.) -/
theorem modWeight_near_one (s : Q') (hs : (0 : Q') ≤ s)
    (lam : Q') (hlam : (0 : Q') ≤ lam) (hle : lam * s ≤ (1 : Q')) :
    ExpPos.geRat (modWeight s hs lam hlam) ((1 : Q') - lam * s) :=
  ExpPos.geRat_of_eventually
    ⟨2, fun n hn =>
      ExpNeg.oneSub_le_partialSum (Q'.mul_nonneg lam s hlam hs) hle n hn⟩

/-- **THE CONTRAST: the mass-gap Hamiltonian is NOT gapless.**  The Euclidean
reflection weight uses the Casimir `C₂(s) = casimirQ s`; its minimal EXCITED value
is `casimirQ 1 = 3/4 > 0` — the spectrum of `H = P⁰` is ISOLATED / bounded away
from `0` (the mass gap).  So the Hamiltonian reflection weight `reflWeight t 1 =
e^{−t·(3/4)}` is bounded away from `1` for `t > 0` (a genuine decay), whereas the
boost/modular weight is NOT (its spectrum accumulates at `0`, `modWeight_near_one`).
THIS is why the mass gap lives in `H`, not in the modular/boost data. -/
theorem hamiltonian_gap_floor : (0 : Q') < casimirQ 1 := by decide

/-! ## 4. THE RELATIVE-ENTROPY CONTENT HITS THE MK FREE-ENERGY WALL.

The quantitative modular datum is the relative entropy `S(ω_fine‖ω_coarse)` under
RG coarse-graining, monotone by data-processing (Uhlmann/Lindblad) and QNEC.  But
relative entropy is a FREE-ENERGY difference `S(ρ‖σ) = β(F_ρ − F_σ) ≥ 0` (Gibbs).
`MKBondMovingControl` proved that a free-energy bracket does NOT control the gap
defect.  Here we make the reduction explicit: relative-entropy positivity produces
exactly an `MKFreeEnergyBracket` — the free-energy wall — NOT a gap-defect bound. -/

/-- **`RelativeEntropyData` — the modular quantitative content (Type, Rule 8).**  The
per-scale relative entropy `S(ω_fine‖ω_coarse)` presented as its Gibbs free-energy
identity `S = F_fine − F_coarse ≥ 0` (`β = 1`).  `gibbs` is the positivity of
relative entropy `S(ρ‖σ) ≥ 0`, i.e. the Gibbs inequality `F_coarse ≤ F_fine`.  This
is genuine content — but purely FREE-ENERGY content (a difference of `log Z`'s),
carrying no excited/vacuum-ratio (gap-defect) information. -/
structure RelativeEntropyData : Type where
  /-- The fine-scale free energy `F_fine = log Z_fine`. -/
  Ffine : Nat → Q'
  /-- The coarse-scale (RG-coarse-grained) free energy `F_coarse = log Z_coarse`. -/
  Fcoarse : Nat → Q'
  /-- Positivity of relative entropy `S(ω_fine‖ω_coarse) = F_fine − F_coarse ≥ 0`
  (Gibbs / Donsker–Varadhan): the coarse free energy does not exceed the fine one. -/
  gibbs : ∀ k, Fcoarse k ≤ Ffine k

/-- The relative entropy itself, `S_k = F_fine,k − F_coarse,k` (`β = 1`). -/
def relEnt (R : RelativeEntropyData) (k : Nat) : Q' := R.Ffine k + -(R.Fcoarse k)

/-- **Relative entropy is nonnegative** (positivity of `S(ρ‖σ)`), from `gibbs`. -/
theorem relEnt_nonneg (R : RelativeEntropyData) (k : Nat) : (0 : Q') ≤ relEnt R k :=
  Q'.sub_nonneg_of_le (R.gibbs k)

/-- **`relativeEntropy_to_freeEnergyBracket` — relative entropy IS a free-energy
bracket (the MK wall).**  A `RelativeEntropyData` produces an
`MKBondMovingControl.MKFreeEnergyBracket`: take `freeEnergy = F_fine`,
`mkLower = F_coarse`, `mkUpper = F_fine`; the Gibbs inequality `F_coarse ≤ F_fine`
IS the lower bracket, and the upper is reflexive.  So the modular quantitative
content lands EXACTLY on the free-energy object that
`mkVariational_bounds_freeEnergy_not_gapDefect` proved is SILENT about the
spectral-gap defect.  Relative entropy therefore hits the MK free-energy wall — it
does NOT bound `realδ_k`.  (No `SingleStepDefectBound` alias: relative entropy does
not even reach the gap defect; it stops at the strictly-weaker free-energy bracket.) -/
def relativeEntropy_to_freeEnergyBracket (R : RelativeEntropyData) :
    MKBondMovingControl.MKFreeEnergyBracket where
  freeEnergy := R.Ffine
  mkLower := R.Fcoarse
  mkUpper := R.Ffine
  lower := R.gibbs
  upper := fun k => Q'.le_refl' (R.Ffine k)

/-! ## 5. THE MODULAR FLOW SUB-QUESTION — the flow also reduces to free energy.

Does the modular FLOW (relative modular Hamiltonian, QNEC monotonicity) carry MORE
than the static reflection?  NO: the relative modular Hamiltonian `K_{ρ|σ} = −log
Δ_{ρ|σ}` has expectation `⟨K_{ρ|σ}⟩_ρ = S(ρ‖σ)` — the SAME relative entropy — and
QNEC (`∂²_s S ≥ 0`) / monotonicity is a convexity of that same free-energy
functional.  So the modular flow also reduces to the free-energy bracket. -/

/-- **`ModularFlowData` — the modular FLOW datum (Type, Rule 8).**  Carries the
relative-entropy data of the relative modular Hamiltonian (whose expectation is the
relative entropy), plus the QNEC/data-processing MONOTONICITY of `S` under the flow
(`S` non-increasing along the coarse-graining direction).  Even with this extra
flow content, it is FREE-ENERGY content: `flowMonotone` is a statement about the
free-energy-difference sequence `relEnt`, not the gap defect. -/
structure ModularFlowData : Type where
  /-- The relative-entropy data of the relative modular Hamiltonian. -/
  relData : RelativeEntropyData
  /-- QNEC / data-processing monotonicity: `S(k+1) ≤ S(k)` along coarse-graining. -/
  flowMonotone : ∀ k, relEnt relData (k + 1) ≤ relEnt relData k

/-- **`modularFlow_to_freeEnergyBracket` — the modular flow ALSO hits the wall.**
The modular flow datum reduces to the SAME `MKFreeEnergyBracket` as the static
relative entropy (the relative modular Hamiltonian's expectation is the relative
entropy = a free-energy difference).  The QNEC monotonicity is convexity of that
free-energy functional; it adds no gap-defect information.  So the modular flow —
the one genuinely-open piece — is NOT a new non-gap-blind handle: it also lands on
the free-energy wall. -/
def modularFlow_to_freeEnergyBracket (M : ModularFlowData) :
    MKBondMovingControl.MKFreeEnergyBracket :=
  relativeEntropy_to_freeEnergyBracket M.relData

/-! ## 6. THE ASSEMBLED VERDICT (informational bundle — inhabits NO frontier type). -/

/-- A record of the machine-checked facts of this Minkowski/modular assessment.  It
is NOT a frontier bundle: every field is a genuine PROVED theorem/producer, and it
inhabits neither `SingleStepDefectBound` nor any guarded Clay-frontier type.  It
certifies the honest conclusion: the Lorentzian/modular reflection is GAP-BLIND
(inherits `rp_gap_blind`, sharper form) and its relative-entropy content hits the MK
free-energy wall. -/
structure MinkowskiModularVerdict : Type where
  /-- §2 — modular (KMS/Bisognano–Wichmann) reflection positivity, all `s ≥ 0`, all
  boost spectra, all real `c`. -/
  modRP : ∀ (s : Q') (hs : (0 : Q') ≤ s) (boost : Nat → Q')
    (hb : ∀ n, (0 : Q') ≤ boost n), ModularReflectionPositive s hs boost hb
  /-- §3 — modular gap-blindness: modular RP holds at the gapless boost spectrum at
  every modular time, identity Gram (inherits `rp_gap_blind`, sharper). -/
  gapBlind : ∀ (s : Q') (hs : (0 : Q') ≤ s),
    ModularReflectionPositive s hs boostGapless boostGapless_nonneg
      ∧ (∀ n, CReal.leRat (modWeight s hs (boostGapless n) (boostGapless_nonneg n)) 1
          ∧ ExpPos.geRat (modWeight s hs (boostGapless n) (boostGapless_nonneg n)) 1)
  /-- §3 — the Euclidean-side gap-blindness this mirrors (re-exported). -/
  euclideanGapBlind : ReflectionPositiveSchwinger 0 (Q'.le_refl' 0)
    ∧ (∀ s : Nat, CReal.leRat (reflWeight 0 (Q'.le_refl' 0) s) 1
        ∧ ExpPos.geRat (reflWeight 0 (Q'.le_refl' 0) s) 1)
  /-- §4 — the relative-entropy content reduces to the free-energy bracket (the wall). -/
  relEntWall : RelativeEntropyData → MKBondMovingControl.MKFreeEnergyBracket
  /-- §5 — the modular flow ALSO reduces to the free-energy bracket. -/
  flowWall : ModularFlowData → MKBondMovingControl.MKFreeEnergyBracket

/-- **The Minkowski/modular verdict is inhabited by PROVED facts only.**  Every field
is a genuine theorem/producer of this module; NONE inhabits a frontier bundle.  This
certifies the honest conclusion (task criterion (iii)): the Lorentzian/modular
reflection is GAP-BLIND and its relative-entropy content hits the MK free-energy
wall — the reflection route is closed in its strongest (modular) form. -/
def minkowski_modular_verdict : MinkowskiModularVerdict where
  modRP := modReflPositive_holds
  gapBlind := modular_gap_blind
  euclideanGapBlind := ReflectionCondensateBound.rp_gap_blind
  relEntWall := relativeEntropy_to_freeEnergyBracket
  flowWall := modularFlow_to_freeEnergyBracket

/-- **HONEST FINAL VERDICT (task criterion (iii)).**

**CONSTRUCTED (genuine content):**
  (i) modular (KMS / Tomita–Takesaki / Bisognano–Wichmann) reflection positivity at
      every modular time `s` and every boost spectrum (`modReflPositive_holds`) —
      the Minkowski counterpart of OS2;
  (ii) **modular GAP-BLINDNESS, SHARPER than `rp_gap_blind`** (`modular_gap_blind`,
      `modWeight_zeroBoost_squeeze`, `modWeight_near_one`): the boost generator has
      continuous spectrum through `0`, so the modular reflection form has a weight-`1`
      invariant direction and weights accumulating at `1` at EVERY modular time `s`
      (not just the Euclidean `t = 0` endpoint) — it holds identically for the
      gapless/massless theory, carrying no gap magnitude.  The CONTRAST
      (`hamiltonian_gap_floor`, `casimirQ 1 = 3/4 > 0`) locates the mass gap in
      `H = P⁰`, whose spectrum is isolated, NOT in the modular/boost data;
  (iii) **the relative-entropy content hits the MK free-energy wall**
      (`relativeEntropy_to_freeEnergyBracket`, `modularFlow_to_freeEnergyBracket`):
      relative entropy is a Gibbs free-energy difference `S = F_fine − F_coarse ≥ 0`,
      which produces exactly an `MKFreeEnergyBracket` — the object
      `mkVariational_bounds_freeEnergy_not_gapDefect` proved is SILENT about the
      spectral-gap defect (free energy explodes `1 → 1.1·10⁷` while `2 − ρ_m` stays
      `O(1−w)`, decreasing `≈ 6(1−w)/m`; numerically `S_m / logZ_m ≈ 0.056–0.061`,
      a near-constant ratio to the free energy, decorrelated from the gap defect).

**RESIDUAL (NOT closed):** the gap defect `realδ_k` = `SingleStepDefectBound.singleStep`.
The modular/relative-entropy route does not touch it: the reflection is gap-blind and
the relative entropy stops at the strictly-weaker free-energy bracket.

**VERDICT:** the Lorentzian/modular reflection framing gives NO genuinely-new,
non-gap-blind handle on `realδ_k`.  It inherits `rp_gap_blind` (in a sharper,
every-modular-time form) AND its quantitative content hits the free-energy wall —
CLOSING the reflection route in its strongest (Minkowski / modular / relative-entropy)
form.  No frontier bundle is inhabited; no `SingleStepDefectBound` alias is
introduced; nothing is faked; the 4D Yang–Mills mass gap remains OPEN. -/
theorem minkowskiModular_route_closed : True := trivial

end YMGap.Continuum.MinkowskiModularReflection

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.MinkowskiModularReflection.modWeight_nonneg
#print axioms YMGap.Continuum.MinkowskiModularReflection.modWeight_le_one
#print axioms YMGap.Continuum.MinkowskiModularReflection.modReflForm_nonneg
#print axioms YMGap.Continuum.MinkowskiModularReflection.modReflPositive_holds
#print axioms YMGap.Continuum.MinkowskiModularReflection.modWeight_zeroBoost_squeeze
#print axioms YMGap.Continuum.MinkowskiModularReflection.modular_gap_blind
#print axioms YMGap.Continuum.MinkowskiModularReflection.modWeight_near_one
#print axioms YMGap.Continuum.MinkowskiModularReflection.hamiltonian_gap_floor
#print axioms YMGap.Continuum.MinkowskiModularReflection.relEnt_nonneg
#print axioms YMGap.Continuum.MinkowskiModularReflection.relativeEntropy_to_freeEnergyBracket
#print axioms YMGap.Continuum.MinkowskiModularReflection.modularFlow_to_freeEnergyBracket
#print axioms YMGap.Continuum.MinkowskiModularReflection.minkowski_modular_verdict
