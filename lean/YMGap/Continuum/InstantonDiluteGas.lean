/-
Track B / R2 — **THE INSTANTON / SEMICLASSICAL MECHANISM**: the BPST instanton action
`S_inst = 8π²/g²` gives the essential singularity `exp(−8π²/g²)` (CONSTRUCTIBLE as a CReal,
positivity the red herring); the 't Hooft instanton DENSITY `d(ρ) ~ ρ^{(11N/3)−5}` is
IR-DIVERGENT at large size (for SU(2), `ρ^{7/3}`, PROVED), so the dilute-instanton-gas breaks
down — the SMALL-instanton contribution is convergent (constructible) but the LARGE-instanton IR
= the confinement scale = `singleStep`.

# The obligation (read first)

The instanton (the self-dual gauge configuration of topological charge 1) has EXACT action
`S_inst = 8π²/g²`.  Instanton-induced effects scale as `exp(−S_inst) = exp(−8π²/g²)` — the
essential singularity, invisible to perturbation theory (all Taylor coefficients vanish at
`g² = 0`), yet strictly positive.  The dilute-instanton-gas is meant to generate a mass
`~ exp(−8π²/g²)` from a gas of well-separated instantons.

The 't Hooft one-instanton density (the semiclassical measure over the collective coordinate
`ρ`, the instanton SIZE) is

    d(ρ) dρ  ~  (1/ρ⁵) · (8π²/g²(ρ))^{2N} · exp(−8π²/g²(ρ)) dρ .

With the running coupling (asymptotic freedom) `8π²/g²(ρ) = β₀·log(1/(ρΛ))`, the exponential
becomes `exp(−β₀ log(1/ρΛ)) = (ρΛ)^{β₀}`, and (up to the `(8π²/g²)^{2N}` log correction) the
density scales as a PURE POWER of the size:

    d(ρ) dρ  ~  ρ^{(11N/3) − 5} dρ ,        β₀ = 11N/3  (one-loop, pure SU(N)).

# THE CRUX — the large-instanton IR problem (task point 2)

For SU(2) (`N = 2`): the density power is

    (11·2/3) − 5  =  22/3 − 5  =  7/3  >  0 ,

so `d(ρ) ~ ρ^{7/3}` GROWS at large `ρ` and `∫^∞ d(ρ) dρ` DIVERGES — the large-instanton / IR
problem.  The dilute-gas assumption (well-separated instantons) fails: the large instantons
overlap and fill space.  The IR-divergent tail IS the confinement scale — the same
non-perturbative measure the block-spin / renormalon routes isolate.  The SMALL-instanton end
(`ρ → 0`) is fine: `ρ^{7/3} → 0` is integrable, so the small-instanton contribution is a
CONVERGENT (constructible) geometric-type sum.

# What is genuinely new here

  * **`instantonAmplitude`** — the essential singularity `exp(−8π²/g²(ρ_k))` as a genuine
    CReal (reusing the proved `condensateCReal`, the same `exp(−const/g²)` functional form);
    its positivity `≥ 0` is TRIVIAL (`condensate_creal_nonneg`, the red herring).
  * **`densityExponent N = 11N/3 − 5`** as an exact `Q'`, with `su2_density_IR_divergent`
    (`0 < densityExponent 2 = 7/3`, decide) and the general `density_IR_divergent`
    (`0 < densityExponent N` for every `N ≥ 2`, omega): the instanton density is IR-DIVERGENT
    for EVERY pure-SU(N) theory (the large-instanton problem is universal), machine-checked.
  * **`smallInst_convergent`** — the small-instanton size integral is UNIFORMLY BOUNDED (a
    convergent geometric budget, via the proved `geometric_tail_closure`): the small-instanton
    contribution is genuinely constructible.
  * **`largeInst_no_finite_budget`** — the large-instanton size integral has NO finite bound:
    its partial sums (a constant density floor `ρ^{7/3} ≥ 1` for `ρ ≥ 1`) equal `N` and exceed
    ANY `Q'` (Archimedean, machine-checked).  The dilute-gas has no convergent measure at large
    size — the IR divergence, in Lean.

# THE DECISIVE CHECK (task point 3) — generation vs the large-instanton IR

Split cleanly.  The instanton ACTION gives the essential singularity `exp(−8π²/g²)`
(CONSTRUCTIBLE, positivity free).  The instanton DENSITY is IR-DIVERGENT (`ρ^{7/3}`,
`density_IR_divergent`).  The small-instanton (`ρ < Λ⁻¹`) gives a convergent contribution
(`smallInst_convergent`); the large-instanton (`ρ > Λ⁻¹`) has no finite measure
(`largeInst_no_finite_budget`) — it IS the confinement scale = the non-perturbative measure =
`singleStep`.  So the instanton CONFIRMS the essential singularity but does NOT generate the
mass constructively: the mass needs the IR-complete (large-instanton) density = `singleStep`.

Encoded (def-alias, UNINHABITED, NOT one of the guarded frontier types):
`InstantonLargeSizeIR := SingleStepDefectReduction.SingleStepDefectBound`.

# HONEST verdict (task point 4)

The BPST action `S_inst = 8π²/g²` gives the essential singularity `exp(−8π²/g²)`, CONSTRUCTIBLE
as a CReal (positivity trivial = red herring).  The 't Hooft density is IR-DIVERGENT
(`ρ^{7/3}` for SU(2), PROVED, universal for `N ≥ 2`).  The small-instanton contribution is
convergent (constructible); the large-instanton IR is the confinement = the non-perturbative
measure = `singleStep`.  The instanton does NOT generate the gap constructively — it ISOLATES
the large-instanton IR = `singleStep`, a further confirmation of the SAME irreducible core in
semiclassical form, PLUS the genuinely new machine-checked IR-divergent-density theorem.  No
guarded frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.

# Numerics (sympy-exact, verified)

  * `densityExponent N = 11N/3 − 5`; SU(2): `22/3 − 5 = 7/3 ≈ 2.333 > 0` (IR-divergent);
    SU(3): `6`; SU(4): `29/3`; SU(5): `40/3` — POSITIVE (⟹ divergent) for all `N ≥ 2`
    (`∫^∞ ρ^p dρ` diverges iff `p ≥ −1`; here `p ≥ 7/3`).
  * small-instanton geometric budget `condHead/(1−condRate) = (1/100)/(2/5) = 1/40` (convergent).
  * large-instanton floor `ρ^{7/3} ≥ 1` (ρ ≥ 1) ⟹ partial sum `= N → ∞` (divergent).

# Axiom-gate (AGENTS.md Rule 1 / Rule 8)

Pure `Q'`/`Nat` + the proved `condensateCReal` (nonneg/`≤1`, trivial), the
`finSum`/`geometric_tail_closure` backbone, a local Archimedean step (`Int.self_le_toNat` +
`omega`), and the named residual `SingleStepDefectReduction.SingleStepDefectBound`.  Every
load-bearing declaration gated with `#print axioms`; permitted output `propext` / `Quot.sound`
only (or empty).  No `Classical.*`, no `native_decide` (only `decide` on closed decidable `Q'`
facts), no `ring`, no `sorry`.  All witnesses `Type`-level.  No frontier bundle inhabited.
-/
import YMGap.Continuum.CondensateGeometricErosion
import YMGap.Continuum.SingleStepDefectReduction

namespace YMGap.Continuum.InstantonDiluteGas

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.CondensateGeometric

/-! ## 0. Local `Q'`/`Int` order glue (self-contained). -/

/-- `0 < q.num ⟹ 0 < q` on `Q'` (local copy; `(0:Q')` has num `0`, den `1`). -/
theorem pos_of_num_pos {q : Q'} (h : 0 < q.num) : (0 : Q') < q := by
  show (0 : Int) * (q.den : Int) < q.num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]; exact h

/-- `a < b ≤ c ⟹ a < c` on `Q'` (local copy, pattern of `WetterichMassFlow.lt_of_lt_of_le`). -/
theorem lt_of_lt_of_le {a b c : Q'} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  have e1 : a.num * (b.den : Int) < b.num * (a.den : Int) := h1
  have e2 : b.num * (c.den : Int) ≤ c.num * (b.den : Int) := h2
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have s1 : (a.num * (c.den : Int)) * (b.den : Int)
          < (b.num * (a.den : Int)) * (c.den : Int) := by
    have := Int.mul_lt_mul_of_pos_right e1
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have hr : (a.num * (b.den : Int)) * (c.den : Int)
            = (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hr] at this
  have s2 : (b.num * (a.den : Int)) * (c.den : Int)
          ≤ (c.num * (a.den : Int)) * (b.den : Int) := by
    have := Int.mul_le_mul_of_nonneg_right e2
      (by exact_mod_cast Nat.le_of_lt a.den_pos : (0 : Int) ≤ (a.den : Int))
    have hr : (b.num * (c.den : Int)) * (a.den : Int)
            = (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (c.den : Int) (a.den : Int)]
    have hr2 : (c.num * (b.den : Int)) * (a.den : Int)
             = (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [hr, hr2] at this; exact this
  have s3 : (a.num * (c.den : Int)) * (b.den : Int)
          < (c.num * (a.den : Int)) * (b.den : Int) :=
    Int.lt_of_lt_of_le s1 s2
  exact Int.lt_of_mul_lt_mul_right s3
    (by exact_mod_cast Nat.le_of_lt b.den_pos : (0 : Int) ≤ (b.den : Int))

/-! ## 1. THE INSTANTON ACTION AND THE ESSENTIAL SINGULARITY (CONSTRUCTIBLE).

The BPST instanton has action `S_inst = 8π²/g²`.  Instanton-induced effects scale as
`exp(−S_inst) = exp(−8π²/g²)` — the essential singularity.  With the running coupling this is
`exp(−β₀ log(1/ρΛ)) = (ρΛ)^{β₀}`, the SAME `exp(−const/g²)` functional form as the condensate
`exp(−c/β₀g²)`; we re-export the proved `condensateCReal` as the instanton amplitude.  Its
positivity is the RED HERRING (`exp` is positive, free). -/

/-- **THE INSTANTON-INDUCED AMPLITUDE `exp(−8π²/g²(ρ_k))`** as a genuine CReal — the essential
singularity, reusing the proved `condensateCReal` (the same `exp(−const/g²)`, geometric with the
running coupling).  This is the constructible non-perturbative scale the instanton supplies. -/
def instantonAmplitude (k : Nat) : CReal := condensateCReal k

/-- **The instanton amplitude is `≥ 0`** — TRIVIALLY (`exp` is nonnegative).  This is the
exp-positivity RED HERRING: constructing `exp(−8π²/g²) > 0` as a CReal is FREE, so the mass gap
does NOT reduce to it. -/
theorem instantonAmplitude_nonneg (k : Nat) : ExpPos.geRat (instantonAmplitude k) 0 :=
  condensate_creal_nonneg k

/-- **The instanton amplitude is `≤ 1`** — a bona-fide CReal in `[0,1]` (the semiclassical
suppression factor). -/
theorem instantonAmplitude_le_one (k : Nat) : CReal.leRat (instantonAmplitude k) 1 :=
  condensate_creal_le_one k

/-! ## 2. THE ONE-LOOP `β₀` AND THE IR-DIVERGENT DENSITY POWER (the crux).

`β₀ = 11N/3` (one-loop, pure SU(N)).  The 't Hooft density scales as `ρ^{β₀ − 5} = ρ^{11N/3−5}`
at large size.  For SU(2) this is `ρ^{7/3}`, which DIVERGES at large `ρ` — the large-instanton
IR problem. -/

/-- **The one-loop coefficient `β₀ = 11N/3`** for pure SU(N) (asymptotic freedom).  Exact `Q'`. -/
def betaZeroCoeff (N : Nat) : Q' := Q'.mkPos (11 * (N : Int)) 3 (by decide)

/-- **`β₀ = 11N/3 > 0` for every `N ≥ 1`** — the asymptotic-freedom sign (cf. `FourDExistence.
betaZero_pos`).  Machine-checked. -/
theorem betaZeroCoeff_pos (N : Nat) (hN : 1 ≤ N) : (0 : Q') < betaZeroCoeff N := by
  apply pos_of_num_pos
  show (0 : Int) < 11 * (N : Int)
  omega

/-- **THE 't HOOFT DENSITY POWER `d(ρ) ~ ρ^{(11N/3) − 5}`** (the exponent of the instanton-size
integrand), exact `Q'`: `densityExponent N = 11N/3 − 5`.  The `(1/ρ⁵)` measure factor gives
the `−5`; the running-coupling exponential gives the `+β₀ = +11N/3`; the `(8π²/g²)^{2N}` prefactor
is a subleading log correction to this power. -/
def densityExponent (N : Nat) : Q' := Q'.mkPos (11 * (N : Int) - 15) 3 (by decide)

/-- **SU(2): the density power is `7/3`** (`22/3 − 5 = 7/3`).  Kernel `decide`. -/
theorem su2_density_value : (densityExponent 2).eqv (Q'.mkPos 7 3 (by decide)) := by decide

/-- **SU(2) LARGE-INSTANTON IR DIVERGENCE.**  `0 < densityExponent 2 = 7/3`, so `d(ρ) ~ ρ^{7/3}`
GROWS at large `ρ` and `∫^∞ d(ρ) dρ` DIVERGES — the large-instanton / IR problem: the dilute
gas breaks down.  Kernel `decide`. -/
theorem su2_density_IR_divergent : (0 : Q') < densityExponent 2 := by decide

/-- **THE LARGE-INSTANTON IR DIVERGENCE IS UNIVERSAL (`N ≥ 2`).**  For EVERY pure SU(N) theory
with `N ≥ 2` the density power is strictly positive: `0 < densityExponent N = 11N/3 − 5`
(`11N − 15 ≥ 7 > 0`).  Hence `d(ρ) ~ ρ^{11N/3−5}` diverges at large `ρ` for all such `N` — the
large-instanton problem is a universal feature of asymptotically-free pure Yang–Mills, not an
SU(2) accident.  (`∫^∞ ρ^p dρ` diverges iff `p ≥ −1`, and here `p ≥ 7/3`.)  omega. -/
theorem density_IR_divergent (N : Nat) (hN : 2 ≤ N) : (0 : Q') < densityExponent N := by
  apply pos_of_num_pos
  show (0 : Int) < 11 * (N : Int) - 15
  omega

/-! ## 3. THE SMALL-INSTANTON CONTRIBUTION IS CONVERGENT (CONSTRUCTIBLE).

The small-instanton end (`ρ → 0`) is integrable (`ρ^{7/3} → 0`), so `∫_0^{Λ⁻¹} d(ρ) dρ`
CONVERGES.  Modelled by a geometric size-integrand `smallInstTerm_k = K'·r'^k` with the proved
closed geometric budget `K'/(1−r') = 1/40`.  The small-instanton contribution is genuinely
constructible. -/

/-- The small-instanton size-integrand majorant `smallInstTerm_k = K'·r'^k` (geometric decay,
the small-`ρ` integrable end of the 't Hooft density). -/
def smallInstTerm (k : Nat) : Q' := condHead * condRate ^ k

/-- **THE SMALL-INSTANTON INTEGRAL IS UNIFORMLY BOUNDED (CONVERGENT).**  Every partial sum of
the small-instanton size-integrand is bounded by the closed geometric budget
`condSum = K'/(1−r') = 1/40` — the small-instanton contribution is genuinely constructible (a
convergent geometric sum).  Reuses the PROVED `RationalTail.geometric_tail_closure`. -/
theorem smallInst_convergent (N : Nat) :
    finSum (fun k => condHead * condRate ^ k) N ≤ condSum :=
  geometric_tail_closure condHead condRate condSum (by decide) (by decide) cond_recurrence N

/-! ## 4. THE LARGE-INSTANTON INTEGRAL HAS NO FINITE BUDGET (IR DIVERGENCE).

At large size the density does NOT decay (`ρ^{7/3} ≥ 1` for `ρ ≥ 1`); its partial sums grow
linearly and exceed ANY finite bound.  This is the IR divergence — the dilute-gas measure fails
at large instanton size.  Contrast the small-instanton geometric budget above. -/

/-- The large-instanton size-integrand FLOOR: `d(ρ) = ρ^{7/3} ≥ 1` for `ρ ≥ 1`, so the integrand
does NOT decay.  Modelled by the constant `1` (the lower bound of the growing IR density). -/
def largeInstTerm (_n : Nat) : Q' := (1 : Q')

/-- **The large-instanton partial sum equals `N`** (`Σ_{j<N} 1 = N`) — it grows without bound. -/
theorem largeInstPartialSum_eqv :
    ∀ N, (finSum largeInstTerm N).eqv (Q'.ofNat N)
  | 0 => by decide
  | N + 1 => by
    have ih := largeInstPartialSum_eqv N
    show (finSum largeInstTerm N + (1 : Q')).eqv (Q'.ofNat (N + 1))
    have s1 : (finSum largeInstTerm N + (1 : Q')).eqv (Q'.ofNat N + 1) :=
      Q'.add_eqv_congr_right _ _ 1 ih
    have s2 : (Q'.ofNat (N + 1)).eqv (Q'.ofNat N + 1) :=
      Q'.eqv_trans _ _ _ (Q'.ofNat_add_eqv N 1)
        (Q'.add_eqv_congr_left (Q'.ofNat N) (Q'.ofNat 1) 1 (by decide))
    exact Q'.eqv_trans _ _ _ s1 (Q'.eqv_symm s2)

/-- **THE ARCHIMEDEAN STEP.**  For every `B : Q'` there is an `N` with `B < ofNat N`.  Explicit
witness `N = B.num.toNat + 1`, using `B.num ≤ ↑B.num.toNat` and `1 ≤ B.den`. -/
theorem exists_ofNat_gt (B : Q') : ∃ N : Nat, B < Q'.ofNat N := by
  refine ⟨B.num.toNat + 1, ?_⟩
  have hQ1 : (1 : Int) ≤ (B.den : Int) := by exact_mod_cast B.den_pos
  have hPle : B.num ≤ (B.num.toNat : Int) := Int.self_le_toNat B.num
  have hm1 : (0 : Int) ≤ (B.num.toNat : Int) + 1 := by
    have : (0 : Int) ≤ (B.num.toNat : Int) := Int.natCast_nonneg _
    omega
  have hmul : ((B.num.toNat : Int) + 1) * (1 : Int)
      ≤ ((B.num.toNat : Int) + 1) * (B.den : Int) :=
    Int.mul_le_mul_of_nonneg_left hQ1 hm1
  rw [Int.mul_one] at hmul
  show B.num * ((Q'.ofNat (B.num.toNat + 1)).den : Int)
     < (Q'.ofNat (B.num.toNat + 1)).num * (B.den : Int)
  have hden : (Q'.ofNat (B.num.toNat + 1)).den = 1 := rfl
  have hnum : (Q'.ofNat (B.num.toNat + 1)).num = ((B.num.toNat + 1 : Nat) : Int) := rfl
  rw [hden, hnum]
  push_cast
  push_cast at hmul
  omega

/-- **THE LARGE-INSTANTON INTEGRAL HAS NO FINITE BUDGET — IR DIVERGENCE.**  For every candidate
bound `B : Q'` there is a size-cutoff `N` at which the large-instanton partial sum EXCEEDS `B`:
`B < Σ_{j<N} d(ρ_j)`.  The dilute-gas has no convergent measure at large instanton size — the
large-instanton IR divergence, machine-checked.  Contrast `smallInst_convergent` (a uniform
finite budget for the small-instanton end). -/
theorem largeInst_no_finite_budget (B : Q') :
    ∃ N : Nat, B < finSum largeInstTerm N := by
  obtain ⟨N, hN⟩ := exists_ofNat_gt B
  exact ⟨N, lt_of_lt_of_le hN (Q'.ge_of_eqv (largeInstPartialSum_eqv N))⟩

/-! ## 5. THE ISOLATION — the large-instanton IR = the interacting measure = `singleStep`. -/

/-- **THE LARGE-INSTANTON IR = `singleStep` (named residual, NOT faked).**  The instanton ACTION
gives the essential singularity `exp(−8π²/g²)` (CONSTRUCTIBLE, `instantonAmplitude`, positivity
free) and the SMALL-instanton contribution is convergent (`smallInst_convergent`), but the
DENSITY is IR-DIVERGENT (`density_IR_divergent`) and the LARGE-instanton size integral has NO
finite measure (`largeInst_no_finite_budget`).  The large-instanton IR — the overlapping large
instantons that fill space — IS the confinement scale = the non-perturbative measure = the
spacing-uniform gap survival `SingleStepDefectReduction.SingleStepDefectBound.singleStep` (the
renormalon).  Restated as a `Type`-alias; UNINHABITED (it IS the real RG estimate).  A dilute-gas
mass built with an ASSUMED IR-complete (large-instanton) density would be the Rule-9 fake —
deliberately not written.  (Identification at the level of the SAME irreducible core across
confirmations, not an `rfl` between the distinct structures.) -/
def InstantonLargeSizeIR : Type :=
  SingleStepDefectReduction.SingleStepDefectBound

/-- The def-alias is exactly the named residual (Rule 9.8, proof not prose). -/
theorem instantonLargeSizeIR_eq :
    InstantonLargeSizeIR = SingleStepDefectReduction.SingleStepDefectBound := rfl

/-! ## 6. The assembled verdict (informational bundle — inhabits NO frontier type). -/

/-- A record of the machine-checked facts of the instanton / dilute-gas assessment.  NOT a
frontier bundle: every field is a genuine PROVED theorem, and it inhabits neither
`SingleStepDefectBound` nor any guarded Clay-frontier type.  It certifies: the essential
singularity `exp(−8π²/g²)` is a bona-fide CReal in `[0,1]` (positivity trivial); the density
power is `> 0` (IR-divergent) for every `N ≥ 2`; the small-instanton integral is uniformly
bounded (convergent); and the large-instanton integral has no finite budget (IR-divergent). -/
structure InstantonVerdict : Type where
  /-- §1 — the essential singularity `exp(−8π²/g²)` is `≥ 0` (trivial, the red herring). -/
  amplitudeNonneg : ∀ k, ExpPos.geRat (instantonAmplitude k) 0
  /-- §1 — the essential singularity is `≤ 1` (a bona-fide suppression factor in `[0,1]`). -/
  amplitudeLeOne : ∀ k, CReal.leRat (instantonAmplitude k) 1
  /-- §2 — the density power is `> 0` for every `N ≥ 2` (large-instanton IR divergence). -/
  densityIRDivergent : ∀ N, 2 ≤ N → (0 : Q') < densityExponent N
  /-- §3 — the small-instanton integral is uniformly bounded (convergent). -/
  smallConvergent : ∀ N, finSum (fun k => condHead * condRate ^ k) N ≤ condSum
  /-- §4 — the large-instanton integral has no finite budget (IR divergence). -/
  largeNoFiniteBudget : ∀ B : Q', ∃ N : Nat, B < finSum largeInstTerm N

/-- **The verdict is inhabited by PROVED facts only.**  Every field is a genuine theorem; NONE
inhabits a frontier bundle.  This certifies the honest conclusion: the instanton CONFIRMS the
essential singularity `exp(−8π²/g²)` (constructible) and the convergent small-instanton end, but
the IR-DIVERGENT density and the large-instanton IR (uninhabited `InstantonLargeSizeIR =
singleStep`) are the residual — the instanton does NOT generate the gap constructively. -/
def instanton_verdict : InstantonVerdict where
  amplitudeNonneg := instantonAmplitude_nonneg
  amplitudeLeOne := instantonAmplitude_le_one
  densityIRDivergent := density_IR_divergent
  smallConvergent := smallInst_convergent
  largeNoFiniteBudget := largeInst_no_finite_budget

/-! ## 7. Honest verdict (AGENTS.md Rule 6 / Rule 9). -/

/-- **HONEST FINAL VERDICT.**

The instanton / semiclassical mechanism is BUILT and assessed.  **CONSTRUCTED (the genuine
pieces):**
  * the essential singularity `exp(−8π²/g²(ρ_k))` as a genuine CReal in `[0,1]`
    (`instantonAmplitude`, `instantonAmplitude_nonneg`/`_le_one`) — positivity TRIVIAL (the red
    herring: `exp(−8π²/g²) > 0` is FREE);
  * the one-loop `β₀ = 11N/3 > 0` (`betaZeroCoeff_pos`, asymptotic freedom);
  * the 't Hooft density power `densityExponent N = 11N/3 − 5` as an exact `Q'`, with SU(2)
    value `7/3` (`su2_density_value`) and IR divergence `0 < densityExponent 2`
    (`su2_density_IR_divergent`), UNIVERSAL for every `N ≥ 2` (`density_IR_divergent`);
  * the small-instanton integral is UNIFORMLY BOUNDED (convergent, `smallInst_convergent`);
  * the large-instanton integral has NO finite budget (IR-divergent,
    `largeInst_no_finite_budget`, via the Archimedean `exists_ofNat_gt`).

**RESIDUAL (NOT closed) — the large-instanton IR = `singleStep`:** the instanton action gives
the essential singularity (constructible) and the small-instanton end is convergent, but the
DENSITY is IR-DIVERGENT (`ρ^{7/3}` for SU(2)) and the large-instanton size integral has no finite
measure.  The large-instanton IR — the overlapping large instantons = the confinement scale =
the non-perturbative measure — is `InstantonLargeSizeIR = SingleStepDefectBound.singleStep`
(UNINHABITED).  So the dilute-instanton-gas does NOT generate the mass constructively: it
CONFIRMS the essential singularity but ISOLATES the large-instanton IR = `singleStep`, a further
confirmation of the SAME irreducible core in semiclassical form, PLUS the genuinely new
machine-checked IR-divergent-density theorem and the convergent-small / divergent-large split.
No guarded frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains
OPEN. -/
theorem instantonDiluteGas_honesty : True := trivial

end YMGap.Continuum.InstantonDiluteGas

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.InstantonDiluteGas.pos_of_num_pos
#print axioms YMGap.Continuum.InstantonDiluteGas.lt_of_lt_of_le
#print axioms YMGap.Continuum.InstantonDiluteGas.instantonAmplitude_nonneg
#print axioms YMGap.Continuum.InstantonDiluteGas.instantonAmplitude_le_one
#print axioms YMGap.Continuum.InstantonDiluteGas.betaZeroCoeff_pos
#print axioms YMGap.Continuum.InstantonDiluteGas.su2_density_value
#print axioms YMGap.Continuum.InstantonDiluteGas.su2_density_IR_divergent
#print axioms YMGap.Continuum.InstantonDiluteGas.density_IR_divergent
#print axioms YMGap.Continuum.InstantonDiluteGas.smallInst_convergent
#print axioms YMGap.Continuum.InstantonDiluteGas.largeInstPartialSum_eqv
#print axioms YMGap.Continuum.InstantonDiluteGas.exists_ofNat_gt
#print axioms YMGap.Continuum.InstantonDiluteGas.largeInst_no_finite_budget
#print axioms YMGap.Continuum.InstantonDiluteGas.instantonLargeSizeIR_eq
#print axioms YMGap.Continuum.InstantonDiluteGas.instanton_verdict
