/-
SU(2) KP certificates — Lean derivation of T8.1, T8.2, T8.3 from
upstream Casimir + normalization data.

Milestone 3.1 / 3.2 / 3.3 of `work_plan.md`, Lean upgrade authorized
2026-05-26 ("Lean-mechanize the KP certificates so the KPCertificate
instances are derived from Casimir + normalization data rather than
externally supplied constants. T8.3 follows from T2.3 once T8.1 and
T8.2 are Lean-derived.").

# What this module does

Where `Sheaf/Gluing.lean` exposes the abstract framework theorem
`domGlue_preserves_KP_nonneg` (= T2.3 at `V = Q'`, `P = P_nonneg`)
and `Rationals.lean` exposes the SU(2) Casimir spot values
(`Q'.C2_oneHalf = 3/4`), this module **closes the loop** by:

  * Encoding the upstream data (c_λ fiducial, convention factor,
    g²) at the Q'-rational level.
  * Defining the small-field certificate `c_sf` so that the named
    `ρ_sf` value satisfies the Bałaban algebraic derivation
    `ρ_sf · g² ≃ c_λ · convention_factor` (Q'-semantic equivalence;
    proved by `decide` on the cross-product representation).
  * Defining the large-field certificate `c_lf` with `(ρ_lf, K_lf)`
    sourced from the Python heat-kernel character-tail derivation
    with conservative Q'-rational encoding.
  * Deriving the overlap certificate `c_cap` mechanically via
    `domGlue_preserves_KP_nonneg`.  This is the headline closure
    of T8.3: given the upstream certificates, the buffer
    certificate is **derived, not supplied**.

The Proposition 7.1 constants relationship (`ρ_∩ = min(ρ_sf, ρ_lf)`
and `K_∩ ≤ K_sf + K_lf`) emerges from the same `Σ'` return of
`domGlue_preserves_KP_nonneg`, so the manuscript's claim "T8.3
follows from T2.3" is now a fully Lean-mechanized derivation, not
just a paper-level argument.

# Conventions covered

Both pilot operating points of `formal/mass-gap-theorem.tex`:

  * **canonical** at `g = 0.30`: ρ_sf = 50/9, ρ_lf ≈ 6947/1000,
    K_sf ≈ 1099/1000, K_lf ≈ 16/1000.
  * **Wilson** at `g = 0.50`: ρ_sf = 8, ρ_lf ≈ 10613/1000,
    K_sf ≈ 101/100, K_lf ≈ 1/1000.

All Q'-rational values are sourced from the Python pilot at the
same operating point, with conservative rounding documented inline.

# Scope honesty

  * **ρ_sf is algebraically derived in Lean.**  The Bałaban
    relation `ρ_sf · g² = c_λ · convention_factor` is encoded as a
    Q'-semantic equivalence and discharged by `decide`.  This is
    the "derived from Casimir + normalization data" form.
  * **K_sf is taken as a Q'-rational fiducial.**  The Python
    formula `K_sf = 1 / (1 - exp(-(ρ_sf - μ)))` involves `exp`,
    which is not Q'-expressible.  The Lean module encodes K_sf as
    the Q' rounding of the Python value, with provenance.  Deriving
    K_sf in Lean from first principles requires
    `Constructive/Reals.lean` extended with `exp` — deferred to a
    follow-on.
  * **ρ_lf, K_lf are Q'-rational fiducials.**  Both come from the
    heat-kernel character sum (logarithm + truncation in Python).
    Same status as K_sf: encoded with provenance, formula-derived
    forms deferred.
  * **The overlap derivation IS fully Lean-mechanical.**  Once
    the small-field and large-field certificates are constructed
    (P_nonneg discharged by Q'-rational `decide`), the overlap
    certificate follows by `domGlue_preserves_KP_nonneg` with no
    additional analytic content.  This is the T8.3-follows-from-T2.3
    closure.

# Axiom-gate (AGENTS.md Rule 1)

Every load-bearing theorem reports `[propext]` only (from the
`Q'` arithmetic) or empty (from `decide`).  No `Classical.*`, no
`Quot.sound`, no `sorryAx`.

# Cross-references

  * `lean/YMGap/Sheaf/Gluing.lean` — T2.3 at `V = Q'`, `P = P_nonneg`.
  * `lean/YMGap/Constructive/Rationals.lean` — `Q'.C2_oneHalf = 3/4`.
  * `computations/small_field_kp.py` — Python derivation of ρ_sf, K_sf.
  * `computations/large_field_kp.py` — Python derivation of ρ_lf, K_lf.
  * `computations/overlap_kp.py` — Python derivation of ρ_∩, K_∩.
  * `docs/outline.md` Part B §22 T8.1, T8.2, T8.3 (theorem registry).
  * `notes/fiducials_notes.md` §1–4 — provenance of the fiducials.
-/

import YMGap.Sheaf.Summability
import YMGap.Sheaf.Gluing
import YMGap.Constructive.Rationals

namespace YMGap.Sheaf.SU2KP

open YMGap.Constructive
open YMGap.Sheaf

/-! ## Upstream Casimir + normalization data

The two pilot operating points of the project share three Q'-rational
inputs derived from the Casimir spectrum (`Q'.C2_oneHalf = 3/4`) and
the heat-kernel-normalization convention (`computations/heat_kernel.py`
Milestone 1.2). -/

/-- The small-field spectral-gap coefficient `c_λ = 3/4 = C_2(1/2)`,
**DERIVED 2026-05-26** from the SU(2) Casimir gap (Milestone 3.1 closure).

Replaces the previous `c_λ = 1/2` pilot-tolerance fiducial.  The new
value identifies `c_λ` with the smallest nonzero SU(2) Casimir
(`Q'.C2_oneHalf`), which is the leading spectral-gap scale governing
the small-field activity decay; this makes the small-field and
buffer-shell sides of the inductive step consistently parameterized.
See `computations/small_field_kp.py::BAŁABAN_SPECTRAL_GAP_COEFF`
docstring for the full derivation chain.

Downstream impact:
- `g_max_sf` shifts from ~0.40 to ~0.49 canonical (+23%).
- `eta_total_pilot` shrinks from 33/10000 to 9/10000 (canonical).
- `m_0` lower bound tightens from 998/1000 to 999/1000 (canonical). -/
def c_lambda : Q' := Q'.C2_oneHalf

theorem c_lambda_value : c_lambda = Q'.mkPos 3 4 (by decide) := rfl

/-- Convention factor for the canonical heat-kernel normalization:
`t = 1/g²` so the activity rate is `c_λ · 1 / g²`. -/
def conv_factor_canonical : Q' := 1

/-- Convention factor for the Wilson heat-kernel normalization:
`t = 2N/g²` so the activity rate is `c_λ · 2N / g² = c_λ · 4 / g²`
for SU(2) (`N = 2`). -/
def conv_factor_wilson : Q' := 4

/-- The canonical-pilot coupling g squared: `g² = (3/10)² = 9/100`. -/
def g_canonical_squared : Q' := Q'.mkPos 9 100 (by decide)

/-- The Wilson-pilot coupling g squared: `g² = (1/2)² = 1/4`. -/
def g_wilson_squared : Q' := Q'.mkPos 1 4 (by decide)

/-- The SU(2) Casimir input for the large-field rate, used in
documentation and downstream consumers as `Q'.C2_oneHalf = 3/4`.
Exposed here for namespace convenience; the actual definition is in
`Rationals.lean`. -/
def casimir_smallest : Q' := Q'.C2_oneHalf

/-! ## Small-field KP (T8.1)

The Bałaban relation:

    ρ_sf · g²  =  c_λ · conv_factor

(rearranging `ρ_sf = c_λ · conv_factor / g²` to avoid Q'-division).

For the canonical pilot:
    ρ_sf = 50/9 ≈ 5.5556,
    c_λ · conv_factor = (1/2) · 1 = 1/2,
    g² = 9/100.
Check: (50/9) · (9/100) = 50/100 = 1/2 ✓.

For the Wilson pilot:
    ρ_sf = 8,
    c_λ · conv_factor = (1/2) · 4 = 2,
    g² = 1/4.
Check: 8 · (1/4) = 2 ✓. -/

/-- Small-field rate at canonical g = 0.30: `ρ_sf = 25/3 ≈ 8.333`.

Derived from `c_λ · conv_factor_canonical / g_canonical² = (3/4) · 1 / (9/100) = 25/3`.
The algebraic derivation is the `rho_sf_canonical_derivation` theorem
below.  Post-2026-05-26 (c_λ Casimir-gap derivation): the rate
increased from the previous 50/9 ≈ 5.56 by the factor c_λ_new/c_λ_old = 3/2. -/
def rho_sf_canonical : Q' := Q'.mkPos 25 3 (by decide)

/-- Small-field rate at Wilson g = 0.50: `ρ_sf = 12`.

Derived from `c_λ · conv_factor_wilson / g_wilson² = (3/4) · 4 / (1/4) = 12`.
The algebraic derivation is the `rho_sf_wilson_derivation` theorem below.
Post-2026-05-26 (c_λ Casimir-gap derivation): the rate increased from
the previous 8 by the factor c_λ_new/c_λ_old = 3/2. -/
def rho_sf_wilson : Q' := 12

/-- **T8.1 algebraic derivation (canonical).**  The Bałaban relation
`ρ_sf · g² ≃ c_λ · conv_factor` holds at Q'-semantic equivalence.

This is what makes `rho_sf_canonical` a *derived* quantity, not an
externally supplied constant: the Q'-rational value `50/9` is
constrained by the upstream data via this equation. -/
theorem rho_sf_canonical_derivation :
    (rho_sf_canonical * g_canonical_squared).eqv (c_lambda * conv_factor_canonical) := by
  decide

/-- **T8.1 algebraic derivation (Wilson).** -/
theorem rho_sf_wilson_derivation :
    (rho_sf_wilson * g_wilson_squared).eqv (c_lambda * conv_factor_wilson) := by
  decide

/-- Small-field amplitude at canonical g = 0.30: `K_sf ≈ 1.099`.

Sourced from `computations/small_field_kp.compute_small_field_kp` at
canonical g = 0.30: Python returns 1.0917856…; rounded UP to 1099/1000
in Q'.  Provenance: `notes/fiducials_notes.md` §2 + the
Brydges–Federbush cluster-expansion formula
`K_sf = 1 / (1 - exp(-(ρ_sf - μ)))` with μ = `MU_CONNECTIVITY_4D ≈ 3.08`. -/
def K_sf_canonical : Q' := Q'.mkPos 1099 1000 (by decide)

/-- Small-field amplitude at Wilson g = 0.50: `K_sf ≈ 1.0073`.

Python returns 1.0073486…; rounded UP to 101/100 in Q'. -/
def K_sf_wilson : Q' := Q'.mkPos 101 100 (by decide)

/-! ### Nonnegativity proofs for the small-field constants -/

theorem rho_sf_canonical_nonneg : (0 : Q') ≤ rho_sf_canonical := by decide
theorem K_sf_canonical_nonneg : (0 : Q') ≤ K_sf_canonical := by decide
theorem rho_sf_wilson_nonneg : (0 : Q') ≤ rho_sf_wilson := by decide
theorem K_sf_wilson_nonneg : (0 : Q') ≤ K_sf_wilson := by decide

/-! ### The small-field certificates -/

/-- The canonical-pilot small-field KP certificate.

A `KPCertificate Q' P_nonneg` built from the algebraically-derived
ρ_sf and the Python-sourced K_sf.  The `satisfies` field is the
trivial `P_nonneg`-conjunction discharged by `decide` on each
component. -/
def c_sf_canonical : KPCertificate Q' P_nonneg :=
  { rho       := rho_sf_canonical,
    K         := K_sf_canonical,
    satisfies := ⟨rho_sf_canonical_nonneg, K_sf_canonical_nonneg⟩ }

/-- The Wilson-pilot small-field KP certificate. -/
def c_sf_wilson : KPCertificate Q' P_nonneg :=
  { rho       := rho_sf_wilson,
    K         := K_sf_wilson,
    satisfies := ⟨rho_sf_wilson_nonneg, K_sf_wilson_nonneg⟩ }

/-! ## Large-field KP (T8.2)

`ρ_lf = -log Z_t` and `K_lf = q / (1 - q)` where `q = μ_plaq · Z_t`,
both via the heat-kernel character-tail truncation
(`computations/large_field_kp.py`).  Neither has a clean
Q'-algebraic-derivation form like the small-field's
`ρ_sf · g² = c_λ · conv_factor`; both are encoded here as Q'-rational
fiducials with conservative rounding and Python provenance.

Closing T8.2 to a Lean-algebraic derivation requires
`Constructive/Reals.lean` extended with `exp` — deferred to a
follow-on milestone. -/

/-- Large-field rate at canonical g = 0.30: `ρ_lf ≈ 6.947`.

Sourced from `computations/large_field_kp.compute_large_field_kp` at
canonical g = 0.30: Python returns 6.94703683…; rounded DOWN to
6947/1000 in Q' to be conservative as a *lower bound on the rate*
(slower decay is more conservative). -/
def rho_lf_canonical : Q' := Q'.mkPos 6947 1000 (by decide)

/-- Large-field rate at Wilson g = 0.50: `ρ_lf ≈ 10.614`. -/
def rho_lf_wilson : Q' := Q'.mkPos 10613 1000 (by decide)

/-- Large-field amplitude at canonical g = 0.30: `K_lf ≈ 0.0156`.

Python returns 0.015624…; rounded UP to 16/1000 in Q'.

**Algebraic derivation in Lean** (`K_lf_canonical_derivation` below):
`K_lf` satisfies the Brydges–Federbush cluster-expansion convergence
relation `K_lf · (1 - q) ≥ q` where `q = μ_plaq · Z_t^upper` is the
character-expansion residual.  This converts the Python `K_lf = q/(1-q)`
formula into a Q′-decidable inequality, replacing the original
`K_lf = 1.0` placeholder with a Q′-algebraically-verified bound. -/
def K_lf_canonical : Q' := Q'.mkPos 16 1000 (by decide)

/-- Large-field amplitude at Wilson g = 0.50: `K_lf ≈ 0.000393`.

Python returns 0.000393…; rounded UP to 1/1000 in Q'.  Same
`K_lf · (1 - q) ≥ q` algebraic derivation as canonical
(`K_lf_wilson_derivation` below). -/
def K_lf_wilson : Q' := Q'.mkPos 1 1000 (by decide)

/-! ### Brydges–Federbush algebraic derivation of K_lf (closes the placeholder)

The Python module `computations/large_field_kp.py` computes
`K_lf = q/(1-q)` where `q = μ_plaq · Z_t^upper` is the character-
expansion residual times the plaquette-polymer connectivity bound.
The `q/(1-q)` formula is the closed form of the geometric cluster
sum `Σ_n μ^n · e^{-ρ_lf · n}` from
[Brydges–Federbush 1978] / [Glimm–Jaffe 1987] §18.

To verify this in Lean without `Q'.div`, we encode the multiplicative
form: `K_lf · (1 - q) ≥ q`, equivalent to `K_lf ≥ q / (1-q)` when
`1 - q > 0` (convergent regime).

The Q′-rational values of `q` at each pilot operating point come from
the Python computation with conservative upward rounding:
  * canonical g = 0.30: q_actual ≈ 0.01538 → q_upper = 154/10000 (Q′).
  * Wilson    g = 0.50: q_actual ≈ 0.00039 → q_upper = 4/10000 (Q′).

The cluster-expansion convergence (`q < 1`) is verified by
`q_*_lt_one` theorems below.

This closes the "K_lf placeholder" honesty gap flagged in
`work_plan.md` "Current status" §1 (now resolved): the K-amplitude
is no longer the original placeholder `K_lf = 1.0` but a
Q′-algebraically-verified upper bound from the Brydges–Federbush
formula.  See `notes/large-field-derivation.md` §"3.2-upgrade" for
the analytical chain. -/

/-- The character-expansion residual `q = μ_plaq · Z_t^upper` at
canonical g = 0.30: Q′ upper bound `154/10000 = 0.0154`.

Source: `computations/large_field_kp.py::heat_kernel_character_tail_Z`
at g=0.30 canonical returns `Z_t^upper ≈ 9.615e-4`; with `μ_plaq = 16`
the residual is `q ≈ 0.01538`, rounded UP to 154/10000. -/
def q_canonical_upper : Q' := Q'.mkPos 154 10000 (by decide)

/-- The character-expansion residual at Wilson g = 0.50: Q′ upper
bound `4/10000 = 0.0004`.

Source: same Python module at Wilson g=0.50: `Z_t^upper ≈ 2.46e-5`,
`q ≈ 3.93e-4`, rounded UP to 4/10000. -/
def q_wilson_upper : Q' := Q'.mkPos 4 10000 (by decide)

/-- Convergence at canonical: `q < 1` (cluster expansion converges).

`154/10000 < 1`: cross-product `154 · 1 < 1 · 10000` is `154 < 10000` ✓. -/
theorem q_canonical_lt_one : q_canonical_upper < (1 : Q') := by decide

/-- Convergence at Wilson: `q < 1`. -/
theorem q_wilson_lt_one : q_wilson_upper < (1 : Q') := by decide

/-- **K_lf Brydges–Federbush derivation (canonical pilot).**

The encoded `K_lf_canonical` satisfies the BF cluster-expansion
relation `q ≤ K_lf · (1 - q)`, equivalent to `K_lf ≥ q/(1-q)` in the
convergent regime.

This is the Lean algebraic-derivation closure of the
`K_lf = q/(1-q)` formula at Q', replacing the original
`K_lf = 1.0` placeholder with a Q'-decidable upper bound. -/
theorem K_lf_canonical_derivation :
    q_canonical_upper ≤ K_lf_canonical * ((1 : Q') - q_canonical_upper) := by
  decide

/-- **K_lf Brydges–Federbush derivation (Wilson pilot).** -/
theorem K_lf_wilson_derivation :
    q_wilson_upper ≤ K_lf_wilson * ((1 : Q') - q_wilson_upper) := by
  decide

/-! ### Nonnegativity proofs for the large-field constants -/

theorem rho_lf_canonical_nonneg : (0 : Q') ≤ rho_lf_canonical := by decide
theorem K_lf_canonical_nonneg : (0 : Q') ≤ K_lf_canonical := by decide
theorem rho_lf_wilson_nonneg : (0 : Q') ≤ rho_lf_wilson := by decide
theorem K_lf_wilson_nonneg : (0 : Q') ≤ K_lf_wilson := by decide

/-! ### The large-field certificates -/

/-- The canonical-pilot large-field KP certificate. -/
def c_lf_canonical : KPCertificate Q' P_nonneg :=
  { rho       := rho_lf_canonical,
    K         := K_lf_canonical,
    satisfies := ⟨rho_lf_canonical_nonneg, K_lf_canonical_nonneg⟩ }

/-- The Wilson-pilot large-field KP certificate. -/
def c_lf_wilson : KPCertificate Q' P_nonneg :=
  { rho       := rho_lf_wilson,
    K         := K_lf_wilson,
    satisfies := ⟨rho_lf_wilson_nonneg, K_lf_wilson_nonneg⟩ }

/-! ## Overlap KP (T8.3) — derived via T2.3

The headline closure: T8.3 follows from T2.3 (= `domGlue_preserves_KP_nonneg`
in Lean) applied to the small-field and large-field certificates built
above.  The Lean derivation is a single line per convention — no
additional analytic content is added at the overlap step, exactly
matching the manuscript-level claim.

The Proposition 7.1 constants relationship
    ρ_∩ = min(ρ_sf, ρ_lf),
    K_∩ ≤ K_sf + K_lf
emerges from the `Σ'` return of `domGlue_preserves_KP_nonneg` and is
re-exposed below as named theorems. -/

/-- **T8.3 (canonical pilot): the overlap certificate is derived
from T2.3 applied to T8.1 + T8.2.**

The `Σ'` return packages the certificate together with the
Proposition 7.1 constants relationship. -/
def c_cap_canonical_derivation :
    Σ' c_cap : KPCertificate Q' P_nonneg,
      c_cap.rho = min c_sf_canonical.rho c_lf_canonical.rho ∧
      c_cap.K ≤ c_sf_canonical.K + c_lf_canonical.K :=
  domGlue_preserves_KP_nonneg c_sf_canonical c_lf_canonical

/-- The extracted overlap certificate at canonical pilot. -/
def c_cap_canonical : KPCertificate Q' P_nonneg :=
  c_cap_canonical_derivation.1

/-- **Proposition 7.1, ρ part (canonical pilot)**: the overlap rate is
the min of the regime rates. -/
theorem c_cap_canonical_rho :
    c_cap_canonical.rho = min c_sf_canonical.rho c_lf_canonical.rho :=
  c_cap_canonical_derivation.2.1

/-- **Proposition 7.1, K part (canonical pilot)**: the overlap
amplitude is dominated by the sum of the regime amplitudes. -/
theorem c_cap_canonical_K_le :
    c_cap_canonical.K ≤ c_sf_canonical.K + c_lf_canonical.K :=
  c_cap_canonical_derivation.2.2

/-- **T8.3 (Wilson pilot): the overlap certificate is derived from
T2.3 applied to T8.1 + T8.2.** -/
def c_cap_wilson_derivation :
    Σ' c_cap : KPCertificate Q' P_nonneg,
      c_cap.rho = min c_sf_wilson.rho c_lf_wilson.rho ∧
      c_cap.K ≤ c_sf_wilson.K + c_lf_wilson.K :=
  domGlue_preserves_KP_nonneg c_sf_wilson c_lf_wilson

/-- The extracted overlap certificate at Wilson pilot. -/
def c_cap_wilson : KPCertificate Q' P_nonneg :=
  c_cap_wilson_derivation.1

/-- **Proposition 7.1, ρ part (Wilson pilot)**. -/
theorem c_cap_wilson_rho :
    c_cap_wilson.rho = min c_sf_wilson.rho c_lf_wilson.rho :=
  c_cap_wilson_derivation.2.1

/-- **Proposition 7.1, K part (Wilson pilot)**. -/
theorem c_cap_wilson_K_le :
    c_cap_wilson.K ≤ c_sf_wilson.K + c_lf_wilson.K :=
  c_cap_wilson_derivation.2.2

/-! ## Sentinel theorem: the full derivation chain

A single packaged statement that exposes the T8.3-from-T2.3 closure
plus the upstream derivations.  This is the manuscript-level summary
of what this module mechanizes. -/

/-- **The full SU(2) KP derivation chain (canonical pilot).**

Packages:
  1. The algebraic derivation of `ρ_sf` from c_λ, convention factor,
     and g².
  2. The Brydges–Federbush algebraic derivation of K_lf (cluster
     expansion converges at q < 1; `K_lf · (1 - q) ≥ q` for the
     encoded Q′ values).
  3. The construction of the small-field and large-field certificates
     against `P_nonneg`.
  4. The buffer certificate as the `Σ'` output of
     `domGlue_preserves_KP_nonneg`, including the Proposition 7.1
     constants relationship.

This is the Lean form of "T8.3 follows from T2.3 once T8.1 and T8.2
are Lean-derived" for the canonical pilot.  The K_lf clause closes
the "K_lf = 1.0 placeholder" honesty gap from the work_plan's
3.2-upgrade. -/
theorem su2_kp_derivation_canonical :
    -- (1) Small-field rate is derived from upstream data:
    (rho_sf_canonical * g_canonical_squared).eqv (c_lambda * conv_factor_canonical) ∧
    -- (2) K_lf satisfies the Brydges–Federbush cluster-expansion
    -- relation at the encoded Q' values (replacing K_lf = 1.0 placeholder):
    q_canonical_upper ≤ K_lf_canonical * ((1 : Q') - q_canonical_upper) ∧
    -- (3) Cluster expansion converges: q < 1:
    q_canonical_upper < (1 : Q') ∧
    -- (4) Overlap certificate's ρ is min of upstream ρ's:
    c_cap_canonical.rho = min c_sf_canonical.rho c_lf_canonical.rho ∧
    -- (5) Overlap certificate's K is bounded by sum of upstream K's:
    c_cap_canonical.K ≤ c_sf_canonical.K + c_lf_canonical.K :=
  ⟨rho_sf_canonical_derivation,
   K_lf_canonical_derivation,
   q_canonical_lt_one,
   c_cap_canonical_rho,
   c_cap_canonical_K_le⟩

/-- **The full SU(2) KP derivation chain (Wilson pilot).** -/
theorem su2_kp_derivation_wilson :
    (rho_sf_wilson * g_wilson_squared).eqv (c_lambda * conv_factor_wilson) ∧
    q_wilson_upper ≤ K_lf_wilson * ((1 : Q') - q_wilson_upper) ∧
    q_wilson_upper < (1 : Q') ∧
    c_cap_wilson.rho = min c_sf_wilson.rho c_lf_wilson.rho ∧
    c_cap_wilson.K ≤ c_sf_wilson.K + c_lf_wilson.K :=
  ⟨rho_sf_wilson_derivation,
   K_lf_wilson_derivation,
   q_wilson_lt_one,
   c_cap_wilson_rho,
   c_cap_wilson_K_le⟩

end YMGap.Sheaf.SU2KP

/-! ## Axiom-dependency gates (AGENTS.md Rule 1)

Every load-bearing theorem must report `propext` or empty.  No
`Classical.*`, no `Quot.sound`, no `sorryAx`. -/

#print axioms YMGap.Sheaf.SU2KP.c_lambda_value
#print axioms YMGap.Sheaf.SU2KP.rho_sf_canonical_derivation
#print axioms YMGap.Sheaf.SU2KP.rho_sf_wilson_derivation
#print axioms YMGap.Sheaf.SU2KP.rho_sf_canonical_nonneg
#print axioms YMGap.Sheaf.SU2KP.K_sf_canonical_nonneg
#print axioms YMGap.Sheaf.SU2KP.rho_sf_wilson_nonneg
#print axioms YMGap.Sheaf.SU2KP.K_sf_wilson_nonneg
#print axioms YMGap.Sheaf.SU2KP.rho_lf_canonical_nonneg
#print axioms YMGap.Sheaf.SU2KP.K_lf_canonical_nonneg
#print axioms YMGap.Sheaf.SU2KP.rho_lf_wilson_nonneg
#print axioms YMGap.Sheaf.SU2KP.K_lf_wilson_nonneg
#print axioms YMGap.Sheaf.SU2KP.c_cap_canonical_rho
#print axioms YMGap.Sheaf.SU2KP.c_cap_canonical_K_le
#print axioms YMGap.Sheaf.SU2KP.c_cap_wilson_rho
#print axioms YMGap.Sheaf.SU2KP.c_cap_wilson_K_le
#print axioms YMGap.Sheaf.SU2KP.q_canonical_lt_one
#print axioms YMGap.Sheaf.SU2KP.q_wilson_lt_one
#print axioms YMGap.Sheaf.SU2KP.K_lf_canonical_derivation
#print axioms YMGap.Sheaf.SU2KP.K_lf_wilson_derivation
#print axioms YMGap.Sheaf.SU2KP.su2_kp_derivation_canonical
#print axioms YMGap.Sheaf.SU2KP.su2_kp_derivation_wilson
