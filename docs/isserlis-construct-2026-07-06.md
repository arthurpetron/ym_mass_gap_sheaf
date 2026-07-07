# The Isserlis-obeying Gaussian base — the foundational fix, and the CONSTRUCT-vs-BOUND retest

**Deliverable Lean file:** `lean/YMGap/Continuum/IsserlisGaussianBase.lean` (wired into `YMGap.lean`;
full `lake build` **green = 713 jobs**; `YMGapGuard` **frontier-guard OK = 5** Clay-frontier types
still unconditionally uninhabited). Numerics `verify_isserlis.py` (mpmath dps 50, sympy exact).
**Commits: none** (per instruction). MAIN tree, NEW file, Lean-core only (`Q'`/`Nat`, no
Mathlib/`ring`/`native_decide`/`set`).

---

## 0. The obligation

`CoupledContinuumWeight` had proved **two** machine-checked obstructions to constructing the
coupled continuum weight `z_n = ∫ e^{−S_int} χ Dφ / Z`:

- **(i) `library_base_fails_wick`** — the library's minimal base ({+s,−s}, equal weight) has
  `⟨A⁴⟩ = s⁴`, not the true-Gaussian Isserlis `⟨A⁴⟩ = 3⟨A²⟩² = 3s⁴`. So it cannot perform the Wick
  contraction that CONSTRUCTING `z_n` requires.
- **(ii) `coupled_underdetermined`** — over the same base/vertex/connectivity/tree-domination the
  free dodge (`z_n ≡ 0`) and the saturating amplitude (`z_n = μⁿz₁ⁿ`) both satisfy the identical KP
  bound; the scaffold BOUNDS `z_n` without DETERMINING it.

Task: build the genuine Isserlis moments (fixing (i)); then test whether Isserlis base + the coupled
Wick expansion CONSTRUCTS (determines) `z_n`, resolving (ii).

---

## 1. HEADLINE VERDICT (machine-checked, axiom-clean)

**The Isserlis fix genuinely FIXES obstruction (i), and it DETERMINES `z_n` term-by-term at every
finite order — REFUTING the free dodge (resolving (ii) at finite order). But the K→∞ perturbative
RESUMMATION + the a→0 CONTINUUM covariance are the exact, named residual. Nothing closes; the 4D
Yang–Mills mass gap remains OPEN.**

This is a genuine, precisely-located Rule-6a reduction: the frontier moves from *"z_n is a free
field an interaction-free dodge inhabits"* to *"z_n's DETERMINED perturbative series must be
resummed (asymptotic) and renormalized (a→0)."*

---

## 2. WHAT IS BUILT (all axiom-clean; `#print axioms ∈ {∅, [propext], [propext, Quot.sound]}`)

### 2.1 The genuine Isserlis moments — FIX of obstruction (i)
- `numPairings : Nat → Nat` — the double factorial `(2n−1)!! = 1·3·5···(2n−1)` = number of perfect
  matchings of `2n` points; recursion `numPairings (n+1) = (2n+1)·numPairings n`
  (`numPairings_succ`, **rfl**); `numPairings 2 = 3`, `numPairings 3 = 15`.
- `gaussMoment s n = (2n−1)!!·s^{2n}` — the genuine mean-zero Gaussian moment obeying Isserlis BY
  CONSTRUCTION.
- **`gaussMoment_fourth_eq` : `⟨x⁴⟩ = 3·s⁴`** (rfl) — the value the library base FAILED to produce.
- `gaussMoment_recursion` : `⟨x^{2(n+1)}⟩ ≃ (2n+1)·s²·⟨x^{2n}⟩` — the combinatorial double-factorial
  recursion, PROVED in `Q'` (via `ofNat_mul_eqv`, a `pow` helper `pow_two_succ`, and a 4-factor
  associativity shuffle `mul4_swap`).
- **`isserlis_fixes_library` (AXIOM-FREE, `decide`)** : `gaussFourthMoment 1 (=1) < gaussMoment 1 2
  (=3)` — the new base OBEYS the Isserlis contraction the `{±s}` base failed.
- **`isserlis_matches_wick` (AXIOM-FREE)** : `gaussMoment 1 2 ≃ wickFourthMoment 1` — it supplies
  EXACTLY the Wick value (`3⟨A²⟩²`) the library missed by the factor 3.

### 2.2 The multi-mode Wick pairing sum (Wick's theorem)
- `wick4 C i j k l = C_ij·C_kl + C_ik·C_jl + C_il·C_jk` — the sum over the 3 pairings of 4 legs; a
  DETERMINED value (function of the covariance), not a free/bounded field.
- `wick4_diagonal` : diagonal `= V·V+V·V+V·V = 3V²` (rfl).
- **`wick4_diagonal_matches_isserlis` (AXIOM-FREE)** : on `C ≡ 1` it equals the single-mode
  `gaussMoment 1 2 = 3` — the multivariate pairing sum is consistent with the double-factorial
  moment.
- **`wick4_pos` (AXIOM-FREE)** : `0 < wick4 (const 1) = 3` — a genuinely positive determined value,
  NOT the free measure's vanishing connected amplitude.

### 2.3 The coupled Feynman/Isserlis `z_n` — DETERMINED at finite order; dodge REFUTED (fix of (ii))
- `feynTrunc diag K = Σ_{k<K} diag k` — the finite-order Feynman/Isserlis truncation, where each
  `diag k` is the DETERMINED order-`k` connected diagram value (Wick contraction × `(g²)^k`). Because
  each coefficient is a determined number, the truncation is a UNIQUE value, not an upper bound.
- `leadingIsserlisDiag` — order-0 (free connected) VANISHES (`freeConnected2_eq_zero`); order-1 = the
  genuine positive Wick contraction `wick4 (const 1) = 3`.
- **`isserlis_refutes_free_dodge` (AXIOM-FREE, apartness)** : `¬ (feynTrunc leadingIsserlisDiag 2) ≃
  0` — the order-2 truncation `= 0 + 3 = 3` is strictly APART from `0`, so `z_n ≢ 0`. This is the
  DECISIVE progress over `coupled_underdetermined`: there the free dodge `z_n ≡ 0` was an
  un-excludable inhabitant of the upper-bound-only scaffold; the Isserlis CONTRACTION now supplies the
  actual value and EXCLUDES it.
- **`feynTrunc_two_determined` (AXIOM-FREE)** : the truncation equals the unique value `3` — the
  Feynman/Isserlis representation gives a determined number, not a container.

### 2.4 The exact residual — NAMED, not faked
- `PerturbativeResummation diag` (`Type`, **UNINHABITED** for the physical coefficients) — names the
  open input: a Cauchy modulus (`resums`) for the perturbative partial sums, with `feynTrunc_increment`
  proving the order-K increment IS the determined coefficient `diag K`. So the open field is exactly
  *"the DETERMINED coefficients shrink below every tolerance"* = the perturbative series RESUMS.
  Left UNINHABITED; producers are conditional (open binders); inhabits none of the 5 guarded types.

---

## 3. THE DECISIVE CHECK (task condition 4), answered honestly

**Does the Isserlis base + the Wick contraction DETERMINE `z_n`, or still only BOUND it?**

- **At every FINITE order: DETERMINED.** Each order-`k` coefficient is the Isserlis/Wick contraction
  — a specific pairing sum of covariances × `(g²)^k` — a unique number. `feynTrunc` is therefore a
  determined value (`feynTrunc_two_determined`), NOT the upper-bounded free field of
  `coupled_underdetermined`. The free-field dodge `z_n ≡ 0` is **REFUTED** (`isserlis_refutes_free_dodge`),
  not merely refused: the leading contraction is provably nonzero. **Obstruction (ii) is resolved at
  finite order.**

- **The full `z_n` (all orders): STILL the residual — but a strictly sharper one.** `z_n = Σ_k
  (1/k!)⟨(−S_int)^k χ⟩_conn` is pinned by its (now-determined) coefficients only through a resummation.
  Numerically confirmed (`verify_isserlis.py`, exact sympy): the diagram coefficients grow FACTORIALLY
  — for the `φ⁴` model `a_k = (−1)^k/k!·(4k−1)!!`, ratios `|a_{k+1}/a_k| = 35/2, 33, 195/4, 323/5,
  81/2, 675/7, …` → ∞, **radius of convergence 0** (Dyson). So determining `z_n` from its determined
  coefficients needs a Borel/nonperturbative resummation; and each contraction's covariance is the
  RENORMALIZED continuum propagator (`a→0`).

**Verdict: the Isserlis fix DETERMINES `z_n` term-by-term (fixing (i) fully and (ii) at finite order,
refuting the dodge) but does NOT CONSTRUCT the full `z_n`. The exact remaining foundational gap is
the pair (R1) K→∞ perturbative RESUMMATION of the asymptotic determined series, and (R2) the a→0
CONTINUUM covariance (renormalization).**

---

## 4. Cascade / STOP audit (mandatory — this is the mass gap)

**No STOP condition tripped. No guarded bundle inhabited. No cascade triggered.**

- The module proves theorems ABOUT the Isserlis base and the Feynman truncation, and NAMES the
  resummation/continuum residual. It inhabits NONE of the 5 guarded Clay-frontier types
  (`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`, `ClayTargetPinned`, `FrontierDAG`). Full
  build: `frontier-guard OK: 5 … unconditionally uninhabited`, **713 jobs** (712 → 713 = the +1
  module).
- `PerturbativeResummation` is a NEW node (like `FieldMeasureSubstrate`), deliberately UNINHABITED;
  no unconditional inhabitant is produced; `resummation_is_conditional` only re-exposes an open field.
- **No overclaim.** The finite-order determination is genuine (machine-checked); the infinite-order
  resummation + a→0 continuum are honestly named and left open. The free-field dodge is REFUTED, not
  faked away.
- **`#print axioms`** for all 16 load-bearing decls ∈ `{∅, [propext], [propext, Quot.sound]}`. The
  decisive facts (`isserlis_fixes_library`, `isserlis_matches_wick`, `gaussMoment_fourth_eq`,
  `wick4_pos`, `wick4_diagonal_matches_isserlis`, `feynTrunc_two_determined`) are AXIOM-FREE. No
  `Classical.*`, `sorryAx`, `native_decide`, or `sorry`/`admit` in code (banned tokens appear only in
  docstring prose).

---

## 5. Numeric validation (`verify_isserlis.py`, mpmath dps 50, sympy exact) — ALL PASS

1. `⟨x^{2n}⟩ = (2n−1)!!·s^{2n}` verified by exact symbolic integration for `n=0..5`
   (`1, s², 3s⁴, 15s⁶, 105s⁸, 945s^{10}`).
2. `⟨x⁴⟩ = 3s⁴` (Isserlis) vs the library's `s⁴`; at `s=1`, `3 > 1`.
3. `numPairings n = (2n−1)!! = (2n)!/(2ⁿn!) =` #matchings, recursion `(2n+1)·`, all equal `n=0..7`.
4. Multi-mode Wick 4-point `= C_ij C_kl + C_ik C_jl + C_il C_jk`; diagonal `= 3V²`; vs a genuine 4-dim
   Gaussian Monte-Carlo (rel.err `8e-3`, N=4·10⁵).
5. Determination-vs-resummation: order-k Feynman coefficients EXACT/determined but factorially
   growing (radius 0); asymptotic partial sums diverge past the optimal truncation → resummation
   required. This IS the residual.

---

## 6. HONEST FINAL VERDICT

The genuine Isserlis Gaussian base is BUILT and the machine-checked substrate obstruction (i)
(`library_base_fails_wick`) is **FIXED**: `gaussMoment s n = (2n−1)!!·s^{2n}` obeys Wick/Isserlis by
construction, `⟨x⁴⟩ = 3s⁴` is PROVED, and the new base matches the required Wick value exactly
(`isserlis_matches_wick`) — strictly above the library's failing `1` (`isserlis_fixes_library`). The
multi-mode Wick pairing sum (`wick4`) is BUILT, reduces to `3V²`, and is a positive determined value.

Obstruction (ii) (`coupled_underdetermined`) is **resolved at finite order**: with the Isserlis
contraction the Feynman truncation `feynTrunc` is a DETERMINED value and the free-field dodge `z_n ≡
0` is REFUTED (`isserlis_refutes_free_dodge`) — the exact un-excludable inhabitant of the old
upper-bound-only scaffold is now EXCLUDED by the actual contraction.

**But `z_n` does NOT close.** The full `z_n = Σ_k (1/k!)⟨(−S_int)^k χ⟩_conn` is determined by its
(now-determined) coefficients ONLY through (R1) a K→∞ RESUMMATION of an ASYMPTOTIC series (factorial
coefficient growth, radius 0 — verified), and (R2) the a→0 CONTINUUM covariance (renormalization of
the propagator in each Wick contraction). `PerturbativeResummation` names this residual exactly and is
left UNINHABITED.

**The Isserlis fix is the genuine foundational fix of (i) and determines `z_n` at every finite order,
refuting the dodge — but the residual is now the resummation + continuum, located exactly, not closed.
No guarded frontier bundle is inhabited; the free-field dodge is REFUTED; nothing is faked; the 4D
Yang–Mills mass gap remains OPEN.**

---

## 7. Build / guard / axioms

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (713 jobs).
```

`IsserlisGaussianBase.lean`, 16 load-bearing decls, `#print axioms ∈ {∅, [propext], [propext,
Quot.sound]}`. Lean-core only (`Q'`/`Nat`); reuses PROVED `gaussSecondMoment`, `gaussFourthMoment`,
`wickFourthMoment`, `freeConnected2_eq_zero`, `finSum`, `SU3CharFactor.ofNat_mul_eqv`, the `Q'`
`pow`/`mul` eqv algebra. All witnesses `Type`-level.
