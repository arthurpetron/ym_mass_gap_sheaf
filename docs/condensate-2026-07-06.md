# The converged Clay core: the condensate ε_k = exp(−c/β₀g²) — CONSTRUCTED summability, OPEN generation

**Deliverables.** `lean/YMGap/Continuum/CondensateGeometricErosion.lean` (wired into
`YMGap.lean`; full `lake build` green = **718 jobs**; `YMGapGuard` **frontier-guard OK = 5**
Clay-frontier types unconditionally uninhabited). Numerics `condensate_numerics.py`
(mpmath dps 50, exact `fractions`). **Committed: nothing** (per instruction). MAIN tree,
NEW file, Lean-core only (`Q'`/`Nat` + the `expNeg` CReal, nonneg only; no
Mathlib/`ring`/`native_decide`; axiom gate `propext`/`Quot.sound`).

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**The condensate ε_k = exp(−c/β₀g²) is GEOMETRIC (r^k), its erosion is GEOMETRICALLY
SUMMABLE (PROVED), and it is ANCHOR-DOMINATED Σε_k < m_phys (PROVED). BUT these are UPPER
bounds on the erosion — the EASY direction (ε_k small ⟹ gap survives) — and they do NOT
close the mass gap. The mass gap needs the condensate to be GENERATED (nonzero): (1) that
the REAL 4D erosion IS the condensate (the renormalon identification), and (2) that the
non-perturbative RG generates margin 0 = m_phys > 0 (the condensate positivity). BOTH are
FREE/ASSUMED inputs — the condensate positivity is DIALED by the self-similar seed, not
constructed. The condensate GENERATION/POSITIVITY is the genuine irreducible 4D Yang–Mills
frontier. No guarded bundle inhabited; the 4D Yang–Mills mass gap remains OPEN.**

The `exp(−c/β₀g²) > 0` positivity that the task worried about splits into a **TRIVIAL**
part (exp of anything is positive — a free CReal fact, `condensate_creal_nonneg`) and the
**GENUINE** part (the REAL theory's non-perturbative scale = a nonzero Λ). The mass gap is
the genuine part, and it is NOT constructed here.

---

## 1. THE CONDENSATE IS GEOMETRIC (task point 1) — PROVED structure

Asymptotic freedom (the PROVED rate shape `AFRateModulus.rate_upper`) gives the two-loop
running `g_k² ≍ 1 − w_k ≍ A/(k+B)`. Substituting into the condensate/renormalon scale:

```
ε_k = exp(−c/(β₀ g_k²)) = exp(−c(k+B)/(β₀A)) = K·r^k,
      r = exp(−c/(β₀A)) ∈ (0,1),   K = exp(−cB/(β₀A)).
```

So the condensate is **GEOMETRIC in k** (constant ratio r), directly confirming task
point 1's claim (Bε = Σr^k < ∞). For SU(2) `β₀ = 22/3` (`= 11/3·C₂(adj=2)`, asymptotic
freedom), `A = 1`, deep-UV anchor `B = 12` (the AF trajectory `w_0 = 11/12`), action
`c = 4` (mpmath dps 50):

| quantity | value | Lean |
|---|---|---|
| ratio `r = exp(−c/β₀A) = exp(−6/11)` | 0.579578 ∈ (0,1) | `condRateExp = 6/11` |
| head `K = exp(−cB/β₀A) = exp(−72/11)` | 0.00143663 | — |
| `ε_{k+1}/ε_k = r` (∀k, exact) | 0.579578 | geometric |

**Lean (PROVED, `[propext, Quot.sound]`):** `condensateCReal k = expNeg((6/11)(k+12))` —
the genuine irrational condensate as a CReal via `CRealExp`; `condensate_creal_nonneg`
(`≥ 0`) and `condensate_creal_le_one` (`≤ 1`): a bona-fide constructive real in `[0,1]`.
**Its positivity is TRIVIAL** (exp is nonneg, `expNeg_geRat_zero`) — the RED HERRING (§5).

---

## 2. SUMMABILITY + ANCHOR-DOMINANCE (task point 2) — PROVED, upper bounds

A rational geometric MAJORANT `condTerm_k = K'·r'^k` with `K' = 1/100 ≥ K_real`,
`r' = 3/5 ≥ r_real` dominates the condensate at every k (exact `fractions`, verified
∀k<200; the domination *itself* is the OPEN identification — §3). For the majorant, BOTH
obligations are PROVED, axiom-clean, Lean-core `decide`/reuse:

- **Geometric summability** `cond_tailSum_le` (`[propext]`): `∑_{j<N} K'·r'^j ≤ K'/(1−r')
  = 1/40 =: Bε` for every window N. Reuses the PROVED `RationalTail.geometric_tail_closure`
  from the one-step recurrence `K' + r'·Bε ≤ Bε` (`cond_recurrence`, zero-axiom `decide`:
  `1/100 + (3/5)(1/40) = 1/40`). This is the geometric analog of the eigenvalue-shift
  telescope — **the condensate is GEOMETRICALLY SUMMABLE, Σε_k < ∞.**
- **Anchor-dominance** `cond_anchorDom` (zero-axiom `decide`): `Bε = 1/40 < 3/10 ≤ m_phys`
  (`m_phys = 1 − e^{−1/e} = 0.30780`), slack ≈ 0.275. **Σε_k < m_phys.**
- **Conditional positive floor** `condensate_floor` (`[propext, Quot.sound]`): the geometric
  ε budget + anchor-dominance ⟹ uniform strictly-positive continuum floor `margin 0 − Bε
  > 0` (∀k), via the PROVED `additiveErosion_uniform_floor`. Open binders — guard-safe.

**The naïve non-anchored sum FAILS** (the honest bad news, `condensate_numerics.py §5`):
`Σ_{k≥0} exp(−c(k+B)/β₀A)` at `B=1` is `1.379 > m_phys`; deep-UV anchoring (`B ≥ 6`)
rescues it (`B=12 → 0.0034`). Exactly as in the eigenvalue-shift route — the anchor depth,
not the block factor, is the operative freedom; the geometric budget is even smaller than
the telescope's `1 − w_0³ = 0.22975`.

So task points 1–2 are answered YES: the condensate ε_k is geometric, summable
(`Σε_k = Bε < ∞`), and anchor-dominated (`Σε_k < m_phys`) — **all PROVED.**

---

## 3. THE GENERATION — is the condensate CONSTRUCTED, or is generation the residual? (task point 3, the crux)

**MAXIMALLY ADVERSARIAL answer: the generation is the residual, on TWO counts, both
UNINHABITED — the two hypotheses of `condensate_floor`:**

**(R1) The renormalon identification** `hmajorant : εReal k ≤ condTerm k`. That the REAL 4D
block-spin additive erosion IS (bounded by) the condensate `exp(−c/β₀g²)`. This is
precisely `BorelRenormalonScaffold`'s finding: the confining-theory renormalon ambiguity is
`~ exp(−c/β₀g²)`, provably **NOT** the perturbative Borel sum
(`connected_reorg_no_resummation`; `IRRenormalonPositiveAxis` UNINHABITED). It is the
non-perturbative renormalon — a **PHYSICS EXPECTATION**, not a construction. The rational
majorant `(1/100)(3/5)^k ≥ exp(−c(k+B)/β₀A)` is numerically true but its *proof for the
real 4D erosion* is exactly this open identification.

**(R2) The condensate positivity / generation** `hanchor : Bε < margin 0`, i.e.
`margin 0 = m_phys > 0`. That the non-perturbative RG **GENERATES** a nonzero condensate
`Λ = a·exp(−1/2β₀g²)`, so the physical dimensionless margin at the UV anchor is a genuine
`m_phys > 0`. `DimensionlessMarginTransmutation` proved this for the IDEAL self-similar
flow — but there `m_phys = 1 − e^{−1/e}` is **DIALED** by the seed `e^{−1}` (the zero-defect
idealization; the doc itself flags this as the `ε ≡ 0` surrogate). The REAL 4D flow's
generation of a nonzero condensate is the open R2. **This is the mass gap itself.**

Λ = a·exp(−1/2β₀g²) is constructible as a concrete CReal via `CRealExp` — but that only
gives a positive *number for a given g*; it does **not** prove the *real 4D theory's*
continuum scale equals a nonzero Λ. The exp-on-CReal residual is discharged (the exponential
is built); the **non-perturbative RG generation** (that the real theory sits on this
trajectory with a nonzero condensate) is the genuine residual.

---

## 4. THE ASSEMBLY (task point 4) — conditional, NOT an inhabitant

`condensate_floor` assembles (a) geometric summability + (b) anchor-dominance + (c) the
condensate as a concrete geometric CReal into the uniform positive floor — **but only as a
CONDITIONAL producer** with open binders on `margin`, `εReal`, `hmajorant`, `hstep`,
`hanchor`. It does **NOT** inhabit `TrueMarginRecursionPhysical`,
`TrueMarginRecursionSummable`, `SingleStepDefectBound`, `UniformSpacingFloor`,
`Tier0Scorecard`, `ClayTarget`, `ClayTargetPinned`, or `FrontierDAG`. **The two open
inputs (R1, R2) ARE the residual.** Inhabiting `TrueMarginRecursionSummable` (which would
cascade to the guarded `UniformSpacingFloor`) requires a constant `εReal ≡ 0` / dialed
`margin` — the exact `ε ≡ 0` fake the transmutation doc refuses; deliberately **not
written**.

---

## 5. MAXIMAL SCRUTINY (task point 5) — the exhaustive audit

The STOP-and-audit condition triggers only if ε_k CASCADES to a guarded bundle. **It does
not.** The audit, field by field:

| claim | status | evidence |
|---|---|---|
| ε_k **IS** the condensate `exp(−c/β₀g²)` | **identified, not proved** | `condensateCReal` builds it; the real-erosion identification (R1) is OPEN (`IRRenormalonPositiveAxis` uninhabited) |
| ε_k is **geometric** r^k | **PROVED (structure)** | AF `g²~A/(k+B)` ⟹ `ε_k = K·r^k`, `r = exp(−c/β₀A) ∈ (0,1)` |
| ε_k is **summable** Σε_k < ∞ | **PROVED** | `cond_tailSum_le`: `Σ ≤ Bε = 1/40` (geometric closed form) |
| ε_k is **anchor-dominated** Σε_k < m_phys | **PROVED** | `cond_anchorDom`: `1/40 < 3/10` (`decide`) |
| the condensate ≠ 0 (**non-pert generation**) | **ASSUMED / DIALED — the residual** | `hanchor` open; `m_phys` dialed by the self-similar seed (R2) |
| every binder | **checked** | `condensate_floor` has open `margin/εReal/hmajorant/hstep/hanchor` |
| NO free-field dodge | **checked** | `condTerm` is a concrete geometric `Q'` (not free); `εReal` majorized by it, not free-standing; but per `CAPSTONE §4` the *bound-on-free-field* inputs remain vacuously fakeable — honestly OPEN because the fake is REFUSED |
| axiom-clean | **checked** | all decls `⊆ {∅, [propext], [propext, Quot.sound]}`, no `sorryAx`/`native_decide`/`Classical` |
| guard reacting | **checked** | `frontier-guard OK: 5 … uninhabited`, unchanged (718 jobs) |

**The CRUX, precisely.** `exp(−c/β₀g²) ≠ 0` is a CONSTRUCTION only in the TRIVIAL sense
(exp is positive — `condensate_creal_nonneg`, free). The mass gap is NOT that trivial fact;
it is (R2) the real 4D theory generating a nonzero condensate scale `Λ`, which is a
**FREE/ASSUMED input** here (the anchor `m_phys > 0` is dialed, not derived from the real
non-perturbative RG). Therefore the **condensate positivity (the non-perturbative
generation)** is the genuine residual — exactly as the task's most-adversarial branch
anticipated.

---

## 6. HONEST FINAL VERDICT

- **CONSTRUCTED (the easy direction, all PROVED axiom-clean):** the condensate ε_k =
  exp(−c/β₀g²) is geometric (`condensateCReal`), its erosion is geometrically summable
  (`cond_tailSum_le`, Σ ≤ 1/40) and anchor-dominated (`cond_anchorDom`, 1/40 < 3/10 ≤
  m_phys), assembling to a conditional positive continuum floor (`condensate_floor`).
- **NOT CONSTRUCTED (the genuine residual, both UNINHABITED):**
  1. the **renormalon identification** — the real 4D erosion IS the condensate (R1;
     non-perturbative, a physics expectation, `BorelRenormalonScaffold`);
  2. the **condensate positivity / non-perturbative generation** — that the real RG
     generates a nonzero `Λ`, so `margin 0 = m_phys > 0` (R2; dialed, not derived).
- Summability is an UPPER bound (ε_k small = good); the mass gap needs the condensate
  GENERATED (nonzero) — the OPPOSITE, harder direction. The task's central adversarial
  hypothesis is **CONFIRMED**: the condensate positivity, not its summability, is the crux,
  and it is a free/assumed input.

**No guarded frontier bundle is inhabited; nothing is faked; the converged Clay core (the
condensate ε_k) has its summability/anchor-dominance CONSTRUCTED but its non-perturbative
GENERATION/POSITIVITY OPEN — the genuine irreducible 4D Yang–Mills frontier. The mass gap
remains OPEN.**

---

## 7. Build / guard / axioms

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (718 jobs).
```

`CondensateGeometricErosion.lean`, 11 gated load-bearing decls,
`#print axioms ⊆ {∅, [propext], [propext, Quot.sound]}`. Reuses PROVED
`additiveErosion_uniform_floor`, `RationalTail.geometric_tail_closure`,
`AnchorDominance.{mPhysLB, qLtLe, qZeroLeOne, zero_tailSum_le}`, `CRealExp.expNeg`.
No `Classical.*`, no `native_decide`, no `sorry`/`sorryAx` (banned tokens in prose only).
```
condExponent_nonneg          : [propext, Quot.sound]
condensate_creal_nonneg      : [propext, Quot.sound]
condensate_creal_le_one      : [propext, Quot.sound]
condTerm_nonneg              : [propext]
cond_recurrence              : (none)
tailSum_condTerm_eq_finSum   : (none)
cond_tailSum_le              : [propext]          ← geometric summability
cond_anchorDom               : (none)             ← anchor-dominance, zero-axiom
condensate_floor             : [propext, Quot.sound] ← conditional positive floor
cond_floor_pos_at_anchor     : (none)
cond_anchor_from_mphys_lb    : [propext]
```
