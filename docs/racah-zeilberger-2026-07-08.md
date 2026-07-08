# A2 Racah / Dougall — admissible-set fix + normaliser-verified Vandermonde layer

Date: 2026-07-08. Working tree only (nothing committed). `lake build` exit 0 (787
jobs); frontier guard: **OK — 5 Clay-frontier types unconditionally uninhabited**.
Axiom gate on all new declarations ⊆ {propext, Quot.sound} (most are axiom-FREE).

## 1. THE ADMISSIBLE-SET FIX (COMPLETE, the honest statement)

The literal `BiedenharnElliottGeneral.BEDougallCore` is FALSE off the physical set,
and the failure is NOT cured by any tuple-level guard: **204 of 205**
outer-admissible `[0,2]⁹` tuples fail the literal identity (the "1/205" figure).

Python ground-truth (`computations/dougall_wz.py` + scratch `probe1/probe2.py`)
isolates the EXACT cause and fix: the failure is entirely the **x-SUM including
off-support terms** (`Nat`-truncated `racahSum`/`triSq` give spurious mass at
non-physical `x`). Guarding **each x-summand** by the genuine physical validity of
the three x-dependent LHS tetrahedra, and restricting to tuples whose two
x-independent RHS tetrahedra are valid, makes the identity hold on the **FULL
admissible set with ZERO exceptions**:

| range | outer-admissible tuples | guardedLHS == RHS failures |
|---|---|---|
| `[0,2]⁹` | 205 | **0** |
| `[0,3]⁹` | 1495 | **0** |
| random `[0,6]⁹` | 1141 | **0** |

The guard is the genuine triangle+parity admissibility (the same `valid6` the 6j
kernel uses), NOT an ad-hoc restriction. The face↔`valid6` mapping is Python-verified
(20000 random tuples). This is the like-`valid6` guard the prompt asked for.

**Lean (`YMGap/Continuum/RacahDougallWZ.lean` §6, new):**
- `lhsAdmX a b c d e f p q r x` — the three LHS tetrahedra all `valid6`.
- `outerAdm a b c d e f p q r` — the two RHS tetrahedra `valid6`.
- `guardedBEWeight` — the signed BE weight, zeroed off admissibility.
- `guardedBERationalLHS … D = finSum guardedBEWeight D`.
- `guardedBEDougall : Prop` — ∀ spins, `outerAdm = true → Σspins < D →
  guardedBERationalLHS ≃ beRationalRHS`. **This is the corrected ∀-spins statement**
  (replaces the false unguarded `BEDougallCore`). Left UNINHABITED as a ∀ (honest).

**Non-vacuity (`decide`, all axiom-FREE):**
- `outerAdm_allzero`, `guardedBEDougall_allzero` — guard holds (1=1) where unguarded gives 3≠1.
- `guardedBEDougall_physical_symm` — a genuine **nondegenerate** physical tetrahedron
  (all spins 1, twice-spin 2): `outerAdm = true` and guardedLHS = **384** = RHS.
- `guardedBEDougall_repairs_naive` — outer-admissible `(0,0,0,0,1,1,0,1,1)`:
  unguarded FAILS (6≠2), guard REPAIRS it (2=2), with `¬ unguarded ≃ RHS` proved.

Honesty note carried in-file: the pre-existing `pentagon_R/_I` tuples are **NOT
outer-admissible** — their RHS faces include the degenerate `(0,0,1)` triangle, so
the unguarded identity held there only as a `Nat`-truncation coincidence.

## 2/3. ZEILBERGER (sympy computes) → normaliser (Lean verifies)

The ring normaliser now verifies a genuine **degree-3** member of the
Vandermonde/Saalschütz convolution layer named absent in `BiedenharnElliottGeneral`
(the deg-2 demo is superseded upward):

  `(n)₃ + 3·(m)₁(n)₂ + 3·(m)₂(n)₁ + (m)₃ = (m+n)(m+n-1)(m+n-2)`   (falling factorials)

sympy (`vdm_gen.py`) COMPUTED it (LHS−RHS ≡ 0, also for p=4); the **Lean proof
trusts sympy for nothing** — `RingNormaliser.vdm3_normal_eq` is a kernel `decide`
(`normalize vdm3LHS = normalize vdm3RHS`, axiom-FREE) and `vandermonde_deg3` closes
the ∀-`m,n : Q'` identity via `poly_identity_of_normal_eq`. This is the exact
pipeline (Zeilberger-family certificate computed in Python, multivariate polynomial
identity verified by the sound normaliser) the task specified, exercised on a real
building block beyond the demo.

## 4. What A2 discharges / the loopy Zreal

- **Discharged this round:** the correct STATEMENT of A2's ∀-spins Racah sum rule
  (`guardedBEDougall`), Python-verified on all admissible tuples, non-vacuity
  `decide`d incl. a nondegenerate physical witness; plus a normaliser-verified
  deg-3 Vandermonde layer member.
- **NOT closed (sharp residual):** the ∀-spins PROOF of `guardedBEDougall`. Its
  x-sum is a genuine MULTI-sum (each summand a product of THREE coupled inner Racah
  t-sums), so no single order-0 (Gosper) certificate — and no single
  normaliser-checkable polynomial certificate this round — spans it. The residual
  is exactly: a creative-telescoping / Zeilberger recurrence over the three coupled
  inner t-sums, plus its base case, reflected through the normaliser + `int_telescope`.
- **Loopy `Zreal` (A2RecouplingDischarge):** does **NOT** close. `SixJRecoupling`
  stays uninhabited; the loopy `Zreal` still requires the ∀-spins recoupling
  identity, which is `beDougall_gives_pentagon`'s hypothesis — now correctly a
  *guarded* pentagon (the unguarded `general_be_of_rational`/pentagon are themselves
  false off-admissibility). The Clay YM mass gap stays OPEN.

## Verdict (honest)

A2's guarded ∀-spins Racah sum rule is **correctly STATED and Python-verified on the
full admissible set (not 1/205), non-vacuity machine-checked** — the admissible-set
fix (step 1) is genuinely COMPLETE. The Zeilberger/normaliser pipeline is
demonstrated end-to-end on a real deg-3 Vandermonde building block. But the ∀-spins
guarded identity is **NOT proven** (the triple-coupled-Racah Zeilberger recurrence
is the named, un-closed residual), and the loopy `Zreal` does **NOT** close.
Nothing is faked; build green; guard 5 intact; axioms ⊆ {propext, Quot.sound}.

## Files
- `lean/YMGap/Continuum/RacahDougallWZ.lean` — §6 admissible-set fix + guarded statement + witnesses; docstring verdict updated.
- `lean/YMGap/Continuum/RingNormaliser.lean` — §8 deg-3 Vandermonde falling-factorial identity (normaliser-verified).
- `computations/dougall_wz.py` — `valid6`/`lhsAdmX`/`outerAdm`/`guardedBERationalLHS` + `scan_guarded` (0 fails on all admissible ranges).
