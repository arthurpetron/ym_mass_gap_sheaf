# A2 `guardedBEDougall` — the triple-coupled Zeilberger attack

**Verdict up front (honest):** A2's guarded ∀-spins Racah/Dougall sum rule
`guardedBEDougall` is **NOT closed** this pass. The coupled recurrence is beyond
one pass, and the exact remaining step is now **named sharply** (not a vague gap):
a *multivariate* creative-telescoping certificate over the coupled
`(x; t₁,t₂,t₃)` simplex. The classical *single-variable* Zeilberger route the
task hoped for (step 2) is **structurally refuted** — see below. Nothing faked;
build green; guard unchanged (stays at 5 — A2 is off the frontier-guard path).

---

## 1. Structure of the coupled sum (Python `computations/racah_coupled.py §1`)

```
guardedBERationalLHS(a..r, D)
  = Σ_{x<D} [lhsAdmX]·(−1)^{(Σj+x)/2}·(x+1)
            · S₁(x)·S₂(x)·S₃(x)
            · Δ²(a,b,x) Δ²(c,d,x) Δ²(e,f,x)
```
each inner factor is itself a Racah `t`-sum **coupled to the outer index `x`**:
```
S₁(x)=racahSum(a,b,x,c,d,p)  over {a b x; c d p}   (Σ_{t₁})
S₂(x)=racahSum(c,d,x,e,f,q)  over {c d x; e f q}   (Σ_{t₂})
S₃(x)=racahSum(e,f,x,b,a,r)  over {e f x; b a r}   (Σ_{t₃})
```
- **Coupling:** the three inner sums share the *outer* index `x` (and two outer
  labels each); given `x` they are mutually independent. So the LHS is a genuine
  **4-fold nested sum** `(x; t₁,t₂,t₃)`.
- RHS = `S_R1·S_R2·Δ²(p,q,r)` — a 2-fold sum. The identity is a 4-fold ⇒ 2-fold
  reduction (the Biedenharn–Elliott pentagon), not a single antidifference.

## 2. Ground-truth (residual 0)

- exhaustive `[0,3]⁹`: **1495** outer-admissible tuples, **0** failures;
- random `[0,8]⁹`: all sampled outer-admissible tuples pass;
- (re-confirms the admissible-set fix already recorded in `dougall_wz.py`).
- Parity: on every admissible `x`, `Σj+x` is **even** (phase `(−1)^{(Σj+x)/2}`
  is well-defined and integer).

## 3. The univariate-Zeilberger route is REFUTED (structural, not a failed search)

Every single spin variable has **bounded admissible support**: the triangle
inequalities `|a−b| ≤ x ≤ a+b` (and analogues for every label) truncate every
one-parameter slice.

- Longest admissible run varying **any one** of the nine labels over `[0,3]⁹`
  bases = **4** (≤ **6** over `[0,6]⁹`, scanning 60 000 random bases).
- Within the longest run (len 6) an exact rational nullspace search finds **NO**
  common order-≤4 / deg-≤5 `P`-recurrence annihilating both LHS and RHS
  sequences.

⇒ There is **no infinite one-parameter holonomic sequence** to run OR verify a
classical Zeilberger recurrence on. `guardedBEDougall` is a genuinely **finite
multivariate** identity, *not* a member of a 1-parameter `P`-recursive family.
This kills the "recurrence in one outer label" plan cleanly.

## 4. The EXACT remaining coupled step

A **multivariate creative telescoping** (Wegschaider / Apagodu–Zeilberger style)
over the coupled `(x; t₁,t₂,t₃)` simplex: a certificate `R` (rational in all nine
labels + four summation indices) whose Δ-closure telescopes the 4-fold summand to
the RHS, **plus** the natural-boundary vanishing on the triangle walls. Cleared to
integer-coefficient polynomial form this certificate has **factorial-scale degree**
in the nine labels — beyond the kernel-`decide` reach of the current
`RingNormaliser` (which dispatches small fixed-degree identities;
`vandermonde_deg2/3/4` are the largest members this round). **That
normaliser-capacity gap for the coupled certificate is the sole obstruction.**

Carried in Lean as the named residual
`RacahDougallWZ.CoupledCreativeTelescoping` (`:= guardedBEDougall`, uninhabited).

## 5. Genuine Lean increments this pass (axiom-clean, `propext`/`Quot.sound`)

- `RingNormaliser.vandermonde_deg4` (+ `vdm4_normal_eq`): the degree-4
  Chu–Vandermonde falling-factorial convolution
  `(n)_4 + 4(m)_1(n)_3 + 6(m)_2(n)_2 + 4(m)_3(n)_1 + (m)_4 = (m+n)_4`, a **new
  member of the exact "Vandermonde/Saalschütz convolution layer"** the residual
  names as its machinery — **normaliser-verified** (`decide` on
  `normalize LHS = normalize RHS`, 553 ms; sympy trusted for nothing).
  `vdm4_normal_eq` depends on **no axioms**.
- `RacahDougallWZ.CoupledCreativeTelescoping` (+ `_eq`): the sharply-named
  residual carrier + honest module verdict recording the structure, the
  univariate refutation, and the exact multivariate step.

## 6. What A2 / loopy-`Zreal` discharges

**Nothing new is discharged.** `guardedBEDougall` is uninhabited ⇒
`general_be_of_rational` (guarded) is not fed ⇒ the A2 signed-6j pentagon is not
closed ⇒ `A2RecouplingDischarge`'s loopy `Zreal` (which needs the full 6j
recoupling identity, strictly stronger than the smallest-tetrahedron value it
already carries) **does not close**. Frontier guard stays at **5/5 uninhabited**
(A2/Racah is off the frontier-guard critical path — correct, not a regression).

## 7. Verification

- `lake build` (full) exit **0**; `YMGapGuard` built (frontier uninhabitedness
  guard passes).
- `#print axioms`: `vandermonde_deg4` = `[propext, Quot.sound]`,
  `vdm4_normal_eq` / `CoupledCreativeTelescoping_eq` = no axioms. Within gate.
- No `sorry` / `native_decide` / new `axiom` introduced. C (loop counter)
  unchanged; guard status unchanged (5).

## 8. Honest bottom line

The coupled Zeilberger attack was pushed to the point of a **sharp, structural
diagnosis**: single-variable Zeilberger is impossible here (bounded triangle
support), and the residual is exactly a multivariate `(x;t₁,t₂,t₃)`
creative-telescoping certificate whose cleared polynomial form exceeds the
current Lean-core normaliser's decide capacity. The next genuine attack is either
(a) grow the normaliser to a *streaming / Horner* evaluator that can verify a
high-degree multivariate certificate without full canonical-form `decide`, or
(b) derive the certificate as a *composition* of lower-degree Saalschütz members
(the layer `vandermonde_deg2/3/4` seeds) so each factor is normaliser-checkable.
`guardedBEDougall` remains the correct statement; the Clay YM mass gap stays OPEN.
