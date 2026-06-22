# Publishable-results audit: what could we write *so far* (2026-06-22)

Method: a full inventory of candidate-original content in the Lean (3 parallel reads), then literature
verification of every genuine candidate (5 parallel skeptical deep-research passes, arXiv/AFP/repos).
Honest framing up front: **the defensible contributions are FORMALIZATION artifacts, not new theorems.**
The literature search found prior art for essentially every *mathematical* candidate; the genuinely
novel, defensible units are the constructive/Mathlib-free/axiom-clean *formalizations*. That is a real,
publishable contribution class (ITP / CPP / JAR / JFR) — it is just not "new mathematics."

This counts only what is ALREADY proved & axiom-clean ("so far"), not the open continuum walls.

## Verification verdicts (what the literature actually says)

| Candidate | Verdict | Key prior art |
|---|---|---|
| Δ_N = S_N²·P_N q-Hankel factorization | **re-derivation** of Stieltjes–Wigert / q-Hermite Hankel determinants + Christoffel twist; telescoping = Desnanot–Jacobi; P_N≥0 = known q-total-positivity | Krattenthaler (math/9902004, 2003.01676, 2101.04225); Pan–Zeng (2107.10608); Sokal (1807.03271) |
| SU(2) worst-case gap reduction | (A) textbook Casimir; (B) packaged uniform reduction **not found published**, BUT the worst-case *direction* is **contestable** (larger groups tend to be *easier* at fixed coupling) — value hinges on actually proving the η-monotonicity | Osterwalder–Seiler (1978); Seiler LNP 159; Shen–Zhu–Zhu (2204.12737, N-uniform by direct estimate) |
| located spectral gap of compact op | **fully known** — compact-op spectrum computable, bounded only lower-semicomputable is *exactly* Brattka's theorem; finite-matrix case trivial | Brattka (J.UCS 2005); Brattka–Dillhage; Spitters; Coquand–Spitters (0808.2705) |
| clustering⇒gap converse | math **fully known** (transfer-operator clustering⇔gap); constructive division-free version novel only as a *formalization sliver*; converse false for general Hamiltonians (state only for finite/compact transfer op) | Ruelle/Perron–Frobenius; Hastings–Koma (math-ph/0507008) caveat |
| log-concavity falsity witness | phenomenon **fully known** (tensor/fusion log-concavity fails in general); our instance is a minor data point; FIX framing (convolution *does* preserve log-concavity — failure is fusion truncation/reflection) | Okounkov (math/0002085); Chindris–Derksen–Weyman (math/0610819) |

## Formalization prior art (the positioning constraints)

- **Constructive reals:** CoRN (Coq) is the only true analog — decades old, classical-interoperating. **No Mathlib-free, intuitionistic, axiom-clean Lean real library with exp/trig/sqrt/cbrt exists.** ⇒ our substrate is **first-of-its-kind in Lean**.
- **OS / reflection positivity:** **OSforGFF** (Lean+Mathlib, ~32k lines, 0 sorries/axioms) already proved all OS axioms incl. RP — **for the free Gaussian field** (arXiv:2603.15770). PhysLean heading to free-field Glimm–Jaffe. ⇒ we CANNOT claim "first RP"; we CAN claim "first RP for an **interacting/lattice-gauge** functional, via Schur/Osterwalder–Seiler, on a **constructive Mathlib-free** substrate." MUST cite OSforGFF.
- **Cluster expansion / KP:** competitor **Shariq81/yang-mills-mass-gap** (Coq) has overlapping files but is classical, choice-heavy, and its physics is **assumed** (`Axiom`/`Parameter`/`Hypothesis`); headline theorem `∃ m>0` is hollow. No honest KP/cluster formalization exists in AFP/Coq/Lean. ⇒ we CAN claim "first **constructive, axiom-clean, content-derived** KP/cluster tower." MUST cite & differentiate.
- **YM mass gap in a prover:** only the Clay *statement* is formalized (LeanMillenniumPrizeProblems). No legitimate machine-checked proof of even the lattice strong-coupling gap exists.

## The paper list (ranked, honest)

### Tier 1 — defensible, genuinely-novel formalization artifacts

**P1 — "A Mathlib-free, intuitionistic, axiom-clean constructive real-analysis library in Lean 4."**
Q' exact rationals, CReal regular reals, with sqrt (Heron), cbrt (located bisection), exp, sin/cos
(via the exponential magnitude subseries) all from scratch; only `propext`/`Quot.sound`; no choice/LEM.
Novel techniques to highlight: division-free reciprocal & Cauchy modulus, trig-via-exponential-subseries,
the `δ²≤δ` product-bound, the "cubing trick" (cube inequalities → pure-Q', eliminating CReal/cube-roots).
**Strongest, most defensible claim.** Venue: ITP/CPP/JAR/JFR. Cite CoRN as the deliberately-unused precedent.

**P2 — "Formalizing Osterwalder–Schrader reflection positivity for a lattice gauge heat-kernel functional."**
OS2/RP via Schur / Osterwalder–Seiler diagonalization of the SU(2) heat-kernel measure (diagonal weighted
SOS, no Gram-PSD detour); the finite-order Gram PSD (2×2, 3×3) content; the genuine OS-axiom predicates.
Claim narrowly: **first RP for an interacting/lattice-gauge functional, on a constructive substrate.**
MUST position against OSforGFF (free field). Venue: ITP/CPP. The q-Hankel Δ_N=S_N²·P_N material lives here
as a *formalization* of the (known) q-total-positivity structure — cite Krattenthaler/Pan–Zeng/Sokal, do
not present as a discovery.

**P3 — "A constructive Kotecký–Preiss / polymer cluster-expansion tower in Lean."**
Polymer model + Haar single-rep collapse via proof-relevant connectivity chains; Mathlib-free
lattice-animal counting via walk-injection (`choiceSeqs`, deg^{2n}); the clustering⇒gap converse
(division-free Bernoulli, stated only for the finite/compact transfer op); the KP limit engine + the
UniformClusterBound⇒positive-rate bridge. Claim: **first constructive, axiom-clean, content-derived
(not assumed) KP/cluster tower.** MUST cite & differentiate Shariq81 (classical, assumption-loaded) and
Kotecký–Preiss (1986). Venue: ITP/CPP/JAR.

(P1–P3 could also be ONE "system/experience" paper: "Constructive lattice Yang–Mills in Lean," with the
substrate as the through-line and OS/cluster as applications — likely the highest-impact single venue.)

### Tier 2 — minor notes / conditional

**P4 — the all-simple-groups → worst-case-SU(2) reduction, formalized.**
Math elementary (textbook SU(N) Casimir i(N−i)≥N−1); the *formalized uniform reduction* via η-monotonicity
is not found published. **CAVEAT (from research):** the worst-case *direction* is physically contestable —
larger groups tend to be *easier* at fixed coupling (SZZ get N-independent thresholds directly). Only
worth writing IF the η-domination monotonicity is genuinely proven (it currently rests on `EtaGapMonotone`);
flag the direction concern. Best as a section of P3 or a short note, not a standalone math claim.

**P5 — constructive-formalization techniques note.**
The cubing trick + located compact-operator spectral gap as reusable constructive-formalization methods.
Math known (Brattka); value is purely methodological. Workshop/short-paper at most; better folded into P1.

### Not paper-worthy (honest)
- Log-concavity falsity witness — known phenomenon (Okounkov/CDW); at most a remark in P3, with corrected framing.
- Δ_N=S_N²·P_N as "new math" — it is Stieltjes–Wigert/q-Hermite Hankel structure; only its *formalization* counts (inside P2).
- Heat-kernel character moments, basic Q' arithmetic, categorical/sheaf layer — infrastructure/expository.

## Bottom line

Three solid formalization papers (P1–P3, or one combined system paper), one conditional note (P4, with a
real physics caveat), one methods note (P5). **No new-mathematics papers** stand up to the literature —
the value "so far" is the constructive, axiom-clean, Mathlib-free *formalization*, which is genuinely
first-of-its-kind in Lean and a legitimate publishable contribution. The open continuum mathematics
(a→0, O(4)) remains a target, not a written result — "open" ≠ "unreachable," but it is not yet ours.
