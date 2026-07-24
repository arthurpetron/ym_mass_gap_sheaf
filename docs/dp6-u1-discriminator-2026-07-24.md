# DP.6-U1 — The U(1) discriminator: abelian comparison for the dual-positivity program

**Status:** computation complete and checked (see `u1_dual_check.py`, all assertions pass).
**Scope:** implements the standing audit rule "every gap-critical positivity/contraction step
must name where it uses non-abelian-ness" for the DP.6 signed-sector-survival milestone.
**One-sentence verdict:** U(1) dual amplitudes on the 4-cube boundary are identically
{0, 1} — dual positivity is *free* abelianly while 4D U(1) is *gapless* at weak coupling
(Guth 1980), so dual-cone positivity is only cone admission and the gap must be produced
by a step that fails for U(1): the candidate is the contraction rate of the blocked
kernel, and the decisive follow-up test is the U(1) run of the slab blocking kernel with
the prediction of corridor NON-narrowing.

---

## 1. The audit rule and why it exists

The Migdal–Kadanoff approximate recursion (Migdal 1975; Kadanoff 1976) predicts
confinement — an area law at all couplings — for 4D lattice gauge theory with *any*
compact gauge group, **including U(1)**. That prediction is false: Guth proved (Phys.
Rev. D 21, 2291 (1980)) that 4D compact U(1) lattice gauge theory has a deconfined
phase at weak coupling, and Fröhlich–Spencer (Commun. Math. Phys. 83, 411 (1982))
established that this phase is a massless Coulomb phase — a free photon, power-law
correlations, **no mass gap**. MK is therefore the canonical *false positive*: a
"gap/confinement mechanism" that is blind to the abelian/non-abelian distinction proves
too much and is thereby refuted.

Hence the standing rule (work_plan §15c, cross-cutting policies): every gap-critical
positivity or contraction step in the DP chain must *name* where it uses non-abelian
structure. Any step that would apply verbatim to 4D U(1) cannot be the step that
produces the gap. This memo runs that audit against the new DP finding — SU(2) dual
(spin-network) amplitudes on the 4-cube boundary are **not** all positive, with
negatives switching on exactly at plaquette spin n = 3 (j = 3/2, the second
quaternionic irrep), minimal exemplar Z = −1/3 981 312 — and against the DP.6 plan to
control the negative sector by heat-kernel weighting d_n s^{n(n+2)} (positive sector
entering at s³, negative at s¹⁵).

## 2. The computation and its result: abelian dual positivity is free — and worthless as a gap mechanism

`u1_dual_check.py` builds the boundary complex of the 4-cube — 8 cubical 3-cells,
24 square faces, 32 edges, 16 vertices; every edge shared by exactly **3** faces — with
explicit integer incidence signs, and verifies the orientation bookkeeping by
∂₁∘∂₂ = 0 and ∂₂∘∂₃ = 0 (the latter checked against all 8 three-cells). Exact results:

- **Admissible charge lattice.** In the U(1) dual (Fourier) representation each face
  carries an integer charge m_f; Haar integration over each edge holonomy forces the
  oriented sum of the 3 incident charges to vanish at every edge, i.e. m ∈ ker ℤ(∂₂).
  Computed exactly (sympy nullspace over ℚ cleared to primitive integer vectors):
  **rank 7**, and the Smith normal form of the basis matrix has invariant factors
  (1,1,1,1,1,1,1) — the basis is saturated, so it is the *full* integer kernel, not a
  finite-index sublattice. (Cross-check: rank ∂₃ = 7 = 8 cubes − 1 and H₂(S³) = 0, so
  every admissible assignment is a ℤ-combination of elementary-cube surface charges.)
- **Amplitudes are {0, 1}, structurally.** The dual amplitude is a product of one
  Kronecker delta per edge: 1 on the kernel, 0 off it. Verified on all 2187 kernel
  vectors with coefficients in {−1,0,1}⁷ (amplitude ≡ 1, charges up to |m_f| = 3
  reached) and on 500 random off-kernel probes with |m_f| ≤ 2 (amplitude ≡ 0). There
  is **no recoupling object in the abelian dual** — no 6j, no signed coefficient exists
  to evaluate — so this holds at *any* charge, not merely the enumerated window.
- **Heat-kernel weighted sum.** With U(1) weights d_m s^{Casimir} = 1·s^{m²} the global
  dual sum over the window |c_i| ≤ 2 in the kernel basis (78 125 admissible
  assignments) at s = 1/2 is the exact positive rational
  S = 21671371554592318675104340270483819859454766277562067986152735871696651287531382495598608385 / 16296287810675888690147565507275025288411747149327490005089123594835050398106693649467179008 ≈ 1.329834856033602,
  manifestly a sum of positive terms s^(Σ m_f²). *Truncation stated honestly:* this is
  the exact value of the windowed sum only; the full rank-7 lattice sum adds further
  strictly positive terms of the same form, so positivity and monotone convergence for
  0 < s < 1 are structural, independent of the window. The cheapest non-trivial
  admissible configuration is an elementary cube surface (6 faces of |m| = 1, weight
  s⁶, multiplicity 16 = 8 cubes × 2 orientations).

**The precise abelian/non-abelian dichotomy.** For U(1) every irrep is 1-dimensional
and χ_m·χ_n = χ_{m+n}: iterated Clebsch–Gordan fusion of the charges meeting at an edge
has exactly *one* path, intertwiner spaces are at most 1-dimensional, and the change of
basis between any two fusion trees is the identity — the 6j symbol, which *is* the
overlap of two inequivalent fusion trees, degenerates to a Kronecker delta. No two
paths, no interference, no sign. For SU(2) a multiple fusion has several inequivalent
trees; the 6j is a genuine orthogonal change of basis with entries of both signs, and
dual amplitudes are interference sums over fusion trees. The sign problem that switches
on at j = 3/2 is therefore an intrinsically non-abelian phenomenon — multiplicity of
paths in iterated fusion — absent for **every** abelian group.

**Conclusion of the comparison.** U(1) enjoys *perfect* dual positivity — the strongest
conceivable form, amplitudes literally in {0, 1} — and yet 4D U(1) has **no gap** at
weak coupling. Therefore:

> Positivity of the dual cone is **not** the gap mechanism and must never be cited as
> such in the DP chain. It is only *cone admission* — the precondition for running
> Birkhoff cone-contraction machinery. (A second, independent reason: positivity
> statements on a fixed finite complex are volume-agnostic scaffolding; the gap is a
> thermodynamic-limit/continuum statement, which no finite-complex positivity can
> decide by itself.)

## 3. Where non-abelian-ness must therefore enter for SU(2)

**(a) The contraction rate / corridor narrowing of the blocked kernel — the candidate
mechanism.** DP.2 (P19) measured the two-sided slab blocking flow running *faster*
than the exact 2D rule: s′ = 0.0341 vs s⁴ = 0.0625 at s = ½, with the flowed corridor
narrowing (1.82 vs wheel 2.23; 0.79 at s = ¾). For U(1) the 2D heat kernel is exactly
form-stable under blocking — character coefficients multiply, s^{m²} → (s^{m²})⁴ =
(s⁴)^{m²}, so the 2D rule is s′ = s⁴ *exactly*, and univalence (d_m = 1 for every
charge) removes the d³ denominator that generates the SU(2) corridor in the first
place. **Testable prediction (the decisive discriminator computation):** run the DP.2
slab blocking kernel with U(1) weights; the discriminator predicts the 4D flow *tracks
the 2D rule with corridor NON-narrowing* — no acceleration beyond s⁴, no envelope
contraction. If instead the U(1) run showed narrowing comparable to SU(2)'s, the
narrowing mechanism would be group-blind and the audit would flag the contraction step
as proving too much (an MK-type false positive inside our own machinery). This is the
step where the gap, if the program succeeds, actually lives — and it is exactly the
step the abelian comparison can falsify or certify.

**(b) The signed j ≥ 3/2 sector itself.** The negative amplitudes are fusion-tree
interference (§2); the object DP.6 must control *does not exist* over U(1). So the
signed-survival argument is automatically non-abelian in its subject matter — but see
§4 for the care needed: controlling a non-abelian liability is not the same as using
non-abelian-ness to produce a gap.

**(c) Anti-screening / self-charge — the physical face of the same fact.** The SU(2)
gluon carries the charge it mediates; one loop gives β(g) = −(22/3)·g³/16π² < 0
(asymptotic freedom, anti-screening), while the photon is neutral and abelian matter
only screens (β ≥ 0). Self-charge of the gauge boson, non-trivial fusion multiplicity,
and signed 6j interference are three faces of one structure: the adjoint representation
is non-trivial exactly when the group is non-abelian. Any continuum-limit step of the
program that invokes running toward strong coupling under blocking is implicitly
invoking (c) and must cite it as such.

## 4. The tag — for the DP.6 deliverable

Reviewers should check the signed-survival argument against this table: **no
group-blind step may be asked to produce the gap.**

Group-blind steps (valid for U(1), hence *cannot* be gap-producing; they are
scaffolding and must be labelled as such in the DP.6 write-up):

1. The duality transform itself (Peter–Weyl / Fourier expansion, Haar edge integrals,
   delta-function flux constraints).
2. Reflection positivity and well-definedness of the heat-kernel action (standing
   policy: heat-kernel action stands on its own axioms).
3. Positivity of the heat-kernel character weights d_n s^{n(n+2)} > 0 term-by-term, and
   convergence/domination of character tails by Casimir growth.
4. The cone formalism: definition of the dual cone, Birkhoff–Hopf projective metric,
   the abstract contraction-implies-spectral-gap implication.
5. Cluster/polymer combinatorics and truncation bookkeeping (ε_slab(M) etc.).

Non-abelian-tagged steps (fail or trivialize for U(1); only these may carry gap
weight):

6. **Existence and structure of the signed sector** — 6j interference, onset at the
   second quaternionic irrep n = 3; trivializes abelianly (empty sector). *Tag:
   liability, not mechanism.*
7. **DP.6 signed-sector survival** (s³ vs s¹⁵ weighted-channel domination on (0,1)):
   the inputs (6j bounds, SU(2) Casimirs, quaternionic structure) are non-abelian, but
   its *conclusion* — positivity of the weighted dual sums — is a property U(1)
   possesses trivially (§2). *Tag: restores cone admission for SU(2); explicitly NOT
   the gap mechanism; must not be cited as one.*
8. **Contraction rate / corridor narrowing of the blocked kernel** (s′ = 0.0341 < s⁴;
   envelope contraction): *conjecturally* non-abelian — this is the one gap-critical
   step whose non-abelian tag is currently an empirical SU(2) measurement plus the
   §3(a) prediction, not yet a theorem or a completed U(1) control run. *Tag: the
   candidate mechanism; tag verification = DP.6-U1 follow-up.*
9. **Anti-screening / self-charge** (sign of the one-loop beta function): physical
   justification for expecting (8); non-abelian by construction. *Tag: motivation and
   consistency check for the direction of the flow.*

Audit rule applied: if the eventual gap proof's load-bearing chain reads
"admission (7) → contraction (8) → gap (4)", then (7) must be presented as opening the
door, (8) as walking through it, and (4) as bookkeeping. Only (8) is allowed to be the
reason the walk terminates, and (8) owes the reader its named non-abelian ingredient —
at present: univalence failure d_n = n + 1 > 1 feeding the c′ = c⁴/d³ rule and the
transverse interference channels absent abelianly.

## 5. One honest open point

Dual positivity restored-by-weighting — DP.6's goal — is still only **cone admission**.
Even a complete DP.6 success (weighted channel sums positive on all of (0,1), s → 1⁻
endpoint controlled, certificates in Lean) leaves the gap-producing step untouched and
untagged. The decisive discriminator computation is the U(1) comparison of the
**contraction step** (§3(a)): run the existing slab blocking kernel with U(1) weights
(d_m = 1, Casimir m²) and test the corridor NON-narrowing prediction s′ = s⁴ with no
envelope contraction. Until that run is done, item (8)'s non-abelian tag rests on one
SU(2) measurement and a physical argument. **Queue as DP.6-U1 follow-up**, parallel-
safe and lock-free: it reuses `computations/slab_blocking_kernel.py` with the abelian
character table, and either outcome is banked — non-narrowing certifies the mechanism's
discriminating power; narrowing flags an MK-type false positive before it can
contaminate the gap chain.

---

### Appendix — reproduction

Script: `u1_dual_check.py` (same directory; Python 3, sympy for exact ℚ/ℤ linear
algebra, `fractions.Fraction` for the weighted sum; runtime ~3 s). Checks asserted at
runtime: ∂₁∘∂₂ = 0; ∂₂∘∂₃ = 0 against all 8 three-cells; edge trivalence with unit
incidence signs; kernel rank 7 with Smith invariant factors all 1 (full integer
kernel); amplitude ≡ 1 on 2187 enumerated kernel vectors and ≡ 0 on 500 off-kernel
probes; exact windowed heat-kernel sum at s = 1/2 as quoted in §2.
