# SL.1 Fiducial Extraction — Provenance Upgrade Draft (2026-07-24)

> Drop-in replacement paragraphs for `notes/fiducials_notes.md`, written in
> that note's style (section numbering, **Status** fields, per-fiducial
> citations).  Sources: (i) exact integer enumeration in
> `sl1/plaquette_connectivity.py` (pinned by
> `sl1/test_plaquette_connectivity.py`, 15 tests passing); (ii) direct
> reads of the local PDF-text corpus
> `_generated/pdf_text/` on 2026-07-24; (iii) bibliographic
> confirmation via Springer DOI pages.
>
> **Corpus file-identity correction (apply to the audit header).**  The
> PDF filenames are swapped relative to their contents:
> `docs/pdf_references/Balaban 116.pdf` actually contains **CMP 109
> (1987) 249–301** (RG I, small-field effective actions, d = 4), and
> `docs/pdf_references/Renormalization Group Approach to Lattice Gauge
> Field Theories.pdf` actually contains **CMP 116 (1988) 1–22** (RG II,
> cluster expansions).  `Balaban 102.pdf` is CMP 102 (1985) 255–275 as
> labeled.  **CMP 119 (1988) 243–285 is not in the corpus.**  Any
> per-fiducial citation of "[Balaban1988RG-II] (CMP 116)" that was read
> from the file named `Balaban 116` was in fact read from CMP 109; the
> 2026-05-25 audit's content attributions (0.27/1.18 → CMP 109;
> 1.32/1.36 → CMP 116) are nevertheless correct — the audit evidently
> keyed on content, not filenames.

---

## §1. `BAŁABAN_SPECTRAL_GAP_COEFF` — upgraded provenance paragraph

**Status: DERIVED (value 3/4, project-internal Casimir identification,
2026-05-26) + SHAPE-LOCATED (2026-07-24): the historical "1/2" is now
traced to a specific display in the primary source, and confirmed to be
a bookkeeping split, not an extracted coefficient.**

**SL.1 direct-text extraction (2026-07-24), CMP 109 p. 258, eq. (0.27).**
The display in which the factor 1/2 literally appears is (OCR-faithful
quote from `_generated/pdf_text/Balaban 116.txt`, page 10 of the PDF =
p. 258 of CMP 109):

> "If its localization domain X is large, for example it is not
> contained in any cube □ ∈ π_k, then the inequality (0.25) ensures that
> |E^(j)(X, U_k)| ≤ E_0 exp(−κ(L^j η)^…) exp(−(1/2)κ d_j(X)),  (0.27)
> and the first exponential can be bounded by an arbitrary positive
> power of L^j η, e.g. by (5!/κ^5)(L^j η)^5.  This power is enough to
> control the sums in (0.23), (0.24)."

The 1/2 in (0.27) is therefore a **decay-rate split**: half of the
inductive rate κ is spent extracting the small prefactor
exp(−κ(L^jη)^…), the other half retained as polymer-size decay.  It is
a proof device, valid for ANY κ satisfying the inductive assumptions —
not a determination of κ.  The value of κ itself is existence-only:

> **Theorem 3** (CMP 109, p. 264, verbatim): "There exist positive
> constants κ_0, M(κ), γ, ε_0, ε_1, α_0, α_1 such, that if κ ≤ κ_0,
> M ≥ M(κ), 0 < g_k ≤ γ for k = 0, 1, …, K, then the sequence of
> actions A_k, defined inductively by the small field renormalization
> transformations (0.17)–(0.20), satisfy all the inductive assumptions
> described between (1.1)–(1.22)."

and the SU(2) specialization defers even its own proof:

> **Theorem 2** (CMP 109, p. 259): "Let d = 4, G = SU(2), and let γ be
> a sufficiently small positive constant, then for a sufficiently small
> positive g there exists a bare coupling constant g_0 = g_0(ε, γ) such
> that the sequence of the effective coupling constants g_k is
> contained in the interval ]0, γ], and g_K = g. […] A proof of this
> theorem, based on perturbative calculations, will be given in a
> separate paper."

**Upgraded verdict.**  The 2026-05-25 audit conclusion ("existence-only,
no numerical κ") is CONFIRMED at quote level, and sharpened: the
project's historical c_λ = 1/2 shape now has a located ancestor — the
(0.27) rate-split — which makes explicit that 1/2 was never a property
of the gauge group or the Laplacian, only of Bałaban's bookkeeping.
This retroactively strengthens the 2026-05-26 decision to re-derive the
value internally as the SU(2) Casimir gap C_2(1/2) = 3/4: the primary
sources supply no number that could contradict (or support) any
specific rational.  Nothing in CMP 109/116/102 pins c_λ.

**Bookkeeping note.**  The Summary table and §1.1 of this file still
show 1/2 in places (pre-2026-05-26 text); they should be updated to the
current 3/4 wire-in when this paragraph is merged.

---

## §3. `MU_PLAQUETTE_4D = 16` and the Seiler "5d − 4" formula — RESOLVED (negative) by in-substrate derivation

**Status: the 5d − 4 formula is now DERIVED-AGAINST (2026-07-24): exact
enumeration shows it is NOT the count of any natural plaquette-adjacency
notion on Z^d.  The code-consumed notion is DERIVED: max-degree
Δ(d) = 8d − 12 (= 20 at d = 4), with rigorous BF constant e·Δ = 20e.
`MU_PLAQUETTE_4D = 16` is downgraded from "widely cited but not
verified" to "UNSUPPORTED for the code-consumed counting statement".**

### §3.3. Exact enumeration of all adjacency notions (SL.1, 2026-07-24)

`sl1/plaquette_connectivity.py` enumerates, in exact integer
arithmetic with a provable bounding-box exhaustiveness certificate
(base coordinates of any vertex-sharing plaquette lie in {−1, 0, 1};
the scan runs over [−2, 2]^d and asserts no qualifier touches the
boundary), every plaquette of every orientation adjacent to a fixed
unit xy-plaquette P₀ at the origin:

| notion                              | d=2 | d=3 | d=4 | d=5 | exact formula |
| ---                                 | --- | --- | --- | --- | ---           |
| share ≥ 1 edge                      | 4   | 12  | 20  | 28  | 8d − 12       |
| … coplanar                          | 4   | 4   | 4   | 4   | 4             |
| … non-coplanar                      | 0   | 8   | 16  | 24  | 8(d − 2)      |
| share ≥ 1 vertex                    | 8   | 32  | 72  | 128 | 8(d − 1)²     |
| … vertex-only (no edge)             | 4   | 20  | 52  | 100 | 8d² − 24d + 20 |
| ≥ 2 shared vertices without an edge | 0   | 0   | 0   | 0   | 0             |
| plaquettes containing a fixed bond  | 2   | 4   | 6   | 8   | 2(d − 1) ✓ BFS (4.24) |
| plaquettes containing a fixed vertex| 4   | 12  | 24  | 40  | 2d(d − 1)     |
| **formula 5d − 4 (Seiler-cited)**   | 6   | 11  | 16  | 21  | —             |

Formula-in-d proofs (three-point exact polynomial fits, verified at a
fourth d where the count is defined): an edge in direction μ lies in
2(d−1) plaquettes (one per perpendicular direction and side; BFS 1978
eq. (4.24), already confirmed in §3.1), so each of P₀'s 4 edges
contributes 2(d−1) − 1 = 2d − 3 other plaquettes, all distinct across
edges: 4(2d − 3) = 8d − 12.  Of these, exactly one per edge is coplanar
(the reflected square), giving 4 and 8d − 16 = 8(d − 2) for the split.
For vertex-sharing: 2d(d−1) plaquettes contain a given vertex (choose
the plane, C(d,2) ways, and the quadrant, 4 ways); inclusion–exclusion
over P₀'s 4 vertices (no plaquette shares ≥ 2 vertices with P₀ without
sharing an edge — enumerated 0 in all d) gives 8(d−1)².

**Conclusion 1 — the 5d − 4 formula matches NO adjacency notion at any
d.**  The single numerical agreement is at d = 4, where 5d − 4 = 16
coincides with the non-coplanar edge-neighbor count 8(d − 2) — and only
there (d = 3: 8 vs 11; d = 5: 24 vs 21).  A coincidence, not a formula.

### §3.4. The code-consumed counting statement, tested directly

What `computations/large_field_kp.py` actually consumes (via
K_lf = q/(1−q), q = μ_plaq·Z_t) is

    N_n(P₀) := #{edge-connected plaquette polymers X, |X| = n, P₀ ∈ X}
             ≤ μ_plaq^n.

Exact enumeration of N_n (same module, duplicate-free connected-subgraph
enumeration):

| d = 4 | N_n     | N_n / N_{n−1} | 16^n      | N_n ≤ 16^n |
| ---   | ---     | ---           | ---       | ---        |
| n = 1 | 1       | —             | 16        | OK         |
| n = 2 | 20      | 20.0          | 256       | OK         |
| n = 3 | 458     | 22.9          | 4096      | OK         |
| n = 4 | 11 132  | 24.3          | 65 536    | OK         |
| n = 5 | 280 175 | 25.2          | 1 048 576 | OK         |

(d = 3: N_n = 1, 12, 158, 2148, 29685; ratios 12.0 → 13.8.)

**Conclusion 2 — 16 holds for n ≤ 5 but is not asymptotically
defensible.**  The one-step growth ratios exceed 16 from n = 2 onward
and increase monotonically (20.0, 22.9, 24.3, 25.2 → the animal growth
constant λ from below).  Unless growth saturates below 16 — implausible
given the monotone ratios and the degree-20 graph — N_n ≤ 16^n fails at
some finite n (naive extrapolation at ratio ≈ 25.5: first violation
near n ≈ 8).  This is evidence, not a theorem: the enumerated n ≤ 5
give a rigorous λ lower bound of only (N_5/5)^{1/5} ≈ 8.9.  What IS a
theorem is: (i) 5d − 4 counts none of the natural adjacency notions,
and (ii) the code-consumed graph has max-degree exactly 20, so the
rigorous derivable constant is `MU_PLAQUETTE_BF_CONSERVATIVE_4D = 20e`
(§3.2), unchanged.

**Disposition.**  If Seiler's LNP 159 (still not in the corpus; not
openly accessible) proves a 5d − 4 bound, it must concern a restricted
polymer class or a different counting weight, not the unrestricted N_n
above.  Recommended: flip the code default to `20e` (or keep 16 only
with an explicit "restricted-class, unverified" caveat).  Downstream
touch-points of `MU_PLAQUETTE_4D` (grep 2026-07-24):
`compute_large_field_kp` / `eps_lf` / `first_few_rg_steps` /
`convergence_threshold_g_lf` defaults in
`computations/large_field_kp.py`; the `mu_plaq` parameter of
`sigma_hat_trajectory`; `fiducial_sensitivity.sweep_mu_plaq` and
`max_g0_closure`.  Cost of the flip (already measured in §3.2):
canonical g_max^lf 0.4245 → 0.3733 (≈ −12%); pilot closure at the
canonical g₀ = 0.30 wire-in unchanged (sf window ≈ 0.40/0.49 binding).

**Citations.**
- Enumeration witness: `sl1/plaquette_connectivity.py` (+
  `sl1/test_plaquette_connectivity.py`, 15 pinned tests).
- Per-bond count: [BrydgesFroehlichSeiler1978IHES] eq. (4.24)
  (unchanged, ✓).
- 5d − 4 attribution: [Seiler1982] LNP 159 — cited-but-unverified,
  now additionally shown incompatible with every natural adjacency
  count; a 2026-07-24 web pass again surfaced no verbatim statement.

---

## §5. `BALABAN_POLYMER_RESIDUAL = 2.0` — extraction reconnaissance (precise null)

**Status: DERIVED (project-internal triangle-inequality channel count,
unchanged from 2026-05-25).  The literature shape-source citation
[Balaban1988convergent] (CMP 119) is hereby demoted to "motivating,
not supplying": SL.1 established that the constant cannot currently be
extracted from any locally held or openly accessible primary source.**

**SL.1 reconnaissance record (2026-07-24).**

1. **CMP 119 (1988) 243–285 is absent from the local corpus** —
   `docs/pdf_references/` contains CMP 102, CMP 109, CMP 116 (see the
   file-identity correction above), BFS-IHES, the Clay statement, and
   Jørgensen; no CMP 119.  Bibliographic identity confirmed externally:
   T. Bałaban, "Convergent renormalization expansions for lattice gauge
   theories", Commun. Math. Phys. 119 (1988) 243–285, DOI
   10.1007/BF01217741.  Full text is subscription-gated at Springer;
   the Project Euclid open archive is bot-walled (Incapsula) from this
   container, so no legitimate open extraction path was available.

2. **CMP 116 (present) supplies no numerical residual factor.**  Its
   cluster-expansion bounds carry named-but-unpinned absolute
   constants and inequality-linked rates, e.g. (quotes from
   `_generated/pdf_text/Renormalization Group Approach to Lattice
   Gauge Field Theories.txt`, pp. 9–10 of CMP 116):

   > "exp(−(1 − δ)κ d_k(Y) − δκ d_j(X)),  (1.32)  if
   > ½(κ₁ − 1) ≥ (1 − δ)κ, 0 < δ < 1."

   > "**Lemma 1.** […] There exist absolute constants C₁, C₂, q, for
   > which |V′_k(Y, U, J, B)| ≤ B₀ ε₁ C₁ M^q exp(C₂κ₁)
   > exp(−(1 − 2δ)κ d_k(Y)).  (1.36)"

   plus the further ordering assumption "(1/8)κ₁ ≥ (1 − 2δ)κ" (p. 9;
   OCR partially garbled, consistent with the 2026-05-25 audit's
   reading of the same constraint).  Everything is existence-only; no
   factor-2 (or any numeric) per-polymer residual appears.

3. **Consequence.**  The constant 2.0 continues to rest entirely on the
   project-internal derivation of §5 (triangle inequality on the
   per-polymer activity change under T_b; channel multiplicity 2;
   optimal worst-case absent a sign-preservation lemma).  What
   extraction WOULD require: CMP 119 §§ on the R-operation /
   large-field–small-field recombination (pages 243–285), plus its
   companions "Large field renormalization I/II" (CMP 122 (1989)
   175–202 and 355–392), under matched conventions — with the realistic
   expectation, given the uniform pattern of Theorems 1–3 (CMP 109) and
   Lemma 1 (CMP 116), that those papers also supply existence-constants
   only, in which case the internal derivation remains the strongest
   available provenance.

**Citations (updated).**
- TeX: `\cite{Balaban1988convergent}` — mark as *shape/motivation only*;
  the constant's provenance citation is `notes/sigma-hat-derivation.md`
  §2.3-derivation.
- Python: `computations.sigma_hat_trajectory.BALABAN_POLYMER_RESIDUAL`
  (unchanged).

---

## Summary-table patch

| Constant | Value | Status (patched) |
| --- | --- | --- |
| `BAŁABAN_SPECTRAL_GAP_COEFF` | 3/4 | DERIVED (Casimir, 2026-05-26); historical 1/2 SHAPE-LOCATED to CMP 109 eq. (0.27) rate-split (2026-07-24); primary sources numerical-value-free (quote-confirmed) |
| `MU_PLAQUETTE_4D` | 16 | **UNSUPPORTED for the code-consumed count** (2026-07-24): 5d−4 matches no adjacency notion; d = 4 agreement with 8(d−2) = 16 is coincidental; N_n ≤ 16^n verified only for n ≤ 5 with growth ratios already > 16; rigorous default remains `20e` |
| `BALABAN_POLYMER_RESIDUAL` | 2.0 | DERIVED (internal, unchanged); CMP 119 extraction: precise null (paper absent locally, not openly accessible; CMP 116 existence-only, quote-confirmed) |
