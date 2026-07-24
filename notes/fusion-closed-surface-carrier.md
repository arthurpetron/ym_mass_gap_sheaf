# Fusion-closed surface carrier

Date: 2026-07-24

## Purpose

Fixed-face dual coefficients are not a positive carrier: the corrected slab
contains an exact coefficient \(-1/196608\). The first candidate physical
carrier instead records a finite multiset of closed labelled surface strands.
Every overlap face is expanded through the complete SU(2) character identity,
including the multiplicity of every fusion path.

This definition makes fusion closure algebraic. It does **not** assume the
dual-positivity conjecture.

## Exact carrier

For a family of strands \(S_\alpha\) with doubled labels \(j_\alpha\), the
unfused observable is

\[
  \prod_\alpha\prod_{f\in S_\alpha}\chi_{j_\alpha}(U_f).
\]

At each face, its character product has the unique expansion

\[
  \prod_{\alpha:f\in S_\alpha}\chi_{j_\alpha}
  =\sum_{j_f}m_f(j_f)\chi_{j_f},
\]

where \(m_f(j_f)\) is a nonnegative integer fusion-path multiplicity. Taking
the product over faces gives a finite ledger of fixed-face assignments with
multiplicity \(\prod_f m_f(j_f)\).

`computations/fusion_closed_surface_carrier.py` implements:

- exact mod-two closure of every surface strand;
- canonical union of carrier elements;
- arbitrary iterated SU(2) fusion with path multiplicities;
- the complete fixed-face ledger;
- independent direct and channel-resummed Haar evaluation;
- the physical heat-weighted activity polynomial

\[
  A_{\mathcal F}(w)=
  \sum_{\{j_f\}}m(\{j_f\})\,A(\{j_f\})
  \prod_f (j_f+1)w^{j_f(j_f+2)}.
\]

## First physical certificate

The two closed fundamental surfaces containing the pinned negative channel
produce 16 fixed-face channels. Four channel amplitudes are negative, and the
unweighted direct/resummed Haar value is

\[
  \frac{31}{331776}>0.
\]

More importantly, inserting the actual label-dependent heat weights gives
the exact polynomial

\[
  A_{\mathcal F}(w)
  =w^{48}\left(1+12w^8+6w^{16}+12w^{24}+w^{32}\right).
\]

It is coefficientwise positive on \(0<w<1\). Thus the first complete carrier
element remains positive after the physical heat weights are restored; its
positivity was not an artifact of the unweighted sum.

## What this does and does not prove

This is a candidate cone generator and a semantic test bed. It does not yet
prove:

1. positivity for every closed surface/fusion family;
2. that these generators give a non-overcounting decomposition of the full
   lattice partition function;
3. closure under the actual coarse-graining map;
4. finite projective image diameter.

Those are now separate falsifiable gates. A negative heat polynomial for any
closed family refutes this candidate cone as stated. Failure of unique or
positive reconstruction would require enriching the carrier with embedded
fusion-tree/intertwiner data rather than reverting to signed fixed-face
labels.
