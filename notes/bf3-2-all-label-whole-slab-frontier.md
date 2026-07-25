# BF3.2 — all-label whole-slab kernel frontier

Date: 2026-07-25

Status: **fixed-block all-label construction complete; full BF3.2 remains
open**.

## 1. Result

The exact BF3.1 Haar coefficient for every nine-word coarse Wilson insertion
now has a constructive all-label completion.  If \(0<s<1\) is the heat
coordinate and \(n\) is the doubled \(SU(2)\) label, then

\[
  (n+1)s^{n(n+2)}\lvert\chi_n(g)\rvert
  \le h_n(s):=(n+1)^2s^{n(n+2)}.
\]

The ratio after the first label omitted by cutoff \(N\) is

\[
  r_N(s)
  =
  \frac{(N+3)^2}{(N+2)^2}s^{2N+5}.
\]

It decreases thereafter.  Whenever \(r_N(s)<1\),

\[
  \sum_{n>N}h_n(s)
  \le
  T_N(s):=
  \frac{(N+2)^2s^{(N+1)(N+3)}}{1-r_N(s)}.
\]

For the corrected slab's 72 fine plaquettes, put

\[
  H_N(s)=\sum_{n=0}^{N}h_n(s)+T_N(s).
\]

The difference between the literal all-label Haar coefficient and the
finite \(72\)-label-cube sum is bounded by

\[
  D_{\mathrm{ext}}\,
  72H_N(s)^{71}T_N(s),
\]

where \(D_{\mathrm{ext}}\) is the product of the dimensions of the inserted
coarse Wilson representations.  Therefore the dimension-weighted
coefficient norm is uniform in every external label.

This is an actual Cauchy name, not a formal series label.  Its \(N\)-th
approximant enumerates the finite cube

\[
  \{0,\ldots,N\}^{72}
\]

and sends every term through the same exact Haar integrator used by BF3.1.
The literal evaluator is definition-level and exponential; BF3.1's affine
and incidence reductions remain the practical low-cutoff engine.

## 2. Normalized strong-coupling corridor

The same estimate controls the normalized Gibbs density where the elementary
character majorant supplies a positive pointwise floor.  If

\[
  E_N(s):=H_N(s)-1<1,
\]

then each plaquette heat kernel is at least \(1-E_N(s)\).  Consequently the
72-face partition function is at least

\[
  (1-E_N(s))^{72},
\]

and the normalized \(L^1\) difference is bounded by

\[
  \frac{2\cdot72H_N(s)^{71}T_N(s)}
       {(1-E_N(s))^{72}}.
\]

At \(s=\tfrac12\), the least cutoff certified by this elementary bound for
normalized error below \(10^{-2}\) is \(N=11\).  This is a bound on the
actual plaquette-coupled Haar density on the fixed corrected slab, not on
the older product-of-multiplicities surrogate.

The cutoff selection is constructive and coupling dependent.  In the raw
dimension-weighted coefficient norm, the least cutoffs for tolerance
\(10^{-2}\) increase strictly at the sample points
\(s=\tfrac12,\tfrac34,\tfrac9{10}\).  This directly implements the
coupling-dependence required by the BF3.3 near-continuum fence.

## 3. Why this does not close BF3.2

Three distinct norms must not be conflated.

1. The estimate above controls a dimension-weighted matrix coefficient, and
   in the positivity corridor the \(L^1\) difference of two fixed-block
   Gibbs densities.
2. BF2's carrier is the cone of positive trace-class kernels on the complete
   fusion/intertwiner boundary Hilbert space.
3. BF4 needs the Hilbert projective metric on a cone invariant under the
   normalized physical block map.

BF2 proves that exact Haar blocking is completely positive.  It does not
prove that the raw blocking map is trace preserving, identify the
coefficient majorant with trace norm on every coherent \(P/Q\) block, or
make complete positivity a Hilbert-metric contraction.  Those are additional
theorems.

The present product estimate also contains \(H_N^{F-1}\) and a factor \(F\)
for \(F\) plaquettes.  It is therefore a fixed-block estimate, not a
volume-uniform one.  This agrees with the axiom-free obstruction
`Z4FixedCutoffNaiveTailFence`: an independent first-omitted-label charge
summed over every plaquette is unbounded on cofinal boxes.  A valid
volume-uniform BF3.2 estimate must instead use a local conditional norm,
connected-cluster cancellation, or another localization mechanism.

Finally, representation truncation is not the RG remainder.  The actual
remainder compares the normalized fine Gibbs pushforward with the actual
coarse Gibbs law and retains

\[
  P\Phi Q,\qquad Q\Phi P,\qquad Q\Phi Q.
\]

`CompactDualPhysicalRemainderLocality` proves that every intertwined
fine/coarse cylinder mismatch lower-bounds its \(L^1\) norm.  Thus no global
refresh kernel can manufacture a zero remainder; the physical cylinder
mismatches still have to be bounded.

## 4. Gate ledger

| BF3.2 obligation | Result |
|---|---|
| all-label fusion/intertwiner field over every coarse word | coefficient-level exact Haar Cauchy name for all nine coarse Wilson labels |
| summable heat tail on one corrected slab | explicit super-geometric bound |
| external-label uniformity | complete after division by the product of representation dimensions |
| coupling-dependent cutoff schedule | constructive |
| normalized actual density tail | complete in the elementary strong-coupling corridor |
| identify the tail with the BF2 trace-class kernel norm | open |
| control all coherent \(P/Q\) blocks in that norm | open |
| volume-uniform vanishing modulus | open; naïve additive route is ruled out |
| bound the actual fine/coarse RG remainder | open |
| pass a ready physical kernel to BF4 | not yet admissible |

The next theorem is therefore:

> Define a localized BF2 kernel norm on the complete boundary
> fusion/intertwiner field, prove the exact Haar block is bounded in that
> norm, and bound every physical cylinder mismatch and coherent \(P/Q\)
> block by a connected tail with constants independent of the ambient
> volume.

Only after this theorem can the grouped physical map be tested against
BF4's nine-field handoff.

## 5. Reproduction

- `computations/all_label_whole_slab_tail.py`;
- `tests/test_all_label_whole_slab_tail.py`;
- `notes/bf2-1-general-reflection-positive-carrier.md`;
- `lean/YMGap/Continuum/Z4FixedCutoffNaiveTailFence.lean`;
- `lean/YMGap/Continuum/CompactDualPhysicalRemainderLocality.lean`.

The executable frontier is
`computations.all_label_whole_slab_tail.bf32_all_label_frontier()`.
