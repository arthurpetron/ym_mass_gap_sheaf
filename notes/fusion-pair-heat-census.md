# Physical heat census for intersecting surface pairs

Date: 2026-07-24

## Question

The earlier four-cube survey proved that the unweighted complete fusion sum
is positive on all 100 intersecting binary-surface pair orbits. That did not
yet prove positivity of the physical grouped activity: each fixed-face
channel receives a label-dependent heat coefficient, so channels at
different heat exponents are reweighted differently.

For a pair \((S,T)\), the physical polynomial tested here is

\[
 A_{S,T}(w)=
 \sum_{\{j_f\}}
 A(\{j_f\})
 \prod_f (j_f+1)w^{j_f(j_f+2)},
\]

where the sum contains every channel in
\(\chi_1^2=\chi_0+\chi_2\) on overlap faces.

## Exact result

The 7,997 raw intersecting pairs form 100 hyperoctahedral orbits. Exact
rational evaluation gives:

- 100 of 100 heat polynomials coefficientwise positive;
- 77 distinct heat polynomials;
- minimum positive coefficient \(1/6561\);
- heat-term counts
  \(2:40,\ 3:19,\ 4:23,\ 5:5,\ 6:9,\ 7:2,\ 9:2\).

Six orbits contain negative fixed-face amplitudes. Their
negative/positive-channel profiles are

\[
 (4,12):3,\qquad (16,48):2,\qquad (64,192):1.
\]

Nevertheless every coefficient at every heat exponent is strictly positive.
Thus these cases do not merely become positive after evaluating at a
particular coupling: their complete physical activities are positive for all
\(w>0\) by coefficient inspection.

The pinned signed-channel family again gives

\[
 w^{48}\left(1+12w^8+6w^{16}+12w^{24}+w^{32}\right).
\]

## Implication

This closes the bounded BF1 falsification campaign for the hardest
two-strand sector on the unit four-cube, including every symmetry orbit with
genuine intersection. It is stronger than the unweighted 100-orbit result
and is stable under the finite \(SU(2)_k\) comparison for every \(k\ge2\),
because each face contains at most two fundamental strands.

## Diagonal duplicate surfaces

The eight nonempty single-surface orbits account for all 127 diagonal pairs
\((S,S)\). These do not require a \(2^F\) channel enumeration. On each
edge-connected component \(S_i\), a label-two subset is admissible only when
it is empty or the whole component. The uniform label-two amplitude is the
two-dimensional Yang--Mills value \(3^{\chi_i-F_i}\); its face-dimension
weight is \(3^{F_i}\). Therefore

\[
 A_{S,S}(w)=\prod_i\left(1+3^{\chi_i}w^{8F_i}\right).
\]

All coefficients are strictly positive. Exact examples include:

\[
\begin{aligned}
\text{six-face sphere:}&\quad 1+9w^{48},\\
\text{two six-face spheres:}&\quad
1+18w^{48}+81w^{96},\\
\text{sixteen-face Clifford torus:}&\quad 1+w^{128}.
\end{aligned}
\]

Thus all 100 intersecting pair orbits and all eight diagonal surface orbits
are now physically heat-positive. The nine disjoint distinct-pair orbits
have no overlap channel and reduce to independent positive surfaces.

This does not prove the general carrier positive. The next minimal sectors are:

1. three closed fundamental strands, where fusion-path multiplicities first
   occur;
2. higher surface labels;
3. corrected slabs larger than one embedded four-cube.

Any of these may produce a negative complete heat polynomial. The
Birkhoff cone cannot be declared before those tests or a structural
positivity theorem supersede them.
