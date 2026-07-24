# Local-face Birkhoff census

Date: 2026-07-24

## Exact reduction

For a four-spin fine packet \(p=(a,b,c,d)\) and retained coarse spin \(s\),
the corrected-slab face kernel is

\[
K_w(p,s)=\operatorname{coeffW}(w,s)
 \sum_{x,y}N_{ab}^{x}N_{cd}^{y}N_{xy}^{s}.
\]

The heat-kernel coefficient depends only on \(s\). It is therefore a
projective column gauge: it cancels from every cross-ratio. For this literal
one-face kernel, any finite Hilbert diameter must come from fusion geometry,
not from heat decay.

## One-step support obstruction

At cutoff one the exact multiplicity rows, ordered lexicographically by the
binary packet, are

```text
(1,0,0,0,0)  (0,1,0,0,0)  (0,1,0,0,0)  (1,0,1,0,0)
(0,1,0,0,0)  (1,0,1,0,0)  (1,0,1,0,0)  (0,2,0,1,0)
(0,1,0,0,0)  (1,0,1,0,0)  (1,0,1,0,0)  (0,2,0,1,0)
(1,0,1,0,0)  (0,2,0,1,0)  (0,2,0,1,0)  (2,0,3,0,1)
```

The nonzero bipartite support has two connected components, the even columns
\(\{0,2,4\}\) and odd columns \(\{1,3\}\). Both contain zero holes. Hence the
one-step local matrix is not strictly positive on either full parity sector,
and its Hilbert image diameter there is infinite.

This is a precise correction to the proposed route: “unbranched cone” cannot
mean the whole center-parity component of the raw one-face operator.

## Minimal reflected primitive

Reflection positivity suggests the square Gram primitive \(G=M^T M\). It is
strictly positive on each parity block. At cutoff one its exact maximal
cross-ratios are

| parity block | exact maximum |
|---|---:|
| even \(\{0,2,4\}\) | \(11/4\) |
| odd \(\{1,3\}\) | \(5/4\) |

Using the repository's conservative rational spread \(R=\theta\), one common
fixed-cutoff certificate is

\[
R=\frac{11}{4},\qquad q=\frac{R-1}{R+1}=\frac{7}{15}.
\]

The primitive repairs positivity but does not yet repair uniformity. The
exact worst-block rates through cutoff four are

| cutoff \(N\) | exact \(q_N\) |
|---:|---:|
| 1 | \(7/15\) |
| 2 | \(19/25\) |
| 3 | \(1333/1495\) |
| 4 | \(2603/2747\) |

They increase rapidly toward one in this census. This finite table is not a
proof of a limiting no-go theorem, but it rules out treating the unweighted
Gram primitive as the missing cutoff-uniform certificate.

## Consequence for RG-I7

The Birkhoff–Hopf route remains structurally useful, but the physical theorem
must add one ingredient not present in the literal face matrix:

1. a smaller invariant cone with quantitative interior bounds;
2. a genuinely nonseparable heat-weighted intermediate-channel map;
3. a coarse-grained iterate whose fusion diameter is proved uniform; or
4. a scale-dependent contraction \(q_k=1-a_k m+o(a_k)\) followed by a
   composed/rescaled estimate.

The fourth alternative is consistent with dimensional transmutation and with
the existing exact result that a per-lattice-step spectral ratio approaches
one. Thus “cutoff-independent” should not be conflated with “bounded away
from one independently of lattice spacing.”

The executable certificate and regression pins are in
`computations/local_face_projective_census.py` and
`tests/test_local_face_projective_census.py`.
