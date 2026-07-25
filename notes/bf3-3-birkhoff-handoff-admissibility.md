# BF3.3: Birkhoff handoff admissibility

Date: 2026-07-25

Status: **closed by the exact obstruction route**. This is a diagnostic
milestone, completed out of dependency order at the user's request. BF3.2
remains open and must be closed before the physical map can enter BF4.

## 1. Question adjudicated

BF3.1 produced an exact positive reflected density on the cutoff-one whole
slab. That does not yet identify a strict Birkhoff contraction. BF3.3 asks
whether any of the three shortest handoffs is valid:

1. use the 64-dimensional BF3.1 reflected density itself as the positive
   map;
2. use the local reflected fusion Gram as a cutoff-independent positive
   primitive;
3. truncate the all-label heat law and let the representation cutoff tend
   to infinity independently of the coupling.

All three proposals fail exactly. The failures determine the minimum data
that the BF3.2-to-BF4 handoff must carry.

This does **not** prove that a grouped physical block kernel cannot
contract. It proves that componentwise positivity, a local Gram primitive,
and a cutoff-only heat tail do not supply that theorem.

## 2. The whole-slab density has no global mixing

Evaluate the BF3.1 polynomial density at any rational heat coordinate
\(0<s<1\). Its support is independent of the chosen positive \(s\). The
exact \(64\times64\) matrix is the direct sum

\[
 K(s)=\bigoplus_{\gamma=1}^{32}v_\gamma(s)v_\gamma(s)^{\mathsf T}.
\]

The support audit gives:

| datum | exact value |
|---|---:|
| boundary dimension | 64 |
| support components | 32 |
| shape of every component | \(2\times2\) |
| rank of every component | 1 |
| rational projective rate inside each component | 0 |
| mixing between cut signatures | none |
| finite global projective diameter | no |

The componentwise rate zero is real but unusable as a global contraction.
For example, entries \(K_{00}\) and \(K_{22}\) are positive while
\(K_{02}=K_{20}=0\). Independent rescaling of the two support components
has unbounded Hilbert distance. Hence the full positive orthant has infinite
image diameter.

There is also an important type fence: \(K(s)\) is the reflected physical
density constructed in BF3.1, not yet the all-label completely positive
block transport required by BF4. This result rejects the shortcut
"positive density equals Birkhoff map"; it does not prejudge the correctly
grouped CP map.

## 3. The local reflected Gram loses cutoff-uniform diameter

Let \(M_N[p,r]\) be the four-face SU(2) fusion multiplicity at fine cutoff
\(N\), and let

\[
 G_N=M_N^{\mathsf T}M_N.
\]

The one-step matrix \(M_N\) has fusion-zero holes. The reflected Gram
removes those holes inside each of its two parity sectors, so at every fixed
cutoff it has a valid finite projective-diameter certificate. The question
is whether those certificates are uniform in \(N\).

### 3.1 An all-cutoff multiplicity family

Restrict the fine packets to

\[
 p_{a,c}=(a,a,c,c),\qquad 0\le a,c\le N,
\]

and retain doubled spin \(2\). The exact multiplicity is

\[
 M_N[p_{a,c},2]
 =
 \begin{cases}
 3a,&a=c,\\
 3\min(a,c)+1,&a\ne c.
 \end{cases}
\]

Indeed, the two equal pairs fuse through even channels
\(x=0,2,\ldots,2a\) and \(y=0,2,\ldots,2c\). Fusion to output \(2\)
requires \(x=y\), \(x=y+2\), or \(y=x+2\), with the zero diagonal excluded.
Counting these three diagonals gives the displayed formula.

The squared contribution of just this subfamily to \(G_N[2,2]\) is

\[
\begin{aligned}
 L_N
 &=9\sum_{m=1}^{N}m^2
   +2\sum_{m=0}^{N-1}(N-m)(3m+1)^2\\
 &=\frac{N(N+1)(3N^2+7N+1)}2.
\end{aligned}
\]

At the stretched output \(4N\), only the packet \((N,N,N,N)\) contributes.
For that packet,

\[
 M_N[(N,N,N,N),4N]=1,\qquad
 M_N[(N,N,N,N),2]=3N.
\]

Consequently

\[
 G_N[4N,4N]=1,\qquad
 G_N[2,4N]=3N,\qquad
 G_N[2,2]\ge L_N.
\]

### 3.2 Quadratic diameter growth

The \((2,4N)\) cross-ratio therefore obeys

\[
\Theta_N
\ge
\frac{G_N[2,2]G_N[4N,4N]}{G_N[2,4N]^2}
\ge
\frac{(N+1)(3N^2+7N+1)}{18N}
\ge \frac{N^2}{6}.
\]

Thus the projective diameter is unbounded. The repository's exact rational
certificate uses the conservative rate

\[
 q_N^{\rm rat}=\frac{\Theta_N-1}{\Theta_N+1}.
\]

Its lower bound tends to one. The sharp diameter expression

\[
 \tanh\!\left(\frac{\log\Theta_N}{4}\right)
 =\frac{\sqrt{\Theta_N}-1}{\sqrt{\Theta_N}+1}
\]

also tends to one. Therefore no cutoff-independent diameter rate
\(q<1\) can be obtained from this local reflected-Gram primitive.

The complete exact fixed-cutoff census is:

| \(N\) | exact rational certificate rate |
|---:|---:|
| 1 | \(7/15\) |
| 2 | \(19/25\) |
| 3 | \(1333/1495\) |
| 4 | \(2603/2747\) |
| 5 | \(1544/1589\) |
| 6 | \(38351/38999\) |
| 7 | \(1715/1733\) |

The certificate is constructive against any proposed uniform rational
rate. For example:

| proposed \(q\) | returned cutoff | quadratic rate floor | exact family floor |
|---:|---:|---:|---:|
| \(1/2\) | 5 | \(19/31\) | \(16/21\) |
| \(9/10\) | 11 | \(115/127\) | \(283/305\) |
| \(99/100\) | 35 | \(1219/1231\) | \(7807/7877\) |

This is a failure of the local primitive, not of the Birkhoff/fusion
program. A successful kernel must mix the physical support after grouping
over a fixed physical distance and must use more structure than
\(M_N^{\mathsf T}M_N\).

## 4. A representation cutoff cannot be chosen independently of coupling

BF3.1 identifies the first feature outside cutoff \(N\):

\[
 T_N(s)=(N+2)s^{E_N},
\qquad
 E_N=(N+1)(N+3).
\]

For every fixed \(s<1\), this tends to zero rapidly. That statement is not
uniform as the heat time tends to zero, equivalently \(s\to1\).

Choose the exact rational coordinate

\[
 s_N=1-\frac1{2E_N}.
\]

Bernoulli's inequality gives

\[
 s_N^{E_N}
\ge 1-E_N\frac1{2E_N}
=\frac12,
\]

and hence

\[
 T_N(s_N)\ge\frac{N+2}{2}.
\]

The unnormalized outside feature not only fails to vanish uniformly over
\(0<s<1\); this selected lower bound grows. This does not by itself lower
bound the normalized physical remainder because the partition function and
physical norm may compensate it. It proves that BF3.2 needs all of:

- a coupling-dependent cutoff schedule;
- normalization by the actual Haar partition function;
- a physical weighted norm on all \(P/Q\) blocks;
- a volume-uniform tail comparison in that norm.

A cutoff-only envelope cannot discharge BF3.2.

## 5. The exact BF4 handoff interface

The fail-closed handoff now requires nine fields:

1. the exact all-label Haar-network block kernel;
2. an invariant positive carrier for that kernel;
3. retained signed intertwiner transport;
4. global mixing, or a proved grouping that supplies it;
5. the physical projective norm;
6. a projective-diameter bound over fixed physical distance;
7. domination of the signed coherent remainder in the same norm;
8. a coupling-dependent cutoff schedule;
9. volume-uniform constants.

Only item 3 is presently closed. BF3.1 supplies its exact finite
intertwiner transports. The remaining eight fields cannot be inferred from
componentwise positivity or from the local reflected Gram.

## 6. Gate adjudication

| BF3.3 action | Result |
|---|---|
| audit whole-slab positive support | 32 disconnected rank-one components |
| distinguish local from global contraction | component rate 0, global diameter infinite |
| audit reflected local primitive | fixed-cutoff positive parity sectors |
| test cutoff uniformity | exact cross-ratio lower bound \(\Theta_N\ge N^2/6\) |
| test cutoff-only heat tail | refuted by \(s_N=1-1/(2E_N)\) |
| define physical BF4 handoff | nine-field fail-closed interface |
| decide readiness for BF4 | false |

BF3.3 closes because every currently proposed shortcut has been decided and
the required replacement theorem is explicit. It does not close BF3.2,
RG-I7, or any continuum gate.

## 7. Consequence for the work order

The critical path returns to **BF3.2: all-label kernel and vanishing
remainder**. BF3.2 must construct the normalized all-label physical map and
its coupling-dependent tail schedule. Only then can a new grouped kernel be
tested against the BF3.3 nine-field interface.

The immediate research target is no longer "find a small positive matrix
with \(q<1\)." It is:

> Construct a grouped, all-label, normalized Haar block whose support mixes
> the physical sectors over a fixed physical distance, and prove its
> diameter and coherent remainder bounds jointly along the
> coupling-dependent cutoff schedule.

## 8. Reproduction

- `computations/bf3_3_birkhoff_handoff.py`;
- `tests/test_bf3_3_birkhoff_handoff.py`;
- `computations/whole_corrected_slab_kraus.py`;
- `computations/local_face_projective_census.py`;
- `computations/rational_projective_diameter.py`.

The aggregate certificate is
`computations.bf3_3_birkhoff_handoff.bf33_certificate()`.
