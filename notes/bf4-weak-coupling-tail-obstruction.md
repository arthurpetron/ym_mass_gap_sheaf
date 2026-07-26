# BF4 fixed-cutoff weak-coupling tail obstruction

The fixed-coupling residual modulus
\[
 E_N(s)=21H_N(s)^{20}T_N(s)
\]
constructs the all-label residual boundary function for every \(s<1\), but
it cannot be made spacing-uniform by choosing one representation cutoff and
holding it fixed.

At the identity of \(SU(2)\), the heat-kernel character expansion is
\[
 K_s(e)=\sum_{n\ge0}(n+1)^2s^{n(n+2)}
\]
with no cancellations.  For cutoff \(N\), set
\[
 C_N=(N+1)(N+3),\qquad
 s_N=1-\frac1{2C_N}.
\]
Bernoulli's inequality gives
\[
 s_N^{C_N}\ge1-C_N(1-s_N)=\frac12.
\]
The first omitted label \(N+1\) therefore contributes
\[
 (N+2)^2s_N^{C_N}\ge\frac{(N+2)^2}{2}
\]
to the actual truncation error at the identity.  The witness coupling
satisfies \(0<s_N<1\).

Consequently no fixed \(N\) gives a small absolute uniform heat-kernel tail
over the entire weak-coupling interval.  In particular, the
boundary-uniform fixed-\(s\) residual estimate cannot be promoted to a
spacing-uniform CP/Choi estimate with a fixed cutoff.

The obstruction also holds for relative error.  Take the \(N+1\) omitted
labels \(N+1,\ldots,2N+1\), set
\[
 \widehat C_N=(2N+1)(2N+3),\qquad
 \widehat s_N=1-\frac1{2\widehat C_N}.
\]
Every term in this omitted block retains at least half its identity value,
whereas every retained term is at most its identity value.  Thus
\[
 \frac12\sum_{n=N+1}^{2N+1}(n+1)^2
 >
 \sum_{n=0}^{N}(n+1)^2.
\]
The omitted tail is therefore larger than the entire retained head, so its
relative share is greater than \(1/2\).  A fixed cutoff cannot be rescued
merely by dividing the absolute error by the heat density.
Writing \(m=N+1\), the exact positive margin is
\[
 \frac12\bigl(S(2m)-S(m)\bigr)-S(m)
 =
 \frac{m(2m+1)(5m-1)}{12}>0,
 \qquad
 S(m)=\sum_{k=1}^{m}k^2.
\]

This does not obstruct:

- a cutoff \(N=N(s)\) that grows toward weak coupling;
- grouping the full label tower before comparison;
- a trace-class Cauchy name at each fixed coupling;
- positivity of the full heat-kernel measure.

The direct-regrouping option has now been executed: the physical
source/target Choi operator retains the full label tower, while a derived
cutoff \(N(s)\) certifies the heat-kernel upper majorant used in
\[
 J_{\rm phys}(s,u)\succeq
 \left(\frac{\ell_s}{H_s}\right)^{21}J_{\rm corr}(s,u).
\]
This resolves fixed-coupling CP order but not weak-coupling uniformity,
because the Jacobi-floor coefficient collapses as \(s\to1\).  Its normalized
difference is now a random-unitary CPTP residual with abstract same-carrier
convolution.  The exact 120-face gluing geometry and boundary-message
Markovization algebra are now pinned, and the continuous all-label
fine-boundary transfer is explicit.  The next theorem must obtain a
spacing-uniform two-sided Harnack estimate for the grouped physical
Feynman--Kac kernel directly on the fixed physical-distance block. The
carrier has been enlarged to the full 23-cycle tree-gauge boundary, where
the retained projection and Markov intertwining are identities. See
`notes/bf4-boundary-message-uniform-order.md`.

The executable certificate is
`computations/transverse_weak_coupling_tail_obstruction.py`.
