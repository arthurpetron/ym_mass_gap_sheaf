# BF4 transverse all-label tail

## Result

The 21-face residual left by normalized-Haar leaf elimination has a
constructive all-label limit as a continuous function of its 18
corridor-protected boundary links, at every fixed heat coordinate
\(0<s<1\).  The convergence is uniform in all boundary holonomies and
independent of the ambient lattice volume.

This result constructs the residual boundary function.  Subsequent direct
all-label measure regrouping constructs the physical source/target Choi
operator and proves fixed-coupling CP-order corridor domination without
expanding this function in a signed recoupling basis.  A spacing-uniform
coefficient as \(s\to1\), mass-preserving RG interpretation, and
consecutive-scale composition remain open.

## Uniform bound

For one \(SU(2)\) heat-kernel character term use
\[
 h_n(s)=(n+1)^2s^{n(n+2)}.
\]
At cutoff \(N\), let \(T_N(s)\) be the existing exact geometric bound for
\(\sum_{n>N}h_n(s)\), and let
\[
 H_N(s)=\sum_{n=0}^{N}h_n(s)+T_N(s).
\]
Then both the full kernel and its truncation are bounded in absolute value by
\(H_N(s)\).  The product-difference telescope for \(F\) plaquettes gives
\[
 \left\|\prod_{f=1}^{F}K_s(H_f)
       -\prod_{f=1}^{F}K_s^{(\le N)}(H_f)\right\|_\infty
 \le F\,H_N(s)^{F-1}T_N(s).
\]

The connected component has \(F=15\).  Integration over its five
unprotected links is with normalized Haar probability, so
\[
 \left\|\int f\,dU-\int g\,dU\right\|_\infty
 \le \|f-g\|_\infty.
\]
The six one-face decorations contribute the same telescope with \(F=6\).
Composing the two estimates gives exactly
\[
\begin{aligned}
 &15H_N^{14}T_N\,H_N^6
 +H_N^{15}\,6H_N^5T_N\\
 &\hspace{4em}=21H_N^{20}T_N.
\end{aligned}
\]
Thus the complete 21-face residual has the explicit uniform Cauchy modulus
\[
 \boxed{\quad E_N(s)=21H_N(s)^{20}T_N(s).\quad}
\]
Because \(T_N(s)\) decays super-geometrically at every fixed \(s<1\), so does
\(E_N(s)\).

## Executable schedule

`computations/transverse_all_label_tail.py` evaluates the bound in exact
rational arithmetic and searches for the least certified cutoff at a
requested rational tolerance.  For tolerance \(10^{-6}\), sample schedules
are:

| heat coordinate | least certified cutoff |
|---:|---:|
| \(1/2\) | 5 |
| \(3/4\) | 12 |
| \(9/10\) | 26 |

These numbers are diagnostics for this conservative uniform bound, not
claims of optimality.

## Remaining obstruction

This theorem removes one ambiguity from the BF4 frontier: the transverse
residual itself is not blocked by an undefined all-label character sum.
The later basis-free construction in
`notes/bf4-physical-all-label-choi-domination.md` has now completed the
physical all-label Choi comparison at each fixed coupling:
\[
 J_{\rm phys}(s,u)\succeq
 \left(\frac{\ell_s}{H_s}\right)^{21}J_{\rm corr}(s,u).
\]
What remains is the stronger operator-theoretic bridge:

1. either materialize the entrywise all-label \(F/R\) transport, if a
   coordinate-level recoupling proof is required, or continue basis-free;
2. replace the collapsing one-step coefficient by a spacing-uniform
   relative residual-order estimate over a fixed physical distance;
3. identify the positive Choi difference as a mass-preserving RG channel
   residual;
4. prove same-carrier composition between consecutive scales.

The fixed-\(s\) modulus above cannot be silently promoted to the second item:
its certified cutoff grows as \(s\to1\), and the available Jacobi-floor
coefficient itself collapses there.
