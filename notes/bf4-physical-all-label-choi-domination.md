# BF4 physical all-label Choi contraction and fixed-coupling CP order

## Result

There is now a direct all-label source/target Choi construction for the
corrected slab which does not first expand the physical density into signed
finite character families.

Let \(S_s\) be the product of the 30 full heat kernels on the nine selected
corridor disks.  Exact normalized-Haar leaf elimination removes 21 of the
other 42 plaquettes.  Integrating the five internal variables of the
remaining 21-face transverse component gives a positive residual function
\(R_s\) on the selected-corridor variables.  The physical and selected-only
normalized measures are
\[
 d\mu_s=\frac{S_sR_s}{Z_{\rm phys}}\,d\lambda,
 \qquad
 d\nu_s=\frac{S_s}{Z_{\rm corr}}\,d\lambda .
\]

For each of the nine coarse holonomies, vectorize the complete
Peter--Weyl matrix block as
\[
 \sqrt{(n+1)u^{n(n+2)}}\,\operatorname{vec}D^n(g).
\]
The row magnetic index is the source index, the column magnetic index is the
target index, and the representation label is shared.  Tensoring the nine
slots gives \(W_u\).  The physical and corridor Choi operators are
\[
\begin{aligned}
 J_{\rm phys}(s,u)
  &=\int |W_u(\Pi x)\rangle\langle W_u(\Pi x)|\,d\mu_s(x),\\
 J_{\rm corr}(s,u)
  &=\int |W_u(\Pi x)\rangle\langle W_u(\Pi x)|\,d\nu_s(x).
\end{aligned}
\]
They act on the same all-label source/target carrier.  Because \(u<1\),
both are positive trace-class operators.

This is the basis-free physical Gram/Choi contraction.  It is equivalent
under every complete signed recoupling basis; an entrywise all-label
\(F/R\) table is not required for the order proof.

## Exact geometry

The executable audit independently recovers:

| item | count |
|---|---:|
| full corrected-slab faces | 72 |
| selected corridor faces | 30 |
| peeled transverse faces | 21 |
| residual transverse faces | 21 |
| selected disk-internal links | 27 |
| protected free links after gauge fixing | 18 |
| residual internal normalized-Haar links | 5 |

The selected faces are pairwise disjoint.  The 27 internal-link sets of the
nine disks are pairwise disjoint, and the oriented boundary of every disk is
its named coarse path.  Consequently the selected-only internal
integrations give six spatial coordinates \(s^4\) and three temporal
coordinates \(s^2\).  The deterministic map \(\Pi\) retains the compatibility
of coarse loops which share boundary links.

## CP-order proof

Let \(\ell_s>0\) be the existing all-label Jacobi-product lower bound for one
heat kernel.  Let \(H_s\) be any certified full character upper bound,
\[
 K_s(g)\le H_s.
\]
The physical operator uses the full heat kernels; the representation cutoff
used to calculate \(H_s\) is only proof data.

Every one of the 21 residual factors lies between \(\ell_s\) and \(H_s\).
Normalized Haar integration therefore gives
\[
 \ell_s^{21}\le R_s(x)\le H_s^{21}.
\]
It follows that
\[
 \ell_s^{21}
 \le \frac{Z_{\rm phys}}{Z_{\rm corr}}
 \le H_s^{21}
\]
and hence
\[
 \frac{d\mu_s}{d\nu_s}
 =R_s\frac{Z_{\rm corr}}{Z_{\rm phys}}
 \ge
 \left(\frac{\ell_s}{H_s}\right)^{21}.
\]
Define
\[
 \eta_s=\left(\frac{\ell_s}{H_s}\right)^{21}>0.
\]
Then
\[
 \boxed{\quad
 J_{\rm phys}(s,u)\succeq \eta_s J_{\rm corr}(s,u).
 \quad}
\]
The difference is an integral of rank-one positive operators against the
positive measure \(\mu_s-\eta_s\nu_s\).  Therefore the inequality is in
full Choi/CP order, not merely scalar or trace norm.  Orthogonal
Peter--Weyl cutoffs preserve it exactly.

## Spacing-dependent cutoff

The proof exposes the representation cutoff as coupling-dependent data.
For a relative upper-tail tolerance \(10^{-2}\), the least certified
one-plaquette majorant cutoffs are:

| \(s\) | cutoff |
|---:|---:|
| \(1/2\) | 2 |
| \(3/4\) | 3 |
| \(9/10\) | 6 |
| \(99/100\) | 23 |

This does not truncate the physical Choi operator.  It computes \(H_s\)
while the measure comparison groups the full label tower before taking
positive order.

## Exact limitation

The first Jacobi-product factor gives the elementary upper bound
\[
 \ell_s
 \le
 \frac{(1-s^2)(1-s)^2}{(1+s)^2}
 =
 \frac{(1-s)^3}{1+s}.
\]
Since \(H_s\ge1\),
\[
 0<\eta_s
 \le
 \left(\frac{(1-s)^3}{1+s}\right)^{21}.
\]
Thus this certified fixed-slab coefficient converges to zero as \(s\to1\).
For the exact dyadic model \(a=2^{-k}\), \(s(a)=1-a\),
\[
 \eta_{s(a)}
 \le
 \left(\frac{a^3}{2-a}\right)^{21}.
\]
Expanding \(m=1/a\) microscopic decompositions and using only histories
with a certified corridor tag gives at most
\[
 1-(1-\eta_s)^m\le m\eta_s\le a^{62}.
\]
Thus composition of the current fixed-slab certificate cannot yield the
required spacing-uniform physical-distance refresh mass.

The normalized positive measure difference has now been promoted, after
finite-cutoff heat-feature deweighting, to a random-unitary CPTP residual.
The finite carriers form an exact projective family, and the resulting
normal all-label channels compose abstractly by group convolution.  See
`notes/bf4-all-label-channel-composition.md`.

The remaining semantic promotion is specifically physical: abstract
convolution has not been identified with the boundary-dependent
Haar-network channel obtained by gluing consecutive corrected slabs.
Nor has the corridor channel been proved to be the input-independent reset
required by the base-norm refresh theorem.

Finally, the Jacobi identity underlying \(\ell_s\) remains a paper-level
analytic input rather than a theorem formalized in the repository's Lean
kernel.

The next theorem is therefore not basic fixed-coupling positivity or
abstract channel algebra.  The two-slab fiber-product geometry and
finite-horizon boundary-message normalization are now exact.  The next
transfer kernel is also explicit on the 48-link fine boundary.  The next
carrier is now the full 23-cycle tree-gauge boundary, so its identity
Markov intertwining is exact. The next object is a spacing-uniform
two-sided Harnack estimate for the grouped physical Feynman--Kac kernel
with all interior spatial weights. The row-order theorem then supplies the
relative backward-message minorization independently of the terminal
message; see `notes/bf4-boundary-message-uniform-order.md`.

The executable certificate is
`computations/physical_all_label_choi_domination.py`, with tests in
`tests/test_physical_all_label_choi_domination.py`.
