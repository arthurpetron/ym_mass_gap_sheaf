# Checkpoint 01 — actual normalized-pair test on the finite cubical core

**Status:** exact Python diagnostic completed; both focused Lean certificate
files pass the local axiom-gated checks. The complete original-source-to-matrix Lean pin has NOT
been formalized. No continuum, volume-uniform, all-cutoff, or completed-Wilson
claim is made. No canonical frontier statement or root import is changed.

## Scope and change boundary

This checkpoint addresses the first priority: test the actual transported
observed/unobserved pair before using an inequality on an untransported
plaquette sector. All delivered paths are relative to `codex/ym_mass_gap_sheaf`.
The files were staged in an isolated working copy. Dropbox has not been modified:
the currently exposed connector has no upload/edit action. Extraction with
`unzip -n` adds these files locally without overwriting existing files.

The connected project was reread. In particular, the exact fringe reduction
already exists in
`BF4ExactSlabFixedSpatialActiveTransfer.original_transfer_haar_active`.
It is reused as an intended consumer-side identification, not reimplemented.
That theorem is Haar-tested equality, not an equality of raw polynomial lists.
It permits a supported test containing the full target spatial weight.

## 1. The finite, positive action under investigation

Use the six-face, twelve-edge cube, the fully active core indicated by the
width-two fixed-spatial geometry. Its exact geometric identification with the
repository's coordinate lists remains part of the pending Lean source pin.
Let `H` be normalized product SU(2) Haar integration, `w=1/2`, and `r=w^3=1/8`.
At representation cutoff one the single-link/face heat polynomial is

\[
h(U)=1+2r\operatorname{tr}(U).
\]

Here the trace is the unnormalized two-dimensional fundamental character.
Since its range is [-2,2], each factor is at least `1-4r=1/2`.
Thus this particular truncated action is pointwise positive. This is an
independent finite-cutoff positivity observation, not a weakening of
`headCutoff(w)` or of any canonical small-nome guard.

Put

\[
V(x)=\prod_{p=1}^6h(U_p(x)),\qquad
(Pb)(y)=\int\prod_{e=1}^{12}h(x_ey_e^{-1})b(x)\,dH(x),\qquad T=P(V\,\cdot).
\]

For a selected fundamental face character `chi`, retain BOTH messages

\[
u=T1,\qquad f=T\chi.
\]

The two-layer probability law and its actual right marginal are

\[
d\pi(x,y)=Z^{-1}V(x)K(x,y)V(y)\,dH(x)dH(y),\qquad
 d\nu(y)=Z^{-1}V(y)u(y)\,dH(y),\quad Z=H[Vu]>0.
\]

The conditional observation is `f/u`, not `f`. No rational function is declared
to be a polynomial; division is used only in the mathematical interpretation.
All stored certificate equalities are denominator-cleared.

## 2. Exact signed Haar computation

At cutoff one, the link representations are vacuum and fundamental. At a
trivalent cube vertex, gauge invariance permits zero or two incident
fundamental links. The resulting even edge supports are disjoint cycles.
There are 32: one empty support, six length-four, sixteen length-six, and
nine length-eight supports. These carry products `W_C` of fundamental loop
characters. Their Haar Gram matrix is the identity: distinct supports have
an odd occurrence on some link; equal supports reduce to normalized loop
squares. This is the mathematical basis interpretation; no general-group or
all-cutoff extension is being inferred.

The original spatial multiplication and kinetic matrices are

\[
A_{CD}=H[W_C V W_D],\qquad D_{CC}=r^{|C|},\qquad [T]=DA.
\]

In particular, the **weighted transfer pairing is `A D A`**, not `D` or `DA`
with the target weight dropped. Every entry of `A` is calculated from signed
fundamental Haar tensors. It is not a matrix of positive multiplicities.

For two and four fundamental matrix factors, respectively, the local tensors
are

\[
\int U_{a_1b_1}U_{a_2b_2}\,dU
 =\tfrac12\epsilon_{a_1a_2}\epsilon_{b_1b_2},
\]

\[
\int\prod_{j=1}^{4}U_{a_jb_j}\,dU
 =\tfrac16\sum_{\mathfrak p}
   \prod_{(i,j)\in\mathfrak p}\epsilon_{a_i a_j}\epsilon_{b_i b_j},
\]

where the second sum is over the three pairings of four indices and
`epsilon[0,1]=1`, `epsilon[1,0]=-1`. Reverse edge occurrences retain the
inverse-matrix signs. The numerator tensors are contracted as integers and
only then divided by the exact products of 2 and 6.

The independent test implementation expands actual quaternion matrix entries
as polynomials and evaluates their S^3 monomial moments. All 4,160 entries
across degrees two/four and all forward/inverse combinations agree exactly.
The Lean normalization file checks the forward tensors directly against the
repository's `productHaar` on its genuine rational-polynomial carrier;
coordinates 4..7 carry the unit. This checks the local normalization, not
the whole tensor-network compiler.

Diagnostic identities include

\[
H\Big[\prod_{p=1}^6\chi_p\Big]=\tfrac1{16},\qquad
H[\chi_p\chi_q\chi_{\partial(p\cup q)}]=\tfrac12
\]

for adjacent cube faces `p,q`. The 1/16 cube normalization must not be replaced
by a bare multiplicity. All 48 cube automorphisms preserve the computed table.

## 3. A denominator-aware escape witness

Let `S` be the span of the constant and the six fundamental plaquette
characters. Take a rectangle character `R` around two adjacent faces. Form
its orthogonal residual `q` against `S` in the **same right marginal**:

\[
q=R-\sum_{i=0}^6 c_i\phi_i,\qquad
\phi_0=1,\ \phi_i=\chi_i,\qquad H[Vu\,q\phi_i]=0.
\]

The coefficients are obtained by rational Gaussian elimination of the actual
seven-by-seven marginal Gram matrix. No unproved decomposition estimate is
assumed. The stored eight-by-eight Gram matrix includes the rectangle; the
full-weight source pairing vector is `H[V phi_i f]`.

The exact data yield

\[
0<\mathbb E_\nu[q^2]<1,\qquad
\frac1{2500000}<\operatorname{Cov}_\pi(\chi(x),q(y))<\frac1{2000000}.
\]

The rational covariance bounds are exact; decimal displays are not used for
sign decisions. Centering gives `H[Vu q]=0`, so

\[
\operatorname{Cov}_\pi(\chi,q)
=H[Vqf]/Z,
\qquad
D(q)=Z H[Vqf]-H[Vf]H[Vu q]=Z H[Vqf]>0.
\]

The full partition is

\[
Z=\frac{281509362544643}{281474976710656}.
\]

**Finite-model consequence of the displayed original-integral identities:**
`f/u` cannot be in `S` in `L^2(nu)`. If it were, its pairing with the exactly
`nu`-orthogonal `q` would vanish, contrary to the positive covariance. This
is stronger than detecting a new bare Haar coefficient of `f`: it retains
`u` and the correct marginal and does not drop the target action.

**Verification boundary:** Python established the rational identities using
the independently tested Haar engine. The Lean arithmetic checker checks
only the displayed integer certificate. Until the original-integral pins
are proved. The two Lean files now pass focused serialized checks: the
fundamental tensor file reports 17 public gates and the integer certificate
file reports 14 public gates, all within `{propext, Quot.sound}`. This still
is NOT a kernel-checked nonclosure theorem for `transferStep`, because the
original cube-to-matrix/source pin remains open.

## 4. Why this changes the immediate work

This finite positive-action test supplies a concrete obstruction to replacing
the actual transported normalized pair by an unpropagated plaquette family.
It does not refute a gap. It does not refute a different stable decomposition.
It is at cutoff one and fixed width: it says nothing by itself about the
late-cutoff orbit, weak-coupling asymptotics, or the current cutoff-removed
Wilson completion.

The next source-level task is deliberately small: identify the displayed
marginal Gram entries and source pairings with the original width-two
integrals, then turn the dual calculation into the corresponding finite
nonclosure statement. Only the selected 8x8 Gram and eight source pairings
are needed. A full 32-state spectral theory is NOT a prerequisite.

Relevant existing sources/consumers:

- `BF4ExactSlabFixedSpatialActiveTransfer.original_transfer_haar_active` and
  `BF4ExactSlabFixedSpatialActiveSpatialWeight.spatialWeight_haar_active`:
  exactly remove the allowed fringe contributions without changing the
  original tested transfer.
- `BF4ExactSlabFixedSpatialTransferStep.swept_step_pairing`:
  retain both endpoint spatial factors.
- `BF4ExactSlabFixedSpatialSeparatedWindowPins.separatedMessage`:
  continue the SAME observed/unobserved pair across a genuinely empty gap.
- `BF4ExactSlabFixedSpatialDirichletCoercivity.terminal_energy_variance_floor`:
  an eventual estimate must control the original marginal, not a substituted
  Haar norm or an unrelated heat-bath Dirichlet form.

After this source pin, the analytical task is a weighted stable-decomposition
or direct signed-orbit estimate for the generated family. The finite counter-
example is not a substitute target to elaborate indefinitely. Do not turn
it into another series of generic toy obstructions. Keep actual temporal
iteration and the larger-domain limiting form as the primary consumers.

## 5. Local verification checkpoint — run now

Save `checkpoint01_changes.zip` in the project root, then:

```sh
cd '/Users/darthur/Dore Dropbox/Arthur Petron/codex/ym_mass_gap_sheaf'
unzip -n checkpoint01_changes.zip
```

The archive contains only new project-relative files. It does not include
copies of existing AGENTS files, the root module, configuration, or the work
plan. Before starting Lean, ensure no other Lean/Lake/test/runner job is
active. Keep the existing safe launcher and its resource protections.

```sh
set -o pipefail
python3 -B scripts/safe_lean_build.py --jobs 1 \
  --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/SU2FundamentalHaarCheckpoint.lean \
  2>&1 | tee audits/checkpoint01-haar-local.log
```

Recorded result: successful elaboration and 17 public axiom reports confined to
`{propext, Quot.sound}` (empty lists also pass). Then run:

```sh
python3 -B scripts/safe_lean_build.py --jobs 1 \
  --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4CubeNormalizedPairEscapeCheck.lean \
  2>&1 | tee audits/checkpoint01-arithmetic-local.log
```

Recorded result: successful elaboration and 14 public reports; the integer
certificate's shape/denominator/source-pairing/covariance inequalities are
verified within `{propext, Quot.sound}` (several are axiom-free). Any extra axiom, compiler error, or resource
stop is a failed/pending gate, not a reason to raise limits. Do not run a
root/full-tree build or full axiom audit for this checkpoint.

If the first check specifically reports a missing imported `.olean`, build
only its existing direct import, retaining the explicit cap, then retry it:

```sh
python3 -B scripts/safe_lean_build.py --jobs 1 \
  --lake-worker-limit-gib 20 \
  -- +YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier:olean
```

The Python reproduction is optional and uses only the existing Python/NumPy
environment; no package installation is needed by the delivered code:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  python3 -B tests/test_cube_cutoff_one_checkpoint.py
```

It writes its result only to this project's `audits/` directory. NumPy integer
contraction is an exploratory evaluator here, not a trusted Lean oracle. No
native-evaluation tactic is present in either Lean candidate.

## 6. Recorded verification and remaining priorities

The final focused Python run passed 11 tests. Exact arithmetic rounding error
is zero for this finite calculation; no bound is supplied for cutoff removal,
volume removal, or continuum approximation. Both Lean files passed the
serialized focused checks under the 20 GiB worker cap; no full-root/full-tree
build or full axiom audit was run. No historical build is reported as current
verification.

The remaining priorities are unchanged: original separated-orbit control;
a same-theory physical-scale trajectory and survival estimate; quantitative
current-carrier range approximation; reviewed, same-theory continuum predicate
repairs; and the all-group construction. This checkpoint starts priority one;
it does not mark the other priorities or the primary analytic bound complete.
